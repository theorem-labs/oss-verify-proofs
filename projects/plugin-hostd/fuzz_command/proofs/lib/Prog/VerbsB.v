From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_QUIT : Z := 0x34108.
Definition IV_TABLE_B : Z := 0x22928.
Definition INFO_TABLE : Z := 0x22888.
Definition SSP_GOT_B : Z := 0x22a68.
Definition SSP_GUARD_B : Z := 0x54450.

Definition iv_ptrs_b : list Z :=
  [0x108e8; 0x108fa; 0x10a20; 0x10545; 0x1071e; 0x1083b; 0x109bc; 0x1074c; 0x1034e;
   0x10360; 0x10855; 0x10331; 0x104cf; 0x107f2; 0x107a5; 0x103ee; 0x102dd; 0x107b4].

Definition info_rows : list (Z * Z) :=
  [(0x109ff, 1); (0x10889, 0); (0x1073c, 0); (0x104c4, 0); (0x10972, 0);
   (0x10713, 0); (0x10638, 0); (0x10874, 0); (0x1087c, 0); (0x10323, 0)].

Definition info_bytes : list byte :=
  concat (map (fun r => Mem.le8 (Z_to_bv 64 (fst r)) ++ Mem.le4 (Z_to_bv 64 (snd r)) ++ Mem.le4 (Z_to_bv 64 0)) info_rows).

Definition SB_REQ : Z := 8194.

Definition sb_n (b : sbound) (k : nat) : sbound :=
  SB (sb_live b + Z.of_nat k) (sb_bytes b + SB_REQ * Z.of_nat k) (sb_cap b).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

Definition le_at (mem : word -> option byte) (a : Z) (bs : list byte) : Prop := blk_data B mem a bs.

Definition outside (L : layout) (A : astate) (stk : Z) (regs : bvmap 5 word) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> ~ owned B L A (a + i) /\ ~ scratch_k B stk regs (a + i).

Definition vr_tables (mem : word -> option byte) (can : word) : Prop :=
  le_at mem IV_TABLE_B (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) iv_ptrs_b)) /\
  le_at mem INFO_TABLE info_bytes /\
  le_at mem SSP_GOT_B (Mem.le8 (Z_to_bv 64 SSP_GUARD_B)) /\
  le_at mem SSP_GUARD_B (Mem.le8 can).

Definition ssp_b (mem : word -> option byte) (can : word) : Prop :=
  le_at mem SSP_GOT_B (Mem.le8 (Z_to_bv 64 SSP_GUARD_B)) /\ le_at mem SSP_GUARD_B (Mem.le8 can).

Definition toks_at (mem : word -> option byte) (tok : Z) (ptrs : list Z) (tks : list (list byte)) (cb ncb : Z) : Prop :=
  tok mod 8 = 0 /\ length ptrs = length tks /\
  le_at mem tok (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) ptrs)) /\
  forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
    le_at mem p (w ++ [Z_to_bv 8 0]) /\ Forall (fun c => bv_unsigned c <> 0) w /\ Z.of_nat (length w) <= 8192 /\
    cb <= p /\ p + Z.of_nat (length w) + 1 <= cb + ncb /\
    (p + Z.of_nat (length w) + 1 <= tok \/ tok + 8 * Z.of_nat (length tks) <= p).

End K.

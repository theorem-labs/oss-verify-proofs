From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB RecInv RecInvP
xstrdup_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition ARG_I : Z := 0x15b1c.
Definition ARG_I_K : Z := XSTRDUP_K + 32.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition arg_i_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (e v m : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    Mem.bytes_at segs mem' (spZ regs - 32) (dec v ++ [Z_to_bv 8 0]) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\ f18_words segs mem' /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    ((m = 6 /\
      call_post_k B MR ARG_I_K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
      blocks L' A' = blocks L A /\ res_ok_slots A' b) \/
     (m < 6 /\ exists p,
      call_post_k B MR ARG_I_K L A regs mem md
        (fun a => e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4 \/
                  e + CALL_OFF_ARGS + 8 * m <= a < e + CALL_OFF_ARGS + 8 * m + 8 \/
                  p <= a < p + Z.of_nat (length (dec v)) + 1)
        L' A' regs' mem' md' /\
      p <> 0 /\ p mod 16 = 0 /\ fresh_block B p (Z.of_nat (length (dec v)) + 1) /\
      (exists b1 b2, blocks L' A' = b1 ++ (p, Z.of_nat (length (dec v)) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
      Mem.bytes_at segs mem' (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 (m + 1))) /\
      Mem.bytes_at segs mem' (e + CALL_OFF_ARGS + 8 * m) (Mem.le8 (Z_to_bv 64 p)) /\
      Mem.bytes_at segs mem' p (dec v ++ [Z_to_bv 8 0]) /\
      st_init_done A' = true /\
      res_ok_slots A' (sb_malloc b (Z.of_nat (length (dec v)) + 1)))).

Definition arg_i_contract : Prop :=
  forall L A regs mem md (e v m : Z) b,
    call_pre_t B API ARG_I_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 e -> getr regs 11 = Z_to_bv 64 v -> -2^31 <= v < 2^31 ->
    e mod 8 = 0 -> REC_SC <= e -> e + CALL_SIZE <= G_REC + REC_SIZE ->
    Mem.wr_at segs mem e CALL_SIZE ->
    Mem.bytes_at segs mem (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 m)) -> 0 <= m <= 6 ->
    f18_words segs mem -> frm_zero fp_csr ->
    res_ok_slots A b ->
    room_slots (sb_malloc b (Z.of_nat (length (dec v)) + 1)) (Z.of_nat (length (dec v)) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 ARG_I) mem (seg_rom segs)) md)
      (arg_i_ret L A regs mem md e v m b).

End K.

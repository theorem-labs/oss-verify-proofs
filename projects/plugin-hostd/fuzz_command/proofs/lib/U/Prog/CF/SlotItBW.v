From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotIter verbs_receive_c joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The state at the entry of check_words in the entry function (pc 0x14bac, returning to 0x14390): the message at
   cursor (p, n) ran on R0 (the recorder R1 owns O; g_rec.state and g_rec.host_settings of R0 in s2 and s3); the
   message's three blocks X = text, copy, arr are live, their addresses at FB + 24, FB + 32, FB + 40; a0 = the
   struct words at FB + 24, which holds the words of the message's line, each word inside a live block that is not
   the recorder's. stC (CF.SlotItC0.v) is this state at pc 0x14390, after check_words returned. *)

Section BW.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (S : Z) (rg : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte).

Notation CF := (CF.SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (CF.SlotInv.FB S).

Definition stBW (m p n : Z) (R0 : rstate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md O R1 x quit (text copy arr kt kc ka : Z) (wp : list Z) (jw : list byte),
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14bac) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ CF.SlotInv.rcap A /\
    vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\
    0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64 /\
    RFX L0 A0 L A mem R1 O (qv quit) [(text, kt); (copy, kc); (arr, ka)] /\
    text <> copy /\ text <> arr /\ copy <> arr /\
    0 <= kt <= 2 ^ 16 /\ 0 <= kc <= 2 ^ 16 /\ 0 <= ka <= 2 ^ 16 /\ arr mod 8 = 0 /\
    LR p0 n0 pl m p n regs mem /\
    getr regs 1 = Z_to_bv 64 0x14390 /\ getr regs 10 = Z_to_bv 64 (FB + 24) /\
    getr regs 18 = Z_to_bv 64 (r_state R0) /\ getr regs 19 = Z_to_bv 64 (r_host R0) /\
    rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\
    rw_cells rsegs mem (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw] /\
    words_view B mem (FB + 24) arr wp (hwords (m_D p0 pl p n)) /\
    words_place L A mem arr wp (hwords (m_D p0 pl p n)) /\
    in_live L A O arr (8 * Z.of_nat (length (hwords (m_D p0 pl p n)))) /\
    (forall k, (k < length (hwords (m_D p0 pl p n)))%nat ->
       in_live L A O (nth k wp 0) (Z.of_nat (length (nth k (hwords (m_D p0 pl p n)) [])) + 1)) /\
    join_need (hwords (m_D p0 pl p n)) + 1 <= 8194 /\
    msg_props R0 (m_D p0 pl p n).

End BW.

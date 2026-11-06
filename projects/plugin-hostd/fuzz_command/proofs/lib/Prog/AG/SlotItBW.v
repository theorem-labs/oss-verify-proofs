(* lib/Prog/SlotItBW.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotIter.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c joined_c CommandB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require SlotInv.
Import ListNotations.
Local Open Scope Z_scope.

(* The state at the entry of check_words in the entry function (pc 0x14980, returning to 0x142dc): the message at
   cursor (p, n) ran on R0 (the recorder R1 owns O; g_rec.state and g_rec.host_settings of R0 in s2 and s3); the
   message's three blocks X = text, copy, arr are live (s4, s5, s10); a0 = the struct words at FB + 40, which holds
   the words of the message's line, each word inside a live block that is not the recorder's; s7 = the input count
   after the message. stC (SlotItC0.v) is this state at pc 0x142dc, after check_words returned. *)

Section BW.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (S : Z) (rg : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte).

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Definition stBW (m p n : Z) (R0 : rstate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md O R1 x quit (text copy arr kt kc ka : Z) (wp : list Z),
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14980) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ SlotInv.rcap A /\
    vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\
    0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64 /\
    RFX L0 A0 L A mem R1 O (qv quit) [(text, kt); (copy, kc); (arr, ka)] /\
    text <> copy /\ text <> arr /\ copy <> arr /\
    0 <= kt <= 2 ^ 16 /\ 0 <= kc <= 2 ^ 16 /\ 0 <= ka <= 2 ^ 16 /\
    LR p0 n0 pl m p n regs mem /\
    getr regs 1 = Z_to_bv 64 0x142dc /\ getr regs 10 = Z_to_bv 64 (FB + 40) /\
    getr regs 18 = Z_to_bv 64 (r_state R0) /\ getr regs 19 = Z_to_bv 64 (r_host R0) /\
    getr regs 20 = Z_to_bv 64 text /\ getr regs 21 = Z_to_bv 64 copy /\ getr regs 26 = Z_to_bv 64 arr /\
    getr regs 23 = Z_to_bv 64 (n - hdr_n n - m_len p0 pl p n) /\
    (exists jsv jw, rw_cells rsegs mem FB (LOC0 jsv) /\ rw_cells rsegs mem (FB + 40) [CB 32 jw]) /\
    words_view B mem (FB + 40) arr wp (hwords (m_D p0 pl p n)) /\
    words_place L A mem arr wp (hwords (m_D p0 pl p n)) /\
    in_live L A O arr (8 * Z.of_nat (length (hwords (m_D p0 pl p n)))) /\
    (forall k, (k < length (hwords (m_D p0 pl p n)))%nat ->
       in_live L A O (nth k wp 0) (Z.of_nat (length (nth k (hwords (m_D p0 pl p n)) [])) + 1)) /\
    join_need (hwords (m_D p0 pl p n)) + 1 <= 8194 /\
    msg_props R0 (m_D p0 pl p n).

End BW.

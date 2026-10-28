From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkMem KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_fse_small_kit fse_kit_dsym.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem fse_dsymf_proof : fse_dsymf_stmt.
Proof.
  unfold fse_dsymf_stmt, fse_dsym_stmt_at, PFSE_DSYMF. intros until tb.
  intros MI STC SR BDC BCR CELB TBLEN TBBY TBOK FR01 TLR A1 A2 R1 R2 R3 R4 R5 R6 D1 D2 D3.
  unfold bitd_cells in BDC.
  assert (MU : munch [(ST, ST + 16); (BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  pose proof (TBOK st SR) as OK. unfold fse_cell_ok in OK. cbv zeta in OK. destruct OK as (NBR & NB1 & NX0 & NXB).
  specialize (NB1 eq_refl).
  pose proof (sk_cell2_ro usegs m (DT + 4) tb (4 * st) CELB TBBY ltac:(lia) ltac:(lia)) as CEL.
  assert (SYR : 0 <= Znth (4 * st + 2) tb < 256) by (apply (Forall_Znth (fun v => 0 <= v < 256) tb); [exact TBBY | lia]).
  set (nb := Znth (4 * st + 3) tb) in *. set (sy := Znth (4 * st + 2) tb) in *.
  set (nx := Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb) in *.
  assert (NXR : 0 <= nx < 4096) by (pose proof (Z.pow_pos_nonneg 2 nb ltac:(lia) ltac:(lia)); lia).
  clearbody nb sy nx. clear CELB TBOK TBBY.
  kx_auto [] 120%nat
    [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5);
     KZRange st 0 4095; KZRange tl 0 12; KZRange bc 0 4096; KZRange (DT + 4 + 4 * st) 4100 (2^47);
     KZRange nb 1 12; KZRange sy 0 255; KZRange nx 0 4095;
     KZAlign ST 8; KZAlign BD 8; KZWr ST 16; KZWr BD 40; KZDisj ST 16 BD 40;
     KZDisj ST 16 (DT + 4 + 4 * st) 4; KZDisj BD 40 (DT + 4 + 4 * st) 4]
    [].
  all: lazymatch goal with |- context [Z_to_bv 64 0x2c238] => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: apply evt_done; unfold fse_dsym_post; repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]; split; [exact STC|].
  all: lazymatch goal with |- context [bv_unsigned ?w / 2 ^ ?e] =>
         pose proof (sk_fast_bits (bv_unsigned w) nb (bv_unsigned_in_range 64 w) ltac:(lia)) as FB;
         set (b := bv_unsigned w / 2 ^ e) in *; clearbody b end.
  all: split; [lia|]; split; [exact BDC | lia].
Qed.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkMem KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_kit RZ_fse_small_kit.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PFSE_DSYMF : Z := 0x2c1b4.
Definition PFSE_DSYM : Z := 0x2c23c.

Definition fse_dsym_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ST BD SRC DT tl bc ptr : Z) (cont : word) (pad : list byte) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' bc',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(ST, ST + 16); (BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' ST [C8 (Z_to_bv 64 st'); C8 (Z_to_bv 64 (DT + 4))] /\ 0 <= st' < 2^tl
    /\ rw_cells usegs m' BD (bitd_cells cont (Z_to_bv 64 bc') pad ptr SRC) /\ bc <= bc' <= bc + tl.

Definition fse_dsym_stmt_at (ENTRY fast : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (ST BD SRC DT tl st bc ptr : Z) (cont : word) (pad : list byte) (tb : list Z),
  mem_inv usegs m ->
  rw_cells usegs m ST [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (DT + 4))] -> 0 <= st < 2^tl ->
  rw_cells usegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRC) -> 0 <= bc <= 4096 ->
  bytes_at usegs m (DT + 4) (map (Z_to_bv 8) tb) -> zlen tb = 4 * 2^tl -> Forall (fun v : Z => 0 <= v < 256) tb ->
  (forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u) -> 0 <= fast <= 1 -> 0 <= tl <= 12 ->
  ST mod 8 = 0 -> BD mod 8 = 0 ->
  4096 <= ST -> ST + 16 < 2^47 -> 4096 <= BD -> BD + 40 < 2^47 -> 4096 <= DT -> DT + 4 + 4 * 2^tl < 2^47 ->
  (ST + 16 <= BD \/ BD + 40 <= ST) -> (ST + 16 <= DT + 4 \/ DT + 4 + 4 * 2^tl <= ST) -> (BD + 40 <= DT + 4 \/ DT + 4 + 4 * 2^tl <= BD) ->
  evt usegs (fse_dsym_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ST BD SRC DT tl bc ptr cont pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 BD) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition fse_dsymf_stmt : Prop := fse_dsym_stmt_at PFSE_DSYMF 1.
Definition fse_dsym_stmt : Prop := forall fast, fse_dsym_stmt_at PFSE_DSYM fast.

Theorem fse_dsym_proof : fse_dsym_stmt.
Proof.
  unfold fse_dsym_stmt, fse_dsym_stmt_at, PFSE_DSYM. intros fast. intros until tb.
  intros MI STC SR BDC BCR CELB TBLEN TBBY TBOK FR01 TLR A1 A2 R1 R2 R3 R4 R5 R6 D1 D2 D3.
  unfold bitd_cells in BDC.
  assert (MU : munch [(ST, ST + 16); (BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  pose proof (TBOK st SR) as OK. unfold fse_cell_ok in OK. cbv zeta in OK. destruct OK as (NBR & _ & NX0 & NXB).
  pose proof (sk_cell2_ro usegs m (DT + 4) tb (4 * st) CELB TBBY ltac:(lia) ltac:(lia)) as CEL.
  assert (SYR : 0 <= Znth (4 * st + 2) tb < 256) by (apply (Forall_Znth (fun v => 0 <= v < 256) tb); [exact TBBY | lia]).
  set (nb := Znth (4 * st + 3) tb) in *. set (sy := Znth (4 * st + 2) tb) in *.
  set (nx := Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb) in *.
  assert (PB : 1 <= 2^nb <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 nb ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (NXR : 0 <= nx < 4096) by lia.
  pose proof (sk_mask_ro m nb MI ltac:(lia)) as MASK. unfold FBITMASK in MASK.
  clearbody nb sy nx. clear CELB TBOK TBBY.
  kx_auto [] 120%nat
    [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5);
     KZRange st 0 4095; KZRange tl 0 12; KZRange bc 0 4096; KZRange (DT + 4 + 4 * st) 4100 (2^47);
     KZRange nb 0 12; KZRange sy 0 255; KZRange nx 0 4095; KZRange (2^nb) 1 4096;
     KZAlign ST 8; KZAlign BD 8; KZWr ST 16; KZWr BD 40; KZDisj ST 16 BD 40;
     KZDisj ST 16 (DT + 4 + 4 * st) 4; KZDisj BD 40 (DT + 4 + 4 * st) 4; KZImg 0x10000 0x14000]
    [].
  all: lazymatch goal with |- context [Z_to_bv 64 0x2c2f4] => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: apply evt_done; unfold fse_dsym_post; repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]; split; [exact STC|].
  all: lazymatch goal with |- context [Z.land ?x ((2 ^ ?k + -1) mod 2 ^ 64)] =>
         pose proof (sk_land_mask x k ltac:(lia)) as FB; set (b := Z.land x ((2 ^ k + -1) mod 2 ^ 64)) in *; clearbody b end.
  all: split; [lia|]; split; [exact BDC | lia].
Qed.

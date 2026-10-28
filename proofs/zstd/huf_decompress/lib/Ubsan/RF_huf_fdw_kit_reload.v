From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_y4_kit_reload.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition PFSE_RELOAD : Z := 0x20de4.

Definition fse_reload_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (BD S : Z) (d' : bitD) (jp : list byte) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' BD (bitdz_cells S d' jp).

Definition fse_reload_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (BD S lo : Z) (bs : list Z) (d : bitD) (jp : list byte)
         (st : dstatus) (d' : bitD),
  rw_cells usegs m BD (bitdz_cells S d jp) ->
  bytes_at usegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  bitd_ok bs d -> bd_bits d <= 64 -> 8 <= bd_ptr d -> reload_dstream bs d = Ok (st, d') ->
  0 < BD -> BD mod 8 = 0 -> 8 <= S -> S + Z.max 8 (zlen bs) + 8 <= 2^64 -> (BD + 40 <= S \/ S + zlen bs <= BD) ->
  stk usegs m lo (bv_unsigned sp) -> (BD + 40 <= lo \/ bv_unsigned sp <= BD) ->
  mem_inv usegs m ->
  evt usegs (fse_reload_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc BD S d' jp lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_RELOAD) fc None m (seg_rom usegs)).

Ltac fr_step stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20e84) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      try (match goal with E1 : bv_unsigned (zx32 _) = _, E2 : Z.shiftr _ 3 = _, E3 : _ mod 2 ^ 3 = _ |- _ =>
             rewrite ?E1, ?E2, ?E3 end); zstep end).

Theorem fse_reload_proof : fse_reload_stmt.
Proof.
  unfold fse_reload_stmt, PFSE_RELOAD.
  intros until d'. intros HBD SRC BY BOK BB P8 RL R1 R2 R3 R4 DJ STK SPD MI.
  destruct d as [c bc p z]. unfold bitd_ok in BOK. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  destruct BOK as (BC & BB0 & BP0 & BPE & BSM & BZ).
  assert (Z0 : z = false) by (destruct z; [specialize (BZ eq_refl); lia | reflexivity]). subst z.
  set (n := zlen bs) in *. assert (ELn : zlen bs = n) by reflexivity.
  assert (NB : 16 <= n /\ Z.max 8 n = n) by lia. destruct NB as (N16 & NMX). rewrite NMX in *.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  replace (64 <? bc) with false in RL by (symmetry; apply Z.ltb_ge; lia).
  replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
  unfold bitdz_cells in HBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in HBD.
  pose proof (munch_refl [(BD, BD + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  fr_step 0.
  assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
  destruct QR as (q & r & -> & Q1 & Q2).
  assert (ESH0 : Z.shiftr (8 * q + r) 3 = q) by (apply y4_sh; lia).
  rewrite ESH0 in RL. rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
  pose proof (y4_zx q r ltac:(lia) ltac:(lia)) as EZX.
  pose proof (y4_sh q r ltac:(lia) ltac:(lia)) as ESH.
  pose proof (y4_md q r ltac:(lia) ltac:(lia)) as EMD.
  repeat (fr_step 0x20e24; brk; try (exfalso; lia)).
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x20e24) _ _ ?mg _) =>
    pose proof (src_rd usegs mg S bs (p - q + 0) SRC ltac:(lia)) as B0;
    pose proof (src_rd usegs mg S bs (p - q + 1) SRC ltac:(lia)) as B1;
    pose proof (src_rd usegs mg S bs (p - q + 2) SRC ltac:(lia)) as B2;
    pose proof (src_rd usegs mg S bs (p - q + 3) SRC ltac:(lia)) as B3;
    pose proof (src_rd usegs mg S bs (p - q + 4) SRC ltac:(lia)) as B4;
    pose proof (src_rd usegs mg S bs (p - q + 5) SRC ltac:(lia)) as B5;
    pose proof (src_rd usegs mg S bs (p - q + 6) SRC ltac:(lia)) as B6;
    pose proof (src_rd usegs mg S bs (p - q + 7) SRC ltac:(lia)) as B7
  | |- _ => idtac end.
  all: repeat (fr_step 0; brk; try (exfalso; lia)).
  all: fr_step 0.
  all: apply evt_done; unfold fse_reload_post, bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero].
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: lazymatch goal with
    H : rw_cells usegs ?mm _ (C8 (Z_to_bv 64 ?w) :: C4 _ :: _) |- rw_cells usegs ?mm _ (C8 (Z_to_bv 64 ?v) :: _) =>
      replace v with w by (rewrite le64_lbu_raw by (apply byte_Znth; [exact BY | lia]); rewrite Z.add_0_r; reflexivity);
      rewrite EMD in H; replace (S + p - q) with (S + (p - q)) in H by lia;
      replace (Z.land (8 * q + r) 7) with r
        by (change (Z.land (8 * q + r) 7) with (Z.land (8 * q + r) (Z.ones 3)); rewrite Z.land_ones by lia;
            symmetry; exact EMD);
      exact H
  end.
Qed.

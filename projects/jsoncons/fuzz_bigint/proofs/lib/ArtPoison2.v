(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.GcFlush06.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import muslA.As0SumsMemset_code muslA.As0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_60f64_615b0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ArtPoison ArtPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma art_poison_hi0_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x16f668 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x60f78 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0xcbb2c)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0xcbb2c : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_60f78 D_60f78.
  zsd F_60f7c D_60f7c (sp - 8) (U raw) ltac:(rewok W).
  zsd F_60f80 D_60f80 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_60f84 D_60f84 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_60f88 D_60f88 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_60f8c D_60f8c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_60f90 D_60f90 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_60f94 D_60f94 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
  assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
  destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
  destruct (Z.eq_dec v 0) as [V0|V1].
  (* [comment removed for export] *)
  - zbtk F_60f98 D_60f98.
    stepn F_60fac D_60fac. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_60fb0 D_60fb0.
  zstep F_60fb4 D_60fb4.
  zld F_60fb8 D_60fb8 0xd58b8 G48.
  zld F_60fbc D_60fbc 0xddb38 Csb. unfold SB in *.
  zstep F_60fc0 D_60fc0. zstep F_60fc4 D_60fc4. zstep F_60fc8 D_60fc8.
  zstep F_60fcc D_60fcc.
  zbft F_60fd0 D_60fd0.
  zstep F_60fd4 D_60fd4. zld F_60fd8 D_60fd8 0xd58c0 G50.
  zstep F_60fdc D_60fdc. zld F_60fe0 D_60fe0 0xd58c8 G58.
  zld F_60fe4 D_60fe4 0xde828 Cmb. zld F_60fe8 D_60fe8 0xde830 Cme.
  zstep F_60fec D_60fec.
  zbtk F_60ff0 D_60ff0.
  zstep F_60ff8 D_60ff8. zld F_60ffc D_60ffc 0xd58d0 G60. zld F_61000 D_61000 0xde820 Che.
  zstep F_61004 D_61004.
  zstep F_61008 D_61008.
  zbft F_6100c D_6100c.
  zbtk F_61010 D_61010.
  zld F_610d8 D_610d8 0xde820 Che.
  zstep F_610dc D_610dc.
  zstep F_610e0 D_610e0.
  zbft F_610e4 D_610e4.
  zbtk F_610e8 D_610e8.
  stepn F_611a8 D_611a8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_611ac D_611ac.
  zstep F_611b0 D_611b0. zstep F_611b4 D_611b4.
  zbft F_611b8 D_611b8.
  zstep F_611bc D_611bc. zld F_611c0 D_611c0 0xd58c0 G50.
  zstep F_611c4 D_611c4. zld F_611c8 D_611c8 0xd58c8 G58.
  zld F_611cc D_611cc 0xde828 Cmb. zld F_611d0 D_611d0 0xde830 Cme.
  zstep F_611d4 D_611d4.
  zbtk F_611d8 D_611d8.
  zstep F_611e0 D_611e0. zld F_611e4 D_611e4 0xd58d0 G60. zld F_611e8 D_611e8 0xde820 Che.
  zstep F_611ec D_611ec.
  zstep F_611f0 D_611f0.
  zbft F_611f4 D_611f4.
  zbft F_611f8 D_611f8.
  zstep F_611fc D_611fc. zld F_61200 D_61200 0xd58d8 G68. zld F_61204 D_61204 0xd7818 Crm.
  zbft F_61208 D_61208.
  stepn F_6120c D_6120c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61210 D_61210. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61214 D_61214. zstep F_61218 D_61218. zstep F_6121c D_6121c.
    zbft F_61220 D_61220.
    zstep F_61224 D_61224. zld F_61228 D_61228 0xd58a8 G38. zld F_6122c D_6122c (0x16f668 + 120) Cth.
    zbtk F_61230 D_61230.
    zstep F_612e0 D_612e0. stepn F_612e4 D_612e4.
  zstep F_612f0 D_612f0.
  zld F_612f4 D_612f4 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_612f8 D_612f8 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_612fc D_612fc (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61300 D_61300 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61304 D_61304 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61308 D_61308 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6130c D_6130c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61310 D_61310.
  stepjr F_61314 D_61314 (0xcbb2c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.
  (* [comment removed for export] *)
  - zbft F_60f98 D_60f98.
    zstep F_60f9c D_60f9c.
    zlb F_60fa0 D_60fa0 0xdd39c Ccp.
    stepfence F_60fa4 D_60fa4.
    zbft F_60fa8 D_60fa8.
    stepn F_60fac D_60fac. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_60fb0 D_60fb0.
  zstep F_60fb4 D_60fb4.
  zld F_60fb8 D_60fb8 0xd58b8 G48.
  zld F_60fbc D_60fbc 0xddb38 Csb. unfold SB in *.
  zstep F_60fc0 D_60fc0. zstep F_60fc4 D_60fc4. zstep F_60fc8 D_60fc8.
  zstep F_60fcc D_60fcc.
  zbft F_60fd0 D_60fd0.
  zstep F_60fd4 D_60fd4. zld F_60fd8 D_60fd8 0xd58c0 G50.
  zstep F_60fdc D_60fdc. zld F_60fe0 D_60fe0 0xd58c8 G58.
  zld F_60fe4 D_60fe4 0xde828 Cmb. zld F_60fe8 D_60fe8 0xde830 Cme.
  zstep F_60fec D_60fec.
  zbtk F_60ff0 D_60ff0.
  zstep F_60ff8 D_60ff8. zld F_60ffc D_60ffc 0xd58d0 G60. zld F_61000 D_61000 0xde820 Che.
  zstep F_61004 D_61004.
  zstep F_61008 D_61008.
  zbft F_6100c D_6100c.
  zbtk F_61010 D_61010.
  zld F_610d8 D_610d8 0xde820 Che.
  zstep F_610dc D_610dc.
  zstep F_610e0 D_610e0.
  zbft F_610e4 D_610e4.
  zbtk F_610e8 D_610e8.
  stepn F_611a8 D_611a8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_611ac D_611ac.
  zstep F_611b0 D_611b0. zstep F_611b4 D_611b4.
  zbft F_611b8 D_611b8.
  zstep F_611bc D_611bc. zld F_611c0 D_611c0 0xd58c0 G50.
  zstep F_611c4 D_611c4. zld F_611c8 D_611c8 0xd58c8 G58.
  zld F_611cc D_611cc 0xde828 Cmb. zld F_611d0 D_611d0 0xde830 Cme.
  zstep F_611d4 D_611d4.
  zbtk F_611d8 D_611d8.
  zstep F_611e0 D_611e0. zld F_611e4 D_611e4 0xd58d0 G60. zld F_611e8 D_611e8 0xde820 Che.
  zstep F_611ec D_611ec.
  zstep F_611f0 D_611f0.
  zbft F_611f4 D_611f4.
  zbft F_611f8 D_611f8.
  zstep F_611fc D_611fc. zld F_61200 D_61200 0xd58d8 G68. zld F_61204 D_61204 0xd7818 Crm.
  zbft F_61208 D_61208.
  stepn F_6120c D_6120c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61210 D_61210. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61214 D_61214. zstep F_61218 D_61218. zstep F_6121c D_6121c.
    zbtk F_61220 D_61220.
    zstep F_612e0 D_612e0. stepn F_612e4 D_612e4.
  zstep F_612f0 D_612f0.
  zld F_612f4 D_612f4 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_612f8 D_612f8 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_612fc D_612fc (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61300 D_61300 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61304 D_61304 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61308 D_61308 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6130c D_6130c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61310 D_61310.
  stepjr F_61314 D_61314 (0xcbb2c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

Theorem art_poison_hi0_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x16f668 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x60f78 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr Wsh.
  pose proof (art_poison_hi0_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0xcbb2c : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma art_poison_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x16f668 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x60f78 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 raw) 2 (Z_to_bv 64 sp)) 6 (Z_to_bv 64 0xcbb2c)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8)))
             13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 (SB - 1))) 15 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
       (0xcbb2c : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  zstep F_60f78 D_60f78.
  zsd F_60f7c D_60f7c (sp - 8) (U raw) ltac:(rewok W).
  zsd F_60f80 D_60f80 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_60f84 D_60f84 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_60f88 D_60f88 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_60f8c D_60f8c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_60f90 D_60f90 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_60f94 D_60f94 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
  assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
  destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
  destruct (Z.eq_dec v 0) as [V0|V1].
  - zbtk F_60f98 D_60f98.
    stepn F_60fac D_60fac. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_60fb0 D_60fb0.
  zstep F_60fb4 D_60fb4.
  zld F_60fb8 D_60fb8 0xd58b8 G48.
  zld F_60fbc D_60fbc 0xddb38 Csb. unfold SB in *.
  zstep F_60fc0 D_60fc0. zstep F_60fc4 D_60fc4. zstep F_60fc8 D_60fc8.
  zstep F_60fcc D_60fcc.
  zbtk F_60fd0 D_60fd0.
  stepn F_611a8 D_611a8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_611ac D_611ac.
  zstep F_611b0 D_611b0. zstep F_611b4 D_611b4.
  zbtk F_611b8 D_611b8.
  zstep F_611fc D_611fc. zld F_61200 D_61200 0xd58d8 G68. zld F_61204 D_61204 0xd7818 Crm.
  zbft F_61208 D_61208.
  stepn F_6120c D_6120c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61210 D_61210. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61214 D_61214. zstep F_61218 D_61218. zstep F_6121c D_6121c.
    zbft F_61220 D_61220.
    zstep F_61224 D_61224. zld F_61228 D_61228 0xd58a8 G38. zld F_6122c D_6122c (0x16f668 + 120) Cth.
    zbtk F_61230 D_61230.
    zstep F_612e0 D_612e0. stepn F_612e4 D_612e4.
  zstep F_612f0 D_612f0.
  zld F_612f4 D_612f4 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_612f8 D_612f8 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_612fc D_612fc (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61300 D_61300 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61304 D_61304 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61308 D_61308 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6130c D_6130c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61310 D_61310.
  stepjr F_61314 D_61314 (0xcbb2c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. subst v. zret.
  - zbft F_60f98 D_60f98.
    zstep F_60f9c D_60f9c.
    zlb F_60fa0 D_60fa0 0xdd39c Ccp.
    stepfence F_60fa4 D_60fa4.
    zbft F_60fa8 D_60fa8.
    stepn F_60fac D_60fac. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_60fb0 D_60fb0.
  zstep F_60fb4 D_60fb4.
  zld F_60fb8 D_60fb8 0xd58b8 G48.
  zld F_60fbc D_60fbc 0xddb38 Csb. unfold SB in *.
  zstep F_60fc0 D_60fc0. zstep F_60fc4 D_60fc4. zstep F_60fc8 D_60fc8.
  zstep F_60fcc D_60fcc.
  zbtk F_60fd0 D_60fd0.
  stepn F_611a8 D_611a8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_611ac D_611ac.
  zstep F_611b0 D_611b0. zstep F_611b4 D_611b4.
  zbtk F_611b8 D_611b8.
  zstep F_611fc D_611fc. zld F_61200 D_61200 0xd58d8 G68. zld F_61204 D_61204 0xd7818 Crm.
  zbft F_61208 D_61208.
  stepn F_6120c D_6120c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61210 D_61210. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61214 D_61214. zstep F_61218 D_61218. zstep F_6121c D_6121c.
    zbtk F_61220 D_61220.
    zstep F_612e0 D_612e0. stepn F_612e4 D_612e4.
  zstep F_612f0 D_612f0.
  zld F_612f4 D_612f4 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_612f8 D_612f8 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_612fc D_612fc (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61300 D_61300 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61304 D_61304 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61308 D_61308 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6130c D_6130c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61310 D_61310.
  stepjr F_61314 D_61314 (0xcbb2c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. zret.
Qed.

Theorem art_poison_lo_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x16f668 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x60f78 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
  pose proof (art_poison_lo_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0xcbb2c : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_poison_lo_ok (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_ok (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.

Theorem art_poison_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x16f668 256 ->
  art_layout M ->
  (art_poison_lo_ok p n \/ art_poison_hi_ok p n) -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x60f78 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L [Hl|Hh] Hp8 Hn8 Hn Hv Hthr Wsh.
  - destruct Hl as (Ha & Hb & Hc). exact (art_poison_lo_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hb Hc Hp8 Hn8 Hn Hv Hthr Wsh).
  - destruct Hh as (Ha & Hb & Hc & Hd). exact (art_poison_hi0_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hd Hp8 Hn8 Hn Hb Hc Hv Hthr Wsh).
Qed.
End FPX.

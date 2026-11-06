(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require ZBridge.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit
  R_small R_m2s R_thread I_consts I_qck I_ikit F_atof_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition F_STRCHR : Z := 0x50fc4.
Definition ISTRCHR_DEPTH : Z := 2224.
Definition LITSEPS : Z := 0x26120.
(* [comment removed for export] *)
Definition schr_res (c : Z) : Z :=
  if c =? 32 then LITSEPS else if c =? 9 then LITSEPS + 1 else if c =? 10 then LITSEPS + 2 else if c =? 44 then LITSEPS + 3 else 0.

(* [comment removed for export] *)
Definition icells_schr (m : mem) : Prop :=
  ro_cells asegs m 0xeb9d0 [C8 (Z_to_bv 64 0x189168)]          (* [comment removed for export] *)
  /\ ro_cells asegs m 0xeb9e0 [C8 (Z_to_bv 64 0xf7638)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xed758 [C8 (Z_to_bv 64 0xe2214)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xf7638 [C8 (Z_to_bv 64 0x7fff8000)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0xf8318 [C1 (Z_to_bv 8 1)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0x18925d [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
  /\ ro_cells asegs m 0x189265 [C1 (Z_to_bv 8 1)].             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEPS_SHB : Z := shad LITSEPS.
Definition SEPS_SHW : Z := al8 (shad LITSEPS).

(* [comment removed for export] *)
Definition istrchr_stmt (c len res : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (w1 : word) (b : byte),
  icells_schr m ->
  ro_cells asegs m SEPS_SHW [C8 w1] -> bytes_at asegs m SEPS_SHB [b] -> sh_ok b (LITSEPS + len) ->
  mem_inv asegs m -> stk asegs m lo usp ->
  lo + ISTRCHR_DEPTH <= usp -> usp <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res [(usp - ISTRCHR_DEPTH, usp)] lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LITSEPS) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 F_STRCHR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land255 : forall c, 0 <= c <= 255 -> Z.land c 255 = c.
Proof. intros c H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia. Qed.

(* [comment removed for export] *)
Lemma shb_pass : forall (b : byte) (a L : Z), sh_ok b a -> L = a mod 8 + 9223372036854775808 ->
  Z.land (Z.land (Z.b2z (0 <? bv_unsigned (sxb b)))
                 (Z.lxor (Z.b2z (L <? Z.lxor (bv_unsigned (sxb b)) 9223372036854775808)) 1)) 255 = 0.
Proof.
  intros b a L SOK ->. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as AR.
  destruct SOK as [Z0 | (R & LT)].
  - rewrite (sxb_small b) by lia. rewrite Z0. reflexivity.
  - rewrite (sxb_small b) by lia. rewrite unsigned_lit by lia.
    change 9223372036854775808 with (2^63). rewrite (ZBridge.zb_lxor_pow2_small (bv_unsigned b) 63) by lia.
    replace (0 <? bv_unsigned b) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (a mod 8 + 2^63 <? bv_unsigned b + 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac schr_intro :=
  unfold istrchr_stmt; intros until b;
  let IC := fresh "IC" in let SW := fresh "SW" in let SB := fresh "SB" in let SOK := fresh "SOK" in let MI := fresh "MI" in
  let ST := fresh "ST" in let LO := fresh "LO" in let UHI := fresh "UHI" in let SAL := fresh "SAL" in let LOH := fresh "LOH" in
  intros IC SW SB SOK MI ST LO UHI SAL LOH;
  destruct IC as (G1 & G2 & RS & SH & AI & SSC & ISC);
  pose proof (ro_C1_of_bytes _ _ _ SB) as SBC;
  (let v := eval vm_compute in SEPS_SHB in change SEPS_SHB with v in * );
  (let v := eval vm_compute in SEPS_SHW in change SEPS_SHW with v in * );
  unfold F_STRCHR, ISTRCHR_DEPTH, LITSEPS in *;
  lazymatch goal with STx : stk asegs ?m _ ?usp |- _ =>
    pose proof (munch_refl [(usp - 2224, usp)] m) as MU; pose proof (wmono_refl asegs m) as WM end.
(* [comment removed for export] *)
Ltac schr_end :=
  finish;
  lazymatch goal with STx : stk asegs _ _ ?usp |- stk asegs _ _ (bv_unsigned (Z_to_bv 64 ?usp)) =>
    rewrite unsigned_lit by (destruct STx as [? _]; lia); exact STx end.
(* [comment removed for export] *)
Ltac shb_fix :=
  lazymatch goal with
  | SOKx : sh_ok ?b ?a |- context [Z.land (Z.land (Z.b2z (0 <? bv_unsigned (sxb ?b)))
                                                 (Z.lxor (Z.b2z (?L <? Z.lxor (bv_unsigned (sxb ?b)) 9223372036854775808)) 1)) 255] =>
      rewrite (shb_pass b a L SOKx eq_refl)
  end.
(* [comment removed for export] *)
Ltac schr_tail :=
  rewrite Z.lor_diag;
  let K := fresh "K" in brfork K;
  [ cwalk (@nil Z); shb_fix; cwalk (@nil Z); schr_end
  | cwalk (@nil Z); schr_end ].

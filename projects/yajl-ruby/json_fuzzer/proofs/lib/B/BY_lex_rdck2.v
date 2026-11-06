(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rdck_tac_b :=
  intros;
  lazymatch goal with
  | BS : u8arr _ _ _ ?shb, E : ?shb = blk_shadow ?On, PL : pol _ _ _, HE : ?A + 1 <= _ + ?On' |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      unfold pol in PL;
      let L := fresh "BSlen" in pose proof (blk_shadow_length On ltac:(lia)) as L; rewrite <- E in L;
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl bsegs m) as WM;
      let HR := fresh "SHR" in let k := fresh "k" in let HK := fresh "HK" in
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?OA / 8) _ =>
          destruct (block_shadow_read_u segs m SB OA On A 1) as (k & HR & HK); [lia|lia|rewrite <- E; exact BS|lia|lia|lia|lia|]
      end;
      zstepA; shadow_addr; zstepA; zstepA; clear HR;
      destruct HK as [-> | HK];
      [ rewrite ?zxb_small, ?sxb_small by lia; zstepA; if_true; apply evtA_done; eexists _, _; reflexivity
      | rewrite ?zxb_small, ?sxb_small by lia; zstepA;
        (let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc; [ exfalso; lia | clear Kc ]);
        stepA;                                                   (* [comment removed for export] *)
        zstepA; change 7 with (Z.ones 3); rewrite ?Z.land_ones by lia; change (2^3) with 8;   (* [comment removed for export] *)
        zstepA;                                                  (* [comment removed for export] *)
        (let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc;
         [ exfalso; revert Kc; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intro Kc; lia | clear Kc ]);
        stepA;                                                   (* [comment removed for export] *)
        apply evtA_done; eexists _, _; reflexivity ]
  end.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rdck_10a5c8 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 539984) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 539964) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac_b. Qed.

Lemma rdck_10a880 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 540812) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 540792) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac_b. Qed.

Lemma rdck_b853f8 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 545836) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 545816) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac_b. Qed.

End RC__1.

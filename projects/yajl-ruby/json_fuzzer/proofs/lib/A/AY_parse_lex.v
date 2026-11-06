(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_parse_kit AY_parse_head.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition lex_site (pc : Z) : Prop := pc = 0x8759c \/ pc = 0x87684 \/ pc = 0x87758 \/ pc = 0x87820 \/ pc = 0x878e8.
Lemma lex_site_state : forall st, lex_state st = true -> lex_site (state_targetA st).
Proof. aceil. intros [] H; try discriminate H; unfold lex_site; cbn; tauto. Qed.

(* [comment removed for export] *)
Lemma lex_site_seg : forall (P : acc -> Prop) (pc : Z) (sp gp tp rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s4v s5v t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H SQ ff T len Lv : Z) (k0 k224 : list byte) (shH : list byte)
    (w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word),
  lex_site pc ->
  rw_cells asegs m SQ
     [CB 24 k0; C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 9223372036854775809); C8 (Z_to_bv 64 ff);
      C8 (Z_to_bv 64 ((H + 32) / 8 + 2147450880)); C8 (Z_to_bv 64 0x21d00); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (H + 40));
      C8 (Z_to_bv 64 ((H + 8) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 8)); C8 (Z_to_bv 64 ((H + 24) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 24));
      C8 (Z_to_bv 64 AY_JT_PTOK); C8 (Z_to_bv 64 (H / 8 + 2147450880)); C8 (Z_to_bv 64 H); C8 (Z_to_bv 64 ((H + 56) / 8 + 2147450880));
      C8 (Z_to_bv 64 (H + 56)); C8 (Z_to_bv 64 ((H + 16) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 16)); C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 len);
      C8 (Z_to_bv 64 (H + 32)); C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 (ff + 64)); C8 (Z_to_bv 64 (H + 48)); CB 8 k224; C8 (Z_to_bv 64 ff)] ->
  rw_cells asegs m H [C8 w0; C8 w1; C8 (Z_to_bv 64 Lv); C8 w3; C4 w4; C4 w5; C8 w6; C8 w7; C4 w8; C4 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14] ->
  True ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 ->
  0 <= SQ -> SQ + 240 <= 2^47 ->
  u8arr asegs m (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  pol P SQ (SQ + 240) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) -> pol P H (H + 104) ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 (pc + 48)) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ)
                   (Z_to_bv 64 Lv) (Z_to_bv 64 T) (Z_to_bv 64 len) (Z_to_bv 64 (H + 32)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 64)) a6 a7
                   s2v (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
                   (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AY_LEX_LEX) fc None m (seg_rom asegs))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             s2v (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until w14. intros SITE FR HC _ HR1 HR2 HR3 SQ0 SQH SHH SHHeq PSTK PHS PH.
  unfold pol, AY_JT_PSTATE, AY_JT_PTOK, AY_LEX_LEX in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as SHHlen. rewrite <- SHHeq in SHHlen.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : ov_read_bytes asegs m (Z_to_bv 64 ((H + 16) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
  { replace ((H + 16) / 8 + 2147450880) with (2147450880 + (H + 16) / 8) by lia.
    apply (block_shadow_read0_u asegs m 2147450880 H 104 (H + 16) 8); [lia| lia| rewrite <- SHHeq; exact SHH| lia| lia| lia| lia]. }
  destruct SITE as [-> | [-> | [-> | [-> | ->]]]];
    (zstepA; zstepA; clear SHR; rewrite ?zxb_small, ?sxb_small by lia; zstepA; if_true;
     zstepA; zstepA; do 5 zstepA; zstepA; apply evtA_done; reflexivity).
Qed.

End RC__1.

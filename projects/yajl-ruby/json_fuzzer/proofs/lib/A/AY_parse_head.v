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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsParse.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_parse_kit.
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
Lemma head_dispatch : forall (P : acc -> Prop) (sp gp tp rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H SQ ff SBK : Z) (st : ystate) (rest : list ystate) (size : Z) (junk shH shS : list byte)
    (w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 : word),
  mem_inv asegs m ->
  rw_cells asegs m H [C8 w0; C8 w1; C8 w2; C8 w3; C4 w4; C4 w5; C8 w6; C8 (Z_to_bv 64 SBK); C4 w8; C4 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14] ->
  True ->
  rw_cells asegs m SBK [CB (Z.to_nat (zlength rest + 1)) (zbytes (stack_bytes (st :: rest))); CB (Z.to_nat (size - (zlength rest + 1))) junk] ->
  zlength rest + 1 <= size -> size mod 8 = 0 -> size < 2^31 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 ->
  (6303744 <= SBK /\ (SBK + size <= 2147446784 \/ 17594333495296 <= SBK)) -> SBK + size <= alloc_ceiling -> SBK mod 16 = 0 ->
  u8arr asegs m (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  u8arr asegs m (2147450880 + SBK / 8) shS -> shS = blk_shadow size ->
  pol P 0x10000 0x603000 -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) -> pol P H (H + 104) ->
  pol P SBK (SBK + size) -> pol P (2147450880 + SBK / 8) (2147450880 + SBK / 8 + (size + 7) / 8) ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 (Z_to_bv 64 (H + 48)) sp (Z_to_bv 64 SQ) (Z_to_bv 64 (state_targetA st)) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 11) (Z_to_bv 64 (H + 64)) s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
                   (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 (state_targetA st)) fc None m (seg_rom asegs))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 (Z_to_bv 64 (H + 48)) sp (Z_to_bv 64 SQ) (Z_to_bv 64 (zlength rest + 1)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (H + 64)) (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AY_PHEAD) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until w14. intros MI HC _ SC USZ SZ8 SZB HR1 HR2 HR3 SB1 SB2 SB3 SHH SHHeq SHS SHSeq PIMG PHS PH PSB PSBs.
  unfold pol, AY_PHEAD, AY_JT_PSTATE in *.
  assert (U0 : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (blk_shadow_length 104 ltac:(lia)) as SHHlen. rewrite <- SHHeq in SHHlen.
  pose proof (blk_shadow_length size ltac:(lia)) as SHSlen. rewrite <- SHSeq in SHSlen.
  pose proof (rw_cells_bound _ _ _ _ SC) as SCB. cbn [cells_size csize Nat.add] in SCB.
  pose proof (state_code_range st) as CR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (SHR : ov_read_bytes asegs m (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
  { replace ((H + 48) / 8 + 2147450880) with (2147450880 + (H + 48) / 8) by lia.
    apply (block_shadow_read0_u asegs m 2147450880 H 104 (H + 48) 8); [lia| lia| rewrite <- SHHeq; exact SHH| lia| lia| lia| lia]. }
  zstepA. clear SHR. rewrite ?zxb_small, ?sxb_small by lia.
  zstepA. if_true.
  (* [comment removed for export] *)
  zstepA.
  zstepA. zstepA. zstepA. rewrite land_M32_small by lia. zstepA.
  (* [comment removed for export] *)
  assert (SHR : ov_read_bytes asegs m (Z_to_bv 64 ((SBK + zlength rest) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
  { replace ((SBK + zlength rest) / 8 + 2147450880) with (2147450880 + (SBK + zlength rest) / 8) by lia.
    apply (block_shadow_read0_u asegs m 2147450880 SBK size (SBK + zlength rest) 1); [lia| lia| rewrite <- SHSeq; exact SHS| lia| lia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]. }
  replace (SBK + (zlength rest + 1 + -1)) with (SBK + zlength rest) by lia.
  zstepA. shadow_addr. zstepA. zstepA. clear SHR. rewrite ?zxb_small, ?sxb_small by lia.
  zstepA. if_true.
  (* [comment removed for export] *)
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  pose proof (u8arr_read asegs m SBK _ (zlength rest) (Z_to_bv 8 (state_code st)) _ ARR ltac:(apply stack_top_byte) ltac:(lia) eq_refl) as RK.
  change (wa (SBK + zlength rest)) with (Z_to_bv 64 (SBK + zlength rest)) in RK.
  zstepA. clear RK. cbv beta. rewrite (u8_val (state_code st)) by lia.
  (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; lia].
  (* [comment removed for export] *)
  zstepA.
  pose proof (jt_pstate_read_bs m st MI) as RD. unfold AY_JT_PSTATE in RD.
  destruct st; cbn [state_code state_targetA jt_pstate_bs] in RD |- *;
    match type of RD with context [wa ?a] => let a' := eval vm_compute in a in replace a with a' in RD by reflexivity end;
    (zstepA; zstepA; zstepA; clear RD; zstepA; zstepA; zstepA; apply evtA_done; reflexivity).
Qed.
End RC__1.

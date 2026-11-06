(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GX/G_vsnprintf.v, with its module paths, module names, addresses and numbers changed; 558 of its 649 lines of code are new or changed and 207 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import G_towrite.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition vfprintf_prog (B got_ssp B_printf_core B_lockfile B_towrite B_unlockfile B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 200%Z
    (PNode 80%Z
      (PNode 40%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 0 2 2 3728 4
            (PJ_Store_SZ8_nnn 4 2 1 360 4
            (PJ_Store_SZ8_nnn 8 2 8 352 4
            (PJ_Store_SZ8_nnn 12 2 9 344 4
            (PJ_Store_SZ8_nnn 16 2 18 336 4
            (PJ_Store_SZ8_nnn 20 2 19 328 4
            (PJ_Store_SZ8_nnn 24 2 20 320 4
            (PJ_Store_SZ8_nnn 28 2 21 312 4
            (PJ_OpImm_ALU_ADD_nnn 32 9 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 36 8 10 0 4 nil)))))))))))
        (PLeaf
            (PJ_Auipc_nt 40 10 (hi20 (got_ssp - (B + 40))) 4
            (PJ_Load_SZ8_true_nnt 44 18 10 (lo12 (got_ssp - (B + 40))) 4
            (PJ_Load_SZ8_true_nnn 48 10 18 0 4
            (PJ_Store_SZ8_nnn 52 2 10 304 4
            (PJ_Store_SZ8_nnn 56 2 12 8 4
            (PJ_Store_SZ8_nnn 60 2 0 296 4
            (PJ_Store_SZ8_nnn 64 2 0 264 4
            (PJ_Store_SZ8_nnn 68 2 0 272 4
            (PJ_Store_SZ8_nnn 72 2 0 280 4
            (PJ_Store_SZ8_nnn 76 2 0 288 4 nil))))))))))))
      (PNode 120%Z
        (PLeaf
            (PJ_Store_SZ8_nnn 80 2 12 0 4
            (PJ_OpImm_ALU_ADD_nnn 84 12 2 0 4
            (PJ_OpImm_ALU_ADD_nnn 88 13 2 96 4
            (PJ_OpImm_ALU_ADD_nnn 92 14 2 264 4
            (PJ_OpImm_ALU_ADD_nnn 96 10 0 0 4
            (PJ_Jal_nt 100 1 (jimm21 (B_printf_core - (B + 100))) 4
            (PJ_Branch_BC_LT_nnn 104 10 0 28 4
            (PJ_Load_SZ4_true_nnn 108 10 8 140 4
            (PJ_Branch_BC_LT_nnn 112 10 0 28 4
            (PJ_OpImm_ALU_ADD_nnn 116 10 8 0 4 nil)))))))))))
        (PNode 160%Z
          (PLeaf
              (PJ_Jal_nt 120 1 (jimm21 (B_lockfile - (B + 120))) 4
              (PJ_OpImm_ALU_SLTU_nnn 124 19 10 1 4
              (PJ_Jal_nn 128 0 16 4
              (PJ_OpImm_ALU_ADD_nnn 132 10 0 4095 4
              (PJ_Jal_nn 136 0 244 4
              (PJ_OpImm_ALU_ADD_nnn 140 19 0 1 4
              (PJ_Load_SZ4_true_nnn 144 21 8 0 4
              (PJ_Load_SZ8_true_nnn 148 10 8 96 4
              (PJ_OpImm_ALU_AND_nnn 152 11 21 4063 4
              (PJ_Store_SZ4_nnn 156 8 11 0 4 nil)))))))))))
          (PLeaf
              (PJ_Branch_BC_EQ_nnn 160 10 0 20 4
              (PJ_Load_SZ8_true_nnn 164 10 8 32 4
              (PJ_OpImm_ALU_ADD_nnn 168 20 0 0 4
              (PJ_Branch_BC_NE_nnn 172 10 0 68 4
              (PJ_Jal_nn 176 0 36 4
              (PJ_Load_SZ8_true_nnn 180 20 8 88 4
              (PJ_OpImm_ALU_ADD_nnn 184 10 2 16 4
              (PJ_Store_SZ8_nnn 188 8 0 32 4
              (PJ_Store_SZ8_nnn 192 8 0 40 4
              (PJ_Store_SZ8_nnn 196 8 0 56 4 nil))))))))))))))
    (PNode 320%Z
      (PNode 240%Z
        (PLeaf
            (PJ_Store_SZ8_nnn 200 8 10 88 4
            (PJ_OpImm_ALU_ADD_nnn 204 10 0 80 4
            (PJ_Store_SZ8_nnn 208 8 10 96 4
            (PJ_OpImm_ALU_ADD_nnn 212 10 8 0 4
            (PJ_Jal_nt 216 1 (jimm21 (B_towrite - (B + 216))) 4
            (PJ_Branch_BC_EQ_nnn 220 10 0 20 4
            (PJ_OpImm_ALU_ADD_nnn 224 9 0 4095 4
            (PJ_OpImm_ALU_AND_nnn 228 21 21 32 4
            (PJ_Branch_BC_NE_nnn 232 20 0 44 4
            (PJ_Jal_nn 236 0 96 4 nil)))))))))))
        (PNode 280%Z
          (PLeaf
              (PJ_OpImm_ALU_ADD_nnn 240 12 2 0 4
              (PJ_OpImm_ALU_ADD_nnn 244 13 2 96 4
              (PJ_OpImm_ALU_ADD_nnn 248 14 2 264 4
              (PJ_OpImm_ALU_ADD_nnn 252 10 8 0 4
              (PJ_OpImm_ALU_ADD_nnn 256 11 9 0 4
              (PJ_Jal_nt 260 1 (jimm21 (B_printf_core - (B + 260))) 4
              (PJ_OpImm_ALU_ADD_nnn 264 9 10 0 4
              (PJ_OpImm_ALU_AND_nnn 268 21 21 32 4
              (PJ_Branch_BC_EQ_nnn 272 20 0 60 4
              (PJ_Load_SZ8_true_nnn 276 13 8 72 4 nil)))))))))))
          (PLeaf
              (PJ_OpImm_ALU_ADD_nnn 280 10 8 0 4
              (PJ_OpImm_ALU_ADD_nnn 284 11 0 0 4
              (PJ_OpImm_ALU_ADD_nnn 288 12 0 0 4
              (PJ_Jalr_nnn 292 1 13 0 4
              (PJ_Load_SZ8_true_nnn 296 10 8 40 4
              (PJ_Store_SZ8_nnn 300 8 0 32 4
              (PJ_Store_SZ8_nnn 304 8 0 40 4
              (PJ_Store_SZ8_nnn 308 8 0 56 4
              (PJ_Store_SZ8_nnn 312 8 20 88 4
              (PJ_Op_ALU_SLTU_nnn 316 10 0 10 4 nil)))))))))))))
      (PNode 360%Z
        (PLeaf
            (PJ_OpImm32_nnn 320 10 10 4095 4
            (PJ_Op_ALU_OR_nnn 324 9 10 9 4
            (PJ_Store_SZ8_nnn 328 8 0 96 4
            (PJ_Load_SZ4_true_nnn 332 10 8 0 4
            (PJ_OpImm_ALU_AND_nnn 336 11 10 32 4
            (PJ_Op_ALU_OR_nnn 340 12 10 21 4
            (PJ_OpImm_ALU_SLTU_nnn 344 10 11 1 4
            (PJ_OpImm32_nnn 348 10 10 4095 4
            (PJ_Op_ALU_OR_nnn 352 10 10 9 4
            (PJ_Store_SZ4_nnn 356 8 12 0 4 nil)))))))))))
        (PNode 400%Z
          (PLeaf
              (PJ_Branch_BC_NE_nnn 360 19 0 20 4
              (PJ_OpImm_ALU_ADD_nnn 364 9 10 0 4
              (PJ_OpImm_ALU_ADD_nnn 368 10 8 0 4
              (PJ_Jal_nt 372 1 (jimm21 (B_unlockfile - (B + 372))) 4
              (PJ_OpImm_ALU_ADD_nnn 376 10 9 0 4
              (PJ_Load_SZ8_true_nnn 380 11 18 0 4
              (PJ_Load_SZ8_true_nnn 384 12 2 304 4
              (PJ_Branch_BC_NE_nnn 388 11 12 40 4
              (PJ_Load_SZ8_true_nnn 392 1 2 360 4
              (PJ_Load_SZ8_true_nnn 396 8 2 352 4 nil)))))))))))
          (PLeaf
              (PJ_Load_SZ8_true_nnn 400 9 2 344 4
              (PJ_Load_SZ8_true_nnn 404 18 2 336 4
              (PJ_Load_SZ8_true_nnn 408 19 2 328 4
              (PJ_Load_SZ8_true_nnn 412 20 2 320 4
              (PJ_Load_SZ8_true_nnn 416 21 2 312 4
              (PJ_OpImm_ALU_ADD_nnn 420 2 2 368 4
              (PJ_Jalr_nnn 424 0 1 0 4
              (PJ_Jal_nt 428 1 (jimm21 (B_stack_chk_fail - (B + 428))) 4 nil)))))))))))).
Definition vfprintf_size : Z := 432.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PROGAT_CODE_vfprintf (IMG : RImg) :=
  vfprintf_prog (sym 0x7f000400) (sym 0x22e18) (sym 0x18704) (sym 0x7f000700) (sym 0x17f40) (sym 0x7f000800) (sym 0x15f04).

Tactic Notation "callw" tactic3(tac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
  end.
Definition hideP (P : Prop) : Prop := P.
Ltac stash H := lazymatch type of H with hideP _ => idtac | ?T => change T with (hideP T) in H end.
Ltac unstash := unfold hideP in *.

Section Img.
  Context {IMG : RImg}.

Definition snf_file (bufp CK : Z) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sym K_SN_WRITE));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bufp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
   C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 CK); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition vfprintf_snf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (fjunk : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength o) N))) junkd)]
    /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (zlength o) N)); C8 (Z_to_bv 64 (N - Z.min (zlength o) N))]
    /\ rw_cells img_segs m' Fp [CB 232 fjunk].

Definition vfprintf_snf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D N OM bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells img_segs m Fp (snf_file bufp CK) ->
    rw_cells img_segs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 N)] ->
    rw_cells img_segs m D [CB dn (Z_to_bv 8 0 :: skipn 1 junkd)] -> length junkd = dn ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok Fp lo 0 CK 16 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= N < 2^63 -> 0 <= OM -> Z.min N OM < Z.of_nat dn -> 0 < bufp < 2^64 ->
    stk img_segs m lo q -> lo <= q - VF_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= STATIC_SPLIT -> 65536 <= A ->
    q <= Fp -> Fp + 232 <= CK -> CK + 16 <= VA -> CK + 16 < 2^63 -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt img_segs (vfprintf_snf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000400)) fc None m (seg_rom img_segs)).

Lemma arg_ok_rebase : forall (Fp B BS RC RCS RE RES Fp' B' BS' RC' RCS' : Z) (m m' : mem) (lo sp sp' ap ap' : Z) (w : word) (a : parg),
  arg_ok Fp B BS RC RCS RE RES m lo sp ap w a ->
  munch [(lo, sp); (Fp, Fp + 232); (RC, RC + RCS); (RE, RE + RES)] m m' ->
  sp' <= sp ->
  (lo <= Fp' /\ Fp' + 232 <= sp \/ Fp' = Fp) ->
  (lo <= B' /\ B' + BS' <= sp \/ (B' = B /\ BS' = BS)) ->
  (lo <= RC' /\ RC' + RCS' <= sp \/ (RC' = RC /\ RCS' = RCS)) ->
  (lo <= ap' /\ ap' + 8 <= sp \/ ap' = ap) ->
  arg_ok Fp' B' BS' RC' RCS' RE RES m' lo sp' ap' w a.
Proof.
  intros Fp B BS RC RCS RE RES Fp' B' BS' RC' RCS' m m' lo sp sp' ap ap' w a H MU Hsp HF HB HR HA.
  destruct a as [s|i|u|d|l]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HS & PAD & NZ & D1 & D2 & D3 & D4 & D5 & D6). exists slack.
  split.
  { eapply bytes_at_transport; [exact BY | exact MU |].
    cbn [disjoint_from]. rewrite length_app. unfold zb. rewrite length_map. cbn [length]. unfold zlength in *. lia. }
  split; [exact HS|]. split; [exact PAD|]. split; [exact NZ|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma args_ok_rebase : forall (Fp B BS RC RCS RE RES Fp' B' BS' RC' RCS' : Z) (m m' : mem) (lo sp sp' ap ap' : Z) (ws : list word) (args : list parg),
  args_ok Fp B BS RC RCS RE RES m lo sp ap ws args ->
  munch [(lo, sp); (Fp, Fp + 232); (RC, RC + RCS); (RE, RE + RES)] m m' ->
  sp' <= sp ->
  (lo <= Fp' /\ Fp' + 232 <= sp \/ Fp' = Fp) ->
  (lo <= B' /\ B' + BS' <= sp \/ (B' = B /\ BS' = BS)) ->
  (lo <= RC' /\ RC' + RCS' <= sp \/ (RC' = RC /\ RCS' = RCS)) ->
  (lo <= ap' /\ ap' + 8 <= sp \/ ap' = ap) ->
  args_ok Fp' B' BS' RC' RCS' RE RES m' lo sp' ap' ws args.
Proof.
  intros Fp B BS RC RCS RE RES Fp' B' BS' RC' RCS' m m' lo sp sp' ap ap' ws args.
  revert ws. induction args as [|a args IH]; intros ws H MU Hsp HF HB HR HA; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_rebase; eassumption | eapply IH; eassumption].
Qed.

Lemma fpcall_snf : forall (Fp B BS RC RCS RE RES : Z) (SINK : mem -> list Z -> Prop) (TOPOK : Z -> Prop) c,
  fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP_snf c.
Proof.
  intros Fp B BS RC RCS RE RES SINK TOPOK [[[[y w] p] fl] t]. cbn.
  intros. unfold implM. cbn. apply evt_done. exact I.
Qed.

Lemma fpcalls_snf : forall (Fp B BS RC RCS RE RES : Z) (SINK : mem -> list Z -> Prop) (TOPOK : Z -> Prop) cs,
  Forall (fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP_snf) cs.
Proof. intros. apply Forall_forall. intros c _. apply fpcall_snf. Qed.


Section SinkLow.
  Context {St : Type}.
  Variables (Fp B BS RC RCS RE RES : Z) (SINK : mem -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).

  Definition printf_core_low_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
           (fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
      SINK m st ->
      bytes_at img_segs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
      a0 = Z_to_bv 64 Fp ->
      rw_cells img_segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
      va_area m VA slots -> 0 <= i -> args_ok Fp B BS RC RCS RE RES m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      stk img_segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
      (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
      (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
      (bv_unsigned a2 + 8 <= B /\ B + BS <= VA) ->
      (0 <= RCS) -> (0 <= RES) ->
      (bv_unsigned a2 + 8 <= RC /\ RC + RCS <= VA) ->
      (0 < RE /\ RE + RES <= 65536 /\ 65536 <= bv_unsigned a1) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      implM img_segs (printf_model OUT OUTFP fmt args) st
            (printf_core_post Fp B BS RC RCS RE RES SINK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (sym 0x18704)) fc None m (seg_rom img_segs)).
End SinkLow.

Definition printf_core_all : Prop :=
  forall (St : Type) (Fp B BS RC RCS RE RES : Z) (SINK : mem -> St -> Prop) (TOPOK : Z -> Prop)
         (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
    sink_frame_stmt Fp B BS RC RCS RE RES SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK ->
    out_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT ->
    printf_core_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP.

Definition printf_core_low_all : Prop :=
  forall (St : Type) (Fp B BS RC RCS RE RES : Z) (SINK : mem -> St -> Prop) (TOPOK : Z -> Prop)
         (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
    sink_frame_stmt Fp B BS RC RCS RE RES SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK ->
    out_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT ->
    printf_core_low_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP.

Lemma printf_core_low_of_all : printf_core_all -> printf_core_low_all.
Proof.
  intros PC0 St Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP H1 H2 H3 H4.
  pose proof (PC0 St Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP H1 H2 H3 H4) as P.
  unfold printf_core_stmt in P. unfold printf_core_low_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary
         fmt VA i slots args
         Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q28.
  eapply P; try eassumption.
  right; right; exact Q25.
Qed.

Section SnfFlush.
  Variables (Fp : Z) (fl0 : byte) (j1 jm jr js jt jx jy : list byte) (lbfw : word)
            (B CK D : Z) (dn : nat) (junkd : list byte) (N TOP OM : Z).

  Definition snf_flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (o : list Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (bj : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom img_segs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (CK, CK + 16);
                (D, D + Z.of_nat dn)] m m'
      /\ wmono img_segs m m' /\ mem_inv img_segs m'
      /\ stk img_segs m' (bv_unsigned sp - 64) (bv_unsigned sp)
      /\ length bj = 80%nat
      /\ wfile m' Fp fl0 j1 (snf_j2 jm jr js jt B) lbfw B [] bj
      /\ rw_cells img_segs m' (Fp + 148) [CB 4 jx; C8 (Z_to_bv 64 CK); CB 72 jy]
      /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (zlength o) N)); C8 (Z_to_bv 64 (N - Z.min (zlength o) N))]
      /\ rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength o) N))) junkd)].

  Definition snf_flush_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (o : list Z),
      SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM m o ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
      stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) -> 64 <= bv_unsigned sp -> bv_unsigned sp <= TOP ->
      (D + Z.of_nat dn <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D) ->
      mem_inv img_segs m ->
      evt img_segs (snf_flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (sym K_SN_WRITE)) fc None m (seg_rom img_segs)).
End SnfFlush.

Definition snf_file2 (fl wend wpos wbase : word) (buf bufsize : Z) (mode : word) (CK : Z) : list cell :=
  [C4 fl; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 wend;
   C8 wpos; C8 (Z_to_bv 64 0); C8 wbase; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sym K_SN_WRITE));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
   C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 CK); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition snf_jz : list byte := le8 (Z_to_bv 64 0).
Definition snf_j1 : list byte :=
  [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ++ le4 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).
Definition snf_jt (mode : word) : list byte :=
  le8 (Z_to_bv 64 80) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)
  ++ le8 (Z_to_bv 64 0) ++ le4 mode ++ le4 (Z_to_bv 64 (-1)).
Definition snf_jx : list byte := le4 (Z_to_bv 64 0).
Definition snf_jy : list byte :=
  le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)
  ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).

Lemma rw_cells_recast : forall m A cs cs', rw_cells img_segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells img_segs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells img_segs m A cs -> A = A' -> rw_cells img_segs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Ltac recast_wf := cbn [cells_wf cell_wf]; rewrite ?length_app, ?length_le4, ?length_le8; repeat first [ reflexivity | split ].
Ltac recast_bytes := cbn [cells_bytes cbytes]; repeat rewrite <- app_assoc; cbn [app]; reflexivity.

Lemma file_to_tw : forall m Fp fl we wp wb buf bs mode CK,
  rw_cells img_segs m Fp (snf_file2 fl we wp wb buf bs mode CK) ->
  rw_cells img_segs m Fp (towrite_file fl (le4 (Z_to_bv 64 0)) (Z_to_bv 64 0) (Z_to_bv 64 0) snf_jz we wp snf_jz wb
     (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 (sym K_SN_WRITE)) ++ le8 (Z_to_bv 64 0)) buf bs
     (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) mode
     (le4 (Z_to_bv 64 (-1)) ++ le4 (Z_to_bv 64 (-1)) ++ snf_jx ++ le8 (Z_to_bv 64 CK) ++ snf_jy)).
Proof.
  intros. eapply rw_cells_recast; [eassumption | |].
  - unfold towrite_file, snf_jz, snf_jx, snf_jy. recast_wf.
  - unfold towrite_file, snf_file2, snf_jz, snf_jx, snf_jy. recast_bytes.
Qed.

Lemma tw_to_file : forall m Fp fl we wp wb buf bs mode CK,
  rw_cells img_segs m Fp (towrite_file fl (le4 (Z_to_bv 64 0)) (Z_to_bv 64 0) (Z_to_bv 64 0) snf_jz we wp snf_jz wb
     (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 (sym K_SN_WRITE)) ++ le8 (Z_to_bv 64 0)) buf bs
     (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) mode
     (le4 (Z_to_bv 64 (-1)) ++ le4 (Z_to_bv 64 (-1)) ++ snf_jx ++ le8 (Z_to_bv 64 CK) ++ snf_jy)) ->
  rw_cells img_segs m Fp (snf_file2 fl we wp wb buf bs mode CK).
Proof.
  intros. eapply rw_cells_recast; [eassumption | |].
  - unfold snf_file2. recast_wf.
  - unfold towrite_file, snf_file2, snf_jz, snf_jx, snf_jy. recast_bytes.
Qed.

Lemma file_to_sink : forall m Fp B mode CK,
  rw_cells img_segs m Fp (snf_file2 (Z_to_bv 64 0) (Z_to_bv 64 (B + 80)) (Z_to_bv 64 B) (Z_to_bv 64 B) B 80 mode CK) ->
  rw_cells img_segs m Fp (FILE_cells (Z_to_bv 8 0) snf_j1 (B + 80) B (snf_j2 snf_jz snf_jz snf_jz (snf_jt mode) B) (Z_to_bv 64 (-1)))
  /\ rw_cells img_segs m (Fp + 148) [CB 4 snf_jx; C8 (Z_to_bv 64 CK); CB 72 snf_jy].
Proof.
  intros m Fp B mode CK H. unfold snf_file2 in H.
  apply (proj1 (rw_cells_app img_segs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] _)) in H.
  destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2. split.
  - eapply rw_cells_recast; [exact H1 | |].
    + unfold FILE_cells, snf_j1, snf_j2, snf_jz, snf_jt. recast_wf.
    + unfold FILE_cells, snf_j1, snf_j2, snf_jz, snf_jt. recast_bytes.
  - eapply rw_cells_recast; [eapply rwc_eq; [exact H2 | lia] | |].
    + unfold snf_jx, snf_jy. recast_wf.
    + unfold snf_jx, snf_jy. recast_bytes.
Qed.

Lemma sink_to_file : forall m Fp B mode CK,
  rw_cells img_segs m Fp (FILE_cells (Z_to_bv 8 0) snf_j1 (B + 80) B (snf_j2 snf_jz snf_jz snf_jz (snf_jt mode) B) (Z_to_bv 64 (-1))) ->
  rw_cells img_segs m (Fp + 148) [CB 4 snf_jx; C8 (Z_to_bv 64 CK); CB 72 snf_jy] ->
  rw_cells img_segs m Fp (snf_file2 (Z_to_bv 64 0) (Z_to_bv 64 (B + 80)) (Z_to_bv 64 B) (Z_to_bv 64 B) B 80 mode CK).
Proof.
  intros m Fp B mode CK H1 H2.
  assert (H : rw_cells img_segs m Fp (FILE_cells (Z_to_bv 8 0) snf_j1 (B + 80) B (snf_j2 snf_jz snf_jz snf_jz (snf_jt mode) B) (Z_to_bv 64 (-1))
                                      ++ [CB 4 snf_jx; C8 (Z_to_bv 64 CK); CB 72 snf_jy])).
  { apply (proj2 (rw_cells_app img_segs _ _ _ _)). split; [exact H1|]. eapply rwc_eq; [exact H2|]. unfold FILE_cells. cbn. lia. }
  eapply rw_cells_recast; [exact H | |].
  - unfold snf_file2. recast_wf.
  - unfold snf_file2, FILE_cells, snf_j1, snf_j2, snf_jz, snf_jt, snf_jx, snf_jy. recast_bytes.
Qed.

  Context {CODE_vfprintf : CodeAtT img_segs (sym 0x7f000400) (PROGAT_CODE_vfprintf IMG)}.
  Context {RB_vfprintf : RelCode (sym 0x7f000400) 432}.
  Context {RN_printf_core : RelNear (sym 0x7f000400) (sym 0x18704)}.
  Context {RN_lockfile : RelNear (sym 0x7f000400) (sym 0x7f000700)}.
  Context {RN_towrite : RelNear (sym 0x7f000400) (sym 0x17f40)}.
  Context {RN_unlockfile : RelNear (sym 0x7f000400) (sym 0x7f000800)}.
  Context {RN_stack_chk_fail : RelNear (sym 0x7f000400) (sym 0x15f04)}.
  Context {CODE_towrite : CodeAtT img_segs (sym 0x17f40) (PROGAT_CODE_towrite IMG)}.
  Context {RB_towrite : RelCode (sym 0x17f40) 84}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_snw : RelSym (sym K_SN_WRITE)}.
  Context {RB_snw : RelCode (sym K_SN_WRITE) 220}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)}.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)}.
  Let rp_22e18 : 0 <= sym 0x22e18 < 2^30 := @rel_sym_pf _ RS_got_ssp.
  Let rp_snw : 0 <= sym K_SN_WRITE < 2^30 := @rel_sym_pf _ RS_snw.
  Let rp_34288 : 0 <= sym 0x34288 < 2^30 := @rel_sym_pf _ RS_34288.
  Let rp_35000 : 0 <= sym 0x35000 < 2^30 := @rel_sym_pf _ RS_35000.
  Let rl0_0 : sym 0x22e18 + 8 <= sym 0x34288 := @zfact_pf _ RL0_0.
  Let rl0_1 : sym 0x34288 + 8 <= sym 0x35000 := @zfact_pf _ RL0_1.
  Let rq_22e18 : 0x14000 <= sym 0x22e18 := @zfact_pf _ RQ_22e18.
  Context (PC : printf_core_all).
  Let PCL : printf_core_low_all := printf_core_low_of_all PC.
  Context (PC1 : printf_core1_stmt).
  Context (SNF_FRAME : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            sink_frame_stmt Fp B 80 CK 16 D (Z.of_nat dn) (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)).
  Context (SNF_FLAGS : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            sink_flags_stmt Fp (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)).
  Context (SNF_OUT : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            out_stmt Fp B 80 CK 16 D (Z.of_nat dn) (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)
                     (TOPOK_snf TOP) (OUT_snf OM)).
  Context (SNF_FLUSH : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            snf_flush_stmt Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM).

Lemma topok_snf : forall TOP, topok_stmt (TOPOK_snf TOP).
Proof. intros TOP a b H1 H2. unfold TOPOK_snf in *. lia. Qed.

Lemma sink_write_cell : forall m Fp fl0 j1 jt jx jy lbfw B CK D dn junkd N TOP OM o,
  SINK_snf Fp fl0 j1 snf_jz snf_jz snf_jz jt jx jy lbfw B CK D dn junkd N TOP OM m o ->
  rw_cells img_segs m (Fp + 72) [C8 (Z_to_bv 64 (sym K_SN_WRITE))].
Proof.
  intros m Fp fl0 j1 jt jx jy lbfw B CK D dn junkd N TOP OM o (o1 & o2 & bj & SN). cbv zeta in SN.
  destruct SN as (_ & _ & _ & _ & _ & Ljt & _ & _ & [FC _] & _).
  unfold FILE_cells in FC.
  apply (proj1 (rw_cells_app img_segs _ _ [_; _; _; _] _)) in FC. destruct FC as [_ FC]. cbn [cells_size csize Nat.add app] in FC.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FC. destruct FC as [FC _].
  assert (FC2 : rw_cells img_segs m (Fp + Z.of_nat 48)
                  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sym K_SN_WRITE));
                   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); CB 48 jt]).
  { eapply rw_cells_recast; [exact FC | |].
    - cbn [cells_wf cell_wf]. repeat split. exact Ljt.
    - unfold snf_j2, snf_jz. recast_bytes. }
  apply (proj1 (rw_cells_app img_segs _ _ [_; _; _] _)) in FC2. destruct FC2 as [_ FC2]. cbn [cells_size csize Nat.add app] in FC2.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FC2. destruct FC2 as [FC2 _].
  eapply rwc_eq; [exact FC2 | lia].
Qed.

Theorem vfprintf_snf_proof : vfprintf_snf_stmt.
Proof.
  unfold vfprintf_snf_stmt. intros until o. cbv zeta.
  intros -> -> -> FH CKC DST LJ BY HF P1 VAA AOK MODEL HN HOM HDN HBP ST LO GLO QHI SSP MI FRM HA HA0 QF FCK CKV CKHI VAHI D0 DHI DD1 DD2.
  unfold VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold zb in AB. rewrite length_map in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof rp_22e18. pose proof rp_snw. pose proof rp_34288. pose proof rp_35000. pose proof rl0_0. pose proof rl0_1. pose proof rq_22e18.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU2.
  stash BY. stash VAA. stash AOK. stash MODEL. stash DST. stash CKC.
  unfold snf_file in FH.
  carve_frame 368%nat ST.
  do 25 zs.
  assert (BY0 : bytes_at img_segs m0 A (zb fmt)).
  { unfold hideP in BY. eapply bytes_at_transport; [exact BY | exact MU |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  zs.
  eapply evt_cut.
  { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
      [ exact BY0 | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
      | split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
  cbv beta. intros ms' P. clear BY0. unfold printf_core1_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m1 -> MUc WMc MIc STc SSPc).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m1 MUc WMc; clear MUc WMc; try clear MI end.
  aret_pc.
  clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  zs. if_lit. zs. zs. if_lit. zs. do 4 zs. zs. if_lit.
  do 9 zs. zs.
  replace (Z.land (bv_unsigned (sx32 (Z_to_bv 64 0))) 18446744073709551583) with 0 in * by (vm_compute; reflexivity).
  assert (FH2 : rw_cells img_segs m1 Fp (snf_file2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                         (bv_unsigned sp + -352) 80 (Z_to_bv 64 0) CK)) by exact FH.
  clear FH. apply file_to_tw in FH2.
  eapply evt_cut.
  { eapply towrite_x_proof; rewrite ?unsigned_lit by lia; [exact FH2 | vm_compute; reflexivity | lia | lia | lia | assumption]. }
  cbv beta. intros ms' P. clear FH2. rewrite !unsigned_lit in P by lia.
  (nelim P 21%nat; intros x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' mode' m2 -> MUc WMc MIt FHt).
  apply tw_to_file in FHt.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m2 MUc WMc; clear MUc WMc; try clear MIc end.
  aret_pc.
  zs. if_lit. do 5 zs. zs.
  set (B := bv_unsigned sp + -352) in *.
  apply (rw_cells_split_CB img_segs _ _ [_; _] 248 _ _ [80; 168]%nat) in FR; [|reflexivity]. cbn [app mk_CB_cells] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [AP2 FR]. cbn [cells_size csize Nat.add app] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [BUFc FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8) with B in BUFc by (unfold B; lia).
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80) with (bv_unsigned sp + -272) in FR by (unfold B; lia).
  replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
  match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
  pose proof (G_printf_core_common.rw_CB_length _ _ _ _ BUFc) as LJB.
  apply (rw_cells_split_CB img_segs _ _ [] 80 _ [] [0; 80]%nat) in BUFc; [|reflexivity]. cbn [app mk_CB_cells] in BUFc.
  change (firstn 0 jb) with (@nil byte) in BUFc. change (skipn 0 jb) with jb in BUFc.
  rewrite (firstn_all2 (n := 80%nat) jb) in BUFc by (rewrite LJB; apply Nat.le_refl).
  apply file_to_sink in FHt. destruct FHt as [FILE1 R148].
  unfold hideP in BY, VAA, AOK, MODEL, DST, CKC.
  assert (BY2 : bytes_at img_segs m2 A (zb fmt)).
  { eapply bytes_at_transport; [exact BY | exact MU2 |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  assert (VAA2 : bytes_at img_segs m2 VA (u64s slots)).
  { eapply bytes_at_transport; [exact VAA | exact MU2 |]. cbn [disjoint_from]. rewrite LU. lia. }
  assert (CKC2 : rw_cells img_segs m2 CK [C8 (Z_to_bv 64 (D + Z.min (zlength (@nil Z)) N)); C8 (Z_to_bv 64 (N - Z.min (zlength (@nil Z)) N))]).
  { replace (Z.min (zlength (@nil Z)) N) with 0 by (unfold zlength; cbn; lia). rewrite Z.add_0_r, Z.sub_0_r.
    eapply rw_cells_transport; [exact CKC | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (DST2 : rw_cells img_segs m2 D [CB dn (zb (firstn (Z.to_nat N) (@nil Z)) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength (@nil Z)) N))) junkd)]).
  { replace (Z.min (zlength (@nil Z)) N) with 0 by (unfold zlength; cbn; lia). rewrite firstn_nil. cbn [zb map app Z.to_nat].
    eapply rw_cells_transport; [exact DST | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (AOK2 : args_ok Fp B 80 CK 16 D (Z.of_nat dn) m2 lo (bv_unsigned sp + -368) (bv_unsigned sp + -368) slots args).
  { eapply args_ok_rebase; [exact AOK | exact MU | lia | right; reflexivity | left; unfold B; lia | right; split; reflexivity | left; lia]. }
  clear MU2 BY VAA AOK CKC DST.
  assert (WF : wfile m2 Fp (Z_to_bv 8 0) snf_j1 (snf_j2 snf_jz snf_jz snf_jz (snf_jt mode') B) (Z_to_bv 64 (-1)) B (zb []) jb).
  { unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB.
    replace (B + Z.of_nat 0 + Z.of_nat 80) with (B + 80) by lia. replace (B + Z.of_nat 0) with B by lia.
    split; [exact FILE1|]. split; [exact BUFc|]. split; [vm_compute; reflexivity|].
    split; [apply Z.leb_le; vm_compute; reflexivity|]. unfold B. lia. }
  assert (SNK : SINK_snf Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1))
                         B CK D dn junkd N (bv_unsigned sp + -368) OM m2 []).
  { exists [], [], jb. cbv zeta.
    split; [reflexivity|].
    split; [unfold SNF_CAP, zlength; rewrite LJB; reflexivity|].
    split; [apply length_le8|]. split; [apply length_le8|]. split; [apply length_le8|].
    split; [unfold snf_jt; rewrite ?length_app, ?length_le4, ?length_le8; reflexivity|].
    split; [apply length_le4|]. split; [unfold snf_jy; rewrite ?length_app, ?length_le8; reflexivity|].
    split; [exact WF|]. split; [exact R148|]. split; [exact CKC2|]. split; [exact DST2|].
    split; [exact LJ|].
    unfold SNF_CAP, B. repeat split; unfold zlength in *; cbn [length] in *; lia. }
  assert (PCALL : forall Q ms, implM img_segs (printf_model (OUT_snf OM) OUTFP_snf fmt args) [] Q ms -> evt img_segs (Q r o) ms).
  { intros Q ms HQ. unfold implM in HQ. rewrite MODEL in HQ. exact HQ. }
  pose proof (SNF_FRAME Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SFR.
  pose proof (SNF_FLAGS Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SFL.
  pose proof (SNF_OUT Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SOUT.
  pose proof (PC (list Z) Fp B 80 CK 16 D (Z.of_nat dn) _ _ (OUT_snf OM) OUTFP_snf SFR SFL (topok_snf (bv_unsigned sp + -368)) SOUT) as PC2.
  pose proof (PCL (list Z) Fp B 80 CK 16 D (Z.of_nat dn) _ _ (OUT_snf OM) OUTFP_snf SFR SFL (topok_snf (bv_unsigned sp + -368)) SOUT) as PCL2.
  unfold printf_core_stmt in PC2. unfold printf_core_low_stmt in PCL2.
  eapply evt_cut.
  { apply PCALL. destruct DD1 as [DD1 | DD1]; [destruct DD2 as [DD2 | DD2] |];
    [ eapply PCL2 with (st := []) (VA := VA) (i := 0) (slots := slots) (args := args) (lo := lo) (canary := canary)
    | eapply PC2 with (st := []) (VA := VA) (i := 0) (slots := slots) (args := args) (lo := lo) (canary := canary)
    | eapply PC2 with (st := []) (VA := VA) (i := 0) (slots := slots) (args := args) (lo := lo) (canary := canary) ];
    rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_snf, zlength;
    first [ exact SNK | exact BY2 | exact HF | reflexivity | (replace (VA + 8 * 0) with VA by lia; exact APC)
          | exact VAA2 | (cbn [Z.to_nat skipn]; exact AOK2) | apply fpcalls_snf | exact STc
          | (split; [exact SSP1 | exact SSP2]) | assumption | exact FRM | lia
          | (left; split; lia) | (right; repeat split; lia) | (repeat split; lia) ]. }
  cbv beta. intros ms' P. clear PC2 PCL2 PCALL.
  unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr).
  unfold SR in MUc. cbn [app] in MUc.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
  aret_pc.
  zs. zs. zs. if_cases Kb; zify_cond Kb. { exfalso. rewrite ?unsigned_lit in Kb by lia. lia. }
  pose proof (sink_write_cell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SNK3) as W72.
  zs. zs. zs. zs. zs. aret_pc.
  destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 64) _ ST3 ltac:(lia)) as [ST4a ST4b]. clear ST3.
  pose proof (SNF_FLUSH Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1))
              B CK D dn junkd N (bv_unsigned sp + -368) OM) as FLU.
  unfold snf_flush_stmt in FLU.
  eapply evt_cut.
  { eapply FLU; clear FLU; rewrite ?unsigned_lit by lia;
      [ exact SNK3 | reflexivity | reflexivity | reflexivity | exact ST4b | lia | lia | lia | assumption ]. }
  clear FLU.
  cbv beta. intros ms' P. unfold snf_flush_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 26%nat; intros z5 z6 z7 e1 e2 e3 e4 e5 e6 e7 z28 z29 z30 z31 m4 bj4 -> MUc WMc MI4 ST4b' Lbj4 WF4 R148' CK4 D4).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
  aret_pc.
  destruct WF4 as (FC4 & BUF4 & _).
  match type of FC4 with rw_cells _ _ _ (FILE_cells _ _ ?we ?wp _ _) =>
    replace we with (B + 80) in FC4 by (rewrite ?Lbj4; cbn; lia); replace wp with B in FC4 by (cbn; lia) end.
  pose proof (sink_to_file _ _ _ _ _ FC4 R148') as FH5. clear FC4 R148'. unfold snf_file2 in FH5.
  do 16 zs.
  try replace (0 <? B) with true by (symmetry; apply Z.ltb_lt; unfold B; lia).
  try replace (Z.land (bv_unsigned (sx32 (Z_to_bv 64 0))) 32) with 0 by (vm_compute; reflexivity).
  try replace (bv_unsigned (sx32 (Z_to_bv 64 0))) with 0 by (vm_compute; reflexivity).
  try replace (Z.land (bv_swrap 32 (Z.b2z true + -1)) 18446744073709551615) with 0 by (vm_compute; reflexivity).
  try replace (Z.land (bv_swrap 32 (Z.b2z (0 <? 1) + -1)) 18446744073709551615) with 0 by (vm_compute; reflexivity).
  rewrite ?Z.lor_0_l.
  zs. if_lit.
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 9 zs.
  replace (Z.land r 18446744073709551615) with r
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; unfold INT_MAX in Hr; lia).
  unfold B in *.
  pose proof (stk_merge _ _ _ _ _ ST4a ST4b' ltac:(lia)) as ST5. clear ST4a ST4b'.
  cbn [length] in BUF4. rewrite Lbj4 in BUF4.
  release_frame APC3 ST5 (bv_unsigned sp + -360).
  release_frame AP2 ST5 (bv_unsigned sp + -352).
  release_frame BUF4 ST5 (bv_unsigned sp + -272).
  release_frame FR ST5 (bv_unsigned sp).
  destruct (rw_cells_forget _ _ _ _ FH5) as [fjunk FJ]. cbn [cells_size csize Nat.add] in FJ.
  apply evt_done. unfold vfprintf_snf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST5|]. split; [split; [exact SSP1 | exact SSP2]|].
  split; [exact D4|]. split; [exact CK4|]. exact FJ.
Qed.

End Img.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* musl's vsnprintf in the plain and ubsan images, as a relocatable program tree (InstFmtP.v and InstFmtU.v check the
   tree at the symbol of each image).
   Port of projects/leptonica/fhmtgen_fuzzer/proofs/lib/K5/A10/F_vsnprintf.v (sha256 439229f024d5
   at 1aeda8ab8602).  That walk runs the same 51 instructions: the donor binary's function, decoded by the decoder that
   wrote vsnprintf_prog below, gives this tree with only its five outside addresses (got_ssp, memset, sn_write, vfprintf,
   __stack_chk_fail) changed.  What changes in the port: memset is called directly here (memset_callZ, from
   memset_contract) instead of through the sanitizer's interceptor; vfprintf is called under vfprintf_snf_stmt, which
   writes into the string FILE and truncates at the cookie's size, so the statement allows output longer than n - 1;
   and the statement drops the shadow-memory side conditions. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition vsnprintf_prog (B got_ssp B_memset K_snw B_vfprintf B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 120%Z
    (PNode 40%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 0 2 2 3792 4
          (PJ_Store_SZ8_nnn 4 2 1 296 4
          (PJ_Store_SZ8_nnn 8 2 8 288 4
          (PJ_Store_SZ8_nnn 12 2 9 280 4
          (PJ_Store_SZ8_nnn 16 2 18 272 4
          (PJ_Store_SZ8_nnn 20 2 19 264 4
          (PJ_OpImm_ALU_ADD_nnn 24 8 13 0 4
          (PJ_OpImm_ALU_ADD_nnn 28 9 12 0 4
          (PJ_Auipc_nt 32 12 (hi20 (got_ssp - (B + 32))) 4
          (PJ_Load_SZ8_true_nnt 36 18 12 (lo12 (got_ssp - (B + 32))) 4 nil)))))))))))
      (PNode 80%Z
        (PLeaf
            (PJ_Load_SZ8_true_nnn 40 12 18 0 4
            (PJ_Store_SZ8_nnn 44 2 12 256 4
            (PJ_OpImm_ALU_ADD_nnn 48 19 2 254 4
            (PJ_Branch_BC_EQ_nnn 52 11 0 8 4
            (PJ_OpImm_ALU_ADD_nnn 56 19 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 60 10 11 4095 4
            (PJ_Op_ALU_SLTU_nnn 64 11 11 10 4
            (PJ_OpImm_ALU_ADD_nnn 68 11 11 4095 4
            (PJ_Op_ALU_AND_nnn 72 10 11 10 4
            (PJ_Store_SZ8_nnn 76 2 19 232 4 nil)))))))))))
        (PLeaf
            (PJ_Store_SZ8_nnn 80 2 10 240 4
            (PJ_OpImm_ALU_ADD_nnn 84 10 2 0 4
            (PJ_OpImm_ALU_ADD_nnn 88 12 0 232 4
            (PJ_OpImm_ALU_ADD_nnn 92 11 0 0 4
            (PJ_Jal_nt 96 1 (jimm21 (B_memset - (B + 96))) 4
            (PJ_Auipc_nt 100 10 (hi20 (K_snw - (B + 100))) 4
            (PJ_OpImm_ALU_ADD_nnn 104 11 2 255 4
            (PJ_OpImm_ALU_ADD_nnn 108 12 0 4095 4
            (PJ_OpImm_ALU_ADD_nnt 112 10 10 (lo12 (K_snw - (B + 100))) 4
            (PJ_Store_SZ8_nnn 116 2 10 72 4 nil)))))))))))))
    (PNode 160%Z
      (PLeaf
          (PJ_Store_SZ8_nnn 120 2 11 88 4
          (PJ_OpImm_ALU_ADD_nnn 124 10 2 232 4
          (PJ_Store_SZ4_nnn 128 2 12 140 4
          (PJ_Store_SZ4_nnn 132 2 12 144 4
          (PJ_Store_SZ8_nnn 136 2 10 152 4
          (PJ_Store_SZ1_nnn 140 19 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 144 10 2 0 4
          (PJ_OpImm_ALU_ADD_nnn 148 11 9 0 4
          (PJ_OpImm_ALU_ADD_nnn 152 12 8 0 4
          (PJ_Jal_nt 156 1 (jimm21 (B_vfprintf - (B + 156))) 4 nil)))))))))))
      (PNode 200%Z
        (PLeaf
            (PJ_Load_SZ8_true_nnn 160 11 18 0 4
            (PJ_Load_SZ8_true_nnn 164 12 2 256 4
            (PJ_Branch_BC_NE_nnn 168 11 12 32 4
            (PJ_Load_SZ8_true_nnn 172 1 2 296 4
            (PJ_Load_SZ8_true_nnn 176 8 2 288 4
            (PJ_Load_SZ8_true_nnn 180 9 2 280 4
            (PJ_Load_SZ8_true_nnn 184 18 2 272 4
            (PJ_Load_SZ8_true_nnn 188 19 2 264 4
            (PJ_OpImm_ALU_ADD_nnn 192 2 2 304 4
            (PJ_Jalr_nnn 196 0 1 0 4 nil)))))))))))
        (PLeaf
            (PJ_Jal_nt 200 1 (jimm21 (B_stack_chk_fail - (B + 200))) 4 nil)))).
Definition vsnprintf_size : Z := 204.

(* The step, call and memory tactics of the relocatable walk. *)
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* The tree at vsnprintf's address, with the five outside addresses of this image. *)
Definition PROGAT_CODE_vsnprintf (IMG : RImg) :=
  vsnprintf_prog (sym 0x7f000200) (sym 0x22e18) (sym 0x21738) (sym K_SN_WRITE) (sym 0x7f000400) (sym 0x15f04).

(* Stack the walk needs below sp: its own 304-byte frame plus what vfprintf needs (VF_DEPTH). *)
Definition VSN_DEPTH : Z := 5856.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_vsnprintf : CodeAtT img_segs (sym 0x7f000200) (PROGAT_CODE_vsnprintf IMG)}.
  Context {RB_vsnprintf : RelCode (sym 0x7f000200) 204}.
  Context {RN_memset : RelNear (sym 0x7f000200) (sym 0x21738)}.
  Context {RN_vfprintf : RelNear (sym 0x7f000200) (sym 0x7f000400)}.
  Context {RN_stack_chk_fail : RelNear (sym 0x7f000200) (sym 0x15f04)}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_snw : RelSym (sym K_SN_WRITE)}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)}.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)}.
  Let rp_22e18 : 0 <= sym 0x22e18 < 2^30 := @rel_sym_pf _ RS_got_ssp.
  Let rp_34288 : 0 <= sym 0x34288 < 2^30 := @rel_sym_pf _ RS_34288.
  Let rp_35000 : 0 <= sym 0x35000 < 2^30 := @rel_sym_pf _ RS_35000.
  Let rl0_0 : sym 0x22e18 + 8 <= sym 0x34288 := @zfact_pf _ RL0_0.
  Let rl0_1 : sym 0x34288 + 8 <= sym 0x35000 := @zfact_pf _ RL0_1.
  Let rq_22e18 : 0x14000 <= sym 0x22e18 := @zfact_pf _ RQ_22e18.
  Context (SPEC_memset : memset_contract).
  Context (VF : vfprintf_snf_stmt).

Definition vsnprintf_x_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (txt : list byte) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m'
    /\ wmono img_segs m m'
    /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' D [CB dn txt].

(* vsnprintf (s = D, n, fmt = A, ap = VA): it writes min(|o|, n - 1) bytes of the output o and a NUL at D, and returns r. *)
Definition vsnprintf_x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells img_segs m D [CB dn junkd] ->
    Z.of_nat dn = Z.min (zlength o) (n - 1) + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots ->
    args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    1 <= n < 2^31 ->
    stk img_segs m lo q -> lo <= q - VSN_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= STATIC_SPLIT -> 65536 <= A ->
    q <= VA -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) ->
    (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt img_segs (vsnprintf_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000200)) fc None m (seg_rom img_segs)).

(* memset_contract, stated for a call whose arguments are literals. *)
Lemma memset_callZ : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q D C N : Z) (junk : list byte),
  rw_cells img_segs m D [CB (Z.to_nat N) junk] ->
  mem_inv img_segs m ->
  0 <= q < 2^64 -> 0 <= D < 2^64 -> 0 <= C < 2^64 -> 0 <= N < 2^64 ->
  evt img_segs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom img_segs)
       /\ munch [(D, D + N)] m m'
       /\ wmono img_segs m m'
       /\ mem_inv img_segs m'
       /\ rw_cells img_segs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))])
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).
Proof using SPEC_memset.
  intros until junk. intros CELLS MINV Hq HD HC HN.
  rewrite <- (unsigned_lit D) in CELLS at 1 by lia. rewrite <- (unsigned_lit N) in CELLS by lia.
  eapply evt_mono; [ exact (SPEC_memset ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk CELLS MINV) | ].
  intros ms' POST. unfold memset_post in POST. rewrite !unsigned_lit in POST by lia. exact POST.
Qed.

(* The 232-byte FILE after memset clears it, in the cell layout of snf_file. *)
Definition zfile : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* The walk: frame and canary, n - 1 into the cookie, memset of the FILE, the FILE fields, the NUL at s, the call of
   vfprintf, the canary check and the return. *)
Theorem vsnprintf_x_proof : vsnprintf_x_stmt.
Proof using IMG CODE_vsnprintf RB_vsnprintf RN_memset RN_vfprintf RS_got_ssp RS_snw RS_34288 RS_35000 RL0_0 RL0_1 RQ_22e18
  rp_22e18 rp_34288 rp_35000 rl0_0 rl0_1 rq_22e18 SPEC_memset VF.
  unfold vsnprintf_x_stmt. intros until o. cbv zeta.
  intros -> -> -> -> DCELL HDN FMTB FMTR P1 VAREA ARGS MODEL Hn STK LODEP GLO QHI SSP MINV FRM0 HAS HA0 QVA VAHI D0 DHI DSEP DLOW.
  unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in RSP.
  pose proof (rw_cells_bound _ _ _ _ DCELL) as DBND. cbn [cells_size csize Nat.add] in DBND.
  pose proof (bytes_at_bound _ _ _ _ FMTB) as ABND. unfold zb in ABND. rewrite length_map in ABND.
  assert (LJ : length junkd = dn) by (destruct DCELL as [[[X _] _] _]; exact X).
  unfold zlength in *.
  destruct SSP as [GOT CAN]. unfold got_ssp, ssp_guard in GOT, CAN.
  pose proof rp_22e18. pose proof rp_34288. pose proof rp_35000. pose proof rl0_0. pose proof rl0_1. pose proof rq_22e18.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  (* MUF follows the frame stores and the memset only, so that the destination cells can be carried past them. *)
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUF.
  stash FMTB. stash VAREA. stash ARGS. stash MODEL. stash DCELL.
  carve_frame 304%nat STK.
  (* 0..44: frame, saved registers, s0 = ap, s1 = fmt, s2 = &guard, canary at sp' + 256. *)
  do 12 zs.
  (* 48..52: s3 = sp' + 254; n is not 0, so the branch falls through. *)
  zs. zs. if_cases K1; zify_cond K1. { exfalso. lia. }
  (* 56..72: s3 = s, a0 = n - 1 (the sltu/and pair is the n = 0 guard). *)
  do 5 zs.
  replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
    by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  (* 76..92: the cookie {s, n - 1} at sp' + 232, then memset's arguments. *)
  do 5 zs.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [FZ FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -304 + Z.of_nat 232) with (bv_unsigned sp + -72) in FR by lia.
  apply (proj1 (rw_cells_app img_segs _ _ [_; _] _)) in FR. destruct FR as [CKC FRT]. cbn [cells_size csize Nat.add app] in FRT.
  replace (bv_unsigned sp + -72 + Z.of_nat 16) with (bv_unsigned sp + -56) in FRT by lia.
  (* 96: memset(sp', 0, 232). *)
  zs.
  call memset_callZ.
  1:{ exact FZ. } 1:{ exact MINV. } 1-4: lia.
  rename x13 into m2. clear SCin1 SCin2.
  pose proof (rw_cells_recast _ _ _ zfile POST ltac:(cbn [cells_wf cell_wf zfile]; repeat split) ltac:(vm_compute; reflexivity)) as FC.
  clear POST. unfold zfile in FC.
  (* 100..136: write = sn_write, buf = sp' + 255, lock = lbf = -1, cookie = sp' + 232. FC is then snf_file. *)
  do 10 zs.
  unfold hideP in DCELL.
  assert (DC0 : rw_cells img_segs m0 D [CB dn junkd]).
  { eapply rw_cells_transport; [exact DCELL | exact MUF | exact WM |]. cbn [disjoint_from cells_size csize Nat.add].
    pose proof (u64s_length slots). lia. }
  clear DCELL MUF.
  (* 140: s[0] = 0, a one-byte store into the destination. *)
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DC0) as DA. clear DC0.
  pose proof (u8arr_store_ok img_segs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zs.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (unfold le1; rewrite unsigned_lit by lia; reflexivity).
  replace (write_to_mem m0 (Z_to_bv 64 D) [Z_to_bv 8 0]) with (write_to_mem m0 (wa (D + 0)) [Z_to_bv 8 0]) by (unfold wa; do 2 f_equal; lia).
  pose proof (u8arr_write img_segs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
  pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. clear DA2.
  change (Z.to_nat 0) with 0%nat in DST.
  rewrite upd_length, LJ in DST. rewrite upd_firstn_skipn in DST by lia. rewrite firstn_O, app_nil_l in DST.
  (* 144..156: vfprintf(sp', fmt, ap). *)
  do 4 zs.
  unfold hideP in FMTB, VAREA, ARGS, MODEL.
  pose proof (u64s_length slots) as LU.
  assert (FMT1 : bytes_at img_segs m1 A (zb fmt)).
  { eapply bytes_at_transport; [exact FMTB | exact MU |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  assert (VA1 : va_area m1 VA slots).
  { unfold va_area in *. eapply bytes_at_transport; [exact VAREA | exact MU |]. cbn [disjoint_from]. rewrite LU. lia. }
  assert (ARG1 : args_ok (bv_unsigned sp + -304) lo 0 (bv_unsigned sp + -72) 16 D (Z.of_nat dn) m1 lo (bv_unsigned sp + -304) lo slots args).
  { eapply args_ok_rebase; [exact ARGS | | | | | |].
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia.
    - lia.
    - left; lia.
    - right; split; reflexivity.
    - left; lia.
    - right; reflexivity. }
  clear FMTB VAREA ARGS.
  pose proof VF as V. unfold vfprintf_snf_stmt in V. cbv zeta in V.
  eapply evt_cut.
  { eapply V with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (N := n - 1) (OM := zlength o)
                  (bufp := bv_unsigned sp + -49) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := fmt)
                  (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear V; rewrite ?unsigned_lit by lia; unfold VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength in *.
    all: first [ reflexivity | exact FC | exact CKC | exact DST | exact LJ | exact FMT1 | exact FMTR | exact P1 | exact VA1
               | exact ARG1 | exact MODEL | exact STK | (split; [exact GOT | exact CAN]) | exact MI | exact FRM0 | lia ]. }
  cbv beta. intros ms' POSTV. unfold vfprintf_snf_post in POSTV. rewrite ?unsigned_lit in POSTV by lia.
  (nelim POSTV 29%nat; intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 Ft fc' fjunk m3 -> MUc WMc MI3 FRM3 FOK ST3 SSP3 DST3 CK3 FJ3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m3 MUc WMc; clear MUc WMc end.
  aret_pc.
  clear V MI VA1 ARG1.
  destruct SSP3 as [GOT3 CAN3]. unfold got_ssp, ssp_guard in GOT3, CAN3.
  (* 160..168: the canary is unchanged, so no __stack_chk_fail. *)
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  (* 172..196: restore and return. *)
  do 7 zs.
  assert (FALL : rw_cells img_segs m3 (bv_unsigned sp + -304)
                   ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o `min` (n - 1))); C8 (Z_to_bv 64 (n - 1 - zlength o `min` (n - 1)))]
                    ++ [CB 8 jk15; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app img_segs _ _ _ _)). split; [exact FJ3|].
    apply (proj2 (rw_cells_app img_segs _ _ _ _)). cbn [cells_size csize Nat.add app].
    split; [eapply rwc_eq; [exact CK3 | lia] | eapply rwc_eq; [exact FRT | lia]]. }
  clear FJ3 CK3 FRT. cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  (* vfprintf wrote dn - 1 bytes and the NUL, so no byte of the old destination is left. *)
  rewrite skipn_all2 in DST3 by (rewrite LJ; unfold zlength; lia).
  apply evt_done. unfold vsnprintf_x_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM3|].
  split; [exact FOK|]. split; [exact ST3|]. split; [split; [exact GOT3 | exact CAN3]|]. exact DST3.
Qed.

End Img.

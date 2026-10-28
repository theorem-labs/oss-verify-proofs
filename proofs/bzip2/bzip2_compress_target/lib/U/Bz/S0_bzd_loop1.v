(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 BzWalkArith S0_bzd_out.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.



(* [comment removed for export] *)
Record bzdctx := BZC {
  z_cx : bctx;                                   (* [comment removed for export] *)
  z_ra : word; z_sp : word; z_gp : word; z_tp : word;   (* [comment removed for export] *)
  z_s0 : word; z_s1 : word; z_s2 : word; z_s3 : word; z_s4 : word; z_s5 : word;
  z_s6 : word; z_s7 : word; z_s8 : word; z_s9 : word; z_s10 : word; z_s11 : word;  (* [comment removed for export] *)
  z_F : bvmap 5 word; z_fc : bv 32;
  z_g1 : word; z_sv : word;                      (* [comment removed for export] *)
  z_payload : list byte;                         (* [comment removed for export] *)
  z_lo : Z;                                      (* [comment removed for export] *)
  z_m0 : word -> option byte;                    (* [comment removed for export] *)
  z_fj : list byte;                              (* [comment removed for export] *)
  z_spi : word                                   (* [comment removed for export] *)
}.

Section Ctx.
  Variable z : bzdctx.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation uspi := (bv_unsigned (z_spi z)).

  Definition bzdctx_ok : Prop :=
    ctx_ok cx /\ usp = b_sp cx /\ (CEILING <= z_lo z)%Z /\ (z_lo z + D14 + 112 <= usp)%Z /\
    length (z_fj z) = 8%nat /\ Z.of_nat (length (z_payload z)) = b_len cx /\
    bv_unsigned (z_spi z) = (usp - 112)%Z /\ Z_to_bv 64 (bv_unsigned (z_spi z) + 112) = z_sp z.

  (* [comment removed for export] *)
  Definition FRMj (fj : list byte) : list cell :=
    [CB 8 fj; C8 (z_s11 z); C8 (z_s10 z); C8 (z_s9 z); C8 (z_s8 z); C8 (z_s7 z); C8 (z_s6 z); C8 (z_s5 z);
     C8 (z_s4 z); C8 (z_s3 z); C8 (z_s2 z); C8 (z_s1 z); C8 (z_s0 z); C8 (z_ra z)].
  Definition FRM : list cell := FRMj (z_fj z).

  (* [comment removed for export] *)
  Definition WBZ : list ivl :=
    [(S, S + DSTATE_SIZE); (STRM, STRM + 44); (b_dst cx, b_dst cx + b_dlen cx); (z_lo z, usp)]%Z ++ blk_ivls cx.

  (* [comment removed for export] *)
  Definition IMGC (m : word -> option byte) : Prop :=
    rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 (z_g1 z); C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] /\
    rw_cells s0segs m 0x32098 [C8 (z_sv z)] /\
    u32arr s0segs m 0x335b0 rnums_words /\ u32arr s0segs m 0x33178 crc_words.

  (* [comment removed for export] *)
  Definition bzd_rest (m : word -> option byte) : Prop :=
    exists (h : dsh) (nbu : Z) (cf : list word) (d : dsm) (j1 : list byte) (snb : Z) (j2 : list byte) (r : drest)
           (b : bzs) (k : blk) (dbytes : list byte),
      rw_cells s0segs m S (HEAD_CELLS h) /\ rw_cells s0segs m (S + 1092) [C4 (Z_to_bv 64 nbu)] /\
      (u32arr s0segs m (S + 1096) cf /\ length cf = 257%nat) /\
      rw_cells s0segs m (S + 3152) (MID_CELLS d) /\ rw_cells s0segs m (S + 64036) (SAVE_CELLS j1 snb j2) /\
      drest_at s0segs m S r /\ rw_cells s0segs m STRM (STRM_CELLS b) /\ blk_at s0segs m cx k /\
      bytes_at s0segs m (b_src cx) (z_payload z) /\ IMGC m /\
      u8arr s0segs m (b_dst cx) dbytes /\ Z.of_nat (length dbytes) = b_dlen cx /\
      sh_strm h = STRM /\ length j1 = 44%nat /\ length j2 = 60%nat /\
      sm_tt d = b_tt cx /\ sm_ll16 d = b_ll16 cx /\ sm_ll4 d = b_ll4 cx /\
      bzs_wf b /\ bs_S b = S /\ bs_src b = b_src cx /\ bs_len b = b_len cx /\ bs_dst b = b_dst cx /\ bs_dlen b = b_dlen cx.

  Definition bzd_post : machine_state -> Prop := fun ms' =>
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) a0 a1 a2 a3 a4 a5 a6 a7
                    (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
               (z_F z) (ret_pc (z_ra z)) (z_fc z) None m' (seg_rom s0segs)
      /\ munch WBZ (z_m0 z) m' /\ wmono s0segs (z_m0 z) m' /\ mem_inv s0segs m'
      /\ (exists rc : Z, a0 = Z_to_bv 64 rc) /\ stk s0segs m' (z_lo z) usp /\ bzd_rest m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ZR (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) :=
    mkR ra (z_spi z) (z_gp z) (z_tp z) t0 t1 t2 (Z_to_bv 64 S) s1 a0 a1 a2 a3 a4 a5 a6 a7
        (Z_to_bv 64 (S + 1096)) s3 (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
        s8 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bzd_entry_post (h : dsh) (b : bzs) (m : word -> option byte) : machine_state -> Prop := fun ms' =>
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (fj : list byte),
      ms' = MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 (usp + -112)) (z_gp z) (z_tp z) t0 t1 t2 (Z_to_bv 64 S) (z_s1 z)
                    (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
                    (z_s8 z) (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6)
               (z_F z) (Z_to_bv 64 0x2462c) (z_fc z) None m' (seg_rom s0segs)
      /\ munch [(usp - 112, usp)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
      /\ rw_cells s0segs m' (usp + -112) (FRMj fj) /\ length fj = 8%nat /\ stk s0segs m' (z_lo z) (usp + -112)
      /\ rw_cells s0segs m' S (HEAD_CELLS h) /\ rw_cells s0segs m' STRM (STRM_CELLS b) /\ IMGC m'.
  Definition bzd_entry_spec : Prop :=
    forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (h : dsh) (b : bzs),
      rw_cells s0segs m S (HEAD_CELLS h) -> sh_strm h = STRM -> sh_state h = 10%Z ->
      rw_cells s0segs m STRM (STRM_CELLS b) -> bs_S b = S ->
      IMGC m -> stk s0segs m (z_lo z) usp -> mem_inv s0segs m ->
      evt s0segs (bzd_entry_post h b m)
          (MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) (Z_to_bv 64 STRM) a1 a2 a3 a4 a5 a6 a7
                   (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
              (z_F z) (Z_to_bv 64 0x14750) (z_fc z) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Ctx.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).
  Notation Q := (bzd_post z).

  Ltac zok :=
    let CX := ident:(CX) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End BZD.

End ACeilS1.

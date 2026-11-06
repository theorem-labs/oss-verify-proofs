(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 DecTacSA A0F_decCutsA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_g10A.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_g10M A0F_g10R A0F_g10C.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU10M.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Lemma g10_skipn_nth_cons : forall {T} (l : list T) k x, nth_error l k = Some x -> skipn k l = x :: skipn (Datatypes.S k) l.
Proof.
  intros T l k. revert l. induction k as [|k IH]; intros [|y l] x H; cbn in H |- *; try discriminate.
  - injection H as E. rewrite E. reflexivity.
  - exact (IH l x H).
Qed.
Lemma g10_pz_step : forall (p : list byte) (pre : list Z) (k : nat) (b : byte),
  map bv_unsigned p = pre ++ skipn k (map bv_unsigned p) -> length pre = k -> nth_error p k = Some b ->
  map bv_unsigned p = (pre ++ [bv_unsigned b]) ++ skipn (Datatypes.S k) (map bv_unsigned p).
Proof.
  intros p pre k b E L N. rewrite <- app_assoc. cbn [app].
  rewrite <- (g10_skipn_nth_cons (map bv_unsigned p) k (bv_unsigned b)); [exact E|].
  rewrite nth_error_map, N. reflexivity.
Qed.
Lemma g10_pz_end : forall (p : list byte) (pre : list Z) (k : nat),
  map bv_unsigned p = pre ++ skipn k (map bv_unsigned p) -> length pre = k -> length p = k -> map bv_unsigned p = pre.
Proof.
  intros p pre k E L N. rewrite E. rewrite skipn_all2; [apply app_nil_r|]. rewrite length_map. lia.
Qed.
Lemma g10_byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
Definition g10_early (payload : list byte) (rc : Z) : Prop :=
  forall (junkD : BzDState.dst) (small dn : Z), early10 rc dn (decompress (dst_init junkD 0 small) (s10 (map bv_unsigned payload) dn)).
(* [comment removed for export] *)
Definition g10_hd (h : dsh) (st bb bl n : Z) : dsh :=
  DSH (sh_strm h) st (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) bb bl n (sh_small h) (sh_p3 h)
      (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h).

Section B.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Notation S := (b_s (a_cx A)).
  Notation strm := (b_strm (a_cx A)).
  Notation src := (b_src (a_cx A)).
  Notation len := (b_len (a_cx A)).
  Notation P := (a_P A).
  Notation usp := (bv_unsigned (a_sp A)).
  Notation payload := (a_payload A).
  Hypothesis GL : g10_lin A.
  Hypothesis GS : (0 < src /\ src + len <= alloc_ceiling /\ 0 <= len < 2 ^ 27 /\ Z.of_nat (length payload) = len)%Z.
  Hypothesis ANS : sanchor S (a_shs A).
  Hypothesis ANT : sanchor strm (a_sht A).
  Hypothesis ANF : sanchor (a_fb A) (a_shf A).
  Hypothesis SEPfs : (a_fb A + 64 <= S \/ S + 64144 <= a_fb A)%Z.
  Hypothesis SEPfsh : (a_fb A + 64 <= a_shf A \/ a_shf A + 8 <= a_fb A)%Z.
  Hypothesis SEPshs : (a_shf A + 8 <= S \/ S + 64144 <= a_shf A)%Z.
  Hypothesis SEPst : (S + 64144 <= strm \/ strm + 80 <= S)%Z.
  Hypothesis SEPsrc : (S + 64144 <= src \/ src + len <= S)%Z.
  Hypothesis SEPtsrc : (strm + 80 <= src \/ src + len <= strm)%Z.
  Hypothesis SEPft : (a_fb A + 64 <= strm \/ strm + 80 <= a_fb A)%Z.
  Hypothesis SEPsht : (a_shf A + 8 <= strm \/ strm + 80 <= a_shf A)%Z.

  Variables (m : word -> option byte) (h : dsh) (b : bzs) (Fr : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Hypothesis SHS : shzW a0segs (W10 A) m S (S + 64144).
  Hypothesis SHT : shzW a0segs (W10 A) m strm (strm + 80).
  Hypothesis SHP : shpW a0segs (W10 A) m src (src + len).
  Hypothesis Hstrm : sh_strm h = strm.
  Hypothesis HN : (0 <= sh_n h < 2 ^ 32)%Z.
  Hypothesis L1 : length (sh_p1 h) = 3%nat.
  Hypothesis L2 : length (sh_p2 h) = 3%nat.
  Hypothesis L3 : length (sh_p3 h) = 3%nat.
  Hypothesis Hsrc : bs_src b = src.
  Hypothesis Hlen : bs_len b = len.
  Hypothesis Hai : bs_ai b = len.
  Hypothesis BZA : bs_bzalloc b = Z_to_bv 64 A0_DBZA.

  (* [comment removed for export] *)
  Hypothesis KE : forall (rc : Z) (m' : word -> option byte) (st bb n ai' : Z) (til' tih' : word)
      (fl : Z) (zt : word) (ng : nat) (jg j24 pos j38 : list byte) (u0 u8 u16 u704 u712 : word)
      (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    g10_early payload rc -> (rc = 0 \/ rc = -5)%Z -> (10 <= st <= 13)%Z -> (0 <= bb < 2 ^ 32)%Z -> (0 <= n < 2 ^ 32)%Z ->
    rw_cells a0segs m' S (HEAD_CELLS (g10_hd h st bb 0 n)) ->
    rw_cells a0segs m' strm (STRM_CELLS (bupd b ai' til' tih')) -> (0 <= ai' <= bs_ai b)%Z ->
    rw_cells a0segs m' (S + 64036) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 zt; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells a0segs m' P [C8 u0; C8 u8; C8 u16; C8 (Z_to_bv 64 (a_fb A + 32)); C8 (Z_to_bv 64 (S + 7884)); C8 (Z_to_bv 64 (S + 2124)); C8 (Z_to_bv 64 (S + 3192)); C8 (Z_to_bv 64 (S + 3152)); C8 (Z_to_bv 64 (S + 2047)); C8 (Z_to_bv 64 (S + 8)); C8 (Z_to_bv 64 (S + 3176)); C8 (Z_to_bv 64 (S + 7820))] ->
    rw_cells a0segs m' (P + 496) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A + 1)); C8 (Z_to_bv 64 0); C8 u704; C8 u712; C8 (Z_to_bv 64 (a_fb A))] ->
    (P + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
    ro_cells a0segs m' (a_fb A + 56) [C8 (Z_to_bv 64 fl)] ->
    rw_cells a0segs m' (P + 96) (FM_CELLS A zt) ->
    rw_cells a0segs m' (P + 728) (CB ng jg :: FT_REGS A) ->
    rw_cells a0segs m' (a_fb A) [C8 (Z_to_bv 64 1172321806); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 8 j24; CB 6 pos; CB 18 j38] ->
    rw_cells a0segs m' (a_shf A) [C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b] ->
    stk a0segs m' (a_lo A) P -> munch (W10 A) m m' -> wmono a0segs m m' -> mem_inv a0segs m' ->
    evt a0segs Q (MS (mkR y1 (Z_to_bv 64 P) gp tp y5 y6 y7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 rc) (Z_to_bv 64 fl) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) Fr (Z_to_bv 64 0x9ee18) fc None m' (seg_rom a0segs)).
  Hypothesis KF : forall (m' : word -> option byte) (uc : Z) (rest : list Z) (u0 u8 u16 u704 u712 : word)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    map bv_unsigned payload = (66 :: 90 :: 104 :: uc :: rest)%Z -> (49 <= uc <= 57)%Z -> (bv_unsigned (sh_small h) = 0)%Z ->
    rw_cells a0segs m' S (HEAD_CELLS (g10_hd h 13 (((66 * 256 + 90) * 256 + 104) * 256 + uc) 0 (uc - 48))) ->
    rw_cells a0segs m' strm (STRM_CELLS (bupd b (len - 4) (Z_to_bv 64 4) (bs_tih b))) ->
    rw_cells a0segs m' (S + 64036) SAVE0_CELLS ->
    bytes_at a0segs m' src payload ->
    rw_cells a0segs m' P [C8 u0; C8 u8; C8 u16; C8 (Z_to_bv 64 (a_fb A + 32)); C8 (Z_to_bv 64 (S + 7884)); C8 (Z_to_bv 64 (S + 2124)); C8 (Z_to_bv 64 (S + 3192)); C8 (Z_to_bv 64 (S + 3152)); C8 (Z_to_bv 64 (S + 2047)); C8 (Z_to_bv 64 (S + 8)); C8 (Z_to_bv 64 (S + 3176)); C8 (Z_to_bv 64 (S + 7820))] ->
    rw_cells a0segs m' (P + 496) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A + 1)); C8 (Z_to_bv 64 0); C8 u704; C8 u712; C8 (Z_to_bv 64 (a_fb A))] ->
    aframe A m' ->
    stk a0segs m' (a_lo A) P -> munch (W10 A) m m' -> wmono a0segs m m' -> mem_inv a0segs m' ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 0x9f528) (Z_to_bv 64 P) gp tp y5 y6 y7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 ((uc - 48) * 400000)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (strm + 56)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 strm) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 (a_sht A + 9)) (Z_to_bv 64 (strm + 72)) (Z_to_bv 64 (a_sht A + 7)) y28 y29 y30 y31) Fr (Z_to_bv 64 A0_MALLOC) fc None m' (seg_rom a0segs)).
  Hypothesis KS : forall (m' : word -> option byte) (uc : Z) (rest : list Z) (u0 u8 u16 u704 u712 : word)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    map bv_unsigned payload = (66 :: 90 :: 104 :: uc :: rest)%Z -> (49 <= uc <= 57)%Z -> (bv_unsigned (sh_small h) <> 0)%Z ->
    rw_cells a0segs m' S (HEAD_CELLS (g10_hd h 13 (((66 * 256 + 90) * 256 + 104) * 256 + uc) 0 (uc - 48))) ->
    rw_cells a0segs m' strm (STRM_CELLS (bupd b (len - 4) (Z_to_bv 64 4) (bs_tih b))) ->
    rw_cells a0segs m' (S + 64036) SAVE0_CELLS ->
    bytes_at a0segs m' src payload ->
    rw_cells a0segs m' P [C8 u0; C8 u8; C8 u16; C8 (Z_to_bv 64 (a_fb A + 32)); C8 (Z_to_bv 64 (S + 7884)); C8 (Z_to_bv 64 (S + 2124)); C8 (Z_to_bv 64 (S + 3192)); C8 (Z_to_bv 64 (S + 3152)); C8 (Z_to_bv 64 (S + 2047)); C8 (Z_to_bv 64 (S + 8)); C8 (Z_to_bv 64 (S + 3176)); C8 (Z_to_bv 64 (S + 7820))] ->
    rw_cells a0segs m' (P + 496) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_shs A + 1)); C8 (Z_to_bv 64 0); C8 u704; C8 u712; C8 (Z_to_bv 64 (a_fb A))] ->
    aframe A m' ->
    stk a0segs m' (a_lo A) P -> munch (W10 A) m m' -> wmono a0segs m m' -> mem_inv a0segs m' ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 0x9f30c) (Z_to_bv 64 P) gp tp y5 y6 y7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 ((uc - 48) * 200000)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (strm + 56)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 strm) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 (a_sht A + 9)) (Z_to_bv 64 (strm + 72)) (Z_to_bv 64 (a_sht A + 7)) y28 y29 y30 y31) Fr (Z_to_bv 64 A0_MALLOC) fc None m' (seg_rom a0segs)).

  (* [comment removed for export] *)
  Lemma g10_KXI : forall (m1 mk : word -> option byte) (bk : bzs) (lbl stk bbk nk : Z) (OUT : Z -> Prop) (u0 u8 u704 u712 : word),
    (10 <= lbl <= 13)%Z ->
    bk = bupd b (bs_ai bk) (bs_til bk) (bs_tih bk) -> (0 <= bs_ai bk <= bs_ai b)%Z ->
    rw_cells a0segs m1 (S + 64036) SAVE0_CELLS -> aframe A m1 ->
    munch (W10m A) m1 mk -> wmono a0segs m1 mk ->
    (forall rc, (rc = 0 \/ rc = -5)%Z -> OUT rc -> g10_early payload rc) ->
    A0F_g10_KX A Q m OUT mk (g10_hd h stk bbk 0 nk) bk lbl (Z_to_bv 64 P) gp tp (a_sp A) (Z_to_bv 64 (S + 64036)) Fr fc
      u0 u8 (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (S + 3176)) (Z_to_bv 64 (S + 7820))
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (a_shs A)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 0) (Z_to_bv 64 0) u704 u712 (Z_to_bv 64 (a_fb A)).
  Proof.
    intros m1 mk bk lbl stk bbk nk OUT u0 u8 u704 u712 LBL Eb Hbk SAV1 AF1 MU1k WM1k EQ.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    unfold A0F_g10_KX.
    intros rc m' bsBuff' nn ai' til' tih' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y22 y24 y25 y26 y27 y28 y29 y30 y31 yw16.
    cbv zeta. intros HD' RB RNN STRM' RAI PAY' FRL' FRH' ST' MU' WM' MUL' WML' MI' RC OUTrc.
    pose proof (munch_trans _ _ _ _ MU1k MUL') as MUc. pose proof (wmono_trans a0segs _ _ _ WM1k WML') as WMc.
    assert (SAV' : rw_cells a0segs m' (S + 64036) SAVE0_CELLS).
    { eapply rw_cells_transport; [exact SAV1 | exact MUc | exact WMc |]. unfold W10m, SAVE0_CELLS. clear - LIN ACR SEPst. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (AF' : aframe A m').
    { apply (aframe_tr A (W10m A) m1 m' AF1 MUc WMc); unfold W10m; cbn [disjoint_from].
      - clear - LIN ACR. lia.
      - clear - LIN ACR. lia.
      - clear - LIN ACR SEPfs SEPft. lia.
      - clear - LIN ACR SEPshs SEPsht. lia. }
    rewrite Eb, bupd_bupd in STRM'.
    unfold SAVE0_CELLS in SAV'.
    eapply (A0F_g10_R A Q m GL ANS SEPfs SEPfsh SEPshs SHS rc);
      [ exact MU' | exact WM' | exact SAV' | exact FRL' | exact FRH' | exact AF' | exact ST' | exact MI' |].
    intros m'' fl zt ng jg j24 pos j38 z1 z5 z6 z7 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
           SAV'' FRL'' FRH'' GEO NG FLP FRM FRT FF FS ST'' MU'' WM'' MUL'' WML'' MI''.
    assert (HD'' : rw_cells a0segs m'' S (HEAD_CELLS (g10_hd h lbl bsBuff' 0 nn))).
    { eapply rw_cells_transport; [exact HD' | exact MUL'' | exact WML'' |]. unfold W10r. clear - LIN ACR SEPfs SEPshs. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (STRM'' : rw_cells a0segs m'' strm (STRM_CELLS (bupd b ai' til' tih'))).
    { eapply rw_cells_transport; [exact STRM' | exact MUL'' | exact WML'' |]. unfold W10r. clear - LIN ACR SEPst SEPft SEPsht. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    eapply (KE rc m'' lbl bsBuff' nn ai' til' tih' fl zt ng jg j24 pos j38 u0 u8 yw16 u704 u712);
      [ exact (EQ rc RC OUTrc) | exact RC | exact LBL | exact RB | exact RNN | exact HD'' | exact STRM'' | clear - RAI Hbk; lia | exact SAV'' | exact FRL'' | exact FRH''
      | exact GEO | exact NG | exact FLP | exact FRM | exact FRT | exact FF | exact FS | exact ST'' | exact MU'' | exact WM'' | exact MI'' ].
  Qed.

  Theorem A0F_g10_B : forall (jf2 : list byte) (fl : Z) (ng : nat) (jg : list byte)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 : word)
      (v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408 v416 v424 v432 v440 v448 v456 v464 v472 : word)
      (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells a0segs m S (HEAD_CELLS h) -> sh_state h = 10%Z -> sh_bsBuff h = 0%Z -> sh_bsLive h = 0%Z ->
    rw_cells a0segs m (S + 64036) SAVE0_CELLS ->
    rw_cells a0segs m strm (STRM_CELLS b) -> bs_til b = Z_to_bv 64 0 ->
    bytes_at a0segs m src payload ->
    rw_cells a0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 (Z_to_bv 64 (S + 8)); C8 w80; C8 w88] ->
    rw_cells a0segs m (P + 96) [C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176; C8 v184; C8 v192; C8 v200; C8 v208; C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312; C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376; C8 v384; C8 v392; C8 v400; C8 v408; C8 v416; C8 v424; C8 v432; C8 v440; C8 v448; C8 v456; C8 v464; C8 v472; C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 (a_shf A))] ->
    rw_cells a0segs m (P + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 (Z_to_bv 64 (a_shs A)); C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 (Z_to_bv 64 (a_shs A + 1)); C8 w696; C8 w704; C8 w712; C8 (Z_to_bv 64 (a_fb A))] ->
    rw_cells a0segs m (P + 728) (CB ng jg :: FT_REGS A) -> (P + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
    rw_cells a0segs m (a_fb A) [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 32 jf2] ->
    ro_cells a0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] ->
    rw_cells a0segs m (a_shf A) [C1 df1b; C1 df1b; C1 df1b; C1 df1b; C1 df8b; C1 df3b; C1 df3b; C1 df3b] ->
    stk a0segs m (a_lo A) P -> mem_inv a0segs m ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 10) (Z_to_bv 64 (sh_strm h)) x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0x9e4d8) fc None m (seg_rom a0segs)).
  Proof.
    intros until x31. intros HD ST10 HBB HBL SAV STRM TIL PAY FRL FRM FRH FRT GEO NG FF FLP FS ST MI.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR. cps_pose GS as (G1 & G2 & G3 & G4).
    assert (PZ0 : map bv_unsigned payload = [] ++ skipn 0 (map bv_unsigned payload)) by reflexivity.
    (* [comment removed for export] *)
    eapply (A0F_g10_P3 A Q GL ANS SEPfs SEPfsh SEPshs) with (x19 := Z_to_bv 64 0);
      [ exact SHS | exact HD | exact ST10 | exact L1 | exact SAV | exact FRL | exact FRM | exact FRH | exact FRT | exact GEO | exact NG | exact FF | exact FLP | exact FS | exact ST | exact MI |].
    clear HD SAV FRL FRM FRH FRT FF FLP FS ST MI.
    intros m1 u0 u8 u16 u704 u712 y10 y11 y12 y13 y14 y22 HD1 SAV1 FRL1 FRH1 AF1 ST1 MI1 MU1 WM1 MUL1.
    unfold W10p3 in MUL1.
    assert (STRM1 : rw_cells a0segs m1 strm (STRM_CELLS b)).
    { eapply rw_cells_transport; [exact STRM | exact MUL1 | exact WM1 |]. clear - LIN ACR. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (PAY1 : bytes_at a0segs m1 src payload).
    { eapply bytes_at_transport; [exact PAY | exact MUL1 |]. clear - LIN ACR G1 G2 G3 G4. cbn [disjoint_from]. lia. }
    clear STRM PAY MUL1.
    rewrite ST10, HBB, HBL in HD1.
    set (h0 := g10_hd h 10 0 0 (sh_n h)).
    assert (HD0 : rw_cells a0segs m1 S (HEAD_CELLS h0)) by exact HD1. clear HD1.
    rewrite Hstrm.
    (* [comment removed for export] *)
    eapply (A0F_g10_M1 A Q m GL GS ANS SEPst SEPsrc SEPtsrc SHS SHT SHP) with (h := h0) (b := b);
      [ exact MU1 | exact WM1 | exact HD0 | exact Hstrm | reflexivity | cbn; lia | exact HN | exact L1 | exact L2 | exact L3
      | exact STRM1 | exact Hsrc | exact Hlen | rewrite Hai; clear - G3; lia | rewrite TIL, Hai; f_equal; lia | exact PAY1 | exact FRL1 | exact FRH1 | exact ST1 | exact MI1 | | ].
    { eapply (g10_KXI m1 m1 b 10 10 0 (sh_n h)); [lia | symmetry; apply bupd_id | rewrite Hai; clear - G3; lia | exact SAV1 | exact AF1 | apply munch_refl | apply wmono_refl |].
      intros rc _ [[-> A0]|[-> (bx & NX & NE)]] junkD small dn.
      - rewrite (g10_pz_end payload [] 0 PZ0 eq_refl ltac:(clear - A0 Hai G4; lia)). apply dec10_eof0'.
      - replace (Z.to_nat (len - bs_ai b)) with 0%nat in NX by (clear - Hai; lia).
        rewrite (g10_pz_step payload [] 0 bx PZ0 eq_refl NX). cbn [app skipn]. apply dec10_bad0'; [apply g10_byte_range | exact NE]. }
    intros m2 b81 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? h1 HD2 NTH1 E81 STRM2 AI2 PAY2 FRL2 FRH2 ST2 MU2 WM2 MUL2 WML2 MI2.
    replace (Z.to_nat (len - bs_ai b)) with 0%nat in NTH1 by (clear - Hai; lia).
    pose proof (g10_pz_step payload [] 0 b81 PZ0 eq_refl NTH1) as PZ1. rewrite E81 in PZ1. cbn [app] in PZ1. clear PZ0 NTH1.
    set (b1 := bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b)) in *.
    (* [comment removed for export] *)
    eapply (A0F_g10_M2 A Q m GL GS ANS SEPst SEPsrc SEPtsrc SHS SHT SHP) with (h := h1) (b := b1);
      [ exact MU2 | exact WM2 | exact HD2 | exact Hstrm | reflexivity | cbn; lia | exact HN | exact L1 | exact L2 | exact L3
      | exact STRM2 | exact Hsrc | exact Hlen | cbn; clear - AI2 Hai G3; lia | cbn; f_equal; lia | exact PAY2 | exact FRL2 | exact FRH2 | exact ST2 | exact MI2 | | ].
    { eapply (g10_KXI m1 m2 b1 11 10 (0 * 256 + 66) (sh_n h)); [lia | reflexivity | cbn; clear - AI2; lia | exact SAV1 | exact AF1 | exact MUL2 | exact WML2 |].
      intros rc _ [[-> A0]|[-> (bx & NX & NE)]] junkD small dn; cbv delta [b1] in *; cbn [bs_ai bupd] in *.
      - rewrite (g10_pz_end payload [66]%Z 1 PZ1 eq_refl ltac:(clear - A0 Hai G4; lia)). apply dec10_eof1.
      - replace (Z.to_nat (len - (bs_ai b - 1))) with 1%nat in NX by (clear - Hai; lia).
        rewrite (g10_pz_step payload [66]%Z 1 bx PZ1 eq_refl NX). cbn [app skipn]. apply dec10_bad1; [apply g10_byte_range | exact NE]. }
    intros m3 b82 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? h2 HD3 NTH2 E82 STRM3 AI3 PAY3 FRL3 FRH3 ST3 MU3 WM3 MUL3 WML3 MI3.
    cbv delta [b1] in AI3, NTH2; cbn [bs_ai bupd] in AI3, NTH2.
    replace (Z.to_nat (len - (bs_ai b - 1))) with 1%nat in NTH2 by (clear - Hai; lia).
    pose proof (g10_pz_step payload [66]%Z 1 b82 PZ1 eq_refl NTH2) as PZ2. rewrite E82 in PZ2. cbn [app] in PZ2. clear PZ1 NTH2.
    set (b2 := bupd b1 (bs_ai b1 - 1) (Z_to_bv 64 (len - (bs_ai b1 - 1))) (bs_tih b1)) in *.
    pose proof (munch_trans _ _ _ _ MUL2 MUL3) as MUc3. pose proof (wmono_trans a0segs _ _ _ WML2 WML3) as WMc3.
    (* [comment removed for export] *)
    eapply (A0F_g10_M3 A Q m GL GS ANS SEPst SEPsrc SEPtsrc SHS SHT SHP) with (h := h2) (b := b2);
      [ exact MU3 | exact WM3 | exact HD3 | exact Hstrm | reflexivity | cbn; lia | exact HN | exact L1 | exact L2 | exact L3
      | exact STRM3 | exact Hsrc | exact Hlen | cbn; clear - AI3 Hai G3; lia | cbn; f_equal; lia | exact PAY3 | exact FRL3 | exact FRH3 | exact ST3 | exact MI3 | | ].
    { eapply (g10_KXI m1 m3 b2 12 11 ((0 * 256 + 66) * 256 + 90) (sh_n h)); [lia | reflexivity | cbn; clear - AI3; lia | exact SAV1 | exact AF1 | exact MUc3 | exact WMc3 |].
      intros rc _ [[-> A0]|[-> (bx & NX & NE)]] junkD small dn; cbv delta [b1 b2] in *; cbn [bs_ai bupd] in *.
      - rewrite (g10_pz_end payload [66; 90]%Z 2 PZ2 eq_refl ltac:(clear - A0 Hai G4; lia)). apply dec10_eof2.
      - replace (Z.to_nat (len - (bs_ai b - 1 - 1))) with 2%nat in NX by (clear - Hai; lia).
        rewrite (g10_pz_step payload [66; 90]%Z 2 bx PZ2 eq_refl NX). cbn [app skipn]. apply dec10_bad2; [apply g10_byte_range | exact NE]. }
    intros m4 b83 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? h3 HD4 NTH3 E83 STRM4 AI4 PAY4 FRL4 FRH4 ST4 MU4 WM4 MUL4 WML4 MI4.
    cbv delta [b1 b2] in AI4, NTH3; cbn [bs_ai bupd] in AI4, NTH3.
    replace (Z.to_nat (len - (bs_ai b - 1 - 1))) with 2%nat in NTH3 by (clear - Hai; lia).
    pose proof (g10_pz_step payload [66; 90]%Z 2 b83 PZ2 eq_refl NTH3) as PZ3. rewrite E83 in PZ3. cbn [app] in PZ3. clear PZ2 NTH3.
    set (b3 := bupd b2 (bs_ai b2 - 1) (Z_to_bv 64 (len - (bs_ai b2 - 1))) (bs_tih b2)) in *.
    pose proof (munch_trans _ _ _ _ MUc3 MUL4) as MUc4. pose proof (wmono_trans a0segs _ _ _ WMc3 WML4) as WMc4.
    (* [comment removed for export] *)
    eapply (A0F_g10_M4 A Q m GL GS ANS SEPst SEPsrc SEPtsrc SHS SHT SHP) with (h := h3) (b := b3);
      [ exact MU4 | exact WM4 | exact HD4 | exact Hstrm | reflexivity | cbn; lia | exact HN | exact L1 | exact L2 | exact L3
      | exact STRM4 | exact Hsrc | exact Hlen | cbn; clear - AI4 Hai G3; lia | cbn; f_equal; lia | exact PAY4 | exact FRL4 | exact FRH4 | exact ST4 | exact MI4 | | ].
    { eapply (g10_KXI m1 m4 b3 13 12 (((0 * 256 + 66) * 256 + 90) * 256 + 104) (sh_n h)); [lia | reflexivity | cbn; clear - AI4; lia | exact SAV1 | exact AF1 | exact MUc4 | exact WMc4 |].
      intros rc _ [[-> A0]|[-> (bx & NX & NE)]] junkD small dn; cbv delta [b1 b2 b3] in *; cbn [bs_ai bupd] in *.
      - rewrite (g10_pz_end payload [66; 90; 104]%Z 3 PZ3 eq_refl ltac:(clear - A0 Hai G4; lia)). apply dec10_eof3.
      - replace (Z.to_nat (len - (bs_ai b - 1 - 1 - 1))) with 3%nat in NX by (clear - Hai; lia).
        rewrite (g10_pz_step payload [66; 90; 104]%Z 3 bx PZ3 eq_refl NX). cbn [app skipn]. apply dec10_bad3; [apply g10_byte_range | exact NE]. }
    intros m5 b84 uc ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? h4 HD5 Ruc NTH4 E84 STRM5 AI5 PAY5 FRL5 FRH5 ST5 MU5 WM5 MUL5 WML5 MI5.
    cbv delta [b1 b2 b3] in AI5, NTH4; cbn [bs_ai bupd] in AI5, NTH4.
    replace (Z.to_nat (len - (bs_ai b - 1 - 1 - 1))) with 3%nat in NTH4 by (clear - Hai; lia).
    pose proof (g10_pz_step payload [66; 90; 104]%Z 3 b84 PZ3 eq_refl NTH4) as PZ4. rewrite E84 in PZ4. cbn [app] in PZ4. clear PZ3 NTH4.
    set (b4 := bupd b3 (bs_ai b3 - 1) (Z_to_bv 64 (len - (bs_ai b3 - 1))) (bs_tih b3)) in *.
    pose proof (munch_trans _ _ _ _ MUc4 MUL5) as MUc5. pose proof (wmono_trans a0segs _ _ _ WMc4 WML5) as WMc5.
    (* [comment removed for export] *)
    assert (SAV5 : rw_cells a0segs m5 (S + 64036) SAVE0_CELLS).
    { eapply rw_cells_transport; [exact SAV1 | exact MUc5 | exact WMc5 |]. unfold W10m, SAVE0_CELLS. clear - LIN ACR SEPst. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (AF5 : aframe A m5).
    { apply (aframe_tr A (W10m A) m1 m5 AF1 MUc5 WMc5); unfold W10m; cbn [disjoint_from].
      - clear - LIN ACR. lia.
      - clear - LIN ACR. lia.
      - clear - LIN ACR SEPfs SEPft. lia.
      - clear - LIN ACR SEPshs SEPsht. lia. }
    (* [comment removed for export] *)
    eapply (A0F_g10_C1 A Q m GL ANS ANT SEPst SHS SHT) with (h := h4) (b := b4) (uc := uc);
      [ exact MU5 | exact WM5 | exact HD5 | exact L1 | exact L2 | exact L3 | exact STRM5 | exact BZA | exact Ruc | exact ST5 | exact MI5 | | ].
    - (* [comment removed for export] *)
      intros m6 z11 z12 z13 SM0 HD6 STRM6 ST6 MU6 WM6 MUL6 WML6 MI6.
      unfold W10c1 in MUL6.
      assert (SAV6 : rw_cells a0segs m6 (S + 64036) SAVE0_CELLS).
      {{ eapply rw_cells_transport; [exact SAV5 | exact MUL6 | exact WML6 |]. unfold SAVE0_CELLS. clear - LIN ACR. cbn [disjoint_from cells_size csize Nat.add]. lia. }}
      assert (AF6 : aframe A m6).
      {{ apply (aframe_tr A _ m5 m6 AF5 MUL6 WML6); cbn [disjoint_from];
          [ clear - LIN ACR; lia | clear - LIN ACR; lia | clear - LIN ACR SEPfs; lia | clear - LIN ACR SEPshs; lia ]. }}
      assert (PAY6 : bytes_at a0segs m6 src payload).
      {{ eapply bytes_at_transport; [exact PAY5 | exact MUL6 |]. clear - LIN ACR G1 G2 G3 G4 SEPsrc. cbn [disjoint_from]. lia. }}
      pose proof (rw_cells_transport a0segs _ m5 m6 _ _ FRL5 MUL6 WML6 ltac:(clear - LIN ACR; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRL6.
      pose proof (rw_cells_transport a0segs _ m5 m6 _ _ FRH5 MUL6 WML6 ltac:(clear - LIN ACR; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRH6.
      cbv delta [b1 b2 b3 b4] in STRM6. unfold bupd in STRM6.
      cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in STRM6. rewrite ?Hsrc, ?Hlen, ?Hai in STRM6.
      eapply evt_eq; [ | eapply (KF m6 uc (skipn 4 (map bv_unsigned payload))) ];
        [ st_eq | exact PZ4 | exact Ruc | assumption
        | unfold g10_hd; hd_proj; rw_by HD6
        | bs_proj; rewrite ?Hsrc, ?Hlen, ?Hai; rw_by STRM6
        | exact SAV6 | exact PAY6 | exact FRL6 | exact FRH6 | exact AF6 | exact ST6 | exact MU6 | exact WM6 | exact MI6 ].
    - (* [comment removed for export] *)
      intros m6 z11 z12 z13 SM1 HD6 STRM6 ST6 MU6 WM6 MUL6 WML6 MI6.
      unfold W10c1 in MUL6.
      assert (SAV6 : rw_cells a0segs m6 (S + 64036) SAVE0_CELLS).
      {{ eapply rw_cells_transport; [exact SAV5 | exact MUL6 | exact WML6 |]. unfold SAVE0_CELLS. clear - LIN ACR. cbn [disjoint_from cells_size csize Nat.add]. lia. }}
      assert (AF6 : aframe A m6).
      {{ apply (aframe_tr A _ m5 m6 AF5 MUL6 WML6); cbn [disjoint_from];
          [ clear - LIN ACR; lia | clear - LIN ACR; lia | clear - LIN ACR SEPfs; lia | clear - LIN ACR SEPshs; lia ]. }}
      assert (PAY6 : bytes_at a0segs m6 src payload).
      {{ eapply bytes_at_transport; [exact PAY5 | exact MUL6 |]. clear - LIN ACR G1 G2 G3 G4 SEPsrc. cbn [disjoint_from]. lia. }}
      pose proof (rw_cells_transport a0segs _ m5 m6 _ _ FRL5 MUL6 WML6 ltac:(clear - LIN ACR; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRL6.
      pose proof (rw_cells_transport a0segs _ m5 m6 _ _ FRH5 MUL6 WML6 ltac:(clear - LIN ACR; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRH6.
      cbv delta [b1 b2 b3 b4] in STRM6. unfold bupd in STRM6.
      cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in STRM6. rewrite ?Hsrc, ?Hlen, ?Hai in STRM6.
      eapply evt_eq; [ | eapply (KS m6 uc (skipn 4 (map bv_unsigned payload))) ];
        [ st_eq | exact PZ4 | exact Ruc | assumption
        | unfold g10_hd; hd_proj; rw_by HD6
        | bs_proj; rewrite ?Hsrc, ?Hlen, ?Hai; rw_by STRM6
        | exact SAV6 | exact PAY6 | exact FRL6 | exact FRH6 | exact AF6 | exact ST6 | exact MU6 | exact WM6 | exact MI6 ].
  Qed.
End B.
End ACeilS1.

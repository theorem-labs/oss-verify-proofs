(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AllocWf AllocKit AllocRep AsAtomics F_memcpy AllocWalkKit AW_DepotFrame AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition realloc_mid_post (sp gp tp s0 s1 s4' s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (U n old : Z) (bs junk : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x197a10) sp gp tp t0 t1 t2 s0 s1 (wz AINST) s1 (wz 0) (wz 0) s0 (wz 1) a6 a7
                  (wz AINST) (wz (Z.min n old)) (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x196ae8) fc None m' (seg_rom asegs)
    /\ munch [(U, U + Z.min n old)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' U [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) bs ++ skipn (Z.to_nat (Z.min n old)) junk)].

Section Mid.
  Variables (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (U P n old : Z) (bs junk : list byte) (b1 : byte) (idw : word).
  Hypothesis Hs1 : s1 = wz P.
  Hypothesis UR : AIMG_TOP <= U /\ U + n <= 2^47.
  Hypothesis PR : AIMG_TOP + 16 <= P /\ P + old <= 2^47.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis OR : 0 <= old <= 64512.
  Hypothesis SEP : P + old <= U - 16 \/ U + n <= P - 16.   (* [comment removed for export] *)
  Hypothesis LBS : length bs = Z.to_nat old.
  Hypothesis LJ : length junk = Z.to_nat n.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis MCP : rw_cells asegs m AMEMCPYP_CELL [C8 (wz AREAL_MEMCPY)].   (* [comment removed for export] *)
  Hypothesis GOTM : rw_cells asegs m 0x5e7840 [C8 (wz AMEMCPYP_CELL)].   (* [comment removed for export] *)
  Hypothesis HDR : rw_cells asegs m (P + -16) [C1 (b8 2); C1 b1; C2 (wz 0); C4 (wz old); C8 idw].
  Hypothesis OLD : rw_cells asegs m P [CB (Z.to_nat old) bs].
  Hypothesis NEW : rw_cells asegs m U [CB (Z.to_nat n) junk].

  Theorem realloc_mid :
    evt asegs (realloc_mid_post sp gp tp s0 s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc m U n old bs junk)
      (MS (mkR (wz 0x19797c) sp gp tp t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 (wz AINST) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19797c) fc None m (seg_rom asegs)).
  Proof.
    subst s1. unfold AMEMCPYP_CELL, AREAL_MEMCPY, AINST, AIMG_TOP, wz in *.
    pose proof (munch_refl [(U, U + Z.min n old)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    fold (wz 0) (wz old). rewrite zx16_wz by lia. rewrite zx32_wz by lia. rewrite (wz_unsigned 0) by lia. rewrite Z.shiftl_0_l.
    match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
      replace (Z.lor x y) with old by (rewrite ?unsigned_lit, ?wz_unsigned, Z.lor_0_l by lia; reflexivity) end.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      assert (MN : Z.min n old = n) by (clear - K; lia). rewrite MN in MU.
      (* [comment removed for export] *)
      step. step. step. step.
      pose proof (rw_cells_bytes_at asegs _ _ _ OLD) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      rewrite <- (firstn_skipn (Z.to_nat n) bs) in SRC. apply bytes_at_app in SRC. destruct SRC as [SRC _].
      callD memcpy_spec. all: rewrite ?wz_unsigned by lia. all: try exact SRC. all: try exact NEW. all: try eassumption.
      all: try (rewrite length_firstn, LBS; lia). all: try (clear - SEP NR OR UR PR K; lia).
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      apply evt_done. unfold realloc_mid_post, wz, AINST. rewrite MN.
      do 10 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv asegs _ |- _ => exact H end|].
      rewrite skipn_all2 by (rewrite LJ; lia). rewrite app_nil_r.
      lazymatch goal with H : rw_cells asegs _ U [CB _ (firstn _ bs)] |- _ => exact H end.
    - (* [comment removed for export] *)
      assert (MN : Z.min n old = old) by (clear - K; lia). rewrite MN in MU.
      (* [comment removed for export] *)
      step. step. step. step. step.
      pose proof (rw_cells_bytes_at asegs _ _ _ OLD) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      destruct (rw_cells_CB_split asegs _ U (Z.to_nat n) (Z.to_nat old) junk NEW ltac:(lia)) as [DST REST].
      callD memcpy_spec. all: rewrite ?wz_unsigned by lia. all: try exact SRC. all: try exact DST. all: try eassumption.
      all: try (rewrite LBS; lia). all: try (clear - SEP NR OR UR PR K; lia).
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      apply evt_done. unfold realloc_mid_post, wz, AINST. rewrite MN.
      do 10 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv asegs _ |- _ => exact H end|].
      rewrite (firstn_all2 bs) by (rewrite LBS; lia).
      lazymatch goal with H1 : rw_cells asegs ?mx U [CB _ bs], H2 : rw_cells asegs ?mx (U + _) [CB _ (skipn _ junk)] |- _ =>
        assert (J : rw_cells asegs mx U ([CB (Z.to_nat old) bs] ++ [CB (Z.to_nat n - Z.to_nat old) (skipn (Z.to_nat old) junk)]));
        [ apply (proj2 (rw_cells_app asegs mx U _ _)); split; [exact H1|];
          match goal with |- rw_cells _ _ ?a _ => replace a with (U + Z.of_nat (Z.to_nat old)) by (cbn [cells_size csize]; lia) end; exact H2 |] end.
      pose proof (rw_cells_merge asegs _ U [] [CB (Z.to_nat old) bs; CB (Z.to_nat n - Z.to_nat old) (skipn (Z.to_nat old) junk)] [] ltac:(rewrite app_nil_r; exact J)) as J2.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in J2. rewrite ?app_nil_r, ?Nat.add_0_r in J2.
      match type of J2 with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat n) in J2 by lia end. exact J2.
  Qed.
End Mid.
End HCW.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg huf411_kit_rs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Cells.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Ltac ft_al := lazymatch goal with
  | |- context [?a mod 4] => match goal with H : rsk_al a 4 |- _ => pose proof (rsk_al_e a 4 H); lia end
  end.

Ltac ft_cf :=
  first [ match goal with H : ?T |- _ => lazymatch T with context [ALU_SLTU] => idtac end;
                                       lazymatch type of T with Prop => idtac end; solve [kx_ub_fast H] end
        | solve [exfalso; kx_lia]
        | match goal with H : ?T |- _ => lazymatch T with context [edenot] => idtac end;
                                       lazymatch type of T with Prop => idtac end; solve [kx_ub H] end ].

Ltac ft_ck := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x220dc) _ _ _ _) => ft_cf
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2213c) _ _ _ _) => ft_cf
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22180) _ _ _ _) => ft_cf
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22188) _ _ _ _) => ft_cf
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22190) _ _ _ _) => ft_cf
  | _ => idtac end.

Ltac ft_r24 D := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch P with
      | ?a + _ => tryif constr_eq a D then idtac else replace P with (D + (P - D)) by lia
      | _ => replace P with (D + (P - D)) by lia
      end
  end.

Ltac ft_k24 D K := ft_r24 D;
  lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?J)) _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply (K _ J); try eassumption; lia
  end.

Ltac ft_r30 E := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _) _ _ _ _ _ _) =>
      tryif constr_eq P E then idtac else replace P with E by lia
  end.

Ltac ft_s8 E := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      tryif constr_eq P E then idtac else replace P with E by lia
  end.

Ltac ft_s23 E := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      tryif constr_eq P E then idtac else replace P with E by lia
  end.
Ltac ft_s18 E := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      tryif constr_eq P E then idtac else replace P with E by lia
  end.

Ltac ft_w22 := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Q _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch Q with
      | Z_to_bv 64 _ => idtac
      | _ => replace Q with (Z_to_bv 64 (bv_unsigned Q)) by apply Z_to_bv_bv_unsigned
      end
  end.


Ltac ft_s26 E := lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _) _ _ _ _ _ _) =>
      tryif constr_eq P E then idtac else replace P with E by lia
  end.

Lemma ft_frs15 : forall segs m S (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : word),
  rw_cells segs m (S + -512) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11;
                              C8 c12; C8 c13; C8 c14; C8 c15] ->
  rw_cells segs m (S + -392) [C8 c15].
Proof.
  intros segs m S c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 H.
  apply (ZdWalkKit.rw_cells_app segs m (S + -512)
           [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14]
           [C8 c15]) in H.
  destruct H as [_ H].
  replace (S + -392) with (S + -512 + Z.of_nat (cells_size
           [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14]))
    by (cbn; lia).
  exact H.
Qed.

Lemma ft_frame408 : forall segs m S c1 c2 c3,
  rw_cells segs m (S + -512) c1 -> rw_cells segs m (S + -384) c2 -> rw_cells segs m (S + -232) c3 ->
  cells_size c1 = 128%nat -> cells_size c2 = 152%nat -> cells_size c3 = 128%nat ->
  rw_cells segs m (S + -512) (c1 ++ c2 ++ c3) /\ cells_size (c1 ++ c2 ++ c3) = 408%nat.
Proof.
  intros segs m S c1 c2 c3 H1 H2 H3 Z1 Z2 Z3. split.
  - apply ZdWalkKit.rw_cells_app. split; [exact H1|]. rewrite Z1.
    replace (S + -512 + Z.of_nat 128) with (S + -384) by lia.
    apply ZdWalkKit.rw_cells_app. split; [exact H2|]. rewrite Z2.
    replace (S + -384 + Z.of_nat 152) with (S + -232) by lia. exact H3.
  - rewrite !Cells.cells_size_app, Z1, Z2, Z3. reflexivity.
Qed.

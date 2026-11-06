(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts AsanKit DecCutA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTacFA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Ltac djA_atom e :=
  lazymatch e with
  | Z.add ?a _ => djA_atom a
  | Z.sub ?a _ => djA_atom a
  | _ => e
  end.
Ltac djA_cls e :=
  let a := djA_atom e in
  lazymatch a with
  | b_s _ => constr:(1) | b_strm _ => constr:(2) | b_src _ => constr:(3) | a_fb _ => constr:(4) | a_shf _ => constr:(5)
  | b_tt _ => constr:(6) | b_ll16 _ => constr:(7) | b_ll4 _ => constr:(8)
  | Zpos _ => constr:(9) | a_P _ => constr:(10) | bv_unsigned (a_sp _) => constr:(10) | a_lo _ => constr:(10)
  | _ => constr:(0)
  end.
(* [comment removed for export] *)
Ltac pjn k X := lazymatch k with 1%nat => constr:(proj1 X) | S ?k' => pjn k' constr:(proj2 X) end.
Ltac pjl n X := lazymatch n with 0%nat => X | S ?n' => pjl n' constr:(proj2 X) end.
(* [comment removed for export] *)
Ltac djA_tt AOK k :=
  match goal with SM : b_small _ = 0 |- _ =>
    let X := constr:(act_tt _ _ AOK SM) in
    pose proof (proj1 X);
    lazymatch k with
    | 0%nat => idtac
    | 6%nat => let P := pjl 5%nat X in pose proof P
    | _ => let P := pjn k X in pose proof P
    end end.
Ltac djA_ll AOK k :=
  match goal with SM : b_small _ = 1 |- _ =>
    let X := constr:(act_ll _ _ AOK SM) in
    pose proof (proj1 X);
    lazymatch k with
    | 0%nat => idtac
    | 12%nat => let P := pjl 11%nat X in pose proof P
    | _ => let P := pjn k X in pose proof P
    end end.
Ltac djA_pair AOK x y :=
  let p := constr:((x, y)) in
  lazymatch p with
  | (?u, ?u) => lazymatch u with 6 => djA_tt AOK 0%nat | 7 => djA_ll AOK 0%nat | 8 => djA_ll AOK 0%nat | _ => idtac end
  | (10, 6) => djA_tt AOK 0%nat | (6, 10) => djA_tt AOK 0%nat
  | (10, 7) => djA_ll AOK 0%nat | (7, 10) => djA_ll AOK 0%nat | (10, 8) => djA_ll AOK 0%nat | (8, 10) => djA_ll AOK 0%nat
  | (10, _) => idtac | (_, 10) => idtac
  | (1, 2) => pose proof (act_sep_s_strm _ _ AOK) | (2, 1) => pose proof (act_sep_s_strm _ _ AOK)
  | (1, 3) => pose proof (act_sep_s_src _ _ AOK) | (3, 1) => pose proof (act_sep_s_src _ _ AOK)
  | (2, 3) => pose proof (act_sep_strm_src _ _ AOK) | (3, 2) => pose proof (act_sep_strm_src _ _ AOK)
  | (4, 1) => pose proof (proj1 (act_sep_fb _ _ AOK)) | (1, 4) => pose proof (proj1 (act_sep_fb _ _ AOK))
  | (4, 2) => pose proof (proj1 (proj2 (act_sep_fb _ _ AOK))) | (2, 4) => pose proof (proj1 (proj2 (act_sep_fb _ _ AOK)))
  | (4, 3) => pose proof (proj1 (proj2 (proj2 (act_sep_fb _ _ AOK)))) | (3, 4) => pose proof (proj1 (proj2 (proj2 (act_sep_fb _ _ AOK))))
  | (4, 5) => pose proof (proj2 (proj2 (proj2 (act_sep_fb _ _ AOK)))) | (5, 4) => pose proof (proj2 (proj2 (proj2 (act_sep_fb _ _ AOK))))
  | (5, 1) => pose proof (proj1 (act_sep_shf _ _ AOK)) | (1, 5) => pose proof (proj1 (act_sep_shf _ _ AOK))
  | (5, 2) => pose proof (proj1 (proj2 (act_sep_shf _ _ AOK))) | (2, 5) => pose proof (proj1 (proj2 (act_sep_shf _ _ AOK)))
  | (5, 3) => pose proof (proj2 (proj2 (act_sep_shf _ _ AOK))) | (3, 5) => pose proof (proj2 (proj2 (act_sep_shf _ _ AOK)))
  | (9, 1) => pose proof (act_img_s _ _ AOK) | (1, 9) => pose proof (act_img_s _ _ AOK)
  | (9, 2) => pose proof (act_img_strm _ _ AOK) | (2, 9) => pose proof (act_img_strm _ _ AOK)
  | (9, 4) => pose proof (act_img_fb _ _ AOK) | (4, 9) => pose proof (act_img_fb _ _ AOK)
  | (9, 5) => pose proof (proj2 (proj2 (proj2 (act_img_sb _ _ AOK)))) | (5, 9) => pose proof (proj2 (proj2 (proj2 (act_img_sb _ _ AOK))))
  (* [comment removed for export] *)
  | (1, 6) => djA_tt AOK 2%nat | (6, 1) => djA_tt AOK 2%nat | (2, 6) => djA_tt AOK 3%nat | (6, 2) => djA_tt AOK 3%nat
  | (3, 6) => djA_tt AOK 4%nat | (6, 3) => djA_tt AOK 4%nat | (4, 6) => djA_tt AOK 5%nat | (6, 4) => djA_tt AOK 5%nat
  | (5, 6) => djA_tt AOK 6%nat | (6, 5) => djA_tt AOK 6%nat
  | (9, 6) => djA_tt AOK 0%nat; match goal with SM : b_small _ = 0 |- _ => pose proof (act_img_tt _ _ AOK SM) end
  | (6, 9) => djA_tt AOK 0%nat; match goal with SM : b_small _ = 0 |- _ => pose proof (act_img_tt _ _ AOK SM) end
  (* [comment removed for export] *)
  | (1, 7) => djA_ll AOK 2%nat | (7, 1) => djA_ll AOK 2%nat | (2, 7) => djA_ll AOK 3%nat | (7, 2) => djA_ll AOK 3%nat
  | (3, 7) => djA_ll AOK 4%nat | (7, 3) => djA_ll AOK 4%nat | (4, 7) => djA_ll AOK 5%nat | (7, 4) => djA_ll AOK 5%nat
  | (5, 7) => djA_ll AOK 6%nat | (7, 5) => djA_ll AOK 6%nat
  | (9, 7) => djA_ll AOK 0%nat; match goal with SM : b_small _ = 1 |- _ => pose proof (proj1 (act_img_ll _ _ AOK SM)) end
  | (7, 9) => djA_ll AOK 0%nat; match goal with SM : b_small _ = 1 |- _ => pose proof (proj1 (act_img_ll _ _ AOK SM)) end
  (* [comment removed for export] *)
  | (1, 8) => djA_ll AOK 7%nat | (8, 1) => djA_ll AOK 7%nat | (2, 8) => djA_ll AOK 8%nat | (8, 2) => djA_ll AOK 8%nat
  | (3, 8) => djA_ll AOK 9%nat | (8, 3) => djA_ll AOK 9%nat | (4, 8) => djA_ll AOK 10%nat | (8, 4) => djA_ll AOK 10%nat
  | (5, 8) => djA_ll AOK 11%nat | (8, 5) => djA_ll AOK 11%nat
  | (9, 8) => djA_ll AOK 0%nat; match goal with SM : b_small _ = 1 |- _ => pose proof (proj2 (act_img_ll _ _ AOK SM)) end
  | (8, 9) => djA_ll AOK 0%nat; match goal with SM : b_small _ = 1 |- _ => pose proof (proj2 (act_img_ll _ _ AOK SM)) end
  | (7, 8) => djA_ll AOK 12%nat | (8, 7) => djA_ll AOK 12%nat
  | _ => idtac
  end.
Ltac djA_conj AOK :=
  lazymatch goal with
  | |- (?a + _ <= ?lo \/ _)%Z => let x := djA_cls a in let y := djA_cls lo in djA_pair AOK x y; slia
  | |- (?a <= ?lo \/ _)%Z => let x := djA_cls a in let y := djA_cls lo in djA_pair AOK x y; slia
  | |- True => exact I
  | |- _ => slia
  end.
Ltac djA_all AOK :=
  lazymatch goal with
  | |- _ /\ _ => split; [ djA_conj AOK | djA_all AOK ]
  | |- _ => djA_conj AOK
  end.
(* [comment removed for export] *)
Ltac djA_slim :=
  repeat match goal with K : ?T |- _ =>
    lazymatch T with
    | Z.of_nat (length _) = _ => fail
    | length _ = _ => fail
    | act_ok _ _ => fail
    | b_small _ = _ => fail
    | dpure _ _ _ _ _ => fail
    | _ => clear K
    end end.
Ltac revive_djA AOK :=
  djA_slim;
  pose proof alloc_ceiling_range; pose proof (alin_core _ _ AOK);
  try match goal with DP : dpure _ _ _ _ _ |- _ => pose proof (dpure_cf_len _ _ _ _ _ DP); clear DP end;
  cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; djA_all AOK.

Ltac revive_smA H AOK MUL WML :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?Ad ?cs => apply (rw_cells_transport segs W me m' Ad cs) in H; [ | exact MUL | exact WML | revive_djA AOK ]
  | ro_cells ?segs me ?Ad ?cs => apply (ro_cells_transport segs W me m' Ad cs) in H; [ | exact MUL | revive_djA AOK ]
  | u32arr ?segs me ?Ad ?ws => apply (u32arr_transport segs W me m' Ad ws) in H; [ | exact MUL | exact WML | revive_djA AOK ]
  | u8arr ?segs me ?Ad ?bs => apply (u8arr_transport segs W me m' Ad bs) in H; [ | exact MUL | exact WML | revive_djA AOK ]
  | bytes_at ?segs me ?Ad ?bs => apply (bytes_at_transport segs W me m' Ad bs) in H; [ | exact MUL | revive_djA AOK ]
  | drest_at ?segs me ?Sd ?r =>
      apply (drest_transport segs W me m' Sd r) in H; [ | exact MUL | exact WML | revive_djA AOK | revive_djA AOK | revive_djA AOK ]
  | blk_at ?segs me ?cxx ?k =>
      apply (blk_at_transport segs W me m' cxx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          first [ exfalso; match goal with SM0 : b_small _ = _ |- _ => clear - E SM0; congruence end | revive_djA AOK ] ]
  end end.
Ltac revive_all_smA AOK MUL WML :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive_smA H AOK MUL WML | fail 100 "cannot revive (smA)" H ] end.

(* [comment removed for export] *)
Ltac unfold_blk SM MU :=
  unfold blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app] in MU;
  repeat match goal with H : shzW _ ?W _ _ _ |- _ => lazymatch W with context [blk_ivls _] => unfold blk_ivls in H; rewrite SM in H; cbn [Z.eqb app] in H end end;
  repeat match goal with H : shpW _ ?W _ _ _ |- _ => lazymatch W with context [blk_ivls _] => unfold blk_ivls in H; rewrite SM in H; cbn [Z.eqb app] in H end end;
  repeat match goal with H : _ /\ _ |- _ => lazymatch type of H with context [blk_ivls _] => unfold blk_ivls in H; rewrite SM in H; cbn [Z.eqb app] in H end end.

(* [comment removed for export] *)
Ltac open_shb SM :=
  match goal with SHBx : (_ = 0 -> _) /\ (_ = 1 -> _) |- _ =>
    let B0 := fresh "SHB0" in let B1 := fresh "SHB1" in
    destruct SHBx as [B0 B1];
    first [ first [ specialize (B0 SM) | specialize (B0 eq_refl) ]; clear B1; rename B0 into SHTT
          | first [ specialize (B1 SM) | specialize (B1 eq_refl) ]; clear B0; let S16 := fresh "SH16" in let S4 := fresh "SH4" in destruct B1 as [S16 S4] ]
  end.

(* [comment removed for export] *)
Ltac DecTacFA.aframe_dj AOK ::= revive_djA AOK.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac off_image_solve L ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app]; try rewrite !Arr.upd_length;
  first [ assumption
        | apply (@off_image_stack _ L _); lia
        | match goal with H : off_image _ _ _ |- _ =>
            apply (off_image_sub L _ _ _ _ H); cbn [Cells.cells_size Cells.csize Nat.add length app]; lia end
        | match goal with H : app_rangeF _ ?p ?n |- _ =>
            apply (off_image_sub L _ _ _ _ (off_image_app L p n H)); cbn [Cells.cells_size Cells.csize Nat.add length app]; lia end
        | match goal with H : app_range _ ?p ?n |- _ =>
            apply (off_image_sub L _ _ _ _ (off_image_app L p n H)); cbn [Cells.cells_size Cells.csize Nat.add length app]; lia end ].

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img A_Cocsh A_Tac.
Ltac henv_side GLOB HSH HG CE MU WM ST ::=
  rewrite ?unsigned_lit by lia;
  first [ reflexivity
        | exact HG | exact ST | assumption
        | (eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
             intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia])
        | (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
        | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
        | (unfold WSASSERT_STACK, WSEMU_STACK, WSMARK_STACK; lia) ].

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import ShZero QcF IcptCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RODATA_LO : Z := 81920.
Definition RODATA_HI : Z := 147456.
Definition ffp_acx (segs : list Segment) (m : word -> option byte) (usp B n Fp : Z) : Prop :=
  aenv m /\ zsh m (usp - 4640) usp /\ zsh m B (B + n) /\ zsh m RODATA_LO RODATA_HI /\
  (0x10007fff8000 + 4640 <= usp <= 0x7fffffffff00)%Z /\ (B + n <= 0x7fffffffff00)%Z /\ (Fp + 148 <= 0x7fffffffff00)%Z.

Ltac open_acx :=
  lazymatch goal with
  | _ : aenv _ |- _ => idtac
  | H : ffp_acx _ _ _ _ _ _ |- _ =>
    let c := fresh "ACXc" in pose proof H as c;
    let a := fresh "AEx" in let z1 := fresh "ZSTx" in let z2 := fresh "ZBx" in let z3 := fresh "ZROx" in
    let h1 := fresh "SPHx" in let h2 := fresh "BHx" in let h3 := fresh "FHx" in
    destruct c as (a & z1 & z2 & z3 & h1 & h2 & h3); unfold RODATA_LO, RODATA_HI in z3
  | _ => idtac
  end.

Lemma shw_range0 : forall lo hi, app lo (hi - lo) -> SBZ <= shw_lo lo /\ shw_hi hi <= 0x10007fff8000.
Proof.
  intros lo hi Ha.
  assert (A1 : 64 <= lo /\ hi <= 0x7fffffffff00) by (destruct Ha as [[A1 A2]|[A1 A2]]; lia).
  pose proof (Z.div_le_mono 64 lo 8 ltac:(lia) ltac:(lia)) as HL. change (64 / 8) with 8 in HL.
  pose proof (Z.div_le_mono hi 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as HD.
  change (0x7fffffffff00 / 8) with 17592186044384 in HD.
  unfold shw_lo, shw_hi, SBZ. lia.
Qed.
Lemma zsh_transport0 : forall m m' W lo hi, zsh m lo hi -> munch W m m' -> in_app_all W -> app lo (hi - lo) -> zsh m' lo hi.
Proof.
  intros m m' W lo hi Z MU HW Ha y Hy.
  pose proof (shw_range0 lo hi Ha) as (R1 & R2).
  assert (Hy2 : 0 <= y < 2^64) by (unfold shw_lo, shw_hi, SBZ in *; lia).
  rewrite (MU (wa y)). { apply Z, Hy. }
  rewrite wa_unsigned by exact Hy2. apply outside_app; [exact HW|]. unfold shw_lo, shw_hi, SBZ in *; lia.
Qed.

Ltac room_lia :=
  first [ lia
        | (repeat match goal with H : length ?x = _ |- context [length ?x] => rewrite H end); lia ].

Ltac hw_lia := apply high_in_app_all; cbn; lia.

Ltac zsh_side :=
  lazymatch goal with |- zsh ?mm ?lo ?hi =>
    first [ match goal with Z : zsh mm ?lo0 ?hi0 |- _ => eapply zsh_sub; [exact Z | room_lia | room_lia] end
          | match goal with Z : zsh ?m0 ?lo0 ?hi0, MU : munch ?W ?m0 mm |- _ =>
              eapply zsh_sub; [eapply zsh_transport0; [exact Z | exact MU | hw_lia | unfold app; first [right; lia | left; lia]] | room_lia | room_lia ] end ]
  end.

Ltac asan_side :=
  open_acx;
  lazymatch goal with
  | |- aenv ?mm =>
      first [ assumption
            | match goal with A : aenv ?m0, MU : munch ?W ?m0 mm |- _ => refine (aenv_munch _ _ _ _ MU A); cbn; lia end ]
  | |- zsh ?mm ?lo ?hi => zsh_side
  | |- shz ?segs ?mm ?p ?n =>
      first [ match goal with S : shz _ mm p n |- _ => exact S end
            | match goal with S : shz _ ?m0 p n, MU : munch ?W ?m0 mm |- _ =>
                eapply shz_transport; [exact S | exact MU | hw_lia | unfold app; left; lia] end
            | apply shz_of_zsh; [ zsh_side | unfold app; first [right; room_lia | left; room_lia] ] ]
  | |- shk ?segs ?mm ?p ?n =>
      first [ match goal with S : shk _ mm p n |- _ => exact S end
            | match goal with S : shk _ ?m0 p n, MU : munch ?W ?m0 mm |- _ =>
                eapply shk_transport; [exact S | exact MU | hw_lia | unfold app; first [right; room_lia | left; room_lia]] end
            | apply shk_of_zsh; [ zsh_side | unfold app; first [right; room_lia | left; room_lia] ] ]
  | |- app _ _ => unfold app; first [ right; room_lia | left; room_lia ]
  | _ => room_lia
  end.

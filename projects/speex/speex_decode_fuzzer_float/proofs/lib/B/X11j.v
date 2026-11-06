(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm
X0ys X0x2 X0yt X0zq X11l X11k X0x1 X0yq X11n.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Export X0zo.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0qz.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sb_bufs_agree : forall (s : sbd_state bptr) S a j (m m' : mem),
sb_bufs bsegs m a j -> sb_junk_ok s j -> agree_blocks bsegs m m' (tl (sb_blocks s S a)) -> sb_bufs bsegs m' a j.
Proof.
intros s S a j m m' (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7) (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) AG.
unfold sb_bufs. repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_agree_at; [eassumption|]);
[ eapply (agree_blocks_at bsegs m m' _ (sbd_g0_mem s, a_g0 a, 256)) | eapply (agree_blocks_at bsegs m m' _ (sbd_g1_mem s, a_g1 a, 256))
| eapply (agree_blocks_at bsegs m m' _ (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s))
| eapply (agree_blocks_at bsegs m m' _ (sbd_old_qlsp s, a_oq a, 32)) | eapply (agree_blocks_at bsegs m m' _ (sbd_interp_qlpc s, a_iq a, 32))
| eapply (agree_blocks_at bsegs m m' _ (sbd_mem_sp s, a_msp a, 64))
| eapply (agree_blocks_at bsegs m m' _ (sbd_pi_gain s, a_pg a, 16)) | eapply (agree_blocks_at bsegs m m' _ (sbd_exc_rms s, a_er a, 16)) ];
try exact AG; try eassumption;
try (cbn; tauto); unfold blk_addr, blk_size; cbn [fst snd]; rewrite ?cells_size_f32; lia.
Qed.

Lemma NoDup_app_in_neq {A} (l1 l2 : list A) x y : List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
intros ND H1 H2 ->. induction l1 as [|z l1 IH]; [destruct H1|].
cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct H1 as [->|H1].
- apply NI. apply in_app_iff. right. exact H2.
- exact (IH ND H1).
Qed.

Ltac gslot := cbn [fupds Nat.eqb]; first [reflexivity | eassumption].

Tactic Notation "sb_unpack" hyp(X) "as" simple_intropattern(P) := let Xc := fresh "Xc" in pose proof X as Xc; apply sb_pieces_iff in Xc; destruct Xc as P.

Ltac pk_all AG :=
lazymatch type of AG with
| agree_blocks bsegs ?m ?m' (tl (sb_blocks ?s ?S ?a) ++ ?LBL) =>
let AGB := fresh "AGB" in let AGL := fresh "AGL" in
assert (AGB : agree_blocks bsegs m m' (tl (sb_blocks s S a)))
by (eapply agree_blocks_sub; [exact AG| let b := fresh in let Hb := fresh in intros b Hb; apply in_app_iff; left; exact Hb]);
assert (AGL : agree_blocks bsegs m m' LBL)
by (eapply agree_blocks_sub; [exact AG| let b := fresh in let Hb := fresh in intros b Hb; apply in_app_iff; right; exact Hb]);
repeat match goal with
| H : sb_bufs bsegs m a ?j, JOK : sb_junk_ok _ ?j |- _ => apply (sb_bufs_agree s S a j m m') in H; [| exact JOK | exact AGB]
end;
pk_blocks AGL; clear AGB AGL
end.

Ltac pk_munch_all MU WM LALL ERR_rep OUT_rep IO_FP IO_img tacB tacI :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks bsegs m m' LALL)
by (apply (agree_blocks_of_munch bsegs W m m' LALL MU WM); let b := fresh "b" in let x := fresh "x" in let Hb := fresh "Hb" in let Hx := fresh "Hx" in
intros b x Hb Hx; tacB b x Hb Hx);
unfold LALL in AG; pk_all AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; apply (fp_local_munch IO_FP P W m m' L IO_img MU); [| exact Pm];
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SEGTOP_A in Hx; tacI x Hx);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.
Ltac pk_pres_all RT PRES WM LALL BL ERR_rep OUT_rep IO_FP IO_img :=
lazymatch type of PRES with
| rt_pres (rt_live RT ?Σ1) ?frames ?sp ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks bsegs m m' LALL) by (exact (agree_blocks_of_pres RT Σ1 frames sp m m' LALL PRES WM BL));
unfold LALL in AG; pk_all AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (fp_local_pres IO_FP P (rt_live RT Σ1) frames sp m m' L IO_img PRES Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.


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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068 X05a
X07y X0b3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X000.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sb_outside_app : forall (W1 W2 : list (Z * Z)) x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[a b] W1 IH]; intros W2 x H1 H2; [exact H2|]. cbn [app outside] in *. destruct H1 as [H1 H1']. split; [exact H1| exact (IH W2 x H1' H2)]. Qed.

Lemma sb_outside_app_inv : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[a b] W1 IH]; intros W2 x H; [split; [exact I| exact H]|]. cbn [app outside] in *. destruct H as [H H']. destruct (IH W2 x H') as [H1 H2]. split; [split; [exact H| exact H1]| exact H2]. Qed.

Ltac gslot := cbn [fupds Nat.eqb]; first [reflexivity | eassumption].

Tactic Notation "sb_unpack" hyp(X) "as" simple_intropattern(P) := let Xc := fresh "Xc" in pose proof X as Xc; apply sb_pieces_iff in Xc; destruct Xc as P.

Ltac pk_blocks AG :=
lazymatch type of AG with
| agree_blocks asegs ?m ?m' ?LBD =>
repeat match goal with
| H : ?c -> dec_exc_ready asegs m ?S ?d, R : DREP ?O ?ST m ?S ?d LBD |- _ =>
let H' := fresh "EXR" in
assert (H' : c -> dec_exc_ready asegs m' S d) by (let E := fresh in intros E; exact (dec_exc_ready_agree asegs _ _ _ _ _ _ _ _ d O ST m m' S LBD R (H E) AG));
clear H
end;
repeat match goal with
| R : DREP ?O ?ST m ?S ?d LBD |- _ => eapply decst_rep_agree in R; [| exact AG]
end
end.
Ltac pk_io ERR_rep OUT_rep KEEP :=
lazymatch type of KEEP with
| forall P, fp_local ?IO_FP P -> P ?m -> P ?m' =>
repeat match goal with
| H : ERR_rep m |- _ => apply (KEEP ERR_rep ltac:(assumption)) in H
| H : forall so, OUT_rep so ?m0 -> OUT_rep so m |- _ =>
let H' := fresh "OUTK" in
assert (H' : forall so, OUT_rep so m0 -> OUT_rep so m') by (let so := fresh in let X := fresh in intros so X; exact (KEEP (OUT_rep so) ltac:(auto) (H so X)));
clear H
end
end.

Ltac pk_munch MU WM LBD ERR_rep OUT_rep IO_FP IO_img tacB tacI :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks asegs m m' LBD)
by (apply (agree_blocks_of_munch asegs W m m' LBD MU WM); let b := fresh "b" in let x := fresh "x" in let Hb := fresh "Hb" in let Hx := fresh "Hx" in
intros b x Hb Hx; tacB b x Hb Hx);
pk_blocks AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; apply (fp_local_munch IO_FP P W m m' L IO_img MU); [| exact Pm];
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SEGTOP_A in Hx; tacI x Hx);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Ltac pk_pres RT PRES WM LBD BL ERR_rep OUT_rep IO_FP IO_img :=
lazymatch type of PRES with
| rt_pres (rt_live RT ?Σ1) ?frames ?sp ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks asegs m m' LBD) by (exact (agree_blocks_of_pres RT Σ1 frames sp m m' LBD PRES WM BL));
pk_blocks AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (fp_local_pres IO_FP P (rt_live RT Σ1) frames sp m m' L IO_img PRES Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Ltac pk_all AG :=
lazymatch type of AG with
| agree_blocks asegs ?m ?m' (tl (sb_blocks ?s ?S ?a) ++ ?LBL) =>
let AGB := fresh "AGB" in let AGL := fresh "AGL" in
assert (AGB : agree_blocks asegs m m' (tl (sb_blocks s S a)))
by (eapply agree_blocks_sub; [exact AG| let b := fresh in let Hb := fresh in intros b Hb; apply in_app_iff; left; exact Hb]);
assert (AGL : agree_blocks asegs m m' LBL)
by (eapply agree_blocks_sub; [exact AG| let b := fresh in let Hb := fresh in intros b Hb; apply in_app_iff; right; exact Hb]);
repeat match goal with
| H : sb_bufs asegs m a ?j, JOK : sb_junk_ok _ ?j |- _ => apply (sb_bufs_agree s S a j m m') in H; [| exact JOK | exact AGB]
end;
pk_blocks AGL; clear AGB AGL
end.

Ltac pk_munch_all MU WM LALL ERR_rep OUT_rep IO_FP IO_img tacB tacI :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks asegs m m' LALL)
by (apply (agree_blocks_of_munch asegs W m m' LALL MU WM); let b := fresh "b" in let x := fresh "x" in let Hb := fresh "Hb" in let Hx := fresh "Hx" in
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
assert (AG : agree_blocks asegs m m' LALL) by (exact (agree_blocks_of_pres RT Σ1 frames sp m m' LALL PRES WM BL));
unfold LALL in AG; pk_all AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (fp_local_pres IO_FP P (rt_live RT Σ1) frames sp m m' L IO_img PRES Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Ltac tr_fp PRES WM tacO :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cps_sizes Hx; split; [ aclient_tac ltac:(ulc) | tacO x Hx ]
| exact WM ]);
clear H; rename H' into H
end
end.

Ltac pk_io_fp PRES ERR_rep OUT_rep IO_FP IO_img tacI :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in let a := fresh "a" in let Ha := fresh "Ha" in
intros P L Pm; apply (L m m' Pm); intros a Ha; apply PRES; [right; left; exact (IO_img _ Ha)|];
pose proof (X000.client_static_range _ (IO_img _ Ha)) as Hy; unfold SEGTOP_A in Hy; tacI (bv_unsigned a) Hy);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

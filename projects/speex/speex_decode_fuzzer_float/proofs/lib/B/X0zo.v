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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0yt X0x1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0qz.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Blocks.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma live_apart : forall (Σ : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2].
Qed.

Definition blocks_in_live (Σ : rts RT) (L : list block) : Prop := forall b, In b L -> In (blk_addr b, blk_size b) (rt_live RT Σ).

Lemma agree_blocks_of_pres : forall (Σ : rts RT) frames sp (m m' : mem) L,
rt_pres (rt_live RT Σ) frames sp m m' -> wmono bsegs m m' -> blocks_in_live Σ L -> agree_blocks bsegs m m' L.
Proof.
intros Σ frames sp m m' L PRES WM BL x Hx (b & Hb & Hab). split; [| apply WM].
apply PRES. rewrite wa_unsigned by lia. right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| exact Hab].
Qed.

Lemma agree_blocks_of_pres_fp : forall (Σ : rts RT) frames sp W (m m' : mem) L,
rt_pres_fp (rt_live RT Σ) frames sp W m m' -> wmono bsegs m m' -> blocks_in_live Σ L ->
(forall b x, In b L -> blk_addr b <= x < blk_addr b + blk_size b -> outside W x) -> agree_blocks bsegs m m' L.
Proof.
intros Σ frames sp W m m' L PRES WM BL OUT x Hx (b & Hb & Hab). split; [| apply WM].
apply PRES; rewrite wa_unsigned by lia; [| exact (OUT b x Hb Hab)].
right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| exact Hab].
Qed.

Lemma outside_blocks_shadow : forall (Σ : rts RT) (m : mem) L x, ART RT Σ m -> blocks_in_live Σ L -> SH_LO <= x < SH_HI -> outside (blocks_ivs L) x.
Proof using AF.
intros Σ m L x ART0 BL Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (af_live_offshadow RT AF Σ m _ _ ART0 (BL b Hb)) as O. unfold SH_LO, SH_HI in Hx. lia.
Qed.

Lemma outside_blocks_app_r : forall L1 L2 x, outside (blocks_ivs (L1 ++ L2)) x -> outside (blocks_ivs L2) x.
Proof. intros L1 L2 x H. apply outside_blocks_ivs. intros b Hb. apply (proj1 (outside_blocks_ivs _ _) H). apply in_app_iff. right. exact Hb. Qed.
Lemma outside_blocks_app_l : forall L1 L2 x, outside (blocks_ivs (L1 ++ L2)) x -> outside (blocks_ivs L1) x.
Proof. intros L1 L2 x H. apply outside_blocks_ivs. intros b Hb. apply (proj1 (outside_blocks_ivs _ _) H). apply in_app_iff. left. exact Hb. Qed.

Lemma acc_of_pres_fp : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall x, SH_LO <= x < SH_HI -> outside W x) ->
acc bsegs m P n -> acc bsegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree bsegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
apply OFF. rewrite SA in R. lia.
Qed.

Lemma lbd_apart_live : forall (Σ : rts RT) (m : mem) L, ART RT Σ m -> blocks_in_live Σ L -> lbd_apart L.
Proof using AF.
intros Σ m L ART0 BL b1 b2 H1 H2 NE. apply (live_apart Σ m _ _ _ _ ART0 (BL b1 H1) (BL b2 H2)). exact NE.
Qed.
End Blocks.

Lemma sb_outside_app : forall (W1 W2 : list (Z * Z)) x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[a b] W1 IH]; intros W2 x H1 H2; [exact H2|]. cbn [app outside] in *. destruct H1 as [H1 H1']. split; [exact H1| exact (IH W2 x H1' H2)]. Qed.
Lemma sb_outside_app_inv : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[a b] W1 IH]; intros W2 x H; [split; [exact I| exact H]|]. cbn [app outside] in *. destruct H as [H H']. destruct (IH W2 x H') as [H1 H2]. split; [split; [exact H| exact H1]| exact H2]. Qed.
Ltac pk_blocks AG :=
lazymatch type of AG with
| agree_blocks bsegs ?m ?m' ?LBD =>
repeat match goal with
| H : ?c -> dec_exc_ready bsegs m ?S ?d, R : DREP ?O ?ST m ?S ?d LBD |- _ =>
let H' := fresh "EXR" in
assert (H' : c -> dec_exc_ready bsegs m' S d) by (let E := fresh in intros E; exact (dec_exc_ready_agree bsegs _ _ _ _ _ _ _ _ d O ST m m' S LBD R (H E) AG));
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
assert (AG : agree_blocks bsegs m m' LBD)
by (apply (agree_blocks_of_munch bsegs W m m' LBD MU WM); let b := fresh "b" in let x := fresh "x" in let Hb := fresh "Hb" in let Hx := fresh "Hx" in
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
assert (AG : agree_blocks bsegs m m' LBD) by (exact (agree_blocks_of_pres RT Σ1 frames sp m m' LBD PRES WM BL));
pk_blocks AG; clear AG;
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
| H : rw_cells bsegs m ?A ?cs |- _ =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H);
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
pose proof (B.X0qz.client_static_range _ (IO_img _ Ha)) as Hy; unfold SEGTOP_A in Hy; tacI (bv_unsigned a) Hy);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

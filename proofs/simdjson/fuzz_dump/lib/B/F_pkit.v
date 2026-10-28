(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import SFModel Arr SysStep ImageA FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import PrintfModelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import FX_lib F_fwritex F_printf_iface Printf_stdio_iface R_m2s F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import PrintfModelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VF_FRAME : Z := 368.

Ltac chkr_tr C MU := apply (chkr_munch _ _ _ _ _ C MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.
Ltac ictx_tr C MU WM := apply (ictx_munch _ _ _ C MU WM); intros ?x ?Hx; cbn [in_rl ICR outside] in *; unfold kHighShadowEnd in *; lia.

Lemma vf_chkr : forall lo sp Fp m m' p n, chkr m p n -> munch [(lo, sp); (Fp, Fp + 232)] m m' ->
  kHighShadowEnd + 8 <= lo -> (Fp + 232 <= SHADOW_LO \/ SHADOW_HI <= Fp) -> chkr m' p n.
Proof.
  intros lo sp Fp m m' p n H MU HSH HF. apply (chkr_munch _ m m' p n H MU).
  intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *. lia.
Qed.
Lemma vf_ictx : forall lo sp Fp m m', ictx m -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono bsegs m m' ->
  kHighShadowEnd + 8 <= lo -> 1517296 <= Fp -> Fp + 232 <= 1526144 -> ictx m'.
Proof.
  intros lo sp Fp m m' H MU WM HSH HF1 HF2. apply (ictx_munch _ m m' H MU WM).
  intros x Hx. cbn [in_rl ICR outside] in *. unfold kHighShadowEnd in *. lia.
Qed.

Lemma zb_length_k : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' ->
  kHighShadowEnd + 8 <= lo -> (Fp + 232 <= SHADOW_LO \/ SHADOW_HI <= Fp) ->
  arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU HSH HF. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HFs & PAD & NZ & D1 & D2 & D3 & D4 & CK). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact (vf_chkr lo sp Fp m m' _ _ CK MU HSH HF)].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length_k. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' ->
  kHighShadowEnd + 8 <= lo -> (Fp + 232 <= SHADOW_LO \/ SHADOW_HI <= Fp) ->
  args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU HSH HF; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells bsegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells bsegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells bsegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
  rw_cells bsegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
  rw_cells bsegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
Proof.
  intros until tail. intros FC. unfold file_cells in FC.
  apply (proj1 (rw_cells_app bsegs m A [_] _)) in FC. destruct FC as [F0 _].
  pose proof (rw_cells_recast m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
  apply (proj1 (rw_cells_app bsegs m A [_] _)) in F1. exact (proj1 F1).
Qed.

Lemma topok_none : topok_stmt TOPOK_none.
Proof. unfold topok_stmt, TOPOK_none. intros. exact I. Qed.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  Monad.implM bsegs (k tt) (f s) Q ms -> Monad.implM bsegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

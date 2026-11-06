(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/SegGxaSeamPf.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The model agreement the GXA seam at musl vfprintf takes, over segconf's grammar: lib/A/FMgxaSeamPf.v Section CoveredP
   (pf_model_agreeP, pt_pargs_shapeP, pf_text_bytesP) for seg_piece, with the model's argument list SegPfText.seg_pargs.
   - seg_model_agree: GXA's printf_model on a segconf format writes the text seg_text renders and returns its length,
     and its first pass accepts the format (SegPfText.seg_printf_text_ok, which covers every seg_piece, so no covered-piece
     predicate is needed);
   - seg_pargs_shape_pt: the model's arguments are FMgxaSeamPf.pt_parg_ok of the run's (the seam derives GXA's argument
     facts from that shape, FMgxaSeam.v sa_args_pf_pt / sa_args_ok_pt / sa_args_kept_pt);
   - seg_text_bytes: the text of fitting arguments is bytes; at PRel p by the released per-piece bytes arms
     (FMgxaSeamPf.v, FMpfArmPdSeam.v, FMpfArmPcSeam.v, FMpfArmPx04Seam.v, FMgxaSeam02x.v, FMpfArmPlluSeam.v), at the
     new pieces by the decimal digits of a nonnegative number and a prefix of a byte string.
   Pure: no machine state, no image value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMpfStep FMgxaSeamPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import SegPfStep SegPfText.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require
FMpfArmPdSeam FMpfArmPcSeam FMpfArmPx04Seam FMgxaSeam02x FMpfArmPlluSeam.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* ---- the model's arguments, in the shape the seam reads ---- *)
Lemma seg_parg_pt : forall a, seg_parg a = pt_parg a.
Proof. intros [v|u|s]; reflexivity. Qed.

Lemma seg_pargs_shape_pt : forall qs args T, seg_text qs args = Some T ->
  Forall2 pt_parg_ok args (seg_pargs qs args).
Proof.
intros qs args T HT. eapply Forall2_impl; [|exact (seg_pargs_shape qs args T HT)].
intros a pa [E|E]; [left; rewrite E; apply seg_parg_pt | right; exact E].
Qed.

(* ---- the text of fitting arguments is bytes ---- *)
Lemma seg_firstn_bytes : forall n (l : list Z), Forall (fun x => 0 < x < 256) l ->
  Forall (fun x => 0 <= x < 256) (firstn n l).
Proof.
induction n as [|n IH]; intros l Hl; [constructor|]. destruct l as [|x l]; [constructor|].
inversion Hl; subst. cbn [firstn]. constructor; [cbv beta; lia | apply IH; assumption].
Qed.

Lemma seg_step_bytes : forall q args c a', seg_code_ok q -> Forall pf_arg_fit args -> seg_step q args = Some (c, a') ->
  Forall (fun x => 0 <= x < 256) c.
Proof.
intros [p| | |] args c a' Hok HF H.
- rewrite seg_step_PRel in H. cbn [seg_code_ok] in Hok. destruct p as [b| | | | | | |].
  + exact (seam_bytes_arm_lit b args c a' Hok HF H).
  + exact (FMpfArmPdSeam.seam_bytes_arm_pd args c a' Hok HF H).
  + exact (FMpfArmPcSeam.seam_bytes_arm_c args c a' Hok HF H).
  + exact (FMpfArmPx04Seam.seam_bytes_arm_x04 args c a' Hok HF H).
  + exact (FMgxaSeam02x.seam_bytes_arm_px02 args c a' Hok HF H).
  + exact (FMpfArmPlluSeam.seam_bytes_arm_pllu args c a' Hok HF H).
  + exact (seam_bytes_arm_ps args c a' Hok HF H).
  + exact (seam_bytes_arm_pps args c a' Hok HF H).
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as <- _. unfold pf_udec. apply FMpfArmPlluSeam.pf_digits_bytes_llu; [|constructor].
  apply Z.mod_pos_bound. lia.
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as <- _. inversion HF as [|? ? Hu _]; subst. cbn [pf_arg_fit] in Hu.
  unfold pf_udec. apply FMpfArmPlluSeam.pf_digits_bytes_llu; [lia | constructor].
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as <- _. inversion HF as [|? ? Hs0 _]; subst. destruct Hs0 as [Hs _].
  exact (seg_firstn_bytes 24 s Hs).
Qed.

Lemma seg_text_bytes : forall qs args T, Forall seg_code_ok qs -> Forall pf_arg_fit args ->
  seg_text qs args = Some T -> Forall (fun x => 0 <= x < 256) T.
Proof.
induction qs as [|q qs IH]; intros args T HC HF HT.
- destruct args as [|a args]; cbn in HT; [injection HT as <-; constructor | discriminate].
- inversion HC as [|? ? Hc HC']; subst. rewrite seg_text_step in HT.
  destruct (seg_step q args) as [[c a']|] eqn:ES; [|discriminate HT].
  destruct (seg_text qs a') as [T'|] eqn:E; cbn in HT; [|discriminate HT]. injection HT as <-.
  destruct (seg_step_prefix q args c a' ES) as [used Eu].
  assert (HF' : Forall pf_arg_fit a') by (rewrite Eu in HF; apply Forall_app in HF; exact (proj2 HF)).
  apply Forall_app. split; [exact (seg_step_bytes q args c a' Hc HF ES) | exact (IH a' T' HC' HF' E)].
Qed.

(* ---- the agreement: GXA's model on a segconf format, with the model's own argument list ---- *)
Theorem seg_model_agree : forall (fmtb : list Z) (qs : list seg_piece) (args : list pf_arg) (T : list Z),
  seg_parse fmtb = Some qs -> seg_text qs args = Some T -> Forall pf_arg_fit args ->
  zlength T <= 2147483647 ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmtb ++ [0]) (seg_pargs qs args) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmtb ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmtb ++ [0]).
Proof.
intros fmtb qs args T HP HT HF HTl.
rewrite Forall_forall in HF.
assert (HI : forall v, In (AInt v) args -> -2^31 <= v < 2^31) by (intros v Hin; exact (HF _ Hin)).
assert (HU : forall u, In (AU64 u) args -> 0 <= u) by (intros u Hin; exact (proj1 (HF _ Hin))).
assert (HS : forall s, In (APtr s) args -> zlength s < 2147483647).
{ intros s Hin. destruct (HF _ Hin) as [_ Hl]. unfold zlength. lia. }
destruct (seg_printf_text_ok fmtb qs args T HP HT HI HU HTl (or_intror HS)) as (M & P1 & _ & BY).
split; [exact M | split; [exact P1 | exact BY]].
Qed.

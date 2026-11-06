(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxVal AxMem AxZZ AxState AxStep AxFetch AxSys AxJoin AxJoinSound AxOcc AxRun AxRunSound AxSplitSound AxAlignSound AxFresh AxFreshSound AxEntryRel AxEntry.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSys2 AxDisp AxFd AxFdEnc AxEntryS AxEntryFacts AxEntryFactsF AxTabs AxSumD AxSumCk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srun (segs : list Segment) (LIM : Z) (sysd : AST -> option (list AST)) (sum : Z -> AST -> option (list AST))
    (H : htable) (fuel : positive) (A0 : AST) : rstate :=
  run segs LIM H sysd sum fuel IEmpty A0.

Definition srun_ok (fin : AST -> bool) (rs : rstate) : bool :=
  match rs_status rs with RRun => true | _ => false end && is_nilb (rs_work rs) && is_nilb (rs_parked rs)
  && forallb fin (rs_final rs).

Lemma srun_ok_parts (fin : AST -> bool) (rs : rstate) : srun_ok fin rs = true ->
  rs_status rs = RRun /\ rs_work rs = [] /\ rs_parked rs = [] /\ forall B, In B (rs_final rs) -> fin B = true.
Proof.
  unfold srun_ok. intros H. apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hp]. apply andb_prop in H as [Hst Hw].
  rewrite forallb_forall in Hf. split; [destruct (rs_status rs); [reflexivity | discriminate | discriminate]|].
  split; [destruct (rs_work rs); [reflexivity | discriminate]|]. split; [destruct (rs_parked rs); [reflexivity | discriminate]|]. exact Hf.
Qed.

(* [comment removed for export] *)
Definition sum_ok (segs : list Segment) (cfg : SpuriousCfg) (LIM : Z) (fs0 : Fs.Fs) (sum : Z -> AST -> option (list AST)) : Prop :=
  forall (KT : valuation -> list byte -> TSet),
    (forall ρ o bs, KT ρ (o ++ bs) [] -> t_eq (KT ρ o) (t_emit (W 2 bs) (KT ρ (o ++ bs)))) ->
    forall k (A : AST) l, sum k A = Some l -> (forall B, In B l -> Sound segs cfg LIM (MR segs fs0) KT B) -> Sound segs cfg LIM (MR segs fs0) KT A.

Theorem asum_ck_ok (T : img_tabs) (segs : list Segment) (pc : N) (cfg : SpuriousCfg) (LIM : Z) :
  img_ok segs pc = true -> tabs_ok T = true -> cks_ok T segs = true -> forall fs0, sum_ok segs cfg LIM fs0 (asum_ck T segs LIM).
Proof.
  intros Himg HT Hck fs0 KT KT_emit k A l.
  exact (asum_ck_sound T HT segs Hck cfg LIM fs0 KT (img_low segs pc Himg) KT_emit k A l).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_none : TSet := fun _ => False.

Definition KTs (TT : list (list byte) -> TSet) (ρ : valuation) (o : list byte) : TSet :=
  match o with [] => TT (dec_argvB ρ) | _ :: _ => t_none end.

Lemma KTs_agree (TT : list (list byte) -> TSet) :
  forall ρ ρ' o, (forall x, entry_var x = true -> ρ' x = ρ x) -> KTs TT ρ' o = KTs TT ρ o.
Proof. intros ρ ρ' o H. unfold KTs. destruct o; [|reflexivity]. rewrite (dec_argvB_agree ρ ρ' H). reflexivity. Qed.

Lemma KTs_emit (TT : list (list byte) -> TSet) :
  forall ρ o bs, KTs TT ρ (o ++ bs) [] -> t_eq (KTs TT ρ o) (t_emit (W 2 bs) (KTs TT ρ (o ++ bs))).
Proof.
  intros ρ o bs H. destruct o as [|x o]; [|exact (False_ind _ H)].
  destruct bs as [|y bs]; [|exact (False_ind _ H)].
  cbn [app] in *. unfold W. cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_lo (segs : list Segment) : Z := reserved_top (segments_reserved segs) / 4096.
Definition brk_hi (segs : list Segment) : Z := (reserved_top (segments_reserved segs) + brk_aslr_max) / 4096.

(* [comment removed for export] *)
Definition start_A0 (segs : list Segment) (pc : N) (ph : PhdrInfo) : AST :=
  entry_state segs (Z.of_N pc) ph (entry_store (FL2 (brk_lo segs) (brk_hi segs))).

(* [comment removed for export] *)
Definition start_cert (segs : list Segment) (pc : N) (ph : PhdrInfo) (LIM : Z) (sum : Z -> AST -> option (list AST))
    (fin : AST -> bool) (H0 : htable) (fuel : positive) : bool :=
  srun_ok fin (srun segs LIM (sys_disp2 segs LIM) sum H0 fuel (start_A0 segs pc ph)).

Section Start.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo).
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Hypothesis Himg : img_ok segs pc = true.
Variable sum : Z -> AST -> option (list AST).
Hypothesis Hsum : forall fs0, sum_ok segs cfg LIM fs0 sum.

(* [comment removed for export] *)
Variable POST : list (list byte) -> Fs.Fs -> config -> Prop.
Variable fin : AST -> bool.
Hypothesis Hfin_out : forall B, fin B = true -> am_out (a_model B) = [].
(* [comment removed for export] *)
Hypothesis Hbridge : forall (fs0 : Fs.Fs) (B : AST), fin B = true ->
  forall ρ c, R segs amodel (MR segs fs0 ρ) LIM ρ B c ->
  forall T : TSet, (forall c', POST (dec_argvB ρ) fs0 c' -> realizes_cfg segs cfg c' T) -> realizes_cfg segs cfg c T.

Variables (H0 : htable) (fuel : positive).
Hypothesis Hcert : start_cert segs pc ph LIM sum fin H0 fuel = true.

Theorem startup_sound : forall (TT : list (list byte) -> TSet) (en : ExecEntry) (inp : ProcInput),
  valid_input inp -> valid_entry (mkImage segs pc ph) en inp ->
  (forall argv c, valid_argv argv -> POST argv (in_fs inp) c -> realizes_cfg segs cfg c (TT argv)) ->
  realizes_cfg segs cfg
    (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) LIM inp)
    (TT (in_argv inp)).
Proof.
  intros TT en inp Hinp Hent Hmain.
  assert (Hva : in_va_size inp = Sv48) by (destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  apply (proj1 (valid_entry_sv48 _ _ _ Hva)) in Hent. destruct en as [sp brk0 mbase draw]. destruct Hent as (Hsp & Hbrk & _ & Hfit).
  cbn [en_sp en_brk en_mmap_base en_draw] in *.
  pose proof (img_low segs pc Himg) as Hlow.
  set (fs0 := in_fs inp). set (KT := KTs TT).
  assert (Hs0 : sat (enc_b inp sp draw brk0) (entry_store (FL2 (brk_lo segs) (brk_hi segs)))).
  { apply sat_entry_store. exact (FL2_sat segs inp sp brk0 draw _ _ Hinp Hsp Hbrk Hfit (Z.le_refl _) (Z.le_refl _)). }
  pose proof (entry_R segs pc ph sp brk0 mbase draw LIM inp _ Hinp Hsp Hbrk Hfit Himg Hs0 (good_inp_enc inp sp brk0 draw Hinp)) as HR.
  destruct (srun_ok_parts _ _ Hcert) as [E1 [E2 [E3 E4]]].
  assert (HS : Sound segs cfg LIM (MR segs fs0) KT (start_A0 segs pc ph)).
  { apply (run_sound segs cfg LIM H0 (MR segs fs0) (MR_mat segs fs0) Hlow KT (sys_disp2 segs LIM) sum) with (ic := IEmpty) (p := fuel).
    - exact (sys_disp2_sound segs cfg Hcfg2 LIM fs0 KT (KTs_agree TT) Hlow).
    - intros A B J HJ HSn. exact (join_sound segs cfg LIM (MR segs fs0) (MR_next segs fs0) KT A B J HJ HSn).
    - intros A f cuts Hsp' HSn. exact (split_sound segs cfg LIM (MR segs fs0) KT A f cuts Hsp' HSn).
    - intros A v h k Hok' HSn. exact (fresh_sound segs cfg LIM (MR segs fs0) (MR_agree segs fs0) KT (KTs_agree TT) A v h k Hok' HSn).
    - intros A B r k Hfl HSn. exact (floor_sound segs cfg LIM (MR segs fs0) (MR_agree segs fs0) (MR_next segs fs0) KT (KTs_agree TT) A B r k Hfl HSn).
    - intros A r f cuts Hr Hxf Hsp' HSn. exact (split_reg_sound segs cfg LIM (MR segs fs0) KT A r f cuts Hr Hxf Hsp' HSn).
    - intros k A l Hs HSn. exact (Hsum fs0 KT (KTs_emit TT) k A l Hs HSn).
    - intros A B J Em Emod HJ HSn. exact (join_nm_sound segs cfg LIM (MR segs fs0) (MR_next segs fs0) KT A B J Em Emod HJ HSn).
    - intros A r k l Hal HSn. exact (align_sound segs cfg LIM (MR segs fs0) KT A r k l Hal HSn).
    - intros k e _ He. rewrite iget_empty in He. discriminate.
    - exact E1.
    - exact E2.
    - exact E3.
    - intros B HB ρ c HRB o Ho. pose proof (E4 B HB) as HfB.
      unfold out_val in Ho. rewrite (Hfin_out B HfB) in Ho. cbn [pieces_val] in Ho. subst o.
      unfold KT, KTs. apply (Hbridge fs0 B HfB ρ c HRB). intros c' Hpost. apply Hmain; [|exact Hpost].
      pose proof (mr_fds segs fs0 ρ _ _ (r_model _ _ _ _ _ _ _ HRB)) as [Hg _]. exact Hg. }
  pose proof (HS _ _ HR [] (entry_out (enc_b inp sp draw brk0) segs (Z.of_N pc) ph (entry_store (FL2 (brk_lo segs) (brk_hi segs))))) as Hz.
  unfold KT, KTs in Hz. rewrite (dec_argvB_enc inp sp brk0 draw Hinp) in Hz. exact Hz.
Qed.

End Start.

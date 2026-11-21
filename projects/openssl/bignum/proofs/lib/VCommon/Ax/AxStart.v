(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv layout and the vDSO). *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxMem AxZZ AxState AxStep AxFetch AxSys AxJoin AxJoinSound AxOcc AxRun AxRunSound AxSplitSound AxAlignSound AxFresh AxFreshSound AxEntryRel AxEntry.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel AxSys2 AxDisp AxFd AxFdEnc AxEntryS AxEntryFacts AxEntryFactsF AxTabs AxSumD AxSumCk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

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

Definition sum_ok (segs : list Segment) (cfg : SpuriousCfg) (LIM : Z) (fs0 : Fs.Fs) (sum : Z -> AST -> option (list AST)) : Prop :=
  forall (KT : valuation -> list byte -> TSet),
    (forall ρ o bs, KT ρ (o ++ bs) [] -> t_eq (KT ρ o) (t_emit (W 2 bs) (KT ρ (o ++ bs)))) ->
    forall k (A : AST) l, sum k A = Some l -> (forall B, In B l -> Sound segs cfg LIM (MR segs fs0) KT B) -> Sound segs cfg LIM (MR segs fs0) KT A.

(* The discriminant is a premise, not derivable here: img_ok is forallb seg_ok1 &&&
   segs_pw &&& two pc tests (AxEntryS.v:86-87) and seg_ok1 (AxEntryS.v:68-75) says
   nothing about seg_kernel_map, so there is no img_nk to match img_low.  segs is
   abstract at this point; it is closed at the unit's own ELF image, which is where
   AsanWLazy.v:100-105 says to discharge it by vm_compute. *)
Theorem asum_ck_ok (T : img_tabs) (segs : list Segment) (pc : N) (cfg : SpuriousCfg) (LIM : Z) :
  img_ok segs pc = true -> tabs_ok T = true -> cks_ok T segs = true ->
  forallb (fun s => negb (seg_kernel_map s)) segs = true ->
  forall fs0, sum_ok segs cfg LIM fs0 (asum_ck T segs LIM).
Proof.
  intros Himg HT Hck Hnk fs0 KT KT_emit k A l.
  exact (asum_ck_sound T HT segs Hck cfg LIM fs0 KT (img_low segs pc Himg) Hnk KT_emit k A l).
Qed.

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

Definition brk_lo (segs : list Segment) : Z := reserved_top (segments_reserved segs) / 4096.
Definition brk_hi (segs : list Segment) : Z := (reserved_top (segments_reserved segs) + brk_aslr_max) / 4096.

(** [r] is the launch's rseq flag.  It is free, so the start-up is proved for BOTH
    layouts and each has its own entry state and its own certificate. *)
Definition start_A0 (r : bool) (segs : list Segment) (pc : N) (ph : PhdrInfo) : AST :=
  entry_state r segs (Z.of_N pc) ph (entry_store (FL2 r (brk_lo segs) (brk_hi segs))).

Definition start_cert (r : bool) (segs : list Segment) (pc : N) (ph : PhdrInfo) (LIM : Z) (sum : Z -> AST -> option (list AST))
    (fin : AST -> bool) (H0 : htable) (fuel : positive) : bool :=
  srun_ok fin (srun segs LIM (sys_disp2 segs LIM) sum H0 fuel (start_A0 r segs pc ph)).

Section Start.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo).
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Hypothesis Himg : img_ok segs pc = true.
(* NEW: sys_disp2_sound is discharged out of AxDisp's Section Disp with Hnk right
   after Hlow (AxDisp.v:27-29,69-72), and Himg does not give it -- see the note on
   asum_ck_ok above.  Discharged at the unit's own ELF image, AsanWLazy.v:100-105. *)
Hypothesis Hnk : forallb (fun s => negb (seg_kernel_map s)) segs = true.
Variable sum : Z -> AST -> option (list AST).
Hypothesis Hsum : forall fs0, sum_ok segs cfg LIM fs0 sum.

Variable POST : list (list byte) -> Fs.Fs -> config -> Prop.
Variable fin : AST -> bool.
Hypothesis Hfin_out : forall B, fin B = true -> am_out (a_model B) = [].
Hypothesis Hbridge : forall (fs0 : Fs.Fs) (B : AST), fin B = true ->
  forall ρ c, R segs amodel (MR segs fs0 ρ) LIM ρ B c ->
  forall T : TSet, (forall c', POST (dec_argvB ρ) fs0 c' -> realizes_cfg segs cfg c' T) -> realizes_cfg segs cfg c T.

Variables (H0 : htable) (fuel : positive).
(** one certificate per auxv layout: with rseq (29 pairs) and without (27) *)
Hypothesis Hcert : start_cert true segs pc ph LIM sum fin H0 fuel = true.
Hypothesis Hcert_norseq : start_cert false segs pc ph LIM sum fin H0 fuel = true.

(* No whole-kernel pin: the start-up reads two kernel fields as named facts, the cache
   words of the auxv and AT_MINSIGSTKSZ.  The vDSO base is read off the launch for every
   build, and rseq is split on below, both branches proved. *)
Theorem startup_sound : forall (TT : list (list byte) -> TSet) (en : ExecEntry) (inp : ProcInput),
  valid_input inp -> launch_cache_words (in_kernel inp) = launch_cache_words default_kernel ->
  min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp) -> valid_entry (mkImage segs pc ph) en inp ->
  (forall argv c, valid_argv argv -> POST argv (in_fs inp) c -> realizes_cfg segs cfg c (TT argv)) ->
  realizes_cfg segs cfg
    (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) LIM inp)
    (TT (in_argv inp)).
Proof.
  intros TT en inp Hinp Hcw Hmss Hent Hmain.
  (* NINE underscores before H WAS the pattern, picking valid_input's 10th conjunct.
     #38 grew valid_input from 11 conjuncts to 17 and the two new ones are INSERTED,
     not appended: `fs_image_real` at 5 and `valid_launch` at 13 (LPS@75d69e00
     Run.v, Definition valid_input).  The one at 5 is before our slot, so
     `in_va_size inp = Sv48` moved from 10th to 11th and the old pattern bound
     `in_abort_terminal inp = false` instead -- "exact H" rejected at :119 chars
     111-112.  One underscore added, nothing else:
     a tail append would have needed no change at all, which is exactly why this
     class is silent everywhere the mis-bound types happen to agree. *)
  assert (Hva : in_va_size inp = Sv48) by (destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  apply (proj1 (valid_entry_sv48 _ _ _ Hva)) in Hent. destruct en as [sp brk0 mbase draw]. destruct Hent as (Hsp & Hbrk & Hmb & _ & Hl).
  cbn [en_sp en_brk en_mmap_base en_draw] in *.
  pose proof (img_low segs pc Himg) as Hlow.
  set (fs0 := in_fs inp). set (KT := KTs TT).
  set (pcw := Z_to_bv 64 (Z.of_N pc)).
  assert (Hs0 : sat (enc_b inp sp mbase pcw draw brk0)
                    (entry_store (FL2 (kb_rseq (in_kernel inp)) (brk_lo segs) (brk_hi segs)))).
  { apply sat_entry_store. exact (FL2_sat segs inp sp brk0 mbase pcw draw _ _ Hinp Hcw Hmss Hsp Hl Hbrk (Z.le_refl _) (Z.le_refl _)). }
  pose proof (entry_R segs pc ph sp brk0 mbase draw LIM inp _ Hinp Hcw Hmss Hsp Hmb Hl Hbrk Himg Hs0
                (good_inp_enc inp sp mbase pcw brk0 draw Hinp)) as HR.
  (* rseq is free: take the certificate of the layout this launch has *)
  set (r := kb_rseq (in_kernel inp)) in *.
  assert (Hcert_r : start_cert r segs pc ph LIM sum fin H0 fuel = true)
    by (unfold r; destruct (kb_rseq (in_kernel inp)); [exact Hcert | exact Hcert_norseq]).
  destruct (srun_ok_parts _ _ Hcert_r) as [E1 [E2 [E3 E4]]].
  assert (HS : Sound segs cfg LIM (MR segs fs0) KT (start_A0 r segs pc ph)).
  { apply (run_sound segs cfg LIM H0 (MR segs fs0) (MR_mat segs fs0) Hlow KT (sys_disp2 segs LIM) sum) with (ic := IEmpty) (p := fuel).
    - exact (sys_disp2_sound segs cfg Hcfg2 LIM fs0 KT (KTs_agree TT) Hlow Hnk).
    - intros A B J HJ HSn. exact (join_sound segs cfg LIM (MR segs fs0) (MR_next segs fs0) KT A B J HJ HSn).
    - intros A f cuts Hsp' HSn. exact (split_sound segs cfg LIM (MR segs fs0) KT A f cuts Hsp' HSn).
    - intros A v h k Hok' HSn. exact (fresh_sound segs cfg LIM (MR segs fs0) (MR_agree segs fs0) KT (KTs_agree TT) A v h k Hok' HSn).
    (* `intros A B r k` and `intros A r f cuts` WERE here, and `intros A r k l` at the
       align bullet.  `r` is this proof's rseq flag, bound by the start_A0 at :144, so
       Coq refuses the shadowing: "r is already used" at :150 chars 17-18, identically
       in all three trees (measured on the farm,
       one round per tree).  These three are REGISTER binders; renaming them is the
       whole change, and each is used only inside its own bullet. *)
    - intros A B rg k Hfl HSn. exact (floor_sound segs cfg LIM (MR segs fs0) (MR_agree segs fs0) (MR_next segs fs0) KT (KTs_agree TT) A B rg k Hfl HSn).
    - intros A rg f cuts Hr Hxf Hsp' HSn. exact (split_reg_sound segs cfg LIM (MR segs fs0) KT A rg f cuts Hr Hxf Hsp' HSn).
    - intros k A l Hs HSn. exact (Hsum fs0 KT (KTs_emit TT) k A l Hs HSn).
    - intros A B J Em Emod HJ HSn. exact (join_nm_sound segs cfg LIM (MR segs fs0) (MR_next segs fs0) KT A B J Em Emod HJ HSn).
    - intros A rg k l Hal HSn. exact (align_sound segs cfg LIM (MR segs fs0) KT A rg k l Hal HSn).
    - intros k e _ He. rewrite iget_empty in He. discriminate.
    - exact E1.
    - exact E2.
    - exact E3.
    - intros B HB ρ c HRB o Ho. pose proof (E4 B HB) as HfB.
      unfold out_val in Ho. rewrite (Hfin_out B HfB) in Ho. cbn [pieces_val] in Ho. subst o.
      unfold KT, KTs. apply (Hbridge fs0 B HfB ρ c HRB). intros c' Hpost. apply Hmain; [|exact Hpost].
      pose proof (mr_fds segs fs0 ρ _ _ (r_model _ _ _ _ _ _ _ HRB)) as [Hg _]. exact Hg. }
  pose proof (HS _ _ HR [] (entry_out (enc_b inp sp mbase pcw draw brk0) r segs (Z.of_N pc) ph (entry_store (FL2 r (brk_lo segs) (brk_hi segs))))) as Hz.
  (* Two separate reasons the rewrite missed, and the probe separated them.
     First, `unfold KT, KTs in Hz` leaves KTs's `match o with [] => TT (dec_argvB rho)`
     unreduced, so there was no dec_argvB at all; `cbn iota beta` takes it to its
     branch.  Second, cbn also ZETA-expands the `set` variable pcw, so the probe
     printed Hz as `... (enc_b inp sp mbase (Z_to_bv 64 (Z.of_N pc)) draw brk0)` while
     the rewrite named pcw -- the same number under two spellings, which is the shape
     that has cost this file several rounds.  Naming the expanded term is the whole
     cure; dec_argvB_enc is unchanged and its argument order (inp)(sp mbase pcw brk0)
     (draw) is the one AxFdEnc's good_inp_enc already uses.
     Measured on the farm, PROBE-HZ. *)
  unfold KT, KTs in Hz. cbn iota beta in Hz.
  rewrite (dec_argvB_enc inp sp mbase (Z_to_bv 64 (Z.of_N pc)) brk0 draw Hinp) in Hz. exact Hz.
Qed.

End Start.

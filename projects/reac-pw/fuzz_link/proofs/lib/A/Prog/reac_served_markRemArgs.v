(* reac_served_mark on image A: remember's Pre, write set and Post at the two call sites (+0x5c8 after a
   successful reac_link_alias_write, +0x574 after wrapper_bcmp), shared by both arms.
   The facts come from the cut (the Kit's srm_marks_blk_at / srm_name_at / srm_policy_at at window REMEMBER_AK);
   this file only assembles them into remember_c.v's shapes. The read set (the name and its NUL) is
   `remember_ard` unfolded; a caller relates its string to the cut's with the Kit's acstr_at_unique.

   Proves no function (kind: segment lemma of reac_served_mark's walk: remember's call-site facts). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.

Lemma srm_rem_pre : forall (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte) gbs s,
  amarks_at SEGS m (aarg regs 0) gbs -> marks_wf gbs -> amarks_ledger bl (aarg regs 0) ->
  amarks_blk_ok SEGS regs REMEMBER_AK m (aarg regs 0) ->
  aarg regs 1 <> 0 -> acstr_at SEGS m (aarg regs 1) s -> (length s <= 15)%nat ->
  astr_rt_ok SEGS regs REMEMBER_AK m (aarg regs 1) s ->
  apart (aarg regs 1) (Z.of_nat (length s) + 8) (aarg regs 0) MK_SIZE ->
  acstr_at SEGS m LA_FMT_S S_FMT_S -> astr_rt_ok SEGS regs REMEMBER_AK m LA_FMT_S S_FMT_S ->
  remember_apre SEGS bl regs m.
Proof.
  intros bl regs m gbs s H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  exists gbs, s. repeat (split; [assumption|]). exact H11.
Qed.

(* the write set is the marks block, a part of the contract's write set *)
Lemma srm_rem_wr : forall (cx : srmcx) (regs : bvmap 5 word) (m : word -> option byte) a,
  aarg regs 0 = srm_mk cx -> inFP (remember_awr regs m) a -> srm_E cx a.
Proof.
  intros cx regs m a H0 (r & Hin & Hr). unfold remember_awr in Hin. cbn [In] in Hin.
  destruct Hin as [<- | []]. unfold srm_E, inFP. exists (aivl (srm_mk cx) MK_SIZE). split.
  - unfold srm_wr, reac_served_mark_awr. cbn [In]. right. left. reflexivity.
  - rewrite <- H0. exact Hr.
Qed.

Lemma srm_rem_wr_blk : forall (regs : bvmap 5 word) (m : word -> option byte) a,
  aarg regs 0 <> 0 -> inFP (remember_awr regs m) a -> aarg regs 0 <= a < aarg regs 0 + MK_SIZE.
Proof.
  intros regs m a H0 (r & Hin & Hr). unfold remember_awr in Hin. cbn [In] in Hin.
  destruct Hin as [<- | []]. unfold aivl in Hr. cbn [fst snd] in Hr.
  destruct (Z.eqb_spec (aarg regs 0) 0) as [E|_]; [contradiction|]. exact Hr.
Qed.

(* the post at the return memory *)
Lemma srm_rem_post : forall (regs : bvmap 5 word) (m : word -> option byte) (regs' : bvmap 5 word)
    (m' : word -> option byte) gbs s,
  remember_apost SEGS regs m regs' m' -> amarks_at SEGS m (aarg regs 0) gbs -> acstr_at SEGS m (aarg regs 1) s ->
  exists gbs', amarks_at SEGS m' (aarg regs 0) gbs' /\ marks_wf gbs'
    /\ mk_names gbs' = remember (mk_names gbs) s /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) s)).
Proof. intros regs m regs' m' gbs s H HM HS. exact (H gbs s HM HS). Qed.

End b.
End a.

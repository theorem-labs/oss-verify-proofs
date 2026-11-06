(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the contract's result as a cut states it
   (reac_served_markDefs.v `srm_pf`), from what each arm knows after its last callee. Every arm of the body that ran
   the read (the read failed; the four verdicts) ends with the kernel as
   the alias callees left it (`srm_kern ... 2`), the marks block, and the FILE with k' pending bytes; `srm_pf_of`
   turns that into `reac_served_mark_apost` for every return register a0 = m_rc M, where M is link_spec's
   `mark_lib` at the entry's objects (the witnesses `srm_ent` names). The entry's objects are the only ones the Post
   quantifies over: the Kit's uniqueness lemmas say any other reading of the same bytes is the same.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markUniq
LinkWalkMkFile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the marks block's count is the length of its name list *)
Lemma srm_mk_n_names : forall gbs, marks_wf gbs -> mk_n gbs = Z.of_nat (length (mk_names gbs)).
Proof. intros gbs (H & _). unfold mk_names. rewrite length_map, length_seq. lia. Qed.

(* the code a reader or a writer answers on a well-formed kernel is an int32, so `beqz a0` on the 64-bit register
   decides `rc = 0` (the plain slot's LC2ReadL.v c2r_talk_rc_range, image-free link_spec facts) *)
Lemma srm_rd32s_range : forall c off, -2^31 <= rd32s c off < 2^31.
Proof.
  intros c off. unfold rd32s, rd32, link_spec.rdn. cbv zeta.
  assert (HL : (length (slice c off 4) <= 4)%nat).
  { unfold slice. rewrite length_firstn. change (Z.to_nat 4) with 4%nat. lia. }
  pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (H2 : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (H3 : bytes_le_to_Z (slice c off 4) < 2 ^ 32) by (eapply Z.lt_le_trans; [exact H1 | exact H2]).
  clear H1 H2 HL. set (v := bytes_le_to_Z (slice c off 4)) in *.
  destruct (v <? 2 ^ 31) eqn:E; cbv beta iota; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Definition srm_err_ok (v : nlv) : Prop :=
  match v with NlErr code => -2^31 <= code < 2^31 | _ => True end.

Lemma srm_msg_scan_ok : forall fuel c off left, srm_err_ok (msg_scan fuel c off left).
Proof.
  induction fuel as [|f IH]; intros c off left; [exact I|].
  cbn [msg_scan]. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try exact I; try apply IH; cbn [srm_err_ok]; apply srm_rd32s_range.
Qed.

Lemma srm_chunk_loop_ok : forall fuel cs i, srm_err_ok (fst (chunk_loop fuel cs i)).
Proof.
  induction fuel as [|f IH]; intros cs i; [exact I|].
  cbn [chunk_loop]. destruct (nth_error cs i) as [c|]; [|exact I].
  unfold chunk_walk.
  pose proof (srm_msg_scan_ok (S (length c)) c 0 (Z.of_nat (length c))) as H.
  destruct (msg_scan (S (length c)) c 0 (Z.of_nat (length c))); cbn [fst]; first [exact I | exact H | apply IH].
Qed.

Lemma srm_talk_rc_range : forall K, 0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  -2^31 <= talk_rc_lib K < 2^31.
Proof.
  intros K H1 H2 H3. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  pose proof (srm_chunk_loop_ok (S (length (k_chunks K))) (k_chunks K) (k_next K)) as HC.
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  cbn [fst] in HC.
  assert (EIO : E_IO = 5) by reflexivity.
  destruct v; cbn [fst]; [lia | lia | cbn [srm_err_ok] in HC; lia | lia].
Qed.

(* the kstate a well-formed kernel holds has the three errno words in range *)
Lemma srm_kstate_bounds : forall kbs, nlk_wf kbs ->
  0 <= k_sock (nk_kstate kbs) < 2^31 /\ 0 <= k_send (nk_kstate kbs) < 2^31 /\ 0 <= k_end (nk_kstate kbs) < 2^31.
Proof.
  intros kbs (_ & _ & _ & _ & _ & _ & _ & _ & He & Hs & Hd & _).
  unfold nk_kstate; cbn [k_sock k_send k_end]. lia.
Qed.

Lemma srm_read_rc_range : forall tab nm kc ac reqs kbs, nlk_wf kbs ->
  -2^31 <= r_rc (read_core tab nm kc ac reqs (nk_kstate kbs)) < 2^31.
Proof.
  intros tab nm kc ac reqs kbs HW. destruct (srm_kstate_bounds kbs HW) as (H1 & H2 & H3).
  assert (EI : E_INVAL = 22) by reflexivity. assert (ED : E_NODEV = 19) by reflexivity.
  unfold read_core. destruct nm as [s|]; [|cbn [r_rc]; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; lia|].
  cbn [r_rc]. apply srm_talk_rc_range; assumption.
Qed.

(* the writer runs on the kstate the reader left; its errno words are the reader's input's *)
Lemma srm_write_rc_range : forall tab nm al reqs K,
  0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  -2^31 <= w_rc (write_core tab nm al reqs K) < 2^31.
Proof.
  intros tab nm al reqs K H1 H2 H3.
  assert (EI : E_INVAL = 22) by reflexivity. assert (ED : E_NODEV = 19) by reflexivity.
  assert (EN : E_NAMETOOLONG = 36) by reflexivity.
  unfold write_core. destruct nm as [s|]; [|cbn [w_rc]; lia]. destruct al as [a|]; [|cbn [w_rc]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [w_rc]; lia|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [cbn [w_rc]; lia|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [w_rc]; lia|].
  cbn [w_rc]. apply srm_talk_rc_range; assumption.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

Lemma srm_kern_mono : forall m kbs kbs' tab St reqs n n',
  n <= n' -> srm_kern m kbs kbs' tab St reqs n -> srm_kern m kbs kbs' tab St reqs n'.
Proof.
  intros m kbs kbs' tab St reqs n n' Hn
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  (* explicit terms only: unifying two different field reads (eassumption) unfolds them to slices of g_nl *)
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj H14 _)))))))))))))). lia.
Qed.

(* THE POST OF A CUT: the kernel as the alias callees left it against M, the marks block with M's names, and the
   FILE with k' pending bytes, k0 <= k' <= k0 + MARK_LINE_MAX, give reac_served_mark_apost for every a0 = m_rc M. *)
Lemma srm_pf_of : forall (cx : srmcx) s kbs tab gbs k0 kbs' gbs' k' (m' : word -> option byte) (M : mres),
  srm_ent cx s kbs tab gbs k0 ->
  M = mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) ->
  srm_kern m' kbs kbs' tab (m_state M) (m_reqs M) 2 ->
  amarks_at SEGS m' (srm_mk cx) gbs' -> marks_wf gbs' -> mk_names gbs' = m_marks M ->
  amemfile_k SEGS m' (sm_sink cx) k' -> k0 <= k' <= k0 + MARK_LINE_MAX ->
  srm_pf cx (m_rc M) m'.
Proof.
  intros cx s kbs tab gbs k0 kbs' gbs' k' m' M HENT HM HK HMK HWF HNM HMF HKB.
  destruct HENT as (Hmk & Hnm & Hs & (HNLK & HNWF & _ & _ & _ & HTAB & _) & HGBS & _ & HMF0 & _).
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  unfold srm_pf, reac_served_mark_apost. intros regs' Hr10.
  split; [|split].
  - intros k Hk. pose proof (amemfile_k_unique SEGS _ _ _ _ Hk HMF0) as Ek. subst k.
    exists k'. split; [exact HKB | exact HMF].
  - intros H0. exfalso. exact (Hmk H0).
  - intros _ kbs0 tab0 nm gbs0 HN0 HT0 HA0 HG0.
    pose proof (anlk_at_unique SEGS _ _ _ _ HN0 HNLK) as Ek. subst kbs0.
    pose proof (aiftab_at_unique SEGS _ _ _ _ HT0 HTAB) as Et. subst tab0.
    pose proof (astr_arg_unique SEGS _ _ _ _ HA0 Hnm) as En. subst nm.
    pose proof (amarks_at_unique SEGS _ _ _ _ HG0 HGBS) as Eg. subst gbs0.
    cbv zeta. rewrite <- HM.
    split; [exact Hr10|]. split.
    + exists gbs'. split; [exact HMK|]. split; [exact HWF|]. split; [exact HNM|].
      rewrite (srm_mk_n_names gbs' HWF), HNM. reflexivity.
    + exists kbs'.
      refine (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K10 (conj K11 (conj K12
        (conj K13 (conj K14 _)))))))))))). lia.
Qed.

End b.
End a.

About srm_pf_of.
Print Assumptions srm_pf_of.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec CatSim PropExec ShapeAlg Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib LibWbxd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Lazyiq4.

Module DA_Erys.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RelSpec CatSim PropExec ShapeAlg Nodes LibWbxd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Lazyiq4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma srz_wall : forall c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  srealizes segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  srealizes segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros c ch bs K Hnb HK H. eapply srz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma copy_iovecs_accesses_2 : forall mp iov,
  exists l, copy_iovecs_accesses mp iov 2 = (iov, 16%nat) :: l /\
            (l = [] \/ l = [(iov + 16, 16%nat)] \/ exists l', l = (iov + 16, 16%nat) :: l' /\ (l' = [])).
Proof.
  intros mp iov. cbn [copy_iovecs_accesses].
  destruct (read_iovec_entry mp iov) as [b len| |].
  - destruct (read_iovec_entry mp (iov + 16)) as [b' len'| |]; (eexists; split; [reflexivity|]); right; left; reflexivity.
  - exists []. split; [reflexivity| left; reflexivity].
  - exists []. split; [reflexivity| left; reflexivity].
Qed.

Lemma accs_in_hull_copy_iovecs_2 : forall A mp iov,
  bytes_in_hull A iov 32 -> accs_in_hull A (copy_iovecs_accesses mp iov 2).
Proof.
  intros A mp iov H.
  assert (H1 : bytes_in_hull A iov 16) by (eapply bytes_in_hull_shrink; [|exact H]; lia).
  assert (H2 : bytes_in_hull A (iov + 16) 16).
  { intros k Hk. unfold bytes_in_hull in H. specialize (H (16 + k)%nat ltac:(lia)).
    replace (woff (iov + 16) k) with (woff iov (16 + k)); [exact H|].
    unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (16:word)) with 16%Z.
    unfold bv_wrap. rewrite Nat2Z.inj_add. change (Z.of_nat 16) with 16%Z.
    rewrite Zplus_mod_idemp_l. f_equal. lia. }
  destruct (copy_iovecs_accesses_2 mp iov) as (l & -> & Hl).
  intros a n Hin. destruct Hin as [E|Hin]; [injection E as <- <-; exact H1|].
  destruct Hl as [-> | [-> | (l' & -> & ->)]]; cbn in Hin; [contradiction| |].
  - destruct Hin as [E|[]]. injection E as <- <-. exact H2.
  - destruct Hin as [E|[]]. injection E as <- <-. exact H2.
Qed.

Lemma accs_in_hull_prefix_2 : forall A b1 n1 b2 k,
  bytes_in_hull A b1 (word_to_nat n1) ->
  accs_in_hull A (iov_prefix_accesses [(b1, n1); (b2, Z_to_bv 64 0)] k).
Proof.
  intros A b1 n1 b2 k H a n Hin. cbn [iov_prefix_accesses] in Hin.
  destruct k as [|k']; [cbn in Hin; contradiction|]. rewrite !word_to_nat_bounded_eq_min in Hin.
  destruct (Nat.eqb (Nat.min (word_to_nat n1) (S k')) 0) eqn:E.
  - replace (word_to_nat (Z_to_bv 64 0)) with 0%nat in Hin by reflexivity. cbn in Hin. contradiction.
  - destruct Hin as [E2|Hin].
    + injection E2 as <- <-. eapply bytes_in_hull_shrink; [|exact H]. lia.
    + replace (word_to_nat (Z_to_bv 64 0)) with 0%nat in Hin by reflexivity. cbn [Nat.min] in Hin.
      destruct (S k' - Nat.min (word_to_nat n1) (S k'))%nat; cbn in Hin; contradiction.
Qed.

(* [comment removed for export] *)
Lemma srz_writev2_hull : forall A AL E ms model x8 (fd : Z) (iov b1 n1 b2 : word) bs1 (K : TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd -> ms_gpr ms 1 = iov -> ms_gpr ms 2 = Z_to_bv 64 2 ->
  iov_array segs (ms_mem ms) iov [(b1, n1); (b2, Z_to_bv 64 0)] ->
  rdn segs (ms_mem ms) b1 (word_to_nat n1) = Some bs1 ->
  (1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= rw_bytes_max)%Z -> (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z -> (bv_unsigned b2 <= TASK_SIZE)%Z ->
  MInv A AL E model -> bytes_in_hull A iov 32 -> bytes_in_hull A b1 (word_to_nat n1) ->
  K [] ->
  (forall k model', (1 <= k)%nat -> (k <= length bs1)%nat -> MInv A AL E model' -> same_but_materialized model model' ->
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model')
                     (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros A AL E ms model x8 fd iov b1 n1 b2 bs1 K Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Harr Hbs Ht1 Htmax Ht30 Hiovt Hok1 Hok2 HI Hiov Hbuf HK Hcont.
  pose proof (u64_range n1) as Rn1. pose proof (u64_range b2) as Rb2.
  assert (Hbufs : iov_bufs segs (ms_mem ms) [(b1, n1); (b2, Z_to_bv 64 0)] [bs1; []]).
  { cbn [iov_bufs]. split; [exact Hbs|]. split; [reflexivity| exact I]. }
  destruct (writev_outcome segs ms x8 model fd iov [(b1, n1); (b2, Z_to_bv 64 0)] [bs1; []] Hrom Hfd Hfdr Hno H0 H1 H2
              ltac:(cbn; lia) Harr Hbufs ltac:(cbn [iovs_total]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)
              ltac:(cbn [iovs_total]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)
              ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
              ltac:(cbn [iovs_access_okb forallb fst snd];
                    rewrite (access_okb_intro b1 n1 Hok1), (access_okb_intro b2 (Z_to_bv 64 0))
                      by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia); reflexivity)) as [Hlen Hchk].
  cbn [concat] in Hlen, Hchk. rewrite app_nil_r in Hlen, Hchk.
  set (CA := copy_iovecs_accesses (ms_read_byte ms) iov 2) in *.
  assert (Hnb : (1 <= length bs1)%nat) by (cbn [iovs_total] in Hlen; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hlen; lia).
  apply srz_wall; [exact Hnb | exact HK |].
  pose (effs := fun i : wr_index bs1 =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses [(b1, n1); (b2, Z_to_bv 64 0)] (proj1_sig i))).
  assert (Hacc : forall i, accs_in_hull A (syscall_effect_accesses (effs i))).
  { intros [k Hk]. unfold effs. cbn [proj1_sig]. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
    intros a n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - exact (accs_in_hull_copy_iovecs_2 A _ iov Hiov a n Hin).
    - exact (accs_in_hull_prefix_2 A b1 n1 b2 k Hbuf a n Hin). }
  destruct (node_family_hull segs A AL E ms model x8 (wr_index bs1) effs (fun _ => model)
              (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) _ Hh Hsvc Hchk) as [Hnode HI'].
  - intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
  - intros o (k & Hk' & ->). exists (exist _ k Hk'). reflexivity.
  - intros _; exact Hh.
  - intros _; exact HI.
  - exact Hacc.
  - eapply (srz_node segs (mkCfg ms model) (wr_index bs1) _ _ (fun i => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (proj1_sig i) bs1)) K)
              (wr_full bs1 Hnb) Hnode).
    intros [k [Hk1 Hk2]]. cbn [proj1_sig].
    specialize (HI' (exist _ k (conj Hk1 Hk2))). unfold effs in HI' |- *. cbn [proj1_sig] in HI' |- *.
    set (cis := CA ++ iov_prefix_accesses [(b1, n1); (b2, Z_to_bv 64 0)] k) in *.
    replace (apply_effect ms (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] cis)) with (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))
      by (rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) cis); reflexivity).
    apply (Hcont k _ Hk1 Hk2 HI'). apply model_after_same.
Qed.

End WithSegs.
End DA_Erys.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_W756.DA_Erys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma accs_in_hull_copy_iovecs : forall A mp cnt iov,
  bytes_in_hull A iov (16 * cnt) -> accs_in_hull A (copy_iovecs_accesses mp iov cnt).
Proof.
  intros A mp cnt. induction cnt as [|cnt IH]; intros iov H a n Hin; cbn [copy_iovecs_accesses] in Hin; [contradiction|].
  destruct Hin as [E|Hin].
  - injection E as <- <-. eapply bytes_in_hull_shrink; [|exact H]. lia.
  - assert (H16 : bytes_in_hull A (iov + 16) (16 * cnt)).
    { intros k Hk. specialize (H (16 + k)%nat ltac:(lia)).
      replace (woff (iov + 16) k) with (woff iov (16 + k)); [exact H|].
      unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (16:word)) with 16%Z.
      unfold bv_wrap. rewrite Nat2Z.inj_add. change (Z.of_nat 16) with 16%Z.
      rewrite Zplus_mod_idemp_l. f_equal. lia. }
    destruct (read_iovec_entry mp iov) as [b len| |]; [|destruct Hin|destruct Hin].
    exact (IH _ H16 a n Hin).
Qed.

(* [comment removed for export] *)
Lemma accs_in_hull_iov_prefix : forall A iovs k,
  (forall b n, In (b, n) iovs -> bytes_in_hull A b (word_to_nat n)) ->
  accs_in_hull A (iov_prefix_accesses iovs k).
Proof.
  intros A iovs. induction iovs as [|[b n] iovs IH]; intros k H a l Hin.
  - destruct k; cbn in Hin; contradiction.
  - cbn [iov_prefix_accesses] in Hin. destruct k as [|k'].
    + contradiction.
    + rewrite !word_to_nat_bounded_eq_min in Hin. destruct (Nat.eqb (Nat.min (word_to_nat n) (S k')) 0) eqn:E.
      * apply (IH (S k')); [| exact Hin]. intros b' n' Hin'. apply H. right. exact Hin'.
      * destruct Hin as [E2|Hin].
        -- injection E2 as <- <-. eapply bytes_in_hull_shrink; [| apply H; left; reflexivity]. lia.
        -- apply (IH (S k' - Nat.min (word_to_nat n) (S k'))%nat); [| exact Hin]. intros b' n' Hin'. apply H. right. exact Hin'.
Qed.

(* [comment removed for export] *)
Lemma srz_writev_hull : forall A AL E ms model x8 (fd : Z) (iov : word) iovs bss (K : TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd -> ms_gpr ms 1 = iov -> ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  iov_array segs (ms_mem ms) iov iovs -> iov_bufs segs (ms_mem ms) iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 26)%Z ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z -> iovs_access_okb iovs = true ->
  MInv A AL E model -> bytes_in_hull A iov (16 * length iovs) ->
  (forall b n, In (b, n) iovs -> bytes_in_hull A b (word_to_nat n)) ->
  K [] ->
  (forall k model', (1 <= k)%nat -> (k <= length (concat bss))%nat -> MInv A AL E model' -> same_but_materialized model model' ->
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model')
                     (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat bss))) K)) ->
  srealizes segs (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss)) K).
Proof.
  intros A AL E ms model x8 fd iov iovs bss K Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Ht1 Ht26 Hiovt Hokb HI Hiov Hbuf HK Hcont.
  destruct (writev_outcome segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Ht1
              ltac:(lia) Hiovt Hokb) as [Hlen Hchk].
  set (bs := concat bss) in *.
  set (CA := copy_iovecs_accesses (ms_read_byte ms) iov (length iovs)) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  apply srz_wall; [exact Hnb | exact HK |].
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Hacc : forall i, accs_in_hull A (syscall_effect_accesses (effs i))).
  { intros [k Hk]. unfold effs. cbn [proj1_sig]. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
    intros a n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - exact (accs_in_hull_copy_iovecs A _ (length iovs) iov Hiov a n Hin).
    - exact (accs_in_hull_iov_prefix A iovs k Hbuf a n Hin). }
  destruct (node_family_hull segs A AL E ms model x8 (wr_index bs) effs (fun _ => model)
              (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) _ Hh Hsvc Hchk) as [Hnode HI'].
  - intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
  - intros o (k & Hk' & ->). exists (exist _ k Hk'). reflexivity.
  - intros _; exact Hh.
  - intros _; exact HI.
  - exact Hacc.
  - eapply (srz_node segs (mkCfg ms model) (wr_index bs) _ _ (fun i => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (proj1_sig i) bs)) K)
              (wr_full bs Hnb) Hnode).
    intros [k [Hk1 Hk2]]. cbn [proj1_sig].
    specialize (HI' (exist _ k (conj Hk1 Hk2))). unfold effs in HI' |- *. cbn [proj1_sig] in HI' |- *.
    set (cis := CA ++ iov_prefix_accesses iovs k) in *.
    replace (apply_effect ms (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] cis)) with (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))
      by (rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) cis); reflexivity).
    apply (Hcont k _ Hk1 Hk2 HI'). apply model_after_same.
Qed.

(* [comment removed for export] *)
Lemma srz_writev1_zero_hull : forall A AL E ms model x8 (fd : Z) (iov b1 : word) (K : TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd -> ms_gpr ms 1 = iov -> ms_gpr ms 2 = Z_to_bv 64 1 ->
  rdn segs (ms_mem ms) iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 <= TASK_SIZE)%Z ->
  MInv A AL E model -> bytes_in_hull A iov 16 ->
  (forall model', MInv A AL E model' -> same_but_materialized model model' ->
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model') K) ->
  srealizes segs (mkCfg ms model) K.
Proof.
  intros A AL E ms model x8 fd iov b1 K Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Rb1 Rn1 Hiovt Hb1 HI Hiov Hc.
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  pose proof (copy_iovecs_of_array segs ms [(b1, Z_to_bv 64 0)] iov Hrom Harr) as Hcp. cbn [length] in Hcp.
  set (CA := copy_iovecs_accesses (ms_read_byte ms) iov 1).
  destruct (node_ret_only_copyins_hull segs A AL E ms model x8 CA (Z_to_bv 64 0) model [] Hh Hsvc) as [Hn HI']; [ | exact Hh | exact HI | | ].
  - intros o.
    rewrite (syscall_spec_66 (sys_input segs ms x8) model o) by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
    rewrite fd32_id by (rewrite u64_lit; lia).
    subst CA. change 1%nat with (word_to_nat (Z_to_bv 64 1)).
    change (ms_read_byte ms) with (in_mem (sys_input segs ms x8)).
    apply (writev_chan_zero_outcome _ _ _ _ model o (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] Hfd).
    + apply w_is0_pos. rewrite u64_lit; lia.
    + reflexivity.
    + reflexivity.
    + unfold IOV_MAX. rewrite u64_lit; lia.
    + rewrite u64_lit by lia. unfold access_okb. pose proof (u64_range iov).
      apply andb_true_iff; split; apply Z.leb_le; unfold TASK_SIZE in *; lia.
    + rewrite in_mem_si. exact Hcp.
    + cbn [iovs_access_okb forallb fst snd]. rewrite u64_lit by lia. unfold access_okb.
      pose proof (u64_range b1).
      rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.leb_le _ _)) by (unfold TASK_SIZE in *; lia). reflexivity.
    + reflexivity.
    + unfold rw_bytes_max. lia.
  - subst CA. exact (accs_in_hull_copy_iovecs A _ 1 iov Hiov).
  - eapply srz_silent1; [exact Hn|]. apply (Hc _ HI'). apply model_after_same.
Qed.
End WithSegs.

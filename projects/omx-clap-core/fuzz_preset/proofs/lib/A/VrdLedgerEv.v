(* fuzz_preset, slice S5b (the S3 walk, a Theorem Labs lane): THE ONE-EVENT CALLEE STEPS of parse_items' loop ledger, one lemma per
   EVENT SHAPE, the callee ABSTRACT (its post's ledger fields are the arguments; no callee is named). They are the
   second argument of the Ival walk's composition vl_ledger_move_app (lib/A/VrdLedgerStep.v, a working branch
   8eb46ea7114), which carries a granted prefix E -> P to E -> P2; the free of a block the position owns is not an
   append, so it is stated directly on the composed move (vle_free_D). a Theorem Labs lane's ruling 2026-10-29 (the S3 walk writes
   the per-shape steps once; IelemC / IelemD (grow), the Ival walk (parse_value), PI-key (parse_string, REFUSE-B's
   fuzz_free) and the number-tail lane cite them).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Pure ledger arithmetic over PRH_FnParse.v rd_ledger_move.
   STATE / VIEW: every conclusion is about the ledger fields (Lam, peak, cnt, fail, ran) a callee's post hands back
   at its post state (the post's prh_ledger), and, for the blocks clause, about the allocator states S (the call
   state) and S' (the post state); no memory view is read.
   THE SHAPES (the callee post's arm -> the lemma):
   - a new block of k bytes (EAlloc k; ok bit true; Lam' = (x, k) :: Lam, peak' = max peak (lsum Lam + k),
     cnt' = cnt + 1, fail and ran kept; cnt <> fail): vle_alloc;
   - the chosen failure (EFail k; bit false; cnt = fail; Lam, peak, ran kept, cnt + 1, fail' = SIZE_MAXZ): vle_fail_chosen;
   - the allocator's refusal (EFail k; bit false; cnt <> fail; Lam, fail kept, cnt + 1; #102's rule: ran' = 1 only when
     the request k is at most most, else ran' = ran; peak' = max peak (min SIZE_MAXZ (lsum Lam + h)), h the bytes the
     ALL-GRANTED call would hold, the head of prh_ev_helds gt): vle_fail_refused;
   - a block taken and given back (EAlloc k; EFree k; bit true; Lam kept, peak' = max peak (lsum Lam + k), cnt + 1;
     cnt <> fail): vle_alloc_free;
   - the free of a block the position owns (EFree k; no bit; Lam = (x, k) :: Lam' up to order): vle_free_D, on the
     composed move E -> P2.
   The no-event step is IproD's vrd_imove_nil (lib/A/VrdIPro.v, a working branch 8a43904f620), not restated here.
   With each shape, the vrd_imodel ledger clauses that composition needs: the lszR-append fact of the shape's trace
   (vl_ledger_move_app's last premise), the held / prh_held / lsum of the trace, and the blocks bound carried from the
   callee's `blocks_bytes S' <= blocks_bytes S + prh_held t` (vle_blocks_step).
   SET: a working branch on ival 8eb46ea7114 (VrdLedgerStep.v) and ielem 58c529f9fd7; texts S5b 49745a1a153
   on walkkit-next preset-tree-at-2026-10-29T08-45-51Z.tsv (sha256 5158fa4d0b4f; internal record). A-only: B sites not measured. No numeral is an address.
   A'LEDGER (a Theorem Labs lane, 2026-10-29), against the kit text PRH_FnParse.v blob 94232293d483 / PRH_Base.v blob
   ee2f5cd7ed35 (a working branch 3ac20a5c9e30): every shape takes rd_ledger_move's g_most (most) and the
   call's ALL-GRANTED trace gt. The old refusal shape (ran' = 1, peak kept) is REFUTED by #102's rule (a Theorem Labs lane's
   counterexample, the string ab with ok [false]: the instance gives g_peak 3 and g_ran_out 0); vle_fail_refused now
   states the text's refusal ledger, which is parse_string's and grow's refused-arm ledger in PRH_FnReader.v blob
   fb7b12dfa169. Each shape whose move keeps a granted max now asks 0 <= peak: rd_ledger_move's peak is a Z.max with
   prh_refused_peak, which is >= 0 (every prh_ledger gives 0 <= lsum Lam <= peak, PRH_Base.prh_ledger_bounds).
   vle_sat_ab: the refusal shape at the counterexample's instance values (check 1 of VERIFY 21:4xZ). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_Charge PRH_FnParse VrdLedgerStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section E.
Context {cp : CfParams}.

(* ---- trace arithmetic ---- *)
Lemma vle_held_app : forall a b, PjGrammar.held (a ++ b) = PjGrammar.held a + PjGrammar.held b.
Proof. induction a as [|e a IH]; intros b; cbn [app PjGrammar.held]; [lia | rewrite IH; lia]. Qed.

Lemma vle_calls_app : forall a b, PjGrammar.calls (a ++ b) = (PjGrammar.calls a + PjGrammar.calls b)%nat.
Proof. induction a as [|e a IH]; intros b; cbn [app PjGrammar.calls]; [reflexivity | rewrite IH; destruct (PjGrammar.is_call e); lia]. Qed.

Lemma vle_prh_held_app : forall a b, prh_held (a ++ b) = prh_held a + prh_held b.
Proof. intros a b. unfold prh_held. rewrite vle_held_app, vle_calls_app. lia. Qed.

Lemma vle_hpeak_nonneg : forall t, 0 <= hpeakR t.
Proof. destruct t; cbn [hpeakR]; lia. Qed.

Lemma vle_held_le_hpeak : forall t, PjGrammar.held t <= hpeakR t.
Proof. induction t as [|e t IH]; cbn [hpeakR PjGrammar.held]; lia. Qed.

Lemma vle_hpeak_app : forall a b, hpeakR (a ++ b) = Z.max (hpeakR a) (PjGrammar.held a + hpeakR b).
Proof.
  induction a as [|e a IH]; intros b; cbn [app hpeakR PjGrammar.held].
  - pose proof (vle_hpeak_nonneg b). lia.
  - rewrite IH. lia.
Qed.

(* the blocks bound, from the callee's (state S, the call state; S', the post state) *)
Lemma vle_blocks_step : forall (S0 S S' : astate) tr t,
  blocks_bytes S <= blocks_bytes S0 + prh_held tr -> blocks_bytes S' <= blocks_bytes S + prh_held t ->
  blocks_bytes S' <= blocks_bytes S0 + prh_held (tr ++ t).
Proof. intros S0 S S' tr t H1 H2. rewrite vle_prh_held_app. lia. Qed.

(* ---- the shapes' traces: lszR append, held, lsum ---- *)
Lemma vle_lsz_alloc : forall tr k, Permutation (lszR (tr ++ [EAlloc k])) (lszR tr ++ lszR [EAlloc k]).
Proof.
  intros tr k. unfold lszR. rewrite fold_left_app. cbn [fold_left lsz_evR].
  apply Permutation_cons_append.
Qed.

Lemma vle_lsz_fail : forall tr k, Permutation (lszR (tr ++ [EFail k])) (lszR tr ++ lszR [EFail k]).
Proof. intros tr k. unfold lszR. rewrite fold_left_app. cbn [fold_left lsz_evR]. rewrite app_nil_r. reflexivity. Qed.

Lemma vle_lsz_alloc_free : forall tr k,
  Permutation (lszR (tr ++ [EAlloc k; EFree k])) (lszR tr ++ lszR [EAlloc k; EFree k]).
Proof.
  intros tr k. unfold lszR. rewrite fold_left_app. cbn [fold_left lsz_evR rm1nR]. rewrite Nat.eqb_refl.
  rewrite app_nil_r. reflexivity.
Qed.

(* ---- THE SHAPES: the callee's one-event move from the position's ledger (Lam, peak, cnt, fail, ran) to the
   post's ledger, as rd_ledger_move over the callee's ok bits and trace ---- *)

(* a new block x of k bytes *)
Lemma vle_alloc : forall Lam peak cnt fail ran most gt x k,
  0 <= cnt -> cnt + 1 < 2 ^ 64 -> cnt <> fail -> 0 <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [true] gt [EAlloc k] [(x, Z.of_nat k)]
    ((x, Z.of_nat k) :: Lam) (Z.max peak (Ledger.lsum Lam + Z.of_nat k)) (cnt + 1) fail ran.
Proof.
  intros Lam peak cnt fail ran most gt x k H0 H1 Hne Hp0. unfold rd_ledger_move.
  cbn [PjGrammar.calls PjGrammar.is_call lszR fold_left lsz_evR hpeakR nliveR nlive_evR length map Z.of_nat
       PjGrammar.held_ev].
  split; [split; [intros i Hi Hc; assert (i = 0%nat) by lia; subst i; cbn in Hc; lia
                 | split; [left; reflexivity | intros i Hi Hn; assert (i = 0%nat) by lia; subst i;
                                               unfold prh_refused in Hn; cbn in Hn; discriminate Hn]]|].
  split; [rewrite Z.mod_small by lia; reflexivity|].
  split; [unfold fail_afterR; split; intros Hf; [lia | reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb Z.of_nat]. lia.
Qed.

(* the chosen failure: the counter reaches fail *)
Lemma vle_fail_chosen : forall Lam peak cnt fail ran most gt k,
  0 <= cnt -> cnt + 1 < 2 ^ 64 -> cnt = fail -> Ledger.lsum Lam <= peak -> 0 <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [false] gt [EFail k] [] Lam peak (cnt + 1) SIZE_MAXZ ran.
Proof.
  intros Lam peak cnt fail ran most gt k H0 H1 Heq Hpk Hp0. unfold rd_ledger_move.
  cbn [PjGrammar.calls PjGrammar.is_call lszR fold_left lsz_evR hpeakR nliveR nlive_evR length map Z.of_nat
       PjGrammar.held_ev app].
  split; [split; [intros i Hi Hc; assert (i = 0%nat) by lia; subst i; reflexivity
                 | split; [left; reflexivity | intros i Hi Hn; assert (i = 0%nat) by lia; subst i;
                                               unfold prh_refused in Hn; cbn in Hn;
                                               rewrite (proj2 (Z.eqb_eq _ _)) in Hn by lia; cbn in Hn;
                                               discriminate Hn]]|].
  split; [rewrite Z.mod_small by lia; reflexivity|].
  split; [unfold fail_afterR; split; intros Hf; [reflexivity | lia]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb Z.of_nat].
  rewrite Z.add_0_r, (proj2 (Z.eqb_eq _ _)) by lia. cbn [negb andb]. lia.
Qed.

(* the allocator's refusal (#102's rule, PRH_Base.v prh_oks / prh_refused_peak): the counter is not at fail; ran is
   set only when the request k is at most most; the peak takes the live bytes plus h, the bytes the ALL-GRANTED call
   would hold (the head of prh_ev_helds gt: k for a malloc, n - m for a grow from m to n) *)
Lemma vle_fail_refused : forall Lam peak cnt fail ran most gt k h,
  0 <= cnt -> cnt + 1 < 2 ^ 64 -> cnt <> fail -> Ledger.lsum Lam <= peak -> 0 <= peak ->
  hd_error (prh_ev_helds gt) = Some h ->
  rd_ledger_move Lam peak cnt fail ran most [false] gt [EFail k] [] Lam
    (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + h))) (cnt + 1) fail (if Z.of_nat k <=? most then 1 else ran).
Proof.
  intros Lam peak cnt fail ran most gt k h H0 H1 Hne Hpk Hp0 Hh. unfold rd_ledger_move.
  assert (Hr : prh_refused [false] cnt fail 0 = true)
    by (unfold prh_refused; cbn [nth negb andb Z.of_nat]; rewrite Z.add_0_r, (proj2 (Z.eqb_neq _ _) Hne);
        reflexivity).
  change (prh_ev_reqs [EFail k]) with [Z.of_nat k].
  cbn [PjGrammar.calls PjGrammar.is_call lszR fold_left lsz_evR hpeakR nliveR nlive_evR length map Z.of_nat
       PjGrammar.held_ev app].
  split.
  { split; [intros i Hi Hc; assert (i = 0%nat) by lia; subst i; reflexivity|].
    split.
    - destruct (Z.leb_spec (Z.of_nat k) most) as [Hk|Hk]; [right | left; reflexivity].
      split; [reflexivity|]. exists 0%nat. split; [lia|]. split; [exact Hr | cbn [nth]; exact Hk].
    - intros i Hi _ Hk. assert (i = 0%nat) by lia. subst i. cbn [nth] in Hk.
      rewrite (proj2 (Z.leb_le _ _) Hk). reflexivity. }
  split; [rewrite Z.mod_small by lia; reflexivity|].
  split; [unfold fail_afterR; split; intros Hf; [lia | reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  unfold prh_refused_peak. cbn [List.seq map fold_right]. rewrite Hr.
  revert Hh. destruct (prh_ev_helds gt) as [|h' hs]; intros Hh; cbn in Hh; [discriminate Hh|]. injection Hh as <-.
  cbn [map nth]. lia.
Qed.

(* a block taken and given back within the call *)
Lemma vle_alloc_free : forall Lam peak cnt fail ran most gt k,
  0 <= cnt -> cnt + 1 < 2 ^ 64 -> cnt <> fail -> 0 <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [true] gt [EAlloc k; EFree k] []
    Lam (Z.max peak (Ledger.lsum Lam + Z.of_nat k)) (cnt + 1) fail ran.
Proof.
  intros Lam peak cnt fail ran most gt k H0 H1 Hne Hp0. unfold rd_ledger_move.
  cbn [PjGrammar.calls PjGrammar.is_call lszR fold_left lsz_evR rm1nR hpeakR nliveR nlive_evR length map Z.of_nat
       PjGrammar.held_ev app]. rewrite Nat.eqb_refl.
  split; [split; [intros i Hi Hc; assert (i = 0%nat) by lia; subst i; cbn in Hc; lia
                 | split; [left; reflexivity | intros i Hi Hn; assert (i = 0%nat) by lia; subst i;
                                               unfold prh_refused in Hn; cbn in Hn; discriminate Hn]]|].
  split; [rewrite Z.mod_small by lia; reflexivity|].
  split; [unfold fail_afterR; split; intros Hf; [lia | reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb Z.of_nat]. lia.
Qed.

(* CHECK 1 OF VERIFY 21:4xZ (the changed shapes are satisfiable, at the unit's own reader run): a Theorem Labs lane's
   counterexample. parse_value at d = 0 on the JSON string ab (bytes 34 97 98 34) with ok = [false]: the reader's
   own trace is [EFail 3] and its all-granted trace prhPv_gtrace holds 3 bytes; at the start ledger Lam = [],
   peak = 0, cnt = 0, ran = 0, with fail = 1 (cnt <> fail: the refusal is the allocator's) and most = 2, the move
   states g_peak 3 and g_ran_out 0, the instance's values (the REFUTED form said 0 and 1) *)
Lemma vle_sat_ab :
  snd (fst (PjGrammar.jr_value prh_jr_strtod 0 [34; 97; 98; 34] [false])) = [EFail 3] /\
  rd_ledger_move [] 0 0 1 0 2 [false] (prhPv_gtrace 0 [34; 97; 98; 34])
    (snd (fst (PjGrammar.jr_value prh_jr_strtod 0 [34; 97; 98; 34] [false]))) [] [] 3 1 1 0.
Proof.
  assert (Ht : snd (fst (PjGrammar.jr_value prh_jr_strtod 0 [34; 97; 98; 34] [false])) = [EFail 3])
    by (vm_compute; reflexivity).
  assert (Hg : hd_error (prh_ev_helds (prhPv_gtrace 0 [34; 97; 98; 34])) = Some 3) by (vm_compute; reflexivity).
  split; [exact Ht|]. rewrite Ht.
  exact (vle_fail_refused [] 0 0 1 0 2 (prhPv_gtrace 0 [34; 97; 98; 34]) 3 3
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) Hg).
Qed.

(* and the composition (VrdLedgerStep.vl_ledger_move_app) on the same refusal after a granted block: a 3-byte block
   granted, then a 3-byte malloc refused at most = 2: g_peak = 3 + 3 (the refusal's live + n), g_ran_out stays 0 *)
Lemma vle_sat_app : forall x,
  rd_ledger_move [] 0 0 5 0 2 ([true] ++ [false]) ([EAlloc 3] ++ [EAlloc 3]) ([EAlloc 3] ++ [EFail 3])
    ([(x, 3)] ++ []) [(x, 3)] 6 2 5 0.
Proof.
  intros x.
  pose proof (vle_alloc [] 0 0 5 0 2 [EAlloc 3] x 3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H1.
  pose proof (vle_fail_refused [(x, 3)] 3 1 5 0 2 [EAlloc 3] 3 3 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(cbn; lia) ltac:(lia) eq_refl) as H2.
  cbn [Ledger.lsum Z.of_nat] in H1, H2.
  exact (vl_ledger_move_app [] 0 0 5 0 2 [EAlloc 3] [EAlloc 3] [(x, 3)] [(x, 3)] 3 1 5 0 [false] [EAlloc 3]
           [EFail 3] [] [(x, 3)] 6 2 5 0 ltac:(lia) ltac:(cbn; lia) H1 H2 ltac:(reflexivity)
           ltac:(cbn; apply Permutation_refl)).
Qed.

(* the held bytes of each shape *)
Lemma vle_held_shapes : forall k,
  PjGrammar.held [EAlloc k] = Z.of_nat k /\ PjGrammar.held [EFail k] = 0 /\
  PjGrammar.held [EAlloc k; EFree k] = 0 /\ PjGrammar.held [EFree k] = - Z.of_nat k.
Proof. intros k. cbn [PjGrammar.held PjGrammar.held_ev]. lia. Qed.

(* ---- the free of a block the position owns, on the composed move E -> P2 ---- *)
Lemma vle_rm1n_perm : forall (s : list nat) k, In k s -> Permutation s (k :: rm1nR k s).
Proof.
  induction s as [|y s IH]; intros k Hin; [destruct Hin|].
  cbn [rm1nR]. destruct (Nat.eqb_spec y k) as [-> | Hne]; [reflexivity|].
  destruct Hin as [-> | Hin]; [exfalso; exact (Hne eq_refl)|].
  eapply perm_trans; [apply perm_skip; exact (IH k Hin)|]. apply perm_swap.
Qed.

Lemma vle_free_D : forall L0 pk0 c0 f0 r0 m0 ok gt tr D Lam peak cnt fail ran Lam' x k,
  rd_ledger_move L0 pk0 c0 f0 r0 m0 ok gt tr (D ++ [(x, Z.of_nat k)]) Lam peak cnt fail ran ->
  Permutation Lam ((x, Z.of_nat k) :: Lam') ->
  Ledger.lsum (D ++ [(x, Z.of_nat k)]) = PjGrammar.held tr ->
  rd_ledger_move L0 pk0 c0 f0 r0 m0 ok gt (tr ++ [EFree k]) D Lam' peak cnt fail ran /\
  Ledger.lsum D = PjGrammar.held (tr ++ [EFree k]).
Proof.
  intros L0 pk0 c0 f0 r0 m0 ok gt tr D Lam peak cnt fail ran Lam' x k
    (Hoks & Hcnt & Hfa & HPL & HPs & Hlen & Hpk) HPx Hls.
  assert (Hc : PjGrammar.calls (tr ++ [EFree k]) = PjGrammar.calls tr)
    by (rewrite vle_calls_app; cbn [PjGrammar.calls PjGrammar.is_call]; lia).
  assert (Hns : prh_ev_reqs (tr ++ [EFree k]) = prh_ev_reqs tr)
    by (rewrite vl_ev_reqs_app; change (prh_ev_reqs [EFree k]) with (@nil Z); apply app_nil_r).
  rewrite vl_lsum_app in Hls. cbn [Ledger.lsum] in Hls.
  split; [|rewrite vle_held_app; cbn [PjGrammar.held PjGrammar.held_ev]; lia].
  unfold rd_ledger_move. rewrite Hc, Hns.
  split; [exact Hoks|]. split; [exact Hcnt|]. split; [exact Hfa|].
  split.
  { apply (Permutation_cons_inv (a := (x, Z.of_nat k))).
    eapply perm_trans; [apply Permutation_sym; exact HPx|]. eapply perm_trans; [exact HPL|].
    rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  split.
  { unfold lszR in *. rewrite fold_left_app. cbn [fold_left lsz_evR].
    rewrite map_app in HPs. cbn [map fst snd] in HPs.
    assert (Hin : In k (fold_left lsz_evR tr [])).
    { assert (Hz : In (Z.of_nat k) (map Z.of_nat (fold_left lsz_evR tr []))).
      { apply (Permutation_in _ HPs). apply in_or_app. right. left. reflexivity. }
      apply in_map_iff in Hz as (k' & Hk' & Hin). apply Nat2Z.inj in Hk'. subst k'. exact Hin. }
    pose proof (vle_rm1n_perm _ k Hin) as Hr. apply (Permutation_map Z.of_nat) in Hr. cbn [map] in Hr.
    apply (Permutation_cons_inv (a := Z.of_nat k)).
    eapply perm_trans; [apply Permutation_cons_append|]. eapply perm_trans; [exact HPs | exact Hr]. }
  split.
  { rewrite length_app in Hlen. cbn [length] in Hlen.
    rewrite vl_nlive_app. cbn [nliveR nlive_evR]. lia. }
  rewrite Hpk, vle_hpeak_app. cbn [hpeakR PjGrammar.held_ev].
  pose proof (vle_held_le_hpeak tr). lia.
Qed.

End E.

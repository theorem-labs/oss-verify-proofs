From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB RecModel RecInv RecInvP
  RecChain rec_calls_free_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma freed_all : forall ps, (forall pn, In pn (concat ps) -> fst pn <> 0) -> freed ps = concat ps.
Proof.
  intros ps. unfold freed. generalize (concat ps). intros l H. induction l as [|x l IH]; [reflexivity|].
  cbn [List.filter]. destruct (fst x =? 0) eqn:E.
  - exfalso. apply Z.eqb_eq in E. exact (H x (or_introl eq_refl) E).
  - cbn [negb]. f_equal. apply IH. intros y Hy. exact (H y (or_intror Hy)).
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem rec_calls_free_g_holds : rec_calls_free_contract B API -> rec_calls_free_g_contract B API.
Proof.
  intros RCF. unfold rec_calls_free_g_contract.
  intros L A regs mem md R O b PRE RO A0 A1 (Q & HR & HO) RES.
  pose proof HR as (HS & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & (ND & _)).
  destruct HS as (_ & _ & _ & WG & _).
  assert (NZ : forall pn, In pn (concat (l_calls Q)) -> fst pn <> 0).
  { intros pn Hin. apply in_concat in Hin as (P & HP & Hpn).
    destruct (In_nth_error _ _ HP) as (i & Ei). destruct (In_nth_error _ _ Hpn) as (k & Ek).
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [cl|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i cl P Ec Ei) as ((_ & _ & LP & _ & _ & _ & SL) & _).
    assert (Hk : (k < length (snd cl))%nat) by (rewrite <- LP; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd cl) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    exact (proj1 (proj2 (SL k s pn Es Ek))). }
  assert (FD : freed (l_calls Q) = concat (l_calls Q)) by (apply freed_all; exact NZ).
  eapply SR_mono.
  - apply (RCF L A regs mem md (G_REC + OFF_CALLS) (l_calls Q) b PRE RO A0); [rewrite C2; exact A1 | | | | | | exact RES].
    + split; [rewrite C2; exact C1|]. intros i P EP.
      assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite EP; discriminate).
      destruct (nth_error (r_calls R) i) as [cl|] eqn:Ec; [|apply nth_error_None in Ec; lia].
      destruct (C4 i cl P Ec EP) as ((_ & L6 & LP & _ & BN & _ & SL) & _).
      split; [rewrite LP; exact L6|].
      split.
      { replace (G_REC + OFF_CALLS + 56 * Z.of_nat i + 4)
          with (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) by (unfold CALL_SIZE, CALL_OFF_NARGS; ring).
        rewrite LP. exact BN. }
      split.
      { intros j Hj. destruct WG as (_ & _ & W).
        replace (G_REC + OFF_CALLS + 56 * Z.of_nat i + 4 + j) with (G_REC + (OFF_CALLS + 56 * Z.of_nat i + 4 + j)) by ring.
        apply W. unfold OFF_CALLS, REC_SIZE. lia. }
      intros a pn Ea.
      assert (Ha : (a < length (snd cl))%nat) by (rewrite <- LP; apply nth_error_Some; rewrite Ea; discriminate).
      destruct (nth_error (snd cl) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
      destruct (SL a s pn Es Ea) as (BS & _ & IB & _).
      split; [|right; exact IB].
      replace (G_REC + OFF_CALLS + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a)
        with (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a)
        by (unfold CALL_SIZE, CALL_OFF_ARGS; ring).
      exact BS.
    + rewrite FD. first [apply NoDup_ListNoDup in ND | idtac]. first [apply NoDup_ListNoDup | idtac].
      unfold lay_blocks in ND. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND).
    + unfold G_REC, OFF_CALLS. lia.
    + rewrite C2. unfold G_REC, OFF_CALLS. lia.
    + intros j Hj. right. apply fg_iff. rewrite C2 in Hj. unfold G_REC, OFF_CALLS. lia.
  - intros c' (L' & A' & regs' & mem' & md' & E & CP & PERM & BK & UK & US & NB & AB & GB & ROc & GK & INI & RGN & UNI & RESc).
    rewrite C2, FD in *.
    assert (UNI' : st_init_done A = false -> L' = L /\ A' = A /\
              (forall lo, spZ regs <= lo -> auxv_pre B (ly_sec L) lo mem -> auxv_pre B (ly_sec L') lo mem')).
    { intros HI. destruct (UNI HI) as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
      intros lo Hlo AU. apply E3; [exact Hlo | | exact AU].
      pose proof PRE as (_ & _ & _ & _ & _ & HCE & _). pose proof alloc_ceiling_val as AC.
      unfold RCF_K, ALLOC_STACK, G_REC, OFF_CALLS in *. lia. }
    exists L', A', regs', mem', md', Q.
    exact (conj E (conj HR (conj HO (conj CP (conj PERM (conj BK (conj UK (conj US (conj NB (conj GB
             (conj ROc (conj GK (conj INI (conj RGN (conj UNI' RESc))))))))))))))).
Qed.

End G.

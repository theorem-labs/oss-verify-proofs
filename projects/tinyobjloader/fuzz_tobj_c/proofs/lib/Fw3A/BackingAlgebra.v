(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "of_nat"; "sub"; "to_nat"; "ltb"; "modulo"; "leb"; "max"; "min"; "mul"; "@Corelib.Init.Datatypes"; "prod"; "list"; "bool"; "app"; "nat"; "true"; "andb"; "negb"; "cons"; "nil"; "pair"; "false"; "length"; "orb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_maps"; "VmMaps"; "maps_subtract_all"; "m_vm_lazy"; "maps_subtract"; "vm_backing_used"; "vm_noaccess"; "m_vm_materialized"; "with_vmmaps"; "vm_forget_range"; "live_bytes"; "vm_add_lazy"; "vm_limit"; "page_size"; "lazy_interior"; "with_vm_backing"; "ProcInput"; "init_model"; "iv_subtract"; "page_outside_range"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "zcount"; "model_ivs_wf"; "sum_count"; "overlap_sum"; "in_rng"; "covered"; "iv_wf"; "ivB"; "ivS"; "iv_count"; "in_iv"; "@Stdlib.Lists.List"; "filter"; "In"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_budget_ok"; "mmap_noreserve_b"; "with_mmap_backing"; "with_mmap_replacement"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => (if P lo then 1 else 0) + zcount P (lo + 1) k
  end.

Lemma zcount_nonneg : ltac2:(tb__ "0|0|
S0S16F_;S0S18S7Z0S3aR3R2R1A3A2Fn;Flo;FP;").
Proof. intros P lo n. revert lo. induction n; intros lo; cbn; [lia|]. destruct (P lo); specialize (IHn (lo+1)); lia. Qed.

Lemma zcount_le_len : ltac2:(tb__ "0|0|
S0S16F_;S0S18S7S3aR3R2R1A3SbR1A1A2Fn;Flo;FP;").
Proof.
  intros P lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. rewrite Nat2Z.inj_succ. destruct (P lo); specialize (IHn (lo+1)); lia.
Qed.

Lemma zcount_mono : ltac2:(tb__ "0|1|
S0S16Fx;M0G0S0S18S0S2S7R3R1A2SaR1S8R3SbR2A1A2A2A2S1S16R6R2A1S19A3S1S16R6R3A1S19A3F_;F_;Fx;S7S3aR5R3R2A3S3aR4R3R2A3A2F_;Fn;Flo;FQ;FP;").
Proof.
  intros P Q lo n. revert lo. induction n; intros lo H; [cbn; lia|].
  cbn [zcount]. rewrite Nat2Z.inj_succ in H.
  assert (IH := IHn (lo + 1) ltac:(intros x Hx; apply H; lia)).
  destruct (P lo) eqn:EP.
  - rewrite (H lo ltac:(lia) EP). lia.
  - destruct (Q lo); lia.
Qed.

Lemma zcount_ext : ltac2:(tb__ "0|1|
S0S16Fx;M0G0S0S18S0S2S7R3R1A2SaR1S8R3SbR2A1A2A2A2S1S16R6R2A1R5R2A1A3F_;Fx;S1S0S3aR5R3R2A3S3aR4R3R2A3A3F_;Fn;Flo;FQ;FP;").
Proof.
  intros P Q lo n H.
  pose proof (zcount_mono P Q lo n ltac:(intros x Hx HP; rewrite <- (H x Hx); exact HP)).
  pose proof (zcount_mono Q P lo n ltac:(intros x Hx HQ; rewrite (H x Hx); exact HQ)). lia.
Qed.

Lemma zcount_or_le : ltac2:(tb__ "0|1|
S0S16Fx;M0G0S0S18S7S3aS0S21R5R1A1R4R1A1A2Lx;R2R1A3S8S3aR4R2R1A3S3aR3R2R1A3A2A2Fn;Flo;FQ;FP;").
Proof.
  intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [orb]; lia.
Qed.

Lemma zcount_and_split : ltac2:(tb__ "0|2|
S0S16F_;S0S16Fx;S0S18S1S0S3aR4R2R1A3S8S3aS0S1aR5R1A1M0R4R1A1M1A2Lx;R2R1A3S3aS0S1aG0S1bG1A1A2Lx;R2R1A3A2A3Fn;Flo;FQ;FP;").
Proof.
  intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [andb negb]; lia.
Qed.

Lemma zcount_const_false : ltac2:(tb__ "0|0|
S0S18S1S0S3aS0S1fL_;R2R1A3Z0A3Fn;Flo;").
Proof. intros lo n. revert lo. induction n; intros; cbn; [lia|]. rewrite IHn. lia. Qed.

Lemma zcount_const_true : ltac2:(tb__ "0|0|
S0S18S1S0S3aS0S19L_;R2R1A3SbR1A1A3Fn;Flo;").
Proof. intros lo n. revert lo. induction n; intros; [cbn; lia|]. cbn [zcount]. rewrite Nat2Z.inj_succ, IHn. lia. Qed.

Lemma zcount_false : ltac2:(tb__ "0|0|
S0S16Fx;S0S18S0S2S7R3R1A2SaR1S8R3SbR2A1A2A2A2S1S16R5R2A1S1fA3F_;Fx;S1S0S3aR4R3R2A3Z0A3F_;Fn;Flo;FP;").
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => false) lo n H). apply zcount_const_false. Qed.

Lemma zcount_true : ltac2:(tb__ "0|1|
S0S16Fx;S0S18S0S2S7R3R1A2SaR1S8R3SbR2A1M0A2A2A2S1S16R5R2A1S19A3F_;Fx;S1S0S3aR4R3R2A3G0A3F_;Fn;Flo;FP;").
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => true) lo n H). apply zcount_const_true. Qed.

Lemma zcount_split : ltac2:(tb__ "0|0|
S0S16F_;S0S18S18S1S0S3aR4R3S4cR2R1A2A3S8S3aR4R3R2A3S3aR4S8R3SbR2A1A2R1A3A2A3Fn2;Fn1;Flo;FP;").
Proof.
  intros P lo n1 n2. revert lo. induction n1; intros lo.
  - cbn [zcount Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [zcount Nat.add]. rewrite IHn1, Nat2Z.inj_succ.
    replace (lo + 1 + Z.of_nat n1) with (lo + Z.succ (Z.of_nat n1)) by lia. lia.
Qed.

Definition ivB (p : word * word) : Z := bv_unsigned (fst p).
Definition ivS (p : word * word) : Z := bv_unsigned (snd p).

Definition in_rng (lo hi x : Z) : bool := ltac2:(tb__ "0|0|
S1aS10Vlo;Vx;A2SeVx;Vhi;A2A2").
Definition in_iv (p : word * word) (x : Z) : bool := ltac2:(tb__ "0|1|
S3eS41Vp;A1M0S8G0S42Vp;A1A2Vx;A3").

Definition covered (C : list (word * word)) (x : Z) : bool := ltac2:(tb__ "0|2|
S47S14S4Q40A1M0G0A2M1G1S44R1Vx;A2Lc;VC;A3").

Definition iv_count (P : Z -> bool) (p : word * word) : Z := ltac2:(tb__ "0|0|
S3aVP;S41Vp;A1SdS42Vp;A1A1A3").

Definition iv_wf (p : word * word) : Prop := ltac2:(tb__ "0|0|
S7S8S41Vp;A1S42Vp;A1A2S9Z2Z40A2A2").

Lemma B_range : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2S2S7Z0S41R1A1M1A2SaG1S9Z2Z40A2A2A2Fp;").
Proof. intros p. unfold ivB. exact (bv_unsigned_in_range _ (fst p)). Qed.
Lemma S_range : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2S2S7Z0S42R1A1M1A2SaG1S9Z2Z40A2A2A2Fp;").
Proof. intros p. unfold ivS. exact (bv_unsigned_in_range _ (snd p)). Qed.

Lemma fg_lit : ltac2:(tb__ "0|1|
S0S2S7Z0R1A2SaR1S9Z2Z40A2A2A2S1S0S5Q40M0S6G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma live_bytes_app : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2S1S0S2eS17G1R2R1A3A1S8S2eR2A1S2eR1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn -[Z.add]; [lia|rewrite IH; lia]. Qed.

Lemma maps_subtract_app : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2S0S0S1G2S28S17G1R4R3A3R2R1A3S17G1S28R4R2R1A3S28R3R2R1A3A3A3Fhi;Flo;Fl2;Fl1;").
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|rewrite IH, app_assoc; reflexivity]. Qed.

Lemma maps_subtract_all_app : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2G2S1G2S26S17G1R2R1A3R3A2S17G1S26R2R3A2S26R1R3A2A3A3Fl2;Fl1;FC;").
Proof.
  induction C as [|[a n] C IH]; intros; cbn; [reflexivity|].
  rewrite maps_subtract_app. apply IH.
Qed.

Lemma maps_subtract_all_nil_l : ltac2:(tb__ "0|4|
S15S14S4Q40A1M0G0A2M1A1M2S1G2S26S1dG1A1M3R1A2G3A3FC;").
Proof. induction C as [|[a n] C IH]; cbn; [reflexivity|exact IH]. Qed.

Lemma maps_subtract_all_cons_l : ltac2:(tb__ "0|3|
S14S4Q40A1M0G0A2M1S15G1A1M2G2S1G2S26S1cG1R3R2A3R1A2S17G1S26S1cG1R3S1dG1A1A3R1A2S26R2R1A2A3A3FC;Fl;Fp;").
Proof. intros. change (p :: l) with ([p] ++ l). apply maps_subtract_all_app. Qed.

Fixpoint sum_count (P : Z -> bool) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | q :: r => iv_count P q + sum_count P r
  end.

Lemma sum_count_app : ltac2:(tb__ "0|3|
S0S16F_;S15S14S4Q40A1M0G0A2M1A1M2G2S1S0S3cR3S17G1R2R1A3A2S8S3cR3R2A2S3cR3R1A2A2A3Fl2;Fl1;FP;").
Proof. induction l1; intros; cbn -[Z.add]; [lia|rewrite IHl1; lia]. Qed.

Lemma sum_count_nonneg : ltac2:(tb__ "0|1|
S0S16F_;S15S14S4Q40A1M0G0A2A1S7Z0S3cR2R1A2A2Fl;FP;").
Proof. induction l; cbn -[Z.add]; [lia|]. pose proof (zcount_nonneg P (ivB a) (Z.to_nat (ivS a))). unfold iv_count. lia. Qed.

Lemma sum_count_mono : ltac2:(tb__ "0|2|
S0S16Fx;M0G0S15S14S4Q40A1M1G1A2A1S0S1S16R4R1A1S19A3S1S16R4R2A1S19A3F_;Fx;S7S3cR4R2A2S3cR3R2A2A2F_;Fl;FQ;FP;").
Proof.
  intros P Q l H. induction l; cbn -[Z.add]; [lia|].
  pose proof (zcount_mono P Q (ivB a) (Z.to_nat (ivS a)) ltac:(intros; auto)). unfold iv_count. lia.
Qed.

Lemma sum_count_ext : ltac2:(tb__ "0|2|
S0S16Fx;M0G0S15S14S4Q40A1M1G1A2A1S0S1S16R4R1A1R3R1A1A3Fx;S1S0S3cR4R2A2S3cR3R2A2A3F_;Fl;FQ;FP;").
Proof.
  intros P Q l H. induction l; cbn -[Z.add]; [lia|].
  unfold iv_count. rewrite (zcount_ext P Q) by (intros; apply H). lia.
Qed.

Lemma sum_count_or_le : ltac2:(tb__ "0|2|
S0S16Fx;M0G0S15S14S4Q40A1M1G1A2A1S7S3cS0S21R4R1A1R3R1A1A2Lx;R1A2S8S3cR3R1A2S3cR2R1A2A2A2Fl;FQ;FP;").
Proof.
  intros P Q l. induction l; cbn -[Z.add]; [lia|].
  pose proof (zcount_or_le P Q (ivB a) (Z.to_nat (ivS a))). unfold iv_count in *. lia.
Qed.

Lemma live_bytes_sum_count : ltac2:(tb__ "0|1|
S15S14S4Q40A1M0G0A2A1S1S0S2eR1A1S3cS0S19L_;R1A2A3Fl;").
Proof.
  induction l as [|[b s] l IH]; cbn -[Z.add]; [lia|].
  unfold iv_count, ivB, ivS. cbn [fst snd]. rewrite zcount_const_true, IH.
  pose proof (bv_unsigned_in_range 64 s). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition ivs_wf (l : list (word * word)) : Prop := ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S46G1R1Vl;A3S40R2A1F_;Fq;").

Lemma ivs_wf_nil : ivs_wf [].
Proof. intros q []. Qed.
Lemma ivs_wf_cons : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S15G1A1S40R2A1S39R2A1S39S1cG1R4R3A3A1F_;F_;Fl;Fp;").
Proof. intros p l Hp Hl q [<-|Hq]; auto. Qed.
Lemma ivs_wf_cons_inv : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S15G1A1S39S1cG1R2R1A3A1S2S40R3A1S39R2A1A2F_;Fl;Fp;").
Proof. intros p l H. split; [apply H; now left|intros q Hq; apply H; now right]. Qed.
Lemma ivs_wf_app : ltac2:(tb__ "0|4|
S15S14S4Q40A1M0G0A2M1A1M2G2S39R2A1M3G3S39S17G1R4R3A3A1F_;F_;Fl2;Fl1;").
Proof. intros l1 l2 H1 H2 q Hq. apply in_app_iff in Hq as [Hq|Hq]; auto. Qed.
Lemma ivs_wf_app_inv : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2S39S17G1R2R1A3A1S2S39R3A1S39R2A1A2F_;Fl2;Fl1;").
Proof. intros l1 l2 H. split; intros q Hq; apply H; apply in_app_iff; auto. Qed.
Lemma ivs_wf_filter : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S16F_;S15G1A1S39R1A1S39S45G1R3R2A3A1F_;Fl;Ff;").
Proof. intros f l H q Hq. apply filter_In in Hq as [Hq _]. auto. Qed.
Lemma iv_wf_intro : ltac2:(tb__ "0|2|
S4Q40M0A1M1G1S7S8S5G0R2A2S5G0R1A2A2S9Z2Z40A2A2S40S1eG1G1R3R2A4A1F_;Fn;Fa;").
Proof. intros a n H. exact H. Qed.

Ltac in_rng_tf :=
  intros x Hx; unfold in_rng;
  first [ rewrite (proj2 (Z.leb_gt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r; reflexivity]
        | rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity]
        | rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity] ].

Lemma count_outside_gen : ltac2:(tb__ "0|4|
S0S16Fx;S0S0S0S0S7Z0M0R1A2S7R5R4A2S1S0S3aS0S1aR8R1A1S1bS3eR7R6R1A3A1A2Lx;R4SdR3A1A3S8S16S0L_;M1SeR4R6A2S3aR7R4SdS12R3ScR6R4A2A2A1A3G0X16x2G1SeR5S8R4R3A2M2A2S3aR7S11R4R5A2M3SdScG2G3A2A1A3G0X16x2A2A3F_;F_;FZ_;FA;Fhi;Flo;FP;").
Proof.
  intros P lo hi A Z_ HZ Hlh.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er.
  - destruct (Z.le_gt_cases (lo - A) Z_) as [H1|H1]; [|lia].
    replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + (Z.to_nat (hi - lo) + Z.to_nat (A + Z_ - hi)))%nat by lia.
    rewrite !zcount_split.
    rewrite (zcount_ext _ P A) by in_rng_tf.
    rewrite (zcount_false _ (A + _)) by in_rng_tf.
    rewrite (zcount_ext _ P (A + _ + _)) by in_rng_tf.
    rewrite (Z.min_r Z_ (lo - A) H1), (Z.max_r A hi) by lia.
    rewrite !Z2Nat.id by lia.
    replace (A + (lo - A) + (hi - lo)) with hi by lia.
    replace (A + Z_ - hi) with (A + Z_ - hi) by lia. lia.
  - destruct (Z.le_gt_cases (A + Z_) lo) as [H1|H1].
    + rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.min_l Z_ (lo - A)) by lia. lia.
    + replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + Z.to_nat (A + Z_ - lo))%nat by lia.
      rewrite zcount_split.
      rewrite (zcount_ext _ P A) by in_rng_tf.
      rewrite (zcount_false _ (A + _)) by in_rng_tf.
      rewrite (Z.min_r Z_ (lo - A)) by lia. lia.
  - destruct (Z.le_gt_cases hi A) as [H1|H1].
    + rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.max_l A hi) by lia.
      replace (A + Z_ - A) with Z_ by lia. lia.
    + replace (Z.to_nat Z_) with (Z.to_nat (hi - A) + Z.to_nat (A + Z_ - hi))%nat by lia.
      rewrite zcount_split.
      rewrite (zcount_false _ A) by in_rng_tf.
      rewrite (zcount_ext _ P (A + _)) by in_rng_tf.
      rewrite (Z.max_r A hi) by lia. rewrite !Z2Nat.id by lia.
      replace (A + (hi - A)) with hi by lia. lia.
  - rewrite zcount_false by in_rng_tf. lia.
Qed.

Lemma count_inside : ltac2:(tb__ "0|0|
S0S0S0S0S7Z0R1A2S7R5R4A2S7S3aS3eR6R5A2R4SdR3A1A3ScR5R6A2A2F_;F_;FZ_;FA;Fhi;Flo;").
Proof.
  intros lo hi A Z_ HZ Hlh.
  pose proof (zcount_and_split (fun _ => true) (in_rng lo hi) A (Z.to_nat Z_)) as Hsplit.
  cbn [andb] in Hsplit. rewrite zcount_const_true, Z2Nat.id in Hsplit by lia.
  rewrite (zcount_ext (fun x => negb (in_rng lo hi x)) (fun x => true && negb (in_rng lo hi x))) in Hsplit by reflexivity.
  rewrite (count_outside_gen (fun _ => true) lo hi A Z_ HZ Hlh) in Hsplit.
  rewrite !zcount_const_true in Hsplit.
  rewrite (zcount_ext (fun x => in_rng lo hi x) (in_rng lo hi)) in Hsplit by reflexivity.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er; rewrite ?Z2Nat.id in Hsplit by lia; lia.
Qed.

Lemma iv_subtract_sem : ltac2:(tb__ "0|4|
S4Q40A1M0G0S0S0S40S1eG0G0R4R3A4A1S7R3R2A2S2S14G0G0A2M1S46G1R1S36R7R6R5R4A4M2A3S40R2A1F_;Fq;S2S0S16F_;S1S0S3cR1G2A2S43S0S1aR2R1A1S1bS3eR6R5R1A3A1A2Lx;S1eG0G0R7R6A4M3A2A3FP;S0S1S16S3fG2R1A2S1aS44G3R1A2S1bS3eR5R4R1A3A1A2A3Fx;A2A2F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, iv_count, ivB, ivS in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  unfold bv_modulus in Ha, Hs.
  set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
  unfold iv_subtract. cbv zeta. fold A. fold Z_.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    pose proof El as El'; pose proof Er as Er';
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El', Er'; cbn [app].
  -
    assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
    assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
    assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[<-|[]]]; cbn [fst snd]; rewrite ?E1, ?E2, ?E3; lia.
    + intros P. cbn [sum_count]. unfold iv_count, ivB, ivS. cbn [fst snd]. fold A. rewrite E1, E2, E3.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, ivB, ivS. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, E2, E3, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite orb_true_iff, !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  -
    assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[]]; cbn [fst snd]; rewrite ?E1; lia.
    + intros P. cbn [sum_count]. unfold iv_count, ivB, ivS. cbn [fst snd]. fold A. rewrite E1.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, ivB, ivS. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  -
    assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
    assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[]]; cbn [fst snd]; rewrite ?E2, ?E3; lia.
    + intros P. cbn [sum_count]. unfold iv_count, ivB, ivS. cbn [fst snd]. rewrite E2, E3.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, ivB, ivS. cbn [existsb fst snd]. fold A. fold Z_. rewrite E2, E3, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  -
    split; [|split].
    + intros q [].
    + intros P. cbn [sum_count]. unfold iv_count, ivB, ivS. cbn [fst snd].
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, ivB, ivS. cbn [existsb fst snd]. fold A. fold Z_.
      symmetry. apply andb_false_iff.
      destruct (Z.lt_ge_cases x A); [left|]. { apply andb_false_iff. left. apply Z.leb_gt. lia. }
      destruct (Z.lt_ge_cases x (A + Z_)); [right|left].
      { apply negb_false_iff. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma maps_subtract_sem : ltac2:(tb__ "0|2|
S15S14S4Q40A1M0G0A2A1S0S0S39R3A1S7R3R2A2S2S39S28R5R4R3A3A1S2S0S16F_;S1S0S3cR1S28R6R5R4A3M1A2S3cS0S1aR2R1A1S1bS3eR6R5R1A3A1A2Lx;R6A2A3FP;S0S1S16S3fG1R1A2S1aS3fR6R1A2S1bS3eR5R4R1A3A1A2A3Fx;A2A2F_;F_;Fhi;Flo;Fl;").
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hwf Hlh.
  - cbn. split; [apply ivs_wf_nil|]. split; [reflexivity|]. intros; reflexivity.
  - apply ivs_wf_cons_inv in Hwf as [Ha Hl].
    destruct (IH lo hi Hl Hlh) as (W & Sm & Cv).
    destruct (iv_subtract_sem a sz lo hi Ha Hlh) as (W1 & Sm1 & Cv1).
    cbn [maps_subtract]. split; [|split].
    + apply ivs_wf_app; [intros q Hq; apply W1; exact Hq|exact W].
    + intros P. rewrite sum_count_app, Sm1, Sm. reflexivity.
    + intros x. unfold covered. rewrite existsb_app. fold (covered (iv_subtract a sz lo hi) x).
      fold (covered (maps_subtract l lo hi) x). fold (covered l x). rewrite Cv1, Cv.
      cbn [existsb]. fold (covered l x). destruct (in_iv (a, sz) x), (covered l x), (in_rng lo hi x); reflexivity.
Qed.

Lemma maps_subtract_wf : ltac2:(tb__ "0|1|
S15S14S4Q40A1M0G0A2A1S0S0S39R3A1S7R3R2A2S39S28R5R4R3A3A1F_;F_;Fhi;Flo;Fl;").
Proof. intros. apply maps_subtract_sem; assumption. Qed.

Lemma covered_app : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2S0S1S16S3fS17G1R3R2A3R1A2S21S3fR3R1A2S3fR2R1A2A2A3Fx;Fl2;Fl1;").
Proof. intros. unfold covered. apply existsb_app. Qed.

Lemma maps_subtract_all_app_cuts : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2G2S1G2S26R3S17G1R2R1A3A2S26S26R3R2A2R1A2A3FC2;FC1;Fl;").
Proof. intros l C1; revert l; induction C1 as [|[a n] C1 IH]; intros; cbn; [reflexivity|apply IH]. Qed.

Theorem live_msa : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2A1M1G1S39R1A1S2S1S0S2eS26R2R3A2M2A1S3cS0S1bS3fR4R1A2A1Lx;R2A2A3S39G2A1A2F_;Fl;FC;").
Proof.
  induction C as [|[a n] C IH]; intros l Hwf.
  - cbn [maps_subtract_all covered existsb negb]. split; [apply live_bytes_sum_count|exact Hwf].
  - cbn [maps_subtract_all].
    pose proof (bv_unsigned_in_range 64 n) as Hn.
    destruct (maps_subtract_sem l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hwf ltac:(lia)) as (W & Sm & Cv).
    destruct (IH _ W) as [Hl Hw]. split; [|exact Hw].
    rewrite Hl, Sm. apply sum_count_ext. intros x.
    unfold covered at 2. cbn [existsb]. fold (covered C x). unfold in_iv, ivB, ivS. cbn [fst snd].
    destruct (covered C x), (in_rng _ _ x); reflexivity.
Qed.

Lemma m_vmmaps_with_vmmaps : ltac2:(tb__ "0|0|
S25S22S1S25S23S2cR2R1A2A1R2A3Fm;Fh;"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : ltac2:(tb__ "0|1|
S25S22S1S15S14S4Q40A1M0G0A2A1S27S2cR2R1A2A1S27R1A1A3Fm;Fh;"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : ltac2:(tb__ "0|0|
S25S22S1S15S4Q40A1A1S2bS2cR2R1A2A1S2bR1A1A3Fm;Fh;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vm_backing : ltac2:(tb__ "0|1|
S15S14S4Q40A1M0G0A2A1S15G0A1S22S1S25S23S33R3R2R1A3A1S23R1A1A3Fm;Fp;Fl;"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vm_backing : ltac2:(tb__ "0|2|
S15S14S4Q40A1M0G0A2A1M1S15G0A1S22S1G1S27S33R3R2R1A3A1R3A3Fm;Fp;Fl;"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vm_backing : ltac2:(tb__ "0|2|
S15S14S4Q40A1M0G0A2A1S15G0A1M1S22S1G1S2bS33R3R2R1A3A1R2A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : ltac2:(tb__ "0|0|
S0S0S22S1S25S23S2dR3R2R1A3A1S23R1A1A3Fm;Fhi;Flo;"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_forget_range : ltac2:(tb__ "0|1|
S0S0S22S1S15S14S4Q40A1M0G0A2A1S27S2dR3R2R1A3A1S28S27R1A1R3R2A3A3Fm;Fhi;Flo;"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_forget_range : ltac2:(tb__ "0|1|
S0S0S22S1S15S4Q40A1M0A1S2bS2dR3R2R1A3A1S45G0S37R3R2A2S2bR1A1A3A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy : ltac2:(tb__ "0|1|
S4Q40A1M0G0S22S1S25S23S2fR3R2R1A3A1S23R1A1A3Fm;Fn;Fa;"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_add_lazy : ltac2:(tb__ "0|2|
S4Q40A1M0G0S22S1S15S14G0G0A2M1A1S27S2fR3R2R1A3A1S17G1S32R3R2A2S27R1A1A3A3Fm;Fn;Fa;"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_add_lazy : ltac2:(tb__ "0|1|
S4Q40A1M0G0S22S1S15G0A1S2bS2fR3R2R1A3A1S2bR1A1A3Fm;Fn;Fa;"). Proof. reflexivity. Qed.

Ltac model_proj :=
  rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
          ?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
          ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps.

Definition model_ivs_wf (m : Model) : Prop := ltac2:(tb__ "0|1|
S2S39S24S23Vm;A1M0A1A1S2S39S2aG0A1A1S39S27Vm;A1A1A2A2").

Definition overlap_sum (l : list (word * word)) (lo hi : Z) : Z := ltac2:(tb__ "0|0|
S3cS3eVlo;Vhi;A2Vl;A2").

Lemma overlap_sum_app : ltac2:(tb__ "0|3|
S15S14S4Q40A1M0G0A2M1A1M2G2S0S0S1S0S3dS17G1R4R3A3R2R1A3S8S3dR4R2R1A3S3dR3R2R1A3A2A3Fhi;Flo;Fl2;Fl1;").
Proof. intros. apply sum_count_app. Qed.

Lemma overlap_sum_cons : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S15G1A1S0S0S1S0S3dS1cG1R4R3A3R2R1A3S8S43S3eR2R1A2R4A2S3dR3R2R1A3A2A3Fhi;Flo;Fl;Fp;").
Proof. reflexivity. Qed.

Lemma overlap_sum_nil : ltac2:(tb__ "0|1|
S0S0S1S0S3dS1dS14S4Q40A1M0G0A2A1R2R1A3Z0A3Fhi;Flo;").
Proof. reflexivity. Qed.

Lemma iv_count_in_rng_le : ltac2:(tb__ "0|1|
S14S4Q40A1M0G0A2S0S0S7R2R1A2S7S43S3eR3R2A2R4A2ScR2R3A2A2F_;Fhi;Flo;Fp;").
Proof. intros p lo hi H. unfold iv_count. apply count_inside; [pose proof (S_range p); lia|exact H]. Qed.

Lemma iv_count_in_rng_disjoint : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2S0S0S3S7S8S41R3A1M1S42R3A1A2R2A2S7R1G1A2A2S1S0S43S3eR3R2A2R4A2Z0A3F_;Fhi;Flo;Fp;").
Proof.
  intros p lo hi H. unfold iv_count. apply zcount_false. intros x Hx.
  pose proof (S_range p). rewrite Z2Nat.id in Hx by lia.
  unfold in_rng. apply andb_false_iff. destruct H; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

Lemma overlap_sum_region_free : ltac2:(tb__ "0|3|
S15S14S4Q40M0A1M1G1A2A1G1G1S1S16S38R3R2R1A3S19A3S1S0S3dR4S5G0R3A2M2S8G2S5G0R2A2A2A3Z0A3F_;Fn;Flo;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free] in H. apply andb_true_iff in H as [H1 H2].
  rewrite overlap_sum_cons, (IH _ _ H2), iv_count_in_rng_disjoint; [lia|].
  apply negb_true_iff in H1. unfold iv_overlap in H1. unfold ivB, ivS. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma overlap_sum_single_le : ltac2:(tb__ "0|2|
S14S4Q40A1M0G0A2M1S0S0S7R2R1A2S7S3dS1cG1R4S1dG1A1A3R3R2A3ScR2R3A2A2F_;Fhi;Flo;Fp;").
Proof. intros. rewrite overlap_sum_cons, overlap_sum_nil. pose proof (iv_count_in_rng_le p lo hi H). lia. Qed.

Lemma vm_backing_used_sem : ltac2:(tb__ "0|1|
S22S3bR1A1S1S0S29R2A1S8S3cS0S1bS3fS17S14S4Q40A1M0G0A2S2aS23R3A1A1S27R3A1A3R1A2A1Lx;S24S23R2A1A1A2S13SbS20G0S2bR2A1A2A1S31A2A2A3F_;Fm;").
Proof.
  intros m (Wm & Wn & Wl). unfold vm_backing_used, vm_backed_maps.
  rewrite <- maps_subtract_all_app_cuts. rewrite (proj1 (live_msa _ _ Wm)). reflexivity.
Qed.

Lemma filter_length_le {A} : ltac2:(tb__ "0|0|
VA;S16F_;S15VA;A1S4dS20VA;S45VA;R2R1A3A2S20VA;R1A2A2Fl;Ff;").
Proof. induction l; cbn; [lia|]. destruct (f a); cbn; lia. Qed.

Theorem backing_forget_commit_le : ltac2:(tb__ "0|2|
S22S25S0S0S3bR4A1S7R3R2A2S1S15S14S4Q40A1M0G0A2A1M1S24R5A1S24S23R6A1A1A3S1G1S2aR6A1S28S2aS23R7A1A1R5R4A3A3S7S29S2dR6R5S2cR7R8A2A3A1S8S29R8A1S3dS24S23R8A1A1R6R5A3A2A2F_;F_;F_;F_;Fhi;Flo;Fh';Fm;").
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl).
  assert (Hwf' : model_ivs_wf (vm_forget_range lo hi (with_vmmaps h' m))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna.
    split; [exact Wm|split; apply maps_subtract_wf; assumption]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  unfold overlap_sum.
  eapply Z.le_trans.
  { apply Z.add_le_mono_r.
    apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
    intros x. rewrite !covered_app, Cn, Cl.
    destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
  pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
                (vm_maps (m_vmmaps m))).
  unfold page_size in *. lia.
Qed.

Theorem backing_mprotect_le : ltac2:(tb__ "0|2|
S22S25S0S0S3bR4A1S7R3R2A2S1S15S14S4Q40A1M0G0A2A1M1S24R5A1S24S23R6A1A1A3S1G1S2aR6A1S28S2aS23R7A1A1R5R4A3A3S7S29S2cR7R8A2A1S8S29R8A1S3dS24S23R8A1A1R6R5A3A2A2F_;F_;F_;F_;Fhi;Flo;Fh';Fm;").
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl).
  assert (Hwf' : model_ivs_wf (with_vmmaps h' m)).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna.
    split; [exact Wm|split; [apply maps_subtract_wf; assumption|exact Wl]]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  unfold overlap_sum.
  eapply Z.le_trans.
  { apply Z.add_le_mono_r.
    apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
    intros x. rewrite !covered_app, Cn.
    destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
  pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
                (vm_maps (m_vmmaps m))).
  unfold page_size in *. lia.
Qed.

Lemma lazy_interior_aligned : ltac2:(tb__ "0|5|
S4Q40M0A1M1G1S1S0SfS5G0R2A2S31A2Z0M2A3M3G3SaG2S5G0R3A2A2S7S8S5G0R5A2S5G0R4A2A2S9Z2Z40A2A2S1S15S14G1G1A2M4A1S32R6R5A2S1cG4S1eG1G1R6R5A4S1dG4A1A3A3F_;F_;F_;F_;Fn;Fa;").
Proof.
  intros a n Ha Hn Hpos Hwf. unfold lazy_interior, page_size in *.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn.
  unfold bv_modulus in Ra, Rn.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Da.
  pose proof (Z.div_mod (bv_unsigned n) 4096 ltac:(lia)) as Dn.
  rewrite Ha in Da. rewrite Hn in Dn.
  set (qa := bv_unsigned a / 4096) in *. set (qn := bv_unsigned n / 4096) in *.
  assert (E1 : (bv_unsigned a + 4096 - 1) / 4096 * 4096 = bv_unsigned a).
  { rewrite Da. replace (4096 * qa + 0 + 4096 - 1) with (qa * 4096 + 4095) by lia.
    rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (E2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 = bv_unsigned a + bv_unsigned n).
  { rewrite Da, Dn. replace (4096 * qa + 0 + (4096 * qn + 0)) with ((qa + qn) * 4096) by lia.
    rewrite Z.div_mul by lia. lia. }
  cbv zeta. rewrite E1, E2.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  f_equal. f_equal.
  - apply bv_eq. rewrite fg_lit by lia. reflexivity.
  - apply bv_eq. rewrite fg_lit by lia. lia.
Qed.

Theorem backing_recommit_lazy_le : ltac2:(tb__ "0|7|
S22S25S4Q40M0A1M1G1S3bR4A1S1S0SfS5G0R3A2S31A2Z0M2A3M3G3SaG2S5G0R4A2A2S7S8S5G0R6A2S5G0R5A2A2S9Z2Z40A2A2S1S15S14G1G1A2A1M4S24R8A1S24S23R9A1A1A3S1G4S2aR9A1S28S2aS23RaA1A1S5G0R8A2M5S8G5S5G0R7A2A2A3A3S7S29S2fR9R8S2dS5G0R9A2M6S8G6G5A2S2cRaRbA2A3A3A1S29RbA1A2F_;F_;F_;F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl).
  set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
  assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  assert (Hwf' : model_ivs_wf (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna, Hli.
    split; [exact Wm|split; [apply maps_subtract_wf; assumption|]].
    apply (ivs_wf_cons (a, n)); [exact Hend|apply maps_subtract_wf; assumption]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna, Hli.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  apply Z.add_le_mono; [|unfold page_size; nia].
  apply sum_count_mono. intros x Hx.
  rewrite covered_app in Hx. rewrite covered_app in Hx. rewrite Cn, Cl in Hx. rewrite covered_app.
  revert Hx. unfold covered at 2. cbn [existsb]. unfold in_iv, ivB, ivS. cbn [fst snd]. fold lo. fold hi.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence.
Qed.

Lemma vm_limit_with_vmmaps : ltac2:(tb__ "0|0|
S25S22S1S0S30S23S2cR2R1A2A1A1S30R2A1A3Fm;Fh;").
Proof. reflexivity. Qed.

Theorem mmap_fixed_rw_budget_ok_commit_intro : ltac2:(tb__ "0|4|
S4Q40M0A1M1S22G1G1S1S16S49R4A1S1fA3S3bR4A1S7S8S29R5A1S3dS24S23R5A1M2A1S5G0R4A2M3S8G3S5G0R3A2A2A3A2S30G2A1A2S1S16S48R7R6R5R4A4S19A3F_;F_;F_;Fn;Faddr;Fm;Fflags;").
Proof.
  intros flags m addr n Hnr Hwf Hb.
  unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
  rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
  pose proof (bv_unsigned_in_range 64 n).
  pose proof (backing_forget_commit_le m (mmap_fixed_rw_next (m_vmmaps m) addr n)
                (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl).
  unfold mmap_fixed_rw_next in *. lia.
Qed.

Theorem mmap_fixed_rw_budget_ok_recommit_intro : ltac2:(tb__ "0|4|
S4Q40M0A1M1S22G1G1S1S16S49R4A1S19A3S3bR4A1S1S0SfS5G0R4A2S31A2Z0M2A3M3G3SaG2S5G0R5A2A2S7S8S5G0R7A2S5G0R6A2A2S9Z2Z40A2A2S7S29R9A1S30S23R9A1A1A2S1S16S48RbRaR9R8A4S19A3F_;F_;F_;F_;F_;F_;F_;Fn;Faddr;Fm;Fflags;").
Proof.
  intros flags m addr n Hnr Hwf Hal Hnl Hpos Hend Hb.
  unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
  rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
  pose proof (backing_recommit_lazy_le m (mmap_fixed_rw_next (m_vmmaps m) addr n) addr n
                Hwf Hal Hnl Hpos Hend eq_refl eq_refl).
  unfold mmap_fixed_rw_next in *. lia.
Qed.

Theorem mprotect_budget_ok_intro_gen : ltac2:(tb__ "0|4|
S22S4Q40M0A1M1G1S3bR3A1S7S8S29R4A1S3dS24S23R4A1M2A1S5G0R3A2M3S8G3S5G0R2A2A2A3A2S30G2A1A2S1S16S4eR5R4R3A3S19A3F_;F_;Fn;Faddr;Fm;").
Proof.
  intros m addr n Hwf Hb.
  unfold mprotect_budget_ok, vm_backing_within_limit, mprotect_model_next.
  apply Z.leb_le. model_proj. cbn [vm_limit].
  pose proof (bv_unsigned_in_range 64 n).
  pose proof (backing_mprotect_le m
                (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)))
                (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl) as Hle.
  cbv zeta in Hle. lia.
Qed.

Lemma lazy_interior_wf : ltac2:(tb__ "0|2|
S4Q40M0A1M1G1S7S8S5G0R2A2S5G0R1A2A2S9Z2Z40A2A2S39S32R3R2A2A1F_;Fn;Fa;").
Proof.
  intros a n H. unfold lazy_interior. cbv zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
  unfold page_size.
  set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096). set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096).
  assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
  { subst hi'. pose proof (Z.mul_div_le (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). lia. }
  assert (Hlo : 0 <= lo').
  { subst lo'. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. }
  destruct (lo' <? hi') eqn:E; [|apply ivs_wf_nil].
  apply Z.ltb_lt in E. apply ivs_wf_cons; [|apply ivs_wf_nil].
  unfold iv_wf, ivB, ivS. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.

Lemma model_ivs_wf_intro : ltac2:(tb__ "0|0|
S22S39S24S23R1A1A1A1S39S2aS23R2A1A1A1S39S27R3A1A1S3bR4A1F_;F_;F_;Fm;").
Proof. intros; repeat split; assumption. Qed.

Lemma model_ivs_wf_with_vmmaps : ltac2:(tb__ "0|0|
S25S22S3bR1A1S39S24R3A1A1S39S2aR4A1A1S3bS2cR5R4A2A1F_;F_;F_;Fm;Fh;").
Proof. intros h m (_ & _ & Wl) Hm Hn. unfold model_ivs_wf. model_proj. repeat split; assumption. Qed.

Lemma model_ivs_wf_vm_forget_range : ltac2:(tb__ "0|0|
S0S0S22S7R3R2A2S3bR2A1S3bS2dR5R4R3A3A1F_;F_;Fm;Fhi;Flo;").
Proof.
  intros lo hi m Hlh (Wm & Wn & Wl). unfold model_ivs_wf. model_proj.
  repeat split; try assumption. apply maps_subtract_wf; assumption.
Qed.

Lemma model_ivs_wf_vm_add_lazy : ltac2:(tb__ "0|2|
S4Q40M0A1M1G1S22S7S8S5G0R3A2S5G0R2A2A2S9Z2Z40A2A2S3bR2A1S3bS2fR5R4R3A3A1F_;F_;Fm;Fn;Fa;").
Proof.
  intros a n m H (Wm & Wn & Wl). unfold model_ivs_wf. model_proj.
  repeat split; try assumption. apply ivs_wf_app; [apply lazy_interior_wf; exact H|exact Wl].
Qed.

Lemma model_ivs_wf_with_mmap_backing : ltac2:(tb__ "0|2|
S4Q40M0A1M1G1G1S22S7S8S5G0R3A2S5G0R2A2A2S9Z2Z40A2A2S3bR2A1S3bS4aR6R5R4R3A4A1F_;F_;Fm;Fn;Fa;Fflags;").
Proof.
  intros flags a n m H Hwf. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); [apply model_ivs_wf_vm_add_lazy; assumption|exact Hwf].
Qed.

Lemma model_ivs_wf_with_mmap_replacement : ltac2:(tb__ "0|2|
S4Q40M0A1M1G1G1S22S7S8S5G0R3A2S5G0R2A2A2S9Z2Z40A2A2S3bR2A1S3bS4bR6R5R4R3A4A1F_;F_;Fm;Fn;Fa;Fflags;").
Proof.
  intros flags a n m H Hwf. unfold with_mmap_replacement.
  apply model_ivs_wf_with_mmap_backing; [exact H|].
  apply model_ivs_wf_vm_forget_range; [pose proof (bv_unsigned_in_range 64 n); lia|exact Hwf].
Qed.

Lemma model_ivs_wf_init : ltac2:(tb__ "0|1|
S15S14S4Q40A1M0G0A2A1G0G0G0S0S34S3bS35R6R5R4R3R2R1A6A1Finp;Flim;Fsp;Fmbase;Fbrk0;Freserved;").
Proof. intros. repeat split; intros q Hq; cbn in Hq; contradiction. Qed.

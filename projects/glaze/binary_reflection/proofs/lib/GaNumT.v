(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaPw.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ID_PW : nat := 49.
Definition PWG : Z := Eval vm_compute in (EVT + KFREE).           (* [comment removed for export] *)
Definition PWL : nat := Eval vm_compute in (Z.to_nat (Z.log2 EVT)).   (* [comment removed for export] *)
Definition PWA (i : nat) : Z := 2 ^ (Z.of_nat PWL - Z.of_nat i).  (* [comment removed for export] *)
Definition PWBi (i : nat) : Z := Z.of_nat i * PWG.                (* [comment removed for export] *)
Definition PWBIG : Z := 2 ^ 61.
Definition PWATOM : Z := 2 ^ 44.               (* [comment removed for export] *)
Definition PWNTOP : Z := 2 ^ 33 - 2 ^ 17.      (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PWA0_ok : PWA 0 = EVT /\ PWG <= 2 * PWA 0 /\ 0 <= PWG.
Proof. vm_compute. repeat split; try reflexivity; intros H; discriminate H. Qed.
Lemma PW_fit : PWATOM + PWA 0 * PWNTOP + PWBi PWL <= PWBIG /\ 0 <= PWNTOP /\ PWBi PWL < 2 ^ 40.
Proof. vm_compute. repeat split; try reflexivity; intros H; discriminate H. Qed.

(* [comment removed for export] *)
Definition pwle (i : nat) (C s m : expr) : expr := esub (eaddz (eadd C (escale (PWA i) s)) (PWBi i)) m.
Definition pwL (i : nat) (C s m : expr) : kentry := KRange (pwle i C s m) 0 PWBIG.
(* [comment removed for export] *)
Definition pwF0 (C m : expr) : kentry := KRange (esub m C) 0 PWBIG.
Definition rungs : list nat := seq 0 (S PWL).
Definition pw_ladder (C s m : expr) : list kentry := map (fun i => pwL i C s m) rungs.
Definition pw_facts (C s m : expr) : list kentry := pwF0 C m :: pw_ladder C s m.
(* [comment removed for export] *)
Definition PWAL : Z := Eval vm_compute in (PWA PWL).
Definition PWBL : Z := Eval vm_compute in (PWBi PWL).
Definition pwtop (s : Z) : Z := PWAL * s + PWBL.
Definition pwtop_e (C s : expr) : expr := eaddz (eadd C (escale PWAL s)) PWBL.
Definition pwtop_d (s : expr) : expr := eaddz (escale PWAL s) PWBL.

(* [comment removed for export] *)
Definition no_cbound (C : expr) (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KRange e _ _ => negb (expr_eqb e C) | _ => true end) k.
(* [comment removed for export] *)
Definition pwcost (M M' : expr) : expr := esub (eaddz M PWG) M'.        (* [comment removed for export] *)
Definition pwdbl (Sz N : expr) : expr := esub N (eaddz (escale 2 Sz) 2).                        (* [comment removed for export] *)
Definition pwdbl2 (Sz N : expr) : expr := esub N (escale 2 Sz).                                  (* [comment removed for export] *)
Definition le_big (k : list kentry) (e : expr) (b : Z) : bool := match xhi k e with Some h => Z.leb h b | None => false end.
Definition ge_lit (k : list kentry) (e : expr) (b : Z) : bool := match xlo k e with Some l => Z.leb b l | None => false end.
Definition ge_litB (bc : AX2B.bctx) (e : expr) (b : Z) : bool := match AX2B.xloB bc e with Some l => Z.leb b l | None => false end.
Lemma ge_litB_eqf : forall k, ge_litB (AX2B.mkbc k) = ge_lit k.
Proof. intros k. unfold ge_litB, ge_lit. rewrite AX2B.xloB_eqf. reflexivity. Qed.
Definition le_bigB (bc : AX2B.bctx) (e : expr) (b : Z) : bool := match AX2B.xhiB bc e with Some h => Z.leb h b | None => false end.
Lemma le_bigB_eqf : forall k, le_bigB (AX2B.mkbc k) = le_big k.
Proof. intros k. unfold le_bigB, le_big. rewrite AX2B.xhiB_eqf. reflexivity. Qed.
Definition node_pw (args : list expr) (cs : acs) : option acs :=
  match args with
  | [M; Sz; N; C; ELit mode] =>
      let k := kn cs in let M' := a_meter cs in         (* [comment removed for export] *)
      let lb := le_bigB (AX2B.mkbc k) in                 (* [comment removed for export] *)
      if (lb M PWATOM && lb Sz PWNTOP && lb M' PWATOM && lb N PWNTOP && lb C PWATOM
          && lb (esub M C) PWBIG && forallb (fun i => lb (pwle i C Sz M) PWBIG) rungs
          && (if Z.eqb mode 0 then lb (esub M' M) PWBIG && lb (pwcost M M') PWBIG && lb (pwdbl Sz N) PWBIG
              else if Z.eqb mode 2 then lb (esub M' M) PWBIG && lb (pwcost M M') PWBIG && lb (pwdbl2 Sz N) PWBIG && ge_litB (AX2B.mkbc k) Sz 2
              else expr_eqb M M' && lb (esub N Sz) PWBIG))%bool
      then Some (add_kn cs (pw_facts C N M')) else None
  | _ => None
  end.
Definition XNw (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id ID_PW then node_pw args cs else XN0 id args cs.

(* [comment removed for export] *)
#[local] Notation u := bv_unsigned.
Lemma u_rng : forall w : word, 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.
Lemma unwrap_small : forall (x t : Z), AX2S.eqm x t -> 0 <= x <= 2 ^ 61 -> - 2 ^ 62 < t < 2 ^ 62 -> x = t.
Proof. intros x t [q Hq] Hx Ht. assert (q = 0) by lia. subst q. lia. Qed.
Lemma wrap_small : forall (x t : Z), AX2S.eqm x t -> 0 <= x < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> x = t.
Proof. intros x t [q Hq] Hx Ht. assert (q = 0) by lia. subst q. lia. Qed.

Section Den.
Variable E : env.
Lemma q_eadd : forall a b, AX2S.eqm (u (edenot E (eadd a b))) (u (edenot E a) + u (edenot E b)).
Proof. intros. unfold eadd. rewrite AX2S.mkAlu_denot. apply AX2S.u_add_eqm. Qed.
Lemma q_esub : forall a b, AX2S.eqm (u (edenot E (esub a b))) (u (edenot E a) - u (edenot E b)).
Proof. intros. unfold esub. rewrite AX2S.mkAlu_denot. apply AX2S.u_sub_eqm. Qed.
Lemma u_lit_small : forall z, 0 <= z < 2 ^ 64 -> u (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite AX2S.u_lit64a. apply Z.mod_small. exact Hz. Qed.
Lemma q_eaddz : forall a z, 0 <= z < 2 ^ 64 -> AX2S.eqm (u (edenot E (eaddz a z))) (u (edenot E a) + z).
Proof.
  intros a z Hz. unfold eaddz. rewrite AX2S.mkAlu_denot. pose proof (AX2S.u_add_eqm (edenot E a) (edenot E (ELit z))) as H.
  cbn [edenot] in H. rewrite (u_lit_small z Hz) in H. exact H.
Qed.
Lemma q_escale : forall c a, 0 <= c < 2 ^ 64 -> AX2S.eqm (u (edenot E (escale c a))) (c * u (edenot E a)).
Proof.
  intros c a Hc. unfold escale. rewrite AX2S.mkMd_denot. pose proof (AX2S.u_mul_eqm (edenot E (ELit c)) (edenot E a)) as H.
  cbn [edenot] in H. rewrite (u_lit_small c Hc) in H. exact H.
Qed.
Lemma PWA_rng : forall i, In i rungs -> 1 <= PWA i <= PWA 0.
Proof.
  intros i Hi. apply in_seq in Hi. unfold PWA. split.
  - assert (0 <= Z.of_nat PWL - Z.of_nat i) by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat PWL - Z.of_nat i) ltac:(lia) H). lia.
  - apply Z.pow_le_mono_r; lia.
Qed.
Lemma PWBi_rng : forall i, In i rungs -> 0 <= PWBi i <= PWBi PWL.
Proof. intros i Hi. apply in_seq in Hi. unfold PWBi. pose proof PWA0_ok as (_ & _ & G0). split; [nia|]. apply Z.mul_le_mono_nonneg_r; lia. Qed.
(* [comment removed for export] *)
Lemma pwle_eqm : forall i C s m, In i rungs ->
  AX2S.eqm (u (edenot E (pwle i C s m))) (u (edenot E C) + PWA i * u (edenot E s) + PWBi i - u (edenot E m)).
Proof.
  intros i C s m Hi. pose proof (PWA_rng i Hi) as HA. pose proof (PWBi_rng i Hi) as HB. pose proof PWA0_ok as (E0 & _). pose proof PW_fit as (_ & _ & BL).
  assert (A64 : 0 <= PWA i < 2 ^ 64) by (rewrite E0 in HA; unfold EVT in HA; lia).
  assert (B64 : 0 <= PWBi i < 2 ^ 64) by lia.
  unfold pwle. destruct (q_esub (eaddz (eadd C (escale (PWA i) s)) (PWBi i)) m) as [q1 H1].
  destruct (q_eaddz (eadd C (escale (PWA i) s)) (PWBi i) B64) as [q0 H0].
  destruct (q_eadd C (escale (PWA i) s)) as [q2 H2]. destruct (q_escale (PWA i) s A64) as [q3 H3]. exists (q1 + q0 + q2 + q3). lia.
Qed.
Lemma pwcost_eqm : forall M M', AX2S.eqm (u (edenot E (pwcost M M'))) (u (edenot E M) + PWG - u (edenot E M')).
Proof.
  intros. unfold pwcost. pose proof PWA0_ok as (E0 & G2 & G0).
  destruct (q_esub (eaddz M PWG) M') as [q1 H1]. destruct (q_eaddz M PWG ltac:(rewrite E0 in G2; unfold EVT in G2; lia)) as [q0 H0].
  exists (q1 + q0). lia.
Qed.
Lemma pwdbl_eqm : forall Sz N, AX2S.eqm (u (edenot E (pwdbl Sz N))) (u (edenot E N) - (2 * u (edenot E Sz) + 2)).
Proof.
  intros. unfold pwdbl. destruct (q_esub N (eaddz (escale 2 Sz) 2)) as [q1 H1]. destruct (q_eaddz (escale 2 Sz) 2 ltac:(lia)) as [q0 H0].
  destruct (q_escale 2 Sz ltac:(lia)) as [q3 H3]. exists (q1 - q0 - q3). lia.
Qed.
Lemma pwdbl2_eqm : forall Sz N, AX2S.eqm (u (edenot E (pwdbl2 Sz N))) (u (edenot E N) - 2 * u (edenot E Sz)).
Proof.
  intros. unfold pwdbl2. destruct (q_esub N (escale 2 Sz)) as [q1 H1]. destruct (q_escale 2 Sz ltac:(lia)) as [q3 H3]. exists (q1 - q3). lia.
Qed.
End Den.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pw_grow_top : forall A G C S M N M',
  0 <= S -> 0 <= A -> G <= 2 * A -> 0 <= C + A * S - M -> 0 <= M + G - M' -> 0 <= N - (2 * S + 2) -> 0 <= C + A * N - M'.
Proof. intros A G C S M N M' HS HA HG H0 HC HD. assert (A * (2 * S + 2) <= A * N) by (apply Z.mul_le_mono_nonneg_l; lia). nia. Qed.
(* [comment removed for export] *)
Lemma pw_grow_step : forall A B G C S M N M',
  0 <= S -> 0 <= A -> 0 <= C + (2 * A) * S + (B - G) - M -> 0 <= M + G - M' -> 0 <= N - (2 * S + 2) -> 0 <= C + A * N + B - M'.
Proof. intros A B G C S M N M' HS HA H0 HC HD. assert (A * (2 * S + 2) <= A * N) by (apply Z.mul_le_mono_nonneg_l; lia). nia. Qed.
(* [comment removed for export] *)
Lemma pw_grow_top2 : forall A G C S M N M',
  2 <= S -> 0 <= A -> G <= 2 * A -> 0 <= C + A * S - M -> 0 <= M + G - M' -> 0 <= N - 2 * S -> 0 <= C + A * N - M'.
Proof. intros A G C S M N M' HS HA HG H0 HC HD. assert (A * (2 * S) <= A * N) by (apply Z.mul_le_mono_nonneg_l; lia). assert (A * 2 <= A * S) by (apply Z.mul_le_mono_nonneg_l; lia). nia. Qed.
Lemma pw_grow_step2 : forall A B G C S M N M',
  0 <= S -> 0 <= A -> 0 <= C + (2 * A) * S + (B - G) - M -> 0 <= M + G - M' -> 0 <= N - 2 * S -> 0 <= C + A * N + B - M'.
Proof. intros A B G C S M N M' HS HA H0 HC HD. assert (A * (2 * S) <= A * N) by (apply Z.mul_le_mono_nonneg_l; lia). nia. Qed.
Lemma pw_keep_step : forall A B C S M N, 0 <= A -> 0 <= C + A * S + B - M -> 0 <= N - S -> 0 <= C + A * N + B - M.
Proof. intros A B C S M N HA H0 HD. assert (A * S <= A * N) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.
Lemma PWA_S : forall i, In (S i) rungs -> PWA i = 2 * PWA (S i).
Proof.
  intros i Hi. apply in_seq in Hi. unfold PWA. rewrite Nat2Z.inj_succ.
  replace (Z.of_nat PWL - Z.of_nat i) with (Z.succ (Z.of_nat PWL - Z.succ (Z.of_nat i))) by lia.
  rewrite Z.pow_succ_r; [reflexivity | lia].
Qed.
Lemma PWBi_S : forall i, PWBi (S i) - PWG = PWBi i.
Proof. intros i. unfold PWBi. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma rungs_pred : forall i, In (S i) rungs -> In i rungs.
Proof. intros i Hi. apply in_seq in Hi. apply in_seq. lia. Qed.

Section Sound.
Context {RC : run_ceil}.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable VSHc : list (Z * Z).
Variable AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Variable XN0 : nat -> list expr -> acs -> option acs.

Lemma le_big_sound : forall E MR k e b, know_ok ASEGS E MR k -> le_big k e b = true -> u (edenot E e) <= b.
Proof.
  intros E MR k e b HK H. unfold le_big in H. destruct (xhi k e) as [h|] eqn:Hh; [|discriminate].
  apply Z.leb_le in H. pose proof (AX2S.xhi_sound ASEGS E MR k e h HK Hh). lia.
Qed.

Lemma ge_lit_sound : forall E MR k e b, know_ok ASEGS E MR k -> ge_lit k e b = true -> b <= u (edenot E e).
Proof.
  intros E MR k e b HK H. unfold ge_lit in H. destruct (xlo k e) as [l|] eqn:Hl; [|discriminate].
  apply Z.leb_le in H. pose proof (AX2S.xlo_sound ASEGS E MR k e l HK Hl). lia.
Qed.

Lemma node_pw_ok : forall args cs cs' E MR, know_ok ASEGS E MR (kn cs) -> node_pw args cs = Some cs' ->
  exists K, cs' = add_kn cs K /\ know_ok ASEGS E MR K.
Proof.
  intros args cs cs' E MR HK Hn. unfold node_pw in Hn.
  destruct args as [|M [|Sz [|N [|C [|md rest]]]]]; try discriminate.
  destruct md as [mode| | | | | | |]; try discriminate. destruct rest; [|discriminate].
  cbv zeta in Hn. rewrite le_bigB_eqf, ge_litB_eqf in Hn. remember (a_meter cs) as M' eqn:HM'eq.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-. eexists. split; [reflexivity|].
  apply andb_prop in Hc as [Hc HX]. apply andb_prop in Hc as [Hc HL]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hc HC]. apply andb_prop in Hc as [Hc HN]. apply andb_prop in Hc as [Hc HM'].
  apply andb_prop in Hc as [HM HS].
  pose proof (le_big_sound E MR _ _ _ HK HM) as BM. pose proof (le_big_sound E MR _ _ _ HK HS) as BS.
  pose proof (le_big_sound E MR _ _ _ HK HM') as BM'. pose proof (le_big_sound E MR _ _ _ HK HN) as BN.
  pose proof (le_big_sound E MR _ _ _ HK HC) as BC. pose proof (le_big_sound E MR _ _ _ HK H0) as B0.
  pose proof (u_rng (edenot E (esub M C))) as R0.
  pose proof (u_rng (edenot E M)) as RM. pose proof (u_rng (edenot E Sz)) as RS. pose proof (u_rng (edenot E M')) as RM'.
  pose proof (u_rng (edenot E N)) as RN. pose proof (u_rng (edenot E C)) as RCc.
  pose proof PWA0_ok as (EA0 & G2 & G0). pose proof PW_fit as (FIT & NT0 & BL).
  assert (EV : 0 <= EVT < 2 ^ 40) by (unfold EVT; lia).
  (* [comment removed for export] *)
  assert (RG : forall i, In i rungs -> 0 <= u (edenot E C) + PWA i * u (edenot E Sz) + PWBi i - u (edenot E M)).
  { intros i Hi. pose proof (proj1 (forallb_forall _ _) HL i Hi) as Hl. cbn beta in Hl.
    pose proof (le_big_sound E MR _ _ _ HK Hl) as Bl. pose proof (u_rng (edenot E (pwle i C Sz M))) as Rl.
    pose proof (PWA_rng i Hi) as HA. pose proof (PWBi_rng i Hi) as HB.
    assert (PWA i * u (edenot E Sz) <= PWA 0 * PWNTOP) by (apply Z.mul_le_mono_nonneg; unfold PWNTOP, PWATOM in *; lia).
    rewrite <- (unwrap_small _ _ (pwle_eqm E i C Sz M Hi)); unfold PWBIG, PWATOM, PWNTOP in *; lia. }
  assert (T0 : 0 <= u (edenot E M) - u (edenot E C)).
  { rewrite <- (unwrap_small _ _ (q_esub E M C)); unfold PWBIG, PWATOM in *; lia. }
  (* [comment removed for export] *)
  assert (CONC : 0 <= u (edenot E M') - u (edenot E M) /\ u (edenot E N) <= PWNTOP
                 /\ forall i, In i rungs -> 0 <= u (edenot E C) + PWA i * u (edenot E N) + PWBi i - u (edenot E M')).
  { destruct (Z.eqb mode 0) eqn:Hm.
    - apply andb_prop in HX as [H5 H6]. apply andb_prop in H5 as [H7 H5].
      pose proof (le_big_sound E MR _ _ _ HK H5) as B3. pose proof (le_big_sound E MR _ _ _ HK H6) as B4. pose proof (le_big_sound E MR _ _ _ HK H7) as B7.
      pose proof (u_rng (edenot E (pwcost M M'))) as R3. pose proof (u_rng (edenot E (pwdbl Sz N))) as R4. pose proof (u_rng (edenot E (esub M' M))) as R7.
      assert (Q7 : 0 <= u (edenot E M') - u (edenot E M)) by (rewrite <- (unwrap_small _ _ (q_esub E M' M)); unfold PWBIG, PWATOM in *; lia).
      assert (Q3 : 0 <= u (edenot E M) + PWG - u (edenot E M')) by (rewrite <- (unwrap_small _ _ (pwcost_eqm E M M')); unfold PWBIG, PWATOM in *; rewrite ?EA0 in *; lia).
      assert (Q4 : 0 <= u (edenot E N) - (2 * u (edenot E Sz) + 2)) by (rewrite <- (unwrap_small _ _ (pwdbl_eqm E Sz N)); unfold PWBIG, PWNTOP in *; lia).
      split; [exact Q7|]. split; [unfold PWNTOP in *; lia|].
      intros i Hi. pose proof (PWA_rng i Hi) as HA. destruct i as [|i'].
      + pose proof (RG O Hi) as R00. rewrite EA0 in R00, HA |- *. replace (PWBi 0%nat) with 0 in R00 |- * by reflexivity. rewrite Z.add_0_r in R00 |- *.
        apply (pw_grow_top EVT PWG _ (u (edenot E Sz)) (u (edenot E M))); lia.
      + apply (pw_grow_step (PWA (S i')) (PWBi (S i')) PWG _ (u (edenot E Sz)) (u (edenot E M))); try lia.
        rewrite <- (PWA_S i' Hi), PWBi_S. exact (RG i' (rungs_pred i' Hi)).
    - destruct (Z.eqb mode 2) eqn:Hm2.
      + (* [comment removed for export] *)
        apply andb_prop in HX as [H5 HG]. apply andb_prop in H5 as [H5 H6]. apply andb_prop in H5 as [H7 H5].
        pose proof (le_big_sound E MR _ _ _ HK H5) as B3. pose proof (le_big_sound E MR _ _ _ HK H6) as B4. pose proof (le_big_sound E MR _ _ _ HK H7) as B7.
        pose proof (ge_lit_sound E MR _ _ _ HK HG) as BG.
        pose proof (u_rng (edenot E (pwcost M M'))) as R3. pose proof (u_rng (edenot E (pwdbl2 Sz N))) as R4. pose proof (u_rng (edenot E (esub M' M))) as R7.
        assert (Q7 : 0 <= u (edenot E M') - u (edenot E M)) by (rewrite <- (unwrap_small _ _ (q_esub E M' M)); unfold PWBIG, PWATOM in *; lia).
        assert (Q3 : 0 <= u (edenot E M) + PWG - u (edenot E M')) by (rewrite <- (unwrap_small _ _ (pwcost_eqm E M M')); unfold PWBIG, PWATOM in *; rewrite ?EA0 in *; lia).
        assert (Q4 : 0 <= u (edenot E N) - 2 * u (edenot E Sz)) by (rewrite <- (unwrap_small _ _ (pwdbl2_eqm E Sz N)); unfold PWBIG, PWNTOP in *; lia).
        split; [exact Q7|]. split; [unfold PWNTOP in *; lia|].
        intros i Hi. pose proof (PWA_rng i Hi) as HA. destruct i as [|i'].
        * pose proof (RG O Hi) as R00. rewrite EA0 in R00, HA |- *. replace (PWBi 0%nat) with 0 in R00 |- * by reflexivity. rewrite Z.add_0_r in R00 |- *.
          apply (pw_grow_top2 EVT PWG _ (u (edenot E Sz)) (u (edenot E M))); lia.
        * apply (pw_grow_step2 (PWA (S i')) (PWBi (S i')) PWG _ (u (edenot E Sz)) (u (edenot E M))); try lia.
          rewrite <- (PWA_S i' Hi), PWBi_S. exact (RG i' (rungs_pred i' Hi)).
      + apply andb_prop in HX as [H5 H6]. apply AX2S.expr_eqb_eq in H5. clear HM'eq. subst M'.
        pose proof (le_big_sound E MR _ _ _ HK H6) as B4. pose proof (u_rng (edenot E (esub N Sz))) as R4.
        assert (Q4 : 0 <= u (edenot E N) - u (edenot E Sz)) by (rewrite <- (unwrap_small _ _ (q_esub E N Sz)); unfold PWBIG, PWNTOP in *; lia).
        split; [lia|]. split; [unfold PWNTOP in *; lia|].
        intros i Hi. pose proof (PWA_rng i Hi) as HA. apply (pw_keep_step _ _ _ (u (edenot E Sz))); try lia. exact (RG i Hi). }
  destruct CONC as (Q0 & QN & QR).
  unfold pw_facts, know_ok. apply Forall_cons.
  - unfold pwF0; cbn [kentry_ok]; (split; [apply u_rng|]).
    rewrite (wrap_small _ _ (q_esub E M' C) (u_rng _)) by (unfold PWATOM in *; lia). unfold PWBIG, PWATOM in *. lia.
  - unfold pw_ladder. apply Forall_map. apply Forall_forall. intros i Hi. unfold pwL; cbn [kentry_ok]; (split; [apply u_rng|]).
    pose proof (PWA_rng i Hi) as HA. pose proof (PWBi_rng i Hi) as HB. pose proof (QR i Hi) as Qi.
    assert (PWA i * u (edenot E N) <= PWA 0 * PWNTOP) by (apply Z.mul_le_mono_nonneg; lia).
    rewrite (wrap_small _ _ (pwle_eqm E i C N M' Hi) (u_rng _)) by (unfold PWBIG, PWATOM in *; lia). unfold PWBIG, PWATOM in *. lia.
Qed.

Theorem XNw_sound :
  GPS.ext_stmt ASEGS NXF XN0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ ->
  GPS.ext_stmt ASEGS NXF (XNw XN0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros H0 id args. unfold XNw. destruct (Nat.eqb id ID_PW); [|exact (H0 id args)].
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  destruct (node_pw_ok args cs cs' E _ (co_know HC) Hn) as (K & -> & HKn).
  apply (Hk E fx R M model).
  - split; apply APS.env_agree_refl.
  - unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [exact HKn | exact (co_know HC)].
  - reflexivity.
Qed.
End Sound.
End GaPw.
Module GaFMST.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaPw.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9efec.
Definition RET : Z := 0x9f8d0.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition v : expr := EVar 9.      (* [comment removed for export] *)
Definition c : expr := EVar 10.     (* [comment removed for export] *)
Definition q : expr := EVar 11.     (* [comment removed for export] *)
Definition E : expr := EVar 12.     (* [comment removed for export] *)
Definition I : expr := EVar 31.
Definition dep : expr := EVar 32.
Definition sv : expr := EVar 33.
Definition e_mtr : expr := EVar 34.  Definition e_fb : expr := EVar 35.
Definition FRX : Z := 4352.         (* [comment removed for export] *)
Definition BUFMAX : Z := 2 ^ 26.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LENMAX : Z := 8 * (2 ^ 24 + 2).                  (* [comment removed for export] *)
Definition FMSGROW : Z := Eval vm_compute in (pwtop LENMAX). (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - 2 ^ 33 - FMSGROW.

(* [comment removed for export] *)
Definition fobj (x : expr) (k n : Z) : list kentry :=
  [KRange (eaddz x k) PTRLO (objhi (n + 8)); KDisj (SA x k) (ELit n) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart x k (ELit n); shmap_apart x k (ELit n)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_mem : list kentry :=
  [KWr (SA q 0) (ELit 8);
   KUnk (SA I 0) (esub E I); KWr (SA I 0) (esub E I); KShOk (SA I 0) (esub E I);
   KWr (SA v 0) (ELit 16); KWr (SA v 16) (ELit 24); KUnk (SA v 16) (ELit 24); KWr (SA v 40) (ELit 24); KWr (SA c 0) (ELit 4); KWr (SA c 32) (ELit 4);
   shok v 0 16; shok v 16 24; shok v 40 24; shok c 0 8; shok c 32 8; shok q 0 8; KIMGA]
  ++ RTC ++ GLZ_LOWSH ++ NEWH.
Definition kn_pure : list kentry :=
  [KRange (esub E I) 0 BUFMAX; KRange I PTRLO PTRHI; KRange E PTRLO PTRHI;
   img_apart I 0 (esub E I); shmap_apart I 0 (esub E I);
   KDisj (SA I 0) (esub E I) (SA e_sp (- FRX)) (ELit (FRX + WSTK));      (* [comment removed for export] *)
   KRange dep 0 254; KAlign v 8; KAlign c 8; KAlign q 8]
  ++ fobj v 0 64 ++ fobj v 16 24 ++ fobj v 40 24 ++ fobj c 0 40 ++ fobj q 0 8
  ++ [KDisj (SA v 0) (ELit 64) (SA c 0) (ELit 40); KDisj (SA v 0) (ELit 64) (SA q 0) (ELit 8); KDisj (SA c 0) (ELit 40) (SA q 0) (ELit 8);
      KDisj (SA v 0) (ELit 64) (SA I 0) (esub E I); KDisj (SA c 0) (ELit 40) (SA I 0) (esub E I); KDisj (SA q 0) (ELit 8) (SA I 0) (esub E I);
      KRange e_fb 2 FBMAX].     (* [comment removed for export] *)
Definition kn_common : list kentry := kn_mem ++ kn_pure.
(* [comment removed for export] *)
Definition sp_in : list kentry := [KWr (SA e_sp (- FRX)) (ELit FRX); KAlign e_sp 32; KRange e_sp (CEIL + FRX) HI47;
   KShOk (SA e_sp (- 256)) (ELit 256)].    (* [comment removed for export] *)
Definition kn0 : list kentry :=
  [KWord (SA q 0) 8 I; KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22; KWord (SA c 0) 4 (ELit 0); KWord (SA c 32) 4 dep;
   KRange e_mtr 0 MTRIN] ++ sp_in ++ kn_common.
Definition WS : list (expr * expr) := [(v, ELit 64); (c, ELit 8); (eaddz c 32, ELit 8); (q, ELit 8); (I, esub E I)].   (* [comment removed for export] *)
Definition mkcsF (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcsF ENTRY regsT kn0 NXF [] e_mtr.

Definition P : expr := EVar 36.  Definition SV2 : expr := EVar 37.  Definition ER : expr := EVar 38.  Definition MTR : expr := EVar 39.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered 40.
Definition mtr_out : list kentry := [KRange (esub MTR e_mtr) 0 FMSGROW; KRange MTR 0 (MTRIN + FMSGROW)].
(* [comment removed for export] *)
Definition x_kn_S : list kentry :=
  [KWord (SA q 0) 8 P; KWord (SA v 16) 1 (escale 2 SV2); KRange SV2 0 22; KWord (SA c 0) 4 ER; KWord (SA c 32) 4 dep] ++ mtr_out ++ kn_mem.
Definition toutS : acs := mkcsF RET x_regs x_kn_S 55 [] MTR.
(* [comment removed for export] *)
Definition DL : expr := EVar 55. Definition SL : expr := EVar 56. Definition AL : expr := EVar 57.
Definition strL (d s a : expr) : list kentry :=
  [KWord (SA v 16) 8 (eaddz (escale 8 a) 1); KWord (SA v 24) 8 s; KWord (SA v 32) 8 d;
   KRange a 3 (2^24 + 2); KRange s 0 (2^27 + 16); KRange (esub (escale 8 a) s) 1 (2^27 + 16);   (* [comment removed for export] *)
   KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
   KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA v 16) (ELit 24);
   KDisj (SA d 0) (escale 8 a) (SA v 0) (ELit 64); KDisj (SA d 0) (escale 8 a) (SA c 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA c 32) (ELit 8);   (* [comment removed for export] *)
   KDisj (SA d 0) (escale 8 a) (SA q 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA I 0) (esub E I)].
Definition x_kn_L : list kentry :=
  [KWord (SA q 0) 8 P; KWord (SA c 0) 4 ER; KWord (SA c 32) 4 dep] ++ mtr_out ++ strL DL SL AL ++ kn_mem.
Definition toutL : acs := mkcsF RET x_regs x_kn_L 58 [(DL, escale 8 AL)] MTR.


(* [comment removed for export] *)
Definition BCAP : Z := 2 ^ 28.  Definition CCAP : Z := 8.
Definition ce2 : gcallee2 := GCE2 NXF tin [toutS] [toutL] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.
End GaFMST.
Module GaJT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
Fixpoint jregs (rss : list (list expr)) (i n : nat) (ov : list (nat * expr)) (keep v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' =>
      let col := map (fun rs => nth i rs (ELit 0)) rss in
      match assocn ov i with
      | Some x => x :: jregs rss (Datatypes.S i) n' ov keep v
      | None =>
          match col with
          | e :: r => if (forallb (expr_eqb e) r && expr_vars_lt keep e)%bool then e :: jregs rss (Datatypes.S i) n' ov keep v
                      else EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          | [] => EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          end
      end
  end.
(* [comment removed for export] *)
Definition is_frame_word (fr : Z) (keep : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w x => (expr_eqb b e_sp && Z.leb (- fr) o && Z.ltb o 0) && expr_vars_lt keep x
  | _ => false
  end.
Definition jframe (fr : Z) (ss : list acs) (keep : nat) : list kentry :=
  match ss with
  | [] => []
  | s0 :: r => List.filter (fun K => is_frame_word fr keep K && forallb (fun s => existsb (kentry_eqb K) (kn s)) r)%bool (kn s0)
  end.
Fixpoint maxvar_regs (rs : list expr) (acc : nat) : nat :=
  match rs with [] => acc | EVar i :: r => maxvar_regs r (Nat.max acc (Datatypes.S i)) | _ :: r => maxvar_regs r acc end.


End GaJT.
Module GaPrune.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ID_PRUNE : nat := 47.

Definition no_vars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | _ => false
  end.
Definition saddr_eqb (a b : saddr) : bool := expr_eqb (a_base a) (a_base b) && Z.eqb (a_off a) (a_off b).
(* [comment removed for export] *)
Definition longer (m m' : expr) : bool :=
  match m, m' with
  | ELit z, ELit z' => Z.ltb z z'
  | _, ELit _ => false
  | _, _ => true
  end.

(* [comment removed for export] *)
Definition contained_inB (bc : AX2B.bctx) (A : saddr) (n : expr) (b : expr) (o : Z) (m : expr) (K' : kentry) : bool :=
  match K' with
  | KDisj A' n' (SA b' o') m' =>
      if saddr_eqb A A' then
        if expr_eqb n n' then
          if longer m m' then
            if (if shares_var b b' then true else if no_vars b then no_vars b' else false) then
              if AX2B.xinsideB bc b o m b' o' m' then negb (AX2B.xinsideB bc b' o' m' b o m) else false
            else false
          else false
        else false
      else false
  | _ => false
  end.
Fixpoint lexistsb {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => false | a :: r => if f a then true else lexistsb f r end.


(* [comment removed for export] *)
Definition k1hash (K : kentry) : PrimInt63.int := match K with KDisj A _ _ _ => AzHashK.AHK.sahash A | _ => AzHashK.AHK.hz 0 end.
Definition prunableBH (bc : AX2B.bctx) (kh : list (PrimInt63.int * kentry)) (K : kentry) : bool :=
  match K with
  | KDisj A n (SA b o) m => let hA := AzHashK.AHK.sahash A in
                            lexistsb (fun q => if PrimInt63.eqb (fst q) hA then contained_inB bc A n b o m (snd q) else false) kh
  | _ => false
  end.
(* [comment removed for export] *)
Definition shadow_content_of (fs : list expr) (K : kentry) : bool :=
  match K with
  | KWord (SA (EAlu ALU_SRL f (ELit 3)) _) _ _ | KZero (SA (EAlu ALU_SRL f (ELit 3)) _) _ | KFill (SA (EAlu ALU_SRL f (ELit 3)) _) _ _ =>
      existsb (expr_eqb f) fs
  | _ => false
  end.
Definition node_prune (args : list expr) (cs : acs) : option acs :=
  let k := kn cs in let bc := AX2B.mkbc k in   (* [comment removed for export] *)
  let kh := map (fun K' => (k1hash K', K')) k in   (* [comment removed for export] *)
  Some (set_kn cs (List.filter (fun K => if prunableBH bc kh K then false else negb (shadow_content_of args K)) k)).

(* [comment removed for export] *)
Definition XNp (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id ID_PRUNE then node_prune args cs else XN0 id args cs.

Section Sound.
Context {RC : run_ceil}.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable VSHc : list (Z * Z).
Variable AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Variable XN0 : nat -> list expr -> acs -> option acs.

Theorem XNp_sound :
  GPS.ext_stmt ASEGS NXF XN0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ ->
  GPS.ext_stmt ASEGS NXF (XNp XN0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros H0 id args. unfold XNp. destruct (Nat.eqb id ID_PRUNE); [|exact (H0 id args)].
  intros cs cs' E fx R M model T HT HC _ Hn Hk. unfold node_prune in Hn. injection Hn as <-.
  apply (Hk E fx R M model).
  - split; apply APS.env_agree_refl.
  - apply cs_ok_set_kn; [exact HC|]. apply APS.know_ok_filter. exact (co_know HC).
  - reflexivity.
Qed.
End Sound.
End GaPrune.
Module GaRead.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaPrune.

Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9e6a4.   (* [comment removed for export] *)
Definition ENTRY3 : Z := 0x9eae8.  (* [comment removed for export] *)
Definition RET : Z := 0x9e9a0.
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 267%nat); (ENTRY3, 254%nat)].

Definition NXF : nat := 37.
Definition R : expr := EVar 9. Definition v : expr := EVar 10. Definition BV : expr := EVar 11.
Definition I : expr := EVar 31. Definition E : expr := EVar 32. Definition sv : expr := EVar 33. Definition CAPW : expr := EVar 34.
Definition e_mtr : expr := EVar 35. Definition e_fb : expr := EVar 36.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition FRX : Z := 4672.
Definition BUFMAX : Z := 2 ^ 26.
Definition MTRIN : Z := GaFMST.MTRIN.        (* [comment removed for export] *)
Definition fobj (x : expr) (k n : Z) : list kentry :=
  [KRange (eaddz x k) PTRLO (objhi (n + 8)); KDisj (SA x k) (ELit n) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart x k (ELit n); shmap_apart x k (ELit n)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition robj (x : expr) (n : Z) : list kentry :=
  [KRange x (CEIL + FRX) (HI47 - (n + 8)); KRange (esub x e_sp) 0 (2 ^ 46); img_apart x 0 (ELit n); shmap_apart x 0 (ELit n)].
Definition kn_mem : list kentry :=
  [KWord (SA BV 0) 8 I; KWord (SA BV 8) 8 E; KWord (SA BV 16) 8 CAPW;
   KUnk (SA I 0) (esub E I); KWr (SA I 0) (esub E I); KShOk (SA I 0) (esub E I);
   KWr (SA v 0) (ELit 16); KWr (SA v 16) (ELit 24); KUnk (SA v 16) (ELit 24); KWr (SA v 40) (ELit 24); KWr (SA R 0) (ELit 32); KWr (SA BV 0) (ELit 24);
   shok v 0 16; shok v 16 24; shok v 40 24; shok R 0 32; shok BV 0 24; KIMGA] ++ RTC ++ GLZ_LOWSH ++ NEWH.
Definition kn_pure : list kentry :=
  [KRange (esub E I) 0 BUFMAX; KRange I PTRLO PTRHI; KRange E PTRLO PTRHI;
   img_apart I 0 (esub E I); shmap_apart I 0 (esub E I);
   KDisj (SA I 0) (esub E I) (SA e_sp (- FRX)) (ELit (FRX + WSTK));
   KAlign v 8; KAlign R 8; KAlign BV 8]
  ++ fobj v 0 64 ++ fobj v 16 24 ++ fobj v 40 24 ++ robj R 32 ++ fobj BV 0 24
  ++ [KDisj (SA v 0) (ELit 64) (SA R 0) (ELit 32); KDisj (SA v 0) (ELit 64) (SA BV 0) (ELit 24); KDisj (SA R 0) (ELit 32) (SA BV 0) (ELit 24);
      KDisj (SA v 0) (ELit 64) (SA I 0) (esub E I); KDisj (SA R 0) (ELit 32) (SA I 0) (esub E I); KDisj (SA BV 0) (ELit 24) (SA I 0) (esub E I);
      KRange e_fb 4 FBMAX].     (* [comment removed for export] *)
Definition kn_common : list kentry := kn_mem ++ kn_pure.
Definition sp_in : list kentry := [KWr (SA e_sp (- FRX)) (ELit FRX); KAlign e_sp 32; KRange e_sp (CEIL + FRX) HI47;
   KShOk (SA e_sp (- FRX)) (ELit FRX)].    (* [comment removed for export] *)
Definition kn0 : list kentry := [KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22; KRange e_mtr 0 MTRIN] ++ sp_in ++ kn_common.
Definition WS : list (expr * expr) := [(v, ELit 64); (R, ELit 32); (BV, ELit 24); (I, esub E I)].
Definition tin : acs := mkcs FRX WS e_mtr e_fb ENTRY regsT kn0 NXF.


(* [comment removed for export] *)
Definition BCAP : Z := 2 ^ 28.  Definition CCAP : Z := 8.   (* [comment removed for export] *)
Definition XN : nat -> list expr -> acs -> option acs := XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT0).   (* [comment removed for export] *)
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 101 then Some GaFMST.ce2 else None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2.

(* [comment removed for export] *)
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered 37.
Definition CNT : expr := EVar 52.      (* [comment removed for export] *)
Definition ER : expr := EVar 53.       (* [comment removed for export] *)
Definition MTR : expr := EVar 54.      (* [comment removed for export] *)
Definition resk : list kentry := [KWord (SA R 0) 8 CNT; KWord (SA R 8) 4 ER; KZero (SA R 16) (ELit 16)].   (* [comment removed for export] *)
Definition mtr_out : list kentry := [KRange (esub MTR e_mtr) 0 GaFMST.FMSGROW; KRange MTR 0 (MTRIN + GaFMST.FMSGROW)].
Definition mkcsR (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
(* [comment removed for export] *)
Definition SV2 : expr := EVar 55.
Definition x_kn_S : list kentry := resk ++ [KWord (SA v 16) 1 (escale 2 SV2); KRange SV2 0 22] ++ mtr_out ++ kn_mem.
Definition toutS : acs := mkcsR RET x_regs x_kn_S 56 [] MTR.
(* [comment removed for export] *)
Definition DL : expr := EVar 55. Definition SL : expr := EVar 56. Definition AL : expr := EVar 57.
Definition strL (d s a : expr) : list kentry :=
  [KWord (SA v 16) 8 (eaddz (escale 8 a) 1); KWord (SA v 24) 8 s; KWord (SA v 32) 8 d;
   KRange a 3 (2^24 + 2); KRange s 0 (2^27 + 16); KRange (esub (escale 8 a) s) 1 (2^27 + 16);
   KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
   KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA v 16) (ELit 24);
   KDisj (SA d 0) (escale 8 a) (SA v 0) (ELit 64); KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32);
   KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA I 0) (esub E I)].
Definition x_kn_L : list kentry := resk ++ mtr_out ++ strL DL SL AL ++ kn_mem.
Definition toutL : acs := mkcsR RET x_regs x_kn_L 58 [(DL, escale 8 AL)] MTR.


Definition ce2 : gcallee2 := GCE2 NXF tin [toutS] [toutL] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
Definition F2 : expr := EVar 37.   (* [comment removed for export] *)
Definition F0 : expr := EVar 86.   (* [comment removed for export] *)
Definition REL3 : Z := 0x9ed64.  Definition REL2 : Z := 0x9e90c.   (* [comment removed for export] *)
Definition BUDBR : Z := 0x9ec5c.  Definition ERRBR : Z := 0x9eca0. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMS_ARGS : list expr := [ELit 0; I; ELit 0; sv; e_mtr; eaddz e_fb (-2)].
Definition JOINB : Z := 0x9ec64.   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [REL3] (PExt 51 [] (PRun [REL2] (PExt 51 [] (PRun [] k)))).
Definition after (h : nat) : plan := PRun [ERRBR] (PBranch (PRun [] (PExt 5 [] (fin (PHandoff h)))) (PRun [] (PExt 5 [] (fin (PHandoff h))))).
(* [comment removed for export] *)
Definition DLX : expr := EVar 219.
Definition afterL (h : nat) : plan :=
  PRun [ERRBR] (PBranch (PRun [] (PExt 5 [] (fin (PExt 13 [DLX] (PHandoff h))))) (PRun [] (PExt 5 [] (fin (PExt 13 [DLX] (PHandoff h)))))).
Definition call : plan := PRun [] (PExt 46 [F0; ELit 32; ELit 8] (PExt 47 [F0] (PBump 200 (PExt2 101 FMS_ARGS (PExt 47 [] (after 0)) (PExt 47 [] (afterL 1)))))).
(* [comment removed for export] *)
Definition pre (k : plan) : plan :=
  PRun [] (PExt 50 [ELit 2] (PExt 47 [] (PRun [] (PExt 46 [F2; ELit 32; ELit 88] (PExt 47 [F2] (PExt 6 [] (PRun [] (PExt 6 [] (PRun [] (PExt 50 [ELit 0] (PExt 47 [] k))))))))))).
Definition plan_read : plan :=
  PCase2 (esub E I) 0
    (pre (PRun [] (PExt 5 [] (fin (PExt 46 [I; ELit 0; esub E I] (PHandoff 0))))))      (* [comment removed for export] *)
    (pre (PRun [BUDBR] (PDiamond JOINB [] call))).



End GaRead.
Module GaReadCert.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaRead.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma read_cert :
  check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_read = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma read_gplan : gplan_ok plan_read = true. Proof. vm_compute. reflexivity. Qed.
End GaReadCert.
Module GaReadE.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaPrune GaRead.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RdE.
(* [comment removed for export] *)
Definition NXFE : nat := 34.
Definition svE : expr := EVar 31.  Definition e_mtrE : expr := EVar 32.  Definition e_fbE : expr := EVar 33.
Definition kn_memE : list kentry :=
  [KWord (SA BV 0) 8 (ELit 0); KWord (SA BV 8) 8 (ELit 0); KWord (SA BV 16) 8 (ELit 0);
   KWr (SA v 0) (ELit 16); KWr (SA v 16) (ELit 24); KUnk (SA v 16) (ELit 24); KWr (SA v 40) (ELit 24); KWr (SA R 0) (ELit 32); KWr (SA BV 0) (ELit 24);
   shok v 0 16; shok v 16 24; shok v 40 24; shok R 0 32; shok BV 0 24; KIMGA] ++ RTC ++ GLZ_LOWSH ++ NEWH.
Definition kn_pureE : list kentry :=
  [KAlign v 8; KAlign R 8; KAlign BV 8]
  ++ fobj v 0 64 ++ fobj v 16 24 ++ fobj v 40 24 ++ robj R 32 ++ fobj BV 0 24
  ++ [KDisj (SA v 0) (ELit 64) (SA R 0) (ELit 32); KDisj (SA v 0) (ELit 64) (SA BV 0) (ELit 24); KDisj (SA R 0) (ELit 32) (SA BV 0) (ELit 24);
      KRange e_fbE 2 FBMAX].     (* [comment removed for export] *)
Definition kn0E : list kentry := [KWord (SA v 16) 1 (escale 2 svE); KRange svE 0 22; KRange e_mtrE 0 MTRIN] ++ sp_in ++ kn_memE ++ kn_pureE.
Definition WSE : list (expr * expr) := [(v, ELit 64); (R, ELit 32); (BV, ELit 24)].
Definition tinE : acs := mkcs FRX WSE e_mtrE e_fbE ENTRY regsT kn0E NXFE.
(* [comment removed for export] *)
Definition x_regsE : list expr := sr_havoc regsT clobbered 34.
Definition x_knE : list kentry :=
  [KWord (SA R 0) 8 (ELit 0); KWord (SA R 8) 4 (ELit 12); KZero (SA R 16) (ELit 16); KWord (SA v 16) 1 (escale 2 svE); KRange svE 0 22] ++ kn_memE.
Definition toutE : acs := ACS (mk_ss RET x_regsE x_knE 49) [] 0 FRX 0 [] WSE 0 e_sp FdStd false e_mtrE [] e_fbE.
Definition ceE : gcallee := GCE NXFE tinE [toutE] 0 0.
Definition XNE : nat -> list expr -> acs -> option acs := XNp (XNc ASEGS IT AASAN NXFE GASAN 0 0 CT0).
Definition F2E : expr := EVar 34.   (* [comment removed for export] *)
Definition preE (k : plan) : plan :=
  PRun [] (PExt 50 [ELit 2] (PExt 47 [] (PRun [] (PExt 46 [F2E; ELit 32; ELit 88] (PExt 47 [F2E] (PExt 6 [] (PRun [] (PExt 6 [] (PRun [] (PExt 50 [ELit 0] (PExt 47 [] k))))))))))).
Definition plan_readE : plan := preE (PRun [] (PExt 5 [] (fin (PHandoff 0)))).

End RdE.
Import RdE.
Lemma readE_cert : check ASEGS IT AASAN NXFE LIMIT ISP0 XNE XE0 XB0 (HSce ceE) 0%nat BFUEL FUEL None (ce_tin ceE) plan_readE = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma readE_gplan : gplan_ok plan_readE = true. Proof. vm_compute. reflexivity. Qed.
End GaReadE.
Module GaVecT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ANNOT : Z := 0x70554.       (* [comment removed for export] *)
Definition SZHI : Z := 2 ^ 26 - 1.

Module Ctor.
Definition ENTRY : Z := 0x9dac8.
Definition RETPC : Z := 0x9db30.
Definition NXF : nat := 33.
Definition V : expr := EVar 9.  Definition FIRST : expr := EVar 10.  Definition SZ : expr := EVar 12.
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition regsT : list expr := sr_upd (sr_upd regs0 4 (ELit (g_tp GASAN))) 12 (eadd FIRST SZ).
Definition FRS : Z := 64 + 32 + MSTK_N.      (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - kcost (SZHI + 1).
Definition vobj : list kentry :=
  [ KRange V PTRLO (objhi 32); KAlign V 8; KWr (SA V 0) (ELit 24); shok V 0 24;
    KDisj (SA V 0) (ELit 24) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart V 0 (ELit 24); shmap_apart V 0 (ELit 24) ].
Definition payload : list kentry :=
  [ KRange SZ 1 SZHI; KRange FIRST PTRLO (PTRHI - 1); KRange (eadd FIRST SZ) (PTRLO + 1) PTRHI; KAlign FIRST 16;
    KWr (SA FIRST 0) SZ; KUnk (SA FIRST 0) SZ; KShOk (SA FIRST 0) SZ;
    KDisj (SA FIRST 0) SZ (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart FIRST 0 SZ; shmap_apart FIRST 0 SZ;
    KDisj (SA FIRST 0) SZ (SA V 0) (ELit 24) ].
Definition stk_facts : list kentry := [ KAlign e_sp 16; KRange e_sp (CEIL + FRS) HI47; KWr (SA e_sp (- FRS)) (ELit FRS) ].
(* [comment removed for export] *)
Definition kn_fixed : list kentry := vobj ++ payload ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.
Definition kn_in : list kentry := kn_fixed ++ stk_facts ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fb; KRange e_mtr 0 MTRIN ].
Definition WS : list (expr * expr) := [(V, ELit 24)].
Definition mkcsV (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcsV [(FIRST, SZ)] e_mtr ENTRY regsT kn_in NXF.
(* [comment removed for export] *)
Definition P : expr := EVar 33.
Definition XLO : nat := 34.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc (sr_upd regs0 4 (ELit (g_tp GASAN))) clobbered XLO.
Definition blkP (p n : expr) : list kentry :=
  [ KRange p PTRLO (PTRHI - 1); KRange (eadd n p) (PTRLO + 1) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n; KShOk (SA p 0) n;
    KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n; shmap_apart p 0 n;
    KDisj (SA p 0) n (SA FIRST 0) SZ; KDisj (SA p 0) n (SA V 0) (ELit 24) ].
Definition kn_out : list kentry :=
  [ KWord (SA V 0) 8 P; KWord (SA V 8) 8 (eadd SZ P); KWord (SA V 16) 8 (eadd SZ P) ] ++ blkP P SZ ++ kn_fixed.
Definition MTRX : expr := eaddz e_mtr EVT.      (* [comment removed for export] *)
Definition tout : acs := mkcsV [(P, SZ); (FIRST, SZ)] MTRX RETPC regs_out kn_out (XLO + 15)%nat.
Definition BCAP : Z := 3 * 2 ^ 26.   (* [comment removed for export] *)
Definition CCAP : Z := 2.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End Ctor.

(* [comment removed for export] *)
Module Push.
Definition ENTRY : Z := 0x9d9c4.
Definition RETPC : Z := 0x9da8c.
Definition NXF : nat := 35.
Definition V : expr := EVar 9.  Definition C : expr := EVar 10.
Definition D : expr := EVar 31.  Definition SZ : expr := EVar 32.
Definition e_mtr : expr := EVar 33.  Definition e_fb : expr := EVar 34.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition FRS : Z := 48 + 112 + MSTK_N.      (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - kcost (2 * SZHI + 2) - KFREE.
Definition vobj : list kentry :=
  [ KRange V PTRLO (objhi 32); KAlign V 8; KWr (SA V 0) (ELit 24); shok V 0 24;
    KDisj (SA V 0) (ELit 24) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart V 0 (ELit 24); shmap_apart V 0 (ELit 24) ].
(* [comment removed for export] *)
Definition cobj : list kentry :=
  [ KRange C (CEIL + FRS) (HI47 - 8); KUnk (SA C 0) (ELit 1); shok C 0 1; KDisj (SA C 0) (ELit 1) (SA V 0) (ELit 24);
    KDisj (SA C 0) (ELit 1) (SA e_sp (- FRS)) (ELit FRS) ].
Definition blk (p n : expr) : list kentry :=
  [ KRange p PTRLO (PTRHI - 1); KRange (eadd n p) (PTRLO + 1) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n; KShOk (SA p 0) n;
    KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n; shmap_apart p 0 n;
    KDisj (SA p 0) n (SA V 0) (ELit 24) ].
Definition stk_facts : list kentry := [ KAlign e_sp 16; KRange e_sp (CEIL + FRS) HI47; KWr (SA e_sp (- FRS)) (ELit FRS) ].
Definition SZLO : Z := 1.      (* [comment removed for export] *)
Definition kn_fixed : list kentry := vobj ++ [KRange SZ SZLO SZHI] ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_in : list kentry :=
  [ KWord (SA V 0) 8 D; KWord (SA V 8) 8 (eadd SZ D); KWord (SA V 16) 8 (eadd SZ D) ] ++ blk D SZ ++ kn_fixed ++ cobj ++ stk_facts
  ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fb; KRange e_mtr 0 MTRIN ].
Definition WS : list (expr * expr) := [(V, ELit 24); (C, ELit 1)].
Definition mkcsV (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcsV [(D, SZ)] e_mtr ENTRY regsT kn_in NXF.
(* [comment removed for export] *)
Definition P2 : expr := EVar 35.
Definition XLO : nat := 36.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsT clobbered XLO.
Definition CAP2 : expr := escale 2 SZ.
Definition blk2 (p : expr) (cap used : expr) (nlo : Z) : list kentry :=
  [ KRange p PTRLO (PTRHI - nlo); KRange (eadd cap p) (PTRLO + nlo) PTRHI; KAlign p 16; KWr (SA p 0) cap; KUnk (SA p 0) cap; KShOk (SA p 0) used;
    KDisj (SA p 0) cap (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 cap; shmap_apart p 0 cap;
    KDisj (SA p 0) cap (SA V 0) (ELit 24) ].
Definition kn_out : list kentry :=
  [ KWord (SA V 0) 8 P2; KWord (SA V 8) 8 (eaddz (eadd SZ P2) 1); KWord (SA V 16) 8 (eadd CAP2 P2) ] ++ blk2 P2 CAP2 (eaddz SZ 1) 2
  ++ [ KRange (eaddz (eadd SZ P2) 1) (PTRLO + 2) PTRHI ]      (* [comment removed for export] *)
  ++ kn_fixed.
Definition MTRX : expr := eaddz e_mtr (EVT + KFREE).      (* [comment removed for export] *)
Definition tout : acs := mkcsV [(P2, CAP2)] MTRX RETPC regs_out kn_out (XLO + 15)%nat.
(* [comment removed for export] *)
Definition kn_out1 : list kentry :=
  [ KWord (SA V 0) 8 P2; KWord (SA V 8) 8 (eaddz P2 2); KWord (SA V 16) 8 (eaddz P2 2) ] ++ blk2 P2 (ELit 2) (ELit 2) 2 ++ [KRange SZ 1 1] ++ kn_fixed.
Definition tout1 : acs := mkcsV [(P2, ELit 2)] (eaddz e_mtr (EVT + KFREE)) RETPC regs_out kn_out1 (XLO + 15)%nat.
Definition BCAP : Z := 4 * 2 ^ 26.  Definition CCAP : Z := 2.
Definition ce2 : gcallee2 := GCE2 NXF tin [tout] [tout1] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
Definition NXFE : nat := 33.
Definition e_mtrE : expr := EVar 31.  Definition e_fbE : expr := EVar 32.
Definition kn_fixedE : list kentry := vobj ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.
Definition kn_inE : list kentry :=
  [ KWord (SA V 0) 8 (ELit 0); KWord (SA V 8) 8 (ELit 0); KWord (SA V 16) 8 (ELit 0) ] ++ kn_fixedE ++ cobj ++ stk_facts
  ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fbE; KRange e_mtrE 0 MTRIN ].
Definition mkcsE (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fbE.
Definition tinE : acs := mkcsE [] e_mtrE ENTRY regsT kn_inE NXFE.
Definition P2E : expr := EVar 33.
Definition regs_outE : list expr := sr_havoc regsT clobbered 34.
Definition kn_outE : list kentry :=
  [ KWord (SA V 0) 8 P2E; KWord (SA V 8) 8 (eaddz P2E 1); KWord (SA V 16) 8 (eaddz P2E 1) ] ++ blk2 P2E (ELit 1) (ELit 1) 1 ++ kn_fixedE.
Definition toutE : acs := mkcsE [(P2E, ELit 1)] (eaddz e_mtrE EVT) RETPC regs_outE kn_outE 49.
Definition BCAPE : Z := 2 ^ 21.
Definition ceE : gcallee := GCE NXFE tinE [toutE] BCAPE 1.
End Push.
End GaVecT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT GaPw.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BNU : Z := 0xaa248.    (* [comment removed for export] *)
Definition BNI : Z := 0xb510c.    (* [comment removed for export] *)
Definition is_int (B : Z) : bool := Z.eqb B BNI.
Definition NINSTR (B : Z) : nat := if is_int B then 1384%nat else 1382%nat.
(* [comment removed for export] *)
Definition IT_def (B : Z) : itab := mk_itab_ranges ASEGS [(B, NINSTR B)].
Definition IT_U : itab := Eval vm_compute in IT_def BNU.
Definition IT_I : itab := Eval vm_compute in IT_def BNI.
Lemma IT_U_eq : IT_U = IT_def BNU. Proof. vm_cast_no_check (@eq_refl itab (IT_def BNU)). Qed.
Lemma IT_I_eq : IT_I = IT_def BNI. Proof. vm_cast_no_check (@eq_refl itab (IT_def BNI)). Qed.
Definition IT (B : Z) : itab := if Z.eqb B BNU then IT_U else if Z.eqb B BNI then IT_I else IT_def B.
Lemma IT_eq : forall B, IT B = IT_def B.
Proof.
  intro B. unfold IT. destruct (Z.eqb_spec B BNU) as [->|_]; [exact IT_U_eq|]. destruct (Z.eqb_spec B BNI) as [->|_]; [exact IT_I_eq | reflexivity].
Qed.
Lemma IT_ok : forall B, itab_sound ASEGS (IT B). Proof. intro. rewrite IT_eq. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition at_ (B off : Z) : Z := B + off + (if (is_int B && Z.ltb 0x600 off)%bool then 4 else 0).
Definition RETPC (B : Z) : Z := at_ B 0xe34.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).   (* [comment removed for export] *)
Definition TP : expr := EVar 9.    Definition G : expr := EVar 10.    Definition PIT : expr := EVar 11.
Definition PEND : expr := EVar 12. Definition OBJ : expr := EVar 13.  Definition PIX : expr := EVar 14.
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition REM : expr := EVar 32.  Definition IX : expr := EVar 33.
Definition D : expr := EVar 34.    Definition S : expr := EVar 35.    Definition A : expr := EVar 36.   (* [comment removed for export] *)
Definition ERR : expr := EVar 37.
Definition INLO : expr := EVar 38.      (* [comment removed for export] *)
Definition TAGV : expr := EVar 39.
Definition e_mtr : expr := EVar 40.     (* [comment removed for export] *)
Definition e_fb : expr := EVar 41.      (* [comment removed for export] *)
Definition NXF : nat := 42.
Definition IT0 : expr := eadd INLO ITO. (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition CAPHI : Z := 4 * IXHI + 8 * INSZ + CAPK.
Definition AHI : Z := CAPHI / 8.
Definition two62 : Z := 2 ^ 62.
Definition FR : Z := 176.
Definition FRK : Z := FR + 3760.        (* [comment removed for export] *)
Definition flo (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NBW : Z := 3 * 2^30 + 16.       (* [comment removed for export] *)
Definition NBN : Z := 3 * 2^30 + 80.       (* [comment removed for export] *)
Definition GEV : Z := 2 * EVT + 8.
Definition MTRJ : Z := MTRMAX NBW.
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop (8 * AHI).   (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.

(* [comment removed for export] *)
Definition szin (m0 : smode) : expr := match m0 with MS => EVar 34 | ML => S end.

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);                 (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    flo d (escale 8 a); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition TAGSZ (B : Z) : Z := if is_int B then 4 else 1.
(* [comment removed for export] *)
Definition tp_facts (B : Z) : list kentry :=
  [ KRange TP (CEIL + FRK) (HI47 - 8); KRange (esub TP e_sp) 0 (2 ^ 46); KShOk (SA TP 0) (ELit (TAGSZ B)); img_apart TP 0 (ELit (TAGSZ B));
    KDisj (SA TP 0) (ELit (TAGSZ B)) (SA OBJ 0) (ELit 24); KDisj (SA TP 0) (ELit (TAGSZ B)) (SA G 0) (ELit 4);
    KDisj (SA TP 0) (ELit (TAGSZ B)) (SA PIT 0) (ELit 8); KDisj (SA TP 0) (ELit (TAGSZ B)) (SA PIX 0) (ELit 8) ].
Definition kn_fixed : list kentry :=
  [ KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 4;
    KRange PEND PTRLO (objhi 8); KWord (SA PEND 0) 8 (eadd IT0 REM); KShOk (SA PEND 0) (ELit 8); KAlign PEND 8;
    KRange PIT PTRLO (objhi 8); KWr (SA PIT 0) (ELit 8); KShOk (SA PIT 0) (ELit 8); KAlign PIT 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8; KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KShOk (SA INLO 0) BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
    KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 4); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIX 0) (ELit 8);
    KAlign e_sp 16; KRange e_sp (CEIL + 4352) (two47 - 16); KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange e_mtr 0 MTRIN; KRange CPW 0 CMAX;
    flo G (ELit 4); flo PEND (ELit 8); flo PIT (ELit 8); flo PIX (ELit 8); flo OBJ (ELit 24); flo INLO BLEN;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart PIT 0 (ELit 8); shmap_apart PIT 0 (ELit 8);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PEND 0 (ELit 8); img_apart INLO 0 BLEN; shmap_apart INLO 0 BLEN;
    KIMGA; fb_fact e_fb ] ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk_shok : kentry := KShOk (SA e_sp (- FRK)) (ELit FRK).
Definition kn_in (m : smode) (B : Z) : list kentry :=
  [ KWord (SA TP 0) (if is_int B then 4%nat else 1%nat) TAGV; KRange TAGV 0 255;
    KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG; stk_shok ]
  ++ pw_facts CPW (szin m) e_mtr ++ str m IX IT0 34 ++ tp_facts B ++ kn_fixed.
Definition WS : list (expr * expr) := [(G, ELit 4); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition regs_in : list expr := regsW.
Definition tin (m : smode) (B : Z) : acs := mkcsV B regs_in (kn_in m B) NXF (vis m 34) e_mtr.

(* [comment removed for export] *)
Definition xERR := EVar 42. Definition xDI := EVar 43. Definition xIX := EVar 44.
 Definition xS := EVar 46.

Definition xMTR := EVar 48.
Definition XLO : nat := 49.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szx (m : smode) : expr := match m with MS => EVar 45 | ML => xS end.   (* [comment removed for export] *)
Definition kn_out (m0 m : smode) (B : Z) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA PIT 0) 8 (eadd IT0 xDI); KRange xDI 0 8; KRange (esub REM xDI) 0 REMHI;
    KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 two62;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ ;
    relx xDI xERR xIX IX 8                                                            (* [comment removed for export] *)
    ] ++ pw_facts CPW (szx m) xMTR ++ [                       (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ ]
  ++ str m xIX (eadd IT0 xDI) 45 ++ no_cbound CPW kn_fixed.
(* [comment removed for export] *)
Definition tout (m0 m : smode) (B : Z) : acs := mkcsV (RETPC B) regs_out (kn_out m0 m B) (XLO + 15)%nat (vis m 45) xMTR.
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout m MS B] [tout m ML B] BCAP CCAP.
Definition ce (m : smode) (B : Z) : gcallee := c2_merged (ce2 m B).
(* [comment removed for export] *)
Definition ceL1 (B : Z) : gcallee := GCE NXF (tin ML B) [tout ML ML B; tout ML ML B] BCAP CCAP.

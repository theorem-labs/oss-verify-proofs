(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepSound VStepMemSound VParamsCheck VCert VItab VDriverMatch VContract VDriver VSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint cover (fuel : nat) (cls : list (Z * Z)) (cur hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if Z.leb hi cur then true else
      match find (fun c : Z * Z => Z.leb (fst c) cur && Z.leb cur (snd c)) cls with
      | Some c => cover f cls (snd c + 1) hi
      | None => false
      end
  end.

Lemma cover_sound : forall fuel cls cur hi,
  cover fuel cls cur hi = true ->
  forall n, cur <= n < hi -> exists c, In c cls /\ fst c <= n <= snd c.
Proof.
  induction fuel as [|f IH]; simpl; intros cls cur hi H n Hn; [discriminate|].
  destruct (Z.leb_spec hi cur); [lia|].
  destruct (find (fun c : Z * Z => Z.leb (fst c) cur && Z.leb cur (snd c)) cls) as [c|] eqn:F; [|discriminate].
  apply find_some in F as [Hin Hc]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (Z.leb_spec n (snd c)).
  - exists c. split; [exact Hin|lia].
  - eapply IH; [exact H|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition root_reg (FP : FParams) (k : Z) : option lin :=
  if Z.eqb k 1 then Some (lconst (fp_ret FP))
  else if Z.eqb k 2 then Some (lsym SP0)
  else if Z.eqb k 3 then Some (lsym GP)
  else if Z.eqb k 4 then Some (lconst (fp_tp FP))
  else if Z.eqb k 10 then Some (lsym DATA)
  else if Z.eqb k 11 then Some (lsym SIZE)
  else match find (fun p : Z * Z => Z.eqb (fst p) k) sreg_idx with
       | Some p => Some (lsym (SREG (snd p)))
       | None => None
       end.

Fixpoint zseq (a : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => a :: zseq (a + 1) n' end.

Lemma zseq_in a n k : a <= k < a + Z.of_nat n -> In k (zseq a n).
Proof.
  revert a. induction n as [|n IH]; simpl; intros a H; [lia|].
  destruct (Z.eq_dec a k); [left; lia|right]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition root_regs_ok (FP : FParams) (m : pmap lin) : bool :=
  forallb (fun k => match pm_get (reg_key k) m with
                    | None => true
                    | Some e => match root_reg FP k with
                                | Some e' => lin_eqb e e'
                                | None => false
                                end
                    end) (zseq 1 31).

(* [comment removed for export] *)
Definition canon_store (cls : Z * Z) : store :=
  mkStore (pm_of_list [(SP0, (Some F_SPLO, Some F_SPHI));
                       (DATA, (Some 1, Some (2 ^ 63 - 1 - fst cls)));
                       (SIZE, (Some (fst cls), Some (snd cls)))])
          [lsub (ladd (lsym DATA) (lsym SIZE)) (lconst (2 ^ 63 - 1))]
          (pm_of_list [(SP0, (16, 0))]).

Definition is_nilb {A : Type} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Definition root_pre_ok (FP : FParams) (cls : Z * Z) (cs : cstate) : bool :=
  cstate_wf cs
  && root_regs_ok FP (vs_regs (load_cstate cs 0 []))
  && is_nilb (cs_slots cs) && is_nilb (cs_globs cs) && is_nilb (cs_nul cs)
  && is_nilb (cs_valset cs) && is_nilb (cs_conddef cs) && is_nilb (cs_moddef cs)
  && store_le (canon_store cls) (store_of cs).

(* [comment removed for export] *)
Definition root_exit_ok (cs : cstate) : bool :=
  match pm_get (reg_key 10) (vs_regs (load_cstate cs 0 [])) with
  | Some e => lin_eqb e (lconst 0)
  | None => false
  end.

Definition root_ok (FP : FParams) (U : vunit) : bool :=
  match u_root U with
  | None => false          (* [comment removed for export] *)
  | Some r =>
  Z.eqb r (fp_ret FP)
  && Z.eqb (u_entry U) (fp_entry FP)
  && Z.eqb (u_sp U) 0
  && is_nilb (u_wstack U)
  && forallb (fun c : Z * Z => Z.eqb (fst c) (fp_prng FP) && Z.eqb (snd c) 8) (u_wglobs U)
  && Z.leb (fst (u_sclass U)) (snd (u_sclass U))
  && root_pre_ok FP (u_sclass U) (u_pre U)
  && forallb root_exit_ok (u_exits U)
  end.

Definition roots (FP : FParams) (C : vcert) : list vunit := List.filter (root_ok FP) C.

Definition roots_ok (FP : FParams) (C : vcert) : bool :=
  cover (S (length C)) (map u_sclass (roots FP C)) 0 (fp_nmax FP).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition covered (l : list (Z * Z)) (r : Z * Z) : bool :=
  existsb (fun c : Z * Z => Z.leb (fst c) (fst r) && Z.leb (snd r) (snd c)) l.

Definition fp_genv_ok (P0 : vparams) (tp errno : Z) (FP : FParams) : bool :=
  Z.eqb (vp_frame P0) (fp_frame FP)
  && Z.eqb tp (fp_tp FP)
  && Z.eqb errno (fp_errno FP)
  && (match vp_fcells P0 with
      | [(a, wa); (b, wb)] => Z.eqb a (fp_prng FP) && Z.eqb wa 8 && Z.eqb b (fp_errno FP) && Z.eqb wb 4
      | _ => false
      end)
  && Z.leb (fp_nmax FP) (vp_nmax P0)
  && Z.leb (vp_splo P0) F_SPLO && Z.leb F_SPHI (vp_sphi P0)
  && Z.leb (vp_frame P0) F_SPLO && Z.leb 0 (vp_frame P0)
  && forallb (covered [(fp_ro_lo FP, fp_ro_hi FP); (fp_gotgrd FP, fp_gotgrd FP + 8); (fp_mcount FP, fp_mcount FP + 8)])
             (vp_pristine P0)
  && Z.leb 0 (fp_ro_lo FP) && Z.leb (fp_ro_hi FP) (2 ^ 64)
  && Z.leb 0 (fp_gotgrd FP) && Z.leb (fp_gotgrd FP + 8) (2 ^ 64)
  && Z.leb 0 (fp_mcount FP) && Z.leb (fp_mcount FP + 8) (2 ^ 64)
  && Z.eqb (fp_ret FP mod 2) 0 && Z.leb 0 (fp_ret FP) && Z.ltb (fp_ret FP) (2 ^ 64)
  && Z.leb 0 (fp_tp FP) && Z.ltb (fp_tp FP) (2 ^ 64)
  && Z.leb 0 (fp_prng FP) && Z.ltb (fp_prng FP) (2 ^ 64)
  && Z.leb 0 (fp_errno FP) && Z.ltb (fp_errno FP) (2 ^ 64).

Definition fp_genv_prop (P0 : vparams) (tp errno : Z) (FP : FParams) : Prop :=
  vp_frame P0 = fp_frame FP
  /\ tp = fp_tp FP
  /\ errno = fp_errno FP
  /\ vp_fcells P0 = [(fp_prng FP, 8); (fp_errno FP, 4)]
  /\ fp_nmax FP <= vp_nmax P0
  /\ vp_splo P0 <= F_SPLO /\ F_SPHI <= vp_sphi P0
  /\ vp_frame P0 <= F_SPLO /\ 0 <= vp_frame P0
  /\ (forall r, In r (vp_pristine P0) ->
        covered [(fp_ro_lo FP, fp_ro_hi FP); (fp_gotgrd FP, fp_gotgrd FP + 8); (fp_mcount FP, fp_mcount FP + 8)] r = true)
  /\ 0 <= fp_ro_lo FP /\ fp_ro_hi FP <= 2 ^ 64
  /\ 0 <= fp_gotgrd FP /\ fp_gotgrd FP + 8 <= 2 ^ 64
  /\ 0 <= fp_mcount FP /\ fp_mcount FP + 8 <= 2 ^ 64
  /\ fp_ret FP mod 2 = 0 /\ 0 <= fp_ret FP < 2 ^ 64
  /\ 0 <= fp_tp FP < 2 ^ 64
  /\ 0 <= fp_prng FP < 2 ^ 64
  /\ 0 <= fp_errno FP < 2 ^ 64.

Local Ltac bsplit H :=
  repeat match type of H with
         | (_ && _) = true => apply andb_prop in H; destruct H as [H ?]
         end.

Lemma fp_genv_ok_sound P0 tp errno FP :
  fp_genv_ok P0 tp errno FP = true -> fp_genv_prop P0 tp errno FP.
Proof.
  unfold fp_genv_ok, fp_genv_prop. intros H. bsplit H.
  destruct (vp_fcells P0) as [|[a wa] [|[b wb] [|]]]; try discriminate.
  repeat match goal with
         | K : (_ && _) = true |- _ => apply andb_prop in K as [K ?]
         end.
  repeat match goal with
         | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
         | K : Z.leb _ _ = true |- _ => apply Z.leb_le in K
         | K : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in K
         | K : forallb _ _ = true |- _ => rewrite forallb_forall in K
         end.
  subst. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv5_of_Z (r : reg) k : bv_unsigned r = k -> r = Z_to_bv 5 k.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma reg_range (r : reg) : 0 <= bv_unsigned r < 32.
Proof. pose proof (bv_unsigned_in_range 5 r) as H. unfold bv_modulus in H. simpl in H. lia. Qed.

Lemma word_eq_u (a b : word) : bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros H. apply bv_eq. exact H. Qed.

Lemma u_word_lt (a : word) : 0 <= bv_unsigned a < 2 ^ 64.
Proof. apply u64_range. Qed.

(* [comment removed for export] *)
Definition rootE (FP : FParams) (regs : bvmap 5 word) (sp data : word) (n : Z) : venv :=
  mkEnv (bv_unsigned sp) (bv_unsigned data) n (fp_ret FP) (fp_tp FP) (bv_unsigned (getr regs (Z_to_bv 5 3)))
        (map (fun p : Z * Z => bv_unsigned (getr regs (Z_to_bv 5 (fst p)))) sreg_idx).

Definition rootnu (E : venv) : val :=
  fun s => match fix_val E s with Some z => z | None => 0 end.

Lemma rootnu_fix E : gamma_fix E (rootnu E).
Proof. intros s z H. unfold rootnu. now rewrite H. Qed.

Lemma rootnu_SP0 E : rootnu E SP0 = e_sp0 E.   Proof. reflexivity. Qed.
Lemma rootnu_DATA E : rootnu E DATA = e_data E. Proof. reflexivity. Qed.
Lemma rootnu_SIZE E : rootnu E SIZE = e_size E. Proof. reflexivity. Qed.
Lemma rootnu_GP E : rootnu E GP = e_gp E.      Proof. reflexivity. Qed.

Lemma rootnu_SREG FP regs sp data n r i :
  In (r, i) sreg_idx ->
  rootnu (rootE FP regs sp data n) (SREG i) = bv_unsigned (getr regs (Z_to_bv 5 r)).
Proof.
  unfold sreg_idx. intros H. simpl in H.
  repeat (destruct H as [H|H]; [inversion H; subst; reflexivity|]). destruct H.
Qed.

(* [comment removed for export] *)
Lemma canon_store_sat cls nu :
  F_SPLO <= nu SP0 <= F_SPHI -> nu SP0 mod 16 = 0 ->
  1 <= nu DATA -> nu DATA + nu SIZE < 2 ^ 63 ->
  fst cls <= nu SIZE <= snd cls ->
  sat nu (canon_store cls).
Proof.
  intros Hsp Hal Hd Hds Hn. unfold canon_store. split; [|split].
  - intros s i Hg. apply pm_of_list_get_in in Hg. simpl in Hg.
    destruct Hg as [Hg|[Hg|[Hg|[]]]]; inversion Hg; subst; split; simpl; lia.
  - constructor; [|constructor]. rewrite eval_lsub, eval_ladd, !eval_lsym, eval_lconst. lia.
  - intros s m r Hg. apply pm_of_list_get_in in Hg. simpl in Hg.
    destruct Hg as [Hg|[]]. inversion Hg; subst. exists (nu SP0 / 16). lia.
Qed.

Lemma root_regs_sound FP cs regs sp data n pc ctx :
  root_regs_ok FP (vs_regs (load_cstate cs 0 [])) = true ->
  getr regs (Z_to_bv 5 1) = Z_to_bv 64 (fp_ret FP) ->
  getr regs (Z_to_bv 5 2) = sp ->
  getr regs (Z_to_bv 5 4) = Z_to_bv 64 (fp_tp FP) ->
  getr regs (Z_to_bv 5 10) = data ->
  getr regs (Z_to_bv 5 11) = Z_to_bv 64 n ->
  gamma_regs (rootnu (rootE FP regs sp data n)) (load_cstate cs pc ctx) regs.
Proof.
  intros H H1 H2 H4 H10 H11 r e Hr0 Hget.
  change (vs_regs (load_cstate cs pc ctx)) with (vs_regs (load_cstate cs 0 [])) in Hget.
  unfold root_regs_ok in H. rewrite forallb_forall in H.
  remember (bv_unsigned r) as k eqn:Hk.
  assert (Hin : In k (zseq 1 31)) by (apply zseq_in; pose proof (reg_range r); simpl; lia).
  specialize (H k Hin). cbn beta in H. rewrite Hget in H.
  destruct (root_reg FP k) as [l|] eqn:R; [|discriminate]. apply lin_eqb_eq in H. subst e.
  rewrite (bv5_of_Z r k (eq_sym Hk)). clear Hr0 Hk Hget Hin.
  unfold root_reg in R.
  destruct (Z.eqb_spec k 1).
  { injection R as <-. subst k. rewrite eval_lconst, H1. apply u_Z_to_bv64. }
  destruct (Z.eqb_spec k 2).
  { injection R as <-. subst k. rewrite eval_lsym, rootnu_SP0, H2. cbn [e_sp0 rootE]. symmetry; apply zwrap64_u. }
  destruct (Z.eqb_spec k 3).
  { injection R as <-. subst k. rewrite eval_lsym, rootnu_GP. cbn [e_gp rootE]. symmetry; apply zwrap64_u. }
  destruct (Z.eqb_spec k 4).
  { injection R as <-. subst k. rewrite eval_lconst, H4. apply u_Z_to_bv64. }
  destruct (Z.eqb_spec k 10).
  { injection R as <-. subst k. rewrite eval_lsym, rootnu_DATA, H10. cbn [e_data rootE]. symmetry; apply zwrap64_u. }
  destruct (Z.eqb_spec k 11).
  { injection R as <-. subst k. rewrite eval_lsym, rootnu_SIZE, H11. cbn [e_size rootE]. apply u_Z_to_bv64. }
  destruct (find (fun p : Z * Z => Z.eqb (fst p) k) sreg_idx) as [[r' i]|] eqn:F; [|discriminate].
  apply find_some in F as [Fin Fk]. simpl in Fk. apply Z.eqb_eq in Fk. subst r'.
  injection R as <-. rewrite eval_lsym, (rootnu_SREG _ _ _ _ _ _ _ Fin). symmetry; apply zwrap64_u.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_nilb_nil {A} (l : list A) : is_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.

Lemma root_ok_facts FP U :
  root_ok FP U = true ->
  u_root U = Some (fp_ret FP) /\ u_entry U = fp_entry FP /\ u_sp U = 0 /\ u_wstack U = []
  /\ (forall c, In c (u_wglobs U) -> c = (fp_prng FP, 8))
  /\ fst (u_sclass U) <= snd (u_sclass U)
  /\ root_pre_ok FP (u_sclass U) (u_pre U) = true
  /\ (forall X, In X (u_exits U) -> root_exit_ok X = true).
Proof.
  unfold root_ok. intros H.
  destruct (u_root U) as [r|]; [|discriminate]. bsplit H. apply Z.eqb_eq in H. subst r.
  repeat match goal with
         | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
         | K : Z.leb _ _ = true |- _ => apply Z.leb_le in K
         | K : forallb _ _ = true |- _ => rewrite forallb_forall in K
         end.
  repeat split; auto.
  - now apply is_nilb_nil.
  - intros [a w] Hc. specialize (H3 _ Hc). apply andb_prop in H3 as [Y1 Y2]. simpl in Y1, Y2.
    apply Z.eqb_eq in Y1. apply Z.eqb_eq in Y2. now subst.
Qed.

Lemma root_pre_facts FP cls cs :
  root_pre_ok FP cls cs = true ->
  cstate_wf cs = true
  /\ root_regs_ok FP (vs_regs (load_cstate cs 0 [])) = true
  /\ cs_slots cs = [] /\ cs_globs cs = [] /\ cs_nul cs = []
  /\ cs_valset cs = [] /\ cs_conddef cs = [] /\ cs_moddef cs = []
  /\ store_le (canon_store cls) (store_of cs) = true.
Proof.
  unfold root_pre_ok. intros H. bsplit H.
  repeat split; auto; now apply is_nilb_nil.
Qed.

Section Top.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable FP : FParams.
  Hypothesis GOK : fp_genv_prop (ge_P0 G) (ge_tp G) (ci_errno (ge_CI G)) FP.
  Hypothesis WR : segs_wr_readable SEGS = true.

  Variable U : vunit.
  Hypothesis RU : root_ok FP U = true.

  Let P := unit_params G U.
  Let cls := u_sclass U.

  (* [comment removed for export] *)
  #[using="GOK WR RU"] Lemma root_entry_gamma (regs : bvmap 5 word) (mem : word -> option byte) (sp data : word) (n : Z) :
    getr regs (Z_to_bv 5 1) = Z_to_bv 64 (fp_ret FP) ->
    getr regs (Z_to_bv 5 2) = sp ->
    getr regs (Z_to_bv 5 4) = Z_to_bv 64 (fp_tp FP) ->
    getr regs (Z_to_bv 5 10) = data ->
    getr regs (Z_to_bv 5 11) = Z_to_bv 64 n ->
    0 <= n < fp_nmax FP ->
    fst cls <= n <= snd cls ->
    bv_unsigned data <> 0 ->
    bv_unsigned data + n < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 ->
    F_SPLO <= bv_unsigned sp <= F_SPHI ->
    (forall i, 0 <= i < n -> exists b, rdn SEGS mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]) ->
    (forall a : word, bv_unsigned sp - fp_frame FP <= bv_unsigned a < bv_unsigned sp -> store_ok SEGS mem a 1 = true) ->
    pristine mem (fp_ro_lo FP) (fp_ro_hi FP) ->
    pristine mem (fp_gotgrd FP) (fp_gotgrd FP + 8) ->
    pristine mem (fp_mcount FP) (fp_mcount FP + 8) ->
    gamma SEGS P (rootE FP regs sp data n) mem (load_cstate (u_pre U) (u_entry U) [])
          (rootnu (rootE FP regs sp data n)) regs mem.
  Proof.
    intros H1 H2 H4 H10 H11 Hn Hcls Hd0 Hdn Hal Hsp Hrd Hst Hpr1 Hpr2 Hpr3.
    destruct GOK as (Gfr & Gtp & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gfrlo & Gfr0 & Gpris & Gro0 & Gro1 & Ggot0 & Ggot1
                     & Gmc0 & Gmc1 & Gret2 & Gret & Gtpr & Gprng & Gerrno).
    destruct (root_ok_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & Rcls & Rpre & Rex).
    destruct (root_pre_facts _ _ _ Rpre) as (Pwf & Pregs & Psl & Pgl & Pnul & Pvs & Pcd & Pmd & Ple).
    pose proof (u_word_lt sp) as Usp. pose proof (u_word_lt data) as Udata.
    assert (PF : vp_frame P = fp_frame FP) by (unfold P, unit_params; cbn [vp_frame]; exact Gfr).
    split.
    { (* [comment removed for export] *)
      unfold env_ok. cbn [e_sp0 e_size e_data e_ra e_tp e_gp e_sregs rootE].
      rewrite PF. unfold P, unit_params; cbn [vp_splo vp_sphi vp_nmax].
      pose proof (u_word_lt (getr regs (Z_to_bv 5 3))).
      repeat split; try (ltac2:(LK.k [@Hn; @Hd0; @Hal; @Gret; @Gtpr; @Gprng; @Gerrno; @Usp; @Udata; @H; @Hsp; @Gsplo; @Gsphi; @Gnmax; @Hdn; @Gfr; @Gfrlo]); lia); unfold F_SPLO, F_SPHI in *; simpl; (ltac2:(LK.k [@Hn; @Hd0; @Hal; @Gret; @Gtpr; @Gprng; @Gerrno; @Usp; @Udata; @H; @Hsp; @Gsplo; @Gsphi; @Gnmax; @Hdn; @Gfr; @Gfrlo]); lia). }
    split.
    { (* [comment removed for export] *)
      unfold MC. cbn [e_sp0 e_size e_data rootE]. rewrite PF.
      split; [|split; [|split]].
      - apply frame_store_ok_readable; auto. unfold F_SPLO in *; lia. unfold F_SPHI in *; lia.
      - intros i Hi. exact (Hrd i Hi).
      - intros lo hi a Hin Ha. unfold P, unit_params in Hin; cbn [vp_pristine] in Hin.
        specialize (Gpris _ Hin). unfold covered in Gpris. simpl in Gpris.
        assert (AUX : forall L H, pristine mem L H -> 0 <= L -> H <= 2 ^ 64 -> L <= lo -> hi <= H -> mem (wordZ a) = None).
        { intros L Hh HP HL HH Hlo Hhi. apply HP. rewrite u_wordZ; (ltac2:(LK.k [@Hn; @Hd0; @Gret; @Gtpr; @Gprng; @Gerrno; @Usp; @Udata; @Ha; @Hlo; @Hhi; @Gpris; @Gro1; @Ggot1; @Gmc1; @HL]); lia). }
        repeat (apply orb_prop in Gpris as [K|Gpris] || rename Gpris into K);
          try (apply andb_prop in K as [K1 K2]; apply Z.leb_le in K1; apply Z.leb_le in K2).
        + eapply (AUX _ _ Hpr1); eauto.
        + eapply (AUX _ _ Hpr2); eauto; lia.
        + eapply (AUX _ _ Hpr3); eauto; lia.
        + discriminate.
      - apply frame_mod_refl. }
    split; [apply rootnu_fix|].
    split.
    { (* [comment removed for export] *)
      cbn [vs_store load_cstate]. eapply store_le_sound; [exact Ple|].
      apply canon_store_sat; rewrite ?rootnu_SP0, ?rootnu_DATA, ?rootnu_SIZE; cbn [e_sp0 e_data e_size rootE]; unfold cls in Hcls; (ltac2:(LK.k [@Hn; @Hsp; @Gret; @Gtpr; @Gprng; @Gerrno; @Usp; @Udata; @Hd0; @Hal; @Hdn; @Hcls]); lia). }
    split.
    { intros b k x y Hg. cbn [vs_conddef load_cstate] in Hg. rewrite Pcd in Hg. simpl in Hg. discriminate. }
    split.
    { intros r x m Hg. cbn [vs_moddef load_cstate] in Hg. rewrite Pmd in Hg. simpl in Hg. discriminate. }
    split.
    { intros s vs Hg. cbn [vs_valset load_cstate] in Hg. rewrite Pvs in Hg. simpl in Hg. discriminate. }
    split; [eapply root_regs_sound; eauto|].
    split.
    { intros off w v Hin. cbn [vs_slots load_cstate] in Hin. rewrite Psl in Hin. destruct Hin. }
    split.
    { intros a w v Hin. cbn [vs_globs load_cstate] in Hin. rewrite Pgl in Hin. destruct Hin. }
    split.
    { intros lo hi Hin. cbn [vs_nul load_cstate] in Hin. rewrite Pnul in Hin. destruct Hin. }
    apply (proj1 (load_cstate_below _ _ _ Pwf)).
  Qed.

  (* [comment removed for export] *)
  Lemma root_exit_post (regs regs' : bvmap 5 word) (mem mem' : word -> option byte) (sp data : word) (n : Z)
        X nu' pc ctx :
    getr regs (Z_to_bv 5 1) = Z_to_bv 64 (fp_ret FP) ->
    getr regs (Z_to_bv 5 2) = sp ->
    getr regs (Z_to_bv 5 4) = Z_to_bv 64 (fp_tp FP) ->
    In X (u_exits U) ->
    gamma SEGS P (rootE FP regs sp data n) mem (load_cstate X pc ctx) nu' regs' mem' ->
    exit_regs G U (rootnu (rootE FP regs sp data n)) regs' ->
    getr regs' (Z_to_bv 5 1) = wordZ (fp_ret FP) ->
    ekeeps regs regs' /\ getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0 /\ frame_mod mem mem' (F_footprint FP sp).
  Proof.
    intros H1 H2 H4 HX HG (XR2 & XR3 & XR4 & XRS) XR1.
    destruct GOK as (Gfr & Gtp & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gfrlo & Gfr0 & Gpris & Gro0 & Gro1 & Ggot0 & Ggot1
                     & Gmc0 & Gmc1 & Gret2 & Gret & Gtpr & Gprng & Gerrno).
    destruct (root_ok_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & Rcls & Rpre & Rex).
    pose proof HG as (HE & HMC & HF & HS & HC & HMo & HV & HR & HSl & HGl & HN & HB).
    split; [|split].
    - (* [comment removed for export] *)
      intros r Hin. unfold ekept in Hin. simpl in Hin.
      assert (K1 : getr regs' (Z_to_bv 5 1) = getr regs (Z_to_bv 5 1)) by (rewrite XR1, H1; reflexivity).
      assert (K2 : getr regs' (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2)).
      { apply word_eq_u. replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity).
        rewrite XR2, rootnu_SP0, Rsp, Z.add_0_r. cbn [e_sp0 rootE].
        replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite H2. apply zwrap64_u. }
      assert (K3 : getr regs' (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3)).
      { apply word_eq_u. replace (Z_to_bv 5 3) with (3%bv : reg) at 1 by (apply bv_eq; reflexivity).
        rewrite XR3, rootnu_GP. cbn [e_gp rootE]. apply zwrap64_u. }
      assert (K4 : getr regs' (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4)).
      { apply word_eq_u. replace (Z_to_bv 5 4) with (4%bv : reg) at 1 by (apply bv_eq; reflexivity).
        rewrite XR4, H4, Gtp. symmetry. apply u_Z_to_bv64. }
      assert (KS : forall r i, In (r, i) sreg_idx -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r0 i Hri. apply word_eq_u. rewrite (XRS _ _ Hri), (rootnu_SREG _ _ _ _ _ _ _ Hri). apply zwrap64_u. }
      repeat (destruct Hin as [<-|Hin]); try (destruct Hin).
      all: match goal with |- getr _ ?rr = getr _ _ =>
             let k := eval vm_compute in (bv_unsigned rr) in
             replace rr with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end.
      all: first [exact K1 | exact K2 | exact K3 | exact K4 | eapply KS; unfold sreg_idx; simpl; tauto].
    - (* [comment removed for export] *)
      specialize (Rex _ HX). unfold root_exit_ok in Rex.
      change (vs_regs (load_cstate X 0 [])) with (vs_regs (load_cstate X pc ctx)) in Rex.
      destruct (pm_get (reg_key 10) (vs_regs (load_cstate X pc ctx))) as [e|] eqn:G10; [|discriminate].
      apply lin_eqb_eq in Rex. subst e.
      apply word_eq_u. rewrite (HR (Z_to_bv 5 10) (lconst 0)).
      + rewrite eval_lconst. rewrite u_Z_to_bv64. reflexivity.
      + vm_compute. discriminate.
      + exact G10.
    - (* [comment removed for export] *)
      destruct HMC as (_ & _ & _ & FM).
      eapply frame_mod_weaken; [|exact FM].
      intros a Ha. unfold footprint, cells_regions. unfold P, unit_params; cbn [vp_frame vp_fcells e_sp0 rootE map fst snd].
      rewrite Gfr, Gfc. cbn [map fst snd]. exact Ha.
  Qed.
End Top.

Section Main.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable FP : FParams.
  Hypothesis GOK : fp_genv_prop (ge_P0 G) (ge_tp G) (ci_errno (ge_CI G)) FP.
  Hypothesis WR : segs_wr_readable SEGS = true.
  Variable C : vcert.
  (* [comment removed for export] *)
  Hypothesis UNITS : forall rom U, In U C -> root_ok FP U = true -> unit_ok SEGS G rom U.
  Hypothesis ROK : roots_ok FP C = true.

  Lemma reg_lit (r : reg) k : bv_unsigned r = k -> Z_to_bv 5 k = r.
  Proof. intros <-. apply Z_to_bv_bv_unsigned. Qed.

  Theorem F_contract_of_roots : F_contract SEGS FP.
  Proof.
    unfold F_contract.
    intros regs mem rom sp data n H1 H2 H4 H10 H11 Hn Hd0 Hdn Hal Hsp Hdisj Hrd Hst Hp1 Hp2 Hp3.
    pose proof GOK as (Gfr & Gtp & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gfrlo & Gfr0 & Gpris & Gro0 & Gro1 & Ggot0 & Ggot1
                     & Gmc0 & Gmc1 & Gret2 & Gret & Gtpr & Gprng & Gerrno).
    (* [comment removed for export] *)
    unfold roots_ok in ROK.
    destruct (cover_sound _ _ _ _ ROK n) as (c & Hc & Hcn); [lia|].
    apply in_map_iff in Hc as (U & EqC & HU). unfold roots in HU. apply filter_In in HU as [HinC RU].
    pose proof (root_ok_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & Rcls & Rpre & Rex).
    (* [comment removed for export] *)
    rewrite <- (reg_lit 1%bv 1 eq_refl) in H1. rewrite <- (reg_lit 2%bv 2 eq_refl) in H2.
    rewrite <- (reg_lit 4%bv 4 eq_refl) in H4. rewrite <- (reg_lit 10%bv 10 eq_refl) in H10.
    rewrite <- (reg_lit 11%bv 11 eq_refl) in H11.
    set (E := rootE FP regs sp data n). set (nu := rootnu E).
    assert (RET : unit_ret U E = fp_ret FP) by (unfold unit_ret; now rewrite Rroot).
    pose proof (UNITS rom U HinC RU E mem nu regs mem) as UOK.
    rewrite RET, Rentry in UOK.
    destruct UOK as (regs' & mem' & MS & EX).
    { apply ret_ok_even. rewrite u_wordZ; [exact Gret2|exact Gret]. }
    { unfold gammaU, PU. rewrite <- Rentry. subst E nu. eapply root_entry_gamma; eauto. rewrite EqC. exact Hcn. }
    exists regs', mem'. split; [exact MS|].
    destruct EX as (X & nu' & HX & HGX & EXT & RA1 & XREGS & FMX).
    rewrite RET in HGX, RA1. rewrite <- (reg_lit 1%bv 1 eq_refl) in RA1.
    destruct (root_exit_post SEGS G FP GOK U RU regs regs' mem mem' sp data n X nu' (fp_ret FP) []
                H1 H2 H4 HX HGX XREGS RA1) as (K1 & K2 & K3).
    split; [exact K1|]. split; [|exact K3].
    rewrite <- (reg_lit 10%bv 10 eq_refl). exact K2.
  Qed.
End Main.

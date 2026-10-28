(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsLazyRun AsStdioCall.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsExit Require Import FeDefs FeRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Notation RSEGS := AsanUbsan.M.loaded_segments (only parsing).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kn_frames (kn : list kentry) (ws : list (saddr * Z)) : list kentry :=
  match ws with
  | [] => kn
  | (SA b k, n) :: r => kn_frames (kn_frame kn b k n) r
  end.

Definition in_win (E : env) (w : saddr * Z) (x : word) : Prop :=
  estart E (fst w) <= bv_unsigned x < estart E (fst w) + snd w.

Lemma know_ok_frames : forall E ws M M' kn,
  know_ok RSEGS E M kn ->
  Forall (fun w => flat E (fst w) (snd w)) ws ->
  (forall x : word, Forall (fun w => ~ in_win E w x) ws -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frames kn ws).
Proof.
  intros E ws. induction ws as [|[[b k] n] ws IH]; intros M M' kn HK Hfl Hout Hg; cbn [kn_frames].
  - assert (EM : M' = M) by (apply functional_extensionality; intros x; apply Hout; constructor). rewrite EM. exact HK.
  - inversion Hfl as [|w ws' Hw Hws]; subst. cbn [fst snd] in Hw.
    set (a := estart E (SA b k)).
    set (M1 := fun x : word => if inr a n x then M' x else M x).
    apply (IH M1 M').
    + eapply know_ok_frame; [exact HK | exact Hw | |].
      * intros x Hx. unfold M1. destruct (inr a n x) eqn:Ei; [|reflexivity]. apply inr_spec in Ei. subst a. lia.
      * intros x Hx. unfold M1. destruct (inr a n x); [apply Hg; exact Hx | exact Hx].
    + exact Hws.
    + intros x Hx. unfold M1. destruct (inr a n x) eqn:Ei; [reflexivity|]. apply Hout. constructor; [|exact Hx].
      apply inr_false in Ei. unfold in_win. cbn [fst snd]. subst a. exact Ei.
    + intros x Hx. unfold M1 in Hx. destruct (inr a n x); [exact Hx | apply Hg; exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition UC_KEPT : list nat := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition FE_WINDOWS_LIT : list (Z * Z) :=
  [(0x6a8000, 4096); (0xbdd000, 4096); (0xbdf000, 4096); (0xbe1000, 4096); (FE_SH_LO, FE_SH_HI - FE_SH_LO)].

Definition uc_windows (qb : expr) (k0 : Z) : list (saddr * Z) :=
  (SA qb (k0 - FE_STK), FE_STK) :: map (fun w => (SA (ELit 0) (fst w), snd w)) FE_WINDOWS_LIT.

Record unreg_res : Type := UCR { uc_sr : list expr; uc_kn : list kentry }.

Definition unreg_call (nv : nat) (sr : list expr) (kn : list kentry) : option unreg_res :=
  match nth 1 sr (ELit 0), nth 10 sr (ELit 0), nth 11 sr (ELit 0) with
  | ELit ra, ELit a0, ELit a1 =>
    let sp := nth 2 sr (ELit 0) in
    let '(qb, k0) := split_lit sp in
    match kindex (is_kwr_cov qb (k0 - FE_STK) FE_STK) kn 0, kindex (is_kwr_cov (ELit 0) FE_SH_LO (FE_SH_HI - FE_SH_LO)) kn 0,
          base_range kn qb with
    | Some _, Some _, Some (blo, bhi) =>
      if ((ra =? FE_RET) && (a0 =? FE_GLB) && (a1 =? FE_NGLB)
          && (4 <=? ealign kn sp) && (FE_SPLO + FE_STK <=? blo + k0) && (bhi + k0 <=? FE_SPHI) && (0 <=? blo)
          && forallb (fun c : Z * nat * Z => match c with (a, n, v) =>
                        match kread RSEGS kn (ELit 0) a n with Some (ELit v') => v' =? v | _ => false end end) FE_CELLS
          && forallb (fun iv : Z * Z => existsb (is_kimg_cov (fst iv) (snd iv - fst iv)) kn) FE_CLEAR
          && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
      then Some (UCR (sr_after_call_j sr UC_KEPT nv) (kn_frames kn (uc_windows qb k0)))
      else None
    | _, _, _ => None
    end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kimg_cov_none : forall E M kn lo hi,
  know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true ->
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M kn lo hi HK Hx i Hi. apply existsb_exists in Hx as (K & HK' & Hc).
  destruct K as [| | |l h| | | |]; try discriminate. cbn [is_kimg_cov] in Hc.
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HK') as Hok. cbn [kentry_ok] in Hok. destruct Hok as (_ & _ & Hn).
  apply Hn. lia.
Qed.

Lemma sixteen_divides : forall k x, 4 <= k -> (2 ^ k | x) -> x mod 16 = 0.
Proof.
  intros k x Hk [q ->]. replace k with (k - 4 + 4) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 4) with 16.
  rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

Section Sound.
  Variables (L S Zr : list (word * word)).

  Theorem unreg_call_sound :
    forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
           (R : bvmap 5 word) (M : word -> option byte) (msF : machine_state) (mo : Model) (res : unreg_res) (K : TSet),
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    unreg_call (length vals) sr kn = Some res ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 FE_ENTRY) M (seg_rom RSEGS) ->
    (forall R' M' msF' mo',
       regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (uc_sr res) R' ->
       know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (uc_kn res) ->
       (forall x : word, ~ fe_written (bv_unsigned (edenot E (nth 2 sr (ELit 0)))) (bv_unsigned x) -> M' x = M x) ->
       mem_grows M M' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 FE_RET) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) K.
  Proof.
    intros vals ebs sr kn R M msF mo res K E HR HK Hc OK RS HCONT.
    cbv beta delta [unreg_call] in Hc. cbv zeta in Hc.
    destruct (nth 1 sr (ELit 0)) as [ra| | | | | | |] eqn:H1; try discriminate.
    destruct (nth 10 sr (ELit 0)) as [a0| | | | | | |] eqn:H10; try discriminate.
    destruct (nth 11 sr (ELit 0)) as [a1| | | | | | |] eqn:H11; try discriminate.
    destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
    destruct (kindex (is_kwr_cov qb (k0 - FE_STK) FE_STK) kn 0) as [j1|] eqn:Hk1; [|discriminate].
    destruct (kindex (is_kwr_cov (ELit 0) FE_SH_LO (FE_SH_HI - FE_SH_LO)) kn 0) as [j2|] eqn:Hk2; [|discriminate].
    destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
    match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    injection Hc as <-. cbn [uc_sr uc_kn] in HCONT.
    apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
    apply andb_prop in Hcond as [Hcond Hclr]. apply andb_prop in Hcond as [Hcond Hcells].
    apply andb_prop in Hcond as [Hcond Hblo0]. apply andb_prop in Hcond as [Hcond Hhi]. apply andb_prop in Hcond as [Hcond Hlo].
    apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond Ea1]. apply andb_prop in Hcond as [Era Ea0].
    apply Z.eqb_eq in Era. apply Z.eqb_eq in Ea0. apply Z.eqb_eq in Ea1. subst ra a0 a1.
    apply Z.leb_le in Hal. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hblo0. apply Nat.eqb_eq in Hlen32.
    (* [comment removed for export] *)
    assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
    { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
    assert (Rra : getr R 1 = Z_to_bv 64 FE_RET).
    { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia. rewrite H1. reflexivity. }
    assert (Ra0 : getr R 10 = Z_to_bv 64 FE_GLB).
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia. rewrite H10. reflexivity. }
    assert (Ra1 : getr R 11 = Z_to_bv 64 FE_NGLB).
    { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). rewrite RG by lia. rewrite H11. reflexivity. }
    set (sp := edenot E (nth 2 sr (ELit 0))) in *.
    pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
    pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
    set (uq := bv_unsigned (edenot E qb)) in *.
    assert (Hspz : bv_unsigned sp = uq + k0).
    { rewrite Hsqd. apply u64_lit. unfold FE_SPLO, FE_SPHI, FE_STK in *. lia. }
    assert (Rsp : getr R 2 = Z_to_bv 64 (uq + k0)).
    { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). rewrite RG by lia. fold sp. rewrite <- Hspz. symmetry. apply Z_to_bv_bv_unsigned. }
    (* [comment removed for export] *)
    destruct (ealign_sound RSEGS E M kn (nth 2 sr (ELit 0)) HK) as [_ Hdiv]. fold sp in Hdiv. rewrite Hspz in Hdiv.
    pose proof (sixteen_divides _ _ Hal Hdiv) as Hsp16.
    (* [comment removed for export] *)
    destruct (kindex_some _ _ _ _ Hk1) as (KW1 & Hn1 & HKW1 & _).
    destruct KW1 as [| | | | | |[cb1 ck1] cl1|]; try discriminate. cbn [is_kwr_cov] in HKW1.
    apply andb_prop in HKW1 as [HKW1 Hc12]. apply andb_prop in HKW1 as [Hcb1 Hc11].
    apply expr_eqb_eq in Hcb1. subst cb1. apply Z.leb_le in Hc11. apply Z.leb_le in Hc12.
    assert (Wstk : forall i, 0 <= i < FE_STK -> store_ok RSEGS M (Z_to_bv 64 (uq + k0 - FE_STK + i)) 1 = true).
    { intros i Hi. pose proof (kwr_store_ok RSEGS E M kn _ qb ck1 cl1 (k0 - FE_STK + i) 1%nat HK Hn1 ltac:(lia) ltac:(cbn; lia)) as W.
      unfold adenot, v_addi in W. cbn [a_base a_off] in W. fold uq in W.
      replace (uq + (k0 - FE_STK + i)) with (uq + k0 - FE_STK + i) in W by lia. exact W. }
    destruct (kindex_some _ _ _ _ Hk2) as (KW2 & Hn2 & HKW2 & _).
    destruct KW2 as [| | | | | |[cb2 ck2] cl2|]; try discriminate. cbn [is_kwr_cov] in HKW2.
    apply andb_prop in HKW2 as [HKW2 Hc22]. apply andb_prop in HKW2 as [Hcb2 Hc21].
    apply expr_eqb_eq in Hcb2. subst cb2. apply Z.leb_le in Hc21. apply Z.leb_le in Hc22.
    assert (Wsh : forall i, 0 <= i < FE_SH_HI - FE_SH_LO -> store_ok RSEGS M (Z_to_bv 64 (FE_SH_LO + i)) 1 = true).
    { intros i Hi. apply (kwr_store_ok_lit RSEGS E M kn _ ck2 cl2 (FE_SH_LO + i) 1%nat HK Hn2); unfold FE_SH_LO, FE_SH_HI in *; cbn; lia. }
    (* [comment removed for export] *)
    assert (Wcells : forall a n v, In (a, n, v) FE_CELLS -> rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v))).
    { intros a n v Hin. rewrite forallb_forall in Hcells. specialize (Hcells _ Hin). cbn beta iota in Hcells.
      destruct (kread RSEGS kn (ELit 0) a n) as [[v'| | | | | | |]|] eqn:Hkr; try discriminate. apply Z.eqb_eq in Hcells. subst v'.
      assert (Hb : 0 <= a /\ a + 8 <= 2 ^ 64 /\ (1 <= n <= 8)%nat).
      { unfold FE_CELLS in Hin. cbn [In] in Hin.
        destruct Hin as [E0|[E0|[E0|[E0|[E0|[E0|[E0|[]]]]]]]]; injection E0 as <- <- <-; (split; [lia | split; [lia | cbn; lia]]). }
      pose proof (kread_rdn RSEGS E M kn (ELit 0) a n (ELit v) HK Hkr ltac:(lia) ltac:(lia) ltac:(apply flat_abs0; lia)) as Rd.
      rewrite adenot_lit0 in Rd. exact Rd. }
    (* [comment removed for export] *)
    assert (Wclr : forall lo hi i, In (lo, hi) FE_CLEAR -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi i Hin Hi. rewrite forallb_forall in Hclr. specialize (Hclr _ Hin). cbn [fst snd] in Hclr.
      exact (kimg_cov_none E M kn lo hi HK Hclr i Hi). }
    (* [comment removed for export] *)
    destruct (fe_run R M (uq + k0) Rra Rsp Ra0 Ra1 Hsp16 ltac:(unfold FE_SPLO, FE_STK in *; lia) ltac:(unfold FE_SPHI in *; lia)
                Wclr Wcells Wstk Wsh) as (R' & M' & Hms & Hsp' & Hsaved & Hfr & Hgrow).
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK | exact RS | exact Hms |].
    intros msF' mo' OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | rewrite Hspz; exact Hfr | exact Hgrow | exact OK' | exact SB' | exact HS' | exact RS'].
    - (* [comment removed for export] *)
      apply (regs_after_call vals ebs sr R R' UC_KEPT Hsv HR).
      + intros i Hi. unfold UC_KEPT in Hi. cbn [In] in Hi.
        destruct Hi as [<-|Hi].
        { split; [lia|]. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Hsp', Rsp. reflexivity. }
        assert (Hs : (i < 32)%nat /\ In (Z.of_nat i) FE_SAVED).
        { unfold FE_SAVED. cbn [In]. destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; split; cbn; lia. }
        destruct Hs as [Hi32 Hin]. split; [exact Hi32|]. exact (Hsaved (Z.of_nat i) Hin).
      + unfold UC_KEPT. cbn [In]. lia.
    - (* [comment removed for export] *)
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (Eqb : edenot E' qb = edenot E qb).
      { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
        apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
      apply (know_ok_frames E' (uc_windows qb k0) M M' kn HK').
      + unfold uc_windows, FE_WINDOWS_LIT. cbn [map].
        repeat (apply Forall_cons); [ | | | | | | apply Forall_nil]; cbn [fst snd].
        1: { unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. fold uq. unfold FE_STK, FE_SPLO, FE_SPHI in *. lia. }
        all: apply flat_abs0; unfold FE_SH_LO, FE_SH_HI; lia.
      + intros x Hout. apply Hfr. intros Hw.
        unfold uc_windows, FE_WINDOWS_LIT in Hout. cbn [map fst snd] in Hout.
        apply Forall_cons_iff in Hout as [W1 Hout]. apply Forall_cons_iff in Hout as [W2 Hout]. apply Forall_cons_iff in Hout as [W3 Hout].
        apply Forall_cons_iff in Hout as [W4 Hout]. apply Forall_cons_iff in Hout as [W5 Hout]. apply Forall_cons_iff in Hout as [W6 _].
        unfold in_win, estart in W1, W2, W3, W4, W5, W6. cbn [fst snd a_base a_off] in W1, W2, W3, W4, W5, W6.
        rewrite Eqb in W1. change (bv_unsigned (edenot E qb)) with uq in W1. change (bv_unsigned (edenot E' (ELit 0))) with 0 in W2, W3, W4, W5, W6.
        unfold fe_written, FE_WR_PAGES, FE_STK, FE_SH_LO, FE_SH_HI in Hw, W1, W2, W3, W4, W5, W6. cbn [In] in Hw.
        pose proof (u64_range x) as Hx. clear - Hw W1 W2 W3 W4 W5 W6 Hx.
        destruct Hw as [Hw|[Hw|Hw]]; [lia | | lia].
        destruct Hw as [Hw|[Hw|[Hw|[Hw|[]]]]];
          match type of Hw with ?p = _ => assert (p * 4096 <= bv_unsigned x < p * 4096 + 4096) by (rewrite Hw; Z.div_mod_to_equations; lia) end; lia.
      + exact Hgrow.
  Qed.
End Sound.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeEFA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module DrvShape.

Definition bz (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition MSG_USAGE_PRE : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition MSG_USAGE_POST : list Z := [32; 73; 78; 80; 85; 84; 10].
Definition MSG_OPEN_PRE : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].
Definition MSG_RDERR_PRE : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32].
Definition NL : list Z := [10].
Definition MSG_OOM : list Z := [99; 108; 105; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10].
Definition MSG_BIG : list Z :=
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32;
   114; 101; 102; 117; 115; 101; 100; 10].
Definition MSG_SHORT : list Z :=
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10].
Definition MSG_CFG : list Z :=
  [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10].
Definition LINE0 : list Z := [48; 10].

Inductive chunk := CLit (zs : list Z) | CA0 | CP1.

Inductive shp := SWr (fd : Z) (cs : list chunk) (k : shp) | SX (c : Z) | SALT (a b : shp).

Fixpoint zs_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && zs_eqb a' b'
  | _, _ => false
  end.
Definition chunk_eqb (a b : chunk) : bool :=
  match a, b with
  | CLit x, CLit y => zs_eqb x y
  | CA0, CA0 => true
  | CP1, CP1 => true
  | _, _ => false
  end.
Fixpoint chunks_eqb (a b : list chunk) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => chunk_eqb x y && chunks_eqb a' b'
  | _, _ => false
  end.
Fixpoint shp_eqb (a b : shp) : bool :=
  match a, b with
  | SWr f x k, SWr g y l => Z.eqb f g && chunks_eqb x y && shp_eqb k l
  | SX c, SX d => Z.eqb c d
  | SALT a1 a2, SALT b1 b2 => shp_eqb a1 b1 && shp_eqb a2 b2
  | _, _ => false
  end.

Fixpoint cnorm (cs : list chunk) : list chunk :=
  match cs with
  | [] => []
  | CLit [] :: cs' => cnorm cs'
  | CLit zs :: cs' => match cnorm cs' with CLit ys :: r => CLit (zs ++ ys) :: r | r => CLit zs :: r end
  | c :: cs' => c :: cnorm cs'
  end.

Fixpoint norm (s : shp) : shp :=
  match s with
  | SWr fd cs k =>
      match norm k with
      | SWr fd' cs' k' => if Z.eqb fd fd' then SWr fd (cnorm (cs ++ cs')) k'
                         else match cnorm cs with [] => SWr fd' cs' k' | c => SWr fd c (SWr fd' cs' k') end
      | k' => match cnorm cs with [] => k' | c => SWr fd c k' end
      end
  | SX c => SX c
  | SALT a b => SALT (norm a) (norm b)
  end.

Definition shp_eqv (a b : shp) : bool := shp_eqb (norm a) (norm b).

Section Den.
Variables (fs0 : Fs) (a0 p1 : list byte).

Definition W (fd : Z) (s : list byte) (T : TSet) : TSet := t_emit (map (WriteEv (Z_to_bv 64 fd)) s) T.
Definition X (c : Z) : TSet := t_exit (Z_to_bv 64 c) fs0.

Definition den_chunk (c : chunk) : list byte := match c with CLit zs => bz zs | CA0 => a0 | CP1 => p1 end.
Fixpoint den_chunks (cs : list chunk) : list byte := match cs with [] => [] | c :: cs' => den_chunk c ++ den_chunks cs' end.

Fixpoint D (s : shp) : TSet :=
  match s with
  | SWr fd cs k => W fd (den_chunks cs) (D k)
  | SX c => X c
  | SALT a b => t_alt2 (D a) (D b)
  end.

Lemma D_nil : forall s, D s [].
Proof.
  induction s as [fd cs k IH | c | a IHa b IHb]; cbn [D].
  - unfold W. apply t_emit_has_nil.
  - unfold X, t_exit. left. exact I.
  - left. exact IHa.
Qed.

Lemma kill_free_W : forall fd s T, kill_free T -> kill_free (W fd s T).
Proof.
  intros fd s T HT. unfold W. apply kill_free_t_emit; [|exact HT].
  intros sig fs Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb.
Qed.
Lemma kill_free_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H]; [exact (HA tr sig fs H) | exact (HB tr sig fs H)]. Qed.
Lemma D_kill_free : forall s, kill_free (D s).
Proof.
  induction s as [fd cs k IH | c | a IHa b IHb]; cbn [D].
  - apply kill_free_W. exact IH.
  - unfold X. apply kill_free_t_exit.
  - apply kill_free_alt2; assumption.
Qed.

Lemma is_prefix_app_inv {A} : forall (tr a b : list A), is_prefix tr (a ++ b) <-> is_prefix tr a \/ exists t, tr = a ++ t /\ is_prefix t b.
Proof.
  intros tr a. revert tr. induction a as [|x a IH]; intros tr b; cbn [app].
  - split; [intros H; right; exists tr; auto|]. intros [H|(t & -> & H)]; [|exact H]. destruct tr; [destruct b; exact I || exact H | destruct H].
  - destruct tr as [|y tr]; cbn [is_prefix].
    + split; [intros _; left; exact I | intros _; exact I].
    + rewrite IH. split.
      * intros [<- [H|(t & -> & H)]]; [left; auto | right; exists t; auto].
      * intros [[<- H]|(t & Heq & H)]; [split; [reflexivity|left; exact H]|]. injection Heq as <- ->. split; [reflexivity|right; exists t; auto].
Qed.

Lemma W_app : forall fd a b T, t_eq (W fd a (W fd b T)) (W fd (a ++ b) T).
Proof.
  intros fd a b T tr. unfold W, t_emit. rewrite map_app. split.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_inv. left. exact Hp.
    + left. apply is_prefix_app_inv. right. exists tr'. auto.
    + right. exists tr''. rewrite app_assoc. auto.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_inv in Hp. destruct Hp as [Hp | (t & -> & Hp)]; [left; exact Hp|]. right. exists t. auto.
    + right. exists (map (WriteEv (Z_to_bv 64 fd)) b ++ tr'). rewrite app_assoc. split; [reflexivity|]. right. exists tr'. auto.
Qed.

Lemma W_nil : forall fd T, T [] -> t_eq (W fd [] T) T.
Proof. intros fd T HT. unfold W. cbn [map]. apply t_emit_nil_eq. exact HT. Qed.

Lemma W_cong : forall fd s T T', t_eq T T' -> t_eq (W fd s T) (W fd s T').
Proof.
  intros fd s T T' H tr. unfold W, t_emit. split; (intros [Hp|(t & -> & Ht)]; [left; exact Hp | right; exists t; split; [reflexivity|apply H; exact Ht]]).
Qed.
Lemma alt2_cong : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). tauto. Qed.

Lemma den_chunks_app : forall a b, den_chunks (a ++ b) = den_chunks a ++ den_chunks b.
Proof. induction a as [|c a IH]; intros b; cbn [den_chunks app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma cnorm_sound : forall cs, den_chunks (cnorm cs) = den_chunks cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|]. cbn [cnorm].
  destruct c as [zs| |]; cbn [den_chunks]; try (rewrite IH; reflexivity).
  destruct zs as [|z zs']; [exact IH|].
  destruct (cnorm cs) as [|[ys| |] r] eqn:Hc; cbn [den_chunks den_chunk] in *; rewrite <- IH; try reflexivity.
  unfold bz. rewrite map_app, app_assoc. reflexivity.
Qed.

Lemma norm_sound : forall s, t_eq (D (norm s)) (D s).
Proof.
  induction s as [fd cs k IH | c | a IHa b IHb]; cbn [norm D].
  - assert (G : forall k', t_eq (D k') (D k) ->
              t_eq (D (match cnorm cs with [] => k' | c0 :: l => SWr fd (c0 :: l) k' end)) (W fd (den_chunks cs) (D k))).
    { intros k' Hk'. destruct (cnorm cs) as [|c r] eqn:Hc.
      - eapply t_eq_trans; [exact Hk'|]. apply t_eq_sym. rewrite <- cnorm_sound, Hc. cbn [den_chunks]. apply W_nil. apply D_nil.
      - cbn [D]. rewrite <- Hc, cnorm_sound. apply W_cong. exact Hk'. }
    destruct (norm k) as [fd' cs' k' | c' | a' b'] eqn:Hn; try (apply G; exact IH).
    destruct (Z.eqb fd fd') eqn:Efd; [|apply G; exact IH].
    apply Z.eqb_eq in Efd. subst fd'. cbn [D]. rewrite cnorm_sound, den_chunks_app.
    eapply t_eq_trans; [apply t_eq_sym; apply W_app|]. apply W_cong. cbn [D] in IH. exact IH.
  - apply t_eq_refl.
  - apply alt2_cong; assumption.
Qed.

Lemma chunks_eqb_eq : forall a b, chunks_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [chunks_eqb] in H; try discriminate H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. f_equal; [|exact (IH b H2)].
  destruct x, y; cbn [chunk_eqb] in H1; try discriminate H1; try reflexivity.
  f_equal. revert zs0 H1. induction zs as [|u us IHu]; intros [|v vs] H1; cbn [zs_eqb] in H1; try discriminate H1; [reflexivity|].
  apply andb_prop in H1 as [Hu Hv]. apply Z.eqb_eq in Hu. rewrite Hu, (IHu vs Hv). reflexivity.
Qed.

Lemma shp_eqb_eq : forall a b, shp_eqb a b = true -> a = b.
Proof.
  induction a as [f x k IH | c | a1 IH1 a2 IH2]; intros [g y l | d | b1 b2] H; cbn [shp_eqb] in H; try discriminate H.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply chunks_eqb_eq in H2.
    rewrite H1, H2, (IH l H3). reflexivity.
  - apply Z.eqb_eq in H. rewrite H. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IH1 b1 H1), (IH2 b2 H2). reflexivity.
Qed.

Theorem shp_eqv_sound : forall a b, shp_eqv a b = true -> t_eq (D a) (D b).
Proof.
  intros a b H. unfold shp_eqv in H. apply shp_eqb_eq in H.
  eapply t_eq_trans; [apply t_eq_sym; apply norm_sound|]. rewrite H. apply norm_sound.
Qed.
End Den.

Fixpoint lines (k : nat) : list Z := match k with O => [] | S k' => LINE0 ++ lines k' end.

Inductive ostate := FRESH | BUF (k : nat).

Definition MSG (zs : list Z) : shp := SWr 2 [CLit zs] (SX 2).
Definition USAGE : shp := SWr 2 [CLit MSG_USAGE_PRE; CA0; CLit MSG_USAGE_POST] (SX 2).
Definition OPENFAIL : shp := SWr 2 [CLit MSG_OPEN_PRE; CP1; CLit NL] (SX 2).
Definition OOM : shp := MSG MSG_OOM.
Definition RDERR : shp := SWr 2 [CLit MSG_RDERR_PRE; CP1; CLit NL] (SX 2).

Definition FIN (w : ostate) : shp :=
  match w with BUF (S k) => SWr 1 [CLit (lines (S k))] (SX 0) | _ => SX 0 end.

Fixpoint CALLS (n : nat) (w : ostate) : shp :=
  match n with
  | O => FIN w
  | S n' => match w with
            | FRESH => SWr 1 [CLit LINE0] (CALLS n' (BUF 0))
            | BUF k => CALLS n' (BUF (S k))
            end
  end.

Section File.
Variable file : list byte.
Definition size : Z := Z.of_nat (length file).
Definition cfgw : Z := match file with b0 :: b1 :: _ => bv_unsigned b0 + 256 * bv_unsigned b1 | _ => 0 end.
Definition cfg_len : Z := cfgw mod 32768.
Definition count_bit : bool := 32768 <=? cfgw.

Definition calls : nat := if cfg_len =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 file (Z_to_bv 8 0)) mod 4)).
Definition payload_len : Z := size - 6 - cfg_len.
Definition payload : list byte := skipn (Z.to_nat (6 + cfg_len)) file.

Definition xcode : Z := if count_bit then 0 else 2.
Definition XC : shp := SX xcode.

Definition POST : shp :=
  if size <? 6 then MSG MSG_SHORT
  else if size <? 6 + cfg_len then MSG MSG_CFG
  else CALLS calls FRESH.

Fixpoint RDn (d : nat) (cap : Z) : shp :=
  if size <? cap then POST
  else match d with
       | O => MSG MSG_BIG
       | S d' => RDn d' (2 * cap)
       end.

Definition FILE : shp := SALT (RDn 10 65536) OPENFAIL.
End File.

Definition DIR : shp := SALT RDERR OPENFAIL.

Definition K2 (fs0 : Fs) (p1 : list byte) : shp :=
  if 4096 <=? Z.of_nat (length p1) then OPENFAIL
  else if path_eqb p1 [] then OPENFAIL
  else if path_is_dirref p1 then DIR
  else match fs_lookup fs0 p1 with
       | None => OPENFAIL
       | Some file => FILE file
       end.

Definition K (inp : ProcInput) : TSet :=
  match in_argv inp with
  | [a0; p1] => D (in_fs inp) a0 p1 (K2 (in_fs inp) p1)
  | a0 :: _ => D (in_fs inp) a0 [] USAGE
  | [] => D (in_fs inp) [] [] USAGE
  end.

Theorem K_kill_free : forall inp, kill_free (K inp).
Proof. intros inp. unfold K. destruct (in_argv inp) as [|a0 [|p1 [|? ?]]]; apply D_kill_free. Qed.

Theorem K_nil : forall inp, K inp [].
Proof. intros inp. unfold K. destruct (in_argv inp) as [|a0 [|p1 [|? ?]]]; apply D_nil. Qed.

Section Edges.
Variable (file : list byte).
Let size := size file.

Lemma RDn_post : forall d cap, size < cap -> RDn file d cap = POST file.
Proof. intros d cap H. destruct d; cbn [RDn]; fold size; (replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact H)); reflexivity. Qed.
Lemma RDn_grow : forall d cap, cap <= size -> RDn file (S d) cap = RDn file d (2 * cap).
Proof. intros d cap H. cbn [RDn]. fold size. replace (size <? cap) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma RDn_big : forall cap, cap <= size -> RDn file 0 cap = MSG MSG_BIG.
Proof. intros cap H. cbn [RDn]. fold size. replace (size <? cap) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma POST_short : size < 6 -> POST file = MSG MSG_SHORT.
Proof. intros H. unfold POST. fold size. replace (size <? 6) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity. Qed.
Lemma POST_cfg : 6 <= size -> size < 6 + cfg_len file -> POST file = MSG MSG_CFG.
Proof.
  intros H1 H2. unfold POST. fold size. replace (size <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (size <? 6 + cfg_len file) with true by (symmetry; apply Z.ltb_lt; exact H2). reflexivity.
Qed.
Lemma POST_calls : 6 + cfg_len file <= size -> POST file = CALLS (calls file) FRESH.
Proof.
  intros H1. unfold POST. fold size. replace (size <? 6) with false by (symmetry; apply Z.ltb_ge; pose proof (Z.mod_pos_bound (cfgw file) 32768); unfold cfg_len in H1; lia).
  replace (size <? 6 + cfg_len file) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma POST_empty : 6 + cfg_len file <= size -> payload_len file = 0 -> POST file = CALLS (calls file) FRESH.
Proof. intros H1 _. exact (POST_calls H1). Qed.
Lemma POST_payload : 6 + cfg_len file <= size -> payload_len file <> 0 -> POST file = CALLS (calls file) FRESH.
Proof. intros H1 _. exact (POST_calls H1). Qed.
Lemma XC_count : count_bit file = true -> XC file = SX 0.
Proof. intros H. unfold XC, xcode. rewrite H. reflexivity. Qed.
Lemma XC_plain : count_bit file = false -> XC file = SX 2.
Proof. intros H. unfold XC, xcode. rewrite H. reflexivity. Qed.
End Edges.

End DrvShape.

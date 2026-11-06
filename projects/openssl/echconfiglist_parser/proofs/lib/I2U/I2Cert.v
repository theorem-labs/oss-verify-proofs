(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import
  I2Inv I2NodeLib I2NodeM I2Start I2Top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition L31 : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Lemma nth_L31 : forall k, (k < 31)%nat -> nth k L31 0 = Z.of_nat k + 1.
Proof. intros k Hk. do 31 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma nth_map_L31 : forall (x : Z -> word) k, (k < 31)%nat -> nth k (map x L31) w0 = x (Z.of_nat k + 1).
Proof.
  intros x k Hk. rewrite (nth_indep _ w0 (x 0)) by (rewrite length_map; cbn; lia).
  rewrite map_nth. rewrite nth_L31 by exact Hk. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record ssrc : Type := SSrc {
  s_cregs : list (Z * Z);          (* [comment removed for export] *)
  s_vals : list (Z * list Z);      (* [comment removed for export] *)
  s_clear : list (Z * Z);          (* [comment removed for export] *)
  s_words : list (Z * Z * int)     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition schunk (m : mem) (A : Z) (bs : list Z) : Prop :=
  forall i, (i < length bs)%nat -> mrd usegs m (wa (A + Z.of_nat i)) = Some (Z_to_bv 8 (nth i bs 0)).
Definition sword (m : mem) (A : Z) (n : Z) (w : word) : Prop :=
  forall j, (j < Z.to_nat n)%nat -> mrd usegs m (wa (A + Z.of_nat j)) = nth_error (le8 w) j.
Definition wlookup (W : list (int * word)) (t : int) : word :=
  match find (fun tw : int * word => (fst tw =? t)%uint63) W with Some tw => snd tw | None => w0 end.

Definition ssrc_holds (S : ssrc) (x : Z -> word) (W : list (int * word)) (m : mem) : Prop :=
  Forall (fun rc : Z * Z => x (fst rc) = Z_to_bv 64 (snd rc)) (s_cregs S)
  /\ Forall (fun ab : Z * list Z => schunk m (fst ab) (snd ab)) (s_vals S)
  /\ Forall (fun lh : Z * Z => forall a, fst lh <= a < snd lh -> m (wa a) = None) (s_clear S)
  /\ Forall (fun ant : Z * Z * int => sword m (fst (fst ant)) (snd (fst ant)) (wlookup W (snd ant))) (s_words S).

(* [comment removed for export] *)
Definition le8Z (v : Z) : list Z := map (fun i : Z => (v / 2 ^ (8 * i)) mod 256) [0; 1; 2; 3; 4; 5; 6; 7].
Definition le4Z (v : Z) : list Z := map (fun i : Z => (v / 2 ^ (8 * i)) mod 256) [0; 1; 2; 3].

(* [comment removed for export] *)
Fixpoint bytes_eqb (bl : list byte) (bs : list Z) : bool :=
  match bl, bs with
  | [], [] => true
  | b :: bl', z :: bs' => (bv_unsigned b =? z)%Z && bytes_eqb bl' bs'
  | _, _ => false
  end.
Lemma schunk_of_bytes_at : forall m A bl bs, bytes_at usegs m A bl -> bytes_eqb bl bs = true -> schunk m A bs.
Proof.
  intros m A bl bs (_ & _ & HB) He i Hi.
  assert (Hlen : length bl = length bs /\ forall k, (k < length bs)%nat -> nth_error bl k = Some (Z_to_bv 8 (nth k bs 0))).
  { clear HB Hi. revert bs He. induction bl as [|b bl IH]; intros [|z bs] He; cbn in He; try discriminate.
    - split; [reflexivity | intros k Hk; cbn in Hk; lia].
    - apply andb_true_iff in He as [Hb Ht]. apply Z.eqb_eq in Hb. destruct (IH bs Ht) as [L R]. split; [cbn; lia|].
      intros [|k] Hk; cbn.
      + f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
      + apply R. cbn in Hk. lia. }
  destruct Hlen as [L R]. rewrite (HB i ltac:(lia)). exact (R i Hi).
Qed.
Lemma schunk_of_rw_cells : forall m A cs bs, rw_cells usegs m A cs -> bytes_eqb (cells_bytes cs) bs = true -> schunk m A bs.
Proof. intros m A cs bs [[_ HB] _] He. exact (schunk_of_bytes_at m A _ bs HB He). Qed.
Lemma sword_of_C8 : forall m A w, rw_cells usegs m A [C8 w] -> sword m A 8 w.
Proof.
  intros m A w [[_ (_ & _ & HB)] _] j Hj. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. apply HB. rewrite length_le8. exact Hj.
Qed.
Lemma sword_of_C4 : forall m A w, rw_cells usegs m A [C4 w] -> sword m A 4 w.
Proof.
  intros m A w [[_ (_ & _ & HB)] _] j Hj. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  rewrite (HB j ltac:(rewrite length_le4; exact Hj)). apply nth_error_le4_le8. exact Hj.
Qed.

(* [comment removed for export] *)
Definition reg_of_tag (d : sdesc) (t : int) : option int :=
  match find (fun rv : int * fval => (vtag (snd rv) =? t)%uint63) (sd_regs d) with
  | Some rv => Some (fst rv) | None => None end.

(* [comment removed for export] *)
Definition rho_of (K : i2consts) (d : sdesc) (x : Z -> word) (W : list (int * word)) (t : int) : word :=
  if (t =? 0)%uint63 then w0
  else if (t =? 1)%uint63 then wa (bv_unsigned (x 2) - to_Z (c_stack K))
  else match reg_of_tag d t with Some r => x (to_Z r) | None => wlookup W t end.

(* [comment removed for export] *)
Definition b60 : int := 1152921504606846976.   (* [comment removed for export] *)
Definition b46 : int := 70368744177664.        (* [comment removed for export] *)
Definition reg_idx_ok (r : int) : bool := ((1 <=? r) && (r <=? 31))%uint63.
Definition opq_tag_ok (t : int) : bool := ((2 <=? t) && (t <? b60))%uint63.
(* [comment removed for export] *)
Definition bytes_match (bs : list Z) (i0 : Z) (n : int) (w : w64) : bool :=
  forallb (fun j : int => ((n <=? j)%uint63
                           || match nth_error bs (Z.to_nat (i0 + to_Z j)) with
                              | Some b => (b =? to_Z (w_byte j w))%Z | None => false end)) ho_iseq8.
Definition val_src_ok (a n : int) (w : w64) (ab : Z * list Z) : bool :=
  ((fst ab <=? to_Z a)%Z) && bytes_match (snd ab) (to_Z a - fst ab) n w.

Definition fact_ok (K : i2consts) (d : sdesc) (S : ssrc) (f : hfact) : bool :=
  match f with
  | HReg r v =>
      reg_idx_ok r &&
      (if (vtag v =? 0)%uint63 then existsb (fun rc : Z * Z => ((fst rc =? to_Z r) && (wZ (vw v) =? snd rc))%Z) (s_cregs S)
       else if (vtag v =? 1)%uint63 then ((r =? 2)%uint63) && fval_eqb v (FV 1 (W64 0 (c_stack K)))
       else opq_tag_ok (vtag v) && fval_eqb v (FV (vtag v) w_zero)
            && match reg_of_tag d (vtag v) with Some r' => (r' =? r)%uint63 | None => false end)
  | HCell t a n w => ((t =? 0)%uint63) && ((1 <=? n)%uint63) && ((n <=? 8)%uint63) && existsb (val_src_ok a n w) (s_vals S)
  | HVal t a v =>
      ((t =? 0)%uint63) && opq_tag_ok (vtag v) && fval_eqb v (FV (vtag v) w_zero)
      && match reg_of_tag d (vtag v) with Some _ => false | None => true end
      && existsb (fun ant : Z * Z * int => ((fst (fst ant) =? to_Z a)%Z) && ((snd (fst ant) =? 8)%Z) && ((snd ant =? vtag v)%uint63)) (s_words S)
  | HBytes t a n v =>
      ((t =? 0)%uint63) && ((n <=? 8)%uint63) && opq_tag_ok (vtag v) && fval_eqb v (FV (vtag v) w_zero)
      && match reg_of_tag d (vtag v) with Some _ => false | None => true end
      && existsb (fun ant : Z * Z * int => ((fst (fst ant) =? to_Z a)%Z) && ((snd (fst ant) =? to_Z n)%Z) && ((snd ant =? vtag v)%uint63)) (s_words S)
  | HClear lo hi => existsb (fun lh : Z * Z => ((fst lh <=? to_Z lo) && (to_Z hi <=? snd lh))%Z) (s_clear S)
  | HRegion t lo len al => ((t =? 1) && (lo =? 0) && (len =? c_stack K) && (al =? 4))%uint63
  | HWr t off len => ((t =? 1) && (off =? 0) && (len =? c_stack K))%uint63
  | HDisj t1 lo1 len1 t2 lo2 len2 => ((t1 =? 0) && (t2 =? 1) && (lo2 =? 0) && (len1 <=? b46))%uint63
  | HZero _ _ _ => false
  end.

(* [comment removed for export] *)
Lemma existsb_In : forall {A} (f : A -> bool) l, existsb f l = true -> exists y, In y l /\ f y = true.
Proof. intros A f l H. apply existsb_exists in H. exact H. Qed.

Lemma opq_tag_ok_spec : forall t, opq_tag_ok t = true -> 2 <= to_Z t < 2 ^ 60 /\ (t =? 0)%uint63 = false /\ (t =? 1)%uint63 = false.
Proof.
  intros t H. unfold opq_tag_ok in H. apply andb_true_iff in H as [H2 H60].
  apply i_leb_le in H2. apply i_ltb_lt in H60. change (to_Z 2%uint63) with 2 in H2. change (to_Z b60) with (2 ^ 60) in H60.
  split; [slia|]. split; apply Uint63.eqb_false_spec; intros ->; [change (to_Z 0%uint63) with 0 in H2 | change (to_Z 1%uint63) with 1 in H2]; slia.
Qed.

(* [comment removed for export] *)
Lemma sword_bytes : forall m a n w j, sword m a n w -> (j < Z.to_nat n)%nat ->
  rview usegs m (wa (a + Z.of_nat j)) = nth_error (wbytes8 w) j.
Proof. intros m a n w j Hs Hj. rewrite wbytes8_le8. exact (Hs j Hj). Qed.

Lemma adr_wa : forall rho t z, adr rho t z = wa (bv_unsigned (rho t) + z).
Proof.
  intros rho t z. unfold adr, wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rget_ms0 : forall (x : Z -> word) Fr pc fc m rom (rr : reg) (r : int), ireg rr = r -> reg_idx_ok r = true ->
  Sem.rget (core_of (MS (mkRl (map x L31)) Fr pc fc None m rom)) rr = x (to_Z r).
Proof.
  intros x Fr pc fc m rom rr r Hi Hr. unfold reg_idx_ok in Hr. apply andb_true_iff in Hr as [H1 H31].
  apply i_leb_le in H1. apply i_leb_le in H31. change (to_Z 1%uint63) with 1 in H1. change (to_Z 31%uint63) with 31 in H31.
  unfold ireg in Hi. pose proof (bv_unsigned_in_range _ rr) as Hrng. change (bv_modulus 5) with 32 in Hrng.
  assert (Er : to_Z r = bv_unsigned rr).
  { rewrite <- Hi. apply toZ_of_Z_small. slia. }
  assert (Hx0 : is_x0 rr = false). { unfold is_x0. apply Z.eqb_neq. slia. }
  unfold Sem.rget. rewrite Hx0. cbn [core_of c_regs ms_regs].
  rewrite (reg_get_mkRl _ _ Hx0). rewrite nth_map_L31 by slia. rewrite Er. f_equal. slia.
Qed.

(* [comment removed for export] *)
Section Start.
  Context {HCEIL : HeapCeil}.
  Variable K : i2consts.
  Variable d : sdesc.
  Variable S : ssrc.
  Variable x : Z -> word.
  Variable W : list (int * word).
  Variables (Fr : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Let rho := rho_of K d x W.
  Let sp := bv_unsigned (x 2).
  Let cs := to_Z (c_stack K).
  Let ms0 := MS (mkRl (map x L31)) Fr (Z_to_bv 64 (to_Z (sd_pc d))) fc None m (seg_rom usegs).

  Hypothesis HK : K_ok K = true.
  Hypothesis HS : ssrc_holds S x W m.
  Hypothesis Hstk : stk usegs m lo sp.
  Hypothesis Hlo : hceil <= lo /\ lo <= sp - cs.
  Hypothesis Hsp63 : sp < 2 ^ 63.
  Hypothesis Hsp16 : sp mod 16 = 0.

  Lemma rho0 : rho 0%uint63 = Z_to_bv 64 0.
  Proof. reflexivity. Qed.
  Lemma rho1 : rho 1%uint63 = wa (sp - cs).
  Proof. reflexivity. Qed.
  Lemma rho_reg : forall t r, (t =? 0)%uint63 = false -> (t =? 1)%uint63 = false -> reg_of_tag d t = Some r -> rho t = x (to_Z r).
  Proof. intros t r H0 H1 Hr. unfold rho, rho_of. rewrite H0, H1, Hr. reflexivity. Qed.
  Lemma rho_W : forall t, (t =? 0)%uint63 = false -> (t =? 1)%uint63 = false -> reg_of_tag d t = None -> rho t = wlookup W t.
  Proof. intros t H0 H1 Hr. unfold rho, rho_of. rewrite H0, H1, Hr. reflexivity. Qed.

  Lemma cs_facts : cs mod 16 = 0 /\ cs <= 2 ^ 40 /\ 0 <= cs.
  Proof.
    clear HS Hstk Hlo Hsp63 Hsp16.
    destruct (HK_err K HK) as (_ & _ & _ & _ & _ & _ & H16 & H40). pose proof (i63_range (c_stack K)).
    unfold cs. repeat split; try assumption. slia.
  Qed.

  Lemma sp_lo_facts : 0x7fff7f800000 <= sp - cs /\ 0 <= sp - cs /\ sp < 2 ^ 63.
  Proof. clear HS Hstk Hsp16. hcb. destruct cs_facts as (_ & _ & ?). destruct Hlo. repeat split; slia. Qed.

  Lemma rho1_unsigned : bv_unsigned (rho 1%uint63) = sp - cs.
  Proof.
    clear HS Hstk Hsp16.
    rewrite rho1. unfold wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    destruct sp_lo_facts as (? & ? & ?). destruct cs_facts as (_ & _ & ?). change (bv_modulus 64) with (2 ^ 64). slia.
  Qed.

  Lemma adr0 : forall z, adr rho 0%uint63 z = wa z.
  Proof. clear HS Hstk Hlo Hsp63 Hsp16. intros z. exact (ho_adr0 rho rho0 z). Qed.

  Lemma words_src : forall (a : int) (n : Z) t,
    existsb (fun ant : Z * Z * int => ((fst (fst ant) =? to_Z a)%Z) && ((snd (fst ant) =? n)%Z) && ((snd ant =? t)%uint63)) (s_words S) = true ->
    sword m (to_Z a) n (wlookup W t).
  Proof.
    clear Hstk Hlo Hsp63 Hsp16. intros a n t H. destruct HS as (_ & _ & _ & HW). apply existsb_In in H as [[[a' n'] t'] [Hin Hb]]. cbn [fst snd] in Hb.
    rewrite !andb_true_iff in Hb. destruct Hb as [[Ha Hn] Ht].
    apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hn. apply Uint63.eqb_spec in Ht. subst.
    rewrite Forall_forall in HW. exact (HW _ Hin).
  Qed.

  Lemma dv_opq : forall v, opq_tag_ok (vtag v) = true -> fval_eqb v (FV (vtag v) w_zero) = true ->
    dv rho v = rho (vtag v).
  Proof.
    clear HS Hstk Hlo Hsp63 Hsp16. intros v Ho Hv. apply fval_eqb_eq in Hv. destruct (opq_tag_ok_spec _ Ho) as (Ht & _ & _).
    rewrite Hv at 1. apply dv_tag_zero. slia.
  Qed.

  (* [comment removed for export] *)
  Lemma start_fact : forall f, fact_ok K d S f = true -> hholds usegs rho ms0 f.
  Proof.
    pose proof HS as HS'. destruct HS' as (HXc & HV & HC & HW).
    intros f Hf. destruct f as [t off n w | t off v | t off n v | t off len | clo chi | t off len | r v | t rlo len al | t1 lo1 len1 t2 lo2 len2];
      cbn [fact_ok] in Hf; try discriminate Hf; cbn [hholds].
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[[Ht Hn1] Hn8] Hex].
      apply Uint63.eqb_spec in Ht. subst t. apply i_leb_le in Hn1. apply i_leb_le in Hn8.
      change (to_Z 1%uint63) with 1 in Hn1. change (to_Z 8%uint63) with 8 in Hn8.
      apply existsb_In in Hex as [[a0 bs] [Hin Hok]]. unfold val_src_ok in Hok. cbn [fst snd] in Hok.
      rewrite !andb_true_iff in Hok. destruct Hok as [Hle Hbm]. apply Z.leb_le in Hle.
      pose proof (i63_range off). pose proof (i63_range n).
      rewrite Forall_forall in HV. specialize (HV _ Hin). cbn [fst snd] in HV.
      intros j Hj. rewrite adr0. change (ms_mem ms0) with m.
      unfold bytes_match in Hbm. rewrite forallb_forall in Hbm.
      set (jj := of_Z (Z.of_nat j)).
      assert (Ejj : to_Z jj = Z.of_nat j) by (subst jj; apply toZ_of_Z_small; slia).
      specialize (Hbm jj ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)).
      apply orb_true_iff in Hbm. destruct Hbm as [Hbm|Hbm]; [apply i_leb_le in Hbm; slia|].
      rewrite Ejj in Hbm.
      destruct (nth_error bs (Z.to_nat (to_Z off - a0 + Z.of_nat j))) as [b|] eqn:En; [|discriminate].
      apply Z.eqb_eq in Hbm. subst b.
      pose proof (proj1 (nth_error_Some bs _) ltac:(rewrite En; discriminate)) as Hlt.
      specialize (HV _ Hlt). rewrite (nth_error_nth _ _ _ En) in HV.
      replace (a0 + Z.of_nat (Z.to_nat (to_Z off - a0 + Z.of_nat j))) with (to_Z off + Z.of_nat j) in HV by slia.
      change (rview usegs m (wa (to_Z off + Z.of_nat j))) with (mrd usegs m (wa (to_Z off + Z.of_nat j))). rewrite HV.
      symmetry. replace j with (Z.to_nat (to_Z jj)) at 1 by slia. apply w_bytes_nth_byte. slia.
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[[[Ht Ho] Hv] Hr] Hex].
      apply Uint63.eqb_spec in Ht. subst t. pose proof (opq_tag_ok_spec _ Ho) as (Htg & E0 & E1).
      destruct (reg_of_tag d (vtag v)) eqn:Er; [discriminate|].
      intros j Hj. rewrite adr0. change (ms_mem ms0) with m. rewrite (dv_opq v Ho Hv), (rho_W _ E0 E1 Er).
      apply (sword_bytes m (to_Z off) 8); [exact (words_src _ _ _ Hex) | exact Hj].
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[[[[Ht Hn] Ho] Hv] Hr] Hex].
      apply Uint63.eqb_spec in Ht. subst t. pose proof (opq_tag_ok_spec _ Ho) as (Htg & E0 & E1).
      destruct (reg_of_tag d (vtag v)) eqn:Er; [discriminate|].
      intros j Hj. rewrite adr0. change (ms_mem ms0) with m. rewrite (dv_opq v Ho Hv), (rho_W _ E0 E1 Er).
      apply (sword_bytes m (to_Z off) (to_Z n)); [exact (words_src _ _ _ Hex) | exact Hj].
    - (* [comment removed for export] *)
      apply existsb_In in Hf as [[lo0 hi0] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      rewrite Forall_forall in HC. specialize (HC _ Hin). cbn [fst snd] in HC.
      intros a Ha. change (ms_mem ms0) with m. change (Z_to_bv 64 a) with (wa a). apply HC. slia.
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[Ht Ho] Hl].
      apply Uint63.eqb_spec in Ht. apply Uint63.eqb_spec in Ho. apply Uint63.eqb_spec in Hl. subst t off len.
      intros j Hj. change (ms_mem ms0) with m. rewrite adr_wa, rho1_unsigned. change (to_Z 0%uint63) with 0.
      destruct Hstk as (_ & _ & Hs). destruct Hlo. apply (Hs (sp - cs + (0 + j))). unfold cs in *. slia.
    - (* [comment removed for export] *)
      apply andb_true_iff in Hf as [Hr Hf]. intros rr Hrr. unfold ms0. rewrite (rget_ms0 x Fr _ fc m _ rr r Hrr Hr).
      destruct (vtag v =? 0)%uint63 eqn:E0.
      + apply existsb_In in Hf as [[r0 c] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_true_iff in Hb as [Hr0 Hv].
        apply Z.eqb_eq in Hr0. apply Z.eqb_eq in Hv. apply Uint63.eqb_spec in E0.
        rewrite Forall_forall in HXc. specialize (HXc _ Hin). cbn [fst snd] in HXc. rewrite <- Hr0, HXc, <- Hv.
        destruct v as [tv wv]. cbn [vtag vw] in *. subst tv. rewrite (fk_dv_conc rho wv rho0). reflexivity.
      + destruct (vtag v =? 1)%uint63 eqn:E1.
        * apply andb_true_iff in Hf as [Hr2 Hv]. apply Uint63.eqb_spec in Hr2. subst r. apply fval_eqb_eq in Hv. rewrite Hv.
          rewrite (fk_dv_plain rho) by (cbn [vtag]; change (to_Z 1%uint63) with 1; slia). cbn [vtag vw]. rewrite rho1.
          change (to_Z 2%uint63) with 2. unfold wa, wbv. rewrite wZ_even_top by reflexivity. cbn [wlo].
          apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod.
          fold cs. replace (sp - cs + cs) with sp by slia. symmetry. apply Z.mod_small. subst sp. apply bv_unsigned_in_range.
        * rewrite !andb_true_iff in Hf. destruct Hf as [[Ho Hv] Hrt].
          destruct (reg_of_tag d (vtag v)) as [r'|] eqn:Er; [|discriminate]. apply Uint63.eqb_spec in Hrt. subst r'.
          rewrite (dv_opq v Ho Hv). symmetry. exact (rho_reg _ _ E0 E1 Er).
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[[Ht Hl] Hn] Ha].
      apply Uint63.eqb_spec in Ht. apply Uint63.eqb_spec in Hl. apply Uint63.eqb_spec in Hn. apply Uint63.eqb_spec in Ha. subst.
      unfold region_ok. cbn [rg_len rg_lo rg_align rg_clo rg_chi rg_kind rkind_ok]. rewrite rho1_unsigned.
      destruct sp_lo_facts as (? & ? & ?). destruct cs_facts as (? & ? & ?). fold cs.
      change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4.
      change (to_Z clo_dflt) with 0. change (to_Z chi_dflt) with (2 ^ 63 - 1). change (2 ^ 4) with 16.
      repeat split; slia.
    - (* [comment removed for export] *)
      rewrite !andb_true_iff in Hf. destruct Hf as [[[H1 H2] H3] H4].
      apply Uint63.eqb_spec in H1. apply Uint63.eqb_spec in H2. apply Uint63.eqb_spec in H3. apply i_leb_le in H4. subst.
      change (to_Z b46) with (2 ^ 46) in H4. rewrite rho0, rho1_unsigned. left.
      change (bv_unsigned (Z_to_bv 64 0)) with 0. change (to_Z 0%uint63) with 0. destruct sp_lo_facts. slia.
  Qed.

  Lemma start_facts : forall facts, forallb (fact_ok K d S) facts = true -> Forall (hholds usegs rho ms0) facts.
  Proof.
    intros facts H. rewrite forallb_forall in H. apply Forall_forall. intros f Hf. apply start_fact. exact (H f Hf).
  Qed.

  (* [comment removed for export] *)
  Theorem start_Rn : forall IMX facts n,
    image_ok usegs IMX -> image_wr_ok IMX ->
    ho_check2 IMX facts d = true -> forallb (fact_tags_lt n) facts = true ->
    forallb (fact_ok K d S) facts = true ->
    Rn usegs IMX n rho (state_of d) ms0.
  Proof.
    intros IMX facts n HIMX HWRX Hho Hlt Hok.
    apply (handoff_Rn2 usegs IMX HIMX HWRX facts d n rho ms0 Hho Hlt rho0 (start_facts facts Hok)); reflexivity.
  Qed.
End Start.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RO_LO : Z := 0x10000.
Definition RO_HI : Z := 0x2c5000.
Definition ro_seg_cell (a : int) : bool := ((RO_LO <=? to_Z a) && (to_Z a + 8 <=? RO_HI))%Z.
Definition K_roc_ok (K : i2consts) : bool :=
  forallb (fun ac : int * cell => xw_cell_ok (fst ac) || ro_seg_cell (fst ac)
                                  || (to_Z (fst ac) =? RGOT_SSP)%Z || (to_Z (fst ac) =? RSSP_GUARD)%Z) (c_ro K).

(* [comment removed for export] *)
Lemma ref_find_segment_ro : forall z, 0x10000 <= z -> z + 1 <= 0x2c5000 ->
  exists seg, find_segment usegs z 1 = Some seg /\ seg_writable seg = false.
Proof.
  intros z Hlo Hhi. unfold usegs, RefMemImage.Ref.loaded_segments, Ubsan.M.loaded_segments,
    Ubsan.Ubsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 65536%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 860160%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 925696%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 1978368%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + 1) (65536 + 860160)); cbn [andb]; try lia.
  - eexists. split; [reflexivity|]. vm_compute. reflexivity.
  - destruct (Z.leb_spec0 925696 z); destruct (Z.leb_spec0 (z + 1) (925696 + 1978368)); cbn [andb]; try lia.
    eexists. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Lemma ref_ro_addr_true : forall u, 0x10000 <= u -> u + 1 <= 0x2c5000 -> ro_addr usegs (wa u) = true.
Proof.
  intros u Hlo Hhi. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (ref_find_segment_ro u Hlo Hhi) as (seg & -> & Hw). rewrite Hw. reflexivity.
Qed.

Lemma mem_inv_ro_none : forall m u, mem_inv usegs m -> 0x10000 <= u -> u + 1 <= 0x2c5000 -> m (wa u) = None.
Proof.
  intros m u Hinv Hlo Hhi. destruct (m (wa u)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite ref_ro_addr_true in Hro by assumption. discriminate.
Qed.

Lemma rw_C8_mrd : forall m A w j, rw_cells usegs m A [C8 w] -> (j < 8)%nat ->
  mrd usegs m (wa (A + Z.of_nat j)) = nth_error (le8 w) j.
Proof.
  intros m A w j [[_ (_ & _ & HB)] _] Hj. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply HB. rewrite length_le8. exact Hj.
Qed.

Section Const.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable K : i2consts.
  Hypothesis HHx : heap_sr_hyps_x H.

  Theorem ro_const_intro : K_roc_ok K = true -> ro_const H K.
  Proof.
    intros Hk s LB m s' LB' m' HR HR' Hinv Hinv' a c Hin Hxw j Hj.
    unfold K_roc_ok in Hk. rewrite forallb_forall in Hk. specialize (Hk _ Hin). cbn [fst] in Hk.
    rewrite Hxw in Hk. cbn [orb] in Hk. rewrite !orb_true_iff in Hk.
    destruct HHx as (_ & _ & _ & _ & Hst & _). destruct (Hst _ _ _ HR) as (_ & Hg & _ & Hc). destruct (Hst _ _ _ HR') as (_ & Hg' & _ & Hc').
    change (rview usegs m' (wa (to_Z a + j))) with (mrd usegs m' (wa (to_Z a + j))).
    change (rview usegs m (wa (to_Z a + j))) with (mrd usegs m (wa (to_Z a + j))).
    destruct Hk as [[Hro | Hgot] | Hssp].
    - unfold ro_seg_cell, RO_LO, RO_HI in Hro. apply andb_true_iff in Hro as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      unfold mrd. rewrite (mem_inv_ro_none m _ Hinv), (mem_inv_ro_none m' _ Hinv'); [reflexivity | slia | slia | slia | slia].
    - apply Z.eqb_eq in Hgot. rewrite Hgot. replace j with (Z.of_nat (Z.to_nat j)) by slia.
      rewrite (rw_C8_mrd m _ _ _ Hg), (rw_C8_mrd m' _ _ _ Hg') by slia. reflexivity.
    - apply Z.eqb_eq in Hssp. rewrite Hssp. replace j with (Z.of_nat (Z.to_nat j)) by slia.
      rewrite (rw_C8_mrd m _ _ _ Hc), (rw_C8_mrd m' _ _ _ Hc') by slia. reflexivity.
  Qed.
End Const.

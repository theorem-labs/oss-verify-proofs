(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition RFresh : option expr := None.
Definition RVal (e : expr) : option expr := Some e.
Definition NoReads : list (option expr) := [].
Definition NoDirs : list bool := [].
Definition NoPins : list (Z * expr) := [].
Definition NoBounds : bounds := [].
Definition NoVals : list Z := [].
Definition NoRegions : list (region * bool) := [].
Definition NoViews : list aview := [].
Definition WR (s : expr) (lo hi : Z) : region * bool := (RG s lo hi, true).
Definition RD (s : expr) (lo hi : Z) : region * bool := (RG s lo hi, false).


Definition reg_of_nat (n : nat) : reg :=
  match n with
  | 1%nat => (1%bv : reg)
  | 2%nat => (2%bv : reg)
  | 3%nat => (3%bv : reg)
  | 4%nat => (4%bv : reg)
  | 5%nat => (5%bv : reg)
  | 6%nat => (6%bv : reg)
  | 7%nat => (7%bv : reg)
  | 8%nat => (8%bv : reg)
  | 9%nat => (9%bv : reg)
  | 10%nat => (10%bv : reg)
  | 11%nat => (11%bv : reg)
  | 12%nat => (12%bv : reg)
  | 13%nat => (13%bv : reg)
  | 14%nat => (14%bv : reg)
  | 15%nat => (15%bv : reg)
  | 16%nat => (16%bv : reg)
  | 17%nat => (17%bv : reg)
  | 18%nat => (18%bv : reg)
  | 19%nat => (19%bv : reg)
  | 20%nat => (20%bv : reg)
  | 21%nat => (21%bv : reg)
  | 22%nat => (22%bv : reg)
  | 23%nat => (23%bv : reg)
  | 24%nat => (24%bv : reg)
  | 25%nat => (25%bv : reg)
  | 26%nat => (26%bv : reg)
  | 27%nat => (27%bv : reg)
  | 28%nat => (28%bv : reg)
  | 29%nat => (29%bv : reg)
  | 30%nat => (30%bv : reg)
  | 31%nat => (31%bv : reg)
  | _ => (0%bv : reg)
  end.

Definition mkE (regs : bvmap 5 word) (vals : list Z)
           (F1 : nat -> Z -> Z) (F2 : nat -> Z -> Z -> Z) : venv :=
  VEnv (fun n => if Nat.ltb n 32 then bv_unsigned (getr regs (reg_of_nat n))
                 else nth (n - 32) vals 0) F1 F2.

Definition F0 : nat -> Z -> Z := fun _ _ => 0.
Definition F0' : nat -> Z -> Z -> Z := fun _ _ _ => 0.

Lemma reg_of_nat_ridx : forall r : reg, reg_of_nat (ridx r) = r.
Proof.
  intro r. apply bv_eq. unfold ridx. pose proof (u5_range r) as Hr.
  set (z := bv_unsigned r) in *. clearbody z.
  assert (H : exists n, (n < 32)%nat /\ z = Z.of_nat n) by (exists (Z.to_nat z); lia).
  destruct H as (n & Hn & ->). rewrite Nat2Z.id.
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma nth_sr_id : forall n, (n < 32)%nat -> nth n sr_id (ELit 0) = EVar n.
Proof. intros n Hn. do 32 (destruct n as [|n]; [reflexivity|]). lia. Qed.

Lemma regs_ok_mkE : forall regs vals F1 F2, regs_ok (mkE regs vals F1 F2) sr_id regs.
Proof.
  intros regs vals F1 F2 r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    rewrite nth_sr_id by exact Hlt. cbn [ed mkE vv].
    assert (Hl : Nat.ltb (ridx r) 32 = true) by (apply Nat.ltb_lt; exact Hlt).
    rewrite Hl, reg_of_nat_ridx. symmetry. apply zw_u.
Qed.

Lemma vars_ok_mkE_id : forall regs vals F1 F2, vars_ok (mkE regs vals F1 F2) vb_id.
Proof.
  intros regs vals F1 F2 n b H. apply blookup_vb_id in H as [-> Hn].
  cbn [mkE vv]. assert (Hl : Nat.ltb n 32 = true) by (apply Nat.ltb_lt; exact Hn).
  rewrite Hl. apply u64_range.
Qed.

Fixpoint sr_pins (ps : list (Z * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (Z.to_nat r) e)
  end.

Fixpoint pins_ok (E : venv) (regs : bvmap 5 word) (ps : list (Z * expr)) : Prop :=
  match ps with
  | [] => True
  | (r, e) :: rest => getr regs (reg_of_nat (Z.to_nat r)) = zw (ed E e) /\ pins_ok E regs rest
  end.

Lemma ridx_reg_of_nat : forall n, (n < 32)%nat -> ridx (reg_of_nat n) = n.
Proof.
  intros n Hn. do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Fixpoint pins_wf (ps : list (Z * expr)) : bool :=
  match ps with
  | [] => true
  | (r, _) :: rest => (0 <=? r) && (r <? 32) && pins_wf rest
  end.

Lemma regs_ok_pins : forall E ps sr regs,
  pins_wf ps = true -> regs_ok E sr regs -> pins_ok E regs ps -> regs_ok E (sr_pins ps sr) regs.
Proof.
  intros E ps. induction ps as [|[r e] rest IH]; intros sr regs Hwf Hr Hp; [exact Hr|].
  cbn [pins_wf] in Hwf. apply andb_prop in Hwf as [Hwf Hrest]. apply andb_prop in Hwf as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  destruct Hp as [Hh Ht]. cbn [sr_pins]. apply IH; [exact Hrest| |exact Ht].
  rewrite <- (ridx_reg_of_nat (Z.to_nat r)) by lia.
  apply regs_ok_pin; [exact Hr | exact Hh].
Qed.

Fixpoint vb_goals (E : venv) (vbx : bounds) : Prop :=
  match vbx with
  | [] => True
  | (n, b) :: rest => (0 <= vv E n < b) /\ vb_goals E rest
  end.

Lemma vars_ok_app : forall E vbx vb,
  vb_goals E vbx -> vars_ok E vb -> vars_ok E (vbx ++ vb).
Proof.
  intros E vbx vb Hg Hv. induction vbx as [|[n b] rest IH]; [exact Hv|].
  destruct Hg as [Hnb Hrest]. intros m c Hl. cbn [blookup app] in Hl.
  destruct (Nat.eqb n m) eqn:Hnm.
  - apply Nat.eqb_eq in Hnm. subst m. injection Hl as <-. exact Hnb.
  - exact (IH Hrest m c Hl).
Qed.

Fixpoint fb_goals (E : venv) (fb : bounds) : Prop :=
  match fb with
  | [] => True
  | (f, b) :: rest => (forall x, 0 <= vf1 E f x < b) /\ fb_goals E rest
  end.

Lemma funs_ok_of_goals : forall E fb, fb_goals E fb -> funs_ok E fb.
Proof.
  intros E fb. induction fb as [|[f b] rest IH]; intros Hg g c x Hl; cbn [blookup] in Hl.
  - discriminate.
  - destruct Hg as [Hfb Hrest]. destruct (Nat.eqb f g) eqn:Hfg.
    + apply Nat.eqb_eq in Hfg. subst g. injection Hl as <-. apply Hfb.
    + exact (IH Hrest g c x Hl).
Qed.

Definition rg_goal (segs : list MemImageType.Segment) (mem : word -> option byte) (E : venv)
           (rw : region * bool) : Prop :=
  if snd rw then sok_ok segs mem E (fst rw) else flat_ok E (fst rw).

Fixpoint rg_goals (segs : list MemImageType.Segment) (mem : word -> option byte) (E : venv)
         (decl : list (region * bool)) : Prop :=
  match decl with
  | [] => True
  | rw :: rest => rg_goal segs mem E rw /\ rg_goals segs mem E rest
  end.

Lemma rg_goals_Forall : forall segs mem E decl,
  rg_goals segs mem E decl -> Forall (rg_goal segs mem E) decl.
Proof.
  intros segs mem E decl. induction decl as [|r rest IH]; cbn; intros H; constructor; [apply H | apply IH; apply H].
Qed.

Definition decl_flat (decl : list (region * bool)) : list region := map fst decl.
Definition decl_sok (decl : list (region * bool)) : list region := map fst (List.filter snd decl).

Definition entry_state (pc : Z) (pins : list (Z * expr)) (vbx : bounds) (nvals : nat)
           (decl : list (region * bool)) : sym_state :=
  SS (ELit pc) (sr_pins pins sr_id) [] (32 + nvals)%nat (vbx ++ vb_id)
     (decl_flat decl) [] (decl_sok decl) [].

Lemma entry_st_ok : forall segs regs vals F1 F2 pc (pcw : word) pins vbx np decl mem rom,
  pins_wf pins = true ->
  pcw = zw pc ->
  pins_ok (mkE regs vals F1 F2) regs pins ->
  vb_goals (mkE regs vals F1 F2) vbx ->
  rg_goals segs mem (mkE regs vals F1 F2) decl ->
  st_ok segs (mkE regs vals F1 F2) mem rom (entry_state pc pins vbx np decl)
        (mkst regs pcw mem rom).
Proof.
  intros segs regs vals F1 F2 pc pcw pins vbx np decl mem rom Hwf -> Hp Hvb Hrg.
  apply rg_goals_Forall in Hrg. rewrite Forall_forall in Hrg.
  exists regs. split; [reflexivity|]. split.
  - cbn [s_regs entry_state]. apply regs_ok_pins; [exact Hwf | apply regs_ok_mkE | exact Hp].
  - unfold inv_ok; cbn [s_vb s_flat s_dj s_sok s_log s_rd entry_state].
    split; [apply vars_ok_app; [exact Hvb | apply vars_ok_mkE_id]|].
    split.
    { apply Forall_forall. intros r Hr. unfold decl_flat in Hr. apply in_map_iff in Hr as ([r' w] & <- & Hin).
      specialize (Hrg _ Hin). unfold rg_goal in Hrg. cbn [fst snd] in Hrg |- *.
      destruct w; [exact (proj1 Hrg) | exact Hrg]. }
    split; [constructor|]. split.
    { apply Forall_forall. intros r Hr. unfold decl_sok in Hr. apply in_map_iff in Hr as ([r' w] & <- & Hin).
      apply List.filter_In in Hin as [Hin Hw]. cbn [snd] in Hw. subst w.
      specialize (Hrg _ Hin). exact Hrg. }
    split; [constructor|]. split; [constructor | constructor].
Qed.


Fixpoint reg_in (r : reg) (l : list reg) : bool :=
  match l with [] => false | x :: t => bv_eqb r x || reg_in r t end.

Lemma reg_in_false : forall r l, Forall (fun x => r <> x) l -> reg_in r l = false.
Proof.
  intros r l H. induction H as [|x t Hx Ht IH]; [reflexivity|]. cbn [reg_in].
  rewrite IH, (bv_eqb_neq r x Hx). reflexivity.
Qed.

Fixpoint changed_aux (sr0 sr : list expr) (k : nat) (n : nat) : list reg :=
  match n with
  | O => []
  | S n' =>
      (if expr_eqb (nth k sr (ELit 0)) (nth k sr0 (ELit 0)) then [] else [reg_of_nat k])
      ++ changed_aux sr0 sr (S k) n'
  end.

Definition changed (sr0 sr : list expr) : list reg := changed_aux sr0 sr 1 31.

Lemma reg_in_app : forall r l1 l2, reg_in r (l1 ++ l2) = false ->
  reg_in r l1 = false /\ reg_in r l2 = false.
Proof.
  intros r l1 l2 Hl. induction l1 as [|x t IHl]; cbn [reg_in app] in Hl |- *; [auto|].
  apply orb_false_elim in Hl as [H1 H2]. destruct (IHl H2) as [H3 H4].
  rewrite H1, H3. auto.
Qed.

Lemma changed_aux_spec : forall sr0 sr n k i,
  (k <= i < k + n)%nat ->
  reg_in (reg_of_nat i) (changed_aux sr0 sr k n) = false ->
  nth i sr (ELit 0) = nth i sr0 (ELit 0).
Proof.
  intros sr0 sr n. induction n as [|n IH]; intros k i Hi H; [lia|].
  cbn [changed_aux] in H. apply reg_in_app in H as [H1 H2].
  destruct (Nat.eq_dec i k) as [->|Hne].
  - destruct (expr_eqb (nth k sr (ELit 0)) (nth k sr0 (ELit 0))) eqn:He.
    + apply expr_eqb_eq. exact He.
    + cbn [reg_in app] in H1. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate.
  - apply (IH (S k) i); [lia | exact H2].
Qed.

Lemma regs_ok_frame : forall E sr0 sr regs R,
  regs_ok E sr0 regs -> regs_ok E sr R ->
  forall r : reg, reg_in r (changed sr0 sr) = false -> getr R r = getr regs r.
Proof.
  intros E sr0 sr regs R H0 HR r Hin.
  destruct (bv_eqb r 0) eqn:Hr0.
  { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r.
    unfold getr. cbn. reflexivity. }
  rewrite (HR r), (H0 r). unfold sr_get. rewrite Hr0.
  pose proof (ridx_range r) as Hlt.
  assert (Hnz : (1 <= ridx r)%nat).
  { unfold ridx. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0.
    pose proof (u5_range r). change (bv_unsigned (0%bv : reg)) with 0 in Hr0. lia. }
  rewrite <- (reg_of_nat_ridx r) in Hin.
  rewrite (changed_aux_spec sr0 sr 31 1 (ridx r)); [reflexivity | lia | exact Hin].
Qed.

Fixpoint incl_b (l1 l2 : list reg) : bool :=
  match l1 with [] => true | x :: t => reg_in x l2 && incl_b t l2 end.

Lemma reg_in_true_eq : forall r x l, reg_in x l = true -> reg_in r l = false -> bv_eqb r x = false.
Proof.
  intros r x l. induction l as [|y t IH]; cbn [reg_in]; intros Hx Hr; [discriminate|].
  apply orb_false_elim in Hr as [H1 H2]. apply orb_prop in Hx as [Hx|Hx]; [|exact (IH Hx H2)].
  unfold bv_eqb in *. apply Z.eqb_eq in Hx. apply Z.eqb_neq in H1. apply Z.eqb_neq. lia.
Qed.

Lemma reg_in_sub : forall r l1 l2, incl_b l1 l2 = true -> reg_in r l2 = false -> reg_in r l1 = false.
Proof.
  intros r l1 l2. induction l1 as [|x t IH]; cbn [incl_b reg_in]; intros Hi Hr; [reflexivity|].
  apply andb_prop in Hi as [H1 H2]. rewrite (IH H2 Hr), (reg_in_true_eq r x l2 H1 Hr). reflexivity.
Qed.


Lemma symex_reg_eq : forall E sr R (r : reg) v,
  regs_ok E sr R -> zw (ed E (sr_get sr r)) = v -> getr R r = v.
Proof. intros E sr R r v HR <-. apply HR. Qed.


Theorem symex_sound :
  forall segs C fuel dirs rds pins vbx decl regs pvals rvals F1 F2 (pc : Z) (pcw : word) mem rom ss' scs,
  run segs C fuel true dirs rds (entry_state pc pins vbx (length pvals) decl) [] = (ss', scs) ->
  pins_wf pins = true ->
  pcw = zw pc ->
  let E := mkE regs (pvals ++ rvals) F1 F2 in
  scs_denot segs mem E scs ->
  pins_ok E regs pins ->
  vb_goals E vbx ->
  fb_goals E (c_fb C) ->
  rg_goals segs mem E decl ->
  exists R,
    regs_ok E (s_regs ss') R
    /\ (forall r : reg, reg_in r (changed (sr_pins pins sr_id) (s_regs ss')) = false ->
                       getr R r = getr regs r)
    /\ inv_ok segs mem E ss'
    /\ msteps segs (mkst regs pcw mem rom)
              (mkst R (zw (ed E (s_pc ss'))) (mem_denot E mem (s_log ss')) rom).
Proof.
  intros segs C fuel dirs rds pins vbx decl regs pvals rvals F1 F2 pc pcw mem rom ss' scs
    Hrun Hwf Hpc E Hsc Hpins Hvb Hfb Hrg.
  pose proof (entry_st_ok segs regs (pvals ++ rvals) F1 F2 pc pcw pins vbx (length pvals) decl mem rom
                Hwf Hpc Hpins Hvb Hrg) as Hst.
  destruct (run_ex segs C fuel true dirs rds _ [] ss' scs E mem rom
              (mkst regs pcw mem rom) Hrun Hsc (funs_ok_of_goals _ _ Hfb) Hst)
    as (R & HR & Hinv & Hms).
  exists R. split; [exact HR|]. split.
  - apply (regs_ok_frame E _ _ regs R); [|exact HR].
    apply regs_ok_pins; [exact Hwf | apply regs_ok_mkE | exact Hpins].
  - split; [exact Hinv | exact Hms].
Qed.


Lemma symex_ret : forall ra : word,
  Z_to_bv 64 (Z.land (bv_unsigned ra + 0) (-2)) = ra ->
  zw (Z.land (bv_unsigned ra) (-2)) = zw (bv_unsigned ra).
Proof. intros ra H. rewrite Z.add_0_r in H. rewrite zw_u. exact H. Qed.


Lemma symex_read1 : forall segs mem P (d : list byte) (i : nat) a v,
  rdn segs mem (Z_to_bv 64 P) (length d) = Some d ->
  (i < length d)%nat ->
  a = P + Z.of_nat i ->
  v = bv_unsigned (nth i d (Z_to_bv 8 0)) ->
  exists bs, rdn segs mem (zw a) 1 = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros segs mem P d i a v Hd Hi -> ->.
  exists [nth i d (Z_to_bv 8 0)]. split.
  - rewrite zw_add_nat. exact (rdn_nth segs mem (length d) (Z_to_bv 64 P) d i Hd Hi).
  - apply SymExec.bytes_le_to_Z_1.
Qed.

Lemma symex_read_sub : forall segs mem P (d : list byte) (k n : nat) a v,
  rdn segs mem (Z_to_bv 64 P) (length d) = Some d ->
  (k + n <= length d)%nat ->
  a = P + Z.of_nat k ->
  v = bytes_le_to_Z (firstn n (skipn k d)) ->
  exists bs, rdn segs mem (zw a) n = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros segs mem P d k n a v Hd Hk -> ->.
  exists (firstn n (skipn k d)). split; [|reflexivity].
  rewrite zw_add_nat. exact (rdn_sub segs k (length d) (Z_to_bv 64 P) mem d n Hd Hk).
Qed.

Lemma symex_read_le : forall segs mem (a : Z) (n : nat) z v,
  rdn segs mem (zw a) n = Some (Z_to_le_bytes n z) ->
  v = z mod 2 ^ (8 * Z.of_nat n) ->
  exists bs, rdn segs mem (zw a) n = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros segs mem a n z v H ->. exists (Z_to_le_bytes n z). split; [exact H|].
  apply bytes_le_to_Z_of_Z.
Qed.

Lemma symex_read_w8 : forall segs mem (a : Z) (w : word) v,
  rdn segs mem (zw a) 8 = Some (word_to_le_bytes 8 w) ->
  v = bv_unsigned w ->
  exists bs, rdn segs mem (zw a) 8 = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros segs mem a w v H ->. exists (word_to_le_bytes 8 w). split; [exact H|].
  apply SeqExec.bytes_le_to_Z_8.
Qed.

Lemma symex_sok_defined : forall segs mem E s lo hi,
  0 <= ed E s + lo -> ed E s + hi <= 2 ^ 64 -> lo < hi ->
  (forall a : word, ed E s + lo <= bv_unsigned a < ed E s + hi -> mem a <> None) ->
  sok_ok segs mem E (RG s lo hi).
Proof.
  intros segs mem E s lo hi H0 H1 Hle Hdef. unfold sok_ok, flat_ok; cbn [r_s r_lo r_hi].
  split; [lia|]. split; [lia|].
  apply store_ok_of_all; rewrite u_zw_small by lia; [lia|].
  intros x Hx. unfold wview. destruct (mem x) as [b|] eqn:Hm; [discriminate|].
  exfalso. apply (Hdef x); [lia | exact Hm].
Qed.

Lemma symex_store_ok : forall segs mem (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (1 <= n)%nat ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> mem x <> None) ->
  RiscvSemantics.store_ok segs mem (zw a) n = true.
Proof.
  intros segs mem a n H0 H1 Hn Hdef.
  apply store_ok_of_all; rewrite u_zw_small by lia; [lia|].
  intros x Hx. unfold wview. destruct (mem x) as [b|] eqn:Hm; [discriminate|].
  exfalso. apply (Hdef x); [lia | exact Hm].
Qed.

Lemma Forall_of_rev : forall {A} (P : A -> Prop) (l : list A), Forall P (rev l) -> Forall P l.
Proof. intros A P l H. rewrite <- (rev_involutive l). apply Forall_rev. exact H. Qed.


End FXG.
Ltac symex_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @nil _ => constr:(0%nat)
  | cons _ ?t => let n := symex_len t in constr:(S n)
  | @cons _ _ ?t => let n := symex_len t in constr:(S n)
  end.
Ltac symex_closed t :=
  first [ StepTac.check_closed_term t
        | fail 100 "symex: argument" t "must be CLOSED syntax (use EVar/vals for symbolic values)" ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_cbn :=
  cbv beta iota delta [sc_denot br_ok flat_ok dj_ok sok_ok r_s r_lo r_hi];
  cbn [r_s r_lo r_hi e_s e_k e_w e_v
       ed vv vf1 vf2 mkE reg_of_nat F0 F0'
       Nat.ltb Nat.leb Nat.sub nth app
       mem_denot msize_bytes];
  rewrite ?Z.add_0_r.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Ltac symex_recast H T' :=
  let T := type of H in
  let H' := fresh "__rc" in
  pose proof (((fun x : T' => x) : T -> T') H) as H';
  clear H; rename H' into H.
Ltac symex_cbn_in H :=
  let T := type of H in
  let T1 := eval cbv beta iota delta [sc_denot br_ok flat_ok dj_ok sok_ok r_s r_lo r_hi] in T in
  let T2 := eval cbn [r_s r_lo r_hi e_s e_k e_w e_v
       ed vv vf1 vf2 mkE reg_of_nat F0 F0'
       Nat.ltb Nat.leb Nat.sub nth app
       mem_denot msize_bytes] in T1 in
  symex_recast H T2;
  rewrite ?Z.add_0_r in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_pc_lit_in H :=
  repeat match type of H with
  | context [mkst _ (zw ?z) _ _] =>
      lazymatch z with
      | Zpos _ => let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
                  replace (zw z) with l in H by (apply bv_eq; vm_compute; reflexivity)
      | Z0 => let l := constr:(@BV 64 0 ltac:(vm_compute; exact I)) in
              replace (zw z) with l in H by (apply bv_eq; vm_compute; reflexivity)
      end
  end;
  rewrite ?zw_u in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_pc_lit :=
  repeat match goal with
  | |- context [mkst _ (zw ?z) _ _] =>
      lazymatch z with
      | Zpos _ => let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
                  replace (zw z) with l by (apply bv_eq; vm_compute; reflexivity)
      | Z0 => let l := constr:(@BV 64 0 ltac:(vm_compute; exact I)) in
              replace (zw z) with l by (apply bv_eq; vm_compute; reflexivity)
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_store_auto :=
  apply symex_store_ok;
  [ lia | lia | lia
  | let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx;
    match goal with
    | W : forall y : word, _ -> ?m y <> None |- ?m' x <> None => apply W; lia
    | W : _ |- _ => apply W; lia
    end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_ret_auto :=
  lazymatch goal with
  | |- zw (Z.land (bv_unsigned ?g) (-2)) = zw (bv_unsigned ?g) =>
      first [ match goal with Hr : ret_ok g |- _ => apply symex_ret; exact Hr end
            | match goal with
              | H : g = ?ra, Hr : ret_ok ?ra |- _ => rewrite H; apply symex_ret; exact Hr
              | H : reg_get ?rs ?r = ?ra, Hr : ret_ok ?ra |- _ =>
                  progress (change g with (reg_get rs r)); rewrite H; apply symex_ret; exact Hr
              end ]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_read_hook := fail.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_read_auto :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = ?v =>
      match goal with
      | H : rdn sg m (zw a) n = Some (Z_to_le_bytes n _) |- _ =>
          eapply symex_read_le; [exact H | rewrite ?Z.mod_small by lia; lia]
      | H : rdn sg m (Z_to_bv 64 a) n = Some (Z_to_le_bytes n _) |- _ =>
          eapply symex_read_le; [exact H | rewrite ?Z.mod_small by lia; lia]
      | H : rdn sg m (zw a) 8%nat = Some (word_to_le_bytes 8 _) |- _ =>
          eapply symex_read_w8; [exact H | reflexivity]
      | H : rdn sg m (Z_to_bv 64 a) 8%nat = Some (word_to_le_bytes 8 _) |- _ =>
          eapply symex_read_w8; [exact H | reflexivity]
      | H : rdn sg m (Z_to_bv 64 ?P) (length ?d) = Some ?d |- _ =>
          lazymatch v with
          | bv_unsigned (nth ?i d _) =>
              eapply (symex_read1 sg m P d i); [exact H | | lia | reflexivity]; lia
          end
      | _ => symex_read_hook
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_sok_auto :=
  split; [lia|]; split; [lia|];
  repeat match goal with
         | |- context [Z.to_nat ?e] =>
             let n := eval vm_compute in (Z.to_nat e) in change (Z.to_nat e) with n
         end;
  symex_store_auto.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_arith_prop P :=
  lazymatch P with
  | ?A /\ ?B => symex_arith_prop A; symex_arith_prop B
  | ?A \/ ?B => symex_arith_prop A; symex_arith_prop B
  | ~ ?A => symex_arith_prop A
  | @eq Z _ _ => idtac | (_ <= _)%Z => idtac | (_ < _)%Z => idtac | (_ >= _)%Z => idtac | (_ > _)%Z => idtac
  | @eq nat _ _ => idtac | (_ <= _)%nat => idtac | (_ < _)%nat => idtac
  | False => idtac | True => idtac
  end.
Ltac symex_auto :=
  try solve [ assumption
            | reflexivity
            | (lazymatch goal with |- ?G => symex_arith_prop G end); lia
            | symex_ret_auto
            | symex_read_auto
            | symex_store_auto
            | symex_sok_auto
            | lia
            | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_decl2 segs C fuel dirs rds pins vbx decl nv pcz :=
  let ss1 := eval vm_compute in
     (fst (run segs C fuel true dirs rds (entry_state pcz pins vbx nv decl) [])) in
  eval vm_compute in (map (fun r => (r, false)) (rev (s_flat ss1))
                      ++ map (fun r => (r, true)) (rev (s_sok ss1))).
Ltac symex_dbg segs C fuel dirs rds pins vbx decl pvals ms :=
  lazymatch ms with
  | mkst ?regs ?pcw ?mem ?rom =>
    let pcz := lazymatch pcw with
               | zw ?z => z | Z_to_bv 64 ?z => z
               | _ => StepTac.vm_eval (bv_unsigned pcw) end in
    let nv := symex_len pvals in
    let decl2 := symex_decl2 segs C fuel dirs rds pins vbx decl nv pcz in
    let res := eval vm_compute in (run segs C fuel true dirs rds (entry_state pcz pins vbx nv decl2) []) in
    idtac res
  end.
Ltac symex segs C fuel dirs rds pins vbx decl pvals rvals F1 F2 ms R HR Hfr Hms :=
  symex_closed C; symex_closed dirs; symex_closed rds; symex_closed pins; symex_closed vbx;
  symex_closed decl;
  lazymatch ms with
  | mkst ?regs ?pcw ?mem ?rom =>
    let pcz := lazymatch pcw with
               | zw ?z => z | Z_to_bv 64 ?z => z
               | _ => StepTac.vm_eval (bv_unsigned pcw) end in
    let nv := symex_len pvals in
    let sok := symex_decl2 segs C fuel dirs rds pins vbx decl nv pcz in
    let ss0 := constr:(entry_state pcz pins vbx nv sok) in
    let res := eval vm_compute in (run segs C fuel true dirs rds ss0 []) in
    lazymatch res with
    | (?ss1, ?scs) =>
      let scsr := eval vm_compute in (rev scs) in
      let EE := constr:(mkE regs (pvals ++ rvals) F1 F2) in
      let Hsc := fresh "Hsc" in
      let Hpins := fresh "Hpins" in
      let Hvb := fresh "Hvb" in
      let Hfb := fresh "Hfb" in
      let Hsok := fresh "Hsok" in
      let Hinv := fresh "Hinv" in
      assert (Hsc : scs_denot segs mem EE scsr);
      [ unfold scs_denot;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        symex_cbn; symex_auto
      | let Hsc0 := fresh "Hsc0" in
        assert (Hsc0 : scs_denot segs mem EE scs)
          by (unfold scs_denot in Hsc |- *; apply Forall_of_rev; exact Hsc);
        clear Hsc; rename Hsc0 into Hsc;
        assert (Hpins : pins_ok EE regs pins);
        [ cbn [pins_ok];
          repeat match goal with
                 | |- context [reg_of_nat (Z.to_nat ?z)] =>
                     let n := eval vm_compute in (reg_of_nat (Z.to_nat z)) in
                     change (reg_of_nat (Z.to_nat z)) with n
                 end;
          symex_cbn;
          repeat match goal with |- _ /\ _ => split end; try exact I; symex_auto
        | assert (Hvb : vb_goals EE vbx);
          [ cbn [vb_goals]; symex_cbn;
            repeat match goal with |- _ /\ _ => split end; try exact I; symex_auto
          | let fbv := eval vm_compute in (c_fb C) in
            assert (Hfb : fb_goals EE fbv);
            [ cbn [fb_goals]; symex_cbn;
              repeat match goal with |- _ /\ _ => split end; try exact I;
              try (intros; symex_cbn; solve [auto | split; auto | lia]); symex_auto
            | assert (Hsok : rg_goals segs mem EE sok);
              [ cbn [rg_goals];
                repeat match goal with |- rg_goal _ _ _ _ /\ _ => split end; try exact I;
                unfold rg_goal; cbn [fst snd]; symex_cbn;
                repeat match goal with
                       | |- context [Z.to_nat ?e] =>
                           let n := eval vm_compute in (Z.to_nat e) in change (Z.to_nat e) with n
                       end;
                try (split; [lia|]); try (split; [lia|]); symex_auto
              | destruct (symex_sound segs C fuel dirs rds pins vbx sok regs pvals rvals F1 F2 pcz pcw mem rom
                          ss1 scs
                          ltac:(vm_compute; reflexivity)
                          ltac:(reflexivity)
                          ltac:(first [ reflexivity | apply bv_eq; vm_compute; reflexivity ])
                          Hsc Hpins Hvb Hfb Hsok)
                as (R & HR & Hfr & Hinv & Hms);
              clear Hsc Hpins Hvb Hfb Hsok;
              let ch := eval vm_compute in (changed (sr_pins pins sr_id) (s_regs ss1)) in
              change (changed (sr_pins pins sr_id) (s_regs ss1)) with ch in Hfr;
              cbn [s_regs s_pc s_log] in HR, Hms, Hinv;
              symex_cbn_in Hms; symex_pc_lit_in Hms
            ] ] ] ] ]
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Tactic Notation "symex_reg" constr(HR) constr(r) "as" ident(H) :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
      let e := eval vm_compute in (sr_get sr r) in
      let z := eval cbn [ed vv vf1 vf2 mkE reg_of_nat F0 F0' Nat.ltb Nat.leb Nat.sub nth app] in (ed E e) in
      assert (H : getr R r = zw z)
        by exact (@eq_trans word (getr R r) (zw (ed E (sr_get sr r))) (zw z)
                    (HR r) (@eq_refl word (zw z)));
      rewrite ?Z.add_0_r in H; rewrite ?zw_u in H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Tactic Notation "symex_frame" constr(Hfr) constr(r) "as" ident(H) :=
  lazymatch type of Hfr with
  | forall x : reg, reg_in x ?l = false -> getr ?R x = getr ?regs x =>
      assert (H : getr R r = getr regs r) by (apply Hfr; reflexivity)
  end.

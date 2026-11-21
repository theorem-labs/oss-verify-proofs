(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees FillWinModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 TreesRod6 TreesApi6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Lemma arr_fill_nat_S : forall {A} k (a : parr A) ofs v,
  arr_fill_nat a ofs (S k) v = arr_set (arr_fill_nat a ofs k v) (ofs + Z.of_nat k) v.
Proof.
  induction k as [|k IH]; intros a ofs v.
  - cbn [arr_fill_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [arr_fill_nat] in *. rewrite (IH (arr_set a ofs v) (ofs + 1) v). f_equal. lia.
Qed.

Definition zst (s : deflate_state) (t : tree_id) (k : nat) : deflate_state :=
  set_tree_fc s t (arr_fill_nat (tree_fc s t) 0 k 0).

Lemma zst_0 : forall s t, zst s t 0 = s.
Proof. intros s [| |]; destruct s; reflexivity. Qed.

Lemma zst_S : forall s t k,
  set_tree_fc (zst s t k) t (arr_set (tree_fc (zst s t k) t) (Z.of_nat k) (wrap16 0)) = zst s t (S k).
Proof.
  intros s t k. unfold zst. rewrite tree_fc_set_tree_fc, set_tree_fc_twice.
  rewrite arr_fill_nat_S. change (wrap16 0) with 0. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma zst_S' : forall s t k i, i = Z.of_nat k ->
  set_tree_fc (zst s t k) t (arr_set (tree_fc (zst s t k) t) i (wrap16 0)) = zst s t (S k).
Proof. intros s t k i ->. apply zst_S. Qed.

Lemma set_sym_next_tree_fc : forall s v a,
  set_tree_fc (set_sym_next s v) TL a = set_sym_next (set_tree_fc s TL a) v.
Proof. intros. destruct s; reflexivity. Qed.
Lemma tree_fc_set_sym_next : forall s v t, tree_fc (set_sym_next s v) t = tree_fc s t.
Proof. intros s v [| |]; reflexivity. Qed.
Lemma set_sym_next_opt_len : forall s a b,
  set_opt_len (set_sym_next s a) b = set_sym_next (set_opt_len s b) a.
Proof. intros. destruct s; reflexivity. Qed.
Lemma set_sym_next_static_len : forall s a b,
  set_static_len (set_sym_next s a) b = set_sym_next (set_static_len s b) a.
Proof. intros. destruct s; reflexivity. Qed.


Lemma init_block_eq6 : forall s,
  init_block s =
    let s3 := zst (zst (zst s TL 286) TD 30) TB 19 in
    let s4 := set_sym_next s3 0 in
    set_matches (set_static_len (set_opt_len
      (set_tree_fc s4 TL (arr_set (tree_fc s4 TL) 256 (wrap16 1))) 0) 0) 0.
Proof.
  intros s. cbv zeta.
  rewrite tree_fc_set_sym_next, set_sym_next_tree_fc, set_sym_next_opt_len, set_sym_next_static_len.
  unfold init_block, set_Freq, zst, arr_fill. cbn [set_tree_fc tree_fc].
  change (Z.to_nat L_CODES) with 286%nat. change (Z.to_nat D_CODES) with 30%nat.
  change (Z.to_nat BL_CODES) with 19%nat. change END_BLOCK with 256.
  match goal with |- ?a = ?b => constr_eq a b end.
  reflexivity.
Qed.

Lemma tr_init_eq6 : forall s, tr_init s = init_block (set_bi_valid (set_bi_buf s 0) 0).
Proof. intros s. unfold tr_init. cbv zeta. match goal with |- ?a = ?b => constr_eq a b end. reflexivity. Qed.


Definition IB_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Definition TI_CLOB : list reg := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition A6_INIT_BLOCK : Z := 0x1aaac.
Definition A6_TR_INIT : Z := 0x1aa50.

End FXG.
Abbreviation dsR_vals6 := (dsl_vals 168672 168704 168736).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition dvals6 (ds : deflate_state) (p : ds_ptrs) (S : Z) (d : Z * Z * Z * Z * Z * Z) : list Z :=
  let '(d1, d2, d3, d4, d5, d6) := d in
  list_upd (list_upd (list_upd (list_upd (list_upd (list_upd (dsR_vals6 ds p S) 37 d1) 39 d2) 40 d3) 42 d4) 43 d5) 45 d6.

Definition BRi6 (F : franges) (mem0 : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
           (m : word -> option byte) (s : deflate_state) : Prop :=
  (exists d, fields s6_segs m S dsl_layout (dvals6 s p S d))
  /\ dsl_arrays s6_segs m S s
  /\ tree_lens s
  /\ cells s6_segs m (p_pending_buf p) 1 1 PBL (arr_get (ds_pending_buf s))
  /\ arr_len (ds_pending_buf s) = PBL
  /\ agree_out F mem0 m
  /\ mapped m S dsl_SIZE /\ mapped m (p_pending_buf p) PBL
  /\ (forall x, mem0 x <> None -> m x <> None).


Section Walk.
Variables (F : franges) (mem0 : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ra : word).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
Hypothesis HFS : sub_franges F S dsl_SIZE.

Definition iC : cfg := CFG [] [] [EVar 1%nat] [0x1aac4; 0x1aad0] [].
Definition iVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 600)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption | lia
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; lia end
            | symex_read_auto ].

Local Ltac irun fuel pins dirs pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in iVB in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs iC fuel dirs NoReads pinsv vbv NoRegions pv NoVals F0 F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Definition IREGS (R : bvmap 5 word) : Prop :=
  getr R 10 = zw S /\ getr R 11 = zw (S + 5900) /\ getr R 12 = zw (S + 2047) /\ getr R 1 = ra.
Definition IPINS : list (Z * expr) :=
  [(10, EVar 32); (11, EAdd (EVar 32) (ELit 5900)); (12, EAdd (EVar 32) (ELit 2047))].

Local Ltac lreg HR :=
  let A := fresh "A" in
  lazymatch goal with |- getr ?R ?r = _ =>
    symex_reg HR r as A; rewrite A; first [reflexivity | assumption | f_equal; lia | rewrite zw_u; reflexivity]
  end.
Local Ltac ltregs HR := unfold IREGS; repeat split; lreg HR.


Local Ltac kof o :=
  lazymatch o with
  | 2904 => constr:(37%nat) | 2920 => constr:(39%nat) | 2928 => constr:(40%nat)
  | 2944 => constr:(42%nat) | 2952 => constr:(43%nat) | 2968 => constr:(45%nat)
  | 5936 => constr:(56%nat) | 5940 => constr:(57%nat)
  end.

Local Ltac fw_tower Hf M :=
  lazymatch M with
  | wbytes ?M1 (zw (S + 5944)) (Z_to_le_bytes ?w ?v) =>
      (* 1.4: `sw zero,8(a1)` at 0x1aa44 clears bi_used, a junk range of the layout *)
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6_segs M1 S dsl_layout ?vs |- _ =>
          let H2 := fresh "HF" in
          pose proof (fields_write_gap s6_segs M1 S dsl_layout vs dsl_SIZE 5944 (Z_to_le_bytes w v) H1 dsl_layout_within
                        ltac:(rewrite length_Z_to_le_bytes; vm_compute; reflexivity) ltac:(lia) ltac:(unfold dsl_SIZE; lia)
                        ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)) as H2;
          clear H1
      end
  | wbytes ?M1 (zw (S + ?o)) (Z_to_le_bytes ?w ?v) =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6_segs M1 S dsl_layout ?vs |- _ =>
          let k := kof o in
          let H2 := fresh "HF" in
          pose proof (fields_write_field s6_segs M1 S dsl_layout vs dsl_SIZE k o w v H1 eq_refl
                        ltac:(vm_compute; reflexivity) dsl_layout_within ltac:(lia) ltac:(unfold dsl_SIZE; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HF" in pose proof Hf as H
  end.

Lemma ti_pro : forall regs m ds,
  BRi6 F mem0 S p PBL m ds ->
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m1,
    msteps s6_segs (mkst regs (0x1aa50 : word) m s6_rom) (mkst R (0x1aac4 : word) m1 s6_rom)
    /\ BRm m1 (set_bi_valid (set_bi_buf ds 0) 0)
    /\ IREGS R /\ getr R 13 = zw (S + 212) /\ getr R 14 = zw (S + 1356)
    /\ (forall r : reg, reg_in r TI_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m ds HBI P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  destruct HBI as ((d & Hf) & Harr & HLn & Cpb & Hlen & Hag & HmS & HmP & Hgr).
  pose proof HmS as MS. unfold mapped, dsl_SIZE in MS.
  irun 60%nat [(10, EVar 32)] NoDirs [S; 0].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [| split; [ltregs HR | split; [lreg HR | split; [lreg HR | fr_weak Hfr]]]];
      fw_tower Hf M
  end.
  lazymatch goal with H1 : fields s6_segs ?M S dsl_layout ?vs |- BR _ _ _ _ _ _ _ _ _ ?M2 ?s1 =>
    assert (Ev : vs = dsR_vals6 s1 p S)
      by (destruct d as [[[[[d1 d2] d3] d4] d5] d6]; unfold dvals6, dsl_vals; cbn [list_upd]; dsred; reflexivity);
    rewrite Ev in H1
  end.
  (* the tower's last name alternates HF / HF0 with the store count (1.4 adds the bi_used store): match it *)
  unfold BR. split; [lazymatch goal with H : fields s6_segs _ S dsl_layout _ |- _ => exact H end|].
  split.
  { change (dsl_arrays s6_segs ?M S (set_bi_valid (set_bi_buf ds 0) 0)) with (dsl_arrays s6_segs M S ds).
    repeat (apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; [| lia | lia | lia | cbn; lia | cbn; lia]).
    exact Harr. }
  split; [unfold tree_lens in *; dsred; exact HLn|].
  split.
  { dsred. repeat (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]).
    exact Cpb. }
  split; [dsred; exact Hlen|].
  split.
  { repeat (apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; [| lia | cbn; lia | intros x Hx; apply HFS; unfold dsl_SIZE; cbn in Hx; lia]).
    exact Hag. }
  split; [repeat apply mapped_wbytes; exact HmS|]. split; [repeat apply mapped_wbytes; exact HmP|].
  intros x Hx. repeat apply wbytes_grows. exact (Hgr x Hx).
Qed.


Lemma ib_pro : forall regs m,
  mapped m S dsl_SIZE ->
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R,
    msteps s6_segs (mkst regs (0x1aaac : word) m s6_rom) (mkst R (0x1aac4 : word) m s6_rom)
    /\ IREGS R /\ getr R 13 = zw (S + 212) /\ getr R 14 = zw (S + 1356)
    /\ (forall r : reg, reg_in r IB_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m MS P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. unfold mapped, dsl_SIZE in MS.
  irun 20%nat [(10, EVar 32)] NoDirs [S; 0].
  exists R. split; [exact Hms|]. split; [ltregs HR|]. split; [lreg HR|]. split; [lreg HR|]. fr_weak Hfr.
Qed.


Definition ZSTEP (L X : word) (rc rE : reg) (t : tree_id) (n : Z) : Prop :=
  forall regs m s (k : nat),
    BRm m s -> Z.of_nat k < n ->
    getr regs rc = zw (S + toff t + 4 * Z.of_nat k) -> getr regs rE = zw (S + toff t + 4 * n) ->
    exists R m',
      msteps s6_segs (mkst regs L m s6_rom)
             (mkst R (if Z.of_nat k + 1 =? n then X else L) m' s6_rom)
      /\ BRm m' (set_tree_fc s t (arr_set (tree_fc s t) (Z.of_nat k) (wrap16 0)))
      /\ getr R rc = zw (S + toff t + 4 * (Z.of_nat k + 1))
      /\ (forall r : reg, reg_in r [rc]%bv = false -> getr R r = getr regs r).

Lemma zloop : forall L X rc rE t n, ZSTEP L X rc rE t n -> n = tsize t \/ n < tsize t -> rc <> rE ->
  forall j (k : nat) regs m s,
    (Z.of_nat k + Z.of_nat j = n)%Z -> (0 < j)%nat ->
    BRm m (zst s t k) ->
    getr regs rc = zw (S + toff t + 4 * Z.of_nat k) -> getr regs rE = zw (S + toff t + 4 * n) ->
    exists R m',
      msteps s6_segs (mkst regs L m s6_rom) (mkst R X m' s6_rom)
      /\ BRm m' (zst s t (k + j))
      /\ (forall r : reg, reg_in r [rc]%bv = false -> getr R r = getr regs r).
Proof.
  intros L X rc rE t n HST Hn Hce j. pose proof (toff_tsize t) as Ht.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'.
  induction j as [|j IH]; intros k regs m s Hkj Hj HB P15 PE; [lia|].
  destruct (HST regs m (zst s t k) k HB ltac:(lia) P15 PE) as (R1 & m1 & Hms1 & HB1 & Q15 & Hfr1).
  rewrite zst_S in HB1.
  destruct (Z.eqb_spec (Z.of_nat k + 1) n) as [E|NE].
  - exists R1, m1. split; [exact Hms1|]. split; [|exact Hfr1].
    replace (k + Datatypes.S j)%nat with (Datatypes.S k) by lia. exact HB1.
  - assert (QE : getr R1 rE = zw (S + toff t + 4 * n)).
    { rewrite (Hfr1 rE); [exact PE|]. apply reg_in_false. constructor; [|constructor]. intros ->. exact (Hce eq_refl). }
    destruct (IH (Datatypes.S k) R1 m1 s ltac:(lia) ltac:(lia) HB1
                ltac:(rewrite Q15; f_equal; lia) QE) as (R2 & m2 & Hms2 & HB2 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [replace (k + Datatypes.S j)%nat with (Datatypes.S k + j)%nat by lia; exact HB2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma zstep1 : ZSTEP (0x1aac4 : word) (0x1aad0 : word) 13%bv 14%bv TL 286.
Proof.
  intros regs m s k HB Hk P13 PE.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _). unfold mapped, dsl_SIZE in MS.
  cbn [toff tsize] in *.
  assert (FIN : forall R (pc : word) a,
    msteps s6_segs (mkst regs (0x1aac4 : word) m s6_rom) (mkst R pc (wbytes m (zw a) (Z_to_le_bytes 2 0)) s6_rom) ->
    a = S + 212 + 4 * Z.of_nat k ->
    getr R 13 = zw (S + 212 + 4 * (Z.of_nat k + 1)) -> (forall r : reg, reg_in r [13]%bv = false -> getr R r = getr regs r) ->
    exists R' m',
      msteps s6_segs (mkst regs (0x1aac4 : word) m s6_rom) (mkst R' pc m' s6_rom)
      /\ BRm m' (set_tree_fc s TL (arr_set (tree_fc s TL) (Z.of_nat k) (wrap16 0)))
      /\ getr R' 13 = zw (S + 212 + 4 * (Z.of_nat k + 1))
      /\ (forall r : reg, reg_in r [13]%bv = false -> getr R' r = getr regs r)).
  { intros R pc a Hms -> Q13 Hfr. exists R, (wbytes m (zw (S + 212 + 4 * Z.of_nat k)) (Z_to_le_bytes 2 0)).
    split; [exact Hms|]. split; [| split; [exact Q13 | exact Hfr]].
    change (S + 212) with (S + toff TL). apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | cbn; lia]. }
  destruct (Z.eqb_spec (Z.of_nat k + 1) 286) as [E|NE].
  - irun 20%nat [(13, EAdd (EVar 32) (EAdd (ELit 212) (EShl (EVar 33) 2))); (14, EAdd (EVar 32) (ELit 1356))]
         [false] [S; Z.of_nat k].
    lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes _ (zw ?a) _) _) =>
      apply (FIN R _ a Hms); [lia | lreg HR | fr_weak Hfr] end.
  - irun 20%nat [(13, EAdd (EVar 32) (EAdd (ELit 212) (EShl (EVar 33) 2))); (14, EAdd (EVar 32) (ELit 1356))]
         [true] [S; Z.of_nat k].
    lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes _ (zw ?a) _) _) =>
      apply (FIN R _ a Hms); [lia | lreg HR | fr_weak Hfr] end.
Qed.


Lemma BR_st_fc_at : forall m s t i v a,
  BRm m s -> 0 <= i < tsize t -> a = S + toff t + 4 * i ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_fc s t (arr_set (tree_fc s t) i (wrap16 v))).
Proof. intros m s t i v a HB Hi ->. apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); assumption. Qed.

Ltac ib_zero_step M1 t c base :=
  lazymatch goal with
  | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
      lazymatch s1 with
      | zst _ t _ => idtac
      | _ => rewrite <- (zst_0 s1 t) in H1
      end
  end;
  lazymatch goal with
  | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
      lazymatch s1 with
      | zst ?b t ?k =>
          let H2 := fresh "HBR" in
          let i := eval vm_compute in ((c - base) / 4)%Z in
          lazymatch goal with
          | |- context [wbytes M1 (zw ?a) (Z_to_le_bytes 2 ?v)] =>
              pose proof (BR_st_fc_at M1 s1 t i v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          | H : context [wbytes M1 (zw ?a) (Z_to_le_bytes 2 ?v)] |- _ =>
              pose proof (BR_st_fc_at M1 s1 t i v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          end;
          rewrite (zst_S' b t k i ltac:(reflexivity)) in H2; clear H1
      end
  end.

Ltac ib_fwd HB M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      ib_fwd HB M1;
      let c := lazymatch a with S + ?c1 + ?c2 => eval vm_compute in (c1 + c2)%Z | S + ?c1 => c1 end in
      let cz := eval vm_compute in (Z.leb 2504 c && Z.ltb c 2624)%bool in
      lazymatch cz with
      | true => ib_zero_step M1 TD c 2504%Z
      | false =>
      let cb := eval vm_compute in (Z.leb 2748 c && Z.ltb c 2824)%bool in
      lazymatch cb with
      | true => ib_zero_step M1 TB c 2748%Z
      | false =>
      lazymatch goal with
      | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
          let H2 := fresh "HBR" in
          lazymatch c with
          | 5900 => pose proof (BR_st_sym_next _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 1236 => pose proof (BR_st_fc_at M1 s1 TL 256 v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          | 5912 => pose proof (BR_st_opt_len _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 5920 => pose proof (BR_st_static_len _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 5928 => pose proof (BR_st_matches _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          end;
          clear H1
      end end end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Lemma ib_tail : forall regs m s,
  BRm m s -> IREGS regs ->
  exists R m',
    msteps s6_segs (mkst regs (0x1aad0 : word) m s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (let s3 := zst (zst s TD 30) TB 19 in
               let s4 := set_sym_next s3 0 in
               set_matches (set_static_len (set_opt_len
                 (set_tree_fc s4 TL (arr_set (tree_fc s4 TL) 256 (wrap16 1))) 0) 0) 0)
    /\ (forall r : reg, reg_in r IB_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m s HB (P10 & P11 & P12 & P1).
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _). unfold mapped, dsl_SIZE in MS.
  irun 80%nat IPINS NoDirs [S; 0].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      ib_fwd HB M; exists R, M; split; [rewrite <- P1; exact Hms|]; clear Hms;
      split; [cbv zeta; lazymatch goal with H : BR _ _ _ _ _ _ _ _ _ M _ |- _ => exact H end | fr_weak Hfr]
  end.
Qed.


Theorem init_block_run : forall regs m s,
  BRm m s -> getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1aaac : word) m s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (init_block s)
    /\ (forall r : reg, reg_in r IB_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m s HB P10 P1.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _).
  destruct (ib_pro regs m MS P10 P1) as (R1 & Hms1 & HI1 & A13 & A14 & Hfr1).
  rewrite <- (zst_0 s TL) in HB.
  destruct (zloop _ _ _ _ TL 286 zstep1 ltac:(cbn; lia) ltac:(discriminate) 286%nat 0%nat R1 m s ltac:(lia) ltac:(lia) HB
              ltac:(rewrite A13; f_equal; cbn; lia) ltac:(rewrite A14; f_equal; cbn; lia))
    as (R2 & m2 & Hms2 & HB2 & Hfr2).
  cbn [Nat.add] in HB2.
  assert (HI2 : IREGS R2).
  { destruct HI1 as (Q10 & Q11 & Q12 & Q1). unfold IREGS.
    rewrite (Hfr2 10%bv eq_refl), (Hfr2 11%bv eq_refl), (Hfr2 12%bv eq_refl), (Hfr2 1%bv eq_refl). auto. }
  destruct (ib_tail R2 m2 _ HB2 HI2) as (R3 & m3 & Hms3 & HB3 & Hfr3).
  exists R3, m3. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
  split; [rewrite init_block_eq6; exact HB3|].
  intros r Hr. rewrite (Hfr3 r Hr). rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity). exact (Hfr1 r Hr).
Qed.

Theorem tr_init_run : forall regs m ds,
  BRi6 F mem0 S p PBL m ds -> getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1aa50 : word) m s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (tr_init ds)
    /\ (forall r : reg, reg_in r TI_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m ds HBI P10 P1.
  destruct (ti_pro regs m ds HBI P10 P1) as (R1 & m1 & Hms1 & HB1 & HI1 & A13 & A14 & Hfr1).
  set (s0 := set_bi_valid (set_bi_buf ds 0) 0) in HB1.
  rewrite <- (zst_0 s0 TL) in HB1.
  destruct (zloop _ _ _ _ TL 286 zstep1 ltac:(cbn; lia) ltac:(discriminate) 286%nat 0%nat R1 m1 s0 ltac:(lia) ltac:(lia) HB1
              ltac:(rewrite A13; f_equal; cbn; lia) ltac:(rewrite A14; f_equal; cbn; lia))
    as (R2 & m2 & Hms2 & HB2 & Hfr2).
  cbn [Nat.add] in HB2.
  assert (HI2 : IREGS R2).
  { destruct HI1 as (Q10 & Q11 & Q12 & Q1). unfold IREGS.
    rewrite (Hfr2 10%bv eq_refl), (Hfr2 11%bv eq_refl), (Hfr2 12%bv eq_refl), (Hfr2 1%bv eq_refl). auto. }
  destruct (ib_tail R2 m2 _ HB2 HI2) as (R3 & m3 & Hms3 & HB3 & Hfr3).
  exists R3, m3. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
  split; [rewrite tr_init_eq6, init_block_eq6; exact HB3|].
  intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity). exact (Hfr1 r Hr).
Qed.

End Walk.


Definition init_block_run6 : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> BR6 F mem0 S p PBL mem ds ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_INIT_BLOCK) mem s6_rom) (mkst R ra m' s6_rom)
      /\ BR6 F mem0 S p PBL m' (init_block ds)
      /\ (forall r : reg, reg_in r IB_CLOB = false -> getr R r = getr regs r).

Definition tr_init_run6 : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> BRi6 F mem0 S p PBL mem ds ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_TR_INIT) mem s6_rom) (mkst R ra m' s6_rom)
      /\ BR6 F mem0 S p PBL m' (tr_init ds)
      /\ (forall r : reg, reg_in r TI_CLOB = false -> getr R r = getr regs r).

Theorem init_block_run6_ok : init_block_run6.
Proof.
  unfold init_block_run6, A6_INIT_BLOCK. intros F mem0 mem S p PBL ds ra regs HL HFS Hret HB P10 P1.
  replace (zw 0x1aaac) with (0x1aaac%bv : word) by (apply bv_eq; reflexivity).
  exact (init_block_run F mem0 S p PBL ra Hret HL HFS regs mem ds HB P10 P1).
Qed.

Theorem tr_init_run6_ok : tr_init_run6.
Proof.
  unfold tr_init_run6, A6_TR_INIT. intros F mem0 mem S p PBL ds ra regs HL HFS Hret HB P10 P1.
  replace (zw 0x1aa50) with (0x1aa50%bv : word) by (apply bv_eq; reflexivity).
  exact (tr_init_run F mem0 S p PBL ra Hret HL HFS regs mem ds HB P10 P1).
Qed.
End FXG.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import ASX. Import ASXS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod_add_multiple : forall a k m, 0 < m -> a mod m = 0 -> (k mod m = 0) -> (a + k) mod m = 0.
Proof.
  intros a k m Hm Ha Hk.
  rewrite Zplus_mod, Ha, Hk. cbn. apply Zmod_0_l.
Qed.

Lemma mod16_shift : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a + k) mod 16 = 0.
Proof. intros. apply mod_add_multiple; lia || assumption. Qed.

Lemma mod8_mod4_12 : forall c, c mod 8 = 0 -> (c + 12) mod 4 = 0.
Proof.
  intros c Hc.
  assert (H8 : c = 8 * (c / 8)) by (pose proof (Z_div_mod_eq_full c 8); lia).
  rewrite H8. replace (8 * (c / 8) + 12) with ((2 * (c / 8) + 3) * 4) by lia.
  apply Z_mod_mult.
Qed.

Lemma mod_sub_multiple : forall a k m, 0 < m -> a mod m = 0 -> k mod m = 0 -> (a - k) mod m = 0.
Proof.
  intros a k m Hm Ha Hk. rewrite Zminus_mod, Ha, Hk. cbn. apply Zmod_0_l.
Qed.

(* [comment removed for export] *)
Lemma alu_add_lit : forall (x : word) (k : Z), alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof.
  intros x k. rewrite alu_add. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_nowrap : forall (x : word) (k s : Z),
  bv_unsigned x = s -> 0 <= s -> 0 <= k -> s + k < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (s + k).
Proof.
  intros x k s Hx Hs Hk Hsk. apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
  change (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) with (low32 x + low32 (Z_to_bv 64 k))%bv.
  rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned, Hx.
  unfold bv_swrap. rewrite !bv_wrap32_mod, !bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  rewrite (Z.mod_small k) by lia. rewrite (Z.mod_small s) by lia. rewrite (Z.mod_small k) by lia.
  rewrite (Z.mod_small (s + k)) by lia. rewrite (Z.mod_small (s + k + 2 ^ 31)) by lia. f_equal. lia.
Qed.

Lemma addw1_lit : forall i, 0 <= i -> i + 1 < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (i + 1).
Proof. intros i H0 H1. apply (addw_nowrap (Z_to_bv 64 i) 1 i); try lia. apply u_small. lia. Qed.

(* [comment removed for export] *)
Lemma ext_val_zx_small : forall n (v : word),
  bv_unsigned v < 2 ^ (8 * Z.of_nat n) -> ext_val false 0 n v = v.
Proof.
  intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r, Z.mod_small by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ext_val_zx4_lit : forall z, 0 <= z < 2 ^ 32 -> ext_val false 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply ext_val_zx_small. rewrite u_small by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma writable_sub : forall mem lo n lo' n',
  writable segs mem lo n -> lo <= lo' -> 0 < n' -> lo' + n' <= lo + n ->
  writable segs mem lo' n'.
Proof.
  intros mem lo n lo' n' (H0 & Hn & Hhi & Hst) H1 H2 H3.
  split; [lia|]. split; [lia|]. split; [lia|].
  apply (store_ok_sub segs mem (Z_to_bv 64 lo) (Z_to_bv 64 lo') (Z.to_nat n) (Z.to_nat n'));
    rewrite ?u_small by lia; rewrite ?Z2Nat.id by lia; try lia. exact Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regions_incl (rs rs' : list (word * Z)) : Prop :=
  forall b n, In (b, n) rs ->
    exists b' n', In (b', n') rs' /\ bv_unsigned b' <= bv_unsigned b /\ bv_unsigned b + n <= bv_unsigned b' + n'.

Lemma outside_In : forall a rs b n, outside a rs -> In (b, n) rs -> ~ in_rng a b n.
Proof.
  intros a rs. induction rs as [|[b0 n0] rs IH]; cbn [outside In]; intros b n Ho Hin; [destruct Hin|].
  destruct Ho as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | exact (IH _ _ H2 Hin)].
Qed.

Lemma outside_of_In : forall a rs, (forall b n, In (b, n) rs -> ~ in_rng a b n) -> outside a rs.
Proof.
  intros a rs. induction rs as [|[b0 n0] rs IH]; cbn [outside]; intros H; [exact I|].
  split; [apply H; left; reflexivity | apply IH; intros b n Hin; apply H; right; exact Hin].
Qed.

Lemma frame_mod_incl : forall mem mem' rs rs',
  regions_incl rs rs' -> frame_mod mem mem' rs -> frame_mod mem mem' rs'.
Proof.
  intros mem mem' rs rs' Hincl Hf. eapply frame_mod_weaken; [|exact Hf].
  intros a Ho. apply outside_of_In. intros b n Hin Hrng.
  destruct (Hincl b n Hin) as (b' & n' & Hin' & H1 & H2).
  apply (outside_In a rs' b' n' Ho Hin'). unfold in_rng in *. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_mod_grow1 : forall mem mem' (b b' : word) n n',
  bv_unsigned b' <= bv_unsigned b -> bv_unsigned b + n <= bv_unsigned b' + n' ->
  frame_mod mem mem' [(b, n)] -> frame_mod mem mem' [(b', n')].
Proof.
  intros mem mem' b b' n n' H1 H2. apply frame_mod_incl.
  intros b0 n0 [Heq|[]]. injection Heq as <- <-. exists b', n'. split; [left; reflexivity| lia].
Qed.

Lemma frame_mod_in2l : forall mem mem' (b b1 b2 : word) n n1 n2,
  bv_unsigned b1 <= bv_unsigned b -> bv_unsigned b + n <= bv_unsigned b1 + n1 ->
  frame_mod mem mem' [(b, n)] -> frame_mod mem mem' [(b1, n1); (b2, n2)].
Proof.
  intros mem mem' b b1 b2 n n1 n2 H1 H2. apply frame_mod_incl.
  intros b0 n0 [Heq|[]]. injection Heq as <- <-. exists b1, n1. split; [left; reflexivity| lia].
Qed.

Lemma frame_mod_in2r : forall mem mem' (b b1 b2 : word) n n1 n2,
  bv_unsigned b2 <= bv_unsigned b -> bv_unsigned b + n <= bv_unsigned b2 + n2 ->
  frame_mod mem mem' [(b, n)] -> frame_mod mem mem' [(b1, n1); (b2, n2)].
Proof.
  intros mem mem' b b1 b2 n n1 n2 H1 H2. apply frame_mod_incl.
  intros b0 n0 [Heq|[]]. injection Heq as <- <-. exists b2, n2. split; [right; left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_app : forall mem n1 n2 (a : word) bs1 bs2,
  rdn segs mem a n1 = Some bs1 ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat n1)) n2 = Some bs2 ->
  rdn segs mem a (n1 + n2) = Some (bs1 ++ bs2).
Proof.
  intros mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
  - cbn [rdn] in H1. injection H1 as <-. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H2.
    cbn [Nat.add app]. exact H2.
  - change (S n1 + n2)%nat with (S (n1 + n2)). cbn [rdn] in H1 |- *.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
    destruct (rdn segs mem (a + 1)%bv n1) as [rest|] eqn:Hr; [|discriminate].
    injection H1 as <-.
    rewrite (IH n2 (a + 1)%bv rest bs2 Hr); [reflexivity|].
    replace (Z_to_bv 64 (bv_unsigned (a + 1)%bv + Z.of_nat n1)) with (Z_to_bv 64 (bv_unsigned a + Z.of_nat (S n1))); [exact H2|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned, !bv_wrap64_mod.
    change (bv_unsigned (1 : word)) with 1.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma cell_of_rdn : forall mem a (n : nat) bs,
  rdn segs mem (Z_to_bv 64 a) n = Some bs -> (n <= 8)%nat ->
  exists x, cell segs mem a n x.
Proof.
  intros mem a n bs Hr Hn. exists (Z_to_bv 64 (bytes_le_to_Z bs)). unfold cell.
  rewrite word_to_le_bytes_of_lez; [exact Hr | exact (rdn_length _ _ _ _ _ Hr) | exact Hn].
Qed.

(* [comment removed for export] *)
Lemma nth_repeat_zero : forall n j, nth j (repeat (Z_to_bv 8 0) n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n. induction n as [|n IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.

Lemma word_to_le_bytes_zero : forall n, (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) n.
Proof.
  intros n Hn.
  do 9 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma rdn_zeros : forall mem a (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (n <= 8)%nat ->
  (forall i, 0 <= i < Z.of_nat n -> mem (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
  rdn segs mem (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 0)).
Proof.
  intros mem a n H0 Hhi Hn Hz. rewrite word_to_le_bytes_zero by exact Hn.
  destruct (Nat.eq_dec n 0) as [->|Hnz]; [reflexivity|].
  apply rdn_pointwise.
  - apply repeat_length.
  - rewrite u_small by lia. lia.
  - intros j Hj. rewrite u_small by lia. rewrite nth_repeat_zero. apply Hz. lia.
Qed.

Lemma cell_zeros : forall mem a (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (n <= 8)%nat ->
  (forall i, 0 <= i < Z.of_nat n -> mem (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
  cell segs mem a n (Z_to_bv 64 0).
Proof. intros. unfold cell. apply rdn_zeros; assumption. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fregs_ok_pin : forall E sfr fr (r : reg) e,
  fregs_ok E sfr fr -> reg_get fr r = edenot E e -> fregs_ok E (sr_upd sfr (ridx r) e) fr.
Proof.
  intros E sfr fr r e Hf Hv r'. unfold sfr_get. rewrite nth_sr_upd.
  destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
  - apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
  - pose proof (Hf r') as H. unfold sfr_get in H. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint sr_upds (sr : list expr) (l : list (reg * expr)) : list expr :=
  match l with
  | [] => sr
  | (r, e) :: rest => sr_upds (sr_upd sr (ridx r) e) rest
  end.

Lemma regs_ok_pins : forall E l sr R,
  regs_ok E sr R -> Forall (fun p => getr R (fst p) = edenot E (snd p)) l -> regs_ok E (sr_upds sr l) R.
Proof.
  intros E l. induction l as [|[r e] l IH]; intros sr R Hsr Hl; [exact Hsr|].
  cbn [sr_upds]. apply Forall_cons_iff in Hl as [H1 H2]. cbn [fst snd] in H1.
  apply IH; [| exact H2]. apply regs_ok_pin; [exact Hsr | exact H1].
Qed.

Lemma fregs_ok_pins : forall E l sfr FR,
  fregs_ok E sfr FR -> Forall (fun p => reg_get FR (fst p) = edenot E (snd p)) l -> fregs_ok E (sr_upds sfr l) FR.
Proof.
  intros E l. induction l as [|[r e] l IH]; intros sfr FR Hs Hl; [exact Hs|].
  cbn [sr_upds]. apply Forall_cons_iff in Hl as [H1 H2]. cbn [fst snd] in H1.
  apply IH; [| exact H2]. apply fregs_ok_pin; [exact Hs | exact H1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lift_to H L :=
  lazymatch type of H with
  | regs_ok ?E0 ?sr ?R =>
      env_parts E0 ltac:(fun V ebs =>
      first [ constr_eq V L
            | lazymatch L with
              | ?L1 ++ ?x =>
                  lift_to H L1;
                  let H' := fresh "Hlift" in
                  pose proof (env_app_regs L1 x ebs sr R ltac:(reflexivity) H) as H';
                  clear H; rename H' into H
              end ])
  | fregs_ok ?E0 ?sfr ?FR =>
      env_parts E0 ltac:(fun V ebs =>
      first [ constr_eq V L
            | lazymatch L with
              | ?L1 ++ ?x =>
                  lift_to H L1;
                  let H' := fresh "Hlift" in
                  pose proof (env_app_fregs L1 x ebs sfr FR ltac:(reflexivity) H) as H';
                  clear H; rename H' into H
              end ])
  | know_ok ?segs ?E0 ?M ?kn =>
      env_parts E0 ltac:(fun V ebs =>
      first [ constr_eq V L
            | lazymatch L with
              | ?L1 ++ ?x =>
                  lift_to H L1;
                  let H' := fresh "Hlift" in
                  pose proof (env_app_know segs L1 x ebs M kn ltac:(reflexivity) H) as H';
                  clear H; rename H' into H
              end ])
  end.

(* [comment removed for export] *)
Ltac lift_id H HR :=
  unfold id in H;
  lazymatch type of HR with
  | regs_ok ?E1 _ _ => env_parts E1 ltac:(fun L _ => lift_to H L)
  | fregs_ok ?E1 _ _ => env_parts E1 ltac:(fun L _ => lift_to H L)
  end;
  lazymatch type of H with ?T => change (id T) in H end.

(* [comment removed for export] *)
Ltac env_extend_with HR HF HK ws :=
  lazymatch type of HR with
  | regs_ok ?E0 ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr ?FR =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
        env_parts E0 ltac:(fun V ebs =>
        let HR' := fresh "HR" in let HF' := fresh "HF" in let HK' := fresh "HK" in
        pose proof (env_app_regs V ws ebs sr R ltac:(reflexivity) HR) as HR';
        pose proof (env_app_fregs V ws ebs sfr FR ltac:(reflexivity) HF) as HF';
        pose proof (env_app_know segs V ws ebs M kn ltac:(reflexivity) HK) as HK';
        clear HR HF HK; rename HR' into HR; rename HF' into HF; rename HK' into HK)
    end
   end
  end.

Tactic Notation "env_extend" constr(ws) :=
  match goal with
  | HR : regs_ok _ _ _, HF : fregs_ok _ _ _, HK : know_ok _ _ _ _ |- _ =>
      env_extend_with HR HF HK ws
  end.

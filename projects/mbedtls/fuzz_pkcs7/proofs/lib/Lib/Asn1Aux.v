(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX AStep.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_1_mod : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_3_mod : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_7_mod : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_15_mod : forall x, Z.land x 15 = x mod 16.
Proof. intros x. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite bv_swrap_small; [reflexivity|]. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.

(* [comment removed for export] *)
Ltac ub_false K :=
  exfalso; rewrite ?unsigned_lit in K by (clear_disj; lia);
  rewrite ?land_7_mod, ?land_3_mod, ?land_1_mod, ?land_15_mod in K; clear_disj; lia.

(* [comment removed for export] *)
Lemma byte_at : forall (bs : list byte) (i : Z),
  0 <= i -> i < Z.of_nat (length bs) -> exists b, nth_error bs (Z.to_nat i) = Some b.
Proof.
  intros bs i Hi Hl. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.
(* [comment removed for export] *)
Ltac get_byte bs i b NB :=
  destruct (byte_at bs i ltac:(clear_disj; lia) ltac:(clear_disj; lia)) as [b NB].

(* [comment removed for export] *)
Ltac read_at HBUF NB i RD :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    pose proof (u8ro_read sg mx _ _ i _ _ HBUF NB ltac:(clear_disj; lia) eq_refl) as RD end.

(* [comment removed for export] *)
Tactic Notation "callx" tactic3(apptac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ apptac | post_call segs m ]
  end.



(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mentions_goal_var T :=
  match goal with
  | x : Z |- _ => lazymatch T with context [x] => lazymatch goal with |- context [x] => idtac end end
  | x : bv _ |- _ => lazymatch T with context [x] => lazymatch goal with |- context [x] => idtac end end
  end.
Ltac prune_disj :=
  repeat match goal with H : ?A \/ ?B |- _ => tryif mentions_goal_var (A \/ B) then fail else clear H end.
Ltac slia ::= first [ exact I | prune_disj; lia | split; [ prune_disj; lia | exact I ] ].
(* [comment removed for export] *)
Ltac plia := prune_disj; lia.

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.
Tactic Notation "callx_sp" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ apptac
      | (* [comment removed for export] *)
        lazymatch goal with |- forall x, ?P x -> _ => let h := head_of P in try unfold h end;
        rewrite ?(unsigned_lit e) by plia; post_call segs m ]
  end.

Ltac fin_goal :=
  lazymatch goal with
  | |- Z_to_bv _ ?x = Z_to_bv _ ?r =>
      first [ lazymatch x with
              | context [Z.b2z ?bb] =>
                  lazymatch bb with true => idtac | false => idtac end;
                  (* [comment removed for export] *)
                  let v := eval vm_compute in (let u := x mod 2^64 in if u <? 2^63 then u else u - 2^64) in
                  unify r v; apply bv_eq; vm_compute; reflexivity
              end
            | reflexivity ]
  | |- @eq (bv _) ?a _ => first [ reflexivity | match goal with H : a = _ |- _ => exact H end ]
  | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
  | |- ro_cells _ ?m ?A _ => match goal with H : ro_cells _ m A _ |- _ => exact H end
  | |- bytes_at _ ?m ?A _ => match goal with H : bytes_at _ m A _ |- _ => exact H end
  | |- u8arr _ ?m ?A _ => match goal with H : u8arr _ m A _ |- _ => exact H end
  | |- stk _ ?m _ _ => match goal with H : stk _ m _ _ |- _ => exact H end
  | |- statics_ok _ _ ?m => match goal with H : statics_ok _ _ m |- _ => exact H end
  | |- _ => prune_disj; lia
  end.
Ltac fin := finish; try fin_goal.

(* [comment removed for export] *)
Lemma lor_shl8_low : forall b r, 0 <= b < 256 -> 0 <= r -> Z_to_bv 8 (Z.lor b (Z.shiftl r 8)) = Z_to_bv 8 b.
Proof.
  intros b r Hb Hr. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8). cbv beta.
  change (bv_wrap 8 b) with (b mod 2^8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r r (i - 8)) by lia. apply orb_false_r.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_shl8_high : forall b r, 0 <= b < 256 -> 0 <= r -> Z.shiftr (Z.lor b (Z.shiftl r 8)) 8 = r.
Proof.
  intros b r Hb Hr. rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
  rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|].
  apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. pose proof (bytes_le_to_Z_nonneg bs).
  f_equal.
  - rewrite lor_shl8_low by (cbn in Hb; lia). apply definitions.Z_to_bv_bv_unsigned.
  - rewrite lor_shl8_high by (cbn in Hb; lia). exact IH.
Qed.

Lemma le8_le_bytes_to_word : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_CB8_C8 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_le_bytes_to_word by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac cb8_to_c8 H pre :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A _ => apply (rw_cells_CB8_C8 sg mx A pre) in H; cbn [app] in H
  end.

(* [comment removed for export] *)
Lemma lxor_small_eq : forall a b, 0 <= a -> 0 <= b -> Z.lxor a b < 1 -> a = b.
Proof. intros a b Ha Hb H. apply Z.lxor_eq_0_iff. pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)). lia. Qed.
Lemma lxor_eq_small : forall a, Z.lxor a a < 1.
Proof. intros a. rewrite Z.lxor_nilpotent. lia. Qed.

(* [comment removed for export] *)
Definition alloc_ceiling_pos {L : heap_layout} : 4096 < alloc_ceiling := @HeapIface.alloc_ceiling_pos L.

(* [comment removed for export] *)
Lemma lor_shl8_byte : forall v b, 0 <= v -> 0 <= b < 256 -> Z.lor (Z.shiftl v 8) b = v * 256 + b.
Proof.
  intros v b Hv Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + replace (v * 256) with (Z.shiftl v 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    + replace b with (b mod 2^8) by (rewrite Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + replace (v * 256) with (Z.shiftl v 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    + replace b with (b mod 2^8) by (rewrite Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma sxb_unsigned : forall b : byte,
  bv_unsigned (sxb b) = (if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b + 2^64 - 256).
Proof.
  intros b. unfold sxb. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
  unfold bv_signed, bv_swrap.
  change (bv_half_modulus 8) with 128. change (bv_wrap 8 ?x) with (x mod 256). change (bv_wrap 64 ?x) with (x mod 2^64).
  destruct (Z.ltb_spec0 (bv_unsigned b) 128).
  - rewrite (Z.mod_small _ 256) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((bv_unsigned b + 128) mod 256) with (bv_unsigned b + 128 - 256) by (Z.div_mod_to_equations; lia). 
    Z.div_mod_to_equations. cbn in *. lia.
Qed.
Lemma sxb_nonneg_small : forall b : byte, bv_unsigned (sxb b) < 2^63 -> bv_unsigned b < 128.
Proof. intros b H. rewrite sxb_unsigned in H. destruct (Z.ltb_spec0 (bv_unsigned b) 128); lia. Qed.
Lemma sxb_neg_big : forall b : byte, 2^63 <= bv_unsigned (sxb b) -> 128 <= bv_unsigned b.
Proof. intros b H. rewrite sxb_unsigned in H. pose proof (bv_unsigned_in_range 8 b). destruct (Z.ltb_spec0 (bv_unsigned b) 128); lia. Qed.
Lemma sxb_zero_iff : forall b : byte, bv_unsigned (sxb b) = 0 <-> bv_unsigned b = 0.
Proof. intros b. rewrite sxb_unsigned. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR; cbn in BR. destruct (Z.ltb_spec0 (bv_unsigned b) 128); lia. Qed.

(* [comment removed for export] *)
Ltac chunk_split H n H1 H2 :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
      let post := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
      change (rw_cells sg mx A cs) with (rw_cells sg mx A (pre ++ post)) in H;
      apply (proj1 (rw_cells_app sg mx A pre post)) in H; destruct H as [H1 H2];
      let z := eval cbv in (Z.of_nat (cells_size pre)) in
      change (Z.of_nat (cells_size pre)) with z in H2
  end.

(* [comment removed for export] *)
Ltac chunk_join H1 H2 H :=
  lazymatch type of H1 with
  | rw_cells ?sg ?mx ?A ?pre =>
    lazymatch type of H2 with
    | rw_cells sg mx ?B ?post =>
      let z := eval cbv in (Z.of_nat (cells_size pre)) in
      replace B with (A + z) in H2 by lia;
      pose proof (proj2 (rw_cells_app sg mx A pre post)
                    (conj H1 ltac:(change (Z.of_nat (cells_size pre)) with z; exact H2))) as H;
      clear H1 H2; cbn [app] in H
    end
  end.


(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  (* [comment removed for export] *)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 2 ?z => constr:(C2 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)

Lemma pristine_munch : forall lo hi E W m m',
  pristine lo hi E m -> munch W m m' ->
  (forall a, lo <= a < hi -> ~ E a -> outside W a) -> pristine lo hi E m'.
Proof.
  intros lo hi E W m m' (H0 & H1 & HP) MU HO. split; [exact H0|]. split; [exact H1|].
  intros a Ha HE. rewrite <- (HP a Ha HE). apply MU. rewrite wa_unsigned by lia. apply HO; assumption.
Qed.

Lemma statics_ok_munch : forall segs L W m m',
  statics_ok segs L m -> munch W m m' ->
  (forall a, hl_data_lo L <= a < hl_data_hi L -> ~ hl_written L a -> outside W a) -> statics_ok segs L m'.
Proof. intros segs L W m m' H MU HO. unfold statics_ok in *. eapply pristine_munch; eauto. Qed.

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  (* [comment removed for export] *)
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  | H : bytes_at segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  end;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_munch segs L W m m') in H; [ | exact MU | cbn [outside]; intros; plia ]
            | idtac "note: dropping statics_ok (callee footprint not provably outside the data range):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_munch lo hi E W m m') in H; [ | exact MU | cbn [outside]; intros; plia ]
            | idtac "note: dropping pristine (callee footprint not provably outside its range):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac flia ::= first [ assumption | clear_disj; slim; lia ].

(* [comment removed for export] *)
Ltac addr_eq_tac ::=
  symmetry;
  first [ apply wa_of_Z_to_bv; first [ clear_disj; lia | plia ]
        | apply wa_of_var; first [ clear_disj; lia | plia ]
        | unfold wa; f_equal; first [ clear_disj; lia | plia ] ].

(* [comment removed for export] *)
Section HeapPres.
Variable segs : list Segment.
Variable L : heap_layout.

#[using="Type"] Lemma heap_pres_sp_mono : forall LB SP SP' m m',
  heap_pres segs L LB SP m m' -> SP <= SP' -> heap_pres segs L LB SP' m m'.
Proof.
  intros LB SP SP' m m' HP HS a Ha Hc. apply HP; [exact Ha|].
  destruct Hc as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono segs m m' ->
  Forall (fun b => block_range L (fst b) (snd b)) LB ->
  hl_data_hi L <= alloc_ceiling ->
  (forall a, outside W a \/ (alloc_ceiling <= a < SP)) ->
  heap_pres segs L LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HB DHI HW a Ha Hc. split; [| apply WM].
  destruct (HW a) as [Ho|Hin].
  - apply MU. rewrite wa_unsigned by lia. exact Ho.
  - exfalso. destruct Hc as [H|[[H1 H2]|(b & Hb & Hr)]]; [lia| lia|].
    rewrite Forall_forall in HB. destruct (HB b Hb) as (_ & _ & _ & Hce & _). lia.
Qed.

#[using="Type"] Lemma block_range_lb_remove : forall A LB,
  Forall (fun b => block_range L (fst b) (snd b)) LB ->
  Forall (fun b => block_range L (fst b) (snd b)) (lb_remove A LB).
Proof. intros A LB H. rewrite Forall_forall in *. intros b Hb. apply H. eapply In_lb_remove; eauto. Qed.

#[using="Type"] Lemma lb_remove_sub : forall A LB b, In b (lb_remove A LB) -> In b LB.
Proof. intros; eapply In_lb_remove; eauto. Qed.
End HeapPres.

(* [comment removed for export] *)
Section HeapPresX.
Variable segs : list Segment.
Variable L : heap_layout.

Definition heap_presx (LB : list blk) (SP : Z) (X : list ivl) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside X a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma heap_presx_refl : forall LB SP X m, heap_presx LB SP X m m.
Proof. intros LB SP X m a _ _ _; auto. Qed.

#[using="Type"] Lemma heap_presx_of_pres : forall LB SP X m m', heap_pres segs L LB SP m m' -> heap_presx LB SP X m m'.
Proof. intros LB SP X m m' H a Ha Hc _. apply H; assumption. Qed.

#[using="Type"] Lemma heap_presx_trans : forall LB SP X m m1 m2,
  heap_presx LB SP X m m1 -> heap_presx LB SP X m1 m2 -> heap_presx LB SP X m m2.
Proof.
  intros LB SP X m m1 m2 H1 H2 a Ha Hc Ho.
  destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2]. split; [congruence| auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_presx_of_pres_sub : forall LB LB1 SP SP1 X m m',
  heap_pres segs L LB1 SP1 m m' -> (forall b, In b LB -> In b LB1) -> SP <= SP1 \/ SP1 <= SP ->
  SP1 <= SP ->
  heap_presx LB SP X m m'.
Proof.
  intros LB LB1 SP SP1 X m m' H HS _ HSP a Ha Hc _. apply H; [exact Ha|].
  destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right; exists b; auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_presx_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono segs m m' ->
  (forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside X a -> outside W a) ->
  heap_presx LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HW a Ha Hc Ho. split; [| apply WM].
  apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
Qed.

#[using="Type"] Lemma heap_presx_bytes_at : forall LB SP X m m' A bs,
  heap_presx LB SP X m m' -> bytes_at segs m A bs -> client_range L LB SP A (Z.of_nat (length bs)) ->
  disjoint_from X A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof.
  intros LB SP X m m' A bs HP (H0 & H1 & HB) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma heap_presx_wr_at : forall LB SP X m m' A n,
  heap_presx LB SP X m m' -> wr_at segs m A n -> client_range L LB SP A n -> disjoint_from X A n -> wr_at segs m' A n.
Proof.
  intros LB SP X m m' A n HP (H0 & H1 & HW) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma heap_presx_rw_cells : forall LB SP X m m' A cs,
  heap_presx LB SP X m m' -> rw_cells segs m A cs -> client_range L LB SP A (Z.of_nat (cells_size cs)) ->
  disjoint_from X A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
  - eapply heap_presx_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply heap_presx_wr_at; eauto.
Qed.

#[using="Type"] Lemma heap_presx_stk : forall LB SP X m m' lo hi,
  heap_presx LB SP X m m' -> stk segs m lo hi -> SP <= lo -> disjoint_from X lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros LB SP X m m' lo hi HP (H0 & H1 & HW) HS HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [E W].
  destruct (HW i Hi) as [W0 [b Hb]]. split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
End HeapPresX.

(* [comment removed for export] *)
Section ClientInside.
Variable L : heap_layout.

#[using="Type"] Lemma client_wrange_inside : forall LB LB' SP TOP A n a k,
  client_wrange L LB SP TOP A n -> (forall b, In b LB -> In b LB') -> A <= a -> a + k <= A + n ->
  client_wrange L LB' SP TOP a k.
Proof.
  intros LB LB' SP TOP A n a k H HS H1 H2 x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma client_range_inside : forall LB LB' SP TOP A n a k,
  client_wrange L LB SP TOP A n -> (forall b, In b LB -> In b LB') -> A <= a -> a + k <= A + n ->
  client_range L LB' SP a k.
Proof.
  intros LB LB' SP TOP A n a k H HS H1 H2 x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma client_range_wsep : forall LB LB' lo TOP SP' A n,
  client_wrange L LB lo TOP A n -> (forall b, In b LB -> In b LB') -> (A + n <= lo \/ SP' <= A) ->
  client_range L LB' SP' A n.
Proof.
  intros LB LB' lo TOP SP' A n H HS HD x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma client_range_sep : forall LB LB' lo SP' A n,
  client_range L LB lo A n -> (forall b, In b LB -> In b LB') -> (A + n <= lo \/ SP' <= A) ->
  client_range L LB' SP' A n.
Proof.
  intros LB LB' lo SP' A n H HS HD x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma client_range_apart : forall LB lo A n N k,
  client_range L LB lo A n -> 0 < n -> 0 < k -> alloc_ceiling <= lo -> N + k <= alloc_ceiling ->
  (N + k <= hl_data_lo L \/ hl_data_hi L <= N) ->
  (forall B j, In (B, j) LB -> N + k <= B \/ B + j <= N) ->
  N + k <= A \/ A + n <= N.
Proof.
  intros LB lo A n N k H Hn Hk HL HC HD HB.
  destruct (Z_lt_le_dec A (N + k)) as [H1|H1]; [| left; lia].
  destruct (Z_lt_le_dec N (A + n)) as [H2|H2]; [| right; lia].
  exfalso. assert (HX : A <= Z.max A N < A + n) by (split; [apply Z.le_max_l| apply Z.max_lub_lt; lia]).
  pose proof (Z.le_max_r A N) as HY.
  destruct (H (Z.max A N) HX) as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
  destruct b as [B j]. cbn in Hr. destruct (HB B j Hb); lia.
Qed.

#[using="Type"] Lemma client_wrange_apart : forall LB lo TOP A n N k,
  client_wrange L LB lo TOP A n -> 0 < n -> 0 < k -> alloc_ceiling <= lo -> N + k <= alloc_ceiling ->
  (N + k <= hl_data_lo L \/ hl_data_hi L <= N) ->
  (forall B j, In (B, j) LB -> N + k <= B \/ B + j <= N) ->
  N + k <= A \/ A + n <= N.
Proof.
  intros LB lo TOP A n N k H Hn Hk HL HC HD HB.
  destruct (Z_lt_le_dec A (N + k)) as [H1|H1]; [| left; lia].
  destruct (Z_lt_le_dec N (A + n)) as [H2|H2]; [| right; lia].
  exfalso. assert (HX : A <= Z.max A N < A + n) by (split; [apply Z.le_max_l| apply Z.max_lub_lt; lia]).
  pose proof (Z.le_max_r A N) as HY.
  destruct (H (Z.max A N) HX) as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
  destruct b as [B j]. cbn in Hr. destruct (HB B j Hb); lia.
Qed.

#[using="Type"] Lemma client_wrange_mono : forall LB LB' SP TOP A n,
  client_wrange L LB SP TOP A n -> (forall b, In b LB -> In b LB') -> client_wrange L LB' SP TOP A n.
Proof. intros. eapply client_wrange_inside; eauto; lia. Qed.
End ClientInside.

Ltac solve_sub :=
  first [ assumption
        | (intros ? Hb; exact Hb)
        | (intros ? Hb; solve [ auto 6 using in_cons, in_or_app with nocore ])
        | (intros ? Hb; apply in_or_app; right; solve [ exact Hb | apply in_or_app; right; exact Hb ])
        | (intros ? Hb; right; solve [ exact Hb | apply in_or_app; right; exact Hb ]) ].

(* [comment removed for export] *)
Ltac dlia := clear_disj; lia.

Ltac solve_client_wrange ::=
  first [ apply client_wrange_stack; [dlia | dlia]
        | match goal with H : In (?B, ?j) ?LBx |- client_wrange ?L ?LBx ?SP ?TOP ?a ?k =>
            apply (client_wrange_block L LBx SP TOP a k B j H); dlia end
        | eapply client_wrange_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange ?L ?LB0 ?SP ?TOP ?A ?n |- client_wrange _ _ _ _ ?a ?k =>
            eapply (client_wrange_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ] end ].

Ltac solve_client_range ::=
  first [ apply client_range_stack; dlia
        | match goal with H : In (?B, ?j) ?LBx |- client_range ?L ?LBx ?SP ?a ?k =>
            apply (client_range_block L LBx SP a k B j H); dlia end
        | eapply client_range_block; [ eassumption | dlia | dlia ]
        | eapply client_range_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange ?L ?LB0 ?SP ?TOP ?A ?n |- client_range _ _ _ ?a ?k =>
            first [ eapply (client_range_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ]
                  | eapply (client_range_wsep L LB0 _ SP TOP _ A n H); [ solve_sub | plia ] ] end
        | match goal with H : client_range ?L ?LB0 ?lo ?A ?n |- client_range _ _ _ ?A ?n =>
            eapply (client_range_sep L LB0 _ lo _ A n H); [ solve_sub | plia ] end ].

Lemma blocks_apart_in2 : forall LB A n B k,
  blocks_apart LB -> In (A, n) LB -> In (B, k) LB -> A <> B -> A + n <= B \/ B + k <= A.
Proof.
  intros LB. induction LB as [|[C j] r IH]; cbn; intros A n B k HA HiA HiB HNE; [destruct HiA|].
  destruct HA as [HC Hr].
  destruct HiA as [EA|HiA]; destruct HiB as [EB|HiB].
  - congruence.
  - injection EA as -> ->. apply (HC B k HiB).
  - injection EB as -> ->. destruct (HC A n HiA); lia.
  - apply IH; assumption.
Qed.

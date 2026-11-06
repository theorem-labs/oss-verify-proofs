(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim StoreOk Hoare Frame LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs AsRtSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod_exact : forall a b, (0 < b)%Z -> (a mod b = 0)%Z -> a = (b * (a / b))%Z.
Proof. intros a b Hb Hm. lia. Qed.
Lemma mod_down : forall a b c, (0 < b)%Z -> (0 < c)%Z -> (a mod (b * c) = 0)%Z -> (a mod b = 0)%Z.
Proof.
  intros a b c Hb Hcc Hm. apply (proj2 (Z.mod_divide a b ltac:(lia))).
  apply (Z.divide_trans b (b * c) a); [exists c; lia | apply (proj1 (Z.mod_divide a (b * c) ltac:(lia))); exact Hm].
Qed.
Lemma frame0_al64 : forall fs p, (fs mod 4096 = 0)%Z -> ((fs + 36864 + 64 * p) mod 64 = 0)%Z.
Proof. intros. lia. Qed.
Lemma div8_addk : forall a k, ((a + 8 * k) / 8 = a / 8 + k)%Z.
Proof. intros. lia. Qed.
Lemma div8_bounds : forall a, (8 * (a / 8) <= a < 8 * (a / 8) + 8)%Z.
Proof. intros. lia. Qed.
(* [comment removed for export] *)
Lemma pos_succ_ne : forall h : word, pos0 (Z_to_bv 64 (bv_unsigned h + 1)) <> pos0 h.
Proof.
  intros h. unfold pos0. pose proof (u64_range h).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (bv_unsigned h + 1)) with ((bv_unsigned h + 1) mod 2 ^ 64)%Z.
  destruct (Z.eq_dec (bv_unsigned h) (2 ^ 64 - 1)) as [E|NE].
  - rewrite E. cbn. lia.
  - rewrite (Z.mod_small (bv_unsigned h + 1) (2 ^ 64)) by lia. lia.
Qed.
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
Record hidden (P : Prop) : Prop := Hide { unhide : P }.
Arguments Hide {P} _. Arguments unhide {P} _.
Ltac hide H := lazymatch type of H with ?T => let H' := fresh in pose proof (@Hide T H) as H'; clear H; rename H' into H end.

(* [comment removed for export] *)
Definition AS_SIMGLO : Z := 0x7fffa000.   (* [comment removed for export] *)
Definition AS_SIMGHI : Z := 0x800b7800.   (* [comment removed for export] *)
Definition in_env_zone (a n : Z) : Prop :=
  (AS_IMGLO <= a /\ a + n <= AS_IMGHI) \/ (AS_SIMGLO <= a /\ a + n <= AS_SIMGHI).

(* [comment removed for export] *)
Definition env_safe (ceil fs : Z) (r : word * Z) : Prop :=
  let a := bv_unsigned (fst r) in
  0 <= snd r /\ (ceil <= a \/ (fs <= a /\ a + snd r <= fs + FS_SIZE)
                 \/ (AS_SB + fs / 8 <= a /\ a + snd r <= AS_SB + (fs + FS_SIZE) / 8)).

(* [comment removed for export] *)
Definition abi_low (A : as_abi) : Prop :=
  (forall a v, In (a, v) (aa_c64 A) -> in_env_zone a 8) /\
  (forall a v, In (a, v) (aa_c32 A) -> in_env_zone a 4) /\
  (forall a v, In (a, v) (aa_c8 A) -> in_env_zone a 1) /\
  (forall a, In a (aa_r64 A) -> in_env_zone a 8) /\
  (forall a v, In (a, v) (aa_shb A) -> in_env_zone a 1) /\
  (forall lo hi, In (lo, hi) (aa_ro A) -> in_env_zone lo (hi - lo)) /\
  in_env_zone (aa_tsdv A) 8 /\ in_env_zone (aa_tp A - 88) (0x30 + 88).

Ltac in_list_bounds :=
  intros; repeat match goal with H : In _ _ |- _ => cbn in H; intuition (try congruence) end;
  repeat match goal with H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst end;
  try match goal with H : _ = _ |- _ => subst end; cbn; lia.

Lemma asan_abi_low : abi_low asan_abi.
Proof.
  unfold abi_low. cbn -[in_env_zone Z.pow Z.le Z.add Z.sub Z.div].
  repeat split; intros;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
  try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try subst;
  unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI; first [left; lia | right; lia].
Qed.

Section WithSegs.
Variable segs : list Segment.
Implicit Types (mem : word -> option byte) (rs : list (word * Z)).

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Lemma env_safe_apart_low : forall ceil fs rs a n,
  Forall (env_safe ceil fs) rs -> AS_STKLO <= ceil -> appm fs FS_SIZE -> 0 <= n -> in_env_zone a n -> apart a n rs.
Proof.
  intros ceil fs rs a n H Hc Hfs Hn Hz. unfold apart. eapply Forall_impl; [|exact H].
  intros [b m] (H2 & H3). cbn [fst snd] in *.
  unfold in_env_zone, appm, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI, AS_SB, AS_LOWEND, AS_HIGHBEG, FS_SIZE in *. lia.
Qed.
Ltac Zify.zify_post_hook ::= idtac.

Lemma env_safe_apart_heap : forall ceil fs rs a,
  Forall (env_safe ceil fs) rs -> appm fs FS_SIZE -> heap_cell_ok ceil a fs -> apart a 8 rs.
Proof.
  intros ceil fs rs a H Hfs (H1 & H2 & H3). unfold apart. eapply Forall_impl; [|exact H].
  intros [b m] (K2 & K3). cbn [fst snd] in *.
  unfold appm, AS_IMGLO, AS_IMGHI, AS_SB, AS_LOWEND, AS_HIGHBEG, FS_SIZE in *.
  assert (Hub : (fs + 0xb09000) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (Hlb : 0 <= fs / 8) by (apply Z.div_pos; lia).
  assert (Hmono : fs / 8 <= (fs + 0xb09000) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma acell_frame : forall mem (mem' : word -> option byte) rs a w v,
  frame_mod mem mem' rs -> acell segs mem a w v -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> apart a (Z.of_nat w) rs ->
  acell segs mem' a w v.
Proof. intros. unfold acell in *. erewrite rdn_frame; eauto. Qed.

Lemma acellw_frame : forall mem (mem' : word -> option byte) rs a v,
  frame_mod mem mem' rs -> acellw segs mem a v -> 0 <= a -> a + 8 <= 2 ^ 64 -> apart a 8 rs ->
  acellw segs mem' a v.
Proof. intros. unfold acellw in *. erewrite (rdn_frame segs mem mem' rs a 8); eauto. Qed.

Lemma areadable_frame : forall mem (mem' : word -> option byte) rs a w,
  frame_mod mem mem' rs -> areadable segs mem a w -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> apart a (Z.of_nat w) rs ->
  areadable segs mem' a w.
Proof. intros mem mem' rs a w Hf [bs H] Ha Hw Hap. exists bs. erewrite rdn_frame; eauto. Qed.

Lemma awritable_frame : forall mem (mem' : word -> option byte) rs a n,
  frame_mod mem mem' rs -> awritable segs mem a n -> awritable segs mem' a n.
Proof. intros mem mem' rs a n Hf H. unfold awritable in *. eapply frame_mod_store_ok; eauto. Qed.

Lemma azero_frame : forall mem (mem' : word -> option byte) rs lo n,
  frame_mod mem mem' rs -> azero mem lo n -> 0 <= lo -> lo + n <= 2 ^ 64 -> apart lo n rs -> azero mem' lo n.
Proof.
  intros mem mem' rs lo n Hf H Hlo Hhi Hap i Hi.
  rewrite (byte_frame mem mem' rs (lo + i) Hf ltac:(lia)); [apply H; exact Hi|].
  eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.

Ltac zone_lia := unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn -[Z.div]; lia.

Lemma env_cells_frame : forall ceil A fs mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> appm fs FS_SIZE -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs ->
  env_cells segs A mem -> env_cells segs A mem'.
Proof.
  intros ceil A fs mem mem' rs (L64 & L32 & L8 & LR & _) Hc Hfs Hf Hs (C64 & C32 & C8 & R64).
  split; [|split; [|split]].
  - intros a v Hin. pose proof (L64 a v Hin). eapply acell_frame; [exact Hf | apply C64; exact Hin | zone_lia | cbn; zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | cbn; lia | exact H]].
  - intros a v Hin. pose proof (L32 a v Hin). eapply acell_frame; [exact Hf | apply C32; exact Hin | zone_lia | cbn; zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | cbn; lia | exact H]].
  - intros a v Hin. pose proof (L8 a v Hin). eapply acell_frame; [exact Hf | apply C8; exact Hin | zone_lia | cbn; zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | cbn; lia | exact H]].
  - intros a Hin. pose proof (LR a Hin). eapply areadable_frame; [exact Hf | apply R64; exact Hin | zone_lia | cbn; zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | cbn; lia | exact H]].
Qed.

Lemma env_shb_frame : forall ceil A fs mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> appm fs FS_SIZE -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs ->
  env_shb A mem -> env_shb A mem'.
Proof.
  intros ceil A fs mem mem' rs (_ & _ & _ & _ & LS & _) Hc Hfs Hf Hs H a v Hin. pose proof (LS a v Hin) as Hz.
  rewrite (byte_frame mem mem' rs a Hf ltac:(zone_lia)); [apply H; exact Hin|].
  eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | lia | exact Hz].
Qed.

Lemma env_ro_frame : forall ceil A fs mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> appm fs FS_SIZE -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs ->
  env_ro A mem -> env_ro A mem'.
Proof.
  intros ceil A fs mem mem' rs (_ & _ & _ & _ & _ & LR & _) Hc Hfs Hf Hs H lo hi i Hin Hi. pose proof (LR lo hi Hin) as Hz.
  rewrite (byte_frame mem mem' rs i Hf ltac:(zone_lia)); [apply (H lo hi i Hin Hi)|].
  eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | lia | unfold in_env_zone in *; lia].
Qed.

Lemma env_chain_frame : forall ceil A fs c mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> appm fs FS_SIZE -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs ->
  env_chain segs ceil A fs c mem -> env_chain segs ceil A fs c mem'.
Proof.
  intros ceil A fs c mem mem' rs (_ & _ & _ & _ & _ & _ & T1 & T2) Hc Hfs Hf Hs
         (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  assert (Z2 : in_env_zone (aa_tp A + 0x8) 8) by (unfold in_env_zone in *; lia).
  pose proof H2 as (A2 & ? & ?). pose proof H4 as (A4 & ? & ?). pose proof H5 as (A5 & ? & ?). pose proof H10 as (A10 & ? & ?).
  unfold appm in A2, A4, A5, A10.
  unfold env_chain.
  split; [eapply acellw_frame; [exact Hf | exact H1 | zone_lia | zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | lia | exact T1]]|].
  split; [exact H2|].
  split; [eapply acellw_frame; [exact Hf | exact H3 | lia | lia | eapply env_safe_apart_heap; [exact Hs | exact Hfs | exact H2]]|].
  split; [exact H4|]. split; [exact H5|].
  split; [eapply acellw_frame; [exact Hf | exact H6 | lia | lia | eapply env_safe_apart_heap; [exact Hs | exact Hfs | exact H4]]|].
  split; [eapply acellw_frame; [exact Hf | exact H7 | lia | lia | eapply env_safe_apart_heap; [exact Hs | exact Hfs | exact H5]]|].
  split; [eapply acellw_frame; [exact Hf | exact H8 | zone_lia | zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact Hfs | lia | exact Z2]]|].
  split; [exact H9|]. split; [exact H10|].
  split; [eapply acellw_frame; [exact Hf | exact H11 | lia | lia | eapply env_safe_apart_heap; [exact Hs | exact Hfs | exact H10]]|].
  exact H12.
Qed.

Lemma as_env_frame : forall ceil A fs c mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> appm fs FS_SIZE -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs ->
  as_env segs ceil A fs c mem -> as_env segs ceil A fs c mem'.
Proof.
  intros ceil A fs c mem mem' rs HA Hc Hfs Hf Hs (E1 & E2 & E3 & E4).
  split; [eapply env_cells_frame; eauto|]. split; [eapply env_shb_frame; eauto|].
  split; [eapply env_ro_frame; eauto|]. eapply env_chain_frame; eauto.
Qed.

(* [comment removed for export] *)
Lemma fs_hdr_frame : forall ceil A fs mem (mem' : word -> option byte) rs,
  abi_low A -> AS_STKLO <= ceil -> frame_mod mem mem' rs -> Forall (env_safe ceil fs) rs -> apart (fs + FS_SSL) 9 rs ->
  fs_hdr segs ceil A fs mem -> fs_hdr segs ceil A fs mem'.
Proof.
  intros ceil A fs mem mem' rs (_ & _ & _ & _ & _ & _ & _ & T4) Hc Hf Hs Hap (H1 & H2 & H3 & H4 & H5 & H6).
  assert (Z0 : in_env_zone (aa_tp A + 0) 8) by (unfold in_env_zone in *; lia).
  pose proof H4 as A4. unfold appm, FS_SIZE in A4. unfold FS_SSL, FS_NEEDSGC in *. unfold fs_hdr, FS_SSL, FS_NEEDSGC.
  split; [eapply acell_frame; [exact Hf | exact H1 | zone_lia | cbn; zone_lia | eapply env_safe_apart_low; [exact Hs | exact Hc | exact H4 | cbn; lia | exact Z0]]|].
  split; [eapply acell_frame; [exact Hf | exact H2 | lia | cbn; lia | eapply apart_sub; [exact Hap | lia | cbn; lia | cbn; lia]]|].
  split; [eapply acell_frame; [exact Hf | exact H3 | lia | cbn; lia | eapply apart_sub; [exact Hap | lia | cbn; lia | cbn; lia]]|].
  split; [exact H4|]. split; [exact H5|]. exact H6.
Qed.

Lemma fs_writable_frame : forall fs mem (mem' : word -> option byte) rs,
  frame_mod mem mem' rs -> fs_writable segs fs mem -> fs_writable segs fs mem'.
Proof.
  intros fs mem mem' rs Hf (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  unfold fs_writable.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; (eapply awritable_frame; [exact Hf|]; assumption).
Qed.

(* [comment removed for export] *)
Lemma fs_flags0_but_frame : forall fs busy busy' mem (mem' : word -> option byte) rs,
  frame_mod mem mem' rs -> fs_flags0_but fs busy mem ->
  0 <= fs -> fs + FS_SIZE <= 2 ^ 64 ->
  (forall i, 0 <= i < FS_FLAGS0_LEN -> ~ In i busy' -> ~ In i busy /\ apart (fs + FS_FLAGS0 + i) 1 rs) ->
  fs_flags0_but fs busy' mem'.
Proof.
  intros fs busy busy' mem mem' rs Hf H Hlo Hhi Hcond i Hi Hni.
  destruct (Hcond i Hi Hni) as [Hnb Hap].
  unfold FS_FLAGS0, FS_FLAGS0_LEN, FS_SIZE in *.
  rewrite (byte_frame mem mem' rs (fs + 4096 + i) Hf ltac:(lia) Hap). apply H; assumption.
Qed.

(* [comment removed for export] *)
Lemma fs_flags0_but_clear : forall fs busy mem p,
  fs_flags0_but fs (p :: busy) mem -> mem (Z_to_bv 64 (fs + FS_FLAGS0 + p)) = Some (Z_to_bv 8 0) ->
  fs_flags0_but fs busy mem.
Proof.
  intros fs busy mem p H Hp i Hi Hni.
  destruct (Z.eq_dec i p) as [->|Hne]; [exact Hp|].
  apply H; [exact Hi|]. intros [Heq|Hin]; [lia | exact (Hni Hin)].
Qed.

Lemma fs_flags0_but_weaken : forall fs busy busy' mem,
  fs_flags0_but fs busy mem -> incl busy busy' -> fs_flags0_but fs busy' mem.
Proof. intros fs busy busy' mem H Hincl i Hi Hni. apply H; [exact Hi|]. intros Hin. apply Hni, Hincl, Hin. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_sub : forall (M : word -> option byte) a m a' m',
  shz M a m -> (a' mod 8 = 0)%Z -> (a <= a')%Z -> (0 <= m')%Z -> (a' + 8 * m' <= a + 8 * m)%Z -> shz M a' m'.
Proof.
  intros M a m a' m' [Hal Hz] Hal' Hle Hm' Hhi. split; [exact Hal'|]. intros j Hj.
  replace (SB + a' / 8 + j)%Z with (SB + a / 8 + (a' / 8 - a / 8 + j))%Z by lia. apply Hz. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Lemma shwz_frame : forall mem (mem' : word -> option byte) rs a n,
  frame_mod mem mem' rs -> shwz mem a n -> 0 <= a -> a + n < 2 ^ 47 ->
  apart (8 * ((AS_SB + a / 8) / 8)) (8 * ((AS_SB + (a + n - 1) / 8) / 8) + 8 - 8 * ((AS_SB + a / 8) / 8)) rs ->
  shwz mem' a n.
Proof.
  intros mem mem' rs a n Hf H Ha Hn Hap x Hx. unfold AS_SB in *.
  rewrite (byte_frame mem mem' rs x Hf ltac:(cbn in *; lia)); [apply H; exact Hx|].
  eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.
Ltac Zify.zify_post_hook ::= idtac.

End WithSegs.

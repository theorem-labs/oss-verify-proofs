(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim StoreOk Hoare Frame LibDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma u_small_frame : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition apart (lo n : Z) (rs : list (word * Z)) : Prop :=
  Forall (fun r => bv_unsigned (fst r) + snd r <= lo \/ lo + n <= bv_unsigned (fst r)) rs.

Lemma apart_nil : forall lo n, apart lo n [].
Proof. intros. constructor. Qed.

Lemma apart_cons : forall lo n b m rs,
  (bv_unsigned b + m <= lo \/ lo + n <= bv_unsigned b) -> apart lo n rs -> apart lo n ((b, m) :: rs).
Proof. intros. constructor; assumption. Qed.

Lemma apart_cons_iff : forall lo n b m rs,
  apart lo n ((b, m) :: rs) <-> (bv_unsigned b + m <= lo \/ lo + n <= bv_unsigned b) /\ apart lo n rs.
Proof. intros. unfold apart. rewrite Forall_cons_iff. cbn [fst snd]. tauto. Qed.

Lemma apart_app : forall lo n rs1 rs2, apart lo n rs1 -> apart lo n rs2 -> apart lo n (rs1 ++ rs2).
Proof. intros. unfold apart in *. apply Forall_app. tauto. Qed.

Lemma apart_app_iff : forall lo n rs1 rs2, apart lo n (rs1 ++ rs2) <-> apart lo n rs1 /\ apart lo n rs2.
Proof. intros. unfold apart. rewrite Forall_app. tauto. Qed.

(* [comment removed for export] *)
Lemma apart_sub : forall lo n lo' n' rs,
  apart lo n rs -> lo <= lo' -> 0 <= n' -> lo' + n' <= lo + n -> apart lo' n' rs.
Proof.
  intros lo n lo' n' rs H H1 H2 H3. unfold apart in *.
  eapply Forall_impl; [|exact H]. intros [b m] Hb. cbn [fst snd] in *. lia.
Qed.

Lemma apart_outside : forall (x : word) lo n rs,
  lo <= bv_unsigned x < lo + n -> apart lo n rs -> outside x rs.
Proof.
  intros x lo n rs Hx. induction rs as [|[b m] rs IH]; cbn [outside]; intros H; [exact I|].
  apply apart_cons_iff in H as [H1 H2]. split; [| apply IH; exact H2]. unfold in_rng. lia.
Qed.

(* [comment removed for export] *)
Ltac solve_apart :=
  unfold apart; repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?u_small_frame by lia; try lia|]);
  try apply Forall_nil.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Implicit Types (mem : word -> option byte) (rs : list (word * Z)).

Lemma byte_frame : forall mem mem' rs a,
  frame_mod mem mem' rs -> 0 <= a < 2 ^ 64 -> apart a 1 rs -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof using .
  intros mem mem' rs a Hf Ha Hap. eapply frame_mod_byte; [exact Hf|].
  eapply apart_outside; [|exact Hap]. rewrite u_small_frame by lia. lia.
Qed.

Lemma rdn_frame : forall mem mem' rs a (w : nat),
  frame_mod mem mem' rs -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> apart a (Z.of_nat w) rs ->
  rdn segs mem' (Z_to_bv 64 a) w = rdn segs mem (Z_to_bv 64 a) w.
Proof using .
  intros mem mem' rs a w Hf H0 Hw Hap.
  destruct w as [|w']; [reflexivity|].
  assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite u_small_frame; lia).
  apply (frame_mod_rdn segs mem mem' rs (S w') (Z_to_bv 64 a) Hf).
  - intros i Hi. rewrite Ha. eapply apart_outside; [|exact Hap]. rewrite u_small_frame by lia. lia.
  - rewrite Ha. exact Hw.
Qed.

Lemma cell_frame : forall mem mem' rs a w x,
  frame_mod mem mem' rs -> cell segs mem a w x -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  apart a (Z.of_nat w) rs -> cell segs mem' a w x.
Proof using .
  intros mem mem' rs a w x Hf Hc H0 Hw Hap. unfold cell in *.
  rewrite (rdn_frame mem mem' rs a w Hf H0 Hw Hap). exact Hc.
Qed.

Lemma cell64_frame : forall mem mem' rs a x,
  frame_mod mem mem' rs -> cell64 segs mem a x -> 0 <= a -> a + 8 <= 2 ^ 64 -> apart a 8 rs ->
  cell64 segs mem' a x.
Proof using . intros. eapply cell_frame; eauto. Qed.

Lemma cell32_frame : forall mem mem' rs a v,
  frame_mod mem mem' rs -> cell32 segs mem a v -> 0 <= a -> a + 4 <= 2 ^ 64 -> apart a 4 rs ->
  cell32 segs mem' a v.
Proof using . intros mem mem' rs a v Hf [Hv Hc] H0 H4 Hap. split; [exact Hv|]. eapply cell_frame; eauto. Qed.

Lemma cell8_frame : forall mem mem' rs a v,
  frame_mod mem mem' rs -> cell8 segs mem a v -> 0 <= a -> a + 1 <= 2 ^ 64 -> apart a 1 rs ->
  cell8 segs mem' a v.
Proof using . intros mem mem' rs a v Hf [Hv Hc] H0 H1 Hap. split; [exact Hv|]. eapply cell_frame; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma writable_frame : forall mem mem' rs lo n,
  frame_mod mem mem' rs -> writable segs mem lo n -> writable segs mem' lo n.
Proof using .
  intros mem mem' rs lo n Hf (W1 & W2 & W3 & W4). repeat split; try assumption.
  eapply frame_mod_store_ok; eassumption.
Qed.

Lemma rodata_clear_frame : forall mem mem' rs lo hi,
  frame_mod mem mem' rs -> rodata_clear mem lo hi -> 0 <= lo -> hi <= 2 ^ 64 -> apart lo (hi - lo) rs ->
  rodata_clear mem' lo hi.
Proof using .
  intros mem mem' rs lo hi Hf Hro H0 Hhi Hap i Hi.
  rewrite (byte_frame mem mem' rs i Hf ltac:(lia)); [apply Hro; exact Hi|].
  eapply apart_sub; [exact Hap| lia | lia | lia].
Qed.

Lemma data_ok_frame : forall mem mem' rs data len bs,
  frame_mod mem mem' rs -> data_ok mem data len bs -> apart (bv_unsigned data) len rs ->
  data_ok mem' data len bs.
Proof using .
  intros mem mem' rs data len bs Hf (H1 & H2 & H3 & H4 & H5) Hap.
  pose proof (u64_range data).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  intros i Hi. rewrite <- (H5 i Hi). eapply byte_frame; [exact Hf| lia |].
  eapply apart_sub; [exact Hap| lia | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma curve_ok_frame : forall mem mem' rs data len c,
  frame_mod mem mem' rs -> curve_ok segs mem data len c -> 0 <= c -> c + 24 <= 2 ^ 64 -> apart c 24 rs ->
  curve_ok segs mem' data len c.
Proof using .
  intros mem mem' rs data len c Hf (n & t8 & t16 & Hn & H8 & H16 & Hrest) H0 H24 Hap.
  exists n, t8, t16. split; [|split; [|split; [|exact Hrest]]].
  - eapply cell32_frame; [exact Hf|exact Hn|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
  - eapply cell64_frame; [exact Hf|exact H8|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
  - eapply cell64_frame; [exact Hf|exact H16|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
Qed.

(* [comment removed for export] *)
Lemma curve_list_frame : forall mem mem' rs data len base offs span,
  frame_mod mem mem' rs ->
  Forall (fun off => curve_ok segs mem data len (base + off)) offs ->
  Forall (fun off => 0 <= off /\ off + 24 <= span) offs ->
  0 <= base -> base + span <= 2 ^ 64 -> apart base span rs ->
  Forall (fun off => curve_ok segs mem' data len (base + off)) offs.
Proof using .
  intros mem mem' rs data len base offs span Hf Hc Hb H0 Hs Hap.
  induction offs as [|off offs IH]; [constructor|].
  apply Forall_cons_iff in Hc as [Hc1 Hc2]. apply Forall_cons_iff in Hb as [Hb1 Hb2].
  constructor; [| apply IH; assumption].
  eapply curve_ok_frame; [exact Hf|exact Hc1|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
Qed.

Lemma profile_curve_offsets_bound :
  Forall (fun off => 0 <= off /\ off + 24 <= 976) profile_curve_offsets.
Proof using . unfold profile_curve_offsets. repeat (constructor; [cbn; lia|]). constructor. Qed.

Lemma curves_ok_frame : forall mem mem' rs data len P,
  frame_mod mem mem' rs -> curves_ok segs mem data len P -> 0 <= P -> P + 976 <= 2 ^ 64 -> apart P 976 rs ->
  curves_ok segs mem' data len P.
Proof using .
  intros mem mem' rs data len P Hf Hc H0 HP Hap. unfold curves_ok in *.
  eapply curve_list_frame; [exact Hf|exact Hc|apply profile_curve_offsets_bound|lia|lia|exact Hap].
Qed.

(* [comment removed for export] *)
Lemma tag_ok_frame : forall mem mem' rs data len T,
  frame_mod mem mem' rs -> tag_ok segs mem data len T -> 0 <= T -> T + 24 <= 2 ^ 64 -> apart T 24 rs ->
  tag_ok segs mem' data len T.
Proof using .
  intros mem mem' rs data len T Hf (sz & buf & Hsz & Hbuf & H4 & Hin) H0 H24 Hap.
  exists sz, buf. split; [|split; [|split; [exact H4|exact Hin]]].
  - eapply cell32_frame; [exact Hf|exact Hsz|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
  - eapply cell64_frame; [exact Hf|exact Hbuf|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
Qed.

(* [comment removed for export] *)
Lemma grid_ok_A2B_frame : forall mem mem' rs data len P,
  frame_mod mem mem' rs -> grid_ok_A2B segs mem data len P -> 0 <= P -> P + 976 <= 2 ^ 64 -> apart P 976 rs ->
  grid_ok_A2B segs mem' data len P.
Proof using .
  intros mem mem' rs data len P Hf (ic & oc & gps & g8 & g16 & Hic & Hoc & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hrest) H0 HP Hap.
  exists ic, oc, gps, g8, g16.
  split; [eapply cell32_frame; [exact Hf|exact Hic|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact Hoc|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Hicr|]. split; [exact Hlen|]. split; [exact Hgps|].
  split.
  { intros i Hi. eapply cell8_frame; [exact Hf|exact (Hgp i Hi)|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia]. }
  split; [eapply cell64_frame; [exact Hf|exact Hg8|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell64_frame; [exact Hf|exact Hg16|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  exact Hrest.
Qed.

Lemma profile_ok_frame : forall mem mem' rs data len bs P,
  frame_mod mem mem' rs -> profile_ok segs mem data len bs P -> 0 <= P -> P + 976 <= 2 ^ 64 -> apart P 976 rs ->
  profile_ok segs mem' data len bs P.
Proof using .
  intros mem mem' rs data len bs P Hf (psz & tc & hasA2B & H0c & H8 & H20 & Ht & Hc & H966 & Hg) H0 HP Hap.
  exists psz, tc, hasA2B.
  split; [eapply cell64_frame; [exact Hf|exact H0c|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H8|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H20|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Ht|].
  split; [eapply curves_ok_frame; [exact Hf|exact Hc|lia|lia|exact Hap]|].
  split; [eapply cell8_frame; [exact Hf|exact H966|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  intros Hnz. eapply grid_ok_A2B_frame; [exact Hf|exact (Hg Hnz)|lia|lia|exact Hap].
Qed.

End WithSegs.

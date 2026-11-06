(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibFPLib LibTagsSpec LibWP2Spec LibTagsLib.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

Section Lib.
Variable segs : list Segment.
Implicit Types (M : word -> option byte) (rs : list (word * Z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zero M (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Lemma zero_sub : forall M a n a' n', zero M a n -> a <= a' -> a' + n' <= a + n -> zero M a' n'.
Proof.
  intros M a n a' n' Hz H1 H2 i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia.
Qed.

Lemma zero_frame : forall M (M' : word -> option byte) rs a n,
  frame_mod M M' rs -> zero M a n -> 0 <= a -> a + n <= 2 ^ 64 -> apart a n rs -> zero M' a n.
Proof.
  intros M M' rs a n Hf Hz H0 Hn Hap i Hi.
  rewrite (byte_frame M M' rs (a + i) Hf ltac:(lia)); [apply Hz; exact Hi|].
  eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.

Lemma zero_cell : forall M a n (w : nat),
  zero M a n -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> Z.of_nat w <= n -> (w <= 8)%nat ->
  cell segs M a w (Z_to_bv 64 0).
Proof.
  intros M a n w Hz H0 Hw Hwn H8. apply cell_zeros; [lia|lia|exact H8|].
  intros i Hi. apply Hz. lia.
Qed.

Lemma zero_cell32 : forall M a n o,
  zero M a n -> 0 <= a -> a + n <= 2 ^ 64 -> 0 <= o -> o + 4 <= n -> cell32 segs M (a + o) 0.
Proof.
  intros M a n o Hz H0 Hn Ho Hon. split; [lia|].
  apply (zero_cell M (a + o) (n - o) 4); [| lia | cbn; lia | cbn; lia | lia].
  eapply zero_sub; [exact Hz | lia | lia].
Qed.

Lemma zero_cell64 : forall M a n o,
  zero M a n -> 0 <= a -> a + n <= 2 ^ 64 -> 0 <= o -> o + 8 <= n -> cell64 segs M (a + o) (Z_to_bv 64 0).
Proof.
  intros M a n o Hz H0 Hn Ho Hon.
  apply (zero_cell M (a + o) (n - o) 8); [| lia | cbn; lia | cbn; lia | lia].
  eapply zero_sub; [exact Hz | lia | lia].
Qed.

Lemma zero_cell8 : forall M a n o,
  zero M a n -> 0 <= a -> a + n <= 2 ^ 64 -> 0 <= o -> o + 1 <= n -> cell8 segs M (a + o) 0.
Proof.
  intros M a n o Hz H0 Hn Ho Hon. split; [lia|].
  apply (zero_cell M (a + o) (n - o) 1); [| lia | cbn; lia | cbn; lia | lia].
  eapply zero_sub; [exact Hz | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma zero_curve_ok : forall M data len a n c,
  zero M a n -> 0 <= a -> a + n <= 2 ^ 64 -> a <= c -> c + 24 <= a + n ->
  curve_ok segs M data len c.
Proof.
  intros M data len a n c Hz H0 Hn H1 H2.
  exists 0, (Z_to_bv 64 0), (Z_to_bv 64 0).
  split; [| split; [| split; [| left; reflexivity]]].
  - replace c with (a + (c - a)) by lia. eapply zero_cell32; [exact Hz|lia|lia|lia|lia].
  - replace (c + 8) with (a + (c - a + 8)) by lia. eapply zero_cell64; [exact Hz|lia|lia|lia|lia].
  - replace (c + 16) with (a + (c - a + 16)) by lia. eapply zero_cell64; [exact Hz|lia|lia|lia|lia].
Qed.

Lemma zero_curve_list : forall M data len a n base offs,
  zero M a n -> 0 <= a -> a + n <= 2 ^ 64 ->
  Forall (fun off => a <= base + off /\ base + off + 24 <= a + n) offs ->
  Forall (fun off => curve_ok segs M data len (base + off)) offs.
Proof.
  intros M data len a n base offs Hz H0 Hn Hb. induction offs as [|o offs IH]; [constructor|].
  apply Forall_cons_iff in Hb as [[B1 B2] Hb]. constructor; [| apply IH; exact Hb].
  eapply zero_curve_ok; [exact Hz | lia | lia | exact B1 | exact B2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition present M (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Lemma zero_present : forall M a n, zero M a n -> present M a n.
Proof. intros M a n Hz i Hi. rewrite (Hz i Hi). discriminate. Qed.

Lemma present_sub : forall M a n a' n', present M a n -> a <= a' -> a' + n' <= a + n -> present M a' n'.
Proof.
  intros M a n a' n' Hp H1 H2 i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply Hp. lia.
Qed.

Lemma present_frame : forall M (M' : word -> option byte) rs a n, frame_mod M M' rs -> present M a n -> present M' a n.
Proof. intros M M' rs a n [_ Hg] Hp i Hi. apply Hg. apply Hp. exact Hi. Qed.

Lemma present_rdn : forall M (w : nat) a,
  present M a (Z.of_nat w) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  exists bs, rdn segs M (Z_to_bv 64 a) w = Some bs.
Proof.
  intros M w. induction w as [|w IH]; intros a Hp H0 Hw; [exists []; reflexivity|].
  cbn [rdn].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hb.
  2:{ exfalso. apply (Hp 0); [lia|]. rewrite Z.add_0_r. exact Hb. }
  destruct (IH (a + 1)) as [bs Hbs]; [| lia | lia |].
  { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hp. lia. }
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
      change (bv_unsigned (1 : word)) with 1. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hbs. exists (b :: bs). reflexivity.
Qed.

Lemma present_cell64 : forall M a,
  present M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, cell64 segs M a w.
Proof.
  intros M a Hp H0 H8.
  destruct (present_rdn M 8 a Hp H0 H8) as [bs Hbs].
  destruct (cell_of_rdn segs M a 8 bs Hbs ltac:(lia)) as [x Hx]. exists x. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_prefix : forall M (a : word) n m bs,
  rdn segs M a (n + m) = Some bs -> rdn segs M a n = Some (firstn n bs).
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a m bs H; [reflexivity|].
  change (S n + m)%nat with (S (n + m)) in H. cbn [rdn] in H |- *.
  destruct (match M a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
  destruct (rdn segs M (a + 1)%bv (n + m)) as [rest|] eqn:Hr; [|discriminate].
  injection H as <-. rewrite (IH _ _ _ Hr). reflexivity.
Qed.

Lemma low32_of_cells : forall M a (w : word) v,
  cell64 segs M a w -> cell32 segs M a v -> bv_unsigned w mod 2 ^ 32 = v.
Proof.
  intros M a w v H8 [Hv H4]. unfold cell64, cell in H8, H4.
  pose proof (rdn_prefix M (Z_to_bv 64 a) 4 4 _ H8) as P4. change (4 + 4)%nat with 8%nat in P4.
  rewrite H4 in P4.
  assert (E4 : firstn 4 (word_to_le_bytes 8 w) = word_to_le_bytes 4 w) by reflexivity.
  assert (P : word_to_le_bytes 4 (Z_to_bv 64 v) = word_to_le_bytes 4 w) by congruence.
  pose proof (f_equal bytes_le_to_Z P) as B.
  unfold word_to_le_bytes in B. pose proof (u64_range w).
  rewrite !bytes_le_Z_to_le in B by (try apply u64_range; rewrite ?u_small by lia; lia).
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B.
  rewrite (u_small v) in B by lia. rewrite (Z.mod_small v) in B by lia. symmetry. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint roseg_ok (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      (match find_segment segs (bv_unsigned a) 1 with
       | Some seg => negb (seg_writable seg)
       | None => true
       end) && roseg_ok (a + 1)%bv n'
  end.

Lemma roseg_ok_all : forall n (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  roseg_ok a n = true ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    match find_segment segs (bv_unsigned x) 1 with
    | Some seg => seg_writable seg = false
    | None => True
    end.
Proof.
  induction n as [|n IH]; intros a Hnw H x Hx; [cbn in Hx; lia|].
  cbn [roseg_ok] in H. apply andb_prop in H as [H1 H2].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - rewrite Heq. destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|exact I].
    destruct (seg_writable seg); [discriminate | reflexivity].
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    apply (IH (a + 1)%bv); [lia | exact H2 | lia].
Qed.

Lemma writable_rodata_apart : forall M lo n lo' hi',
  0 <= lo' -> hi' <= 2 ^ 64 -> lo' < hi' ->
  roseg_ok (Z_to_bv 64 lo') (Z.to_nat (hi' - lo')) = true ->
  writable segs M lo n -> rodata_clear M lo' hi' ->
  (lo + n <= lo' \/ hi' <= lo).
Proof.
  intros M lo n lo' hi' H0 Hhi Hlt Hro (W1 & W2 & W3 & W4) Hclear.
  destruct (Z_lt_le_dec lo' (lo + n)) as [A|A]; [|left; lia].
  destruct (Z_lt_le_dec lo hi') as [B|B]; [|right; lia].
  exfalso.
  set (x := Z.max lo lo').
  assert (Hx1 : lo <= x < lo + n) by lia. assert (Hx2 : lo' <= x < hi') by lia.
  pose proof (store_ok_all segs M (Z.to_nat n) (Z_to_bv 64 lo) ltac:(rewrite u_small_frame, Z2Nat.id by lia; lia) W4
                (Z_to_bv 64 x) ltac:(rewrite !u_small_frame, Z2Nat.id by lia; lia)) as Hw.
  apply Hw. unfold wview. rewrite (Hclear x Hx2).
  pose proof (roseg_ok_all (Z.to_nat (hi' - lo')) (Z_to_bv 64 lo') ltac:(rewrite u_small_frame, Z2Nat.id by lia; lia) Hro
                (Z_to_bv 64 x) ltac:(rewrite !u_small_frame, Z2Nat.id by lia; lia)) as Hs.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 x)) 1) as [seg|]; [|reflexivity].
  rewrite Hs. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tags_ok_intro : forall len bs tc psz,
  0 <= tc -> 132 + 12 * tc <= psz -> psz <= len ->
  (forall i, 0 <= i < tc -> 4 <= be32 bs (132 + 12 * i + 8) /\
                            be32 bs (132 + 12 * i + 4) + be32 bs (132 + 12 * i + 8) <= psz) ->
  tags_ok len bs tc psz.
Proof. intros len bs tc psz H1 H2 H3 H4. split; [lia|]. split; [lia|]. exact H4. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma profile_curve_offsets_bound928 :
  Forall (fun off => 0 <= off /\ off + 24 <= 928) profile_curve_offsets.
Proof. unfold profile_curve_offsets. repeat (constructor; [cbn; lia|]). constructor. Qed.

(* [comment removed for export] *)
Lemma curves_ok_frame928 : forall M (M' : word -> option byte) rs data len P,
  frame_mod M M' rs -> curves_ok segs M data len P -> 0 <= P -> P + 976 <= 2 ^ 64 -> apart P 928 rs ->
  curves_ok segs M' data len P.
Proof.
  intros M M' rs data len P Hf Hc H0 HP Hap. unfold curves_ok in *.
  eapply curve_list_frame; [exact Hf|exact Hc|apply profile_curve_offsets_bound928|lia|lia|exact Hap].
Qed.

(* [comment removed for export] *)
Lemma grid_ok_A2B_frame288 : forall M (M' : word -> option byte) rs data len P,
  frame_mod M M' rs -> grid_ok_A2B segs M data len P -> 0 <= P -> P + 976 <= 2 ^ 64 -> apart (P + 288) 176 rs ->
  grid_ok_A2B segs M' data len P.
Proof.
  intros M M' rs data len P Hf (ic & oc & gps & g8 & g16 & Hic & Hoc & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hrest) H0 HP Hap.
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

(* [comment removed for export] *)
Lemma parsed_ok_frame : forall M (M' : word -> option byte) rs data len bs P,
  frame_mod M M' rs -> parsed_ok segs M data len bs P -> 0 <= P -> P + 976 <= 2 ^ 64 ->
  apart P 960 rs -> apart (P + 964) 1 rs -> apart (P + 966) 1 rs ->
  parsed_ok segs M' data len bs P.
Proof.
  intros M M' rs data len bs P Hf (psz & tc & htrc & hasA2B & H0c & H8 & H20 & Ht & Hc & H964 & R964 & H966 & R966 & Hg) H0 HP Hap A964 A966.
  exists psz, tc, htrc, hasA2B.
  split; [eapply cell64_frame; [exact Hf|exact H0c|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H8|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H20|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Ht|].
  split; [eapply curves_ok_frame928; [exact Hf|exact Hc|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell8_frame; [exact Hf|exact H964|lia|lia|exact A964]|].
  split; [exact R964|].
  split; [eapply cell8_frame; [exact Hf|exact H966|lia|lia|exact A966]|].
  split; [exact R966|].
  intros Hnz. eapply grid_ok_A2B_frame288; [exact Hf|exact (Hg Hnz)|lia|lia|]. eapply apart_sub; [exact Hap|lia|lia|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Forall_offs_shift : forall (Pc : Z -> Prop) base k offs,
  Forall (fun off => Pc (base + k + off)) offs -> Forall (fun off => Pc (base + off)) (map (Z.add k) offs).
Proof.
  intros Pc base k offs H. apply Forall_map. eapply Forall_impl; [| exact H].
  intros a Ha. cbv beta in Ha. replace (base + (k + a)) with (base + k + a) by lia. exact Ha.
Qed.

Lemma curves_ok_assemble : forall M data len p,
  Forall (fun off => curve_ok segs M data len (p + off)) [24; 56; 88] ->
  Forall (fun off => curve_ok segs M data len (p + 160 + off)) a2b_curve_offsets ->
  Forall (fun off => curve_ok segs M data len (p + 560 + off)) b2a_curve_offsets ->
  curves_ok segs M data len p.
Proof.
  intros M data len p H1 H2 H3. unfold curves_ok.
  change profile_curve_offsets with ([24; 56; 88] ++ map (Z.add 160) a2b_curve_offsets ++ map (Z.add 560) b2a_curve_offsets).
  apply Forall_app. split; [exact H1|]. apply Forall_app. split; apply Forall_offs_shift; assumption.
Qed.

Lemma a2b_curve_offsets_bound : Forall (fun off => 0 <= off /\ off + 24 <= 400) a2b_curve_offsets.
Proof. unfold a2b_curve_offsets. repeat (constructor; [cbn; lia|]). constructor. Qed.
Lemma b2a_curve_offsets_bound : Forall (fun off => 0 <= off /\ off + 24 <= 400) b2a_curve_offsets.
Proof. unfold b2a_curve_offsets. repeat (constructor; [cbn; lia|]). constructor. Qed.
Lemma trc_offsets_bound : Forall (fun off => 0 <= off /\ off + 24 <= 96) [24 - 24; 56 - 24; 88 - 24].
Proof. repeat (constructor; [cbn; lia|]). constructor. Qed.

(* [comment removed for export] *)
Lemma zero_a2b_curves : forall M data len p,
  zero M (p + 160) 400 -> 0 <= p -> p + 976 <= 2 ^ 64 ->
  Forall (fun off => curve_ok segs M data len (p + 160 + off)) a2b_curve_offsets.
Proof.
  intros M data len p Hz H0 Hp. eapply zero_curve_list; [exact Hz | lia | lia |].
  eapply Forall_impl; [| apply a2b_curve_offsets_bound]. intros a Ha. cbv beta in Ha. lia.
Qed.
Lemma zero_b2a_curves : forall M data len p,
  zero M (p + 560) 400 -> 0 <= p -> p + 976 <= 2 ^ 64 ->
  Forall (fun off => curve_ok segs M data len (p + 560 + off)) b2a_curve_offsets.
Proof.
  intros M data len p Hz H0 Hp. eapply zero_curve_list; [exact Hz | lia | lia |].
  eapply Forall_impl; [| apply b2a_curve_offsets_bound]. intros a Ha. cbv beta in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma a2b_curves_frame : forall M (M' : word -> option byte) rs data len p,
  frame_mod M M' rs -> Forall (fun off => curve_ok segs M data len (p + 160 + off)) a2b_curve_offsets ->
  0 <= p -> p + 976 <= 2 ^ 64 -> apart (p + 160) 400 rs ->
  Forall (fun off => curve_ok segs M' data len (p + 160 + off)) a2b_curve_offsets.
Proof.
  intros M M' rs data len p Hf Hc H0 Hp Hap.
  eapply curve_list_frame; [exact Hf | exact Hc | apply a2b_curve_offsets_bound | lia | lia | exact Hap].
Qed.
Lemma b2a_curves_frame : forall M (M' : word -> option byte) rs data len p,
  frame_mod M M' rs -> Forall (fun off => curve_ok segs M data len (p + 560 + off)) b2a_curve_offsets ->
  0 <= p -> p + 976 <= 2 ^ 64 -> apart (p + 560) 400 rs ->
  Forall (fun off => curve_ok segs M' data len (p + 560 + off)) b2a_curve_offsets.
Proof.
  intros M M' rs data len p Hf Hc H0 Hp Hap.
  eapply curve_list_frame; [exact Hf | exact Hc | apply b2a_curve_offsets_bound | lia | lia | exact Hap].
Qed.
Lemma trc_curves_frame : forall M (M' : word -> option byte) rs data len p,
  frame_mod M M' rs -> Forall (fun off => curve_ok segs M data len (p + off)) [24; 56; 88] ->
  0 <= p -> p + 976 <= 2 ^ 64 -> apart (p + 24) 96 rs ->
  Forall (fun off => curve_ok segs M' data len (p + off)) [24; 56; 88].
Proof.
  intros M M' rs data len p Hf Hc H0 Hp Hap.
  apply Forall_cons_iff in Hc as [C1 Hc]. apply Forall_cons_iff in Hc as [C2 Hc]. apply Forall_cons_iff in Hc as [C3 _].
  repeat constructor.
  - eapply curve_ok_frame; [exact Hf | exact C1 | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]].
  - eapply curve_ok_frame; [exact Hf | exact C2 | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]].
  - eapply curve_ok_frame; [exact Hf | exact C3 | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pcs_of (raw : word) : Z := if Z.eq_dec (bv_unsigned raw) 0x205a5958 then 1 else 0.

Lemma pcs_of_01 : forall raw, pcs_of raw = 0 \/ pcs_of raw = 1.
Proof. intros raw. unfold pcs_of. destruct (Z.eq_dec _ _); lia. Qed.

Lemma lxor_u64_range : forall (x y : word), 0 <= Z.lxor (bv_unsigned x) (bv_unsigned y) < 2 ^ 64.
Proof.
  intros x y. pose proof (u64_range x) as Hx. pose proof (u64_range y) as Hy.
  split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor (bv_unsigned x) (bv_unsigned y)) 0) as [->|Hnz]; [lia|].
  assert (Hnn : 0 <= Z.lxor (bv_unsigned x) (bv_unsigned y)) by (apply Z.lxor_nonneg; lia).
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec (bv_unsigned x) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec (bv_unsigned y) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma sltiu_xor_pcs : forall (raw : word),
  v_sltu (v_xor raw (Z_to_bv 64 0x205a5958)) (Z_to_bv 64 1) = Z_to_bv 64 (pcs_of raw).
Proof.
  intros raw. unfold v_sltu, c_ltu, bv_ltu, v_xor, pcs_of.
  pose proof (lxor_u64_range raw (Z_to_bv 64 0x205a5958)) as R.
  rewrite (u_small 0x205a5958) in R by lia.
  rewrite (u_small 0x205a5958) by lia. rewrite !u_small by lia.
  destruct (Z.eq_dec (bv_unsigned raw) 0x205a5958) as [E|NE].
  - rewrite E, Z.lxor_nilpotent. reflexivity.
  - destruct (Z.ltb_spec (Z.lxor (bv_unsigned raw) 0x205a5958) 1) as [L|L]; [|reflexivity].
    exfalso. apply NE. apply Z.lxor_eq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell64_inj : forall M a (x y : word), cell64 segs M a x -> cell64 segs M a y -> x = y.
Proof.
  intros M a x y Hx Hy. unfold cell64, cell in Hx, Hy. rewrite Hx in Hy.
  assert (E8 : word_to_le_bytes 8 x = word_to_le_bytes 8 y) by congruence.
  pose proof (f_equal bytes_le_to_Z E8) as B. rewrite !bytes_le_N in B.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B.
  pose proof (u64_range x). pose proof (u64_range y).
  rewrite !Z.mod_small in B by lia. apply bv_eq. exact B.
Qed.

Lemma cell64_low32 : forall M a (w : word), cell64 segs M a w -> cell32 segs M a (bv_unsigned w mod 2 ^ 32).
Proof.
  intros M a w H8. unfold cell64, cell in H8.
  pose proof (rdn_prefix M (Z_to_bv 64 a) 4 4 _ H8) as P4. change (4 + 4)%nat with 8%nat in P4.
  assert (E4 : firstn 4 (word_to_le_bytes 8 w) = word_to_le_bytes 4 w) by reflexivity.
  rewrite E4 in P4. apply cell32_of_word. exact P4.
Qed.

(* [comment removed for export] *)
Lemma curve_ok_copy : forall M data len c (w0 w1 w2 : word),
  curve_ok segs M data len c ->
  cell64 segs M c w0 -> cell64 segs M (c + 8) w1 -> cell64 segs M (c + 16) w2 ->
  forall (M' : word -> option byte) c',
    cell64 segs M' c' w0 -> cell64 segs M' (c' + 8) w1 -> cell64 segs M' (c' + 16) w2 ->
    curve_ok segs M' data len c'.
Proof.
  intros M data len c w0 w1 w2 (n & t8 & t16 & Hn & H8 & H16 & Hrest) C0 C8 C16 M' c' D0 D8 D16.
  pose proof (low32_of_cells M c w0 n C0 Hn) as Hlow.
  pose proof (cell64_inj M (c + 8) _ _ C8 H8) as ->.
  pose proof (cell64_inj M (c + 16) _ _ C16 H16) as ->.
  exists n, t8, t16. split; [| split; [exact D8 | split; [exact D16 | exact Hrest]]].
  rewrite <- Hlow. apply cell64_low32. exact D0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint kzero_lookup (kn : list kentry) (b : expr) (k : Z) : option Z :=
  match kn with
  | [] => None
  | KZero (SA b' k') (ELit l) :: rest =>
      if (expr_eqb b' b && Z.eqb k' k)%bool then Some l else kzero_lookup rest b k
  | _ :: rest => kzero_lookup rest b k
  end.

Lemma kzero_lookup_sound : forall E M kn b k l,
  know_ok segs E M kn -> kzero_lookup kn b k = Some l -> (0 <= l < 2 ^ 64) ->
  zero M (bv_unsigned (edenot E b) + k) l.
Proof.
  intros E M kn b k l HK Hl Hl64. induction kn as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HK1 HK2]. cbn [kzero_lookup] in Hl.
  destruct K; try (apply IH; assumption).
  destruct a as [b' k']. destruct n; try (apply IH; assumption).
  destruct (expr_eqb b' b && (k' =? k))%bool eqn:Heq; [| apply IH; assumption].
  apply andb_prop in Heq as [Hb Hk]. apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. subst b' k'.
  injection Hl as ->.
  cbn [kentry_ok] in HK1. destruct HK1 as [Hfl Hz]. unfold elenZ in Hz. cbn [edenot] in Hz.
  rewrite u_small in Hz by lia. unfold estart in Hz. cbn [a_base a_off] in Hz.
  intros i Hi. apply Hz. exact Hi.
Qed.

End Lib.

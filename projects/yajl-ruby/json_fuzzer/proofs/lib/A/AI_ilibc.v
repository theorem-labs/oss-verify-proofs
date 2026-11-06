(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SFModel Image SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_stdio_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma rodata_cstr : forall m T (tb : list Z),
  mem_inv asegs m -> ro_bytes_b asegs T (zb tb ++ [Z_to_bv 8 0]) = true -> 0 <= T -> T + zlength tb + 1 <= 2^64 ->
  bytes_at asegs m T (zb tb ++ [Z_to_bv 8 0]).
Proof.
  intros m T tb MI RB H0 H1.
  pose proof (ro_cells_bytes_at asegs m T _ (ro_cells_image asegs m T _ MI RB H0 ltac:(rewrite length_app, zb_length; cbn [length]; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Strlen.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (s : list Z).
Hypothesis STR : bytes_at asegs m S (zb s ++ [Z_to_bv 8 0]).
Hypothesis HS : Forall (fun c => 0 < c < 256) s.
Hypothesis PSTR : forall a k, S <= a -> a + Z.of_nat k <= S + zlength s + 1 -> P (Z_to_bv 64 a, k).

Definition istrlen_post : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma istrlen_loop : forall k i a1 a2,
  Z.to_nat (zlength s - i) = k -> 0 <= i <= zlength s ->
  a1 = Z_to_bv 64 i ->
  evtA asegs P istrlen_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65574) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i a1 a2 Hk Hi ->.
  - (* [comment removed for export] *)
    assert (i = zlength s) by lia. subst i.
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app, zb_length in B. cbn [length] in B. unfold zlength in *.
    pose proof (u8ro_read asegs m S _ (Z.of_nat (length s)) (Z_to_bv 8 0) (Z_to_bv 64 (S + Z.of_nat (length s))) STR
                  ltac:(rewrite Nat2Z.id, nth_error_app2 by (rewrite zb_length; lia); rewrite zb_length, Nat.sub_diag; reflexivity) ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. zstepA. clear RD. zstepA. stepA. if_false. zstepA. stepA.
    apply evtA_done. unfold istrlen_post. do 2 eexists.
    replace (Z.of_nat (length s) + 1 - 1) with (Z.of_nat (length s)) by lia. reflexivity.
  - assert (i < zlength s) by lia.
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app, zb_length in B. cbn [length] in B. unfold zlength in *.
    assert (Hc : exists c, nth_error s (Z.to_nat i) = Some c /\ 0 < c < 256).
    { destruct (nth_error s (Z.to_nat i)) as [c|] eqn:E.
      - exists c. split; [reflexivity|]. rewrite Forall_nth in HS.
        pose proof (HS (Z.to_nat i) 0 ltac:(apply nth_error_lt in E; exact E)) as X. erewrite nth_error_nth in X by exact E. exact X.
      - apply nth_error_None in E. lia. }
    destruct Hc as (c & E & Hc).
    pose proof (u8ro_read asegs m S _ i (Z_to_bv 8 c) (Z_to_bv 64 (S + i)) STR
                  ltac:(rewrite nth_error_app1 by (rewrite zb_length; lia); unfold zb; rewrite nth_error_map, E; reflexivity) ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. zstepA. clear RD. zstepA. stepA.
    if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K by lia. lia. }
    eapply (IH (i + 1)); [lia | lia | f_equal; lia].
Qed.

Lemma internal_strlen_spec : forall a1 a2,
  evtA asegs P istrlen_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65570) fc None m (seg_rom asegs)).
Proof.
  intros a1 a2. zstepA. eapply (istrlen_loop (Z.to_nat (zlength s)) 0); [lia | unfold zlength; lia | reflexivity].
Qed.
End Strlen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint strchr_idx (tb : list Z) (c : Z) : option nat :=
  match tb with
  | [] => None
  | x :: tb' => if Z.eqb x c then Some 0%nat else option_map S (strchr_idx tb' c)
  end.
Definition strchr_res (T : Z) (tb : list Z) (c : Z) : Z :=
  match strchr_idx tb c with Some i => T + Z.of_nat i | None => 0 end.

Lemma strchr_idx_skip : forall tb c j,
  (forall i, (i < j)%nat -> exists x, nth_error tb i = Some x /\ x <> c) ->
  strchr_idx tb c = match strchr_idx (skipn j tb) c with Some i => Some (j + i)%nat | None => None end.
Proof.
  intros tb c j. revert tb. induction j as [|j IH]; intros tb H.
  - change (skipn 0 tb) with tb; cbn [Nat.add]. destruct (strchr_idx tb c); reflexivity.
  - destruct tb as [|x tb].
    + destruct (H 0%nat ltac:(lia)) as (y & Hy & _). discriminate.
    + cbn [skipn strchr_idx]. destruct (H 0%nat ltac:(lia)) as (y & Hy & Hne). cbn in Hy. injection Hy as ->.
      destruct (Z.eqb_spec y c); [contradiction|].
      rewrite (IH tb). 2:{ intros i Hi. exact (H (S i) ltac:(lia)). }
      destruct (strchr_idx (skipn j tb) c); reflexivity.
Qed.

Section Strchr.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (T : Z) (tb : list Z) (c : Z).
Hypothesis TB : bytes_at asegs m T (zb tb ++ [Z_to_bv 8 0]).
Hypothesis HT : Forall (fun x => 0 < x < 256) tb.
Hypothesis Hc : 0 < c < 256.
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + Z.of_nat (length tb) + 1 -> P (Z_to_bv 64 a, k).

Definition istrchr_post : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strchr_res T tb c)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

Notation tbz := (tb ++ [0]).

Lemma tbz_nth : forall j, (j <= length tb)%nat -> exists x, nth_error tbz j = Some x /\ 0 <= x < 256 /\ (x = 0 <-> j = length tb).
Proof.
  intros j Hj. destruct (Nat.eq_dec j (length tb)) as [->|NE].
  - exists 0. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn. split; [reflexivity|]. split; [lia|]. tauto.
  - destruct (nth_error tb j) as [x|] eqn:E.
    + exists x. rewrite nth_error_app1 by lia. split; [exact E|].
      rewrite Forall_nth in HT. pose proof (HT j 0 ltac:(lia)) as X. erewrite nth_error_nth in X by exact E.
      split; [lia|]. split; [lia| intros; lia].
    + apply nth_error_None in E. lia.
Qed.

Lemma tbz_read : forall j x a, nth_error tbz j = Some x -> (j <= length tb)%nat -> a = wa (T + Z.of_nat j) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 x].
Proof.
  intros j x a E Hj ->.
  pose proof (bytes_at_bound _ _ _ _ TB) as B. rewrite length_app, zb_length in B. cbn [length] in B.
  eapply (u8ro_read asegs m T _ (Z.of_nat j)); [exact TB | | lia | reflexivity].
  rewrite Nat2Z.id. replace (zb tb ++ [Z_to_bv 8 0]) with (zb tbz) by (unfold zb; rewrite map_app; reflexivity).
  unfold zb. rewrite nth_error_map, E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma istrchr_loop : forall k j x x11,
  (length tb - j)%nat = k -> (j <= length tb)%nat ->
  nth_error tbz j = Some x -> x <> c ->
  (forall i, (i <= j)%nat -> exists y, nth_error tbz i = Some y /\ y <> c) ->
  evtA asegs P istrchr_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + Z.of_nat j)) x11 (Z_to_bv 64 c) (Z_to_bv 64 x) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x654e0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j x x11 Hk Hj E Hx PREV.
  - assert (j = length tb) by lia. subst j.
    destruct (tbz_nth (length tb) ltac:(lia)) as (x' & E' & _ & X0). rewrite E in E'. injection E' as <-.
    assert (x = 0) by tauto. subst x.
    zstepA. if_true. zstepA. stepA.
    apply evtA_done. unfold istrchr_post, strchr_res.
    rewrite (strchr_idx_skip tb c (length tb)).
    2:{ intros i Hi. destruct (PREV i ltac:(lia)) as (y & Hy & Ny). exists y. rewrite nth_error_app1 in Hy by lia. tauto. }
    rewrite skipn_all. cbn [strchr_idx]. do 3 eexists. reflexivity.
  - assert (j < length tb)%nat by lia.
    destruct (tbz_nth j ltac:(lia)) as (x' & E' & R' & X0). rewrite E in E'. injection E' as <-.
    assert (x <> 0) by (intros X; apply X0 in X; lia).
    zstepA. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K0 by lia. lia. }
    destruct (tbz_nth (S j) ltac:(lia)) as (y & Ey & Ry & Y0).
    pose proof (tbz_read (S j) y (Z_to_bv 64 (T + Z.of_nat j + 1)) Ey ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 y) by lia. zstepA. zstepA. zstepA.
    if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit, ?unsigned_lit8 in K1 by lia.
      replace (T + Z.of_nat j + 1) with (T + Z.of_nat (S j)) by lia.
      eapply (IH (S j) y); [lia | lia | exact Ey | lia |].
      intros i Hi. destruct (Nat.eq_dec i (S j)) as [->|NE]; [exists y; split; [exact Ey| lia]|]. apply PREV. lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit, ?unsigned_lit8 in K1 by lia. assert (y = c) by lia. subst y.
      zstepA. stepA. apply evtA_done. unfold istrchr_post, strchr_res.
      assert (S j < length tb + 1)%nat by lia.
      assert (SJ : (S j <= length tb)%nat) by lia.
      assert (S j <> length tb) by (intros X; apply Y0 in X; lia).
      rewrite (strchr_idx_skip tb c (S j)).
      2:{ intros i Hi. destruct (PREV i ltac:(lia)) as (z & Hz & Nz). exists z. rewrite nth_error_app1 in Hz by lia. tauto. }
      rewrite nth_error_app1 in Ey by lia.
      destruct (skipn (S j) tb) as [|z tl] eqn:SK.
      { exfalso. apply (f_equal (@length Z)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
      assert (z = c).
      { pose proof (nth_error_skipn (S j) tb 0) as Q. rewrite SK, Nat.add_0_r, Ey in Q. cbn in Q. congruence. }
      subst z. cbn [strchr_idx]. rewrite Z.eqb_refl, Nat.add_0_r. do 3 eexists.
      replace (T + Z.of_nat (S j)) with (T + Z.of_nat j + 1) by lia. reflexivity.
Qed.

Lemma internal_strchr_spec : forall (x12 x13 : word),
  evtA asegs P istrchr_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 c) x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x654d0) fc None m (seg_rom asegs)).
Proof.
  intros x12 x13.
  destruct (tbz_nth 0 ltac:(lia)) as (x & E & R & X0).
  pose proof (tbz_read 0 x (Z_to_bv 64 (T + 0)) E ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 x) by lia. zstepA. zstepA.
  rewrite ?(land255 c) by lia.
  if_cases K; zify_cond K; rewrite ?unsigned_lit, ?unsigned_lit8, ?(land255 c) in K by lia.
  - (* [comment removed for export] *)
    replace T with (T + Z.of_nat 0) at 1 by lia.
    eapply (istrchr_loop (length tb) 0 x); [lia | lia | exact E | lia |].
    intros i Hi. replace i with 0%nat by lia. exists x. split; [exact E| lia].
  - (* [comment removed for export] *)
    stepA. apply evtA_done. unfold istrchr_post, strchr_res.
    destruct tb as [|z tl].
    { cbn in E. injection E as <-. exfalso. lia. }
    cbn in E. injection E as ->. assert (x = c) by lia. subst x. cbn [strchr_idx]. rewrite Z.eqb_refl.
    do 3 eexists. replace (T + Z.of_nat 0) with T by lia. reflexivity.
Qed.
End Strchr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition imemset_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (D n v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].

Section Memset.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (D n v : Z).
Hypothesis HD : 0 < D.
Hypothesis HDN : D + n < 2^63.
Hypothesis HN : 1 <= n.
Hypothesis ODD : Z.testbit n 3 = true.
Hypothesis HV : 0 <= v < 256.
Hypothesis PD : forall a k, D <= a -> a + Z.of_nat k <= D + n -> P (Z_to_bv 64 a, k).

Notation POST := (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc D n v m).

(* [comment removed for export] *)
Lemma imemset_loop : forall k i m1 junk,
  Z.to_nat (n - i) = k -> 0 < i < n ->
  mem_inv asegs m1 -> munch [(D, D + n)] m m1 -> wmono asegs m m1 ->
  rw_cells asegs m1 D [CB (Z.to_nat i) (repeat (Z_to_bv 8 v) (Z.to_nat i))] ->
  rw_cells asegs m1 (D + i) [CB (Z.to_nat (n - i)) junk] ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 v) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65434) fc None m1 (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i m1 junk Hk Hi MI MU WM DONE FR; [lia|].
  pose proof (rw_cells_bound _ _ _ _ FR) as BF.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat (n - i)) _ [] [1; Z.to_nat (n - i) - 1]%nat) in FR; [| cbn; lia].
  cbn [mk_CB_cells app] in FR.
  remember (D + i) as Di eqn:HDi.  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  subst Di.
  zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    lazymatch goal with FR2 : rw_cells asegs m2 (D + i) ?cs, DONE2 : rw_cells asegs m2 D _ |- _ =>
      apply (proj1 (rw_cells_app asegs m2 (D + i) [_] [_])) in FR2; destruct FR2 as [NEWB REST];
      cbn [cells_size csize] in REST; rewrite Nat.add_0_r in REST; change (Z.of_nat 1) with 1 in REST;
      rewrite (Z.mod_small v 256) in NEWB by lia;
      replace (D + i) with (D + Z.of_nat (cells_size [CB (Z.to_nat i) (repeat (Z_to_bv 8 v) (Z.to_nat i))])) in NEWB
        by (cbn [cells_size csize]; lia);
      pose proof (proj2 (rw_cells_app asegs m2 D [CB (Z.to_nat i) (repeat (Z_to_bv 8 v) (Z.to_nat i))] [_]) (conj DONE2 NEWB)) as D3;
      cbn [app] in D3; apply (rw_cells_merge asegs m2 D [] [CB (Z.to_nat i) (repeat (Z_to_bv 8 v) (Z.to_nat i)); C1 (Z_to_bv 8 v)] []) in D3;
      cbn [app cells_size cells_bytes csize cbytes] in D3;
      rewrite Nat.add_0_r in D3;
      replace (repeat (Z_to_bv 8 v) (Z.to_nat i) ++ [Z_to_bv 8 v]) with (repeat (Z_to_bv 8 v) (Z.to_nat i + 1)) in D3
        by (rewrite repeat_app; reflexivity);
      clear DONE2 NEWB
    end end.
  if_cases K; zify_cond K.
  - replace (D + i + 1) with (D + (i + 1)) in * by lia.
    eapply (IH (i + 1)); [lia | lia | eassumption | eassumption | eassumption | |].
    + replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia. assumption.
    + replace (Z.to_nat (n - (i + 1))) with (Z.to_nat (n - i) - 1)%nat by lia. eassumption.
  - (* [comment removed for export] *)
    assert (i + 1 = n) by lia.
    stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
    apply evtA_done. unfold imemset_post. do 3 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    replace (Z.to_nat n) with (Z.to_nat i + 1)%nat by lia. assumption.
Qed.

Lemma internal_memset_spec : forall x13 junk,
  2 <= n ->
  mem_inv asegs m -> rw_cells asegs m D [CB (Z.to_nat n) junk] ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 v) (Z_to_bv 64 n) x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6541c) fc None m (seg_rom asegs)).
Proof.
  intros x13 junk HN2 MI FR.
  pose proof (munch_refl [(D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  { exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K by lia.
    assert (X : Z.testbit (Z.land (Z.lor n D) 15) 3 = true).
    { rewrite Z.land_spec, Z.lor_spec, ODD. cbn. reflexivity. }
    rewrite K in X. cbn in X. discriminate. }
  zstepA. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K1 by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [1; Z.to_nat n - 1]%nat) in FR; [| cbn; lia].
  cbn [mk_CB_cells app] in FR.
  zstepA. (* [comment removed for export] *) zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K2 by lia. lia. }
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    lazymatch goal with FR2 : rw_cells asegs m2 D ?cs |- _ =>
      apply (proj1 (rw_cells_app asegs m2 D [_] [_])) in FR2; destruct FR2 as [NEWB REST];
      cbn [cells_size csize] in REST; rewrite Nat.add_0_r in REST; change (Z.of_nat 1) with 1 in REST;
      rewrite (Z.mod_small v 256) in NEWB by lia;
      apply (rw_cells_merge asegs m2 D [] [C1 (Z_to_bv 8 v)] []) in NEWB; cbn [app cells_size cells_bytes csize cbytes Nat.add] in NEWB
    end end.
  eapply (imemset_loop (Z.to_nat (n - 1)) 1); [lia | lia | eassumption | eassumption | eassumption | |].
  - cbn [Z.to_nat Pos.to_nat repeat]. exact NEWB.
  - replace (Z.to_nat (n - 1)) with (Z.to_nat n - 1)%nat by lia. exact REST.
Qed.
End Memset.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_dioux : Z := 0x1c53e.
Definition S_dioux : list Z := [100; 105; 111; 117; 120; 88; 110].   (* [comment removed for export] *)

Lemma S_dioux_bytes : forall m, mem_inv asegs m -> bytes_at asegs m T_dioux (zb S_dioux ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply rodata_cstr; [exact MI | vm_compute; reflexivity | unfold T_dioux; lia | unfold T_dioux, zlength; cbn; lia]. Qed.

Definition fgvs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma fgvs_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (c LM lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 LM -> In c S_dioux ->
  bytes_at asegs m LM [Z_to_bv 8 0] ->
  (LM + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= LM) ->
  (forall a k, bv_unsigned sp - 32 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  P (Z_to_bv 64 LM, 1%nat) ->
  evtA asegs P (fgvs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x48d08) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros SK LOC LO MI -> -> HIN LMB LMD PSTK PIMG PLM.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (Hc : 0 < c < 256) by (cbn in HIN; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat SK.
  do 5 stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  change (Z_to_bv 64 116030) with (Z_to_bv 64 T_dioux).
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@internal_strchr_spec P) with (m := mx) (T := T_dioux) (tb := S_dioux) (c := c) | intros ms' (x11' & x12' & x13' & ->); ret_pc_lit ] end.
  1:{ apply S_dioux_bytes; assumption. }
  1:{ unfold S_dioux; repeat constructor; lia. }
  1:{ exact Hc. }
  1:{ intros; apply PIMG; unfold T_dioux in *; cbn [length S_dioux] in *; lia. }
  assert (HR : exists i, (i < 7)%nat /\ strchr_res T_dioux S_dioux c = T_dioux + Z.of_nat i).
  { cbn in HIN.
    destruct HIN as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
      [exists 0%nat | exists 1%nat | exists 2%nat | exists 3%nat | exists 4%nat | exists 5%nat | exists 6%nat];
      (split; [lia | vm_compute; reflexivity]). }
  destruct HR as (ir & Hir & HR). rewrite HR. unfold T_dioux.
  zstepA. (* [comment removed for export] *) if_cases K0; zify_cond K0.
  { exfalso. rewrite <- ?unsigned_lit_land, ?unsigned_lit in K0 by lia. lia. }
  lazymatch goal with LMBx : bytes_at asegs ?mx LM _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8ro_read asegs _ LM [Z_to_bv 8 0] 0 (Z_to_bv 8 0) (Z_to_bv 64 LM) LMBx eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. cbv beta. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K1 by lia. cbn in K1. lia. }
  zstepA. (* [comment removed for export] *) if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit8 in K2 by lia. lia. }
  stepA. (* [comment removed for export] *)
  do 5 stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  lazymatch goal with FR : rw_cells asegs _ (bv_unsigned sp + -32) _, SK' : stk asegs _ lo _ |- _ => release_frame FR SK' (bv_unsigned sp) end.
  apply evtA_done. unfold fgvs_post. do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
End RC__1.

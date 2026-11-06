(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv SjS2Inv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS2Tab.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2Lin S2Dig S2StrVC S2G2 S2WalkVC S2WalkLem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation u := bv_unsigned.

Lemma find_atom_in : forall id l args, find_atom id l = Some args -> In (ST.GA id args) l.
Proof.
  intros id l args. induction l as [|[i a] r IH]; cbn [find_atom]; [discriminate|].
  cbn [ST.g_id ST.g_args]. destruct (Nat.eqb i id) eqn:E.
  - intros H. injection H as <-. apply Nat.eqb_eq in E. subst. left. reflexivity.
  - intros H. right. exact (IH H).
Qed.

Lemma atoms_of_in : forall id l args, In args (atoms_of id l) -> In (ST.GA id args) l.
Proof.
  intros id l args H. unfold atoms_of in H. apply in_map_iff in H as ([i a] & <- & Hin). apply filter_In in Hin as [Hin E].
  cbn [ST.g_id] in E. apply Nat.eqb_eq in E. subst. exact Hin.
Qed.

Lemma rrec_some : forall w s a v, rrec w s = Some (a, v) -> s = SCReadBase a w false (EVar v).
Proof.
  intros w s a v H. destruct s; cbn [rrec] in H; try discriminate.
  match type of H with (match ?e with _ => _ end) = _ => destruct e eqn:He; try discriminate end.
  match type of H with (if ?cc then _ else _) = _ => destruct cc eqn:Ec; [|discriminate] end.
  injection H as <- <-. apply andb_prop in Ec as [E1 E2]. apply Nat.eqb_eq in E1. apply negb_true_iff in E2. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrec_den : forall segs m E l w s a v, scs_denot segs m E l -> In s l -> rrec w s = Some (a, v) ->
  exists bs, rdn segs m (adenot E a) w = Some bs /\ Z_to_bv 64 (bytes_le_to_Z bs) = ev E v.
Proof.
  intros segs m E l w s a v HP Hin H. apply rrec_some in H. subst s.
  pose proof (proj1 (Forall_forall _ _) HP _ Hin) as (bs & Hr & Hv). cbn [sc_denot extz] in Hv. exists bs. split; [exact Hr|].
  cbn [edenot] in Hv. exact Hv.
Qed.

Lemma rdn_length' : forall segs m a w bs, rdn segs m a w = Some bs -> length bs = w.
Proof. intros segs m a w bs H. exact (rdn_length segs m w a bs H). Qed.

Lemma u_x4 : forall E v, u (ev E v) < 2 ^ 32 -> u (edenot E (x4 v)) = u (ev E v).
Proof.
  intros E v H. unfold x4. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  change (2 ^ (8 * 4)) with (2 ^ 32). pose proof (u_rng (ev E v)). rewrite (Z.mod_small _ (2 ^ 32)) by lia. apply u_lit. lia.
Qed.

Lemma u_x1 : forall E v, u (ev E v) < 256 -> u (edenot E (x1 v)) = u (ev E v).
Proof.
  intros E v H. unfold x1. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. pose proof (u_rng (ev E v)). rewrite (Z.mod_small _ 256) by lia. apply u_lit. lia.
Qed.


Lemma mem_denot_app : forall E base l1 l2, mem_denot E base (l1 ++ l2) = mem_denot E (mem_denot E base l2) l1.
Proof. intros E base l1 l2. induction l1 as [|[a w v] r IH]; cbn [app mem_denot]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma log_flat_app : forall E l1 l2, log_flat E (l1 ++ l2) -> log_flat E l1 /\ log_flat E l2.
Proof.
  intros E l1 l2. induction l1 as [|[a w v] r IH]; cbn [app log_flat]; [intros H; split; [exact I | exact H]|].
  intros (H1 & H2 & H3). destruct (IH H3) as [A B]. split; [split; [exact H1| split; [exact H2 | exact A]] | exact B].
Qed.

(* [comment removed for export] *)
Lemma mem_denot_apart_gen : forall segs E M kn lg W, know_ok segs E M kn -> log_flat E lg -> SG.log_apart kn lg W = true ->
  forall base x, (exists w, In w W /\ let '(lo, hi) := SG.win_den E w in (lo <= bv_unsigned x < hi)%Z) ->
  mem_denot E base lg x = base x.
Proof.
  intros segs E M kn lg W HK. induction lg as [|[a w v] rest IH]; intros Hlf Hap base x Hin; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf'). cbn [SG.log_apart forallb] in Hap. apply andb_prop in Hap as [Ha1 Ha2].
  cbn [mem_denot]. rewrite <- (IH Hlf' Ha2 base x Hin).
  destruct Hin as ([[b off] n] & HinW & Hx). cbn [SG.win_den] in Hx.
  pose proof (proj1 (forallb_forall _ _) Ha1 _ HinW) as Hap1. cbn beta iota in Hap1. cbn [e_addr e_width] in Hap1.
  destruct a as [ab ak]. cbn [a_base a_off] in Hap1.
  pose proof (ranges_apart_x_sound segs E M kn ab ak (elen w) b off n HK Hap1) as R.
  rewrite SG.elenZ_elen8' in R by exact Hw8. unfold estart in R. cbn [a_base a_off] in R. unfold elenZ in R.
  pose proof (flat_u E _ _ Hfa) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
  apply wbytes_outside.
  - rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
  - rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Lemma newest_split : forall kn a lg s pre, newest kn a lg = Some (s, pre) ->
  exists rest, lg = pre ++ s :: rest /\ e_width s = 4%nat /\ same_addr kn (eaddl (a_base (e_addr s)) (a_off (e_addr s))) a = true.
Proof.
  intros kn a lg. induction lg as [|x r IH]; intros s pre H; cbn [newest] in H; [discriminate|].
  destruct (Nat.eqb (e_width x) 4 && same_addr kn (eaddl (a_base (e_addr x)) (a_off (e_addr x))) a)%bool eqn:C.
  - injection H as <- <-. apply andb_prop in C as [C1 C2]. apply Nat.eqb_eq in C1. exists r. split; [reflexivity|]. split; assumption.
  - destruct (newest kn a r) as [[s' pre']|] eqn:Hn; [|discriminate]. injection H as <- <-.
    destruct (IH s' pre' eq_refl) as (rest & -> & W & A). exists rest. split; [reflexivity|]. split; assumption.
Qed.

Lemma newest1_split : forall kn a lg s pre, newest1 kn a lg = Some (s, pre) ->
  exists rest, lg = pre ++ s :: rest /\ e_width s = 1%nat /\ same_addr kn (eaddl (a_base (e_addr s)) (a_off (e_addr s))) a = true.
Proof.
  intros kn a lg. induction lg as [|x r IH]; intros s pre H; cbn [newest1] in H; [discriminate|].
  destruct (Nat.eqb (e_width x) 1 && same_addr kn (eaddl (a_base (e_addr x)) (a_off (e_addr x))) a)%bool eqn:C.
  - injection H as <- <-. apply andb_prop in C as [C1 C2]. apply Nat.eqb_eq in C1. exists r. split; [reflexivity|]. split; assumption.
  - destruct (newest1 kn a r) as [[s' pre']|] eqn:Hn; [|discriminate]. injection H as <- <-.
    destruct (IH s' pre' eq_refl) as (rest & -> & W & A). exists rest. split; [reflexivity|]. split; assumption.
Qed.

Lemma same_addr_den : forall segs E m kn x y, know_ok segs E m kn -> same_addr kn x y = true -> edenot E x = edenot E y.
Proof.
  intros segs E m kn x y HK H. unfold same_addr in H. apply orb_prop in H as [H|H]; [exact (leq_den E x y H)|].
  destruct (decide_branch kn BC_EQ x y) as [[]|] eqn:D; cbn in H; try discriminate.
  pose proof (decide_branch_sound segs E m kn BC_EQ x y true HK D) as B. cbn [branch_taken] in B. unfold bv_eqb in B.
  apply Z.eqb_eq in B. apply bv_eq. exact B.
Qed.

(* [comment removed for export] *)
Lemma tden_filter : forall E (p : Z * expr -> bool) ts,
  tden E ts = tden E (List.filter p ts) + tden E (List.filter (fun t => negb (p t)) ts).
Proof.
  intros E p ts. induction ts as [|[k a] r IH]; cbn [tden List.filter]; [reflexivity|].
  destruct (p (k, a)); cbn [negb tden]; rewrite IH; lia.
Qed.

Lemma tden_lanes : forall E ts, forallb is_lane ts = true ->
  0 <= tden E ts <= Z.of_nat (length ts) * (255 * 2 ^ 48).
Proof.
  intros E ts. induction ts as [|[k a] r IH]; cbn [tden forallb length]; [lia|].
  intros H. apply andb_prop in H as [H1 H2]. specialize (IH H2). unfold is_lane in H1. cbn [fst snd] in H1.
  destruct a as [| | | | | |sx lo n a'| ]; try discriminate. destruct sx; try discriminate.
  destruct lo; try discriminate. destruct n as [|[|n]]; try discriminate. destruct a' as [|v| | | | | |]; try discriminate.
  apply andb_prop in H1 as [H1 H3]. apply Z.leb_le in H1. apply Z.leb_le in H3.
  assert (U : 0 <= uE E (EExt false 0 1 (EVar v)) <= 255).
  { unfold uE. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
    change (2 ^ (8 * 1)) with 256. pose proof (Z.mod_pos_bound (bv_unsigned (ev E v)) 256 ltac:(lia)).
    rewrite u_lit by lia. lia. }
  nia.
Qed.

Lemma land_cf0 : forall A B, Z.land (Z.lor (Z.land A C0F) (Z.land B CF0)) CF0 = Z.land B CF0.
Proof.
  intros A B. rewrite Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
  change (Z.land C0F CF0) with 0. change (Z.land CF0 CF0) with CF0. rewrite Z.land_0_r, Z.lor_0_l. reflexivity.
Qed.

Lemma Forall_flat_map' : forall {T1 T2 : Type} (P : T2 -> Prop) (f : T1 -> list T2) l, (forall x, In x l -> Forall P (f x)) -> Forall P (flat_map f l).
Proof.
  intros T1 T2 P f l H. apply Forall_forall. intros y Hy. apply in_flat_map in Hy as (x & Hx & Hy).
  exact (proj1 (Forall_forall _ _) (H x Hx) y Hy).
Qed.

Section Sound.
  Variable segs : list Segment.
  Variables data idxs : list Z.
  Variable MF : Z.
  Hypothesis MF_rng : 0 <= MF <= 2 ^ 30.
  Variable TD : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).
  Local Notation GP := (gp2 segs data idxs).
  Local Notation n := (zlength idxs - 3).
  Local Notation len := (zlength data).

  Section Ctx.
    Variables (E : env) (m : word -> option byte) (c : SG.vc).
    Hypothesis HK : know_ok segs E m (SG.vc_kn c).
    Hypothesis HP : scs_denot segs m E (SG.vc_path c).
    Hypothesis HS : SG.gholds GP E m (SG.vc_src c).

    Lemma src_holds : forall id args, In (ST.GA id args) (SG.vc_src c) -> GP id (map (edenot E) args) m.
    Proof. intros id args H. exact (proj1 (Forall_forall _ _) HS _ H). Qed.

    (* [comment removed for export] *)
    Variables (X NN B L : expr).
    Hypothesis HX : find_atom 2 (SG.vc_src c) = Some [X; NN].
    Hypothesis HB : find_atom 1 (SG.vc_src c) = Some [B; L].

    Lemma gidx_ctx : u (edenot E NN) = n /\ S1OUT data idxs n /\ u (edenot E X) + 4 * (n + 3) < 2 ^ 64 /\
                     mbytes m (u (edenot E X)) (u32bytes idxs).
    Proof. exact (src_holds 2 [X; NN] (find_atom_in _ _ _ HX)). Qed.
    Lemma gbuf_ctx : u (edenot E L) = len /\ u (edenot E B) + u (edenot E L) + 64 < 2 ^ 64 /\
                     Forall (fun c => 0 <= c < 256) data /\ mbytes m (u (edenot E B)) (bufbytes data).
    Proof. exact (src_holds 1 [B; L] (find_atom_in _ _ _ HB)). Qed.

    Lemma zlen_idxs : zlength idxs = n + 3.
    Proof. lia. Qed.

    (* [comment removed for export] *)
    Lemma r1_sound : forall kn s, know_ok segs E m kn -> In s (SG.vc_path c) ->
      know_ok segs E m (fst (r1_read segs MF kn X NN L s)) /\ forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd (r1_read segs MF kn X NN L s)).
    Proof.
      intros kn s HKn Hin. unfold r1_read.
      destruct (rrec 4 s) as [[a v]|] eqn:Hr; [|split; [constructor | intros; constructor]].
      destruct (kimp segs kn (KAlign (rel a X) 4) && kimp segs kn (KRange (rel a X) 0 (KOMAX MF)) && kimp segs kn (KRange NN 0 MF)
                && kimp segs kn (KRange L 0 MF) && kimp segs kn (KRange (esub2 (eaddl (emul 4 NN) 8) (rel a X)) 0 (KOMAX MF)))%bool eqn:C;
        [|split; [constructor | intros; constructor]].
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      rename C into C1. match goal with H1 : kimp _ _ (KRange (rel a X) _ _) = true, H2 : kimp _ _ (KRange NN _ _) = true,
        H3 : kimp _ _ (KRange L _ _) = true, H4 : kimp _ _ (KRange (esub2 _ _) _ _) = true |- _ =>
        rename H1 into C2; rename H2 into C3; rename H3 into C4; rename H4 into C5 end.
      destruct gidx_ctx as (HN & HS1 & HXb & HXm). destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      pose proof (kimp_ok segs E m kn _ HKn C1) as [_ A4]. pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R2.
      pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3. pose proof (kimp_range segs E m kn _ _ _ HKn C4) as R4.
      set (ko := u (edenot E (rel a X))) in *.
      assert (EMUL : forall k, 0 <= k <= 8 -> u (edenot E (emul k NN)) = k * n).
      { intros k Hk. rewrite u_emul', HN. rewrite (Z.mod_small k) by lia. apply Z.mod_small. nia. }
      assert (R5 : 0 <= 4 * n + 8 - ko <= KOMAX MF).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C5) as R. rewrite u_esub2, u_eaddl, EMUL in R by lia.
        try unfold KOMAX in *. rewrite (Z.mod_small 8) in R by lia. rewrite (Z.mod_small (4 * n + 8)) in R by lia.
        apply sub_exact; try unfold KOMAX in *; lia. }
      set (j := ko / 4).
      assert (Hko : ko = 4 * j) by (unfold j; pose proof (Z.div_mod ko 4 ltac:(lia)); lia).
      assert (Hj : 0 <= j <= n + 2) by (try unfold KOMAX in *; lia).
      (* [comment removed for export] *)
      destruct (rrec_den segs m E _ 4 s a v HP Hin Hr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E X) + 4 * j).
      { rewrite (rel_addr E a X) by (fold ko; lia). fold ko. lia. }
      assert (Hbs : bs = word_to_le_bytes 4 (Z_to_bv 64 (znth idxs j))).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)) in Hrd. rewrite Haddr in Hrd.
        rewrite (mbytes_rdn segs m (u (edenot E X)) (u32bytes idxs) (4 * j) 4 HXm) in Hrd;
          [| pose proof (u_rng (edenot E X)); lia | lia | rewrite zlength_u32; lia | rewrite zlength_u32; lia].
        injection Hrd as <-. apply u32bytes_cell. lia. }
      pose proof (idx_rng data idxs HS1 j Hj) as Ij.
      assert (Vv : u (ev E v) = znth idxs j).
      { rewrite <- Hv, Hbs, le4_val by lia. apply u_lit. lia. }
      assert (VX : u (edenot E (x4 v)) = znth idxs j) by (rewrite u_x4; lia).
      split.
      - cbn [fst]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split.
        + destruct (kimp segs kn (KRange (esub2 (eaddl (emul 4 NN) 4) (rel a X)) 0 (KOMAX MF))); [|constructor].
          constructor; [cbn [kentry_ok]; lia|]. constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2, VX, HLen.
          rewrite Z.mod_small by lia. lia.
        + destruct (kimp segs kn (KRange (esub2 (emul 4 NN) (eaddl (rel a X) 4)) 0 (KOMAX MF))) eqn:C6; [|constructor].
          constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2, VX, HLen.
          pose proof (kimp_range segs E m kn _ _ _ HKn C6) as R. rewrite u_esub2, u_eaddl, EMUL in R by lia. fold ko in R.
          rewrite (Z.mod_small 4) in R by lia. rewrite (Z.mod_small (ko + 4)) in R by (try unfold KOMAX in *; lia).
          assert (0 <= 4 * n - (ko + 4) <= KOMAX MF) by (apply sub_exact; try unfold KOMAX in *; lia).
          pose proof (idx_real data idxs HS1 j ltac:(lia)). destruct HS1 as [_ _ Hlt _ _ _]. pose proof (Hlt j ltac:(lia)).
          rewrite Z.mod_small by lia. lia.
      - intros M. cbn [snd]. constructor; [|constructor]. cbn [ST.g_id ST.g_args map gp2]. fold ko.
        split; [rewrite Hko, Z.mul_comm; apply Z.mod_mul; lia|]. split; [unfold j in *; lia|]. rewrite VX. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma r2_sound : forall kn s, know_ok segs E m kn -> In s (SG.vc_path c) -> know_ok segs E m (r2_read segs kn (SG.vc_src c) s).
    Proof.
      intros kn s HKn Hin. unfold r2_read.
      destruct (rrec 4 s) as [[a v]|] eqn:Hr; [|constructor].
      unfold know_ok. apply Forall_forall. intros K HKin. apply in_flat_map in HKin as (args & Hargs & HKin).
      destruct args as [|OC [|D [|BW [|? ?]]]]; try (cbn in HKin; contradiction).
      match type of HKin with In _ (if ?cc then _ else _) => destruct cc eqn:C; [|cbn in HKin; contradiction] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H1 : kimp _ _ (KRange (rel a OC) _ _) = true, H2 : kimp _ _ (KRange (esub2 _ _) _ _) = true,
        H3 : kimp _ _ (KRange D _ _) = true, H4 : kimp _ _ (KRange BW _ _) = true |- _ =>
        rename H1 into C2; rename H2 into C3; rename H3 into C4; rename H4 into C5 end.
      pose proof (kimp_ok segs E m kn _ HKn C) as [_ A8]. pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R2.
      pose proof (kimp_range segs E m kn _ _ _ HKn C4) as R4. pose proof (kimp_range segs E m kn _ _ _ HKn C5) as R5.
      set (dof := u (edenot E (rel a OC))) in *.
      assert (R3 : 0 <= 8 * u (edenot E D) - dof <= 8184).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R. rewrite u_esub2, u_emul' in R.
        rewrite (Z.mod_small 8) in R by lia. rewrite (Z.mod_small (8 * _)) in R by lia. apply sub_exact; lia. }
      pose proof (src_holds 5 [OC; D; BW] (atoms_of_in _ _ _ Hargs)) as G. cbn [map gp2] in G. destruct G as (Gb & Gc).
      set (i := dof / 8). assert (Hi : dof = 8 * i) by (unfold i; pose proof (Z.div_mod dof 8 ltac:(lia)); lia).
      destruct (Gc i ltac:(lia)) as (t & Ht0 & Ht & Hm).
      destruct (rrec_den segs m E _ 4 s a v HP Hin Hr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E OC) + 8 * i) by (rewrite (rel_addr E a OC) by (fold dof; lia); fold dof; lia).
      rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)) in Hrd. rewrite Haddr in Hrd. unfold mcell in Hm.
      pose proof (u_rng (edenot E OC)).
      rewrite <- (Z.add_0_r (u (edenot E OC) + 8 * i)) in Hrd.
      rewrite (mbytes_rdn segs m _ _ 0 4 Hm) in Hrd by (rewrite ?length_Z_to_le_bytes; lia). injection Hrd as <-.
      change (Z_to_bv 64 (bytes_le_to_Z (Z_to_le_bytes 4 t)) = ev E v) in Hv.
      rewrite bytes_le_to_Z_of_le_bytes in Hv by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hv.
      assert (Vv : u (ev E v) = t mod 2 ^ 32) by (rewrite <- Hv; apply u_lit; pose proof (Z.mod_pos_bound t (2 ^ 32)); lia).
      pose proof (Z.mod_pos_bound t (2 ^ 32) ltac:(lia)). pose proof (Z.mod_le t (2 ^ 32) ltac:(lia) ltac:(lia)).
      assert (VX : u (edenot E (x4 v)) = t mod 2 ^ 32) by (rewrite u_x4; lia).
      destruct HKin as [<-|[<-|[]]]; cbn [kentry_ok].
      - rewrite VX. lia.
      - rewrite u_esub2, u_emul', VX. rewrite (Z.mod_small 8) by lia. rewrite (Z.mod_small (8 * _)) by lia.
        rewrite Z.mod_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma r3_sound : forall kn s, know_ok segs E m kn -> In s (SG.vc_path c) -> know_ok segs E m (r3_read segs MF kn B L s).
    Proof.
      intros kn s HKn Hin. unfold r3_read.
      destruct (rrec 1 s) as [[a b]|] eqn:Hr; [|constructor].
      match goal with |- know_ok _ _ _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H2 : kimp _ _ (KRange (esub2 _ _) _ _) = true, H3 : kimp _ _ (KRange L _ _) = true,
        H4 : (kimp _ _ (KRange (x1 b) _ _) || _)%bool = true |- _ =>
        rename H2 into C2; rename H3 into C3; rename H4 into C4 end.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      pose proof (kimp_range segs E m kn _ _ _ HKn C) as R1. pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3.
      set (xe := u (edenot E (rel a B))) in *.
      assert (R2 : 0 <= u (edenot E L) + 63 - xe <= MF + 63).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R. rewrite u_esub2, u_eaddl in R.
        rewrite (Z.mod_small 63) in R by lia. rewrite (Z.mod_small (_ + 63)) in R by lia. apply sub_exact; lia. }
      destruct (rrec_den segs m E _ 1 s a b HP Hin Hr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E B) + xe) by (rewrite (rel_addr E a B) by (fold xe; lia); fold xe; lia).
      rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)) in Hrd. rewrite Haddr in Hrd.
      pose proof (u_rng (edenot E B)).
      rewrite (mbytes_rdn segs m _ _ xe 1 HBm) in Hrd by (rewrite ?bufbytes_length; lia). injection Hrd as <-.
      assert (Hb1 : 1 <= u (ev E b) <= 255).
      { apply orb_prop in C4 as [C4|C4]; pose proof (kimp_range segs E m kn _ _ _ HKn C4) as R.
        - rewrite u_x1 in R; [lia|].
          rewrite <- Hv. rewrite u_litm. pose proof (Z.mod_pos_bound (bytes_le_to_Z (firstn 1 (skipn (Z.to_nat xe) (bufbytes data)))) (2 ^ 64)).
          destruct (skipn (Z.to_nat xe) (bufbytes data)) as [|b0 r0]; cbn [firstn bytes_le_to_Z]; [cbn; lia|].
          rewrite Z.shiftl_0_l, Z.lor_0_r. pose proof (bv_unsigned_in_range _ b0) as Rb. unfold bv_modulus in Rb.
          change (2 ^ Z.of_N 8) with 256 in Rb. rewrite Z.mod_small by lia. lia.
        - exact R. }
      assert (Hxe : xe < u (edenot E L)).
      { destruct (Z_lt_ge_dec xe (u (edenot E L))) as [Lt|Ge]; [exact Lt|]. exfalso.
        assert (Hz : skipn (Z.to_nat xe) (bufbytes data) = Z_to_bv 8 0 :: skipn (S (Z.to_nat xe)) (bufbytes data)).
        { pose proof (bufbytes_nth data xe HBd ltac:(lia)) as Hn. rewrite byte_at_past in Hn by (unfold zlength in HLen; lia).
          assert (Hl : (Z.to_nat xe < length (bufbytes data))%nat) by (pose proof (bufbytes_length data); lia).
          rewrite <- Hn. clear -Hl. revert Hl. generalize (bufbytes data) as l. generalize (Z.to_nat xe) as k.
          induction k as [|k IH]; intros [|x l] Hl; cbn in Hl |- *; try lia; [reflexivity|]. apply IH. lia. }
        rewrite Hz in Hv. cbn [firstn bytes_le_to_Z] in Hv.
        assert (Z0 : u (ev E b) = 0) by (rewrite <- Hv; rewrite u_litm; reflexivity). lia. }
      constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2. fold xe. rewrite Z.mod_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma u_srl_lit : forall a s, 0 <= s < 64 -> u (edenot E (EAlu ALU_SRL a (ELit s))) = u (edenot E a) / 2 ^ s.
    Proof.
      intros a s Hs. cbn [edenot]. rewrite alu_srl. unfold v_srl. rewrite (u_lit s) by lia. rewrite (Z.mod_small s) by lia.
      rewrite Z.shiftr_div_pow2 by lia. apply u_lit. pose proof (u_rng (edenot E a)).
      split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (u (edenot E a)); [apply Z.div_le_upper_bound; [lia|] | lia].
      pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)). nia.
    Qed.

    Lemma srl_sound : forall kn e, know_ok segs E m kn -> know_ok segs E m (srl_facts segs kn e).
    Proof.
      intros kn e HKn. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo nn a IHa|sx k i nn];
        cbn [srl_facts]; try constructor; try (apply Forall_app; split; assumption); try assumption.
      destruct op; try (apply Forall_app; split; assumption).
      destruct b as [s|v|op b1 b2|op b1 b2|op b1 b2|op b1 b2|sx lo nn b1|sx k i nn]; try (apply Forall_app; split; assumption).
      apply Forall_app. split; [|exact IHa].
      destruct (Z.leb 0 s && Z.ltb s 64)%bool eqn:Hs; [|constructor]. apply andb_prop in Hs as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (u_rng (edenot E a)) as Ra. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as P.
      assert (P64 : 2 ^ s < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
      pose proof (u_srl_lit a s (conj H1 H2)) as Hq.
      pose proof (Z.div_mod (u (edenot E a)) (2 ^ s) ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound (u (edenot E a)) (2 ^ s) ltac:(lia)) as Mb.
      constructor.
      - cbn [kentry_ok]. rewrite u_esub2, u_emul', Hq. rewrite (Z.mod_small (2 ^ s)) by lia.
        rewrite (Z.mod_small (2 ^ s * _)) by (split; [apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; lia] | lia]).
        rewrite Z.mod_small by lia. lia.
      - destruct (kimp segs kn (KRange a 0 (2 ^ 34))) eqn:C; [|constructor]. constructor; [|constructor].
        pose proof (kimp_range segs E m kn _ _ _ HKn C) as R. cbn [kentry_ok]. rewrite Hq. rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_le_mono; lia.
    Qed.

    (* [comment removed for export] *)
    Definition tok_holds (args : list expr) : Prop := GP 3 (map (edenot E) args) m.
    Definition ge_holds (args : list expr) : Prop := GP 4 (map (edenot E) args) m.

    Lemma r4_sound : forall kn args, know_ok segs E m kn -> tok_holds args -> know_ok segs E m (r4_tok segs MF kn NN L args).
    Proof.
      intros kn args HKn Ht. unfold r4_tok. destruct args as [|K [|VX [|? ?]]]; try constructor.
      match goal with |- know_ok _ _ _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H2 : kimp _ _ (KRange (esub2 (eaddl _ _) _) _ _) = true, H3 : kimp _ _ (KRange K _ _) = true,
        H4 : kimp _ _ (KRange NN _ _) = true, H5 : kimp _ _ (KRange L _ _) = true |- _ =>
        rename H2 into C2; rename H3 into C3; rename H4 into C4; rename H5 into C5 end.
      pose proof (kimp_range segs E m kn _ _ _ HKn C5) as R5.
      destruct gidx_ctx as (HN & HS1 & HXb & HXm). destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      unfold tok_holds in Ht. cbn [map gp2] in Ht. destruct Ht as (Hk4 & Hkj & Hv).
      pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3. pose proof (kimp_range segs E m kn _ _ _ HKn C4) as R4.
      set (j := u (edenot E K) / 4) in *.
      assert (Hko : u (edenot E K) = 4 * j) by (unfold j; pose proof (Z.div_mod (u (edenot E K)) 4 ltac:(lia)); lia).
      pose proof (idx_rng data idxs HS1 j ltac:(pose proof (u_rng (edenot E K)); unfold j; split; [apply Z.div_pos; lia | lia])) as Ij.
      assert (R1 : 1 <= u (edenot E L) - u (edenot E VX) <= MF) by (apply (kimp_sub segs E m kn _ _ _ _ HKn C); lia).
      assert (EMUL : forall k, 0 <= k <= 8 -> u (edenot E (emul k NN)) = k * n).
      { intros k Hk. rewrite u_emul', HN. rewrite (Z.mod_small k) by lia. apply Z.mod_small. nia. }
      assert (R2 : 0 <= 4 * n + 4 - u (edenot E K) <= KOMAX MF).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R. rewrite u_esub2, u_eaddl, EMUL in R by lia.
        rewrite (Z.mod_small 4) in R by lia. rewrite (Z.mod_small (4 * n + 4)) in R by (unfold KOMAX in *; lia).
        apply sub_exact; unfold KOMAX in *; lia. }
      pose proof (idx_real data idxs HS1 j ltac:(unfold KOMAX in *; lia) ltac:(lia)).
      constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2, EMUL, u_eaddl by lia. rewrite (Z.mod_small 4) by lia.
      unfold KOMAX in *. rewrite (Z.mod_small (_ + 4)) by lia. rewrite Z.mod_small by lia. lia.
    Qed.

    Lemma r5_sound : forall kn args, know_ok segs E m kn -> tok_holds args ->
      forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (r5_tok segs MF kn NN args).
    Proof.
      intros kn args HKn Ht M. unfold r5_tok. destruct args as [|K [|VX [|? ?]]]; try constructor.
      match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H3 : kimp _ _ (KRange K _ _) = true, H4 : kimp _ _ (KRange NN _ _) = true |- _ =>
        rename H3 into C3; rename H4 into C4 end.
      destruct gidx_ctx as (HN & HS1 & HXb & HXm).
      unfold tok_holds in Ht. cbn [map gp2] in Ht. destruct Ht as (Hk4 & Hkj & Hv).
      pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3. pose proof (kimp_range segs E m kn _ _ _ HKn C4) as R4.
      set (j := u (edenot E K) / 4) in *.
      assert (Hko : u (edenot E K) = 4 * j) by (unfold j; pose proof (Z.div_mod (u (edenot E K)) 4 ltac:(lia)); lia).
      assert (EMUL : forall k, 0 <= k <= 8 -> u (edenot E (emul k NN)) = k * n).
      { intros k Hk. rewrite u_emul', HN. rewrite (Z.mod_small k) by lia. apply Z.mod_small. nia. }
      assert (R1 : 0 <= 4 * n - (u (edenot E K) + 4) <= KOMAX MF).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C) as R. rewrite u_esub2, u_eaddl, EMUL in R by lia.
        rewrite (Z.mod_small 4) in R by lia. rewrite (Z.mod_small (_ + 4)) in R by (unfold KOMAX in *; lia).
        apply sub_exact; unfold KOMAX in *; lia. }
      assert (Hj0 : 0 <= j) by (unfold j; apply Z.div_pos; [pose proof (u_rng (edenot E K)); lia | lia]).
      pose proof (idx_mono data idxs HS1 j Hj0 ltac:(lia)). pose proof (idx_rng data idxs HS1 (j + 1) ltac:(lia)).
      constructor; [|constructor]. cbn [ST.g_id ST.g_args map gp2].
      rewrite !u_eaddl. rewrite (Z.mod_small 4), (Z.mod_small 1) by lia. unfold KOMAX in *.
      rewrite (Z.mod_small (_ + 4)) by lia.
      assert (HV : u (edenot E VX) = znth idxs j) by exact Hv. rewrite HV.
      pose proof (idx_rng data idxs HS1 j ltac:(lia)). destruct gbuf_ctx as (HLen & _ & _ & _). pose proof (u_rng (edenot E L)).
      rewrite (Z.mod_small (_ + 1)) by lia.
      replace ((u (edenot E K) + 4) / 4) with (j + 1) by (rewrite Hko; replace (4 * j + 4) with ((j + 1) * 4) by lia; rewrite Z.div_mul; lia).
      split; [rewrite Hko; replace (4 * j + 4) with ((j + 1) * 4) by lia; apply Z.mod_mul; lia|]. split; lia.
    Qed.

    Lemma link_sound : forall kn L0 ges gsbs args, know_ok segs E m kn -> tok_holds args -> Forall ge_holds ges ->
      Forall (fun a => GP 7 (map (edenot E) a) m) gsbs -> know_ok segs E m (link_tok segs MF kn L0 ges gsbs args).
    Proof.
      intros kn L0 ges gsbs args HKn Ht Hges Hgsb. unfold link_tok. destruct args as [|K [|VX [|? ?]]]; try constructor.
      destruct (kimp segs kn (KRange VX 0 MF)) eqn:C0; [|constructor].
      pose proof (kimp_range segs E m kn _ _ _ HKn C0) as R0.
      unfold tok_holds in Ht. cbn [map gp2] in Ht. destruct Ht as (Hk4 & Hkj & Hv).
      apply Forall_app. split.
      - unfold know_ok. apply Forall_forall. intros F HF. apply in_flat_map in HF as (a & Ha & HF).
        destruct a as [|K' [|E' [|? ?]]]; try (cbn in HF; contradiction).
        destruct (leq K' K && kimp segs kn (KRange E' 0 (BIGS)))%bool eqn:C; [|cbn in HF; contradiction].
        apply andb_prop in C as [C1 C2]. destruct HF as [<-|[]].
        pose proof (proj1 (Forall_forall _ _) Hges _ Ha) as G. unfold ge_holds in G. cbn [map gp2] in G.
        rewrite (leq_den E K' K C1) in G. destruct G as (_ & _ & G). pose proof (kimp_range segs E m kn _ _ _ HKn C2).
        cbn [kentry_ok]. rewrite u_esub2. rewrite Z.mod_small; lia.
      - unfold know_ok. apply Forall_forall. intros F HF. apply in_flat_map in HF as (a & Ha & HF).
        destruct a as [|K' [|OL [|C' [|? ?]]]]; try (cbn in HF; contradiction); [| destruct C'; cbn in HF; contradiction].
        destruct C' as [cc| | | | | | |]; try (cbn in HF; contradiction).
        destruct (leq K' K && Z.leb 0 cc && Z.leb cc 16 && kimp segs kn (KRange OL 0 BIGS))%bool eqn:C; [|cbn in HF; contradiction].
        repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
        match goal with H1 : Z.leb 0 cc = true, H2 : Z.leb cc 16 = true, H3 : kimp _ _ (KRange OL _ _) = true |- _ =>
          apply Z.leb_le in H1; apply Z.leb_le in H2; pose proof (kimp_range segs E m kn _ _ _ HKn H3) as ROL end.
        pose proof (proj1 (Forall_forall _ _) Hgsb _ Ha) as G. cbn [map gp2] in G.
        rewrite (leq_den E K' K C) in G. destruct G as (_ & _ & G). rewrite edenot_lit, u_lit in G by lia.
        assert (HV : u (edenot E VX) = znth idxs (u (edenot E K) / 4)) by exact Hv. rewrite <- HV in G. unfold BIGS in ROL.
        destruct HF as [<-|HF].
        + cbn [kentry_ok]. rewrite u_esub2, !u_emul'. rewrite (Z.mod_small 5), (Z.mod_small 3) by lia.
          rewrite (Z.mod_small (5 * _)) by lia. rewrite (Z.mod_small (3 * _)) by lia. rewrite Z.mod_small by lia. lia.
        + destruct OL as [ol| | | | | | |]; try (cbn in HF; contradiction).
          destruct (Z.leb 0 ol && Z.leb ol MF)%bool eqn:Co; [|cbn in HF; contradiction]. destruct HF as [<-|[]].
          apply andb_prop in Co as [Co1 Co2]. apply Z.leb_le in Co1. apply Z.leb_le in Co2.
          rewrite edenot_lit, u_lit in G by lia. cbn [kentry_ok]. split; [|lia].
          assert ((3 * ol + cc + 4) / 5 < u (edenot E VX) + 1) by (apply Z.div_lt_upper_bound; lia). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn1_val : forall M a b0, rdn segs M a 1 = Some [b0] -> mbyte segs M (u a) = u b0.
    Proof. intros M a b0 H. unfold mbyte. rewrite Z_to_bv_bv_unsigned, H. reflexivity. Qed.

    Lemma byte34_sound : forall kn B0 X0, know_ok segs E m kn -> byte34 segs kn (SG.vc_path c) B0 X0 = true ->
      u (edenot E B0) + u (edenot E X0) < 2 ^ 64 -> mbyte segs m (u (edenot E B0) + u (edenot E X0)) = 34.
    Proof.
      intros kn B0 X0 HKn H Hr. unfold byte34 in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a b]|] eqn:Hrr; [|discriminate]. apply andb_prop in H as [H1 H2].
      pose proof (leq_den E _ _ H1) as HX0.
      destruct (rrec_den segs m E _ 1 sc a b HP Hin Hrr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E B0) + u (edenot E X0)).
      { rewrite (rel_addr E a B0) by (rewrite HX0; lia). rewrite HX0. reflexivity. }
      pose proof (rdn_length segs m 1 (adenot E a) bs Hrd) as HLn.
      destruct bs as [|b0 [|b1 r]]; cbn in HLn; try discriminate.
      cbn [bytes_le_to_Z] in Hv. rewrite Z.shiftl_0_l, Z.lor_0_r in Hv.
      pose proof (bv_unsigned_in_range _ b0) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      assert (Vb : u (ev E b) = u b0) by (rewrite <- Hv; apply u_lit; lia).
      assert (B34 : u b0 = 34).
      { apply orb_prop in H2 as [H2|H2]; pose proof (kimp_range segs E m kn _ _ _ HKn H2) as R.
        - rewrite u_x1 in R by lia. lia.
        - cbn [edenot] in R. lia. }
      rewrite <- Haddr. rewrite (rdn1_val m (adenot E a) b0 Hrd). exact B34.
    Qed.

    Lemma rdn1_some : forall M a b0, M a = Some b0 -> rdn segs M a 1 = Some [b0].
    Proof. intros M a b0 H. cbn [rdn]. rewrite H. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma mdata_data : forall M B0, Forall (fun c => 0 <= c < 256) data -> u (edenot E B0) + len < 2 ^ 64 ->
      (forall i, 0 <= i < len -> M (Z_to_bv 64 (u (edenot E B0) + i)) = Some (Z_to_bv 8 (byte_at data i))) ->
      mdata segs M (u (edenot E B0)) len = data.
    Proof.
      intros M B0 HF Hb HM. pose proof (mdata_length segs M (u (edenot E B0)) len ltac:(unfold zlength; lia)) as HL.
      apply nth_ext with (d := 0) (d' := 0); [unfold zlength in HL |- *; lia|].
      intros i Hi. assert (Hi' : 0 <= Z.of_nat i < len) by (unfold zlength in *; lia).
      pose proof (mdata_byte segs M (u (edenot E B0)) len (Z.of_nat i) Hi') as Hby. unfold byte_at in Hby. rewrite Nat2Z.id in Hby.
      rewrite Hby. unfold mbyte. rewrite (rdn1_some M _ _ (HM (Z.of_nat i) Hi')).
      pose proof (byte_at_rng data (Z.of_nat i) HF) as R. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold byte_at. rewrite Nat2Z.id. reflexivity.
    Qed.

    Lemma koff_den : forall P' P k, koff P' P = Some k -> exists q, u (edenot E P') = u (edenot E P) + k + q * 2 ^ 64.
    Proof.
      intros P' P k H. unfold koff in H. destruct (lin_of (nsub P' P)) as [k' [|t ts]] eqn:Hl; [|discriminate]. injection H as <-.
      pose proof (lin_of_sound E (nsub P' P)) as [q Hq]. rewrite Hl in Hq. unfold lden, uE in Hq. cbn [fst snd tden] in Hq.
      rewrite nsub_den in Hq. rewrite alu_sub in Hq. unfold v_sub in Hq. rewrite u_litm in Hq.
      pose proof (Z.div_mod (u (edenot E P') - u (edenot E P)) (2 ^ 64) ltac:(lia)) as Dm.
      exists ((u (edenot E P') - u (edenot E P)) / 2 ^ 64 - q). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sexit_sound : forall kn args, know_ok segs E m kn -> GP 0 (map (edenot E) args) m ->
      know_ok segs E m (fst (sexit segs MF kn (SG.vc_path c) args)) /\
      forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd (sexit segs MF kn (SG.vc_path c) args)).
    Proof.
      intros kn args HKn HG. unfold sexit.
      destruct args as [|B0 [|L0 [|P0 [|KO0 [|? ?]]]]]; try (split; [constructor| intros; constructor]).
      destruct (byte34 segs kn (SG.vc_path c) B0 P0 && kimp segs kn (KRange L0 0 MF))%bool eqn:C;
        [|split; [constructor| intros; constructor]].
      apply andb_prop in C as [C1 C2]. pose proof (kimp_range segs E m kn _ _ _ HKn C2) as RL.
      destruct gidx_ctx as (HN & HS1 & HXb & HXm).
      cbn [map gp2] in HG. destruct HG as (HBL & HK4 & HKj & q & Hq & Hp & Hqi).
      pose proof (bpath_bound _ _ _ _ Hp) as [Hpq Hq34].
      pose proof (u_rng (edenot E P0)). pose proof (u_rng (edenot E B0)). pose proof (u_rng (edenot E KO0)). pose proof (u_rng (edenot E X)).
      pose proof (byte34_sound kn B0 P0 HKn C1 ltac:(lia)) as H34.
      assert (Hb : byte_at (mdata segs m (u (edenot E B0)) (u (edenot E L0))) (u (edenot E P0)) = 34)
        by (rewrite mdata_byte by lia; exact H34).
      pose proof (bpath_quote_here _ _ _ _ Hp Hb) as EQ. subst q.
      split.
      - constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2. rewrite Z.mod_small by lia. lia.
      - intros M. constructor; [|constructor]. cbn [ST.g_id ST.g_args map gp2].
        set (j := u (edenot E KO0) / 4) in *.
        assert (Hko : u (edenot E KO0) = 4 * j) by (unfold j; pose proof (Z.div_mod (u (edenot E KO0)) 4 ltac:(lia)); lia).
        assert (U4 : u (edenot E (eaddl KO0 4)) = 4 * j + 4).
        { rewrite u_eaddl, (Z.mod_small 4) by lia. rewrite Hko. apply Z.mod_small. lia. }
        assert (U1 : u (edenot E (eaddl P0 1)) = u (edenot E P0) + 1).
        { rewrite u_eaddl, (Z.mod_small 1) by lia. apply Z.mod_small. lia. }
        rewrite U4, U1. replace ((4 * j + 4) / 4) with (j + 1) by (replace (4 * j + 4) with ((j + 1) * 4) by lia; rewrite Z.div_mul; lia).
        split; [replace (4 * j + 4) with ((j + 1) * 4) by lia; apply Z.mod_mul; lia|]. split; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma str_tgt_sound : forall kn toks g, know_ok segs E m kn -> log_flat E (SG.vc_log c) ->
      (forall a, In a toks -> tok_holds a) ->
      str_tgt_ok segs MF TD kn (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) toks g = true ->
      GP (ST.g_id g) (map (edenot E) (ST.g_args g)) (mem_denot E m (SG.vc_log c)) /\
      forall B' L' P' KO', ST.g_args g = [B'; L'; P'; KO'] -> 1 <= u (edenot E L') - u (edenot E P') <= MF.
    Proof.
      intros kn toks [gid gargs] HKn HL HT H. unfold str_tgt_ok in H. cbn [ST.g_id ST.g_args] in *. rewrite HX, HB in H.
      destruct gid as [|gid]; [|discriminate].
      destruct gargs as [|B' [|L' [|P' [|KO' [|? ?]]]]]; try discriminate.
      destruct gidx_ctx as (HN & HS1 & HXb & HXm). destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      assert (FIN : forall b1 l1, leq b1 B' = true -> leq l1 L' = true -> u (edenot E b1) + u (edenot E l1) + 64 < 2 ^ 64 ->
                    SG.log_apart kn (SG.vc_log c) [(B', 0, L')] = true ->
                    mdata segs (mem_denot E m (SG.vc_log c)) (u (edenot E B')) (u (edenot E L')) =
                    mdata segs m (u (edenot E b1)) (u (edenot E l1))).
      { intros b1 l1 E1 E2 Hr Hap. rewrite <- (leq_den E _ _ E1), <- (leq_den E _ _ E2).
        pose proof (u_rng (edenot E b1)). pose proof (u_rng (edenot E l1)).
        apply mdata_ext; [lia | lia | lia |]. intros x Hx. eapply mem_denot_apart_gen; [exact HKn | exact HL | exact Hap |].
        exists (B', 0, L'). split; [left; reflexivity|]. cbn [SG.win_den]. rewrite <- (leq_den E _ _ E1), <- (leq_den E _ _ E2). lia. }
      apply orb_prop in H as [H|H].
      - (* [comment removed for export] *)
        unfold sstart_ok in H.
        repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H1 : leq L L' = true, H2 : kimp _ _ (KRange L _ _) = true, H3 : kimp _ _ (KRange NN _ _) = true,
          H4 : kimp _ _ (KRange KO' _ _) = true, H5 : kimp _ _ (KRange (esub2 _ _) _ _) = true, H6 : SG.log_apart _ _ _ = true,
          H7 : existsb _ toks = true |- _ =>
          rename H1 into C1; rename H2 into C2; rename H3 into C3; rename H4 into C4; rename H5 into C5; rename H6 into C6;
          rename H7 into C7 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn C2) as RL. pose proof (kimp_range segs E m kn _ _ _ HKn C3) as RN.
        pose proof (kimp_range segs E m kn _ _ _ HKn C4) as RK.
        apply existsb_exists in C7 as (args & Ha & C7). destruct args as [|K [|V [|? ?]]]; try discriminate.
        repeat match type of C7 with (_ && _)%bool = true => apply andb_prop in C7; destruct C7 as [C7 ?] end.
        match goal with H1 : leq P' _ = true, H2 : byte34 _ _ _ _ _ = true |- _ => rename H1 into C8; rename H2 into C9 end.
        pose proof (HT _ Ha) as Tk. unfold tok_holds in Tk. cbn [map gp2] in Tk. destruct Tk as (Tk4 & Tkj & Tv).
        rewrite (leq_den E K KO' C7) in Tk4, Tkj, Tv.
        set (j := u (edenot E KO') / 4) in *.
        assert (Hko : u (edenot E KO') = 4 * j) by (unfold j; pose proof (Z.div_mod (u (edenot E KO')) 4 ltac:(lia)); lia).
        assert (EMUL : u (edenot E (emul 4 NN)) = 4 * n).
        { rewrite u_emul', HN. rewrite (Z.mod_small 4) by lia. apply Z.mod_small. lia. }
        assert (R5 : 0 <= 4 * n - (u (edenot E KO') + 4) <= KOMAX MF).
        { pose proof (kimp_range segs E m kn _ _ _ HKn C5) as R. rewrite u_esub2, u_eaddl, EMUL in R.
          rewrite (Z.mod_small 4) in R by lia. unfold KOMAX in *. rewrite (Z.mod_small (_ + 4)) in R by lia.
          apply sub_exact; try lia. }
        destruct HS1 as [Hn1 Hl1 Hlt1 Hinc1 Hsent1 Hstr1].
        pose proof (Hlt1 j ltac:(lia)) as Ij.
        pose proof (u_rng (edenot E B)). pose proof (u_rng (edenot E V)).
        pose proof (byte34_sound kn B V HKn C9 ltac:(lia)) as H34.
        assert (Hd34 : byte_at data (znth idxs j) = 34).
        { rewrite <- H34, Tv. unfold mbyte. rewrite <- Tv.
          rewrite (mbytes_rdn segs m _ _ (u (edenot E V)) 1 HBm) by (rewrite ?bufbytes_length; lia).
          destruct (skipn (Z.to_nat (u (edenot E V))) (bufbytes data)) as [|b0 r0] eqn:Hsk.
          - exfalso. pose proof (f_equal (@length byte) Hsk) as LL. rewrite length_skipn in LL. cbn in LL.
            pose proof (bufbytes_length data). lia.
          - cbn [firstn]. assert (Hn0 : nth (Z.to_nat (u (edenot E V))) (bufbytes data) (Z_to_bv 8 0) = b0).
            { rewrite <- (firstn_skipn (Z.to_nat (u (edenot E V))) (bufbytes data)), app_nth2; rewrite length_firstn; [|pose proof (bufbytes_length data); lia].
              replace (Z.to_nat (u (edenot E V)) - Nat.min (Z.to_nat (u (edenot E V))) (length (bufbytes data)))%nat with 0%nat
                by (pose proof (bufbytes_length data); lia). rewrite Hsk. reflexivity. }
            rewrite <- Hn0. rewrite bufbytes_nth by (try exact HBd; lia). rewrite Tv.
            pose proof (byte_at_rng data (znth idxs j) HBd). rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
            change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
        destruct (Hstr1 j ltac:(lia) Hd34) as (q & Hq & Hqi).
        pose proof (bpath_bound _ _ _ _ Hq) as [Hpq Hq34].
        assert (UP : u (edenot E P') = znth idxs j + 1).
        { rewrite (leq_den E _ _ C8), u_eaddl, Tv. rewrite (Z.mod_small 1) by lia. apply Z.mod_small. lia. }
        assert (MD : mdata segs (mem_denot E m (SG.vc_log c)) (u (edenot E B')) (u (edenot E L')) = data).
        { rewrite (FIN B L) by (first [assumption | lia]). rewrite HLen. apply mdata_data; [exact HBd | lia |].
          intros i Hi. rewrite (HBm i) by (rewrite bufbytes_length; lia). rewrite bufbytes_nth by (try exact HBd; lia). reflexivity. }
        assert (UL : u (edenot E L') = len) by (rewrite <- (leq_den E _ _ C1); exact HLen).
        split.
        + cbn [map gp2]. rewrite MD, UL, UP. rewrite <- (leq_den E _ _ H).
          split; [lia|]. split; [exact Tk4|]. split; [unfold j in *; lia|]. exists q. split; [lia|]. split; [exact Hq|]. exact Hqi.
        + intros B'' L'' P'' KO'' Heq. injection Heq as <- <- <- <-. rewrite UL, UP. unfold zlength in *. lia.
      - (* [comment removed for export] *)
        unfold sarm_ok in H. apply existsb_exists in H as (args & Ha & H).
        destruct args as [|B0 [|L0 [|P0 [|KO0 [|? ?]]]]]; try discriminate.
        destruct (koff P' P0) as [k|] eqn:Hk; [|discriminate].
        repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H1 : leq L0 L' = true, H2 : leq KO0 KO' = true, H3 : Z.leb 1 k = true, H4 : Z.leb k 12 = true,
          H5 : kimp _ _ (KRange L0 _ _) = true, H6 : has_kimg _ _ _ = true, H7 : arm_ok _ _ _ _ _ = true,
          H8 : SG.log_apart _ _ _ = true |- _ =>
          rename H1 into C1; rename H2 into C2; apply Z.leb_le in H3; apply Z.leb_le in H4; rename H5 into C5; rename H6 into C6;
          rename H7 into C7; rename H8 into C8 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn C5) as RL.
        pose proof (src_holds 0 _ (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (GB & GK4 & GKj & q & Hq & Hp & Hqi).
        pose proof (has_kimg_ok segs TD TD_rng E m kn TD (TD + 3544) HKn C6) as HU.
        pose proof (arm_sound segs TD TD_rng D2V_IMG m E (SG.vc_path c) HP HU B0 P0 (u (edenot E L0)) q GB Hp k C7) as Hp'.
        pose proof (bpath_bound _ _ _ _ Hp') as [Hpq _].
        destruct (koff_den P' P0 k Hk) as [z Hz]. pose proof (u_rng (edenot E P')). pose proof (u_rng (edenot E P0)).
        assert (UP : u (edenot E P') = u (edenot E P0) + k) by (assert (z = 0) by nia; subst z; lia).
        assert (MD : mdata segs (mem_denot E m (SG.vc_log c)) (u (edenot E B')) (u (edenot E L')) =
                     mdata segs m (u (edenot E B0)) (u (edenot E L0))) by (apply FIN; first [assumption | lia]).
        split.
        + cbn [map gp2]. rewrite MD, UP. rewrite <- (leq_den E _ _ H), <- (leq_den E _ _ C1), <- (leq_den E _ _ C2).
          split; [exact GB|]. split; [exact GK4|]. split; [exact GKj|]. exists q. split; [exact Hq|]. split; [exact Hp'|]. exact Hqi.
        + intros B'' L'' P'' KO'' Heq. injection Heq as <- <- <- <-. rewrite UP. rewrite <- (leq_den E _ _ C1). lia.
    Qed.
    Lemma swar_sound : forall sc, In sc (SG.vc_path c) -> know_ok segs E m (swar_facts sc).
    Proof.
      intros sc Hin. unfold swar_facts.
      destruct sc as [t cc T k'| | | | | | ]; try constructor. destruct k' as [k| | | | | | |]; try constructor.
      match goal with |- know_ok _ _ _ (if ?b then _ else _) => destruct b eqn:C; [|constructor] end.
      apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1. subst k.
      destruct (swar_v T) as [v|] eqn:Hs; [|constructor]. destruct (top_lane v) as [b7|] eqn:Ht; [|constructor].
      constructor; [|constructor]. cbn [kentry_ok].
      (* [comment removed for export] *)
      pose proof (proj1 (Forall_forall _ _) HP _ Hin) as Hb. cbn [sc_denot] in Hb.
      assert (HT : u (edenot E T) = C33).
      { rewrite edenot_lit in Hb. destruct t, cc; try discriminate; cbn [branch_taken] in Hb; unfold bv_eqb in Hb.
        - apply Z.eqb_eq in Hb. rewrite Hb. apply u_lit. unfold C33. lia.
        - apply negb_false_iff in Hb. apply Z.eqb_eq in Hb. rewrite Hb. apply u_lit. unfold C33. lia. }
      (* [comment removed for export] *)
      unfold swar_v in Hs.
      destruct T as [| |o1 T1 T2| | | | |]; try discriminate. destruct o1; try discriminate.
      destruct T1 as [| |o2 T3 c2e| | | | |]; try discriminate. destruct o2; try discriminate.
      destruct T3 as [| |o3 T4 c4e| | | | |]; try discriminate. destruct o3; try discriminate.
      destruct T4 as [| |o4 v1 c1e| | | | |]; try discriminate. destruct o4; try discriminate.
      destruct c1e as [c1| | | | | | |]; try discriminate. destruct c4e as [c4| | | | | | |]; try discriminate.
      destruct c2e as [c2| | | | | | |]; try discriminate.
      destruct T2 as [| |o5 v2 c3e| | | | |]; try discriminate. destruct o5; try discriminate.
      destruct c3e as [c3| | | | | | |]; try discriminate.
      match type of Hs with (if ?b then _ else _) = _ => destruct b eqn:C; [|discriminate] end.
      injection Hs as <-.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H : expr_eqb v1 v2 = true |- _ => apply expr_eqb_eq in H; subst v2 end.
      match goal with H : Z.eqb c3 CF0 = true |- _ => apply Z.eqb_eq in H; subst c3 end.
      match goal with H : Z.eqb c2 C0F = true |- _ => apply Z.eqb_eq in H; subst c2 end.
      assert (HBm : Z.land (u (edenot E v1)) CF0 = Z.land C33 CF0).
      { rewrite <- HT. cbn [edenot]. rewrite !alu_or_u, !alu_and_u. rewrite !u_lit by (unfold C0F, CF0; lia).
        symmetry. apply land_cf0. }
      change (Z.land C33 CF0) with 3472328296227680304 in HBm.
      (* [comment removed for export] *)
      unfold top_lane in Ht.
      destruct (lin_of v1) as [c0 ts] eqn:Hl. cbn [fst snd] in Ht.
      destruct (List.filter (fun t0 => Z.eqb (fst t0) (2 ^ 56)) ts) as [|[k7 e7] tl] eqn:Hf; [discriminate|].
      destruct e7 as [| | | | | |sx lo n a'| ]; try discriminate. destruct sx; try discriminate.
      destruct lo; try discriminate. destruct n as [|[|n]]; try discriminate. destruct a' as [|w| | | | | |]; try discriminate.
      destruct tl as [|? ?]; [|discriminate].
      match type of Ht with (if ?b then _ else _) = _ => destruct b eqn:C'; [|discriminate] end.
      injection Ht as <-.
      repeat match type of C' with (_ && _)%bool = true => apply andb_prop in C'; destruct C' as [C' ?] end.
      apply Z.eqb_eq in C'. subst c0.
      match goal with H1 : Nat.leb _ 7 = true, H2 : forallb is_lane _ = true |- _ =>
        apply Nat.leb_le in H1; pose proof (tden_lanes E _ H2) as TL end.
      assert (K7 : k7 = 2 ^ 56).
      { assert (HIn : In (k7, EExt false 0 1 (EVar w)) (List.filter (fun t0 => Z.eqb (fst t0) (2 ^ 56)) ts)) by (rewrite Hf; left; reflexivity).
        apply filter_In in HIn as [_ HIn]. cbn [fst] in HIn. apply Z.eqb_eq in HIn. exact HIn. }
      subst k7.
      pose proof (lin_of_sound E v1) as LS. rewrite Hl in LS. unfold lden in LS. cbn [fst snd] in LS.
      rewrite (tden_filter E (fun t0 => Z.eqb (fst t0) (2 ^ 56)) ts), Hf in LS. cbn [tden] in LS.
      set (x7 := uE E (EExt false 0 1 (EVar w))) in *.
      assert (R7 : 0 <= x7 <= 255).
      { unfold x7, uE. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
        change (2 ^ (8 * 1)) with 256. pose proof (Z.mod_pos_bound (bv_unsigned (ev E w)) 256 ltac:(lia)).
        rewrite u_lit by lia. lia. }
      set (rest := tden E (List.filter (fun t0 => negb (Z.eqb (fst t0) (2 ^ 56))) ts)) in *.
      assert (Hrest : 0 <= rest <= 7 * (255 * 2 ^ 48)).
      { unfold rest. match goal with H1 : (length _ <= 7)%nat |- _ => clear - TL H1 end. nia. }
      destruct LS as [q Hq]. unfold uE in Hq. pose proof (u_rng (edenot E v1)) as RV1.
      change (bv_unsigned (edenot E (x1 w))) with x7. split; [|lia].
      destruct (Z_lt_ge_dec x7 42) as [SM|BG]; [|lia].
      exfalso. clearbody x7 rest.
      assert (q = 0) by (clear - Hq Hrest RV1 R7 SM; lia). subst q.
      assert (Xl : u (edenot E v1) < 3 * 2 ^ 60) by (clear - Hq Hrest RV1 R7 SM; lia).
      set (vv := u (edenot E v1)) in *.
      assert (D3 : 0 <= vv / 2 ^ 60 <= 2) by (split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]).
      assert (SH : Z.shiftr (Z.land vv CF0) 60 = Z.land (vv / 2 ^ 60) 15).
      { rewrite Z.shiftr_land, Z.shiftr_div_pow2 by lia. f_equal. }
      assert (LQ : Z.land (vv / 2 ^ 60) 15 <= 2).
      { destruct (Z.eq_dec (vv / 2 ^ 60) 0) as [->|N0]; [cbv; discriminate|].
        destruct (Z.eq_dec (vv / 2 ^ 60) 1) as [->|N1]; [cbv; discriminate|].
        replace (vv / 2 ^ 60) with 2 by lia. cbv; discriminate. }
      rewrite HBm in SH. rewrite Z.shiftr_div_pow2 in SH by lia. change (3472328296227680304 / 2 ^ 60) with 3 in SH. lia.
    Qed.

    Lemma u_x1' : forall v, u (edenot E (x1 v)) = u (ev E v) mod 256.
    Proof.
      intros v. unfold x1. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
      change (2 ^ (8 * 1)) with 256. pose proof (Z.mod_pos_bound (u (ev E v)) 256 ltac:(lia)). apply u_lit. lia.
    Qed.

    Lemma byte_facts_sound : forall kn sc, know_ok segs E m kn -> know_ok segs E m (byte_facts segs kn sc).
    Proof.
      intros kn sc HKn. unfold byte_facts. destruct (rrec 1 sc) as [[a b]|]; [|constructor].
      pose proof (u_x1' b) as Ub. pose proof (Z.mod_pos_bound (u (ev E b)) 256 ltac:(lia)) as Rb.
      apply Forall_app. split.
      - destruct (kimp segs kn (KRange (dig_expr b) 0 9)) eqn:C; [|constructor]. constructor; [|constructor].
        pose proof (kimp_range segs E m kn _ _ _ HKn C) as R. unfold dig_expr in R. cbn [edenot] in R.
        rewrite alu_and_u, u_lit in R by lia. change (edenot E (EAlu ALU_ADD (x1 b) (ELit (-48)))) with (alu64 ALU_ADD (edenot E (x1 b)) (Z_to_bv 64 (-48))) in R.
        rewrite alu_add in R. unfold v_add in R. rewrite u_litm, (u_litm (-48)) in R.
        change 255 with (Z.ones 8) in R. rewrite Z.land_ones in R by lia. change (2 ^ 8) with 256 in R.
        rewrite <- Znumtheory.Zmod_div_mod in R by (try lia; exists (2 ^ 56); reflexivity).
        rewrite Zplus_mod, Ub in R. change (-48 mod 2 ^ 64 mod 256) with 208 in R.
        rewrite Z.mod_mod in R by lia.
        cbn [kentry_ok]. rewrite Ub. set (x := u (ev E b) mod 256) in *.
        assert (Hx : 0 <= x < 256) by (unfold x; lia). clearbody x.
        destruct (Z_lt_ge_dec (x + 208) 256) as [Lt|Ge].
        + rewrite Z.mod_small in R by lia. lia.
        + replace ((x + 208) mod 256) with (x - 48) in R; [lia|].
          rewrite <- (Z.mod_small (x - 48) 256) by lia. replace (x + 208) with (x - 48 + 1 * 256) by lia. rewrite Z.mod_add; lia.
      - apply Forall_flat_map'. intros K HKin. cbv beta. destruct K as [| | | | |e lo hi| | | |]; try constructor.
        match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
        apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C2. apply Z.leb_le in C3.
        apply expr_eqb_eq in C1. subst e. constructor; [|constructor].
        pose proof (proj1 (Forall_forall _ _) HKn _ HKin) as R. cbn [kentry_ok] in R |- *. unfold msk_expr in R. cbn [edenot] in R.
        rewrite alu_and_u, u_lit in R by lia. change 255 with (Z.ones 8) in R. rewrite Z.land_ones in R by lia.
        change (2 ^ 8) with 256 in R. rewrite Ub in R. rewrite Ub. rewrite Z.mod_mod in R by lia. exact R.
    Qed.

    (* [comment removed for export] *)
    Lemma fill_sound : forall kn sc, know_ok segs E m kn -> In sc (SG.vc_path c) -> know_ok segs E m (fill_facts segs kn sc).
    Proof.
      intros kn sc HKn Hin. unfold fill_facts. destruct (rrec 1 sc) as [[a b]|] eqn:Hr; [|constructor].
      apply Forall_flat_map'. intros K HKin. destruct (fill_of K) as [[[FS n] cb]|] eqn:Hf; [|constructor].
      match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H1 : kimp _ _ (KRange (eaddl (a_base a) (a_off a)) _ _) = true, H2 : kimp _ _ (KRange FS _ _) = true,
        H3 : kimp _ _ (KRange (esub2 _ _) _ _) = true |- _ =>
        pose proof (kimp_range segs E m kn _ _ _ HKn H1) as RA; pose proof (kimp_range segs E m kn _ _ _ HKn H2) as RF;
        rename H3 into C3 end.
      set (A' := eaddl (a_base a) (a_off a)) in *.
      assert (UA : u (adenot E a) = u (edenot E A')).
      { unfold A'. rewrite u_eaddl. unfold adenot, v_addi. rewrite u_litm. rewrite Z.add_mod_idemp_r by lia. reflexivity. }
      (* [comment removed for export] *)
      assert (FILL : exists st, u (edenot E FS) = st /\ 1 <= n <= 4096 /\ 0 <= cb < 256 /\
                       forall i, 0 <= i < n -> m (Z_to_bv 64 (st + i)) = Some (Z_to_bv 8 cb)).
      { pose proof (proj1 (Forall_forall _ _) HKn _ HKin) as HK'.
        destruct K as [| [FB FO] nn | | | | | | | [FB FO] nn cc0 |]; cbn [fill_of] in Hf; try discriminate.
        - destruct nn as [n'| | | | | | |]; try discriminate.
          match type of Hf with (if ?b then _ else _) = _ => destruct b eqn:Cn; [|discriminate] end.
          injection Hf as <- <- <-. apply andb_prop in Cn as [Cn1 Cn2]. apply Z.leb_le in Cn1. apply Z.leb_le in Cn2.
          cbn [kentry_ok] in HK'. destruct HK' as [Hfl Hz]. unfold elenZ in Hz. rewrite edenot_lit, u_lit in Hz by lia.
          exists (estart E (SA FB FO)). split; [|split; [lia|split; [lia|]]].
          + rewrite u_eaddl. unfold estart. cbn [a_base a_off]. destruct Hfl as (F1 & F2 & _). pose proof (u_rng (edenot E FB)).
            rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. unfold estart in F1, F2. cbn [a_base a_off] in F1, F2. lia.
          + intros i Hi. exact (Hz i Hi).
        - destruct nn as [n'| | | | | | |]; try discriminate.
          match type of Hf with (if ?b then _ else _) = _ => destruct b eqn:Cn; [|discriminate] end.
          injection Hf as <- <- <-.
          repeat match type of Cn with (_ && _)%bool = true => apply andb_prop in Cn; destruct Cn as [Cn ?] end.
          repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
          cbn [kentry_ok] in HK'. destruct HK' as [Hfl Hz]. unfold elenZ in Hz. rewrite edenot_lit, u_lit in Hz by lia.
          exists (estart E (SA FB FO)). split; [|split; [lia|split; [lia|]]].
          + rewrite u_eaddl. unfold estart. cbn [a_base a_off]. destruct Hfl as (F1 & F2 & _). pose proof (u_rng (edenot E FB)).
            rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. unfold estart in F1, F2. cbn [a_base a_off] in F1, F2. lia.
          + intros i Hi. exact (Hz i Hi). }
      destruct FILL as (st & Hst & Hn & Hcb & Hz).
      assert (R3 : 1 <= u (edenot E FS) + n - u (edenot E A') <= 2 ^ 62).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R. rewrite u_esub2, u_eaddl in R.
        rewrite (Z.mod_small n) in R by lia. rewrite (Z.mod_small (_ + n)) in R by lia. apply sub_exact; lia. }
      destruct (rrec_den segs m E _ 1 sc a b HP Hin Hr) as (bs & Hrd & Hv).
      assert (LT : u (edenot E A') < u (edenot E FS)).
      { destruct (Z_lt_ge_dec (u (edenot E A')) (u (edenot E FS))) as [LT0|G]; [exact LT0|]. exfalso.
        set (i := u (edenot E A') - st).
        assert (Hm : m (adenot E a) = Some (Z_to_bv 8 cb)).
        { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)), UA. replace (u (edenot E A')) with (st + i) by (unfold i; lia).
          apply Hz. unfold i. lia. }
        cbn [rdn] in Hrd. rewrite Hm in Hrd. cbn [rdn] in Hrd. injection Hrd as <-. cbn [bytes_le_to_Z] in Hv.
        rewrite Z.shiftl_0_l, Z.lor_0_r in Hv. rewrite Z_to_bv_unsigned in Hv. unfold bv_wrap, bv_modulus in Hv.
        change (2 ^ Z.of_N 8) with 256 in Hv. rewrite Z.mod_small in Hv by lia.
        assert (Vb : u (ev E b) = cb) by (rewrite <- Hv; apply u_lit; lia).
        pose proof (u_x1' b) as Ub. rewrite Vb, Z.mod_small in Ub by lia.
        match goal with H : (kimp _ _ _ || kimp _ _ _)%bool = true |- _ => apply orb_prop in H as [H|H];
          pose proof (kimp_range segs E m kn _ _ _ HKn H) as R; lia end. }
      constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2. rewrite Z.mod_small by lia. lia.
    Qed.

    Lemma r1_ids : forall kn s g, In g (snd (r1_read segs MF kn X NN L s)) -> ST.g_id g = 3%nat.
    Proof.
      intros kn s g H. unfold r1_read in H. destruct (rrec 4 s) as [[a v]|]; [|contradiction].
      match type of H with In _ (snd (if ?cc then _ else _)) => destruct cc end; cbn in H; [|contradiction].
      destruct H as [<-|[]]. reflexivity.
    Qed.
    Lemma r5_ids : forall kn args g, In g (r5_tok segs MF kn NN args) -> ST.g_id g = 4%nat.
    Proof.
      intros kn args g H. unfold r5_tok in H. destruct args as [|K [|VX [|? ?]]]; try contradiction.
      match type of H with In _ (if ?cc then _ else _) => destruct cc end; [|contradiction]. destruct H as [<-|[]]. reflexivity.
    Qed.


    Lemma pure3 : forall args M M', GP 3 args M -> GP 3 args M'.
    Proof. intros args M M' H. destruct args as [|a [|b [|? ?]]]; exact H. Qed.
    Lemma pure4 : forall args M M', GP 4 args M -> GP 4 args M'.
    Proof. intros args M M' H. destruct args as [|a [|b [|? ?]]]; exact H. Qed.
    Lemma pure7 : forall args M M', GP 7 args M -> GP 7 args M'.
    Proof. intros args M M' H. destruct args as [|a [|b [|cc [|? ?]]]]; exact H. Qed.

    Lemma sexit_ids : forall kn args g, In g (snd (sexit segs MF kn (SG.vc_path c) args)) -> ST.g_id g = 4%nat.
    Proof.
      intros kn args g H. unfold sexit in H. destruct args as [|B0 [|L0 [|P0 [|KO0 [|? ?]]]]]; try (cbn in H; contradiction).
      match type of H with In _ (snd (if ?cc then _ else _)) => destruct cc end; cbn in H; [|contradiction].
      destruct H as [<-|[]]. reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma r14_sound : forall kn s, know_ok segs E m kn -> In s (SG.vc_path c) -> know_ok segs E m (r14_read segs kn (SG.vc_src c) s).
    Proof.
      intros kn s HKn Hin. unfold r14_read.
      destruct (rrec 1 s) as [[a v]|] eqn:Hr; [|constructor].
      unfold know_ok. apply Forall_forall. intros K HKin. apply in_flat_map in HKin as (args & Hargs & HKin).
      destruct args as [|IA [|D [|? ?]]]; try (cbn in HKin; contradiction).
      match type of HKin with In _ (if ?cc then _ else _) => destruct cc eqn:C; [|cbn in HKin; contradiction] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H2 : kimp _ _ (KRange (esub2 _ _) _ _) = true, H3 : kimp _ _ (KRange D _ _) = true,
        H4 : kimp _ _ (KRange IA _ _) = true |- _ =>
        pose proof (kimp_range segs E m kn _ _ _ HKn C) as R1; pose proof (kimp_range segs E m kn _ _ _ HKn H3) as R3;
        pose proof (kimp_range segs E m kn _ _ _ HKn H4) as R4; rename H2 into C2 end.
      set (I := u (edenot E (rel a IA))) in *.
      assert (R2 : 0 <= u (edenot E D) - I <= 1023).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R. rewrite u_esub2 in R. fold I in R. pose proof (u_rng (edenot E D)).
        apply sub_exact; lia. }
      pose proof (src_holds 6 [IA; D] (atoms_of_in _ _ _ Hargs)) as G. cbn [map gp2] in G. destruct G as (Gb & Gc).
      destruct (rrec_den segs m E _ 1 s a v HP Hin Hr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E IA) + I) by (rewrite (rel_addr E a IA) by (fold I; lia); fold I; lia).
      rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)) in Hrd. rewrite Haddr in Hrd.
      assert (V01 : u (ev E v) = 0 \/ u (ev E v) = 1).
      { destruct (Gc I ltac:(lia)) as [Hm|Hm]; rewrite (rdn1_some m _ _ Hm) in Hrd; injection Hrd as <-;
          cbn [bytes_le_to_Z] in Hv; rewrite Z.shiftl_0_l, Z.lor_0_r in Hv; rewrite <- Hv; [left | right]; reflexivity. }
      assert (X01 : u (edenot E (x1 v)) = u (ev E v)) by (rewrite u_x1 by lia; reflexivity).
      destruct HKin as [<-|[<-|[]]]; cbn [kentry_ok]; [rewrite X01|]; cbn [edenot]; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma gia_sound : forall kn lg g, know_ok segs E m kn -> log_flat E lg -> gia_ok segs kn lg (SG.vc_src c) g = true ->
      GP (ST.g_id g) (map (edenot E) (ST.g_args g)) (mem_denot E m lg).
    Proof.
      intros kn lg [gid gargs] HKn HL H. unfold gia_ok in H. cbn [ST.g_id ST.g_args] in *.
      destruct gid as [|[|[|[|[|[|[|gid]]]]]]]; try discriminate.
      destruct gargs as [|IA' [|D' [|? ?]]]; try discriminate.
      repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
      rename H into C1. match goal with H2 : kimp _ _ (KRange IA' _ _) = true, H4 : (_ || _)%bool = true |- _ =>
        rename H2 into C2; rename H4 into C4 end.
      pose proof (kimp_range segs E m kn _ _ _ HKn C1) as R1. pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R2.
      cbn [map gp2]. split; [lia|].
      apply orb_prop in C4 as [C4|C4].
      - (* [comment removed for export] *)
        rewrite (leq_den E D' (ELit 0) C4), edenot_lit, u_lit by lia. intros i Hi. lia.
      - apply existsb_exists in C4 as (args & Ha & C4).
        destruct args as [|IA [|D [|? ?]]]; try discriminate.
        repeat match type of C4 with (_ && _)%bool = true => apply andb_prop in C4; destruct C4 as [C4 ?] end.
        match goal with H2 : kimp _ _ (KRange D _ _) = true, H5 : (_ || _)%bool = true |- _ =>
          rename H2 into C6; rename H5 into C9 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn C6) as R6.
        pose proof (src_holds 6 [IA; D] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (Gb & Gc).
        rewrite (leq_den E IA IA' C4) in Gb, Gc.
        assert (OLD : forall dd, 0 <= u (edenot E dd) <= 1023 -> SG.log_apart kn lg [(IA', 1, dd)] = true ->
                      forall i, 1 <= i <= u (edenot E dd) -> i <= u (edenot E D) ->
                      mem_denot E m lg (Z_to_bv 64 (u (edenot E IA') + i)) = Some (Z_to_bv 8 0) \/
                      mem_denot E m lg (Z_to_bv 64 (u (edenot E IA') + i)) = Some (Z_to_bv 8 1)).
        { intros dd Hdd Hap i Hi HiD. rewrite (mem_denot_apart_gen segs E m kn lg _ HKn HL Hap m).
          - exact (Gc i ltac:(lia)).
          - exists (IA', 1, dd). split; [left; reflexivity|]. cbn [SG.win_den]. pose proof (u_rng (edenot E IA')).
            rewrite u_lit by lia. lia. }
        apply orb_prop in C9 as [C9|C9].
        + (* [comment removed for export] *)
          apply andb_prop in C9 as [C10 C11].
          assert (R10 : 0 <= u (edenot E D) - u (edenot E D') <= 1023) by (apply (kimp_sub segs E m kn _ _ _ _ HKn C10); lia).
          intros i Hi. exact (OLD D' ltac:(lia) C11 i Hi ltac:(lia)).
        + (* [comment removed for export] *)
          repeat match type of C9 with (_ && _)%bool = true => apply andb_prop in C9; destruct C9 as [C9 ?] end.
          match goal with H2 : SG.log_apart _ _ [(IA', 1, D)] = true |- _ => rename H2 into C11 end.
          pose proof (leq_den E D' (eaddl D 1) C9) as ED. assert (UD : u (edenot E D') = u (edenot E D) + 1).
          { rewrite ED, u_eaddl. rewrite (Z.mod_small 1) by lia. apply Z.mod_small. lia. }
          intros i Hi. destruct (Z_le_gt_dec i (u (edenot E D))) as [Le|Gt].
          * exact (OLD D ltac:(lia) C11 i ltac:(lia) Le).
          * replace i with (u (edenot E D')) by lia.
            match goal with H3 : match newest1 _ _ _ with _ => _ end = true |- _ => rename H3 into C12 end.
            destruct (newest1 kn (EAlu ALU_ADD IA' D') lg) as [[sx pre]|] eqn:Hn; [|discriminate].
            apply andb_prop in C12 as [C12 C13].
            destruct (newest1_split kn _ lg sx pre Hn) as (rest & -> & Hw & Hsa).
            pose proof (same_addr_den segs E m kn _ _ HKn Hsa) as HA.
            destruct sx as [sa sw sv]. cbn [e_width e_addr e_val] in *. subst sw.
            pose proof (kimp_range segs E m kn _ _ _ HKn C12) as RV.
            apply log_flat_app in HL as [HLp HLs]. cbn [log_flat] in HLs. destruct HLs as (_ & Hfa & _).
            pose proof (flat_u E _ _ Hfa) as Hu. destruct Hfa as (Hf0 & Hf1 & _ & Hf3).
            assert (UA : u (edenot E (EAlu ALU_ADD IA' D')) = u (adenot E sa)).
            { rewrite <- HA. rewrite u_eaddl. unfold adenot, v_addi. rewrite u_litm. rewrite Z.add_mod_idemp_r by lia. reflexivity. }
            assert (UA2 : u (edenot E (EAlu ALU_ADD IA' D')) = u (edenot E IA') + u (edenot E D')).
            { rewrite u_add_gen. apply Z.mod_small. lia. }
            rewrite mem_denot_app. rewrite (mem_denot_apart_gen segs E m kn pre [(EAlu ALU_ADD IA' D', 0, ELit 1)] HKn HLp C13).
            2:{ exists (EAlu ALU_ADD IA' D', 0, ELit 1). split; [left; reflexivity|]. cbn [SG.win_den].
                rewrite edenot_lit. rewrite !u_lit by lia. rewrite UA2. rewrite Z.add_0_r. lia. }
            cbn [mem_denot]. rewrite <- UA2, UA. rewrite <- (Z.add_0_r (u (adenot E sa))).
            change 0 with (Z.of_nat 0). rewrite wbytes_nth.
            2:{ rewrite length_N_to_le_bytes. unfold estart in Hu, Hf3. rewrite <- Hu in Hf3. lia. }
            2:{ rewrite length_N_to_le_bytes. lia. }
            assert (EV : edenot E sv = Z_to_bv 64 0 \/ edenot E sv = Z_to_bv 64 1).
            { destruct (Z.eq_dec (u (edenot E sv)) 0) as [Z0|NZ]; [left|right]; apply bv_eq; rewrite u_lit by lia; lia. }
            destruct EV as [-> | ->]; [left | right]; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma byte_in_sound : forall kn B0 X0 lo hi, know_ok segs E m kn -> byte_in segs kn (SG.vc_path c) B0 X0 lo hi = true ->
      u (edenot E B0) + u (edenot E X0) < 2 ^ 64 -> lo <= mbyte segs m (u (edenot E B0) + u (edenot E X0)) <= hi.
    Proof.
      intros kn B0 X0 lo hi HKn H Hr. unfold byte_in in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a b]|] eqn:Hrr; [|discriminate]. apply andb_prop in H as [H1 H2].
      pose proof (leq_den E _ _ H1) as HX0.
      destruct (rrec_den segs m E _ 1 sc a b HP Hin Hrr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E B0) + u (edenot E X0)).
      { rewrite (rel_addr E a B0) by (rewrite HX0; lia). rewrite HX0. reflexivity. }
      pose proof (rdn_length segs m 1 (adenot E a) bs Hrd) as HLn.
      destruct bs as [|b0 [|b1 r]]; cbn in HLn; try discriminate.
      cbn [bytes_le_to_Z] in Hv. rewrite Z.shiftl_0_l, Z.lor_0_r in Hv.
      pose proof (bv_unsigned_in_range _ b0) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      assert (Vb : u (ev E b) = u b0) by (rewrite <- Hv; apply u_lit; lia).
      assert (BR : lo <= u b0 <= hi).
      { apply orb_prop in H2 as [H2|H2].
        - assert (HKb : know_ok segs E m (KRange (x1 b) 0 255 :: kn)).
          { constructor; [|exact HKn]. cbn [kentry_ok]. rewrite u_x1 by lia. lia. }
          pose proof (kimp_range segs E m _ _ _ _ HKb H2) as R. rewrite u_x1 in R by lia. lia.
        - pose proof (kimp_range segs E m kn _ _ _ HKn H2) as R. cbn [edenot] in R. lia. }
      rewrite <- Haddr. rewrite (rdn1_val m (adenot E a) b0 Hrd). exact BR.
    Qed.

    Lemma byte_out_sound : forall kn B0 X0, know_ok segs E m kn -> byte_out kn (SG.vc_path c) B0 X0 = true ->
      u (edenot E B0) + u (edenot E X0) < 2 ^ 64 ->
      let v := mbyte segs m (u (edenot E B0) + u (edenot E X0)) in v < 45 \/ 58 <= v.
    Proof.
      intros kn B0 X0 HKn H Hr v. unfold byte_out in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a b]|] eqn:Hrr; [|discriminate]. apply andb_prop in H as [H1 H2].
      pose proof (leq_den E _ _ H1) as HX0.
      destruct (rrec_den segs m E _ 1 sc a b HP Hin Hrr) as (bs & Hrd & Hv).
      assert (Haddr : u (adenot E a) = u (edenot E B0) + u (edenot E X0)).
      { rewrite (rel_addr E a B0) by (rewrite HX0; lia). rewrite HX0. reflexivity. }
      pose proof (rdn_length segs m 1 (adenot E a) bs Hrd) as HLn.
      destruct bs as [|b0 [|b1 r]]; cbn in HLn; try discriminate.
      cbn [bytes_le_to_Z] in Hv. rewrite Z.shiftl_0_l, Z.lor_0_r in Hv.
      pose proof (bv_unsigned_in_range _ b0) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      assert (Vb : u (ev E b) = u b0) by (rewrite <- Hv; apply u_lit; lia).
      assert (Hvv : v = u b0) by (unfold v; rewrite <- Haddr; exact (rdn1_val m (adenot E a) b0 Hrd)).
      apply existsb_exists in H2 as (K & HKin & HOK). unfold out_fact in HOK.
      destruct K as [| | | | |e lo hi| | | |]; try discriminate.
      destruct e as [| |op e1 e2| | | | |]; try discriminate. destruct op; try discriminate.
      destruct e1 as [| | | | | |sx k1 w1 e3|]; try discriminate. destruct sx; try discriminate.
      destruct k1 as [|k1]; [|discriminate]. destruct w1 as [|[|w1]]; try discriminate.
      destruct e3 as [|b'| | | | | |]; try discriminate.
      destruct e2 as [z| | | | | | |]; try discriminate.
      repeat match type of HOK with (_ && _)%bool = true => apply andb_prop in HOK; destruct HOK as [HOK ?] end.
      apply Nat.eqb_eq in HOK. subst b'.
      repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end.
      pose proof (proj1 (Forall_forall _ _) HKn _ HKin) as RK. cbn [kentry_ok] in RK.
      change (edenot E (EAlu ALU_ADD (EExt false 0 1 (EVar b)) (ELit z))) with (edenot E (eaddl (x1 b) z)) in RK.
      rewrite u_eaddl, Z.add_mod_idemp_r in RK by lia. rewrite u_x1 in RK by lia. rewrite Vb in RK.
      rewrite Hvv. destruct (Z_lt_ge_dec (u b0) 45) as [LT1|G]; [left; exact LT1|]. right.
      destruct (Z_lt_ge_dec (u b0) (lo - z)) as [L2|G2]; [|lia]. exfalso.
      rewrite Z.mod_small in RK by lia. lia.
    Qed.

    Lemma gbuf_byte : forall v, 0 <= v < len -> mbyte segs m (u (edenot E B) + v) = byte_at data v.
    Proof.
      intros v Hv. destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)).
      unfold mbyte. rewrite (mbytes_rdn segs m _ _ v 1 HBm) by (rewrite ?bufbytes_length; lia).
      destruct (skipn (Z.to_nat v) (bufbytes data)) as [|b0 r0] eqn:Hsk.
      - exfalso. pose proof (f_equal (@length byte) Hsk) as LL. rewrite length_skipn in LL. cbn in LL.
        pose proof (bufbytes_length data). lia.
      - cbn [firstn]. assert (Hn0 : nth (Z.to_nat v) (bufbytes data) (Z_to_bv 8 0) = b0).
        { rewrite <- (firstn_skipn (Z.to_nat v) (bufbytes data)), app_nth2; rewrite length_firstn; [|pose proof (bufbytes_length data); lia].
          replace (Z.to_nat v - Nat.min (Z.to_nat v) (length (bufbytes data)))%nat with 0%nat
            by (pose proof (bufbytes_length data); lia). rewrite Hsk. reflexivity. }
        rewrite <- Hn0. rewrite bufbytes_nth by (try exact HBd; lia).
        pose proof (byte_at_rng data v HBd). rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
    Qed.

    Lemma gnum1_sound : forall kn args, know_ok segs E m kn -> tok_holds args ->
      forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (gnum1 segs MF kn (SG.vc_path c) B L args).
    Proof.
      intros kn args HKn Ht M. unfold gnum1.
      destruct args as [|K [|V [|? ?]]]; try constructor.
      match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C; [|constructor] end.
      repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
      match goal with H1 : kimp _ _ (KRange (esub2 L V) _ _) = true, H2 : kimp _ _ (KRange V 0 MF) = true,
        H3 : kimp _ _ (KRange L 0 MF) = true |- _ =>
        pose proof (kimp_sub segs E m kn _ _ _ _ HKn H1) as RLV; pose proof (kimp_range segs E m kn _ _ _ HKn H2) as RV;
        pose proof (kimp_range segs E m kn _ _ _ HKn H3) as RL end.
      unfold tok_holds in Ht. cbn [map gp2] in Ht. destruct Ht as (Hk4 & Hkj & Hv).
      rewrite (leq_den E K (ELit 0) C), edenot_lit, u_lit in Hv by lia. change (0 / 4) with 0 in Hv.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      assert (RLV' : 1 <= u (edenot E L) - u (edenot E V) <= MF) by (apply RLV; lia).
      assert (BY : mbyte segs m (u (edenot E B) + u (edenot E V)) = byte_at data (znth idxs 0)).
      { rewrite gbuf_byte by lia. rewrite Hv. reflexivity. }
      pose proof (u_rng (edenot E B)). pose proof (u_rng (edenot E V)).
      apply Forall_app. split.
      - match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C2; [|constructor] end.
        constructor; [|constructor]. cbn [ST.g_id ST.g_args map gp2]. unfold is_numstart.
        apply orb_prop in C2 as [C2|C2]; pose proof (byte_in_sound kn B V _ _ HKn C2 ltac:(lia)) as R; rewrite BY in R.
        + replace (byte_at data (znth idxs 0)) with 45 by lia. reflexivity.
        + apply orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia.
      - match goal with |- Forall _ (if ?cc then _ else _) => destruct cc eqn:C2; [|constructor] end.
        constructor; [|constructor]. cbn [ST.g_id ST.g_args map gp2]. unfold is_numstart.
        assert (NS : byte_at data (znth idxs 0) < 45 \/ byte_at data (znth idxs 0) = 46 \/ byte_at data (znth idxs 0) = 47 \/
                     58 <= byte_at data (znth idxs 0)).
        { repeat (apply orb_prop in C2 as [C2|C2]).
          - pose proof (byte_in_sound kn B V _ _ HKn C2 ltac:(lia)) as R; rewrite BY in R. lia.
          - pose proof (byte_in_sound kn B V _ _ HKn C2 ltac:(lia)) as R; rewrite BY in R. lia.
          - pose proof (byte_in_sound kn B V _ _ HKn C2 ltac:(lia)) as R; rewrite BY in R. lia.
          - pose proof (byte_out_sound kn B V HKn C2 ltac:(lia)) as R; cbv zeta in R; rewrite BY in R. lia. }
        apply orb_false_intro; [apply Z.eqb_neq; lia|].
        destruct (Z.leb_spec 48 (byte_at data (znth idxs 0))); destruct (Z.leb_spec (byte_at data (znth idxs 0)) 57);
          cbn [andb]; try reflexivity; lia.
    Qed.

    (* [comment removed for export] *)
    Ltac urng := repeat match goal with
      | H : context [u (edenot ?E0 ?x)] |- _ =>
          lazymatch goal with _ : 0 <= u (edenot E0 x) < 2 ^ 64 |- _ => fail | _ => pose proof (u_rng (edenot E0 x)) end
      | |- context [u (edenot ?E0 ?x)] =>
          lazymatch goal with _ : 0 <= u (edenot E0 x) < 2 ^ 64 |- _ => fail | _ => pose proof (u_rng (edenot E0 x)) end
      end.
    Ltac ulia := urng; lia.
    Lemma gbuf_byte64 : forall v, 0 <= v < len + 64 -> mbyte segs m (u (edenot E B) + v) = byte_at data v.
    Proof.
      intros v Hv. destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)).
      unfold mbyte. rewrite (mbytes_rdn segs m _ _ v 1 HBm) by (rewrite ?bufbytes_length; ulia).
      destruct (skipn (Z.to_nat v) (bufbytes data)) as [|b0 r0] eqn:Hsk.
      - exfalso. pose proof (f_equal (@length byte) Hsk) as LL. rewrite length_skipn in LL. cbn in LL.
        pose proof (bufbytes_length data). ulia.
      - cbn [firstn]. assert (Hn0 : nth (Z.to_nat v) (bufbytes data) (Z_to_bv 8 0) = b0).
        { rewrite <- (firstn_skipn (Z.to_nat v) (bufbytes data)), app_nth2; rewrite length_firstn; [|pose proof (bufbytes_length data); ulia].
          replace (Z.to_nat v - Nat.min (Z.to_nat v) (length (bufbytes data)))%nat with 0%nat
            by (pose proof (bufbytes_length data); ulia). rewrite Hsk. reflexivity. }
        rewrite <- Hn0. rewrite bufbytes_nth by (try exact HBd; ulia).
        pose proof (byte_at_rng data v HBd). rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by ulia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma read1 : forall s a v X0, In s (SG.vc_path c) -> rrec 1 s = Some (a, v) -> leq (rel a B) X0 = true ->
      0 <= u (edenot E X0) < len + 64 ->
      u (ev E v) = byte_at data (u (edenot E X0)) /\ u (edenot E (x1 v)) = byte_at data (u (edenot E X0)).
    Proof.
      intros s a v X0 Hin Hrr H1 Hr. pose proof (leq_den E _ _ H1) as HX0.
      destruct (rrec_den segs m E _ 1 s a v HP Hin Hrr) as (bs & Hrd & Hv).
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm).
      assert (Haddr : u (adenot E a) = u (edenot E B) + u (edenot E X0)).
      { rewrite (rel_addr E a B) by (rewrite HX0; ulia). rewrite HX0. reflexivity. }
      pose proof (rdn_length segs m 1 (adenot E a) bs Hrd) as HLn.
      destruct bs as [|b0 [|b1 r]]; cbn in HLn; try discriminate.
      cbn [bytes_le_to_Z] in Hv. rewrite Z.shiftl_0_l, Z.lor_0_r in Hv.
      pose proof (bv_unsigned_in_range _ b0) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      assert (Vb : u (ev E v) = u b0) by (rewrite <- Hv; apply u_lit; ulia).
      pose proof (rdn1_val m (adenot E a) b0 Hrd) as Hmb. rewrite Haddr, gbuf_byte64 in Hmb by ulia.
      split; [ulia|]. rewrite u_x1 by ulia. ulia.
    Qed.

    Lemma u_dig : forall v, u (edenot E (dig_expr v)) = (u (ev E v) mod 256 + 208) mod 256.
    Proof.
      intros v. pose proof (u_x1' v) as Ub. unfold dig_expr. cbn [edenot].
      rewrite alu_and_u, u_lit by ulia. change (edenot E (EAlu ALU_ADD (x1 v) (ELit (-48)))) with (alu64 ALU_ADD (edenot E (x1 v)) (Z_to_bv 64 (-48))).
      rewrite alu_add. unfold v_add. rewrite u_litm, (u_litm (-48)).
      change 255 with (Z.ones 8). rewrite Z.land_ones by ulia. change (2 ^ 8) with 256.
      rewrite <- Znumtheory.Zmod_div_mod by (try ulia; exists (2 ^ 56); reflexivity).
      rewrite Zplus_mod, Ub. change (-48 mod 2 ^ 64 mod 256) with 208. rewrite Z.mod_mod by ulia. reflexivity.
    Qed.

    Lemma digv_at_sound : forall kn X0 D, know_ok segs E m kn -> digv_at segs kn (SG.vc_path c) B X0 D = true ->
      0 <= u (edenot E X0) < len + 64 ->
      byte_at data (u (edenot E X0)) = u (edenot E D) + 48 /\ u (edenot E D) <= 9 /\ u (edenot E X0) < len.
    Proof.
      intros kn X0 D HKn H Hr. unfold digv_at in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a v]|] eqn:Hrr; [|discriminate].
      repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
      match goal with H1 : leq D _ = true, H2 : kimp _ _ (KRange (x1 v) 48 57) = true |- _ => rename H1 into C2; rename H2 into C3 end.
      destruct (read1 sc a v X0 Hin Hrr H Hr) as [R1 R2].
      pose proof (kimp_range segs E m kn _ _ _ HKn C3) as RB. rewrite R2 in RB.
      rewrite (leq_den E _ _ C2). change (EAlu ALU_ADD (x1 v) (ELit (-48))) with (eaddl (x1 v) (-48)).
      rewrite u_eaddl, R2. rewrite Zplus_mod_idemp_r.
      rewrite Z.mod_small by ulia.
      split; [ulia|]. split; [ulia|].
      destruct (Z_lt_ge_dec (u (edenot E X0)) len) as [LT|GE]; [exact LT|]. rewrite byte_at_past in RB by (unfold zlength in *; ulia). ulia.
    Qed.

    Lemma nodig_at_sound : forall kn X0, know_ok segs E m kn -> nodig_at segs kn (SG.vc_path c) B X0 = true ->
      0 <= u (edenot E X0) < len + 64 -> ~ isdig (byte_at data (u (edenot E X0))).
    Proof.
      intros kn X0 HKn H Hr. unfold nodig_at in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a v]|] eqn:Hrr; [|discriminate]. apply andb_prop in H as [H1 H2].
      destruct (read1 sc a v X0 Hin Hrr H1 Hr) as [R1 R2].
      pose proof (kimp_range segs E m kn _ _ _ HKn H2) as RD. rewrite u_dig, R1 in RD.
      destruct gbuf_ctx as (_ & _ & HBd & _). pose proof (byte_at_rng data (u (edenot E X0)) HBd) as Rb.
      unfold isdig. intros Hd. rewrite (Z.mod_small (byte_at _ _)) in RD by ulia.
      replace ((byte_at data (u (edenot E X0)) + 208) mod 256) with (byte_at data (u (edenot E X0)) - 48) in RD; [ulia|].
      rewrite <- (Z.mod_small (byte_at data (u (edenot E X0)) - 48) 256) by ulia.
      replace (byte_at data (u (edenot E X0)) + 208) with (byte_at data (u (edenot E X0)) - 48 + 1 * 256) by ulia.
      rewrite Z.mod_add; ulia.
    Qed.

    Lemma zero_at_sound : forall kn X0, know_ok segs E m kn -> zero_at segs kn (SG.vc_path c) B X0 = true ->
      0 <= u (edenot E X0) < len + 64 -> byte_at data (u (edenot E X0)) = 48.
    Proof.
      intros kn X0 HKn H Hr. unfold zero_at in H. apply existsb_exists in H as (sc & Hin & H).
      destruct (rrec 1 sc) as [[a v]|] eqn:Hrr; [|discriminate]. apply andb_prop in H as [H1 H2].
      destruct (read1 sc a v X0 Hin Hrr H1 Hr) as [R1 R2].
      apply orb_prop in H2 as [H2|H2]; pose proof (kimp_range segs E m kn _ _ _ HKn H2) as RV; cbn [edenot] in RV; ulia.
    Qed.

    Lemma acc_step_sound : forall X0 X' D, acc_step X0 X' D = true -> u (edenot E D) <= 9 ->
      u (edenot E X') = (10 * u (edenot E X0) + u (edenot E D)) mod 2 ^ 64.
    Proof.
      intros X0 X' D H HD. unfold acc_step in H.
      assert (EQ : u (edenot E (nsub X' (emul 10 X0))) = (u (edenot E X') - (10 * u (edenot E X0)) mod 2 ^ 64) mod 2 ^ 64).
      { rewrite nsub_den. change (alu64 ALU_SUB (edenot E X') (edenot E (emul 10 X0))) with (edenot E (esub2 X' (emul 10 X0))).
        rewrite u_esub2, u_emul'. rewrite (Z.mod_small 10) by ulia. reflexivity. }
      assert (DV : u (edenot E (nsub X' (emul 10 X0))) = u (edenot E D)).
      { apply orb_prop in H as [H|H]; rewrite (leq_den E _ _ H); [reflexivity|].
        cbn [edenot]. rewrite alu_and_u, u_lit by ulia. change 255 with (Z.ones 8). rewrite Z.land_ones by ulia.
        apply Z.mod_small. pose proof (u_rng (edenot E D)). ulia. }
      rewrite EQ in DV. pose proof (u_rng (edenot E X')). pose proof (u_rng (edenot E X0)). pose proof (u_rng (edenot E D)).
      pose proof (Z.mod_pos_bound (10 * u (edenot E X0)) (2 ^ 64) ltac:(ulia)).
      rewrite <- Zplus_mod_idemp_l. rewrite <- DV.
      rewrite Zplus_mod_idemp_r. replace ((10 * u (edenot E X0)) mod 2 ^ 64 + (u (edenot E X') - (10 * u (edenot E X0)) mod 2 ^ 64))
        with (u (edenot E X')) by ulia. rewrite Z.mod_small by ulia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma gdb_step_sound : forall P0 X0 X', gdb_step (SG.vc_src c) P0 X0 X' = true ->
      u (edenot E P0) < len /\ byte_at data (u (edenot E P0)) = (u (edenot E X') - 10 * u (edenot E X0)) mod 2 ^ 64 + 48 /\
      (exists dd : word, u dd <= 9 /\ byte_at data (u (edenot E P0)) = u dd + 48 /\ u (edenot E X') = (10 * u (edenot E X0) + u dd) mod 2 ^ 64).
    Proof.
      intros P0 X0 X' H. unfold gdb_step in H. apply existsb_exists in H as (args & Ha & H).
      destruct args as [|P2 [|D [|? ?]]]; try discriminate. apply andb_prop in H as [H1 H2].
      pose proof (src_holds 11 [P2; D] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (G1 & G2 & G3).
      rewrite (leq_den E _ _ H1) in G1, G2.
      pose proof (acc_step_sound X0 X' D H2 G3) as ST.
      split; [exact G1|]. split.
      - rewrite ST, G2. f_equal. rewrite Zminus_mod_idemp_l. replace (10 * u (edenot E X0) + u (edenot E D) - 10 * u (edenot E X0)) with (u (edenot E D)) by ulia.
        rewrite Z.mod_small; [reflexivity|]. pose proof (u_rng (edenot E D)). ulia.
      - exists (edenot E D). split; [exact G3|]. split; [exact G2 | exact ST].
    Qed.

    Lemma gdv_sound : forall kn args M, know_ok segs E m kn -> gdv_ok segs MF kn (SG.vc_src c) L args = true ->
      GP 10 (map (edenot E) args) M.
    Proof.
      intros kn args M HKn H. unfold gdv_ok in H. destruct args as [|SA0' [|P' [|X' [|? ?]]]]; try discriminate.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)). cbn [map gp2].
      apply orb_prop in H as [H|H].
      - repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H1 : leq X' (ELit 0) = true, H2 : kimp _ _ (KRange SA0' 0 MF) = true, H3 : kimp _ _ (KRange (esub2 L SA0') 0 MF) = true |- _ =>
          rename H1 into C2; rename H2 into C3; rename H3 into C4 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3.
        assert (R4 : 0 <= u (edenot E L) - u (edenot E SA0') <= MF) by (apply (kimp_sub segs E m kn _ _ _ _ HKn C4); ulia).
        rewrite (leq_den E _ _ H), (leq_den E _ _ C2), edenot_lit, u_lit by ulia.
        split; [ulia|]. split; [ulia|]. split; [intros i Hi; ulia|]. rewrite decval_nil. reflexivity.
      - apply existsb_exists in H as (args & Ha & H). destruct args as [|SA0 [|P [|X0 [|? ?]]]]; try discriminate.
        pose proof (src_holds 10 [SA0; P; X0] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (G1 & G2 & G3 & G4).
        apply andb_prop in H as [HS' H]. rewrite (leq_den E _ _ HS').
        apply orb_prop in H as [H|H].
        + apply andb_prop in H as [HP' HX']. rewrite (leq_den E _ _ HP'), (leq_den E _ _ HX'). split; [ulia|]. split; [ulia|]. split; [exact G3 | exact G4].
        + apply andb_prop in H as [HP' HG]. destruct (gdb_step_sound P X0 X' HG) as (B1 & _ & (dd & D1 & D2 & D3)). pose proof (u_rng dd) as Rdd.
          assert (UP : u (edenot E P') = u (edenot E P) + 1).
          { pose proof (u_rng (edenot E P)). rewrite (leq_den E _ _ HP'), u_eaddl. rewrite (Z.mod_small 1) by ulia. apply Z.mod_small. ulia. }
          rewrite UP. split; [ulia|]. split; [ulia|]. split.
          * intros i Hi. destruct (Z.eq_dec i (u (edenot E P))) as [->|NE]; [unfold isdig; ulia | apply G3; ulia].
          * rewrite D3, G4, decval_step by ulia. rewrite D2.
            rewrite Zplus_mod, (Zmult_mod 10), Z.mod_mod by ulia. rewrite <- (Zmult_mod 10 (decval _ _ _)).
            rewrite <- Zplus_mod. f_equal. ulia.
    Qed.

    Lemma gdb_sound : forall kn args M, know_ok segs E m kn -> gdb_ok segs MF kn (SG.vc_path c) (SG.vc_src c) B L args = true ->
      GP 11 (map (edenot E) args) M.
    Proof.
      intros kn args M HKn H. unfold gdb_ok in H. destruct args as [|P' [|D' [|? ?]]]; try discriminate.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)). cbn [map gp2].
      apply orb_prop in H as [H|H].
      - repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H2 : kimp _ _ (KRange (esub2 _ _) _ _) = true, H3 : digv_at _ _ _ _ _ _ = true |- _ =>
          rename H2 into C2; rename H3 into C3 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn H) as R1.
        pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R2. rewrite u_esub2, u_eaddl in R2.
        rewrite (Z.mod_small 63) in R2 by ulia. rewrite (Z.mod_small (_ + 63)) in R2 by ulia.
        assert (R3 : u (edenot E P') <= len + 63).
        { destruct (Z_le_gt_dec (u (edenot E P')) (u (edenot E L) + 63)) as [Le|Gt]; [ulia|]. exfalso.
          rewrite <- (Z.mod_add _ 1) in R2 by ulia. rewrite Z.mod_small in R2 by ulia. ulia. }
        destruct (digv_at_sound kn P' D' HKn C3 ltac:(ulia)) as (D1 & D2 & D3). split; [exact D3|]. split; [exact D1 | exact D2].
      - apply existsb_exists in H as (args & Ha & H). destruct args as [|P [|D [|? ?]]]; try discriminate.
        pose proof (src_holds 11 [P; D] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G.
        apply andb_prop in H as [H1 H2]. rewrite (leq_den E _ _ H1), (leq_den E _ _ H2). exact G.
    Qed.

    Lemma gdz_adv_sound : forall kn S0 S2 S2' P0, know_ok segs E m kn -> gdz_adv segs kn (SG.vc_path c) B S2 S2' = true ->
      u (edenot E S0) <= u (edenot E S2) <= u (edenot E P0) -> u (edenot E P0) <= len ->
      (forall i, u (edenot E S0) <= i < u (edenot E S2) -> byte_at data i = 48) ->
      (forall i, u (edenot E S2) <= i < u (edenot E P0) -> isdig (byte_at data i)) -> ~ isdig (byte_at data (u (edenot E P0))) ->
      u (edenot E S0) <= u (edenot E S2') <= u (edenot E P0) /\
      (forall i, u (edenot E S0) <= i < u (edenot E S2') -> byte_at data i = 48) /\
      (forall i, u (edenot E S2') <= i < u (edenot E P0) -> isdig (byte_at data i)).
    Proof.
      intros kn S0 S2 S2' P0 HKn H R1 R2 Z1 D1 N1. unfold gdz_adv in H. apply orb_prop in H as [H|H].
      - rewrite (leq_den E _ _ H). split; [exact R1|]. split; [exact Z1 | exact D1].
      - apply andb_prop in H as [H1 H2]. pose proof (zero_at_sound kn S2 HKn H2 ltac:(ulia)) as Z0.
        assert (LT : u (edenot E S2) < u (edenot E P0)).
        { destruct (Z.eq_dec (u (edenot E S2)) (u (edenot E P0))) as [EQ|NE]; [|ulia]. exfalso. apply N1. rewrite <- EQ, Z0. unfold isdig. ulia. }
        assert (US : u (edenot E S2') = u (edenot E S2) + 1).
        { pose proof (u_rng (edenot E S2)). rewrite (leq_den E _ _ H1), u_eaddl. rewrite (Z.mod_small 1) by ulia. apply Z.mod_small. ulia. }
        rewrite US. split; [ulia|]. split.
        + intros i Hi. destruct (Z.eq_dec i (u (edenot E S2))) as [->|NE]; [exact Z0 | apply Z1; ulia].
        + intros i Hi. apply D1. ulia.
    Qed.

    Lemma gdz_sound : forall kn args M, know_ok segs E m kn -> gdz_ok segs kn (SG.vc_path c) (SG.vc_src c) B args = true ->
      GP 12 (map (edenot E) args) M.
    Proof.
      intros kn args M HKn H. unfold gdz_ok in H. destruct args as [|SA0' [|S2' [|P' [|X' [|? ?]]]]]; try discriminate.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)). cbn [map gp2].
      apply orb_prop in H as [H|H].
      - apply existsb_exists in H as (args & Ha & H). destruct args as [|SA0 [|S2 [|P [|X0 [|? ?]]]]]; try discriminate.
        pose proof (src_holds 12 [SA0; S2; P; X0] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G.
        destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H2 : leq P' P = true, H3 : leq X' X0 = true, H4 : gdz_adv _ _ _ _ _ _ = true |- _ =>
          rename H2 into C2; rename H3 into C3; rename H4 into C4 end.
        rewrite (leq_den E _ _ H), (leq_den E _ _ C2), (leq_den E _ _ C3).
        destruct (gdz_adv_sound kn SA0 S2 S2' P HKn C4 ltac:(ulia) G3 G4 G5 G6) as (A1 & A2 & A3).
        split; [ulia|]. split; [ulia|]. split; [exact G3|]. split; [exact A2|]. split; [exact A3|]. split; [exact G6 | exact G7].
      - apply existsb_exists in H as (args & Ha & H). destruct args as [|SA0 [|P [|X0 [|? ?]]]]; try discriminate.
        pose proof (src_holds 10 [SA0; P; X0] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (G1 & G2 & G3 & G4).
        repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H2 : gdz_adv _ _ _ _ _ _ = true, H3 : (_ || _)%bool = true |- _ => rename H2 into C2; rename H3 into C3 end.
        rewrite (leq_den E _ _ H).
        apply orb_prop in C3 as [C3|C3].
        + repeat match type of C3 with (_ && _)%bool = true => apply andb_prop in C3; destruct C3 as [C3 ?] end.
          match goal with H2 : leq X' X0 = true, H3 : nodig_at _ _ _ _ _ = true |- _ => rename H2 into C4; rename H3 into C5 end.
          rewrite (leq_den E _ _ C3), (leq_den E _ _ C4).
          pose proof (nodig_at_sound kn P HKn C5 ltac:(ulia)) as N1.
          destruct (gdz_adv_sound kn SA0 SA0 S2' P HKn C2 ltac:(ulia) G2 ltac:(intros i Hi; ulia) G3 N1) as (A1 & A2 & A3).
          split; [ulia|]. split; [ulia|]. split; [exact G2|]. split; [exact A2|]. split; [exact A3|]. split; [exact N1 | exact G4].
        + repeat match type of C3 with (_ && _)%bool = true => apply andb_prop in C3; destruct C3 as [C3 ?] end.
          match goal with H2 : nodig_at _ _ _ _ _ = true, H3 : gdb_step _ _ _ _ = true |- _ => rename H2 into C4; rename H3 into C5 end.
          destruct (gdb_step_sound P X0 X' C5) as (B1 & _ & (dd & D1 & D2 & D3)). pose proof (u_rng dd) as Rdd.
          assert (UP : u (edenot E P') = u (edenot E P) + 1).
          { pose proof (u_rng (edenot E P)). rewrite (leq_den E _ _ C3), u_eaddl. rewrite (Z.mod_small 1) by ulia. apply Z.mod_small. ulia. }
          pose proof (nodig_at_sound kn P' HKn C4 ltac:(ulia)) as N1.
          assert (DG : forall i, u (edenot E SA0) <= i < u (edenot E P') -> isdig (byte_at data i)).
          { intros i Hi. destruct (Z.eq_dec i (u (edenot E P))) as [->|NE]; [unfold isdig; ulia | apply G3; ulia]. }
          destruct (gdz_adv_sound kn SA0 SA0 S2' P' HKn C2 ltac:(ulia) ltac:(ulia) ltac:(intros i Hi; ulia) DG N1) as (A1 & A2 & A3).
          split; [ulia|]. split; [ulia|]. split; [ulia|]. split; [exact A2|]. split; [exact A3|]. split; [exact N1|].
          rewrite UP, D3, G4, decval_step by ulia. rewrite D2.
          rewrite Zplus_mod, (Zmult_mod 10), Z.mod_mod by ulia. rewrite <- (Zmult_mod 10 (decval _ _ _)).
          rewrite <- Zplus_mod. f_equal. ulia.
    Qed.

    Lemma gd_sound : forall kn g M, know_ok segs E m kn -> gd_ok segs MF kn (SG.vc_path c) (SG.vc_src c) g = true ->
      GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M.
    Proof.
      intros kn [gid gargs] M HKn H. unfold gd_ok in H. rewrite HB in H. cbn [ST.g_id ST.g_args] in *.
      destruct gid as [|[|[|[|[|[|[|[|[|[|[|[|[|gid]]]]]]]]]]]]]; try discriminate.
      - exact (gdv_sound kn gargs M HKn H).
      - exact (gdb_sound kn gargs M HKn H).
      - exact (gdz_sound kn gargs M HKn H).
    Qed.

    Lemma le18_sound : forall kn A P, know_ok segs E m kn -> le18 segs MF kn L A P = true ->
      u (edenot E A) <= u (edenot E P) -> u (edenot E P) <= len -> 0 <= u (edenot E P) - u (edenot E A) <= 18.
    Proof.
      intros kn A P HKn H R1 R2. destruct gbuf_ctx as (HLen & HBb & HBd & HBm). unfold le18 in H.
      apply orb_prop in H as [H|H].
      - pose proof (kimp_range segs E m kn _ _ _ HKn H) as R. rewrite u_esub2 in R. rewrite Z.mod_small in R by ulia. ulia.
      - apply andb_prop in H as [H1 H2]. pose proof (kimp_range segs E m kn _ _ _ HKn H2) as RL.
        pose proof (kimp_range segs E m kn _ _ _ HKn H1) as R. rewrite u_esub2, u_eaddl in R.
        rewrite (Z.mod_small 18) in R by ulia. rewrite (Z.mod_small (_ + 18)) in R by ulia.
        destruct (Z_le_gt_dec (u (edenot E P)) (u (edenot E A) + 18)) as [Le|Gt]; [ulia|]. exfalso.
        rewrite <- (Z.mod_add _ 1) in R by ulia. rewrite Z.mod_small in R by ulia. ulia.
    Qed.

    Lemma gd_fact_sound : forall kn K, know_ok segs E m kn -> gd_fact segs MF kn (SG.vc_src c) K = true -> kentry_ok segs E m K.
    Proof.
      intros kn K HKn H. unfold gd_fact in H. rewrite HB in H. destruct K as [| | | | |X' lo hi| | | |]; try discriminate.
      repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
      match goal with H2 : Z.eqb hi E18 = true, H3 : (_ || _)%bool = true |- _ => rename H2 into C2; rename H3 into C3 end.
      apply Z.eqb_eq in H. apply Z.eqb_eq in C2. subst lo hi. cbn [kentry_ok]. unfold E18.
      destruct gbuf_ctx as (HLen & HBb & HBd & HBm). pose proof (u_rng (edenot E B)).
      assert (B18 : forall x d, x = d mod 2 ^ 64 -> 0 <= d <= 999999999999999999 -> 0 <= x <= 999999999999999999).
      { intros x d -> Hd. rewrite Z.mod_small by ulia. exact Hd. }
      apply orb_prop in C3 as [C3|C3].
      - apply existsb_exists in C3 as (args & Ha & C3). destruct args as [|SA0 [|S2 [|P [|X0 [|? ?]]]]]; try discriminate.
        pose proof (src_holds 12 [SA0; S2; P; X0] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G.
        destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7). apply andb_prop in C3 as [C3 C4].
        pose proof (le18_sound kn S2 P HKn C4 G2 G3) as R.
        rewrite (leq_den E _ _ C3). apply (B18 _ _ G7).
        rewrite (decval_zeros data (u (edenot E SA0)) (u (edenot E S2)) (u (edenot E P))); [| ulia | exact G4].
        apply decval_18; [ulia | ulia | exact G5].
      - apply existsb_exists in C3 as (args & Ha & C3). destruct args as [|SA0 [|P [|X0 [|? ?]]]]; try discriminate.
        pose proof (src_holds 10 [SA0; P; X0] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (G1 & G2 & G3 & G4).
        apply orb_prop in C3 as [C3|C3]; apply andb_prop in C3 as [C3 C4].
        + pose proof (le18_sound kn SA0 P HKn C4 G1 G2) as R.
          rewrite (leq_den E _ _ C3). apply (B18 _ _ G4). apply decval_18; [ulia | ulia | exact G3].
        + destruct (gdb_step_sound P X0 X' C3) as (B1 & _ & (dd & D1 & D2 & D3)). pose proof (u_rng dd) as Rdd.
          assert (UP1 : u (edenot E (eaddl P 1)) = u (edenot E P) + 1).
          { rewrite u_eaddl. rewrite (Z.mod_small 1) by ulia. apply Z.mod_small. ulia. }
          pose proof (le18_sound kn SA0 (eaddl P 1) HKn C4 ltac:(rewrite UP1; ulia) ltac:(rewrite UP1; ulia)) as R.
          rewrite UP1 in R.
          assert (DG : forall i, u (edenot E SA0) <= i < u (edenot E P) + 1 -> isdig (byte_at data i)).
          { intros i Hi. destruct (Z.eq_dec i (u (edenot E P))) as [->|NE]; [unfold isdig; ulia | apply G3; ulia]. }
          apply (B18 _ (decval data (u (edenot E SA0)) (u (edenot E P) + 1))).
          * rewrite D3, G4, decval_step by ulia. rewrite D2.
            rewrite Zplus_mod, (Zmult_mod 10), Z.mod_mod by ulia. rewrite <- (Zmult_mod 10 (decval _ _ _)).
            rewrite <- Zplus_mod. f_equal. ulia.
          * apply decval_18; [ulia | ulia | exact DG].
    Qed.

    Lemma derive_sound : log_flat E (SG.vc_log c) -> know_ok segs E m (fst (derive segs MF TD c)) /\
      forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd (derive segs MF TD c)).
    Proof.
      intros HL. unfold derive. cbv zeta. rewrite HX, HB. cbn [fst snd].
      set (kn := SG.vc_kn c). set (src := SG.vc_src c). set (path := SG.vc_path c).
      set (F6 := flat_map (fun s => srl_facts segs kn (e_val s)) (SG.vc_log c)).
      set (R1 := map (r1_read segs MF kn X NN L) path).
      assert (HF6 : know_ok segs E m F6) by (apply Forall_flat_map'; intros x _; apply srl_sound; exact HK).
      assert (HR1 : forall x, In x R1 -> know_ok segs E m (fst x) /\
                     forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd x)).
      { intros x Hx. apply in_map_iff in Hx as (sc & <- & Hin). exact (r1_sound kn sc HK Hin). }
      assert (HF1 : know_ok segs E m (flat_map fst R1)) by (apply Forall_flat_map'; intros x Hx; exact (proj1 (HR1 x Hx))).
      assert (HA1 : forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (flat_map snd R1))
        by (intros M; apply Forall_flat_map'; intros x Hx; exact (proj2 (HR1 x Hx) M)).
      assert (HA1id : forall g, In g (flat_map snd R1) -> ST.g_id g = 3%nat).
      { intros g Hg. apply in_flat_map in Hg as (x & Hx & Hg). apply in_map_iff in Hx as (sc & <- & _). exact (r1_ids kn sc g Hg). }
      assert (HF2 : know_ok segs E m (flat_map (r2_read segs kn src) path))
        by (apply Forall_flat_map'; intros x Hx; exact (r2_sound kn x HK Hx)).
      set (kn0 := flat_map (byte_facts segs kn) path ++ flat_map swar_facts path ++ kn).
      assert (HK0 : know_ok segs E m kn0).
      { apply Forall_app. split; [apply Forall_flat_map'; intros x _; exact (byte_facts_sound kn x HK)|].
        apply Forall_app. split; [apply Forall_flat_map'; intros x Hx; exact (swar_sound x Hx) | exact HK]. }
      assert (HF3 : know_ok segs E m (flat_map (r3_read segs MF kn0 B L) path ++ flat_map (fill_facts segs kn0) path)).
      { apply Forall_app. split; apply Forall_flat_map'; intros x Hx; [exact (r3_sound kn0 x HK0 Hx) | exact (fill_sound kn0 x HK0 Hx)]. }
      assert (HF14 : know_ok segs E m (flat_map (r14_read segs kn src) path))
        by (apply Forall_flat_map'; intros x Hx; exact (r14_sound kn x HK Hx)).
      set (kn1 := F6 ++ flat_map fst R1 ++ flat_map (r2_read segs kn src) path ++ (flat_map (r3_read segs MF kn0 B L) path ++ flat_map (fill_facts segs kn0) path) ++ flat_map (r14_read segs kn src) path ++ kn0).
      assert (HK1 : know_ok segs E m kn1).
      { apply Forall_app. split; [exact HF6|]. apply Forall_app. split; [exact HF1|]. apply Forall_app. split; [exact HF2|].
        apply Forall_app. split; [exact HF3|]. apply Forall_app. split; [exact HF14 | exact HK0]. }
      set (toks := atoms_of 3 src ++ map ST.g_args (flat_map snd R1)).
      assert (HT : forall a, In a toks -> tok_holds a).
      { intros a Ha. apply in_app_or in Ha as [Ha|Ha].
        - exact (src_holds 3 a (atoms_of_in _ _ _ Ha)).
        - apply in_map_iff in Ha as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) (HA1 m) g Hg) as G.
          cbv beta in G. rewrite (HA1id g Hg) in G. exact G. }
      set (kn2a := flat_map (r4_tok segs MF kn1 NN L) toks ++ kn1).
      assert (HK2a : know_ok segs E m kn2a).
      { apply Forall_app. split; [|exact HK1]. apply Forall_flat_map'. intros a Ha. exact (r4_sound kn1 a HK1 (HT a Ha)). }
      set (kn2 := flat_map (fun s => fst (r1_read segs MF kn2a X NN L s)) path ++ kn2a).
      assert (HK2 : know_ok segs E m kn2).
      { apply Forall_app. split; [|exact HK2a]. apply Forall_flat_map'. intros sc Hin. exact (proj1 (r1_sound kn2a sc HK2a Hin)). }
      set (A5 := flat_map (r5_tok segs MF kn2 NN) toks).
      assert (HA5 : forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) A5)
        by (intros M; apply Forall_flat_map'; intros a Ha; exact (r5_sound kn2 a HK2 (HT a Ha) M)).
      assert (HA5id : forall g, In g A5 -> ST.g_id g = 4%nat).
      { intros g Hg. apply in_flat_map in Hg as (a & _ & Hg). exact (r5_ids kn2 a g Hg). }
      set (SX := map (sexit segs MF kn2 path) (atoms_of 0 src)).
      assert (HSX : forall x, In x SX -> know_ok segs E m (fst x) /\
                     forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd x)).
      { intros x Hx. apply in_map_iff in Hx as (a & <- & Ha). exact (sexit_sound kn2 a HK2 (src_holds 0 a (atoms_of_in _ _ _ Ha))). }
      assert (HSXA : forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (flat_map snd SX))
        by (intros M; apply Forall_flat_map'; intros x Hx; exact (proj2 (HSX x Hx) M)).
      assert (HSXid : forall g, In g (flat_map snd SX) -> ST.g_id g = 4%nat).
      { intros g Hg. apply in_flat_map in Hg as (x & Hx & Hg). apply in_map_iff in Hx as (a & <- & _). exact (sexit_ids kn2 a g Hg). }
      assert (HG : Forall ge_holds (atoms_of 4 src ++ map ST.g_args A5 ++ map ST.g_args (flat_map snd SX))).
      { apply Forall_forall. intros a Ha. apply in_app_or in Ha as [Ha|Ha]; [|apply in_app_or in Ha as [Ha|Ha]].
        - exact (src_holds 4 a (atoms_of_in _ _ _ Ha)).
        - apply in_map_iff in Ha as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) (HA5 m) g Hg) as G.
          cbv beta in G. rewrite (HA5id g Hg) in G. exact G.
        - apply in_map_iff in Ha as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) (HSXA m) g Hg) as G.
          cbv beta in G. rewrite (HSXid g Hg) in G. exact G. }
      assert (HGS : Forall (fun a => GP 7 (map (edenot E) a) m) (atoms_of 7 src)).
      { apply Forall_forall. intros a Ha. exact (src_holds 7 a (atoms_of_in _ _ _ Ha)). }
      assert (HF8 : know_ok segs E m (str_facts segs MF TD kn2 path (SG.vc_log c) src toks (SG.vc_tgt c))).
      { unfold str_facts. apply Forall_flat_map'. intros g _.
        destruct (ST.g_args g) as [|B' [|L' [|P' [|KO' [|? ?]]]]] eqn:Hg; try constructor.
        destruct (str_tgt_ok segs MF TD kn2 path (SG.vc_log c) src toks g) eqn:C; [|constructor].
        destruct (str_tgt_sound kn2 toks g HK2 HL HT C) as [_ R]. specialize (R B' L' P' KO' Hg).
        constructor; [|constructor]. cbn [kentry_ok]. rewrite u_esub2. rewrite Z.mod_small by lia. lia. }
      split.
      - apply Forall_app. split; [exact HF8|]. apply Forall_app. split; [apply Forall_flat_map'; intros x Hx; exact (proj1 (HSX x Hx))|].
        apply Forall_app. split; [|exact HK2]. apply Forall_flat_map'. intros a Ha. exact (link_sound kn2 L _ _ a HK2 (HT a Ha) HG HGS).
      - intros M. apply Forall_app. split; [exact (HA1 M)|]. apply Forall_app. split; [exact (HA5 M)|].
        apply Forall_app. split; [exact (HSXA M)|].
        apply Forall_flat_map'. intros a Ha. exact (gnum1_sound kn2 a HK2 (src_holds 3 a (atoms_of_in _ _ _ Ha)) M).
    Qed.

    (* [comment removed for export] *)
    Lemma cell_ok_sound : forall kn lg OC' D' BW' a, know_ok segs E m kn -> log_flat E lg ->
      cell_ok segs kn lg OC' D' BW' a = true ->
      exists t, 0 <= t /\ 8 * t < u (edenot E BW') /\ mcell (mem_denot E m lg) (u (edenot E a)) 4 t.
    Proof.
      intros kn lg OC' D' BW' a HKn HL H. unfold cell_ok in H.
      destruct (newest kn a lg) as [[sx pre]|] eqn:Hn; [|discriminate].
      repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
      match goal with H2 : kimp _ _ (KRange (esub2 _ _) _ _) = true, H3 : SG.log_apart _ _ _ = true |- _ =>
        rename H2 into C2; rename H3 into C3 end.
      destruct (newest_split kn a lg sx pre Hn) as (rest & -> & Hw & Ha).
      pose proof (same_addr_den segs E m kn _ _ HKn Ha) as HA.
      destruct sx as [sa sw sv]. cbn [e_width e_addr e_val] in *. subst sw.
      pose proof (kimp_range segs E m kn _ _ _ HKn H) as R1.
      set (t := u (edenot E sv)) in *.
      assert (R2 : 1 <= u (edenot E BW') - 8 * t <= 2 ^ 62).
      { pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R. rewrite u_esub2, u_emul' in R. fold t in R.
        rewrite (Z.mod_small 8) in R by lia. rewrite (Z.mod_small (8 * t)) in R by lia.
        apply sub_exact; [apply u_rng | lia | lia | lia | exact R]. }
      exists t. split; [lia|]. split; [lia|].
      apply log_flat_app in HL as [HLp HLs]. cbn [log_flat] in HLs. destruct HLs as (_ & Hfa & _).
      pose proof (flat_u E _ _ Hfa) as Hu. destruct Hfa as (Hf0 & Hf1 & _ & Hf3).
      assert (UA : u (edenot E a) = u (adenot E sa)).
      { rewrite <- HA. rewrite u_eaddl. unfold adenot, v_addi. rewrite u_litm. rewrite Z.add_mod_idemp_r by lia. reflexivity. }
      unfold estart in Hu, Hf3. rewrite <- Hu in Hf3. rewrite <- UA in Hf3.
      intros i Hi. rewrite length_Z_to_le_bytes in Hi.
      rewrite mem_denot_app. rewrite (mem_denot_apart_gen segs E m kn pre [(a, 0, ELit 4)] HKn HLp C3).
      2:{ exists (a, 0, ELit 4). split; [left; reflexivity|]. cbn [SG.win_den]. pose proof (u_rng (edenot E a)).
          rewrite edenot_lit. rewrite !u_lit by lia. lia. }
      cbn [mem_denot]. rewrite UA. replace (Z.to_nat i) with (Z.to_nat i) by reflexivity.
      replace (u (adenot E sa) + i) with (u (adenot E sa) + Z.of_nat (Z.to_nat i)) by lia.
      rewrite wbytes_nth.
      - unfold word_to_le_bytes. fold t. reflexivity.
      - rewrite length_N_to_le_bytes. lia.
      - rewrite length_N_to_le_bytes. lia.
    Qed.

    Lemma goc_sound : forall kn lg g, know_ok segs E m kn -> log_flat E lg -> goc_ok segs kn lg (SG.vc_src c) g = true ->
      GP (ST.g_id g) (map (edenot E) (ST.g_args g)) (mem_denot E m lg).
    Proof.
      intros kn lg [gid gargs] HKn HL H. unfold goc_ok in H. cbn [ST.g_id ST.g_args] in *.
      destruct gid as [|[|[|[|[|[|gid]]]]]]; try discriminate.
      destruct gargs as [|OC' [|D' [|BW' [|? ?]]]]; try discriminate.
      repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
      rename H into C1. match goal with H2 : kimp _ _ (KRange D' _ _) = true, H3 : kimp _ _ (KRange BW' _ _) = true,
        H4 : (_ || _)%bool = true |- _ => rename H2 into C2; rename H3 into C3; rename H4 into C4 end.
      pose proof (kimp_range segs E m kn _ _ _ HKn C1) as R1. pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R2.
      pose proof (kimp_range segs E m kn _ _ _ HKn C3) as R3.
      cbn [map gp2]. split; [lia|].
      apply orb_prop in C4 as [C4|C4].
      - (* [comment removed for export] *)
        apply andb_prop in C4 as [C5 C6]. rewrite (leq_den E D' (ELit 0) C5), edenot_lit, u_lit by lia.
        intros i Hi. replace i with 0 by lia. rewrite Z.mul_0_r, Z.add_0_r.
        exact (cell_ok_sound kn lg OC' D' BW' OC' HKn HL C6).
      - apply existsb_exists in C4 as (args & Ha & C4).
        destruct args as [|OC [|D [|BW [|? ?]]]]; try discriminate.
        repeat match type of C4 with (_ && _)%bool = true => apply andb_prop in C4; destruct C4 as [C4 ?] end.
        match goal with H2 : kimp _ _ (KRange D _ _) = true, H3 : kimp _ _ (KRange BW _ _) = true,
          H4 : kimp _ _ (KRange (esub2 BW' BW) _ _) = true, H5 : (_ || _)%bool = true |- _ =>
          rename H2 into C6; rename H3 into C7; rename H4 into C8; rename H5 into C9 end.
        pose proof (kimp_range segs E m kn _ _ _ HKn C6) as R6. pose proof (kimp_range segs E m kn _ _ _ HKn C7) as R7.
        assert (R8 : 0 <= u (edenot E BW') - u (edenot E BW) <= 2 ^ 62) by (apply (kimp_sub segs E m kn _ _ _ _ HKn C8); lia).
        pose proof (src_holds 5 [OC; D; BW] (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. destruct G as (Gb & Gc).
        rewrite (leq_den E OC OC' C4) in Gb, Gc.
        (* [comment removed for export] *)
        assert (OLD : forall dd, 0 <= u (edenot E dd) <= 1023 -> SG.log_apart kn lg [(OC', 0, eaddl (emul 8 dd) 4)] = true ->
                      forall i, 0 <= i <= u (edenot E dd) -> i <= u (edenot E D) ->
                      exists t, 0 <= t /\ 8 * t < u (edenot E BW') /\ mcell (mem_denot E m lg) (u (edenot E OC') + 8 * i) 4 t).
        { intros dd Hdd Hap i Hi HiD. destruct (Gc i ltac:(lia)) as (t & Ht0 & Ht & Hm). exists t. split; [lia|]. split; [lia|].
          intros k Hk. rewrite length_Z_to_le_bytes in Hk.
          rewrite (mem_denot_apart_gen segs E m kn lg _ HKn HL Hap m).
          - exact (Hm k ltac:(rewrite length_Z_to_le_bytes; lia)).
          - exists (OC', 0, eaddl (emul 8 dd) 4). split; [left; reflexivity|]. cbn [SG.win_den].
            rewrite u_eaddl, u_emul'. rewrite (Z.mod_small 8), (Z.mod_small 4) by lia. rewrite (Z.mod_small (8 * _)) by lia.
            rewrite Z.mod_small by lia. rewrite u_lit by lia. lia. }
        apply orb_prop in C9 as [C9|C9].
        + (* [comment removed for export] *)
          apply andb_prop in C9 as [C10 C11].
          assert (R10 : 0 <= u (edenot E D) - u (edenot E D') <= 1023) by (apply (kimp_sub segs E m kn _ _ _ _ HKn C10); lia).
          intros i Hi. exact (OLD D' ltac:(lia) C11 i Hi ltac:(lia)).
        + (* [comment removed for export] *)
          repeat match type of C9 with (_ && _)%bool = true => apply andb_prop in C9; destruct C9 as [C9 ?] end.
          match goal with H2 : SG.log_apart _ _ _ = true, H3 : cell_ok _ _ _ _ _ _ _ = true |- _ =>
            rename H2 into C11; rename H3 into C12 end.
          pose proof (leq_den E D' (eaddl D 1) C9) as ED. assert (UD : u (edenot E D') = u (edenot E D) + 1).
          { rewrite ED, u_eaddl. rewrite (Z.mod_small 1) by lia. apply Z.mod_small. lia. }
          intros i Hi. destruct (Z_le_gt_dec i (u (edenot E D))) as [Le|Gt].
          * exact (OLD D ltac:(lia) C11 i ltac:(lia) Le).
          * destruct (cell_ok_sound kn lg OC' D' BW' _ HKn HL C12) as (t & Ht0 & Ht & Hm). exists t. split; [lia|]. split; [lia|].
            replace i with (u (edenot E D')) by lia.
            replace (u (edenot E OC') + 8 * u (edenot E D')) with (u (edenot E (EAlu ALU_ADD OC' (emul 8 D')))); [exact Hm|].
            rewrite u_add_gen, u_emul'. rewrite (Z.mod_small 8) by lia. rewrite (Z.mod_small (8 * _)) by lia.
            apply Z.mod_small. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma gesrc_holds : forall A, (forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) A) ->
      forall args, In args (ge_src (SG.vc_src c) A) -> exists K' E', args = [K'; E'] /\ u (edenot E K') mod 4 = 0 /\
        u (edenot E K') / 4 <= n + 2 /\ u (edenot E E') <= znth idxs (u (edenot E K') / 4).
    Proof.
      intros A HA args Hin. unfold ge_src in Hin. repeat (apply in_app_or in Hin as [Hin|Hin]).
      - pose proof (src_holds 4 args (atoms_of_in _ _ _ Hin)) as G.
        destruct args as [|K' [|E' [|? ?]]]; try (cbn in G; contradiction). exists K', E'. split; [reflexivity|]. exact G.
      - pose proof (proj1 (Forall_forall _ _) (HA m) _ (atoms_of_in _ _ _ Hin)) as G. cbv beta in G. cbn [ST.g_id ST.g_args] in G.
        destruct args as [|K' [|E' [|? ?]]]; try (cbn in G; contradiction). exists K', E'. split; [reflexivity|]. exact G.
      - pose proof (src_holds 3 args (atoms_of_in _ _ _ Hin)) as G.
        destruct args as [|K' [|E' [|? ?]]]; try (cbn in G; contradiction). exists K', E'. split; [reflexivity|].
        cbn [map gp2] in G. destruct G as (G1 & G2 & G3). split; [exact G1|]. split; [exact G2|]. lia.
      - pose proof (proj1 (Forall_forall _ _) (HA m) _ (atoms_of_in _ _ _ Hin)) as G. cbv beta in G. cbn [ST.g_id ST.g_args] in G.
        destruct args as [|K' [|E' [|? ?]]]; try (cbn in G; contradiction). exists K', E'. split; [reflexivity|].
        cbn [map gp2] in G. destruct G as (G1 & G2 & G3). split; [exact G1|]. split; [exact G2|]. lia.
    Qed.

    Lemma tgt_pure_sound : forall kn A g, know_ok segs E m kn ->
      (forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) A) ->
      tgt_pure_ok segs kn (SG.vc_src c) A g = true -> forall M, GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M.
    Proof.
      intros kn A [gid gargs] HKn HA H M. unfold tgt_pure_ok in H. cbn [ST.g_id ST.g_args] in *.
      destruct gid as [|[|[|[|[|[|[|[|[|[|gid]]]]]]]]]]; try discriminate.
      - (* [comment removed for export] *)
        destruct gargs as [|K [|V [|? ?]]]; try discriminate.
        apply existsb_exists in H as (args & Ha & C). destruct args as [|K' [|V' [|? ?]]]; try discriminate.
        apply andb_prop in C as [C1 C2]. pose proof (proj1 (Forall_forall _ _) (HA M) _ (atoms_of_in _ _ _ Ha)) as G.
        cbv beta in G. cbn [ST.g_id ST.g_args map] in G |- *. rewrite (leq_den E K K' C1), (leq_den E V V' C2). exact G.
      - (* [comment removed for export] *)
        destruct gargs as [|K [|E0 [|? ?]]]; try discriminate.
        apply existsb_exists in H as (args & Ha & C).
        destruct (gesrc_holds A HA args Ha) as (K' & E' & -> & G1 & G2 & G3).
        repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
        match goal with H1 : kimp _ _ (KRange E0 _ _) = true, H2 : kimp _ _ (KRange E' _ _) = true,
          H3 : kimp _ _ (KRange (esub2 _ _) _ _) = true |- _ =>
          pose proof (kimp_range segs E m kn _ _ _ HKn H1); pose proof (kimp_range segs E m kn _ _ _ HKn H2);
          pose proof (kimp_sub segs E m kn _ _ _ _ HKn H3) end.
        cbn [map gp2]. rewrite (leq_den E K K' C). unfold BIGS in *. split; [exact G1|]. split; [exact G2|]. lia.
      - (* [comment removed for export] *)
        destruct gargs as [|K [|OL [|C' r]]]; try discriminate. destruct C' as [cc| | | | | | |]; try discriminate.
        destruct r; try discriminate.
        repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
        match goal with H1 : Z.leb cc 16 = true, H2 : kimp _ _ (KRange OL _ _) = true, H3 : (_ || _)%bool = true |- _ =>
          apply Z.leb_le in H1; pose proof (kimp_range segs E m kn _ _ _ HKn H2) as ROL; rename H3 into C end.
        apply Z.leb_le in H. unfold BIGS in *. cbn [map gp2]. rewrite edenot_lit, u_lit by lia.
        apply orb_prop in C as [C|C].
        + apply existsb_exists in C as (args & Ha & C).
          destruct (gesrc_holds A HA args Ha) as (K' & E' & -> & G1 & G2 & G3).
          apply andb_prop in C as [C C2]. apply andb_prop in C as [C C1].
          pose proof (kimp_range segs E m kn _ _ _ HKn C1) as RE.
          pose proof (kimp_range segs E m kn _ _ _ HKn C2) as R. rewrite u_esub2, u_eaddl, !u_emul' in R.
          rewrite (Z.mod_small 5), (Z.mod_small 3), (Z.mod_small cc) in R by lia.
          rewrite (Z.mod_small (5 * _)), (Z.mod_small (3 * _)) in R by lia. rewrite (Z.mod_small (3 * _ + cc)) in R by lia.
          assert (0 <= 5 * u (edenot E E') - (3 * u (edenot E OL) + cc) <= 2 ^ 40) by (apply sub_exact; lia).
          rewrite (leq_den E K K' C). split; [exact G1|]. split; [exact G2|]. lia.
        + apply existsb_exists in C as (args & Ha & C).
          destruct args as [|K' [|OL' [|C'' r']]]; try discriminate. destruct C'' as [cc'| | | | | | |]; try discriminate.
          destruct r'; try discriminate.
          repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
          match goal with H1 : Z.leb 0 cc' = true, H2 : Z.leb cc' 16 = true, H3 : kimp _ _ (KRange OL' _ _) = true,
            H4 : kimp _ _ (KRange (esub2 _ _) _ _) = true |- _ =>
            apply Z.leb_le in H1; apply Z.leb_le in H2; pose proof (kimp_range segs E m kn _ _ _ HKn H3) as ROL';
            pose proof (kimp_range segs E m kn _ _ _ HKn H4) as R end.
          rewrite u_esub2, !u_eaddl, !u_emul' in R. rewrite (Z.mod_small 3), (Z.mod_small cc), (Z.mod_small cc') in R by lia.
          rewrite !(Z.mod_small (3 * _)) in R by lia. rewrite (Z.mod_small (3 * u (edenot E OL') + cc')) in R by lia.
          rewrite (Z.mod_small (3 * u (edenot E OL) + cc)) in R by lia.
          assert (0 <= (3 * u (edenot E OL') + cc') - (3 * u (edenot E OL) + cc) <= 2 ^ 40) by (apply sub_exact; lia).
          pose proof (src_holds 7 _ (atoms_of_in _ _ _ Ha)) as G. cbn [map gp2] in G. rewrite edenot_lit, u_lit in G by lia.
          rewrite (leq_den E K K' C). destruct G as (G1 & G2 & G3). split; [exact G1|]. split; [exact G2|]. lia.
      - (* [comment removed for export] *)
        destruct gargs; [|discriminate]. apply existsb_exists in H as ([gi ga] & Ha & C). cbn [ST.g_id ST.g_args] in C.
        destruct gi as [|[|[|[|[|[|[|[|[|?]]]]]]]]]; try discriminate. destruct ga; [|discriminate].
        exact (proj1 (Forall_forall _ _) (HA M) _ Ha).
      - (* [comment removed for export] *)
        destruct gargs; [|discriminate]. apply existsb_exists in H as ([gi ga] & Ha & C). cbn [ST.g_id ST.g_args] in C.
        destruct gi as [|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]; try discriminate. destruct ga; [|discriminate].
        exact (proj1 (Forall_forall _ _) (HA M) _ Ha).
    Qed.
  End Ctx.

  Lemma derive_any : forall E m c, know_ok segs E m (SG.vc_kn c) -> scs_denot segs m E (SG.vc_path c) -> log_flat E (SG.vc_log c) ->
    SG.gholds GP E m (SG.vc_src c) ->
    know_ok segs E m (fst (derive segs MF TD c)) /\
    forall M, Forall (fun g => GP (ST.g_id g) (map (edenot E) (ST.g_args g)) M) (snd (derive segs MF TD c)).
  Proof.
    intros E m c HK HP HL HS.
    assert (DFLT : know_ok segs E m (flat_map (fun s => srl_facts segs (SG.vc_kn c) (e_val s)) (SG.vc_log c) ++ SG.vc_kn c)).
    { apply Forall_app. split; [|exact HK]. apply Forall_flat_map'. intros x _. apply srl_sound. exact HK. }
    destruct (find_atom 2 (SG.vc_src c)) as [a2|] eqn:HX;
    [destruct a2 as [|X [|NN [|? ?]]] | ];
    destruct (find_atom 1 (SG.vc_src c)) as [a1|] eqn:HB;
    try (destruct a1 as [|B [|L [|? ?]]]);
    try (unfold derive; cbv zeta; rewrite ?HX, ?HB; cbn [fst snd]; split; [exact DFLT | intros; constructor]).
    exact (derive_sound E m c HK HP HS X NN B L HX HB HL).
  Qed.

  (* [comment removed for export] *)
  Lemma room_sound : forall E m kn L K, know_ok segs E m kn -> room_ok segs MF kn L K = true -> kentry_ok segs E m K.
  Proof.
    intros E m kn L K HK H. unfold room_ok in H.
    destruct K as [| | | | |e lo hi| | | |]; try discriminate.
    destruct e as [| |op1 e1 e2| | | | |]; try discriminate. destruct op1; try discriminate.
    destruct e1 as [| |op2 CS OL| | | | |]; try discriminate. destruct op2; try discriminate.
    destruct e2 as [| |op3 L' VX| | | | |]; try discriminate. destruct op3; try discriminate.
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
    match goal with H1 : Z.leb lo 7 = true, H2 : Z.leb (2 ^ 40) hi = true, H3 : caps_ok _ _ _ = true,
      H4 : kimp _ _ (KRange L 0 MF) = true, H5 : kimp _ _ (KRange CS _ _) = true, H6 : kimp _ _ (KRange (esub2 L VX) _ _) = true,
      H7 : kimp _ _ (KRange OL _ _) = true, H8 : kimp _ _ (KRange (esub2 (emul 5 VX) _) _ _) = true,
      H9 : kimp _ _ (KRange VX 0 MF) = true |- _ => pose proof (kimp_range segs E m kn _ _ _ HK H9) as RVX;
      apply Z.leb_le in H1; apply Z.leb_le in H2; rename H3 into C3;
      pose proof (kimp_range segs E m kn _ _ _ HK H4) as RL; pose proof (kimp_range segs E m kn _ _ _ HK H5) as RC;
      pose proof (kimp_range segs E m kn _ _ _ HK H7) as RO; rename H6 into C6; rename H8 into C8 end.
    unfold BIGS in RO.
    assert (RV : 0 <= u (edenot E L) - u (edenot E VX) <= MF) by (apply (kimp_sub segs E m kn _ _ _ _ HK C6); lia).
    pose proof (u_rng (edenot E VX)).
    assert (R58 : 5 <= 5 * u (edenot E VX) - 3 * u (edenot E OL) <= 5 * MF).
    { pose proof (kimp_range segs E m kn _ _ _ HK C8) as R. rewrite u_esub2, !u_emul' in R.
      rewrite (Z.mod_small 5), (Z.mod_small 3) in R by lia. rewrite (Z.mod_small (5 * _)), (Z.mod_small (3 * _)) in R by lia.
      apply sub_exact; lia. }
    unfold caps_ok in C3. apply existsb_exists in C3 as (K' & HinK & C3).
    destruct K' as [| | | | |e' lo' hi'| | | |]; try discriminate.
    destruct e' as [| |o1 a1 b1| | | | |]; try discriminate. destruct o1; try discriminate.
    destruct a1 as [| | | |o2 x3 CS'| | |]; try discriminate. destruct o2; try discriminate.
    destruct x3 as [k3| | | | | | |]; try discriminate.
    destruct b1 as [| | | |o3 x5 L''| | |]; try discriminate. destruct o3; try discriminate.
    destruct x5 as [k5| | | | | | |]; try discriminate.
    repeat match type of C3 with (_ && _)%bool = true => apply andb_prop in C3; destruct C3 as [C3 ?] end.
    match goal with H1 : leq L'' L = true, H2 : Z.leb 182 lo' = true, H3 : Z.leb hi' (2 ^ 40) = true,
      H4 : Z.eqb k5 5 = true, H5 : expr_eqb CS' CS = true |- _ =>
      pose proof (leq_den E _ _ H1) as EL; apply Z.leb_le in H2; apply Z.leb_le in H3; apply Z.eqb_eq in H4;
      apply expr_eqb_eq in H5 end.
    apply Z.eqb_eq in C3. subst k3 k5 CS'.
    pose proof (proj1 (Forall_forall _ _) HK _ HinK) as RK. cbn [kentry_ok] in RK.
    change (edenot E (EAlu ALU_SUB (EMd M_MUL (ELit 3) CS) (EMd M_MUL (ELit 5) L''))) with (edenot E (esub2 (emul 3 CS) (emul 5 L''))) in RK.
    rewrite u_esub2, !u_emul', EL in RK. rewrite (Z.mod_small 3), (Z.mod_small 5) in RK by lia.
    rewrite (Z.mod_small (3 * _)), (Z.mod_small (5 * _)) in RK by lia.
    assert (RC3 : 182 <= 3 * u (edenot E CS) - 5 * u (edenot E L) <= 2 ^ 40) by (apply sub_exact; lia).
    cbn [kentry_ok].
    change (edenot E (EAlu ALU_SUB (EAlu ALU_SUB CS OL) (EAlu ALU_SUB L' VX))) with (edenot E (esub2 (esub2 CS OL) (esub2 L' VX))).
    rewrite !u_esub2. rewrite (leq_den E _ _ H).
    rewrite (Z.mod_small (u (edenot E CS) - _)) by lia. rewrite (Z.mod_small (u (edenot E L) - _)) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma pure_any : forall E M M' K, is_pure2 K = true -> kentry_ok segs E M K -> kentry_ok segs E M' K.
  Proof. intros E M M' K HP H. destruct K; try discriminate; exact H. Qed.

  (* [comment removed for export] *)
  Theorem wvc_ok_sound : forall c, wvc_ok segs MF TD c = true -> SG.vc_holds segs GP c.
  Proof.
    intros c H E m HK HP HL HS. unfold wvc_ok in H.
    pose proof (derive_any E m c HK HP HL HS) as [HD1 HD2].
    destruct (derive segs MF TD c) as [kn2 A] eqn:HD. cbn [fst snd] in HD1, HD2.
    apply andb_prop in H as [Ht Hf]. split.
    - unfold SG.gholds. apply Forall_forall. intros g Hg. pose proof (proj1 (forallb_forall _ _) Ht g Hg) as Hg1. cbv beta in Hg1.
      assert (SPLIT : (str_tgt_ok segs MF TD kn2 (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) (atoms_of 3 (SG.vc_src c) ++ atoms_of 3 A) g = true)
                      \/ goc_ok segs kn2 (SG.vc_log c) (SG.vc_src c) g = true \/ gia_ok segs kn2 (SG.vc_log c) (SG.vc_src c) g = true
                      \/ tgt_pure_ok segs kn2 (SG.vc_src c) A g = true \/ gd_ok segs MF kn2 (SG.vc_path c) (SG.vc_src c) g = true).
      { destruct (ST.g_id g) as [|[|[|[|[|[|[|[|[|[|[|[|[|gid]]]]]]]]]]]]] eqn:Hid;
          first [ left; exact Hg1 | right; left; exact Hg1 | right; right; left; exact Hg1
                | right; right; right; right; exact Hg1 | right; right; right; left; exact Hg1 ]. }
      destruct SPLIT as [G0|[G5|[G6|[GP0|G10]]]].
      + (* [comment removed for export] *)
        destruct (find_atom 2 (SG.vc_src c)) as [[|X [|NN [|? ?]]]|] eqn:HX;
          try (unfold str_tgt_ok in G0; rewrite HX in G0; destruct (ST.g_id g) as [|?]; [|discriminate];
               destruct (ST.g_args g) as [|? [|? [|? [|? [|? ?]]]]]; discriminate).
        destruct (find_atom 1 (SG.vc_src c)) as [[|B [|L [|? ?]]]|] eqn:HB;
          try (unfold str_tgt_ok in G0; rewrite HX, HB in G0; destruct (ST.g_id g) as [|?]; [|discriminate];
               destruct (ST.g_args g) as [|? [|? [|? [|? [|? ?]]]]]; discriminate).
        assert (HT : forall a, In a (atoms_of 3 (SG.vc_src c) ++ atoms_of 3 A) -> tok_holds E m a).
        { intros a Ha. apply in_app_or in Ha as [Ha|Ha].
          - exact (src_holds E m c HS 3 a (atoms_of_in _ _ _ Ha)).
          - pose proof (proj1 (Forall_forall _ _) (HD2 m) _ (atoms_of_in _ _ _ Ha)) as G. exact G. }
        eapply proj1. eapply str_tgt_sound; eassumption.
      + eapply goc_sound; [exact HS | exact HD1 | exact HL | exact G5].
      + eapply gia_sound; [exact HS | exact HD1 | exact HL | exact G6].
      + eapply tgt_pure_sound; [exact HS | exact HD1 | exact HD2 | exact GP0].
      + (* [comment removed for export] *)
        destruct (find_atom 1 (SG.vc_src c)) as [a1|] eqn:HB.
        2: { unfold gd_ok in G10. rewrite HB in G10. discriminate. }
        destruct a1 as [|B [|L [|? ?]]]; try (unfold gd_ok in G10; rewrite HB in G10; discriminate).
        eapply (gd_sound E m c); eassumption.
    - unfold know_ok. apply Forall_forall. intros K HKin. pose proof (proj1 (forallb_forall _ _) Hf K HKin) as HK1. cbv beta in HK1.
      destruct (is_unk K) eqn:Hu.
      + destruct K; try discriminate. apply (kentry_ok_unk_grows segs E m (mem_denot E m (SG.vc_log c)) _ _ (mem_denot_grows E m _)).
        exact (ST.kin_ok segs E m _ _ HK HK1).
      + apply andb_prop in HK1 as [HP2 HI]. apply (pure_any E m _ K HP2). apply orb_prop in HI as [HI|HI]; [apply orb_prop in HI as [HI|HI]|].
        * exact (kimp_ok segs E m kn2 K HD1 HI).
        * destruct (find_atom 1 (SG.vc_src c)) as [[|B [|L [|? ?]]]|]; try discriminate. exact (room_sound E m kn2 L K HD1 HI).
        * destruct (find_atom 1 (SG.vc_src c)) as [a1|] eqn:HB.
          2: { unfold gd_fact in HI. rewrite HB in HI. discriminate. }
          destruct a1 as [|B [|L [|? ?]]]; try (unfold gd_fact in HI; rewrite HB in HI; discriminate).
          eapply (gd_fact_sound E m c); eassumption.
  Qed.
End Sound.

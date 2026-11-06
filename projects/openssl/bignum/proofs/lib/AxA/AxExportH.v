(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require RzCPS.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxBytes AxMem AxZZ AxScan AxState AxSys AxAcct AxMeasure AxLz AxGrant AxFd AxModelRel AxSys2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section ExportH.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.

Let HM : MR segs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.
Let HLZ := mr_lz segs fs0 ρ (a_model B) model HM.

Definition pdn (z : Z) : Z := z / 4096 * 4096.
Definition pup (z : Z) : Z := (z + 4095) / 4096 * 4096.
Definition den_w (w : lin * Z) : Z * Z := (pdn (leval ρ (fst w)), pup (leval ρ (fst w) + snd w)).
Definition A' : list (Z * Z) := (- J, 0) :: map den_w W.

Definition w_ok (w : lin * Z) : bool := (0 <=? snd w).

Lemma pdn_spec (z : Z) : pdn z <= z /\ pdn z mod 4096 = 0.
Proof. unfold pdn. split; [rewrite Z.mul_comm; apply Z.mul_div_le; lia | apply Z_mod_mult]. Qed.
Lemma pup_spec (z : Z) : z <= pup z /\ pup z mod 4096 = 0 /\ pup z <= z + 4095.
Proof.
  unfold pup. pose proof (Z.div_mod (z + 4095) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (z + 4095) 4096 ltac:(lia)) as M.
  split; [lia|]. split; [apply Z_mod_mult | lia].
Qed.

Lemma w_ok_spec (w : lin * Z) : w_ok w = true -> 0 <= snd w.
Proof. unfold w_ok. intros H. apply Z.leb_le. exact H. Qed.

Theorem A_wf_A' : 0 <= J -> J mod 4096 = 0 -> forallb w_ok W = true -> A_wf A'.
Proof.
  intros HJ HJa HW. unfold A_wf, A'. constructor.
  - cbn [fst snd]. unfold page_size. split; [lia|]. split; [|reflexivity].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in HJa; [|lia]. destruct HJa as [k ->]. exists (- k). lia.
  - apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as [w [<- Hw]]. rewrite forallb_forall in HW.
    pose proof (w_ok_spec w (HW w Hw)) as A2. unfold den_w, page_size. cbn [fst snd].
    destruct (pdn_spec (leval ρ (fst w))) as [P1 P2]. destruct (pup_spec (leval ρ (fst w) + snd w)) as (Q1 & Q2 & _).
    split; [lia|]. split; [exact P2 | exact Q2].
Qed.

Lemma u_wz' (z : Z) : 0 <= z < 2 ^ 47 -> bv_unsigned (wz z) = z.
Proof. intros H. apply u_wz. lia. Qed.

Lemma allowed_win (w : lin * Z) (a : word) : In w W -> w_ok w = true ->
  leval ρ (fst w) <= bv_unsigned a < leval ρ (fst w) + snd w -> page_allowedb A' (page_base a) = true.
Proof.
  intros Hw Hok Ha. destruct (pdn_spec (leval ρ (fst w))) as [A0 A1]. destruct (pup_spec (leval ρ (fst w) + snd w)) as (B0 & Ah & _).
  destruct (page_in_aligned a (pdn (leval ρ (fst w))) (pup (leval ρ (fst w) + snd w)) A1 Ah ltac:(lia)) as [P1 P2].
  unfold page_allowedb, A'. cbn [existsb]. apply orb_true_iff. right. apply existsb_exists. exists (den_w w).
  split; [apply in_map; exact Hw|]. unfold den_w, page_size. cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Theorem vis_win (w : lin * Z) (z : Z) : In w W -> w_ok w = true -> 0 <= z < 2 ^ 47 ->
  leval ρ (fst w) <= z < leval ρ (fst w) + snd w -> RzCPS.HID A' model (wz z) = false.
Proof.
  intros Hw Hok Hz Hin. unfold RzCPS.HID, mkH. rewrite (allowed_win w (wz z) Hw Hok) by (rewrite (u_wz' z Hz); exact Hin).
  rewrite andb_false_r. cbn [orb]. apply Z.leb_gt. rewrite (u_wz' z Hz). lia.
Qed.

Lemma lazy_in_big (a : word) : page_in_ranges (page_base a) (m_vm_lazy model) = true ->
  exists e, In e (am_maps (a_model B)) /\ BIGMIN <= ae_size e /\ ent_lo ρ e <= bv_unsigned a < ent_hi ρ e.
Proof.
  intros H. apply pir_spec in H as [q [Hq [Q1 Q2]]]. destruct HLZ as (Z1 & _ & _ & Z6).
  pose proof (proj1 (proj1 (Forall_forall _ _) Z6 q Hq)) as Hpos. destruct (Z1 q Hq Hpos) as (e & He & Hb & E1 & E2).
  exists e. split; [exact He|]. split; [exact Hb|]. rewrite page_base_val in Q1, Q2.
  pose proof (Z.mul_div_le (bv_unsigned a) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)) as D2.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as D3. lia.
Qed.

Theorem vis_notbig (z : Z) : 0 <= z < 2 ^ 47 ->
  (forall e, In e (am_maps (a_model B)) -> BIGMIN <= ae_size e -> ~ (ent_lo ρ e <= z < ent_hi ρ e)) ->
  RzCPS.HID A' model (wz z) = false.
Proof.
  intros Hz Hnb. unfold RzCPS.HID, mkH. destruct (page_in_ranges (page_base (wz z)) (m_vm_lazy model)) eqn:E.
  - exfalso. destruct (lazy_in_big (wz z) E) as (e & He & Hb & Hin). rewrite (u_wz' z Hz) in Hin. exact (Hnb e He Hb Hin).
  - cbn [andb orb]. apply Z.leb_gt. rewrite (u_wz' z Hz). lia.
Qed.

Definition has_win (f : lin) (n : Z) : bool := existsb (fun w => lin_eqb (fst w) f && (snd w =? n) && w_ok w) W.

Lemma has_win_spec (f : lin) (n : Z) : has_win f n = true -> exists w, In w W /\ w_ok w = true /\ fst w = f /\ snd w = n.
Proof.
  unfold has_win. intros H. apply existsb_exists in H as [w [Hw Hb]]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  exists w. split; [exact Hw|]. split; [exact H3|]. split; [exact (lin_eqb_eq _ _ H1) | apply Z.eqb_eq; exact H2].
Qed.

Definition has_lit_cover (lo n : Z) : bool :=
  existsb (fun w => match snd (fst w) with [] => (fst (fst w) <=? lo) && (lo + n <=? fst (fst w) + snd w) && w_ok w | _ => false end) W.

Lemma has_lit_cover_spec (lo n : Z) : has_lit_cover lo n = true ->
  exists w, In w W /\ w_ok w = true /\ leval ρ (fst w) <= lo /\ lo + n <= leval ρ (fst w) + snd w.
Proof.
  unfold has_lit_cover. intros H. apply existsb_exists in H as [w [Hw Hb]]. destruct w as [[c ts] nw]. cbn [fst snd] in Hb.
  destruct ts; [|discriminate Hb]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists ((c, []), nw). split; [exact Hw|]. split; [exact H3|]. unfold leval. cbn [fst snd teval]. lia.
Qed.

Definition sh_reg_ok (R : region) : bool :=
  negb (is_shadow R) ||| iall cell_is0 (rg_cells R)
  ||| (has_win (wZ (rg_bo R), rg_ts R) (to_Z (rg_n R))
       &&& match lrange (a_facts B) (wZ (rg_bo R), rg_ts R) with Some (lo, hi) => (0 <=? lo) &&& (hi <? 18446744073709551616) | None => false end).

Definition ent_hz_ok (e : aent) : bool :=
  (ae_size e <? BIGMIN) ||| lzfull e
  ||| (if ae_na e then forallb (fun x => negb (aent_eqb (fst (fst x)) e) ||| has_win (snd (fst x)) (snd x)) (am_exp (a_model B))
       else has_win (ae_base e) (ae_size e)).

Definition hz_ok : bool :=
  forallb ent_hz_ok (am_maps (a_model B)) &&& forallb sh_reg_ok (a_mem B)
  &&& forallb (fun R => (0 <? to_Z (rg_n R))) (a_mem B)
  &&& has_lit_cover sh_lo 4096
  &&& has_wit (a_facts B) ls_beg ls_end (a_mem B) &&& has_wit (a_facts B) hs_beg hs_hi (a_mem B).

Lemma in_exp_dec (e : aent) (z : Z) : in_exp ρ (am_exp (a_model B)) e z \/ ~ in_exp ρ (am_exp (a_model B)) e z.
Proof.
  unfold in_exp. induction (am_exp (a_model B)) as [|x l IH].
  - right. intros [y [Hy _]]. destruct Hy.
  - destruct IH as [[y [Hy Hp]]|IH]; [left; exists y; split; [right; exact Hy | exact Hp]|].
    assert (Hx : (fst (fst x) = e /\ leval ρ (snd (fst x)) <= z < leval ρ (snd (fst x)) + snd x)
                 \/ ~ (fst (fst x) = e /\ leval ρ (snd (fst x)) <= z < leval ρ (snd (fst x)) + snd x)).
    { destruct (aent_eq_dec (fst (fst x)) e) as [E|E]; [|right; intros [X _]; exact (E X)].
      destruct (Z_le_dec (leval ρ (snd (fst x))) z) as [L1|L1]; [|right; intros [_ X]; lia].
      destruct (Z_lt_dec z (leval ρ (snd (fst x)) + snd x)) as [L2|L2]; [left; split; [exact E | lia] | right; intros [_ X]; lia]. }
    destruct Hx as [Hx|Hx]; [left; exists x; split; [left; reflexivity | exact Hx]|].
    right. intros [y [Hy Hp]]. destruct Hy as [Hy|Hy]; [subst y; exact (Hx Hp) | apply IH; exists y; split; assumption].
Qed.

Lemma rv_shadow (z : Z) (b : byte) : ls_beg <= z < 2 ^ 64 -> rv segs (ms_mem ms) (wz z) = Some b -> ms_mem ms (wz z) = Some b.
Proof.
  intros Hz H. unfold rv in H. destruct (ms_mem ms (wz z)) as [b0|] eqn:E; [exact H|]. exfalso.
  destruct (seg_rom_in_segs segs (wz z) b H) as [sg [Hsg Hr]]. rewrite u_wz in Hr by (unfold ls_beg in Hz; lia). specialize (Hlow sg Hsg). lia.
Qed.

Theorem ex_HZ : hz_ok = true -> RzCPS.HZ A' (mkCfg ms model).
Proof.
  unfold hz_ok. intros H. apply andb_prop in H as [H HwH]. apply andb_prop in H as [H HwL]. apply andb_prop in H as [H Hpg].
  apply andb_prop in H as [H Hpos]. apply andb_prop in H as [Hents Hsh].
  rewrite forallb_forall in Hents, Hsh, Hpos.
  intros a Hh Hna. cbn [cfg_ms cfg_model] in *. unfold mkH in Hh. apply andb_prop in Hh as [Hlz Hnal]. apply negb_true_iff in Hnal.
  destruct (lazy_in_big a Hlz) as (e & He & Hbig & Hin).
  pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
  assert (Ea : wz (bv_unsigned a) = a) by (unfold wz; apply Z_to_bv_bv_unsigned).
  specialize (Hents e He). unfold ent_hz_ok in Hents.
  destruct (ae_size e <? BIGMIN) eqn:Eb; [apply Z.ltb_lt in Eb; lia|]. cbv iota in Hents.
  destruct (lzfull e) eqn:Ef.
  -
    clear Hents. destruct (lzfull_in_span ρ e Ef) as [S1 S2]. unfold ent_lo, ent_hi in Hin.
    destruct (Z_lt_le_dec (bv_unsigned a) ls_beg) as [L|L].
    { exfalso. destruct (has_lit_cover_spec _ _ Hpg) as (w & Hw & Hok & C1 & C2).
      rewrite (allowed_win w a Hw Hok) in Hnal; [discriminate Hnal|]. unfold sh_lo, ls_beg in *. lia. }
    assert (Hss : in_ss (bv_unsigned a)).
    { unfold in_ss. destruct (lzfull_cases e Ef) as [->| ->]; unfold leval, ls_ent, hs_ent in Hin; cbn [ae_base ae_size fst snd teval] in Hin;
        unfold ls_beg, ls_end, hs_beg, hs_hi in *; [left | right]; lia. }
    destruct (r_hs _ _ _ _ _ _ _ HR) as [[[R0 [HR0 Hz0]] _]|(_ & Hbg & HpL & HpH)]; cbn [cfg_ms] in *.
    { exfalso. specialize (Hpos R0 HR0). cbv beta in Hpos. apply Z.ltb_lt in Hpos. lia. }

    assert (Hcase : (exists C, In C (a_mem B) /\ is_shadow C = true /\ in_rg ρ C (bv_unsigned a))
                    \/ (forall C, In C (a_mem B) -> is_shadow C = true -> ~ in_rg ρ C (bv_unsigned a))).
    { clear - ρ. induction (a_mem B) as [|C l IH]; [right; intros C []|].
      destruct IH as [[C0 [H0 X]]|IH]; [left; exists C0; split; [right; exact H0 | exact X]|].
      destruct (is_shadow C) eqn:Es.
      - unfold in_rg. destruct (Z_le_dec (rbase ρ C) (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (rbase ρ C + to_Z (rg_n C))) as [L2|L2]|].
        + left. exists C. split; [left; reflexivity | split; [exact Es | lia]].
        + right. intros C0 [<-|H0] Hs0; [unfold in_rg; lia | exact (IH C0 H0 Hs0)].
        + right. intros C0 [<-|H0] Hs0; [unfold in_rg; lia | exact (IH C0 H0 Hs0)].
      - right. intros C0 [<-|H0] Hs0; [rewrite Es in Hs0; discriminate | exact (IH C0 H0 Hs0)]. }
    destruct Hcase as [[C [HC [HsC HinC]]]|Hout].
    +
      specialize (Hsh C HC). unfold sh_reg_ok in Hsh. rewrite HsC in Hsh. cbn [negb] in Hsh; cbv iota in Hsh.
      assert (HeC : is_entry C = false) by (unfold is_shadow, is_entry in *; destruct (rg_kind C); try reflexivity; discriminate HsC).
      pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok HF]. cbn [cfg_ms] in HF.
      pose proof (proj1 (Forall_forall _ _) HF C HC) as HRC. rewrite (RRegion_ne segs ρ _ C HeC) in HRC.
      destruct (regions_ok_in ρ _ C Hrok HC) as (W1 & W2 & _).
      unfold in_rg in HinC. set (y := of_Z (bv_unsigned a - rbase ρ C)).
      assert (Ey : to_Z y = bv_unsigned a - rbase ρ C) by (unfold y; apply phi_of_Z_small; lia).
      destruct (HRC y ltac:(lia)) as [[b [Hb Hx]] _]. replace (rbase ρ C + to_Z y) with (bv_unsigned a) in Hb by lia. rewrite Ea in Hb.
      destruct (iall cell_is0 (rg_cells C)) eqn:Ez.
      *
        assert (Hb0 : rbyte segs C y = BL 0%uint63).
        { unfold rbyte. unfold get_cell_opt. destruct (iget (rg_d C) (rg_cells C) (y >> 3)%uint63) as [c|] eqn:Eg.
          - apply (cell_is0_byte c _ (iall_iget cell_is0 _ _ _ c Ez Eg)). apply i2n_lt8.
          - unfold is_shadow in HsC. destruct (rg_kind C); try discriminate HsC. reflexivity. }
        rewrite Hb0 in Hx. unfold xb_bv in Hx. cbn [xb_z] in Hx. change (to_Z 0%uint63) with 0 in Hx.
        assert (b = Z_to_bv 8 0) by (rewrite <- Hx; symmetry; apply Z_to_bv_bv_unsigned). subst b.
        rewrite <- Ea. apply rv_shadow; [lia | rewrite Ea; exact Hb].
      * exfalso. cbv iota in Hsh. apply andb_prop in Hsh as [Hwin Hrng].
        destruct (has_win_spec _ _ Hwin) as (w & Hw & Hok & F1 & F2).
        destruct (lrange (a_facts B) (wZ (rg_bo C), rg_ts C)) as [[lo hi]|] eqn:El; [|discriminate Hrng].
        apply andb_prop in Hrng as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
        pose proof (lrange_sound ρ _ _ Hsat _ El) as X. cbn [fst snd] in X. unfold leval in X. cbn [fst snd] in X.
        rewrite (allowed_win w a Hw Hok) in Hnal; [discriminate Hnal|]. rewrite F1, F2. unfold leval. cbn [fst snd].
        unfold rbase, smod in HinC. rewrite Z.mod_small in HinC by (unfold FastWord.two64, AxAcct.two64 in *; lia). lia.
    +
      destruct (Hbg (bv_unsigned a) Hss Hout) as [Hn|Hz]; [|rewrite Ea in Hz; exact Hz]. exfalso. rewrite Ea in Hn.
      destruct Hss as [Hs|Hs].
      * destruct (has_wit_sound ρ _ ls_beg ls_end _ Hsat ltac:(unfold ls_beg; lia) ltac:(unfold ls_end, AxAcct.two64; lia) HwL) as (W0 & w0 & HW0 & Hs0 & Hin0 & Hr0).
        destruct HpL as [Hm|Hm]; [exact (Hm _ Hs ltac:(rewrite Ea; exact Hn))|].
        assert (HeW : is_entry W0 = false) by (unfold is_shadow, is_entry in *; destruct (rg_kind W0); try reflexivity; discriminate Hs0).
        pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok HF]. cbn [cfg_ms] in HF.
        pose proof (proj1 (Forall_forall _ _) HF W0 HW0) as HRW. rewrite (RRegion_ne segs ρ _ W0 HeW) in HRW.
        destruct (regions_ok_in ρ _ W0 Hrok HW0) as (V1 & V2 & _). unfold in_rg in Hin0.
        set (y := of_Z (w0 - rbase ρ W0)). assert (Ey : to_Z y = w0 - rbase ρ W0) by (unfold y; apply phi_of_Z_small; lia).
        destruct (HRW y ltac:(lia)) as [[b [Hb _]] _]. replace (rbase ρ W0 + to_Z y) with w0 in Hb by lia.
        pose proof (rv_shadow w0 b ltac:(unfold ls_end in *; lia) Hb) as Hb'. rewrite (Hm w0 Hr0) in Hb'. discriminate Hb'.
      * destruct (has_wit_sound ρ _ hs_beg hs_hi _ Hsat ltac:(unfold hs_beg; lia) ltac:(unfold hs_hi, AxAcct.two64; lia) HwH) as (W0 & w0 & HW0 & Hs0 & Hin0 & Hr0).
        destruct HpH as [Hm|Hm]; [exact (Hm _ Hs ltac:(rewrite Ea; exact Hn))|].
        assert (HeW : is_entry W0 = false) by (unfold is_shadow, is_entry in *; destruct (rg_kind W0); try reflexivity; discriminate Hs0).
        pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok HF]. cbn [cfg_ms] in HF.
        pose proof (proj1 (Forall_forall _ _) HF W0 HW0) as HRW. rewrite (RRegion_ne segs ρ _ W0 HeW) in HRW.
        destruct (regions_ok_in ρ _ W0 Hrok HW0) as (V1 & V2 & _). unfold in_rg in Hin0.
        set (y := of_Z (w0 - rbase ρ W0)). assert (Ey : to_Z y = w0 - rbase ρ W0) by (unfold y; apply phi_of_Z_small; lia).
        destruct (HRW y ltac:(lia)) as [[b [Hb _]] _]. replace (rbase ρ W0 + to_Z y) with w0 in Hb by lia.
        pose proof (rv_shadow w0 b ltac:(unfold hs_beg, ls_beg, hs_hi in *; lia) Hb) as Hb'. rewrite (Hm w0 Hr0) in Hb'. discriminate Hb'.
  - cbv iota in Hents. exfalso. destruct (ae_na e) eqn:Ena.
    +
      rewrite forallb_forall in Hents. destruct (in_exp_dec e (bv_unsigned a)) as [[x [Hx [Ex Hzx]]]|Hnx].
      * specialize (Hents x Hx). rewrite Ex, aent_eqb_refl in Hents. cbn [negb] in Hents; cbv iota in Hents.
        destruct (has_win_spec _ _ Hents) as (w & Hw & Hok & F1 & F2).
        rewrite (allowed_win w a Hw Hok) in Hnal; [discriminate Hnal | rewrite F1, F2; exact Hzx].
      * pose proof (mr_nacov segs fs0 ρ _ model HM e (bv_unsigned a) He Ena Hin Hnx) as [p [Hp Hap]].
        destruct HLZ as (_ & _ & Z4 & _). destruct (proj1 (Forall_forall _ _) Z4 p Hp) as (P1 & P2 & P3).
        assert (Ph : (bas p + bsz p) mod 4096 = 0) by (rewrite Z.add_mod, P2, P3 by lia; reflexivity).
        destruct (page_in_aligned a _ _ P2 Ph Hap) as [G1 G2].
        assert (X : page_in_ranges (page_base a) (vm_noaccess (m_vmmaps model)) = true) by (apply pir_spec; exists p; split; [exact Hp | lia]).
        rewrite X in Hna. discriminate Hna.
    +
      destruct (has_win_spec _ _ Hents) as (w & Hw & Hok & F1 & F2).
      rewrite (allowed_win w a Hw Hok) in Hnal; [discriminate Hnal | rewrite F1, F2; exact Hin].
Qed.

End ExportH.

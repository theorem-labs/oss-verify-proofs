(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanZeroWin.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffImage HandoffArgv R_depot_defs RT_state RT_init RT_init_mem RT_init_img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hg_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Definition kw8_in (k : list kentry) (b : expr) (o : Z) : bool :=
  existsb (fun K => match K with KWord (SA b' o') 8 _ => (expr_eqb b' b && Z.eqb o' o)%bool | _ => false end) k.

Definition kb16_in (k : list kentry) (b : expr) (o : Z) : bool :=
  existsb (fun K => match K with KBlob (SA b' o') (ELit 16) _ => (expr_eqb b' b && Z.eqb o' o)%bool | _ => false end) k.

Definition hs_stkwin_ok (ch : acs) : bool :=
  (kwr_cover (kn ch) e_sp0 (-8388608) 0 (S (length (kn ch)))
   && kw8_in (kn ch) e_sp0 0 && kw8_in (kn ch) e_sp0 8 && kw8_in (kn ch) e_sp0 16
   && forallb (fun j => kw8_in (kn ch) (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) (seq 0 20)
   && kb16_in (kn ch) (fst e_atrb) (snd e_atrb))%bool.

Lemma kw8_in_sound : forall k b o, kw8_in k b o = true -> exists v, In (KWord (SA b o) 8 v) k.
Proof.
  intros k b o H. unfold kw8_in in H. apply existsb_exists in H as (K & Hin & HK).
  destruct K as [a w v| | | | | | | | |]; try discriminate. destruct a as [b' o'].
  do 9 (destruct w as [|w]; try discriminate). apply andb_prop in HK as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst b' o'.
  exists v. exact Hin.
Qed.

Lemma kb16_in_sound : forall k b o, kb16_in k b o = true -> exists kk, In (KBlob (SA b o) (ELit 16) kk) k.
Proof.
  intros k b o H. unfold kb16_in in H. apply existsb_exists in H as (K & Hin & HK).
  destruct K as [| |a n kk| | | | | | |]; try discriminate. destruct a as [b' o']. destruct n as [z| | | | | | |]; try discriminate.
  destruct (Z.eq_dec z 16) as [->|Hz]; [|exfalso; destruct z as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate); apply Hz; reflexivity].
  apply andb_prop in HK as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst b' o'. exists kk. exact Hin.
Qed.

Lemma split_base_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= APS.uE E e -> APS.uE E b + k = APS.uE E e.
Proof.
  intros E e b k Hs Hk Hle. unfold APS.uE in *. rewrite (APS.split_lit_denot E e b k Hs) in Hle |- *.
  pose proof (PropExec.u64_range (edenot E b)) as Rb.
  rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
  destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
  - rewrite Z.mod_small by lia. reflexivity.
  - exfalso. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E b) + k) (2 ^ 64) ltac:(lia)) as MB.
    assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
    { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma e_auxv_vars : expr_vars_lt NX0 e_auxv = true /\ ev_only e_auxv = true. Proof. split; reflexivity. Qed.
Lemma e_atrandom_vars : expr_vars_lt NX0 e_atrandom = true /\ ev_only e_atrandom = true. Proof. split; reflexivity. Qed.
Lemma e_auxb_split : split_lit e_auxv = (fst e_auxb, snd e_auxb). Proof. unfold e_auxb. destruct (split_lit e_auxv); reflexivity. Qed.
Lemma e_atrb_split : split_lit e_atrandom = (fst e_atrb, snd e_atrb). Proof. unfold e_atrb. destruct (split_lit e_atrandom); reflexivity. Qed.
Lemma e_auxb_k : snd e_auxb = 24. Proof. vm_compute. reflexivity. Qed.
Lemma e_atrb_k : snd e_atrb = 184. Proof. vm_compute. reflexivity. Qed.

Section StkWin.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation E0 := (AsanInit.E0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation bsb := (build_stack_bytes ph sp argv envp uid hw rdraw).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation MR := (APS.Mr A argH E ch model FULL).

Let AH := ha_argH_high ph sp rdraw argv envp uid hw Hsp Hva.

Lemma sw_some : forall a b, CEIL <= a < 2 ^ 47 -> m (wa a) = Some b -> wview asegs m (wa a) <> None /\ exists b', mrd asegs m (wa a) = Some b'.
Proof. intros a b Ha Hm. unfold wview, mrd. rewrite Hm. split; [discriminate | exists b; reflexivity]. Qed.

Lemma sw_bytes : forall a0 bs a, bytes_at asegs m a0 bs -> CEIL <= a0 -> a0 + Z.of_nat (length bs) <= 2 ^ 47 -> a0 <= a < a0 + Z.of_nat (length bs) ->
  wview asegs m (wa a) <> None /\ exists b', mrd asegs m (wa a) = Some b'.
Proof.
  intros a0 bs a B Ha0 Hb Ha. pose proof (ha_wr A SEGS_in_hull HULL_ok FULL model A' a0 bs B Ha0 Hb) as (_ & _ & W).
  destruct B as (_ & _ & B3). specialize (W (a - a0) ltac:(lia)). replace (a0 + (a - a0)) with a in W by lia. split; [exact W|].
  specialize (B3 (Z.to_nat (a - a0)) ltac:(lia)). rewrite Z2Nat.id in B3 by lia. replace (a0 + (a - a0)) with a in B3 by lia.
  destruct (nth_error bs (Z.to_nat (a - a0))) as [b|] eqn:Hn; [exists b; exact B3 | apply nth_error_None in Hn; lia].
Qed.

Lemma sw_ptop : usp + Z.of_nat (length bsb) <= entry_page_top sp bsb /\ entry_page_top sp bsb mod 4096 = 0 /\ entry_page_top sp bsb <= 2 ^ 47.
Proof.
  destruct (ha_bsb ph sp rdraw argv envp uid hw Hfit) as (F1 & _).
  unfold entry_page_top, entry_block_top, page_round_up_Z, page_size.
  pose proof (Z.div_mod (usp + Z.of_nat (length bsb) + 4096 - 1) 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (usp + Z.of_nat (length bsb) + 4096 - 1) 4096 ltac:(lia)) as M.
  split; [lia|]. split; [apply Z.mod_mul; lia|].
  assert (Hq : (usp + Z.of_nat (length bsb) + 4096 - 1) / 4096 <= (2 ^ 47 + 4095) / 4096) by (apply Z.div_le_mono; lia).
  replace ((2 ^ 47 + 4095) / 4096) with (2 ^ 35) in Hq by reflexivity. lia.
Qed.

Lemma sw_usp : sp_window_lo <= usp <= sp_window_hi /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. destruct (ha_lens ph sp rdraw argv envp uid hw Hsp Hva Hve) as (L1 & L2 & L3). repeat split; lia. Qed.

Lemma sw_atop : alloc_top (m_vmmaps model) = usp - 8388608.
Proof.
  destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. unfold alloc_top, stack_max_size.
  rewrite I1, (ha_sp0 A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC). lia.
Qed.

Lemma sw_hidden : forall a, usp <= a < entry_page_top sp bsb -> argH E (wa a) = true ->
  wview asegs m (wa a) <> None /\ exists b', mrd asegs m (wa a) = Some b'.
Proof.
  intros a Ha HH. pose proof sw_ptop as (P1 & P2 & P3). pose proof sw_usp as ((U1 & U2) & _). unfold sp_window_lo in U1.
  assert (Hu : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (Hv : m (wa a) = FULL (wa a)).
  { apply (ha_visible A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC A'). rewrite Hu, sw_atop. lia. }
  rewrite (ha_block A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC (wa a) HH) in Hv.
  rewrite (wrap_above_sp ph sp argv envp (wa a) uid hw rdraw ltac:(rewrite Hu; lia)) in Hv.
  pose proof (entry_stack_image_top ph sp argv envp uid hw rdraw) as T.
  unfold stack_to_mem in Hv. rewrite Hu in Hv. rewrite (proj2 (Z.leb_le usp a)) in Hv by lia.
  rewrite (proj2 (Z.ltb_lt (a - usp) _)) in Hv by lia.
  destruct (nth_error (entry_stack_image ph sp argv envp uid hw rdraw) (Z.to_nat (a - usp))) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
  apply (sw_some a b); [unfold CEIL; lia | exact Hv].
Qed.

Lemma sw_uauxv : APS.uE E (fst e_auxb) + 24 = usp + 8 * argc + 8 * envc + 24.
Proof.
  pose proof sw_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof (ha_u A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC e_auxv (proj1 e_auxv_vars) (proj2 e_auxv_vars)) as U.
  rewrite (u_e_auxv ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) in U.
  pose proof (split_base_u E e_auxv (fst e_auxb) (snd e_auxb) e_auxb_split) as S. rewrite e_auxb_k in S. rewrite <- U. apply S; lia.
Qed.

Lemma sw_uatr : APS.uE E (fst e_atrb) + 184 = usp + Z.of_nat (length bsb) - 16.
Proof.
  pose proof sw_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof (bsb_ge ph sp rdraw argv envp uid hw) as (G & _).
  pose proof (ha_u A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC e_atrandom (proj1 e_atrandom_vars) (proj2 e_atrandom_vars)) as U.
  rewrite (u_e_atrandom ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) in U.
  pose proof (split_base_u E e_atrandom (fst e_atrb) (snd e_atrb) e_atrb_split) as S. rewrite e_atrb_k in S. rewrite <- U. apply S; lia.
Qed.

Lemma sw_visible : hs_stkwin_ok ch = true -> forall a, usp <= a < entry_page_top sp bsb -> argH E (wa a) = false ->
  wview asegs m (wa a) <> None /\ exists b', mrd asegs m (wa a) = Some b'.
Proof.
  intros HT a Ha HH. pose proof sw_ptop as (P1 & P2 & P3). pose proof sw_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3). pose proof (bsb_ge ph sp rdraw argv envp uid hw) as (G & _).
  destruct (ha_bsb ph sp rdraw argv envp uid hw Hfit) as (F1 & _).
  assert (Hu : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  unfold hs_stkwin_ok in HT. apply andb_prop in HT as [HT T6]. apply andb_prop in HT as [HT T5]. apply andb_prop in HT as [HT T4].
  apply andb_prop in HT as [HT T3]. apply andb_prop in HT as [_ T2].

  assert (Hc : a < usp + 24 \/ (usp + 8 * argc + 8 * envc + 24 <= a < usp + 8 * argc + 8 * envc + 184)
               \/ (usp + Z.of_nat (length bsb) - 16 <= a < usp + Z.of_nat (length bsb))).
  { unfold argH0, argH0_old in HH. cbv zeta in HH. rewrite Hu in HH.
    apply orb_false_iff in HH as [HH1 HH2]. apply orb_false_iff in HH1 as [H1 H2]. apply orb_false_iff in HH2 as [H3 H4].
    apply andb_false_iff in H1. apply andb_false_iff in H2. apply andb_false_iff in H3. apply andb_false_iff in H4.
    rewrite !Z.leb_gt, !Z.ltb_ge in *. lia. }
  assert (CE : CEIL <= usp) by (unfold CEIL; lia).
  destruct Hc as [C|[C|C]].
  -
    assert (Ho : exists o, (o = 0 \/ o = 8 \/ o = 16) /\ kw8_in (kn ch) e_sp0 o = true /\ usp + o <= a < usp + o + 8).
    { destruct (Z_lt_le_dec a (usp + 8)); [exists 0; split; [tauto|]; split; [exact T2 | lia]|].
      destruct (Z_lt_le_dec a (usp + 16)); [exists 8; split; [tauto|]; split; [exact T3 | lia]|]. exists 16. split; [tauto|]. split; [exact T4 | lia]. }
    destruct Ho as (o & Ho & Tk & Hr). destruct (kw8_in_sound _ _ _ Tk) as (v & Hin).
    pose proof (ha_kw A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok E ch R FULL model HC A' HA' o v Hin ltac:(lia)) as B.
    apply (sw_bytes (usp + o) (le8 (edenot E v)) a B); [lia | unfold le8; rewrite CatExec.length_N_to_le_bytes; lia | unfold le8; rewrite CatExec.length_N_to_le_bytes; lia].
  -
    set (j := Z.to_nat ((a - (usp + 8 * argc + 8 * envc + 24)) / 8)).
    assert (Hj : (j < 20)%nat /\ usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j <= a < usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j + 8).
    { unfold j. pose proof (Z.div_mod (a - (usp + 8 * argc + 8 * envc + 24)) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (a - (usp + 8 * argc + 8 * envc + 24)) 8 ltac:(lia)) as M.
      assert (0 <= (a - (usp + 8 * argc + 8 * envc + 24)) / 8 < 20) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite Z2Nat.id by lia. split; [lia | lia]. }
    destruct Hj as (Hj & Hr).
    pose proof (proj1 (forallb_forall _ _) T5 j ltac:(apply in_seq; lia)) as Tk. cbv beta in Tk.
    destruct (kw8_in_sound _ _ _ Tk) as (v & Hin).
    pose proof (hk_kword asegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok AH E ch R FULL model HC A' HA' _ 8%nat v Hin) as B.
    unfold estart in B. cbn [a_base a_off] in B. rewrite e_auxb_k in B. pose proof sw_uauxv as UA. unfold APS.uE in UA.
    replace (bv_unsigned (edenot E (fst e_auxb)) + (24 + 8 * Z.of_nat j)) with (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j) in B by lia.
    specialize (B ltac:(change (Z.of_nat 8) with 8; lia)).
    apply (sw_bytes _ _ a B); [lia | rewrite CatExec.length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia | rewrite CatExec.length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia].
  -
    destruct (kb16_in_sound _ _ _ T6) as (kk & Hin).
    destruct (hk_kentry asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC _ Hin) as (Hfl & Hlen & Hb).
    rewrite (APS.elenZ_lit E 16 ltac:(lia)) in Hb. unfold estart in Hb. cbn [a_base a_off] in Hb. rewrite e_atrb_k in Hb.
    pose proof sw_uatr as UA. unfold APS.uE in UA.
    specialize (Hb (a - (usp + Z.of_nat (length bsb) - 16)) ltac:(lia)).
    replace (bv_unsigned (edenot E (fst e_atrb)) + 184 + (a - (usp + Z.of_nat (length bsb) - 16))) with a in Hb by lia.
    fold (wa a) in Hb.
    assert (Hm : m (wa a) = MR (wa a)).
    { apply (hk_mr_some asegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA'); [rewrite Hb; discriminate | rewrite Hu; lia]. }
    rewrite Hb in Hm. exact (sw_some a _ ltac:(lia) Hm).
Qed.

Lemma sw_below : kwr_cover (kn ch) e_sp0 (-8388608) 0 (S (length (kn ch))) = true -> stk asegs m (usp - 8388608) usp.
Proof.
  intros H. pose proof sw_usp as ((U1 & U2) & _). unfold sp_window_lo, sp_window_hi in *.
  pose proof (ha_sp0 A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC) as US.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (kwr_cover_sound _ _ _ _ _ H (a - usp) ltac:(lia)) as (o & n & Hin & Hn & Hi).
  destruct (hi_wr_byte asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC e_sp0 o n (a - usp) Hin Hn Hi) as [W Hr].
  unfold APS.uE in US. unfold AX2S.uE in W, Hr. rewrite US in W, Hr. replace (usp + (a - usp)) with a in W by lia.
  assert (Hnh : APS.in_hull A (bv_unsigned (wa a)) = false).
  { pose proof HULL_ok as (H0 & H1 & H2 & H3). unfold KHI in H3. unfold APS.in_hull. rewrite wa_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  pose proof (SEGS_in_hull _ Hnh) as F.
  unfold wview in W. fold (wa a) in W. rewrite F in W.
  destruct (MR (wa a)) as [bb|] eqn:Hm; [|exfalso; apply W; reflexivity].
  rewrite <- (hk_mr_some asegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA' (wa a)) in Hm;
    [| rewrite Hm; discriminate | rewrite wa_unsigned by lia; lia].
  unfold wview, mrd. rewrite Hm. split; [discriminate| exists bb; reflexivity].
Qed.

Theorem hg_stkwin : hs_stkwin_ok ch = true ->
  forall top, top mod 4096 = 0 -> top < usp - 0xa0 + 4096 -> stk asegs m (usp - 0x800000) top.
Proof.
  intros HT top Hal Hlt. pose proof sw_ptop as (P1 & P2 & P3). pose proof sw_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo, sp_window_hi in *.
  pose proof (bsb_ge ph sp rdraw argv envp uid hw) as (G & _).
  assert (T1 : kwr_cover (kn ch) e_sp0 (-8388608) 0 (S (length (kn ch))) = true).
  { unfold hs_stkwin_ok in HT. repeat (apply andb_prop in HT as [HT _]). exact HT. }
  pose proof (sw_below T1) as S1. change 0x800000 with 8388608.
  destruct (Z_le_gt_dec top usp) as [Hle|Hgt].
  - destruct S1 as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros a Ha. apply A3. lia.
  -
    assert (Htp : top <= entry_page_top sp bsb).
    { pose proof (Z.div_mod top 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (entry_page_top sp bsb) 4096 ltac:(lia)) as D2. rewrite Hal in D1. rewrite P2 in D2.
      destruct (Z_le_gt_dec top (entry_page_top sp bsb)) as [X|X]; [exact X|]. exfalso.
      assert (entry_page_top sp bsb / 4096 < top / 4096) by lia. lia. }
    apply (stk_merge asegs m _ usp _ S1); [|lia].
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (argH E (wa a)) eqn:HH; [apply sw_hidden | apply (sw_visible HT)]; first [exact HH | lia].
Qed.

End StkWin.

Definition hs_depz_ok (ch : acs) : bool :=
  match lit_of (eH1 ch) with
  | Some h1 => (kimg_cover (kn ch) d_tab (d_tab + 4 * bkt h1) (S (length (kn ch)))
                && kimg_cover (kn ch) (d_tab + 4 * bkt h1 + 4) (d_tab + 2 ^ 22) (S (length (kn ch))))%bool
  | None => false
  end.

Section DepZ.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation MR := (APS.Mr A argH E ch model FULL).

Theorem hg_depz : hs_depz_ok ch = true ->
  forall h1 b, lit_of (eH1 ch) = Some h1 -> 0 <= b < 2 ^ 20 -> b <> bkt h1 -> rw_cells asegs m (d_tab + 4 * b) [zw4 0].
Proof.
  intros HT h1 b Hh Hb Hne. unfold hs_depz_ok in HT. rewrite Hh in HT. apply andb_prop in HT as [T1 T2].
  assert (Hbk : 0 <= bkt h1 < 2 ^ 20) by (unfold bkt; apply Z.mod_pos_bound; lia).
  set (a0 := d_tab + 4 * b).
  assert (Ha0 : ZWIN_LO <= a0 /\ a0 + 4 <= ZWIN_HI /\ 0x164000 <= a0 /\ a0 + 4 <= 0x6ca000) by (unfold a0, ZWIN_LO, ZWIN_HI; lia).
  assert (RD : forall i, a0 <= i < a0 + 4 -> mrd asegs m (wa i) = Some (Z_to_bv 8 0)).
  { intros i Hi.
    assert (COV : exists lo h, In (KImg lo h) (kn ch) /\ lo <= i < h).
    { destruct (Z_lt_le_dec b (bkt h1)); [apply (kimg_cover_sound _ _ _ _ T1 i) | apply (kimg_cover_sound _ _ _ _ T2 i)]; unfold a0 in Hi; lia. }
    destruct COV as (lo & h & Hin & Hr).
    pose proof (hk_kimg asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC lo h Hin i Hr) as MRN. fold (wa i) in MRN.
    assert (Hu : bv_unsigned (wa i) = i) by (apply wa_unsigned; lia).
    assert (Hhull : APS.in_hull A (bv_unsigned (wa i)) = true).
    { destruct (APS.in_hull A (bv_unsigned (wa i))) eqn:Ehull; [reflexivity|]. exfalso.
      pose proof (SEGS_in_hull _ Ehull) as F. rewrite Hu in F.
      pose proof (seg_rw_byte_win i ltac:(lia)) as SB. unfold seg_rw_byte in SB. rewrite F in SB. discriminate SB. }
    destruct (hk_hull asegs A nx0 LIMIT SINV argH FS0 HULL_ok argH_high E ch R FULL model HC A' HA' (wa i) Hhull) as (E1 & E2).
    unfold mrd. rewrite E1, <- E2, MRN. apply (asan_zero_win (wa i)). rewrite Hu. lia. }
  apply rw_cells_of.
  - cbn. auto.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    rewrite (RD (a0 + Z.of_nat i) ltac:(lia)).
    do 4 (destruct i as [|i]; [reflexivity|]). lia.
  - change (Z.of_nat (cells_size [zw4 0])) with 4.
    exact (proj1 (seg_rw_ok_sound asegs a0 4 (seg_rw_ok_win a0 4 ltac:(lia) ltac:(lia) ltac:(lia)) m)).
Qed.

End DepZ.

Definition hs_g1_ok (ch : acs) : bool := (hs_stkwin_ok ch && hs_depz_ok ch)%bool.

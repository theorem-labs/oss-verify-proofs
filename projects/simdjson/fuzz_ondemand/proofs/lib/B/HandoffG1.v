(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off's stack-window check reads the run's whole launch input and its CONFIG_RSEQ-dependent auxv layout, and checks the 0x5D0000-byte span the start state guarantees below sp instead of 8 MiB. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import AsanZeroWinB.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow HandoffKit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout HandoffImage HandoffArgv R_depot_defs RT_state RT_init RT_init_mem RT_init_img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hg_fx : PropExec.FPState := PropExec.fx0.

Definition kw8_in (k : list kentry) (b : expr) (o : Z) : bool :=
  existsb (fun K => match K with KWord (SA b' o') 8 _ => (expr_eqb b' b && Z.eqb o' o)%bool | _ => false end) k.

Definition kb16_in (k : list kentry) (b : expr) (o : Z) : bool :=
  existsb (fun K => match K with KBlob (SA b' o') (ELit 16) _ => (expr_eqb b' b && Z.eqb o' o)%bool | _ => false end) k.

Definition kz16_in (k : list kentry) (b : expr) (o : Z) : bool :=
  existsb (fun K => match K with KZero (SA b' o') (ELit 16) => (expr_eqb b' b && Z.eqb o' o)%bool | _ => false end) k.

Definition kunk_in (k : list kentry) (b : expr) (o n : Z) : bool :=
  existsb (fun K => match K with KUnk (SA b' o') (ELit n') => (expr_eqb b' b && Z.eqb o' o && Z.eqb n' n)%bool | _ => false end) k.

(* [r] is the launch's CONFIG_RSEQ bit as 0 or 1 ([AP.rseq_z]).  LPS 727298f3:
   - below sp the start state claims only [StoreOk.stack_window_depth] = 6144513
     bytes writable ([AsanPlanCore.init_kn_with]'s [KWr (SA e_sp0 (-6144513)) ..]),
     so the window checked is the guaranteed span 0x5D0000 = 6094848
     ([RT_iface.STACK_SPAN]), not 8 MiB;
   - above sp, [AsanInit.argH0] hides the envp array, argv[2..] with argv's NULL,
     the STACK_ROUND gap and the pad and strings up to the stack VMA's end, so the
     visible bytes are the argc / argv[0] / argv[1] words at sp, sp+8, sp+16, the
     auxv vector ([AUXSZ r] bytes at the auxv base plus 24; a [KUnk] over it, or
     every one of its words) and the sixteen AT_RANDOM bytes at the auxv base plus
     [24 + AUXSZ r] (a [KBlob] or a [KZero]). *)
Definition hs_stkwin_ok (r : Z) (ch : acs) : bool :=
  (kwr_cover (kn ch) e_sp0 (-6094848) 0 (S (length (kn ch)))
   && kw8_in (kn ch) e_sp0 0 && kw8_in (kn ch) e_sp0 8 && kw8_in (kn ch) e_sp0 16
   && (kunk_in (kn ch) (fst e_auxb) (snd e_auxb) (AUXSZ r)
       || forallb (fun j => kw8_in (kn ch) (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) (seq 0 (Z.to_nat (AUXSZ r / 8))))
   && (kb16_in (kn ch) (fst (e_atrb r)) (snd (e_atrb r)) || kz16_in (kn ch) (fst (e_atrb r)) (snd (e_atrb r))))%bool.

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

Lemma kz16_in_sound : forall k b o, kz16_in k b o = true -> In (KZero (SA b o) (ELit 16)) k.
Proof.
  intros k b o H. unfold kz16_in in H. apply existsb_exists in H as (K & Hin & HK).
  destruct K as [|a n| | | | | | | |]; try discriminate. destruct a as [b' o']. destruct n as [z| | | | | | |]; try discriminate.
  destruct (Z.eq_dec z 16) as [->|Hz]; [|exfalso; destruct z as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate); apply Hz; reflexivity].
  apply andb_prop in HK as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst b' o'. exact Hin.
Qed.

Lemma kunk_in_sound : forall k b o n, kunk_in k b o n = true -> In (KUnk (SA b o) (ELit n)) k.
Proof.
  intros k b o n H. unfold kunk_in in H. apply existsb_exists in H as (K & Hin & HK).
  destruct K as [| | | | | | | | |a l]; try discriminate. destruct a as [b' o']. destruct l as [z| | | | | | |]; try discriminate.
  apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst b' o' z. exact Hin.
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
Lemma e_atrandom_vars : forall b, expr_vars_lt NX0 (e_atrandom (rseq_z b)) = true /\ ev_only (e_atrandom (rseq_z b)) = true.
Proof. intros [|]; split; reflexivity. Qed.
Lemma e_auxb_split : split_lit e_auxv = (fst e_auxb, snd e_auxb). Proof. unfold e_auxb. destruct (split_lit e_auxv); reflexivity. Qed.
Lemma e_atrb_split : forall r, split_lit (e_atrandom r) = (fst (e_atrb r), snd (e_atrb r)).
Proof. intros r. unfold e_atrb. destruct (split_lit (e_atrandom r)); reflexivity. Qed.
Lemma e_auxb_k : snd e_auxb = 24. Proof. vm_compute. reflexivity. Qed.
(* was [snd e_atrb = 184] at the pre-revision layout.  [AUXSZ r] is not a
   literal at a free [r] and the smart constructors do not normalise, so
   destruct the flag first and give both branches -- the model's own idiom and
   its whole proof (75d69e00 AsanPlanCore.v:3874). *)
Lemma e_atrb_k : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section StkWin.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
(* LPS 727298f3: the launch, as AS/AsanInit.v's Section Init names it: the run's
   whole input [inp] (A/HandoffArgv.v and A/HandoffA.v take it the same way). *)
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation SINV := (SINV0 A ph sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0 := (AsanInit.E0 sp rdraw brk0 inp).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation utop := (bv_unsigned (ed_top rdraw)).
#[local] Notation bsb := (entry_stack_image inp mbase ph (Z_to_bv 64 (a_entry A)) sp rdraw).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
(* the launch's CONFIG_RSEQ flag, read off the kernel build: never pinned *)
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
(* AS/AsanInit.v's [CHEAD] (sp to the top of the AT_RANDOM bytes) and [G]
   (STACK_ROUND's gap, in words) *)
#[local] Notation CHD := (Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) argv envp)).
#[local] Notation GAP := (Z.of_nat (block_items argv envp mod 2)).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation MR := (APS.Mr A argH E ch model FULL).

Lemma sw_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. eapply argH0_high; eassumption. Qed.

Lemma sw_some : forall a b, CEIL <= a < 2 ^ 47 -> m (wa a) = Some b -> wview bsegs m (wa a) <> None /\ exists b', mrd bsegs m (wa a) = Some b'.
Proof. intros a b Ha Hm. unfold wview, mrd. rewrite Hm. split; [discriminate | exists b; reflexivity]. Qed.

Lemma sw_bytes : forall a0 bs a, bytes_at bsegs m a0 bs -> CEIL <= a0 -> a0 + Z.of_nat (length bs) <= 2 ^ 47 -> a0 <= a < a0 + Z.of_nat (length bs) ->
  wview bsegs m (wa a) <> None /\ exists b', mrd bsegs m (wa a) = Some b'.
Proof.
  intros a0 bs a B Ha0 Hb Ha.
  assert (WR : wr_at bsegs m a0 (Z.of_nat (length bs))) by (eapply ha_wr; eassumption).
  destruct WR as (_ & _ & W).
  destruct B as (_ & _ & B3). specialize (W (a - a0) ltac:(lia)). replace (a0 + (a - a0)) with a in W by lia. split; [exact W|].
  specialize (B3 (Z.to_nat (a - a0)) ltac:(lia)). rewrite Z2Nat.id in B3 by lia. replace (a0 + (a - a0)) with a in B3 by lia.
  destruct (nth_error bs (Z.to_nat (a - a0))) as [b|] eqn:Hn; [exists b; exact B3 | apply nth_error_None in Hn; lia].
Qed.

Lemma sw_lens : 1 <= argc <= 1024 /\ 0 <= envc <= 256 /\ sp_window_lo <= usp <= sp_window_hi.
Proof. eapply ha_lens; eassumption. Qed.

(* the block runs from sp to the stack VMA's end [ed_top], which is page-aligned:
   there is no page tail above it at this revision *)
Lemma sw_layout : usp + Z.of_nat (length bsb) <= 2 ^ 47 /\ usp + Z.of_nat (length bsb) = utop /\ utop mod 4096 = 0
  /\ CHD + 8 <= Z.of_nat (length bsb).
Proof.
  assert (F : usp + Z.of_nat (length bsb) <= 2 ^ 47) by (eapply usp_fit; eassumption).
  assert (G1 : Z.of_nat (length bsb) = CHD + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) argv envp (in_execfn inp))
                 + Z.of_nat (launch_string_bytes argv envp (in_execfn inp)) + 8)
    by (edestruct bsb_ge as [_ G1]; first [exact G1 | eassumption]).
  pose proof (length_entry_stack_image_launch Sv48 inp mbase ph (Z_to_bv 64 (a_entry A)) sp brk0 rdraw Hlau) as T.
  pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as (Hst & _ & _).
  destruct Hst as (Hm & _ & _). unfold page_size in Hm.
  split; [exact F|]. split; [lia|]. split; [exact Hm | lia].
Qed.

Lemma sw_chead : CHD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * GAP /\ 0 <= GAP <= 1 /\ 0 <= RZ <= 1
  /\ AUXSZ RZ / 8 = 54 + 4 * RZ.
Proof.
  split; [eapply chead_eq; eassumption|].
  split; [pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)); lia|].
  destruct (kb_rseq (in_kernel inp)); cbn [rseq_z]; split; first [lia | reflexivity].
Qed.

Lemma sw_u : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> APS.uE E e = APS.uE E0 e.
Proof. intros e H1 H2. eapply ha_u; eassumption. Qed.

Lemma sw_uauxv : APS.uE E (fst e_auxb) + 24 = usp + 8 * argc + 8 * envc + 24.
Proof.
  pose proof sw_lens as (LA & LE & U1 & U2). unfold sp_window_lo in U1.
  assert (U : APS.uE E e_auxv = usp + 8 * argc + 8 * envc + 24).
  { rewrite (sw_u e_auxv (proj1 e_auxv_vars) (proj2 e_auxv_vars)). eapply u_e_auxv; eassumption. }
  pose proof (split_base_u E e_auxv (fst e_auxb) (snd e_auxb) e_auxb_split) as S. rewrite e_auxb_k in S. rewrite <- U. apply S; lia.
Qed.

(* the AT_RANDOM block's literal offset is [24 + AUXSZ RZ] above the auxv base,
   and the block ends at [usp + CHEAD] (AS/AsanInit.v [u_e_atrandom]) *)
Lemma sw_uatr : APS.uE E (fst (e_atrb RZ)) + (24 + AUXSZ RZ) = usp + CHD - 16.
Proof.
  pose proof sw_lens as (LA & LE & U1 & U2). unfold sp_window_lo in U1.
  pose proof sw_chead as (CH & GR & RR & _).
  assert (U : APS.uE E (e_atrandom RZ) = usp + CHD - 16).
  { rewrite (sw_u (e_atrandom RZ) (proj1 (e_atrandom_vars (kb_rseq (in_kernel inp)))) (proj2 (e_atrandom_vars (kb_rseq (in_kernel inp))))).
    eapply u_e_atrandom; eassumption. }
  pose proof (split_base_u E (e_atrandom RZ) (fst (e_atrb RZ)) (snd (e_atrb RZ)) (e_atrb_split RZ)) as S.
  rewrite (e_atrb_k (kb_rseq (in_kernel inp))) in S. rewrite <- U. unfold AUXSZ in *. apply S; lia.
Qed.

Lemma sw_hidden : forall a, usp <= a < utop -> argH E (wa a) = true ->
  wview bsegs m (wa a) <> None /\ exists b', mrd bsegs m (wa a) = Some b'.
Proof.
  intros a Ha HH. pose proof sw_layout as (P1 & P2 & P3 & P4). pose proof sw_lens as (_ & _ & U1 & U2). unfold sp_window_lo in U1.
  assert (Hu : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (HAT : alloc_top (m_vmmaps model) = usp - 8388608) by (eapply ha_isp; eassumption).
  assert (Hv : m (wa a) = FULL (wa a)) by (eapply ha_visible; first [eassumption | rewrite Hu, HAT; lia]).
  assert (Hb : FULL (wa a) = wrap_mem inp mbase ph (Z_to_bv 64 (a_entry A)) sp rdraw (wa a)) by (eapply ha_block; eassumption).
  rewrite Hb in Hv.
  rewrite (wrap_above_sp inp mbase ph (Z_to_bv 64 (a_entry A)) sp rdraw (wa a) ltac:(rewrite Hu; lia)) in Hv.
  unfold stack_to_mem in Hv. cbv zeta in Hv. rewrite Hu in Hv. rewrite (proj2 (Z.leb_le usp a)) in Hv by lia.
  rewrite (proj2 (Z.ltb_lt (a - usp) _)) in Hv by lia.
  destruct (nth_error bsb (Z.to_nat (a - usp))) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
  apply (sw_some a b); [unfold CEIL; lia | exact Hv].
Qed.

Lemma sw_visible : hs_stkwin_ok RZ ch = true -> forall a, usp <= a < utop -> argH E (wa a) = false ->
  wview bsegs m (wa a) <> None /\ exists b', mrd bsegs m (wa a) = Some b'.
Proof.
  intros HT a Ha HH. pose proof sw_layout as (P1 & P2 & P3 & P4). pose proof sw_lens as (LA & LE & U1 & U2). unfold sp_window_lo in U1.
  pose proof sw_chead as (CH & GR & RR & AX8).
  assert (Hu : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (CE : CEIL <= usp) by (unfold CEIL; lia).
  unfold hs_stkwin_ok in HT. apply andb_prop in HT as [HT T6]. apply andb_prop in HT as [HT T5]. apply andb_prop in HT as [HT T4].
  apply andb_prop in HT as [HT T3]. apply andb_prop in HT as [_ T2].
  (* the visible bytes of [AsanInit.argH0]: the three words at sp, the auxv vector,
     the AT_RANDOM bytes *)
  assert (Hc : a < usp + 24 \/ (usp + 8 * argc + 8 * envc + 24 <= a < usp + CHD - 16 - 8 * GAP)
               \/ (usp + CHD - 16 <= a < usp + CHD)).
  { unfold argH0, argH0_old in HH. cbv zeta in HH. rewrite Hu in HH.
    apply orb_false_iff in HH as [HH H4]. apply orb_false_iff in HH as [HH H3]. apply orb_false_iff in HH as [H1 H2].
    apply andb_false_iff in H1. apply andb_false_iff in H2. apply andb_false_iff in H3. apply andb_false_iff in H4.
    rewrite !Z.leb_gt, !Z.ltb_ge in *. lia. }
  destruct Hc as [C|[C|C]].
  - (* argc, argv[0], argv[1] *)
    assert (Ho : exists o, (o = 0 \/ o = 8 \/ o = 16) /\ kw8_in (kn ch) e_sp0 o = true /\ usp + o <= a < usp + o + 8).
    { destruct (Z_lt_le_dec a (usp + 8)); [exists 0; split; [tauto|]; split; [exact T2 | lia]|].
      destruct (Z_lt_le_dec a (usp + 16)); [exists 8; split; [tauto|]; split; [exact T3 | lia]|]. exists 16. split; [tauto|]. split; [exact T4 | lia]. }
    destruct Ho as (o & Ho & Tk & Hr). destruct (kw8_in_sound _ _ _ Tk) as (v & Hin).
    assert (B : bytes_at bsegs m (usp + o) (le8 (edenot E v))) by (eapply ha_kw; first [exact Hin | lia | eassumption]).
    apply (sw_bytes (usp + o) (le8 (edenot E v)) a B); [lia | unfold le8; rewrite CatExec.length_N_to_le_bytes; lia | unfold le8; rewrite CatExec.length_N_to_le_bytes; lia].
  - (* the auxv vector, [AUXSZ RZ] bytes at the auxv base plus 24 *)
    pose proof sw_uauxv as UA. unfold APS.uE in UA.
    apply orb_prop in T5 as [T5|T5].
    + pose proof (kunk_in_sound _ _ _ _ T5) as Hin.
      destruct (hk_kentry bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC _ Hin) as (Hfl & Hb).
      assert (HAX : 0 <= AUXSZ RZ < 2 ^ 64) by (unfold AUXSZ; lia).
      rewrite (APS.elenZ_lit E (AUXSZ RZ) HAX) in Hb. unfold estart in Hb. cbn [a_base a_off] in Hb. rewrite e_auxb_k in Hb.
      specialize (Hb (a - (usp + 8 * argc + 8 * envc + 24)) ltac:(unfold AUXSZ in *; lia)).
      replace (bv_unsigned (edenot E (fst e_auxb)) + 24 + (a - (usp + 8 * argc + 8 * envc + 24))) with a in Hb by lia.
      fold (wa a) in Hb.
      assert (Hm : m (wa a) = MR (wa a)).
      { apply (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA'); [exact Hb | rewrite Hu; lia]. }
      assert (Hs : exists b, MR (wa a) = Some b).
      { destruct (MR (wa a)) as [b|] eqn:HM; [exists b; reflexivity|]. exfalso. first [exact (Hb HM) | apply Hb; reflexivity]. }
      destruct Hs as (b & HM). rewrite HM in Hm. exact (sw_some a b ltac:(lia) Hm).
    + set (j := Z.to_nat ((a - (usp + 8 * argc + 8 * envc + 24)) / 8)).
      assert (Hj : Z.of_nat j < 54 + 4 * RZ /\ usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j <= a < usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j + 8).
      { unfold j. pose proof (Z.div_mod (a - (usp + 8 * argc + 8 * envc + 24)) 8 ltac:(lia)) as D.
        pose proof (Z.mod_pos_bound (a - (usp + 8 * argc + 8 * envc + 24)) 8 ltac:(lia)) as M.
        assert (0 <= (a - (usp + 8 * argc + 8 * envc + 24)) / 8 < 54 + 4 * RZ) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        rewrite Z2Nat.id by lia. split; [lia | lia]. }
      destruct Hj as (Hj & Hr).
      pose proof (proj1 (forallb_forall _ _) T5 j ltac:(apply in_seq; rewrite AX8; lia)) as Tk. cbv beta in Tk.
      destruct (kw8_in_sound _ _ _ Tk) as (v & Hin).
      pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok sw_argH_high E ch R FULL model HC A' HA' _ 8%nat v Hin) as B.
      unfold estart in B. cbn [a_base a_off] in B. rewrite e_auxb_k in B.
      replace (bv_unsigned (edenot E (fst e_auxb)) + (24 + 8 * Z.of_nat j)) with (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j) in B by lia.
      specialize (B ltac:(change (Z.of_nat 8) with 8; lia)).
      apply (sw_bytes _ _ a B); [lia | rewrite CatExec.length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia | rewrite CatExec.length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia].
  - (* the sixteen AT_RANDOM bytes at the auxv base plus [24 + AUXSZ RZ] *)
    pose proof sw_uatr as UA. unfold APS.uE in UA.
    apply orb_prop in T6 as [T6|T6].
    + destruct (kb16_in_sound _ _ _ T6) as (kk & Hin).
      destruct (hk_kentry bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC _ Hin) as (Hfl & Hlen & Hb).
      rewrite (APS.elenZ_lit E 16 ltac:(lia)) in Hb. unfold estart in Hb. cbn [a_base a_off] in Hb. rewrite (e_atrb_k (kb_rseq (in_kernel inp))) in Hb.
      specialize (Hb (a - (usp + CHD - 16)) ltac:(lia)).
      replace (bv_unsigned (edenot E (fst (e_atrb RZ))) + (24 + AUXSZ RZ) + (a - (usp + CHD - 16))) with a in Hb by lia.
      fold (wa a) in Hb.
      assert (Hm : m (wa a) = MR (wa a)).
      { apply (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA'); [rewrite Hb; discriminate | rewrite Hu; lia]. }
      rewrite Hb in Hm. exact (sw_some a _ ltac:(lia) Hm).
    + pose proof (kz16_in_sound _ _ _ T6) as Hin.
      assert (HZ : estart E (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) + elenZ E (ELit 16) <= 2 ^ 47).
      { rewrite (APS.elenZ_lit E 16 ltac:(lia)). unfold estart. cbn [a_base a_off]. rewrite (e_atrb_k (kb_rseq (in_kernel inp))). lia. }
      pose proof (hk_kzero bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA' _ _ Hin HZ) as Z0.
      rewrite (APS.elenZ_lit E 16 ltac:(lia)) in Z0. unfold estart in Z0. cbn [a_base a_off] in Z0. rewrite (e_atrb_k (kb_rseq (in_kernel inp))) in Z0.
      specialize (Z0 (a - (usp + CHD - 16)) ltac:(lia)).
      replace (bv_unsigned (edenot E (fst (e_atrb RZ))) + (24 + AUXSZ RZ) + (a - (usp + CHD - 16))) with a in Z0 by lia.
      fold (wa a) in Z0. exact (sw_some a _ ltac:(lia) Z0).
Qed.

Lemma sw_below : kwr_cover (kn ch) e_sp0 (-6094848) 0 (S (length (kn ch))) = true -> stk bsegs m (usp - 6094848) usp.
Proof.
  intros H. pose proof sw_lens as (_ & _ & U1 & U2). unfold sp_window_lo, sp_window_hi in *.
  assert (US : APS.uE E e_sp0 = usp) by (eapply ha_sp0; eassumption).
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (kwr_cover_sound _ _ _ _ _ H (a - usp) ltac:(lia)) as (o & n & Hin & Hn & Hi).
  destruct (hi_wr_byte bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC e_sp0 o n (a - usp) Hin Hn Hi) as [W Hr].
  unfold APS.uE in US. unfold AX2S.uE in W, Hr. rewrite US in W, Hr. replace (usp + (a - usp)) with a in W by lia.
  assert (Hnh : APS.in_hull A (bv_unsigned (wa a)) = false).
  { pose proof HULL_ok as (H0 & H1 & H2 & H3). unfold KHI in H3. unfold APS.in_hull. rewrite wa_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  pose proof (SEGS_in_hull _ Hnh) as F.
  unfold wview in W. fold (wa a) in W. rewrite F in W.
  destruct (MR (wa a)) as [bb|] eqn:Hm; [|exfalso; apply W; reflexivity].
  rewrite <- (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA' (wa a)) in Hm;
    [| rewrite Hm; discriminate | rewrite wa_unsigned by lia; lia].
  unfold wview, mrd. rewrite Hm. split; [discriminate| exists bb; reflexivity].
Qed.

(* the window from 0x5D0000 = 6094848 bytes below sp ([RT_iface.STACK_SPAN]; the
   caller rewrites with [RT_iface.STACK_SPAN_val]) up to a page boundary just
   above sp *)
Theorem hg_stkwin : hs_stkwin_ok RZ ch = true ->
  forall top, top mod 4096 = 0 -> top < usp - 0xa0 + 4096 -> stk bsegs m (usp - 6094848) top.
Proof.
  intros HT top Hal Hlt. pose proof sw_layout as (P1 & P2 & P3 & P4). pose proof sw_lens as (LA & LE & U1 & U2). unfold sp_window_lo, sp_window_hi in *.
  assert (T1 : kwr_cover (kn ch) e_sp0 (-6094848) 0 (S (length (kn ch))) = true).
  { unfold hs_stkwin_ok in HT. repeat (apply andb_prop in HT as [HT _]). exact HT. }
  pose proof (sw_below T1) as S1.
  destruct (Z_le_gt_dec top usp) as [Hle|Hgt].
  - destruct S1 as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros a Ha. apply A3. lia.
  -
    assert (Htp : top <= utop).
    { pose proof (Z.div_mod top 4096 ltac:(lia)) as D1. pose proof (Z.div_mod utop 4096 ltac:(lia)) as D2.
      rewrite Hal in D1. rewrite P3 in D2. lia. }
    apply (stk_merge bsegs m _ usp _ S1); [|lia].
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
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation MR := (APS.Mr A argH E ch model FULL).

Theorem hg_depz : hs_depz_ok ch = true ->
  forall h1 b, lit_of (eH1 ch) = Some h1 -> 0 <= b < 2 ^ 20 -> b <> bkt h1 -> rw_cells bsegs m (d_tab + 4 * b) [zw4 0].
Proof.
  intros HT h1 b Hh Hb Hne. unfold hs_depz_ok in HT. rewrite Hh in HT. apply andb_prop in HT as [T1 T2].
  assert (Hbk : 0 <= bkt h1 < 2 ^ 20) by (unfold bkt; apply Z.mod_pos_bound; lia).
  set (a0 := d_tab + 4 * b).
  assert (Ha0 : ZWIN_LO <= a0 /\ a0 + 4 <= ZWIN_HI /\ 0x117000 <= a0 /\ a0 + 4 <= 0x679000) by (unfold a0, ZWIN_LO, ZWIN_HI; lia).
  assert (RD : forall i, a0 <= i < a0 + 4 -> mrd bsegs m (wa i) = Some (Z_to_bv 8 0)).
  { intros i Hi.
    assert (COV : exists lo h, In (KImg lo h) (kn ch) /\ lo <= i < h).
    { destruct (Z_lt_le_dec b (bkt h1)); [apply (kimg_cover_sound _ _ _ _ T1 i) | apply (kimg_cover_sound _ _ _ _ T2 i)]; unfold a0 in Hi; lia. }
    destruct COV as (lo & h & Hin & Hr).
    pose proof (hk_kimg bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model HC lo h Hin i Hr) as MRN. fold (wa i) in MRN.
    assert (Hu : bv_unsigned (wa i) = i) by (apply wa_unsigned; lia).
    assert (Hhull : APS.in_hull A (bv_unsigned (wa i)) = true).
    { destruct (APS.in_hull A (bv_unsigned (wa i))) eqn:Ehull; [reflexivity|]. exfalso.
      pose proof (SEGS_in_hull _ Ehull) as F. rewrite Hu in F.
      pose proof (seg_rw_byte_win i ltac:(lia)) as SB. unfold seg_rw_byte in SB. rewrite F in SB. discriminate SB. }
    destruct (hk_hull bsegs A nx0 LIMIT SINV argH FS0 HULL_ok argH_high E ch R FULL model HC A' HA' (wa i) Hhull) as (E1 & E2).
    unfold mrd. rewrite E1, <- E2, MRN. apply (asan_zero_win (wa i)). rewrite Hu. lia. }
  apply rw_cells_of.
  - cbn. auto.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    rewrite (RD (a0 + Z.of_nat i) ltac:(lia)).
    do 4 (destruct i as [|i]; [reflexivity|]). lia.
  - change (Z.of_nat (cells_size [zw4 0])) with 4.
    exact (proj1 (seg_rw_ok_sound bsegs a0 4 (seg_rw_ok_win a0 4 ltac:(lia) ltac:(lia) ltac:(lia)) m)).
Qed.

End DepZ.

Definition hs_g1_ok (r : Z) (ch : acs) : bool := (hs_stkwin_ok r ch && hs_depz_ok ch)%bool.

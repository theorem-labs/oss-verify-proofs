(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree Nodes Decode VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Malloc KInv KStep KStepK MBound.
Import ListNotations.
Local Open Scope Z_scope.

Definition HIGH : Z := 2^32.
Definition SBMAX : Z := 0x5c000 + 2^31.
Definition BRKTOP : Z := SBMAX + PGSZ * BP * Z.of_nat KTOP + PGSZ.
Definition MAPTOP : Z := BM * Z.of_nat KTOP.
Definition BACKTOP : Z := 2^34.
Definition ZLO : Z := 2^43.

Lemma BRKTOP_HIGH : BRKTOP + 2^28 <= HIGH.
Proof. unfold BRKTOP, SBMAX, HIGH, PGSZ, BP, KTOP. cbn. lia. Qed.

Lemma mmap_base_min_val : mmap_base_min = 0x154555557000.
Proof. reflexivity. Qed.
Lemma page_size_val : page_size = 4096.
Proof. reflexivity. Qed.

Definition esz (e : word * word) : Z := bv_unsigned (snd e).
Lemma ehi_elo e : ehi e = elo e + esz e. Proof. destruct e; reflexivity. Qed.
Lemma elo_nonneg e : 0 <= elo e. Proof. unfold elo. apply bv_unsigned_in_range. Qed.
Lemma esz_nonneg e : 0 <= esz e. Proof. unfold esz. apply bv_unsigned_in_range. Qed.
Lemma esz_lt e : esz e < 2^64. Proof. unfold esz. pose proof (bv_unsigned_in_range 64 (snd e)). unfold bv_modulus in H. lia. Qed.
Lemma elo_lt e : elo e < 2^64. Proof. unfold elo. pose proof (bv_unsigned_in_range 64 (fst e)). unfold bv_modulus in H. lia. Qed.

Lemma live_bytes_cons e l : live_bytes (e :: l) = esz e + live_bytes l.
Proof. destruct e; reflexivity. Qed.
Lemma live_bytes_app l1 l2 : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|e l1 IH]; [reflexivity|]. cbn [app]. rewrite !live_bytes_cons, IH. lia. Qed.
Lemma live_bytes_nonneg l : 0 <= live_bytes l.
Proof. induction l as [|e l IH]; [cbn; lia|]. rewrite live_bytes_cons. pose proof (esz_nonneg e). lia. Qed.
Lemma live_bytes_filter_le f l : live_bytes (List.filter f l) <= live_bytes l.
Proof.
  induction l as [|e l IH]; [cbn; lia|]. cbn [List.filter]. pose proof (esz_nonneg e).
  destruct (f e); rewrite ?live_bytes_cons; lia.
Qed.
Lemma length_filter_le {A} (f : A -> bool) l : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma lb_iv_subtract a sz lo hi : lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros LH. unfold iv_subtract. pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in *.
  change (2 ^ Z.of_N 64) with (2^64) in *.
  pose proof (Z.le_max_l (bv_unsigned a) hi). pose proof (Z.le_max_r (bv_unsigned a) hi).
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app live_bytes];
   rewrite ?unsigned_lit; lia.
Qed.

Lemma lb_maps_subtract_le l lo hi : lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  intros LH. induction l as [|[a sz] l IH]; cbn [maps_subtract]; [cbn; lia|].
  rewrite live_bytes_app, live_bytes_cons. pose proof (lb_iv_subtract a sz lo hi LH). unfold esz; cbn [snd]. lia.
Qed.

Lemma lb_msa_le cuts : forall l, live_bytes (maps_subtract_all l cuts) <= live_bytes l.
Proof.
  induction cuts as [|[a n] cuts IH]; intros l; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH|]. apply lb_maps_subtract_le. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma vm_backing_used_le mo : m_vm_lazy mo = [] ->
  vm_backing_used mo <= live_bytes (vm_maps (m_vmmaps mo)) + Z.of_nat (length (m_vm_materialized mo)) * page_size.
Proof.
  intros HL. unfold vm_backing_used. rewrite HL. cbn [maps_subtract_all]. unfold vm_backed_maps.
  pose proof (lb_msa_le (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))). lia.
Qed.

Lemma In_maps_subtract l lo hi e' : (forall e, In e l -> ehi e <= 2^64) -> In e' (maps_subtract l lo hi) ->
  exists e, In e l /\ elo e <= elo e' /\ ehi e' <= ehi e.
Proof.
  intros WF. induction l as [|[a sz] l IH]; cbn [maps_subtract]; [intros []|]. intros H. apply in_app_or in H as [H|H].
  - exists (a, sz). split; [left; reflexivity|]. specialize (WF (a, sz) (or_introl eq_refl)). unfold ehi, elo in *; cbn [fst snd] in *.
    pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in *.
    change (2 ^ Z.of_N 64) with (2^64) in *.
    unfold iv_subtract in H. destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app] in H;
      repeat (destruct H as [<-|H]); try contradiction; cbn [fst snd];
      try (pose proof (Z.le_max_l (bv_unsigned a) hi); pose proof (Z.le_max_r (bv_unsigned a) hi));
      rewrite ?unsigned_lit; try lia.
  - destruct (IH (fun e He => WF e (or_intror He)) H) as (e & He & B). exists e. split; [right; exact He| exact B].
Qed.

Lemma length_maps_subtract_le l lo hi : (forall e, In e l -> lo <= elo e) -> (length (maps_subtract l lo hi) <= length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; cbn [maps_subtract]; intros H; [cbn; lia|].
  rewrite length_app. specialize (IH (fun e He => H e (or_intror He))).
  assert ((length (iv_subtract a sz lo hi) <= 1)%nat); [| cbn [length] in *; lia].
  specialize (H (a, sz) (or_introl eq_refl)). unfold elo in H; cbn [fst] in H.
  unfold iv_subtract. destruct (Z.ltb_spec (bv_unsigned a) lo); [lia|]. cbn [app]. destruct (_ <? _); cbn; lia.
Qed.

Lemma In_map_remove l k e : In e (map_remove l k) -> In e l.
Proof. unfold map_remove. intros H. apply filter_In in H. tauto. Qed.
Lemma lb_map_remove_le l k : live_bytes (map_remove l k) <= live_bytes l.
Proof. unfold map_remove. apply live_bytes_filter_le. Qed.
Lemma length_map_remove_le l k : (length (map_remove l k) <= length l)%nat.
Proof. unfold map_remove. apply length_filter_le. Qed.

Definition nres : nat := 64.

Record PK (zd : bool) (wb wm wp : Z) (mo : Model) : Prop := mkPK {
  pk_zone : forall e, In e (vm_maps (m_vmmaps mo)) ->
      (bv_unsigned (vm_start_brk (m_vmmaps mo)) <= elo e /\ ehi e <= bv_unsigned (vm_brk (m_vmmaps mo)))
      \/ ((zd = true -> HIGH <= elo e) /\ esz e <= LMAX);
  pk_sb : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= SBMAX;
  pk_brk : bv_unsigned (vm_brk (m_vmmaps mo)) + PGSZ * wp <= BRKTOP;
  pk_cnt : Z.of_nat (length (vm_maps (m_vmmaps mo))) + wm <= MAPTOP;
  pk_resv : (length (vm_reserved (m_vmmaps mo)) <= nres)%nat;
  pk_back : live_bytes (vm_maps (m_vmmaps mo)) + Z.of_nat (length (m_vm_materialized mo)) * 4096 + wb <= BACKTOP;
  pk_lim : BACKTOP <= vm_limit (m_vmmaps mo);
  pk_base : mmap_base_min <= bv_unsigned (vm_mmap_base (m_vmmaps mo));
  pk_W : 0 <= wb /\ 0 <= wm /\ 0 <= wp }.

Lemma PK_weaken zd wb wm wp wb' wm' wp' mo : PK zd wb wm wp mo -> 0 <= wb' <= wb -> 0 <= wm' <= wm -> 0 <= wp' <= wp -> PK zd wb' wm' wp' mo.
Proof.
  intros P Hb Hm Hp. destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. assert (PG : PGSZ = 4096) by reflexivity. constructor; auto; try lia; try nia.
Qed.

Lemma PK_forget zd wb wm wp mo : PK zd wb wm wp mo -> PK false wb wm wp mo.
Proof.
  intros P. destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. constructor; auto.
  intros e He. destruct (Zn e He) as [B|[_ Z2]]; [left; exact B| right; split; [discriminate| exact Z2]].
Qed.

Lemma PK_vm_eq zd wb wm wp mo mo' : PK zd wb wm wp mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_materialized mo' = m_vm_materialized mo -> PK zd wb wm wp mo'.
Proof. intros P E1 E2. destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. constructor; rewrite ?E1, ?E2; auto. Qed.

Lemma m_vm_materialized_with_fds v m : m_vm_materialized (with_fds v m) = m_vm_materialized m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_tid v m : m_vm_materialized (with_tid v m) = m_vm_materialized m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps v m : m_vm_materialized (with_vmmaps v m) = m_vm_materialized m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vm_materialized_vm_forget_range lo hi m :
  m_vm_materialized (vm_forget_range lo hi m) = List.filter (page_outside_range lo hi) (m_vm_materialized m).
Proof. destruct m; reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range lo hi m : m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vm_materialized_forget_vm_ranges rs : forall m, (length (m_vm_materialized (forget_vm_ranges rs m)) <= length (m_vm_materialized m))%nat.
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [lia|].
  etransitivity; [apply IH|]. rewrite m_vm_materialized_vm_forget_range. apply length_filter_le.
Qed.
Lemma m_vmmaps_forget_vm_ranges' rs : forall m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. apply m_vmmaps_vm_forget_range. Qed.
Lemma m_vm_materialized_init_model r brk mb sp lim inp : m_vm_materialized (init_model r brk mb sp lim inp) = [].
Proof. reflexivity. Qed.

Lemma PK_with_fds zd wb wm wp mo v : PK zd wb wm wp mo -> PK zd wb wm wp (with_fds v mo).
Proof. intros P. eapply PK_vm_eq; [exact P| apply m_vmmaps_with_fds| apply m_vm_materialized_with_fds]. Qed.
Lemma PK_with_tid zd wb wm wp mo v : PK zd wb wm wp mo -> PK zd wb wm wp (with_tid v mo).
Proof. intros P. eapply PK_vm_eq; [exact P| apply m_vmmaps_with_tid| apply m_vm_materialized_with_tid]. Qed.

Lemma PK_init zd r brk mb sp lim inp :
  (length r <= nres)%nat -> bv_unsigned brk <= SBMAX -> BACKTOP <= lim -> mmap_base_min <= bv_unsigned mb ->
  PK zd (BB * Z.of_nat KTOP) (BM * Z.of_nat KTOP) (BP * Z.of_nat KTOP) (init_model r brk mb sp lim inp).
Proof.
  intros Hr Hb Hl Hm. constructor; rewrite ?m_vmmaps_init_model, ?m_vm_materialized_init_model;
    cbn [vm_maps vm_start_brk vm_brk vm_reserved vm_limit vm_mmap_base length live_bytes Z.of_nat]; auto.
  - intros e [].
  - unfold BRKTOP. assert (PGSZ = 4096) by reflexivity. nia.
  - unfold MAPTOP. lia.
  - unfold BACKTOP, BB, KTOP. cbn. lia.
  - unfold BB, BM, BP, KTOP. cbn. lia.
Qed.

Lemma PK_same zd wb wm wp wb' wm' wp' mo mo' :
  PK zd wb wm wp mo ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  (length (m_vm_materialized mo') <= length (m_vm_materialized mo))%nat ->
  0 <= wb' <= wb -> 0 <= wm' <= wm -> 0 <= wp' <= wp ->
  PK zd wb' wm' wp' mo'.
Proof.
  intros P E1 E2 E3 E4 E5 E6 LM Hb Hm Hp. destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. assert (PG : PGSZ = 4096) by reflexivity.
  constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6; auto; try lia; nia.
Qed.

Lemma with_brk_next_fields mo req r :
  let h' := m_vmmaps (with_brk_next mo req r) in
  h' = brk_model_next (m_vmmaps mo) req r
  /\ (length (m_vm_materialized (with_brk_next mo req r)) <= length (m_vm_materialized mo))%nat.
Proof.
  unfold with_brk_next. split.
  - rewrite m_vmmaps_forget_vm_ranges', m_vmmaps_with_vmmaps. reflexivity.
  - etransitivity; [apply m_vm_materialized_forget_vm_ranges|]. rewrite m_vm_materialized_with_vmmaps. lia.
Qed.

Lemma PK_brk_query zd wb wm wp mo rsp mo' evs :
  PK zd wb wm wp mo -> nstep (NBrk 0) mo rsp mo' evs -> PK zd wb wm wp mo'.
Proof.
  intros P ST. destruct (nstep_brk_inv _ _ _ _ _ ST) as (r & Hr & Eh & _ & _ & _).
  apply brk_r_ok_query in Hr. subst r.
  destruct ST as (_ & (r' & _ & _ & Emo') & _).
  pose proof (brk_model_next_query (m_vmmaps mo)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (pk_W _ _ _ _ _ P).
  apply (PK_same zd wb wm wp wb wm wp mo mo' P); rewrite ?Eh; try assumption; try reflexivity; try lia.
  rewrite Emo'. apply (proj2 (with_brk_next_fields mo _ _)).
Qed.

Lemma brk_model_next_misc h req r :
  vm_limit (brk_model_next h req r) = vm_limit h /\ vm_mmap_base (brk_model_next h req r) = vm_mmap_base h
  /\ vm_reserved (brk_model_next h req r) = vm_reserved h /\ vm_start_brk (brk_model_next h req r) = vm_start_brk h.
Proof. repeat split; reflexivity. Qed.

Lemma PK_brk_grow zd wb wm wp mo rsp mo' evs req :
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req <= b + 2 * PGSZ ->
  2 * PGSZ <= wb -> 1 <= wm -> 2 <= wp ->
  PK zd wb wm wp mo -> nstep (NBrk req) mo rsp mo' evs -> PK zd (wb - 2 * PGSZ) (wm - 1) (wp - 2) mo'.
Proof.
  intros h b. subst h b. set (h := m_vmmaps mo). set (b := bv_unsigned (vm_brk h)). intros Hb Hsb Hreq Wb Wm Wp P ST.
  pose proof (pk_brk _ _ _ _ _ P) as PB. fold h b in PB. pose proof BRKTOP_HIGH as BH. unfold PGSZ, HIGH in *.
  assert (R64 : b < req < 2^64) by lia.
  destruct (nstep_brk_inv _ _ _ _ _ ST) as (r & Hr & Eh & _ & _ & _). fold h in Hr, Eh.
  destruct ST as (_ & (r' & _ & _ & Emo') & _).
  pose proof (proj2 (with_brk_next_fields mo (Z_to_bv 64 req) r')) as LM. rewrite <- Emo' in LM.
  pose proof (brk_model_next_misc h (Z_to_bv 64 req) r) as (M1 & M2 & M3 & M4).
  destruct (brk_r_ok_grow mo req r Hsb R64 Hr) as [->|[-> GO]].
  - pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    apply (PK_same zd wb wm wp _ _ _ mo mo' P); rewrite ?Eh; auto; lia.
  - pose proof (brk_model_next_grown h req Hb R64) as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. fold h in Zn, Sb, Bk, Cn, Rv, Bc, Lm, Bs. unfold PGSZ in *.
    constructor; rewrite ?Eh, ?Q1, ?Q2, ?Q4, ?Q5, ?M1, ?M2; rewrite ?unsigned_lit by lia; unfold PGSZ; auto; try lia.
    + intros e [<-|He].
      * left. unfold elo, ehi; cbn [fst snd]. rewrite unsigned_lit by lia. fold b. lia.
      * destruct (Zn e He) as [[Z1 Z2]|Z3]; [left| right; exact Z3]. fold b in Z2. lia.
    + cbn [length]. lia.
    + rewrite live_bytes_cons. unfold esz; cbn [snd]. rewrite unsigned_lit by lia. nia.
Qed.

Lemma mkVmMapsFull_fields r m na sb b lim mb sp :
  vm_reserved (mkVmMapsFull r m na sb b lim mb sp) = r /\ vm_maps (mkVmMapsFull r m na sb b lim mb sp) = m
  /\ vm_start_brk (mkVmMapsFull r m na sb b lim mb sp) = sb /\ vm_brk (mkVmMapsFull r m na sb b lim mb sp) = b
  /\ vm_limit (mkVmMapsFull r m na sb b lim mb sp) = lim /\ vm_mmap_base (mkVmMapsFull r m na sb b lim mb sp) = mb.
Proof. repeat split; reflexivity. Qed.

Lemma m_vm_materialized_with_mmap_backing_plain a n m :
  m_vm_materialized (with_mmap_backing (Z_to_bv 64 MAPF) a n m) = m_vm_materialized m.
Proof. rewrite with_mmap_backing_noreserve_false by reflexivity. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing_plain a n m :
  m_vmmaps (with_mmap_backing (Z_to_bv 64 MAPF) a n m) = m_vmmaps m.
Proof. rewrite with_mmap_backing_noreserve_false by reflexivity. reflexivity. Qed.

Lemma PK_mmap zd wb wm wp mo rsp mo' evs L pbrk len prot :
  KL L pbrk mo -> PK zd wb wm wp mo -> 0 < len <= LMAX -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  round_up_pg len <= wb -> 1 <= wm ->
  (zd = true -> errno_of (eff_ret rsp) = None -> HIGH <= bv_unsigned (eff_ret rsp)) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> PK zd (wb - round_up_pg len) (wm - 1) wp mo'.
Proof.
  intros K P Hl Hp Wb Wm HHI ST. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  pose proof (MBound.round_up_pg_ge len) as RG. pose proof (KL_top_bracket _ _ _ K) as TB.
  assert (SR : forall r ws zs us cs, Nodes.strip rsp = mkEffectU r ws zs us cs [] -> eff_ret rsp = r).
  { intros r ws zs us cs E. destruct rsp as [r0 ws0 zs0 us0 cs0 ci0]. rewrite strip_mk in E. injection E. auto. }
  destruct ST as [_ ST]. cbv zeta in ST.
  destruct ST as [(e & He & Hs & ->)|[(_ & a & PL & _ & Hs & Emo')|[(_ & _ & a & PL & Hs & Emo')|(M1 & M2 & M3 & _)]]].
  - eapply (PK_same zd wb wm wp); eauto; lia.
  - destruct PL as (A1 & A2 & A3 & A4 & A5). rewrite unsigned_lit in * by (unfold LMAX in Hl; lia).
    assert (HA : zd = true -> HIGH <= bv_unsigned a).
    { intros Hzd. rewrite <- (SR _ _ _ _ _ Hs). apply (HHI Hzd). rewrite (SR _ _ _ _ _ Hs). apply errno_of_small. pose proof (mmap_len_bound len ltac:(lia)). unfold mmap_len in *. lia. }
    rewrite <- KStep.round_up_pg_eq in *.
    assert (RU : round_up_pg len <= LMAX).
    { pose proof (MBound.round_up_pg_mono len LMAX ltac:(lia)). rewrite (MBound.round_up_pg_id LMAX) in H by reflexivity. exact H. }
    destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. subst mo'. constructor; rewrite ?m_vmmaps_with_mmap_backing_plain, ?m_vm_materialized_with_mmap_backing_plain,
      ?m_vmmaps_with_vmmaps, ?m_vm_materialized_with_vmmaps;
      cbn [vm_maps vm_reserved vm_start_brk vm_brk vm_limit vm_mmap_base length]; auto; try lia.
    + intros e [<-|He]; [| exact (Zn e He)]. right. unfold elo, esz; cbn [fst snd]. rewrite unsigned_lit by (unfold LMAX in *; lia). split; [intros Hzd; exact (HA Hzd)| lia].
    + rewrite live_bytes_cons. unfold esz; cbn [snd]. rewrite unsigned_lit by (unfold LMAX in *; lia). lia.
  - destruct PL as (A1 & A2 & A3 & A4 & A5). rewrite unsigned_lit in * by (unfold LMAX in Hl; lia).
    assert (HA : zd = true -> HIGH <= bv_unsigned a).
    { intros Hzd. rewrite <- (SR _ _ _ _ _ Hs). apply (HHI Hzd). rewrite (SR _ _ _ _ _ Hs). apply errno_of_small. pose proof (mmap_len_bound len ltac:(lia)). unfold mmap_len in *. lia. }
    rewrite <- KStep.round_up_pg_eq in *.
    assert (RU : round_up_pg len <= LMAX).
    { pose proof (MBound.round_up_pg_mono len LMAX ltac:(lia)). rewrite (MBound.round_up_pg_id LMAX) in H by reflexivity. exact H. }
    destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. subst mo'. constructor; rewrite ?m_vmmaps_with_mmap_backing_plain, ?m_vm_materialized_with_mmap_backing_plain,
      ?m_vmmaps_with_vmmaps, ?m_vm_materialized_with_vmmaps;
      cbn [vm_maps vm_reserved vm_start_brk vm_brk vm_limit vm_mmap_base length]; auto; try lia.
    + intros e [<-|He]; [| exact (Zn e He)]. right. unfold elo, esz; cbn [fst snd]. rewrite unsigned_lit by (unfold LMAX in *; lia). split; [intros Hzd; exact (HA Hzd)| lia].
    + rewrite live_bytes_cons. unfold esz; cbn [snd]. rewrite unsigned_lit by (unfold LMAX in *; lia). lia.
  - exfalso. destruct Hp as [-> | ->]; [revert M2| revert M1]; vm_compute; discriminate.
Qed.

Lemma m_vmmaps_with_mmap_replacement_x a n m :
  m_vmmaps (with_mmap_replacement (Z_to_bv 64 MAPFX) a n m) = m_vmmaps m
  /\ (length (m_vm_materialized (with_mmap_replacement (Z_to_bv 64 MAPFX) a n m)) <= length (m_vm_materialized m))%nat.
Proof.
  unfold with_mmap_replacement. rewrite with_mmap_backing_noreserve_false by reflexivity.
  rewrite m_vmmaps_vm_forget_range, m_vm_materialized_vm_forget_range. split; [reflexivity| apply length_filter_le].
Qed.
Lemma m_vmmaps_with_mmap_destroyed a n h' m :
  m_vmmaps (with_mmap_destroyed a n h' m) = h'
  /\ (length (m_vm_materialized (with_mmap_destroyed a n h' m)) <= length (m_vm_materialized m))%nat.
Proof.
  unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range, m_vm_materialized_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_materialized_with_vmmaps.
  split; [reflexivity| apply length_filter_le].
Qed.

Lemma PK_mmap_fixed zd wb wm wp mo rsp mo' evs L pbrk a :
  KL L pbrk mo -> PK zd wb wm wp mo -> a = bv_unsigned (vm_start_brk (m_vmmaps mo)) ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs -> PK zd wb wm wp mo'.
Proof.
  intros K P Ha ST. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  pose proof (kl_wf _ _ _ K) as [WF _]. pose proof (pk_sb _ _ _ _ _ P) as SB.
  pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
  destruct ST as [_ ST]. cbv zeta in ST.
  destruct ST as [(e & He & Hs & ->)|[(M1 & _)|[(_ & M1 & _)|(_ & _ & _ & HX)]]].
  - eapply (PK_same zd wb wm wp); eauto; lia.
  - exfalso. revert M1. vm_compute. discriminate.
  - exfalso. revert M1. vm_compute. discriminate.
  - destruct HX as [(Hs & ->)|(e & He & Hs & ->)].
    + pose proof (m_vmmaps_with_mmap_replacement_x (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))))
        (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (vm_maps (m_vmmaps mo))
          ((Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) ::
             maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned (Z_to_bv 64 a))
             (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))))))
           (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo)) as [E1 E2].
      rewrite m_vmmaps_with_vmmaps, m_vm_materialized_with_vmmaps in *.
      eapply (PK_same zd wb wm wp); [exact P| rewrite E1; reflexivity ..| exact E2| lia| lia| lia].
    + exfalso. unfold mmap_destructive_errnos in He. destruct He.
Qed.

Lemma PK_munmap zd wb wm wp mo rsp mo' evs a len :
  PK zd wb wm wp mo -> nstep (NMunmap a len) mo rsp mo' evs -> PK zd wb wm wp mo'.
Proof.
  intros P ST. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  destruct ST as [_ ST]. cbv zeta in ST. destruct ST as [Hs ->].
  match goal with |- PK _ _ _ _ (with_mmap_destroyed ?x ?y ?h ?m) => pose proof (m_vmmaps_with_mmap_destroyed x y h m) as [E1 E2] end.
  destruct P as [Zn Sb Bk Cn Rv Bc Lm Bs Wn]. constructor; rewrite ?E1; cbn [vm_maps vm_reserved vm_start_brk vm_brk vm_limit vm_mmap_base]; auto; try lia.
  - intros e He. apply Zn. eapply In_map_remove. exact He.
  - pose proof (length_map_remove_le (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a)). lia.
  - pose proof (lb_map_remove_le (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a)). nia.
Qed.

Lemma PK_mprotect zd wb wm wp wb' mo rsp mo' evs a len prot :
  PK zd wb wm wp mo -> 0 <= wb' <= wb -> nstep (NMprotect a len prot) mo rsp mo' evs -> PK zd wb' wm wp mo'.
Proof.
  intros P Hb ST. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  destruct ST as [_ ST]. cbv zeta in ST. destruct ST as [(e & He & Hs & ->)|(Hbud & Hs & ->)].
  - eapply (PK_same zd wb wm wp); eauto; lia.
  - unfold mprotect_model_next. eapply (PK_same zd wb wm wp); [exact P| rewrite m_vmmaps_with_vmmaps; reflexivity ..| rewrite m_vm_materialized_with_vmmaps; lia| lia|lia|lia].
Qed.

Lemma brk_ns_of_nonrefusal : forall req mo eff,
  brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff) = false ->
  ~ spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo eff.
Proof.
  intros req mo eff H. apply spurious_refusal_not_refusal.
  assert (E : bv_unsigned (in_sysno (pure_input 214 [Z_to_bv 64 req])) = 214) by reflexivity.
  rewrite (refusal_b_214 _ _ _ E). cbn [in_arg in_args pure_input nth]. exact H.
Qed.

Lemma brk_query_nonrefusal : forall mo r, brk_refusal_b mo (Z_to_bv 64 0) r = false.
Proof. intros mo r. unfold brk_refusal_b. change (w_is0 (Z_to_bv 64 0)) with true. reflexivity. Qed.

Lemma nstep_brk_intro req mo r :
  brk_r_ok mo (Z_to_bv 64 req) r = true ->
  ~ spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo
      (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] []) ->
  nstep (NBrk req) mo (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
        (with_brk_next mo (Z_to_bv 64 req) r) [].
Proof. intros Hr Hns. cbn [nstep]. split; [reflexivity|]. split; [exists r; rewrite strip_mk; auto| exact Hns]. Qed.

Lemma brk_r_ok_refuse mo req : brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  unfold brk_r_ok.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo)))); [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo))); [rewrite bv_eqb_refl; apply orb_true_r|].
  rewrite bv_eqb_refl, orb_true_r. cbn [andb]. unfold brk_grow_ok, brk_budget_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma nstep_brk_exists req mo : exists rsp mo', nstep (NBrk req) mo rsp mo' [].
Proof.
  set (i := pure_input 214 [Z_to_bv 64 req]).
  assert (Hno : bv_unsigned (in_sysno i) = 214) by reflexivity.
  assert (OUT : forall o, syscall_spec i mo o <->
            exists r, brk_r_ok mo (Z_to_bv 64 req) r = true /\
              o = LinuxProcessSemantics.LinuxProcessSem.Monad.Ok (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo)))
                                (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
                     (with_brk_next mo (Z_to_bv 64 req) r) []).
  { intros o. rewrite (RelSpec.syscall_spec_214 _ _ _ Hno). apply RelSpec.brk_outcome. }
  assert (H0 : syscall_spec i mo
    (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok (mkEffectU (vm_brk (m_vmmaps mo)) [] (brk_zeros (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)))
                   (brk_unmaps (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))) [] [])
        (with_brk_next mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo))) [])).
  { apply OUT. exists (vm_brk (m_vmmaps mo)). split; [apply brk_r_ok_refuse| reflexivity]. }
  destruct (exists_nonspurious ACFG i mo _ _ _ H0) as (eff & mo' & evs & Hs & Hns).
  apply OUT in Hs. destruct Hs as (r & Hr & E). injection E as E1 E2 E3. subst eff mo' evs.
  eexists _, _. apply nstep_brk_intro; [exact Hr| exact Hns].
Qed.

Lemma nstep_mmap_fixed_done_intro a mo :
  let h := m_vmmaps mo in let A := Z_to_bv 64 a in let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) in
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo (mkEffectU A [] [] [(A, n)] [] [])
        (with_mmap_replacement (Z_to_bv 64 MAPFX) A n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
              ((A, n) :: maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) [].
Proof.
  cbn [nstep]. split; [reflexivity|]. right. right. right.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  left. rewrite strip_mk. split; reflexivity.
Qed.

Lemma nstep_munmap_intro a len mo :
  let h := m_vmmaps mo in let A := Z_to_bv 64 a in let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in
  nstep (NMunmap a len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] [])
        (with_mmap_destroyed A n
           (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
              (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) [].
Proof. cbn [nstep]. split; [reflexivity|]. rewrite strip_mk. split; reflexivity. Qed.

Lemma m_vm_lazy_with_vmmaps v m : m_vm_lazy (with_vmmaps v m) = m_vm_lazy m.
Proof. destruct m; reflexivity. Qed.

Lemma PK_backing_room zd wb wm wp L pbrk mo mo' :
  KL L pbrk mo -> PK zd wb wm wp mo -> m_vm_lazy mo' = [] ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> m_vm_materialized mo' = m_vm_materialized mo ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  vm_backing_used mo' + wb <= vm_limit (m_vmmaps mo').
Proof.
  intros K P HL E1 E2 E3. pose proof (vm_backing_used_le _ HL) as U. rewrite E1, E2, E3 in *.
  pose proof (pk_back _ _ _ _ _ P) as BK. pose proof (pk_lim _ _ _ _ _ P) as LM. rewrite page_size_val in U. lia.
Qed.

Lemma nstep_mprotect_ok_intro zd wb wm wp L pbrk a len prot mo :
  let A := Z_to_bv 64 a in let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in
  KL L pbrk mo -> PK zd wb wm wp mo ->
  nstep (NMprotect a len prot) mo (mkEffect (Z_to_bv 64 0) [] [(A, n)]) (mprotect_model_next mo A n) [].
Proof.
  intros A n K P. subst A n. cbn [nstep]. split; [reflexivity|]. right. rewrite strip_mk. split; [| split; reflexivity].
  unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  match goal with |- vm_backing_used ?m <= _ => epose proof (PK_backing_room zd wb wm wp L pbrk mo m K P) as R end.
  unfold mprotect_model_next in *. rewrite m_vm_lazy_with_vmmaps, !m_vmmaps_with_vmmaps, m_vm_materialized_with_vmmaps in *.
  cbn [vm_maps vm_limit] in *. specialize (R (minv_nolazy _ (kl_minv _ _ _ K)) eq_refl eq_refl eq_refl). lia.
Qed.

Lemma PK_gap zd wb wm wp mo L pbrk n :
  KL L pbrk mo -> PK zd wb wm wp mo -> 0 < n <= LMAX -> vm_gap_available (m_vmmaps mo) n = true.
Proof.
  intros K P Hn. set (h := m_vmmaps mo).
  pose proof (kl_resv_top _ _ _ K) as RT. pose proof (kl_start _ _ _ K) as (S1 & S2 & S3 & S4).
  pose proof (pk_sb _ _ _ _ _ P) as SB. pose proof (pk_brk _ _ _ _ _ P) as PB.
  pose proof (pk_cnt _ _ _ _ _ P) as CN. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3). pose proof (pk_back _ _ _ _ _ P) as BK.
  pose proof (KL_top_bracket _ _ _ K) as TB. pose proof BRKTOP_HIGH as BH. fold h in RT, S1, S2, S3, S4, SB, PB, CN, BK, TB.
  assert (PG : PGSZ = 4096) by reflexivity.
  apply (vm_gap_available_of_cost h n HIGH); [unfold HIGH; lia| reflexivity| lia|].
  rewrite gap_cost_app.
  assert (R0 : gap_cost n HIGH (vm_reserved h) = 0).
  { rewrite gap_cost_eq, bytes_above_low, nabove_low; [lia| |]; intros e He; specialize (RT e He);
      change (vhi e) with (ehi e); unfold BRKTOP, SBMAX, HIGH in *; nia. }
  rewrite R0.
  assert (CM : gap_cost n HIGH (vm_maps h) <= BACKTOP + MAPTOP * (n + 4095)).
  { apply gap_cost_le; [lia| |].
    - etransitivity; [apply bytes_above_le_live|]. pose proof (live_bytes_nonneg (vm_maps h)). nia.
    - pose proof (nabove_le_length HIGH (vm_maps h)). lia. }
  unfold HIGH, BACKTOP, MAPTOP, BM, KTOP, LMAX in *. cbn in CM |- *. lia.
Qed.

Lemma PK_not_forced_mmap zd wb wm wp mo L pbrk len prot :
  KL L pbrk mo -> PK zd wb wm wp mo -> 0 < len <= LMAX -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  round_up_pg len <= wb -> nmmap_refusable mo len prot MAPF = false.
Proof.
  intros K P Hl Hp Wb. pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (RU : round_up_pg len <= LMAX).
  { pose proof (MBound.round_up_pg_mono len LMAX ltac:(lia)). rewrite (MBound.round_up_pg_id LMAX) in H by reflexivity. exact H. }
  assert (NE : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = round_up_pg len).
  { rewrite unsigned_lit by (unfold LMAX in Hl; lia). rewrite <- KStep.round_up_pg_eq. reflexivity. }
  pose proof (MBound.round_up_pg_ge len) as RG.
  pose proof (PK_gap zd wb wm wp mo L pbrk (round_up_pg len) K P ltac:(lia)) as GAP.
  unfold nmmap_refusable. rewrite NE. destruct Hp as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota.
    unfold mmap_reserve_refusable. rewrite GAP. reflexivity.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota.
    unfold mmap_grant_refusable. rewrite GAP.
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota.
    pose proof (vm_backing_used_le mo (minv_nolazy _ (kl_minv _ _ _ K))) as U. rewrite page_size_val in U.
    pose proof (pk_back _ _ _ _ _ P) as BK. pose proof (pk_lim _ _ _ _ _ P) as LM.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma PK_not_forced_mprotect zd wb wm wp mo L pbrk a len :
  KL L pbrk mo -> PK zd wb wm wp mo ->
  mprotect_refusable mo (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = false.
Proof.
  intros K P. unfold mprotect_refusable. apply (f_equal negb) with (y := true).
  unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  match goal with |- vm_backing_used ?m <= _ => epose proof (PK_backing_room zd wb wm wp L pbrk mo m K P) as R end.
  unfold mprotect_model_next in *. rewrite m_vm_lazy_with_vmmaps, !m_vmmaps_with_vmmaps, m_vm_materialized_with_vmmaps in *.
  cbn [vm_maps vm_limit] in *. specialize (R (minv_nolazy _ (kl_minv _ _ _ K)) eq_refl eq_refl eq_refl). lia.
Qed.

Lemma PK_mmap_not_refused zd wb wm wp mo L pbrk len prot rsp mo' evs e :
  KL L pbrk mo -> PK zd wb wm wp mo -> 0 < len <= LMAX -> (prot = PROT_NONE \/ prot = PROT_RW) -> round_up_pg len <= wb ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> Nodes.strip rsp = efferr e -> 1 <= e <= 4095 -> False.
Proof.
  intros K P Hl Hp Wb ST Hs He.
  destruct (nstep_mmap_err_forced _ _ _ _ _ _ _ _ _ ST Hs He) as (F & _).
  rewrite (PK_not_forced_mmap zd wb wm wp mo L pbrk len prot K P Hl Hp Wb) in F. discriminate F.
Qed.

Lemma PK_mprotect_not_refused zd wb wm wp mo L pbrk a len prot rsp mo' evs e :
  KL L pbrk mo -> PK zd wb wm wp mo ->
  nstep (NMprotect a len prot) mo rsp mo' evs -> Nodes.strip rsp = efferr e -> 1 <= e <= 4095 -> False.
Proof.
  intros K P ST Hs He.
  destruct (nstep_mprotect_err_forced _ _ _ _ _ _ _ _ ST Hs He) as (F & _).
  rewrite (PK_not_forced_mprotect zd wb wm wp mo L pbrk a len K P) in F. discriminate F.
Qed.

Lemma nstep_mmap_fixed_cases a mo rsp mo' evs :
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  let h := m_vmmaps mo in let A := Z_to_bv 64 a in let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) in
  evs = [] /\ Nodes.strip rsp = mkEffectU A [] [] [(A, n)] [] [] /\
  mo' = with_mmap_replacement (Z_to_bv 64 MAPFX) A n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
              ((A, n) :: maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo).
Proof.
  intros [-> ST]. cbv zeta in ST. cbv zeta. split; [reflexivity|].
  destruct ST as [(e & He & Hs & ->)|[(M1 & _)|[(_ & M1 & _)|(_ & _ & _ & HX)]]].
  - exfalso. apply mmap_errnos_when_forced in He. revert He. unfold nmmap_refusable. vm_compute. discriminate.
  - exfalso. revert M1. vm_compute. discriminate.
  - exfalso. revert M1. vm_compute. discriminate.
  - destruct HX as [(Hs & ->)|(e & He & Hs & ->)]; [split; [exact Hs| reflexivity]|].
    exfalso. exact (mmap_destructive_errnos_False _ He).
Qed.

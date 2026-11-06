(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe STree Malloc ProgP KInv KStep KLink KEv Relim StepB Gap NFKern LB_Kernel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition abovef (e : word * word) : bool := FLOOR <? ghi e.
Definition kcnt (l : list (word * word)) : Z := Z.of_nat (length (List.filter abovef l)).
Definition gabove (g : Z * Z) : bool := FLOOR <? fst g + mmap_len (snd g).
Definition mabove (m : Z * Z * Z) : bool := FLOOR <? fst (fst m) + mmap_len (snd (fst m)).
Definition lcnt (L : mled) : Z :=
  Z.of_nat (length (List.filter gabove (ld_groups L))) + Z.of_nat (length (List.filter mabove (ld_metas L))).

Lemma kcnt_cons e l : kcnt (e :: l) = (if abovef e then 1 else 0) + kcnt l.
Proof. unfold kcnt. cbn. destruct (abovef e); cbn [length]; lia. Qed.
Lemma kcnt_app l1 l2 : kcnt (l1 ++ l2) = kcnt l1 + kcnt l2.
Proof. unfold kcnt. rewrite filter_app, length_app. lia. Qed.
Lemma kcnt_nonneg l : 0 <= kcnt l.
Proof. unfold kcnt. lia. Qed.

Lemma lcnt_le_len L : lcnt L <= Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)).
Proof. unfold lcnt. pose proof (length_filter_le gabove (ld_groups L)). pose proof (length_filter_le mabove (ld_metas L)). lia. Qed.

Lemma lcnt_set_brkph v L : lcnt (set_brkph v L) = lcnt L. Proof. reflexivity. Qed.
Lemma lcnt_set_brkreg v L : lcnt (set_brkreg v L) = lcnt L. Proof. reflexivity. Qed.
Lemma lcnt_set_live v L : lcnt (set_live v L) = lcnt L. Proof. reflexivity. Qed.
Lemma lcnt_add_group a len L :
  lcnt (set_groups ((a, len) :: ld_groups L) L) = (if gabove (a, len) then 1 else 0) + lcnt L.
Proof. unfold lcnt. cbn. destruct (gabove (a, len)); cbn [length]; lia. Qed.
Lemma lcnt_add_meta a len L :
  lcnt (set_metas ((a, len, 0) :: ld_metas L) L) = (if mabove (a, len, 0) then 1 else 0) + lcnt L.
Proof. unfold lcnt. cbn. destruct (mabove (a, len, 0)); cbn [length]; lia. Qed.
Lemma lcnt_bump a L : lcnt (set_metas (map (bump_meta a) (ld_metas L)) L) = lcnt L.
Proof.
  unfold lcnt. cbn [ld_groups ld_metas set_metas]. f_equal. f_equal.
  induction (ld_metas L) as [|[[b l] k] ms IH]; [reflexivity|]. cbn [map List.filter].
  assert (E : mabove (bump_meta a (b, l, k)) = mabove (b, l, k)).
  { unfold bump_meta. destruct (b + (1 + k) * PGSZ =? a); reflexivity. }
  rewrite E. destruct (mabove (b, l, k)); cbn [length]; rewrite IH; reflexivity.
Qed.

Lemma g_remove_notin a (l : list (Z * Z)) : ~ In a (map fst l) -> g_remove a l = l.
Proof.
  induction l as [|[b n] l IH]; intros NI; [reflexivity|]. cbn. destruct (Z.eqb_spec b a) as [->|NE].
  - exfalso. apply NI. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros Hin. apply NI. right. exact Hin.
Qed.

Lemma lcnt_remove_group L a l0 : List.NoDup (map fst (ld_groups L)) -> In (a, l0) (ld_groups L) ->
  lcnt (set_groups (g_remove a (ld_groups L)) L) = lcnt L - (if gabove (a, l0) then 1 else 0).
Proof.
  unfold lcnt. cbn [ld_groups ld_metas set_groups]. intros ND Hin.
  enough (E : Z.of_nat (length (List.filter gabove (g_remove a (ld_groups L)))) =
             Z.of_nat (length (List.filter gabove (ld_groups L))) - (if gabove (a, l0) then 1 else 0)) by lia.
  revert ND Hin. generalize (ld_groups L). intros gs ND Hin.
  induction gs as [|[b n] gs IH]; [destruct Hin|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  cbn [g_remove fst]. destruct (Z.eqb_spec b a) as [->|NE].
  - destruct Hin as [E|Hin].
    + injection E as ->. cbn. destruct (gabove (a, l0)); cbn [length]; lia.
    + exfalso. apply NI. apply in_map_iff. exists (a, l0). auto.
  - destruct Hin as [E|Hin]; [injection E; intros; subst; congruence|].
    cbn. specialize (IH ND' Hin). destruct (gabove (b, n)); cbn [length]; lia.
Qed.

Lemma kcnt_map_remove maps aw nw : In (aw, nw) maps ->
  kcnt (map_remove maps aw) <= kcnt maps - (if abovef (aw, nw) then 1 else 0).
Proof.
  intros Hin. unfold map_remove. induction maps as [|e l IH]; [destruct Hin|].
  cbn [List.filter]. destruct Hin as [->|Hin].
  - cbn [fst]. rewrite bv_eqb_refl. cbn [negb]. rewrite kcnt_cons.
    assert (kcnt (List.filter (fun p : word * word => negb (bv_eqb (fst p) aw)) l) <= kcnt l); [|destruct (abovef (aw, nw)); lia].
    clear IH. induction l as [|e' l' IH']; cbn [List.filter]; [lia|]. destruct (negb _); rewrite ?kcnt_cons; destruct (abovef e'); lia.
  - specialize (IH Hin). destruct (negb (bv_eqb (fst e) aw)); rewrite ?kcnt_cons; destruct (abovef e); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LNstat (h : VmMaps) : Prop :=
  bv_unsigned (vm_start_brk h) + 2^31 + 8 * PGSZ <= FLOOR      (* [comment removed for export] *)
  /\ 2^31 <= vm_limit h
  /\ live_bytes (vm_reserved h) <= 2^30.

Definition LN (L : mled) (mo : Model) : Prop :=
  kcnt (vm_maps (m_vmmaps mo)) <= lcnt L
  /\ LNstat (m_vmmaps mo)
  /\ (forall b l, ld_brkreg L = Some (b, l) -> b = bv_unsigned (vm_start_brk (m_vmmaps mo))).

Lemma LN_intro L mo : kcnt (vm_maps (m_vmmaps mo)) <= lcnt L -> LNstat (m_vmmaps mo) ->
  (forall b l, ld_brkreg L = Some (b, l) -> b = bv_unsigned (vm_start_brk (m_vmmaps mo))) -> LN L mo.
Proof. intros. split; [|split]; assumption. Qed.

(* [comment removed for export] *)
Lemma LN_frame L L' mo mo' :
  LN L mo ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) -> vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  lcnt L' = lcnt L -> ld_brkreg L' = ld_brkreg L ->
  LN L' mo'.
Proof.
  intros (C & (S1 & S2 & S3) & B) E1 E2 E3 E4 E5 E6. split; [|split].
  - rewrite E1, E5. exact C.
  - unfold LNstat. rewrite E2, E3, E4. auto.
  - rewrite E6, E2. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_model_next_limit' : forall h req r, vm_limit (brk_model_next h req r) = vm_limit h.
Proof. reflexivity. Qed.

Lemma ln_brk0 L pbrk mo rsp mo' evs z : KL L pbrk mo -> LN L mo -> ld_brk L = BPUntried ->
  nstep (NBrk 0) mo rsp mo' evs -> LN (set_brkph (BPQueried z) L) mo'.
Proof.
  intros HK HL Hph Hst. destruct (nstep_brk_inv 0 mo rsp mo' evs Hst) as (r & Hok & -> & _ & _).
  apply brk_r_ok_query in Hok. subst r. destruct (brk_model_next_query (m_vmmaps mo)) as (E1 & E2 & _ & E4 & _).
  rewrite with_brk_next_noshrink by lia.
  apply (LN_frame L _ mo); [exact HL| | | | | reflexivity| reflexivity]; rewrite m_vmmaps_with_vmmaps; [exact E2| exact E4| reflexivity| exact E1].
Qed.

(* [comment removed for export] *)
Lemma ln_brk_grow L pbrk mo rsp mo' evs req a :
  KL L pbrk mo -> LN L mo -> BB L + PGSZ <= 2^31 ->
  ((exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
   \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)) ->
  nstep (NBrk req) mo rsp mo' evs -> dec_brk pbrk req rsp = Some a ->
  LN (event_post L (EBrk req) (match a with BrkGrown => req | BrkSame => pbrk end)) mo'.
Proof.
  intros HK HL HBB Hpre Hst Hd. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_lt _ _ _ HK) as HKat.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ HK) as P.
  pose proof HL as (C & (T1 & T2 & T3) & HBR).
  set (h := m_vmmaps mo) in *.
  assert (PH : bv_unsigned (vm_brk h) = pbrk /\ 0 < pbrk /\ pbrk < req /\ req + PGSZ <= FLOOR /\ req <> 0
               /\ (forall v, lcnt (set_brkph v L) = lcnt L)
               /\ ld_brkreg (set_brkph BPDead L) = ld_brkreg L).
  { destruct Hpre as [(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]; rewrite Hph in P.
    - destruct P as (Ecur & Ebrk & Epbrk & Hreg).
      rewrite (round_up_pg_aligned cur) by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *. repeat split; try reflexivity; try lia.
    - destruct P as (b' & l' & Hreg' & Ebrk & Epbrk). rewrite Hreg in Hreg'. inversion Hreg'; subst b' l'.
      pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _).
      pose proof (HBR b l Hreg) as Eb. unfold BB in HBB. rewrite Hph, Hreg in HBB.
      unfold PGSZ in *. repeat split; try reflexivity; lia. }
  destruct PH as (Ebrk & Hp0 & Hreq & HreqF & NZ & LC & BRd).
  pose proof FLOOR_val as FV. assert (HPG : PGSZ = 4096) by reflexivity.
  destruct (nstep_brk_inv req mo rsp mo' evs Hst) as (r & Hok & Emo' & Ersp & _). fold h in Hok, Emo', Ersp.
  unfold event_post. rewrite (proj2 (Z.eqb_neq _ _) NZ).
  pose proof (dec_brk_Some _ _ _ _ Hd) as (ci & SH).
  destruct a.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. assert (Er : r = Z_to_bv 64 req) by (inversion SH; reflexivity). subst r.
    destruct (brk_model_next_grown h req ltac:(lia) ltac:(lia)) as (Eres & Emaps & _ & Esb & _).
    rewrite Z.eqb_refl. rewrite Emo', with_brk_next_noshrink by (rewrite unsigned_lit by lia; fold h; lia).
    split; [|split].
    + rewrite m_vmmaps_with_vmmaps, Emaps, kcnt_cons.
      rewrite Ebrk. replace (abovef (vm_brk h, Z_to_bv 64 (req - pbrk))) with false.
      2:{ symmetry. unfold abovef, ghi, glo, gsz. cbn [fst snd]. rewrite unsigned_lit by lia. rewrite Ebrk. apply Z.ltb_ge. lia. }
      assert (LC2 : forall v, lcnt (set_brkreg v L) = lcnt L) by (intros; reflexivity).
      fold h in C.
      destruct (ld_brk L); rewrite ?LC; try lia; destruct (ld_brkreg L) as [[b l]|]; rewrite ?LC2; lia.
    + unfold LNstat. rewrite m_vmmaps_with_vmmaps, Esb, brk_model_next_limit', Eres. fold h. auto.
    + intros b l. rewrite m_vmmaps_with_vmmaps, Esb. fold h.
      destruct (ld_brk L); try (cbn; apply HBR).
      all: destruct (ld_brkreg L) as [[b0 l0]|] eqn:ER; cbn; [| intros E'; exfalso; clear -E' ER; congruence].
      all: intros E; injection E as <- <-; apply (HBR b0 l0); first [exact ER| reflexivity].
  - (* [comment removed for export] *)
    rewrite Ersp in SH. unfold eff0_ci in SH. assert (Er : r = Z_to_bv 64 pbrk) by (inversion SH; reflexivity).
    assert (Er' : r = vm_brk h) by (rewrite Er, <- Ebrk; apply Z_to_bv_bv_unsigned). clear Er. subst r.
    destruct (brk_model_next_same h (Z_to_bv 64 req)) as (Eres & Emaps & _ & Esb & _).
    replace (pbrk =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Emo', with_brk_next_noshrink by (fold h; lia).
    apply (LN_frame L _ mo); [exact HL| | | | | apply LC| exact BRd]; rewrite m_vmmaps_with_vmmaps; fold h;
      [exact Emaps| exact Esb| apply brk_model_next_limit'| exact Eres].
Qed.

(* [comment removed for export] *)
Lemma abovef_went a len : 0 < a -> 0 < len -> a + mmap_len len <= alloc_ceiling ->
  abovef (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) = gabove (a, len).
Proof.
  intros Ha Hl Hc. pose proof alloc_ceiling_lt. pose proof (mmap_len_ge len Hl).
  unfold abovef, gabove, ghi, glo, gsz. cbn [fst snd]. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma ln_mmap_rw L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LN L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs -> dec_mmap (ld_atop L) len [] rsp = Some x ->
  LN (event_post L (EMmap 0 len PROT_RW MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen. pose proof alloc_ceiling_lt as Hcl.
  pose proof (KL_atop_range _ _ _ HK) as HKat. pose proof (KL_atop_lt _ _ _ HK) as HKlt.
  destruct (nstep_dec_mmap (ld_atop L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) ltac:(rewrite (kl_atop _ _ _ HK); lia) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  rewrite (mm_post_eq L len PROT_RW (mm_val x)) by (right; reflexivity).
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. rewrite (is_err_neg ENOMEM) by (unfold ENOMEM; lia). exact HL.
  - destruct Hx as (Hok & _ & E). destruct (mmap_ok_not_err _ _ _ _ Hok ltac:(lia) (proj2 HKlt)) as [NE Ha]. rewrite NE.
    change (PROT_RW =? PROT_NONE) with false. cbv iota.
    apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _].
    pose proof HL as (C & ST & HBR). split; [|split].
    + rewrite E. cbn [vm_maps]. rewrite kcnt_cons, lcnt_add_group, (abovef_went a len) by lia. lia.
    + rewrite E. exact ST.
    + rewrite E. cbn. exact HBR.
Qed.

Lemma ln_mmap_none L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LN L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs -> dec_mmap_none (ld_atop L) len [] rsp = Some x ->
  LN (event_post L (EMmap 0 len PROT_NONE MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen. pose proof alloc_ceiling_lt as Hcl.
  pose proof (KL_atop_range _ _ _ HK) as HKat. pose proof (KL_atop_lt _ _ _ HK) as HKlt.
  destruct (nstep_dec_mmap_none (ld_atop L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) ltac:(rewrite (kl_atop _ _ _ HK); lia) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  rewrite (mm_post_eq L len PROT_NONE (mm_val x)) by (left; reflexivity).
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. rewrite (is_err_neg ENOMEM) by (unfold ENOMEM; lia). exact HL.
  - destruct Hx as (Hok & _ & E). destruct (mmap_ok_not_err _ _ _ _ Hok ltac:(lia) (proj2 HKlt)) as [NE Ha]. rewrite NE.
    change (PROT_NONE =? PROT_NONE) with true. cbv iota.
    apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _].
    pose proof HL as (C & ST & HBR). split; [|split].
    + rewrite E. cbn [vm_maps]. rewrite kcnt_cons, lcnt_add_meta. replace (mabove (a, len, 0)) with (gabove (a, len)) by reflexivity.
      rewrite (abovef_went a len) by lia. lia.
    + rewrite E. exact ST.
    + rewrite E. cbn. exact HBR.
Qed.

(* [comment removed for export] *)
Lemma dec_mmap_fixed_errno : forall addr len rsp x,
  dec_mmap_fixed addr len rsp = Some x -> match x with FxKept e | FxLost e => errno_of (eff_ret rsp) = Some e | FxDone => True end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mmap_fixed in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); [|discriminate]. injection H as <-. reflexivity.
  - destruct cs; [|discriminate]. destruct (_ && _); [|discriminate].
    destruct (errno_of r); [injection H as <-; reflexivity|]. destruct (bv_eqb r _); [|discriminate]. injection H as <-. exact I.
  - discriminate.
Qed.

Lemma fixed_gate_facts : forall L cur pbrk mo,
  KL L pbrk mo -> ld_brk L = BPGuard cur ->
  let h := m_vmmaps mo in let a := round_up_pg cur in
  a = cur /\ cur = bv_unsigned (vm_start_brk h)
  /\ 0 < a /\ a + 2 * PGSZ <= ld_atop L /\ a mod 4096 = 0
  /\ region_free (vm_reserved h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true.
Proof.
  intros L cur pbrk mo HK Hph h a. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_lt _ _ _ HK) as HKlt.
  pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in Ecur, Ebrk, He0, S1, S2, S3, S4.
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  split; [exact Ha|]. split; [exact Ecur|]. split; [lia|]. split; [lia|]. split; [rewrite Ha, Ecur; exact S2|]. split.
  - apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He.
  - unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in He0l, He0h.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity.
Qed.

Lemma ln_mmap_fixed L pbrk mo rsp mo' evs cur z :
  KL L pbrk mo -> LN L mo -> ld_brk L = BPGuard cur ->
  nstep (NMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  LN (event_post L (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) z) mo'.
Proof.
  intros HK HL Hph Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (kl_atop _ _ _ HK) as HKtop.
  destruct (fixed_gate_facts L cur pbrk mo HK Hph) as (Ea & Ecur & Pa & Ca & Aa & Rf & Mc).
  set (a := round_up_pg cur) in *.
  pose proof (NF_mmap_fixed a mo Pa ltac:(rewrite <- HKtop; unfold PGSZ in *; lia) Aa Rf Mc _ _ _ Hst) as NE.
  pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs Pa ltac:(rewrite <- HKtop; unfold PGSZ in *; lia) Aa Rf Mc Hst) as (_ & _ & x & Hd & Hx).
  pose proof (dec_mmap_fixed_errno _ _ _ _ Hd) as HE.
  destruct x as [e| |e]; [rewrite NE in HE; discriminate| | rewrite NE in HE; discriminate].
  assert (POST : forall z, event_post L (EMmap a PGSZ PROT_NONE MAPFX) z = set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) by reflexivity.
  rewrite POST. pose proof HL as (C & ST & HBR). split; [|split].
  - rewrite Hx. cbn [vm_maps]. rewrite lcnt_set_brkph, lcnt_set_brkreg. exact C.
  - rewrite Hx. exact ST.
  - rewrite Hx. cbn. intros b l E. injection E as <- <-. rewrite Ea. exact Ecur.
Qed.

(* [comment removed for export] *)
Lemma ln_munmap L pbrk mo rsp mo' evs a l0 len z :
  KL L pbrk mo -> LN L mo -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  LN (event_post L (EMunmap a len) z) mo'.
Proof.
  intros HK HL Hin Hlen Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). unfold LEN_MAX in A1.
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  assert (Hnn : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = mmap_len l0).
  { destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  pose proof (nstep_munmap_exact a len l0 mo rsp mo' evs A2 ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) ltac:(lia) Hlen1 Hlen2 A5 Hst) as Emaps.
  destruct (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(lia) Hst) as (_ & _ & x & _ & Hx).
  unfold went, wz in A5.
  assert (NOTSAME : mo' = mo -> False).
  { intros ->. assert (HinR : In (Z_to_bv 64 a, Z_to_bv 64 (mmap_len l0)) (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a))) by (rewrite <- Emaps; exact A5).
    unfold map_remove in HinR. apply filter_In in HinR as [_ HinR]. cbn [fst] in HinR. rewrite bv_eqb_refl in HinR. discriminate. }
  destruct x as [e|[|]]; [destruct Hx as [_ E]; destruct (NOTSAME E)| | destruct Hx as [E _]; destruct (NOTSAME E)].
  destruct Hx as [_ E].
  change (event_post L (EMunmap a len) z) with (set_groups (g_remove a (ld_groups L)) L).
  pose proof HL as (C & ST & HBR). split; [|split].
  - rewrite E. cbn [vm_maps].
    pose proof (kcnt_map_remove _ _ _ A5) as K. rewrite (abovef_went a l0) in K by lia.
    pose proof (kl_distinct _ _ _ HK) as ND. apply List.NoDup_app_remove_r in ND.
    rewrite (lcnt_remove_group L a l0 ND Hin). lia.
  - rewrite E. exact ST.
  - rewrite E. cbn. exact HBR.
Qed.

(* [comment removed for export] *)
Lemma ln_mprotect L pbrk mo rsp mo' evs b l k z :
  KL L pbrk mo -> LN L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  nstep (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  LN (event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z) mo'.
Proof.
  intros HK HL Hin Hk Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). unfold LEN_MAX in A1.
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  destruct (nstep_dec_mprotect (b + (1 + k) * PGSZ) PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(vm_compute; reflexivity) Hst) as (_ & _ & x & _ & Hx).
  assert (LC : forall L', (L' = L \/ L' = set_metas (map (bump_meta (b + (1 + k) * PGSZ)) (ld_metas L)) L) -> lcnt L' = lcnt L /\ ld_brkreg L' = ld_brkreg L).
  { intros L' [-> | ->]; [auto|]. split; [apply lcnt_bump| reflexivity]. }
  assert (POST : event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z = L
                 \/ event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z = set_metas (map (bump_meta (b + (1 + k) * PGSZ)) (ld_metas L)) L).
  { unfold event_post. destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); auto. }
  destruct (LC _ POST) as [E5 E6].
  destruct x as [e|[|]].
  - destruct Hx as [_ ->]. apply (LN_frame L _ mo); auto.
  - destruct Hx as (_ & _ & E). apply (LN_frame L _ mo); try assumption; rewrite E; reflexivity.
  - rewrite Hx. apply (LN_frame L _ mo); auto.
Qed.

(* [comment removed for export] *)
Lemma mprotect_gate_facts : forall L pbrk mo b l k, KL L pbrk mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  let n := mmap_len l in let a := b + (1 + k) * PGSZ in
  0 <= a /\ a + PGSZ < 2^64 /\ a mod 4096 = 0
  /\ map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true.
Proof.
  intros L pbrk mo b l k HK Hin Hk n a. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) n in Hk, A4, Ak1, A5, A6, Ana |- *.
  pose proof (mmap_len_pos_pg l ltac:(lia)) as Hnp. fold n in Hnp.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; nia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  unfold PGSZ in A3. split; [unfold PGSZ in *; nia|]. split; [unfold PGSZ in *; nia|]. split.
  { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
  split.
  - destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - unfold map_contains. apply existsb_exists. exists (went b n). split; [exact A5|]. rewrite Ua, Un. unfold went, wz. cbn [fst snd].
    rewrite !unsigned_lit by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gm_nonneg L pbrk mo : KL L pbrk mo -> 0 <= gm L.
Proof.
  intros HK. unfold gm.
  assert (G1 : forall l : list (Z * Z), (forall g, In g l -> 0 < snd g) -> 0 <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|a l IH]; cbn; intros H; [lia|]. pose proof (H a (or_introl eq_refl)). pose proof (mmap_len_ge (snd a) ltac:(lia)).
    specialize (IH ltac:(intros; apply H; right; assumption)). lia. }
  assert (G2 : forall l : list (Z * Z * Z), (forall m, In m l -> 0 < snd (fst m)) -> 0 <= fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) l)).
  { induction l as [|a l IH]; cbn; intros H; [lia|]. pose proof (H a (or_introl eq_refl)). pose proof (mmap_len_ge (snd (fst a)) ltac:(lia)).
    specialize (IH ltac:(intros; apply H; right; assumption)). lia. }
  specialize (G1 (ld_groups L) ltac:(intros [b l] Hin; cbn; pose proof (kl_groups _ _ _ HK b l Hin); lia)).
  specialize (G2 (ld_metas L) ltac:(intros [[b l] k] Hin; cbn; pose proof (kl_metas _ _ _ HK b l k Hin); lia)).
  lia.
Qed.

(* [comment removed for export] *)
Definition NMAX : Z := 2^17.
Definition RMAX : Z := 2^29 + 2^17.     (* [comment removed for export] *)

Lemma band_arith : (NMAX + 1) * (RMAX + 4095) + 2^35 <= CEIL - FLOOR.
Proof. rewrite CEIL_val, FLOOR_val. unfold NMAX, RMAX. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma N_band_le L pbrk mo : KL L pbrk mo -> LN L mo ->
  Z.of_nat (length (List.filter in_band_b (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)))) <= lcnt L.
Proof.
  intros HK (C & (S1 & _ & _) & _).
  rewrite filter_app, length_app, Nat2Z.inj_add.
  assert (R0 : length (List.filter in_band_b (vm_reserved (m_vmmaps mo))) = 0%nat).
  { pose proof (kl_resv_top _ _ _ HK) as RT.
    assert (G : forall e, In e (vm_reserved (m_vmmaps mo)) -> in_band_b e = false).
    { intros e He. specialize (RT e He). unfold in_band_b, ghi, glo, gsz. unfold ehi in RT.
      rewrite andb_false_iff. right. apply Z.ltb_ge. unfold PGSZ in S1. lia. }
    revert G. clear. generalize (vm_reserved (m_vmmaps mo)). intros l G.
    induction l as [|e r IH]; [reflexivity|]. cbn. rewrite (G e (or_introl eq_refl)). apply IH.
    intros e' He'. apply G. right. exact He'. }
  rewrite R0. cbn [Z.of_nat].
  assert (M : (length (List.filter in_band_b (vm_maps (m_vmmaps mo))) <= length (List.filter abovef (vm_maps (m_vmmaps mo))))%nat).
  { clear. induction (vm_maps (m_vmmaps mo)) as [|e r IH]; cbn; [lia|].
    unfold in_band_b at 1. unfold abovef at 1. destruct (glo e <? CEIL); cbn; destruct (FLOOR <? ghi e); cbn; lia. }
  unfold kcnt in C. lia.
Qed.

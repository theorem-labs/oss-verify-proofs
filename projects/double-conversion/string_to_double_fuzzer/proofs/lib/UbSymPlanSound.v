(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec SpecConsts LibWritev RefNodes UbExitBase UbLibCas UbLibCas2 Hoare Frame
  RefMemcpyLib UbMemcpyBase UbMemcpy
  MallocDefs UbEnframeBase RefEnframeArith UbEnframe UbGetMeta UbFreePro UbStdioDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots UbSymPlanSoundA SymPlanMerge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPS.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Export SPSA.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

(* [comment removed for export] *)
Lemma ISPAN_eq : ISPAN U0 = 0xd6000. Proof. reflexivity. Qed.
Lemma ITOP_eq : i_top U0 = 0xe6000. Proof. reflexivity. Qed.
Lemma IRW_eq : i_rw U0 = 0xb3000. Proof. reflexivity. Qed.
Lemma IRO_eq : i_ro U0 = 0xac000. Proof. reflexivity. Qed.
Lemma DSC_eq : d_sc U0 = 0x1abc8. Proof. reflexivity. Qed.

Section NX0.
Variable nx0 : nat.
(* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound RSEGS IT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FX1.
Context {fx : FPState}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

Lemma kentry_keep_sem : forall E M M' K lo n,
  kentry_ok RSEGS E M K -> kfoot_apart E K lo n ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  kentry_ok RSEGS E M' K.
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn RSEGS M' a k = rdn RSEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2]; cbn [kentry_ok] in *;
    try exact HK.
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (A & B & C). split; [exact A|]. split; [exact B|]. intros i Hi.
    rewrite Hout; [apply C; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview RSEGS M x).
    eapply (store_ok_all RSEGS M (S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Lemma kentry_apart_b_sem : forall E M allkn K ub uk un,
  know_ok RSEGS E M allkn -> kentry_apart_b allkn ub uk un K = true ->
  kfoot_apart E K (estart E (SA ub uk)) (elenZ E un).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

Lemma kentry_apart_keep : forall E M M' allkn K (ub : expr) uk un,
  know_ok RSEGS E M allkn -> kentry_ok RSEGS E M K ->
  kentry_apart_b allkn ub uk un K = true ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  kentry_ok RSEGS E M' K.
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

Lemma know_ok_filter_apart : forall E M M' k (f : kentry -> bool) (ub : expr) uk un,
  know_ok RSEGS E M k ->
  (forall K, In K k -> f K = true -> kentry_apart_b k ub uk un K = true \/ kentry_ok RSEGS E M' K) ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  know_ok RSEGS E M' (List.filter f k).
Proof.
  intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin Hfk].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
  eapply kentry_apart_keep; eassumption.
Qed.

(* [comment removed for export] *)
Lemma kentry_apart_bp_eq : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_unfill : forall E M k ub un,
  know_ok RSEGS E M k -> flat E (SA ub 0) (elenZ E un) ->
  know_ok RSEGS E (unfill (edenot E ub) (edenot E un) M) (kn_unfill k ub 0 un).
Proof.
  intros E M k ub un HK Hfl. rewrite kn_unfill_eq. (* [comment removed for export] *) unfold kn_unfill_ref.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  cbv zeta. eapply know_ok_filter_apart; [exact HK | |].
  - intros K Hin Hf. cbv beta in Hf. rewrite kentry_apart_bp_eq in Hf.   (* [comment removed for export] *)
    apply orb_prop in Hf as [Himg|Ha]; [|left; exact Ha].
    right. destruct K; try discriminate. cbn [kentry_ok].
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as (A & B & C). split; [exact A|]. split; [exact B|].
    intros i Hi. unfold unfill. rewrite (C i Hi). destruct (_ && _)%bool; reflexivity.
  - intros x Hx. apply unfill_out. fold (elenZ E un).
    unfold estart in Hx. cbn [a_base a_off] in Hx. unfold estart in Hu. cbn [a_base a_off] in Hu.
    unfold adenot, v_addi in Hu. cbn [a_base a_off] in Hu. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hu. lia.
Qed.

(* [comment removed for export] *)

Lemma seps_In2 : forall l p q, seps l -> In p l -> In q l -> p = q \/ iv_disjoint p q.
Proof.
  intros l p q Hs. induction Hs as [|r l Hf Hs IH]; intros Hp Hq; [destruct Hp|].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - left; reflexivity.
  - right. exact (proj1 (Forall_forall _ _) Hf q Hq).
  - right. pose proof (proj1 (Forall_forall _ _) Hf p Hp) as H. unfold iv_disjoint in *. lia.
  - exact (IH Hp Hq).
Qed.

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l Hs. induction Hs as [|p l Hf Hs IH]; cbn [List.filter]; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma Forall_filter : forall {A} (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma map_remove_filter : forall l (a : word), map_remove l a = List.filter (fun p => negb (bv_eqb (fst p) a)) l.
Proof. reflexivity. Qed.

Lemma In_map_remove : forall l (a b n : word), In (b, n) l -> b <> a -> In (b, n) (map_remove l a).
Proof.
  intros l a b n Hin Hne. rewrite map_remove_filter. apply filter_In. split; [exact Hin|].
  cbn [fst]. unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned b) (bv_unsigned a)) as [Heq|Hneq]; [|reflexivity].
  exfalso. apply Hne. apply bv_eq. exact Heq.
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof.
  intros l a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
  cbn [fst snd]. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma munmap_len_sound : forall E cs R M model n nhi,
  cs_ok E cs R M model -> munmap_len cs = Some (n, nhi) ->
  exists len, getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ (0 < len)%Z
              /\ page_round_up_Z len = elenZ E n /\ (elenZ E n <= nhi)%Z.
Proof.
  intros E cs R M model n nhi HC H. unfold munmap_len in H.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit cs 11) as [len|] eqn:H11.
  - destruct (Z.ltb 0 len && Z.leb (page_up len) (2 ^ 40))%bool eqn:Hl; [|discriminate].
    apply andb_prop in Hl as [Hl Hpb]. apply Z.ltb_lt in Hl. apply Z.leb_le in Hpb. injection H as <- <-.
    destruct (reg_lit_sound E cs R M model 11 len HC ltac:(lia) H11) as [R11 Hlenr].
    exists len. split; [exact R11|]. split; [exact Hl|].
    assert (Hpu : page_round_up_Z len = page_up len) by (symmetry; apply page_up_eq).
    assert (Hb : (0 <= page_up len < 2 ^ 64)%Z).
    { split; [|lia]. unfold page_up. assert (0 <= (len + 4095) / 4096)%Z by (apply Z.div_pos; lia). lia. }
    rewrite elenZ_lit by exact Hb. split; [exact Hpu | lia].
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    destruct (Z.ltb 0 lo && Z.leb 12 (ealign (kn cs) (reg cs 11)))%bool eqn:Hc; [|discriminate].
    injection H as <- <-. apply andb_prop in Hc as [Hlo Hal]. apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal.
    pose proof (xlo_sound RSEGS E M (kn cs) _ lo HKN Hxl) as A.
    pose proof (xhi_sound RSEGS E M (kn cs) _ hi HKN Hxh) as B.
    exists (bv_unsigned (edenot E (reg cs 11))).
    split; [rewrite Z_to_bv_bv_unsigned; apply (reg_sound E cs R M model 11 HC ltac:(lia))|].
    split; [lia|]. unfold elenZ. split; [|lia].
    destruct (ealign_sound RSEGS E M (kn cs) (reg cs 11) HKN) as [Hea [q Hq]].
    assert (Hd : (2 ^ 12 | 2 ^ ealign (kn cs) (reg cs 11))%Z) by (apply pow2_divide_le; lia).
    destruct Hd as [r Hr]. rewrite Hr in Hq.
    unfold page_round_up_Z, page_size. rewrite Hq.
    replace (q * (r * 2 ^ 12) + 4096 - 1)%Z with (q * r * 4096 + 4095)%Z by (change (2^12)%Z with 4096%Z; ring).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Z.div_add_l by lia. change (4095 / 4096)%Z with 0%Z. change (2 ^ 12)%Z with 4096%Z. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma len_eqb_sound : forall E M k n m,
  know_ok RSEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros E M k n m HK H. rewrite len_eqb_eq in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound RSEGS E M k _ _ HK H1) as A. pose proof (lin_ge0_sound RSEGS E M k _ _ HK H2) as B.
    cbn [xt_den] in A, B. apply bv_eq. lia.
Qed.

Lemma node_munmap_sound : forall cs cs' E R M model T,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_munmap U0 cs = Some cs' ->
  (forall R' M' model', cs_ok E cs' R' M' model' -> m_fs model' = m_fs model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model') T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hec Hn HK.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_munmap in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (munmap_len cs) as [[n nhi]|] eqn:HML.
  2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hno : no = 215).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; reflexivity. }
  subst no.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hn with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. subst cs'. clear Hn.
  apply andb_prop in Hcond as [Hcond Hhi]. apply andb_prop in Hcond as [Hcond Hhull]. apply andb_prop in Hcond as [Hcond Hoth].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hn30 Hfind].
  apply Z.leb_le in Hn30. apply Z.leb_le in Hal.
  set (b := reg cs 10) in *.
  destruct (ehi (kn cs) b) as [hi|] eqn:Hehi; [|discriminate]. apply Z.ltb_lt in Hhi.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit_sound E cs R M model 17 215 HC ltac:(lia) H17) as [R17 _].
  destruct (munmap_len_sound E cs R M model n nhi HC HML) as (len & R11 & Hlen0 & Hpr & HNhi).
  set (N := elenZ E n) in *.
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10. fold b in R10.
  (* [comment removed for export] *)
  assert (Hbhi : (bv_unsigned (edenot E b) <= hi)%Z).
  { unfold ehi in Hehi. destruct b; try (destruct (erange (kn cs) _) as [[lo' hi']|] eqn:Her; [|discriminate];
      injection Hehi as <-; exact (proj2 (erange_sound RSEGS E M (kn cs) _ lo' hi' HKN Her))).
    injection Hehi as <-. cbn [edenot]. rewrite u_lit64. lia. }
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) b HKN) as [Hea [q Hq]].
  assert (Hmod : (bv_unsigned (edenot E b) mod page_size = 0)%Z).
  { unfold page_size. rewrite Hq.
    assert (Hd : (2 ^ 12 | 2 ^ ealign (kn cs) b)%Z) by (apply pow2_divide_le; lia).
    destruct Hd as [r Hr]. rewrite Hr. replace (q * (r * 2 ^ 12))%Z with ((q * r) * 4096)%Z by (change (2^12)%Z with 4096%Z; ring).
    apply Z.mod_mul. lia. }
  pose proof (u64_range (edenot E b)) as Hbr.
  assert (Hnpos : (0 < N)%Z).
  { rewrite <- Hpr. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  assert (HNw : Z_to_bv 64 N = edenot E n) by (subst N; unfold elenZ; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (co_vm _ _ _ _ _ HC) as HV.
  assert (MATCH : forall m, smap_match (kn cs) b n m = true ->
                    sm_exact m = true /\ sm_base m = b /\ edenot E (sm_len m) = Z_to_bv 64 N).
  { intros [mb ml mx] Hm. unfold smap_match in Hm. cbn [sm_exact sm_base sm_len] in *.
    apply andb_prop in Hm as [Hm Hl]. apply andb_prop in Hm as [Hx Hb].
    apply expr_eqb_eq in Hb. subst. rewrite HNw. split; [reflexivity|]. split; [reflexivity|].
    symmetry. eapply len_eqb_sound; [exact HKN | exact Hl]. }
  assert (Hin : In (edenot E b, Z_to_bv 64 N) (vm_maps (m_vmmaps model))).
  { apply existsb_exists in Hfind as (m & Hm_in & Hm).
    destruct (MATCH m Hm) as (Hx & Hb & Hl).
    pose proof (proj1 (Forall_forall _ _) (vo_maps _ _ _ _ _ HV) m Hm_in) as Hok.
    unfold smap_ok in Hok. rewrite Hx, Hb, Hl in Hok. destruct Hok as (_ & _ & Hok). exact Hok. }
  unfold cfg_of.
  eapply (rz_munmap RSEGS R (Z_to_bv 64 (pc cs)) M model w (edenot E b) len T Hf He
            (co_halt _ _ _ _ _ HC) (co_lazy _ _ _ _ _ HC) R17 R10 Hmod R11 Hlen0).
  { (* [comment removed for export] *)
    rewrite Hpr. pose proof (proj1 (Forall_forall _ _) (vo_top _ _ _ _ _ HV) _ Hin) as Ht. cbn [fst snd] in Ht.
    pose proof (vo_sp0w _ _ _ _ _ HV) as Hw. unfold two64 in Hhi. rewrite u64_lit in Ht by lia.
    unfold TASK_SIZE, sp_window_hi, STKWIN in *. lia. }
  { rewrite Hpr. apply map_has_In. exact Hin. }
  rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite Hpr.
  rewrite (munmap_model_simple _ _ model (co_lazy _ _ _ _ _ HC) (co_mat _ _ _ _ _ HC)).
  apply HK; [|reflexivity].
  (* [comment removed for export] *)
  destruct HC as [HR HK0 HL Hh Hlz Hmt Hfd HV0 HS0 HLIB].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - replace (sr_upd (s_regs (c_ss cs)) 10 (ELit 0)) with (sr_upd (s_regs (c_ss cs)) (ridx (10%bv : bv 5)) (ELit 0)) by reflexivity.
    apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate | reflexivity].
  - rewrite HNw. apply know_ok_unfill; [exact HK0|]. fold N. unfold flat, estart. cbn [a_base a_off]. unfold two64 in Hhi. lia.
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    destruct HV0 as [Vres Vmaps Vlen Vlive Vsmall Vnw Vseps Vlim Vsp0 Vsp0w Vtop].
    rewrite m_vmmaps_with_vmmaps. constructor; cbn [vm_reserved vm_maps vm_limit vm_live_bytes].
    + exact Vres.
    + (* [comment removed for export] *)
      apply Forall_forall. intros m Hm. unfold remove_exact in Hm. apply filter_In in Hm as [Hm_in Hnm].
      pose proof (proj1 (Forall_forall _ _) Vmaps m Hm_in) as Hok.
      rewrite others_apart_eq in Hoth. pose proof (proj1 (forallb_forall _ _) Hoth m Hm_in) as Hap.
      cbv beta in Hap. apply negb_true_iff in Hnm.
      apply orb_prop in Hap as [Hap|Hap]; [rewrite Hap in Hnm; discriminate|].
      pose proof (ranges_apart_x_sound RSEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as Hd.
      unfold estart in Hd. cbn [a_base a_off] in Hd. rewrite !Z.add_0_r in Hd. fold N in Hd.
      unfold smap_ok in Hok |- *. destruct Hok as (Hl0 & Hnw & Hok). split; [exact Hl0|]. split; [exact Hnw|].
      unfold elenZ in Hd.
      destruct (sm_exact m).
      * apply In_map_remove; [exact Hok|]. intros Heq. apply (f_equal bv_unsigned) in Heq. lia.
      * destruct Hok as (lo & sz & Hinl & Hlo & Hsz). exists lo, sz. split; [|split; [exact Hlo | exact Hsz]].
        apply In_map_remove; [exact Hinl|]. intros Heq.
        destruct (seps_In2 _ _ _ Vseps Hinl Hin) as [Hsame | Hdisj].
        -- injection Hsame as Hlo' Hsz'. rewrite Hsz' in Hsz. rewrite Hlo' in Hlo, Hsz.
           rewrite u64_lit in Hsz by (unfold two64 in *; lia). lia.
        -- unfold iv_disjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite u64_lit in Hdisj by (unfold two64 in *; lia).
           apply (f_equal bv_unsigned) in Heq. pose proof (u64_range sz). lia.
    + pose proof (map_remove_length (vm_maps (m_vmmaps model)) (edenot E b)). lia.
    + unfold vm_live_bytes in Vlive |- *. cbn [vm_maps].
      pose proof (live_bytes_map_remove_le (vm_maps (m_vmmaps model)) (edenot E b)). lia.
    + rewrite map_remove_filter. apply Forall_filter. exact Vsmall.
    + rewrite map_remove_filter. apply Forall_filter. exact Vnw.
    + rewrite map_remove_filter. apply seps_filter. exact Vseps.
    + exact Vlim.
    + (* [comment removed for export] *) exact Vsp0.
    + exact Vsp0w.
    + cbn [vm_init_sp]. rewrite map_remove_filter. apply Forall_filter. exact Vtop.
  - (* [comment removed for export] *) rewrite HNw. eapply slots_unfill_sound; [exact HK0 | exact HS0 |].
    fold N. unfold flat, estart. cbn [a_base a_off]. unfold two64 in Hhi. lia.
  - (* [comment removed for export] *)
    eapply lib_ok_frame; [|exact HLIB]. intros a Ha.
    pose proof (ranges_apart_x_sound RSEGS E M (kn cs) _ _ _ _ _ _ HK0 Hhull) as Hd.
    unfold estart, elenZ in Hd. cbn [a_base a_off edenot] in Hd. rewrite !Z.add_0_r in Hd. rewrite <- HNw in Hd.
    assert (E0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity. rewrite E0 in Hd.
    assert (EH : bv_unsigned (Z_to_bv 64 (t_hull_hi U0 - t_hull_lo U0)) = (t_hull_hi U0 - t_hull_lo U0)%Z) by (vm_compute; reflexivity).
    rewrite EH in Hd. unfold HULL_LO, HULL_HI in Ha.
    assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply u64_lit; unfold two64 in Hhi; lia). rewrite EN in Hd.
    apply unfill_out. rewrite EN. rewrite u64_lit by (cbn in Ha |- *; lia). cbn in Ha, Hd |- *. lia.
Qed.

(* [comment removed for export] *)

Lemma lin_inside_sound : forall E M kn b1 k1 n1 b2 k2 n2,
  know_ok RSEGS E M kn -> lin_inside kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z /\ (estart E (SA b1 k1) + n1 <= estart E (SA b2 k2) + n2)%Z.
Proof.
  intros E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold lin_inside in H.
  apply andb_prop in H as [H Hm]. apply andb_prop in H as [Hw1 Hw2].
  pose proof (lin_nowrapR_sound RSEGS E M kn b1 Hkn Hw1) as E1.
  pose proof (lin_nowrapR_sound RSEGS E M kn b2 Hkn Hw2) as E2.
  destruct (lin_of b1) as [c1 ts1] eqn:Hl1. destruct (lin_of b2) as [c2 ts2] eqn:Hl2. cbn [fst snd] in *.
  apply (lin_test_sound RSEGS E M kn) in Hm as (lo & hi & Hm & Hb); [|exact Hkn].
  rewrite lsub_e_sound in Hb. unfold estart. cbn [a_base a_off]. rewrite E1, E2.
  apply andb_prop in Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.leb_le in Hm2. lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_val : segments_reserved RSEGS =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x22000); (Z_to_bv 64 0x32000, Z_to_bv 64 0x7a000);
   (Z_to_bv 64 0xac000, Z_to_bv 64 0x7000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x33000)].
Proof. vm_compute. reflexivity. Qed.

Lemma region_free_image : forall maps (a : word) (n : Z),
  (0 < n < 2 ^ 64)%Z ->
  region_free (segments_reserved RSEGS ++ maps) a (Z_to_bv 64 n) = true ->
  (bv_unsigned a + n <= 0x10000 \/ 0xe6000 <= bv_unsigned a)%Z
  /\ (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z.
Proof.
  intros maps a n Hn H. rewrite region_free_app in H. apply andb_prop in H as [Hr Hm].
  split.
  - rewrite reserved_val in Hr.
    pose proof (fun b s Hin => region_free_In _ a (Z_to_bv 64 n) b s Hr Hin) as X.
    rewrite u64_lit in X by lia.
    pose proof (X _ _ (or_introl eq_refl)) as X1.
    pose proof (X _ _ (or_intror (or_introl eq_refl))) as X2.
    pose proof (X _ _ (or_intror (or_intror (or_introl eq_refl)))) as X3.
    pose proof (X _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as X4.
    rewrite !u64_lit in X1, X2, X3, X4 by lia. lia.
  - intros b s Hin. pose proof (region_free_In _ a (Z_to_bv 64 n) b s Hm Hin) as X. rewrite u64_lit in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma grant_keep_b_sem : forall E M k ms maps K (a : word) n,
  know_ok RSEGS E M k -> Forall (smap_ok E maps) ms ->
  (0x1000 <= bv_unsigned a)%Z -> (bv_unsigned a + n <= bv_unsigned (ev E SP0V) - STKWIN)%Z -> (0 < n)%Z ->
  (bv_unsigned a + n <= 0x10000 \/ 0xe6000 <= bv_unsigned a)%Z ->
  (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z ->
  grant_keep_b U0 k ms K = true -> kfoot_apart E K (bv_unsigned a) n.
Proof.
  intros E M k ms maps K a n HK Hms Ha Hc Hn Himg Hmaps Hb.
  assert (SR : forall b off len, safe_range U0 k ms b off len = true ->
            (estart E (SA b off) + elenZ E len <= bv_unsigned a \/ bv_unsigned a + n <= estart E (SA b off))%Z).
  { clear Hb. intros b off len H. unfold safe_range in H. rewrite ?ITOP_eq in H.
    pose proof (u64_range (edenot E len)) as Hlr. unfold elenZ.
    apply orb_prop in H as [H|H].
    - destruct (xhi k len) as [lh|] eqn:Hxh; [|discriminate].
      pose proof (xhi_sound RSEGS E M k len lh HK Hxh) as Hlh.
      apply orb_prop in H as [H|H].
      + (* [comment removed for export] *)
        destruct (lin_inside_sound E M k b off lh (EVar SP0V) (- STKWIN) STKWIN HK H) as [I1 I2].
        unfold estart in I1, I2 |- *. cbn [a_base a_off edenot] in I1, I2 |- *. lia.
      + destruct (erange k b) as [[lo hi]|] eqn:Hr; [|discriminate].
        pose proof (erange_sound RSEGS E M k b lo hi HK Hr) as Hbr. unfold estart. cbn [a_base a_off].
        apply orb_prop in H as [H|H];
          apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; unfold two64 in *; lia.
    - induction ms as [|m rest IH]; [discriminate|]. cbn [inside_maps] in H.
      apply Forall_cons_iff in Hms as [Hm Hrest].
      apply orb_prop in H as [H|H]; [|exact (IH Hrest H)].
      assert (I12 : (estart E (SA (sm_base m) 0) <= estart E (SA b off))%Z
                    /\ (estart E (SA b off) + bv_unsigned (edenot E len) <= estart E (SA (sm_base m) 0) + elenZ E (sm_len m))%Z).
      { assert (XI : xinside k b off len (sm_base m) 0 (sm_len m) = true ->
                     (estart E (SA (sm_base m) 0) <= estart E (SA b off))%Z
                     /\ (estart E (SA b off) + bv_unsigned (edenot E len) <= estart E (SA (sm_base m) 0) + elenZ E (sm_len m))%Z)
          by (intros HX; exact (xinside_sound RSEGS E M k b off len (sm_base m) 0 (sm_len m) HK HX)).
        destruct len as [l| | | | | | |]; try (apply XI; exact H).
        destruct (sm_len m) as [ml| | | | | | |] eqn:Hml; try (apply XI; exact H).
        destruct (lin_inside_sound E M k b off _ (sm_base m) 0 _ HK H) as [I1 I2].
        unfold elenZ. cbn [edenot]. rewrite !u_lit64. split; [exact I1 | exact I2]. }
      destruct I12 as [I1 I2].
      unfold estart in I1, I2 |- *. unfold elenZ in I2. cbn [a_base a_off] in *.
      unfold smap_ok in Hm. destruct Hm as (Hml & Hmnw & Hm).
      destruct (sm_exact m).
      + pose proof (Hmaps _ _ Hm) as D. lia.
      + destruct Hm as (lo & sz & Hin & Hlo & Hsz). pose proof (Hmaps _ _ Hin) as D. lia. }
  unfold kfoot_apart, kfoot.
  destruct K as [[b kk] w v|[b kk] nn|[b kk] nn kb|ilo ihi|e m|e rlo rhi|[b kk] nn|a1 n1 a2 n2]; cbn [grant_keep_b] in Hb;
    rewrite ?ITOP_eq in Hb; try exact I; try discriminate.
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (SR _ _ _ Hb) as X. rewrite elenZ_lit in X by lia. lia.
  - exact (SR _ _ _ Hb).
  - exact (SR _ _ _ Hb).
  - apply orb_prop in Hb as [Hb|Hb]; apply andb_prop in Hb as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
  - exact (SR _ _ _ Hb).
Qed.

(* [comment removed for export] *)
Lemma safe_range_sem : forall E M k ms maps (a : word) n b off len,
  know_ok RSEGS E M k -> Forall (smap_ok E maps) ms ->
  (0x1000 <= bv_unsigned a)%Z -> (bv_unsigned a + n <= bv_unsigned (ev E SP0V) - STKWIN)%Z -> (0 < n)%Z ->
  (bv_unsigned a + n <= 0x10000 \/ 0xe6000 <= bv_unsigned a)%Z ->
  (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z ->
  safe_range U0 k ms b off len = true ->
  (estart E (SA b off) + elenZ E len <= bv_unsigned a \/ bv_unsigned a + n <= estart E (SA b off))%Z.
Proof.
  intros E M k ms maps a n b off len HK Hms Ha Hc Hn Himg Hmaps H.
  pose proof (grant_keep_b_sem E M k ms maps (KZero (SA b off) len) a n HK Hms Ha Hc Hn Himg Hmaps) as G.
  cbn [grant_keep_b] in G. specialize (G H). unfold kfoot_apart, kfoot in G. exact G.
Qed.

Lemma grant_ok_facts : forall hint model (a : word) n,
  vm_reserved (m_vmmaps model) = segments_reserved RSEGS -> (0 < n < 2 ^ 64)%Z ->
  grant_ok hint model a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0x1000 <= bv_unsigned a)%Z /\ (bv_unsigned a + n <= alloc_top (m_vmmaps model))%Z   (* [comment removed for export] *)
  /\ (bv_unsigned a + n <= 0x10000 \/ 0xe6000 <= bv_unsigned a)%Z
  /\ (forall b s, In (b, s) (vm_maps (m_vmmaps model)) ->
        bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z
  /\ (vm_backing_used model + n <= vm_limit (m_vmmaps model))%Z.
Proof.
  intros hint model a n Hres Hn Hg. unfold grant_ok in Hg.
  apply andb_prop in Hg as [Hg Hl]. apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Hc].   (* [comment removed for export] *)
  apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hc. apply Z.leb_le in Hl.
  rewrite Hres in Hrf. destruct (region_free_image _ a n Hn Hrf) as [Himg Hmaps].
  repeat split; try assumption.
  unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). nia.
Qed.

Lemma regs_ok_ext : forall b E E' sr R, env_agree b E E' -> SP.sr_vars_lt b sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof.
  intros b E E' sr R Hag Hv HR.
  eapply regs_ok_agree; [exact Hag | | exact HR].
  clear -Hv. induction sr as [|e r IH]; cbn [SP.sr_vars_lt SymRun3.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in Hv as [H1 H2]. rewrite <- expr_vars_lt_eq, H1. cbn [andb]. exact (IH H2).
Qed.

Lemma kentry_vars_lt_eq : forall b K, SP.kentry_vars_lt b K = SymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [a w v|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2];
    cbn [SP.kentry_vars_lt SymRun3.kentry_vars_lt]; unfold SP.saddr_vars_lt, SymRun3.saddr_vars_lt;
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.

Lemma kn_vars_lt_eq : forall b kn, SP.kn_vars_lt b kn = SymRun3.kn_vars_lt b kn.
Proof.
  intros b kn. induction kn as [|K r IH]; cbn [SP.kn_vars_lt SymRun3.kn_vars_lt]; [reflexivity|].
  rewrite IH, kentry_vars_lt_eq. reflexivity.
Qed.

Lemma know_ok_ext : forall b E E' M kn, env_agree b E E' -> SP.kn_vars_lt b kn = true -> know_ok RSEGS E M kn -> know_ok RSEGS E' M kn.
Proof.
  intros b E E' M kn Hag Hv HK. eapply know_ok_agree; [exact Hag | rewrite <- kn_vars_lt_eq; exact Hv | exact HK].
Qed.

Lemma kn_vars_lt_filter : forall b f kn, SP.kn_vars_lt b kn = true -> SP.kn_vars_lt b (List.filter f kn) = true.
Proof.
  intros b f kn. induction kn as [|K r IH]; cbn [SP.kn_vars_lt List.filter]; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (f K); cbn [SP.kn_vars_lt]; [rewrite H1, (IH H2); reflexivity | exact (IH H2)].
Qed.

Lemma smaps_ok_ext : forall b E E' maps ms,
  env_agree b E E' -> maps_vars_lt b ms = true -> Forall (smap_ok E maps) ms -> Forall (smap_ok E' maps) ms.
Proof.
  intros b E E' maps ms Hag Hv H. apply Forall_forall. intros m Hm.
  pose proof (proj1 (Forall_forall _ _) H m Hm) as Hok.
  unfold maps_vars_lt in Hv. pose proof (proj1 (forallb_forall _ _) Hv m Hm) as Hvm.
  apply andb_prop in Hvm as [Hvb Hvl].
  unfold smap_ok in *. rewrite <- (edenot_agree b E E' (sm_base m) Hag) by (rewrite <- expr_vars_lt_eq; exact Hvb).
  rewrite <- (edenot_agree b E E' (sm_len m) Hag) by (rewrite <- expr_vars_lt_eq; exact Hvl). exact Hok.
Qed.

(* [comment removed for export] *)
Lemma vm_ok_ext : forall b E E' ms nm lv VM,
  env_agree b E E' -> maps_vars_lt b ms = true -> (SP0V < b)%nat ->
  vm_ok E ms nm lv VM -> vm_ok E' ms nm lv VM.
Proof.
  intros b E E' ms nm lv VM Hag Hmv Hb HV. destruct HV; constructor; try assumption.
  - eapply smaps_ok_ext; [exact Hag | exact Hmv | assumption].
  - destruct Hag as [Hag _]. rewrite <- (Hag SP0V Hb). assumption.
Qed.

Lemma max1_le_l : forall a v, (Nat.max 1 a <= v)%nat -> (a <= v)%nat.
Proof. intros. lia. Qed.
Lemma max1_le_0 : forall a v, (Nat.max 1 a <= v)%nat -> (SP0V < v)%nat.
Proof. intros. unfold SP0V. lia. Qed.

Lemma page_round_up_Z_mono : forall a b, (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

Lemma page_up_e_denot : forall E e,
  (bv_unsigned (edenot E e) + 4095 < 2 ^ 64)%Z ->
  edenot E (page_up_e e) = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E e))).
Proof.
  intros E e Hb. unfold page_up_e. rewrite !mkAlu_denot. cbn [edenot].
  pose proof (u64_range (edenot E e)) as Hr.
  rewrite alu_add.
  rewrite alu_srl, (alu_sll_amt _ (Z_to_bv 64 12) 12) by (rewrite u64_lit by lia; reflexivity).
  unfold v_srl, v_add. rewrite (u64_lit 12) by lia. change (12 mod 64)%Z with 12%Z.
  rewrite (u64_lit 4095) by lia. rewrite (u64_lit (bv_unsigned (edenot E e) + 4095)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : (0 <= (bv_unsigned (edenot E e) + 4095) / 2 ^ 12 < 2 ^ 64)%Z).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite u64_lit by lia. unfold page_round_up_Z, page_size. f_equal. change (2 ^ 12)%Z with 4096%Z. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_len_sound : forall E cs R M model ne lo nhi,
  cs_ok E cs R M model -> mmap_len cs = Some (ne, lo, nhi) ->
  exists len, getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len
    /\ (lo <= len)%Z /\ (0 <= len < 2 ^ 64)%Z /\ (page_round_up_Z len <= nhi)%Z
    /\ SP.expr_vars_lt (s_next (c_ss cs)) ne = true
    /\ forall E', env_agree (s_next (c_ss cs)) E E' -> edenot E' ne = Z_to_bv 64 (page_round_up_Z len).
Proof.
  intros E cs R M model ne lo nhi HC H. unfold mmap_len in H.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit cs 11) as [len|] eqn:H11.
  - injection H as <- <- <-.
    destruct (reg_lit_sound E cs R M model 11 len HC ltac:(lia) H11) as [R11 Hlenr]. unfold two64 in Hlenr.
    exists len. split; [exact R11|]. split; [lia|]. split; [lia|].
    rewrite page_up_eq. split; [lia|]. split; [reflexivity|].
    intros E' _. cbn [edenot]. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo'|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [lhi|] eqn:Hxh; [|discriminate].
    set (ne1 := match foldK (kn cs) (page_up_e (reg cs 11)) with ELit z => ELit z | _ => page_up_e (reg cs 11) end) in H.
    assert (FK1 : edenot E ne1 = edenot E (page_up_e (reg cs 11))).
    { subst ne1. pose proof (foldK_denot RSEGS E M (kn cs) (page_up_e (reg cs 11)) HKN) as FK.
      destruct (foldK (kn cs) (page_up_e (reg cs 11))); first [exact FK | reflexivity]. }
    clearbody ne1.
    destruct (xhi (kn cs) ne1) as [nhi'|] eqn:Hxn; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hb Hv]. apply Z.leb_le in Hb.
    assert (ne = ne1 /\ lo' = lo /\ nhi' = nhi) as (-> & <- & <-) by (injection H; auto). clear H.
    pose proof (xlo_sound RSEGS E M (kn cs) _ lo' HKN Hxl) as A.
    pose proof (xhi_sound RSEGS E M (kn cs) _ lhi HKN Hxh) as B.
    pose proof (xhi_sound RSEGS E M (kn cs) _ nhi' HKN Hxn) as C.
    pose proof (u64_range (edenot E (reg cs 11))) as Hr.
    assert (PD : edenot E (page_up_e (reg cs 11)) = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
      by (apply page_up_e_denot; lia).
    assert (PD1 : edenot E ne1 = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) by (rewrite FK1; exact PD).
    exists (bv_unsigned (edenot E (reg cs 11))).
    split; [rewrite Z_to_bv_bv_unsigned; apply (reg_sound E cs R M model 11 HC ltac:(lia))|].
    split; [lia|]. split; [lia|].
    split.
    { rewrite PD1 in C. rewrite u64_lit in C; [exact C|].
      pose proof (page_round_up_Z_bounds (bv_unsigned (edenot E (reg cs 11))) ltac:(lia)) as PB. unfold page_size in PB. lia. }
    split; [exact Hv|].
    intros E' Hag. rewrite <- (edenot_agree _ E E' _ Hag) by (rewrite <- expr_vars_lt_eq; exact Hv). exact PD1.
Qed.

Lemma node_mmap_sound : forall cs csf css E R M model TA TB,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_mmap U0 nx0 cs = Some (csf, css) ->
  (forall R' M', cs_ok E csf R' M' model -> realizes RSEGS (cfg_of R' (pc csf) M' model) TA) ->
  (forall a R' M' model', cs_ok (ext1 E (s_next (c_ss cs)) a) css R' M' model' -> m_fs model' = m_fs model ->
      realizes RSEGS (cfg_of R' (pc css) M' model') TB) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_alt2 TA TB).
Proof.
  intros cs csf css E R M model TA TB HC Hec Hn HKA HKB.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_mmap in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [z10|] eqn:H10. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (mmap_len cs) as [[[ne lo] nhi]|] eqn:HML. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 12) as [z12|] eqn:H12. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 13) as [z13|] eqn:H13. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 14) as [m1|] eqn:H14. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 15) as [z15|] eqn:H15. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hlits : no = 222 /\ z10 = 0 /\ z12 = 3 /\ z13 = 34 /\ z15 = 0).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. repeat split; reflexivity. }
  destruct Hlits as (-> & -> & -> & -> & ->).
  match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hn with Some (?x, ?y) = Some (?x', ?y') =>
    assert (Ef : x' = x) by congruence; assert (Es : y' = y) by congruence end.
  subst csf css. clear Hn.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hlive].
  apply andb_prop in Hcond as [Hcond Hcnt]. apply andb_prop in Hcond as [Hcond Hm1].
  apply andb_prop in Hcond as [Hlo0 Hn30].
  apply Z.ltb_lt in Hlo0. apply Z.leb_le in Hn30. apply Z.eqb_eq in Hm1. apply Z.leb_le in Hcnt. apply Z.leb_le in Hlive.
  set (v := s_next (c_ss cs)) in *.
  destruct (mmap_len_sound E cs R M model ne lo nhi HC HML) as (len & R11 & Hlolen & Hlenr & Hnhi & Hnev & Hne).
  fold v in Hnev, Hne.
  set (n := page_round_up_Z len) in *.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hnb. fold n in Hnb. unfold page_size in Hnb.
  assert (Hnpos : (0 < n)%Z) by lia.
  assert (Hnlo : (page_up lo <= n)%Z).
  { rewrite page_up_eq. subst n. apply page_round_up_Z_mono. lia. }
  assert (Hplo : (0 < page_up lo)%Z).
  { unfold page_up. assert (1 <= (lo + 4095) / 4096)%Z by (apply Z.div_le_lower_bound; lia). lia. }
  destruct (reg_lit_sound E cs R M model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 12 3 HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound E cs R M model 13 34 HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound E cs R M model 14 m1 HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound E cs R M model 15 0 HC ltac:(lia) H15) as [R15 _].
  pose proof (co_vm _ _ _ _ _ HC) as HV. destruct HV as [Vres Vmaps Vlen Vlive Vsmall Vnw Vseps Vlim Vsp0 Vsp0w Vtop].  (* [comment removed for export] *)
  unfold cfg_of.
  eapply (rz_mmap_anon RSEGS R (Z_to_bv 64 (pc cs)) M model w len TA TB Hf He (co_halt _ _ _ _ _ HC) (co_lazy _ _ _ _ _ HC) R17 R11);
    [lia | exact R12 | exact R13 | | exact R15 | | |].
  { etransitivity; [exact R14|]. rewrite Hm1. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity. }
  { (* [comment removed for export] *)
    fold n. apply (grant_exists_gen _ model (2 ^ 30) n 1004); try lia.
    - reflexivity.
    - rewrite Vres, reserved_val. repeat apply Forall_cons; try (cbn [snd]; rewrite u64_lit by lia; lia).
      apply Forall_forall. intros [b sz] Hin. cbn [snd]. exact (proj2 (proj1 (Forall_forall _ _) Vsmall _ Hin)).
    - rewrite length_app, Vres, reserved_val. cbn [length]. lia.
    - rewrite bottomup_floor_val. unfold alloc_ceiling. cbn. lia.
    - apply grant_budget_intro; [exact (co_lazy _ _ _ _ _ HC) | exact (co_mat _ _ _ _ _ HC) | lia].
    - (* [comment removed for export] *) unfold init_sp_ok. lia. }
  { (* [comment removed for export] *)
    intros e Hine. cbn [mmap_errnos In] in Hine. destruct Hine as [<-|[]].
    rewrite (v_addi_pc (pc cs) Hp0 Hp4).
    specialize (HKA (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) M).
    unfold pc in HKA at 1. cbn [c_ss s_pc set_pc set_reg] in HKA. apply HKA.
    apply cs_ok_set_reg_pc; [exact HC | lia |].
    cbn [edenot]. unfold errno_ret, ENOMEM. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity. }
  (* [comment removed for export] *)
  fold n. intros a Hg.
  destruct (grant_ok_facts _ model a n Vres ltac:(lia) Hg) as (Gal & Glo & Gceil & Gimg & Gmaps & Glive).
  rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  apply (HKB a); [|reflexivity].
  (* [comment removed for export] *)
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv].
  apply andb_prop in Hfresh as [Hsv Hkv]. fold v in Hsv, Hkv, Hmv, Hslv, Hnx0.
  set (E' := ext1 E v a).
  pose proof (ext1_agree E v a) as Hag. fold E' in Hag.
  assert (HneE' : edenot E' ne = Z_to_bv 64 n) by (apply Hne; exact Hag).
  assert (HelE' : elenZ E' ne = n) by (unfold elenZ; rewrite HneE'; apply u64_lit; lia).
  (* [comment removed for export] *)
  unfold alloc_top, stack_max_size in Gceil.
  assert (Hv0 : (SP0V < v)%nat).
  { apply (max1_le_0 nx0). apply Nat.leb_le. exact Hnx0. }
  assert (Esp0 : ev E' SP0V = vm_init_sp (m_vmmaps model)).
  { rewrite Vsp0. symmetry. apply (proj1 Hag). exact Hv0. }
  assert (Gsp : (bv_unsigned a + n <= bv_unsigned (ev E' SP0V) - 8388608)%Z) by (rewrite Esp0; lia).
  assert (Gtop : (bv_unsigned (ev E' SP0V) <= 0x800000000000)%Z) by (rewrite Esp0; unfold sp_window_hi in Vsp0w; lia).
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd _ HSL HLIB].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots pc s_pc].
  - (* [comment removed for export] *)
    replace (sr_upd (s_regs (c_ss cs)) 10 (EVar v)) with (sr_upd (s_regs (c_ss cs)) (ridx (10%bv : bv 5)) (EVar v)) by reflexivity.
    apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate | apply ext1_at].
    eapply regs_ok_ext; [exact Hag | exact Hsv | exact HR].
  - (* [comment removed for export] *)
    apply Forall_app. split.
    + (* [comment removed for export] *)
      rewrite kn_grant_filter_eq. (* [comment removed for export] *) apply Forall_forall. intros K Hin. apply filter_In in Hin as [Hin Hkeep].
      assert (HK' : know_ok RSEGS E' M (s_know (c_ss cs))) by (eapply know_ok_ext; [exact Hag | exact Hkv | exact HK]).
      pose proof (proj1 (Forall_forall _ _) HK' K Hin) as HKK.
      eapply kentry_keep_sem; [exact HKK | |].
      * eapply (grant_keep_b_sem E' M (s_know (c_ss cs)) (c_maps cs) (vm_maps (m_vmmaps model)) K a n HK');
          [eapply smaps_ok_ext; [exact Hag | exact Hmv | exact Vmaps] | exact Glo | exact Gsp | exact Hnpos | exact Gimg | exact Gmaps | exact Hkeep].
      * intros x Hx. apply zfill_out. rewrite u64_lit by lia. lia.
    + (* [comment removed for export] *)
      assert (Hv : edenot E' (EVar v) = a) by apply ext1_at.
      assert (Hv' : ev E' v = a) by apply ext1_at.
      unfold kn_mmap. rewrite ?ISPAN_eq. apply Forall_app. split.
      * repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; rewrite ?Hv, ?Hv', ?HelE'.
        -- unfold SP.STKWIN. lia.
        -- split; [lia|]. unfold page_size in Gal. exact Gal.
        -- split; [unfold flat, estart; cbn [a_base a_off]; rewrite ?Hv, ?Hv'; lia|].
           intros d m Hd Hdm. unfold estart. cbn [a_base a_off]. rewrite ?Hv, ?Hv'.
           unfold zfill. apply store_ok_zmem; rewrite ?u64_lit; try lia.
        -- unfold flat, estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv'.
           split; [lia|].
           intros i Hi. unfold zfill, zmem. rewrite Z.add_0_r.
           rewrite u64_lit by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite u64_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
        -- unfold estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv'. rewrite elenZ_lit by lia. rewrite u64_lit by lia. lia.
        -- (* [comment removed for export] *)
           unfold estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv'. unfold SP.STKTOP, SP.STKWIN. rewrite elenZ_lit by lia. right. lia.
        -- (* [comment removed for export] *)
           cbn [edenot]. rewrite ?Hv, ?Hv'. rewrite alu_sub. unfold v_sub.
           pose proof (u64_range (ev E' SP0V)) as Hsp0r. pose proof (u64_range a) as Har.
           unfold SP.STKWIN. rewrite u64_lit by lia. lia.
      * apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (m & <- & Hm).
        cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv', ?HelE'.
        pose proof (proj1 (Forall_forall _ _) (smaps_ok_ext v E E' _ _ Hag Hmv Vmaps) m Hm) as Hok.
        unfold smap_ok in Hok. destruct Hok as (Hl0 & Hnw & Hok). unfold elenZ.
        destruct (sm_exact m).
        -- pose proof (Gmaps _ _ Hok) as D. lia.
        -- destruct Hok as (lo1 & sz & Hin & Hlo & Hsz). pose proof (Gmaps _ _ Hin) as D. lia.
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    unfold mmap_model. rewrite m_vmmaps_with_vmmaps. constructor; cbn [vm_reserved vm_maps vm_limit vm_live_bytes].
    + exact Vres.
    + apply Forall_cons.
      * unfold smap_ok. cbn [sm_base sm_len sm_exact]. assert (Hv : edenot E' (EVar v) = a) by apply ext1_at.
        rewrite Hv, HneE'. rewrite u64_lit by lia. split; [lia|]. split; [lia|]. left. reflexivity.
      * apply Forall_forall. intros m Hm.
        pose proof (proj1 (Forall_forall _ _) (smaps_ok_ext v E E' _ _ Hag Hmv Vmaps) m Hm) as Hok.
        unfold smap_ok in *. destruct Hok as (Hl0 & Hnw & Hok). split; [exact Hl0|]. split; [exact Hnw|].
        destruct (sm_exact m); [right; exact Hok|].
        destruct Hok as (lo1 & sz & Hin & Hlo & Hsz). exists lo1, sz. split; [right; exact Hin|]. auto.
    + cbn [length]. lia.
    + unfold vm_live_bytes in *. cbn [vm_maps]. rewrite live_bytes_cons, u64_lit by lia. lia.
    + apply Forall_cons; [|exact Vsmall]. cbn [snd]. rewrite u64_lit by lia. lia.
    + apply Forall_cons; [|exact Vnw]. cbn [fst snd]. rewrite u64_lit by lia. lia.
    + constructor; [|exact Vseps]. apply Forall_forall. intros [b sz] Hin. unfold iv_disjoint. cbn [fst snd].
      rewrite u64_lit by lia. pose proof (Gmaps _ _ Hin). lia.
    + exact Vlim.
    + (* [comment removed for export] *) cbn [vm_init_sp]. symmetry. exact Esp0.
    + cbn [vm_init_sp]. exact Vsp0w.
    + cbn [vm_init_sp vm_maps]. apply Forall_cons; [cbn [fst snd]; unfold SP.STKWIN; rewrite u64_lit by lia; lia | exact Vtop].
  - (* [comment removed for export] *)
    assert (HSL' : slots_ok E' M (c_slots cs)) by (eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL]).
    assert (HK' : know_ok RSEGS E' M (s_know (c_ss cs))) by (eapply know_ok_ext; [exact Hag | exact Hkv | exact HK]).
    rewrite slots_grant_filter_eq. (* [comment removed for export] *) unfold slots_ok. apply Forall_forall. intros sl Hin. apply filter_In in Hin as [Hin Hkeep].
    pose proof (proj1 (Forall_forall _ _) HSL' sl Hin) as HS1.
    destruct (split_lit (sl_start sl)) as [hb hk] eqn:Hsp.
    pose proof (safe_range_sem E' M (s_know (c_ss cs)) (c_maps cs) (vm_maps (m_vmmaps model)) a n hb (hk - 4) (sl_stride sl) HK'
                  ltac:(eapply smaps_ok_ext; [exact Hag | exact Hmv | exact Vmaps]) Glo Gsp Hnpos Gimg Gmaps Hkeep) as D.
    eapply slot_ok_agree; [exact HS1|].
    pose proof HS1 as (_ & _ & Hhull & _). rewrite Hsp in Hhull.
    intros x Hx _. apply zfill_out. rewrite u64_lit by lia.
    unfold estart, elenZ in D. cbn [a_base a_off] in D. unfold uE in *. lia.
  - (* [comment removed for export] *)
    eapply lib_ok_frame; [|exact HLIB]. intros x Hx. unfold HULL_LO, HULL_HI in Hx. cbn in Hx.
    apply zfill_out. rewrite (u64_lit n) by lia. rewrite (u64_lit x) by lia. lia.
Qed.

Lemma fd_lookup_std1 : forall model, m_fds model = fds_std ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros model H. rewrite H. reflexivity. Qed.
Lemma fd_lookup_std2 : forall model, m_fds model = fds_std ->
  fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros model H. rewrite H. reflexivity. Qed.

Lemma node_ioctl_sound : forall cs cs' E R M model T,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_ioctl cs = Some cs' ->
  (forall R' M', cs_ok E cs' R' M' model -> realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hec Hn HK.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_ioctl in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [fd|] eqn:H10; [|destruct no; try discriminate; repeat (destruct p; try discriminate)].
  destruct (reg_lit cs 11) as [rq|] eqn:H11.
  all: repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; try discriminate.
  injection Hn as <-.
  destruct (reg_lit_sound E cs R M model 17 29 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 1 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 11 0x5413 HC ltac:(lia) H11) as [R11 _].
  unfold cfg_of.
  eapply (rz_ioctl_winsz RSEGS R (Z_to_bv 64 (pc cs)) M model w (Z_to_bv 64 1));
    [exact Hf | exact He | exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact R17 | exact R10 | rewrite u64_lit; lia
    | apply fd_lookup_std1; exact (co_fds _ _ _ _ _ HC) | discriminate | exact R11 |].
  rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  specialize (HK (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOTTY)) M).
  rewrite pc_set_pc in HK. apply HK.
  apply cs_ok_set_reg_pc; [exact HC | lia |].
  cbn [edenot]. unfold errno_ret, ENOTTY. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma flat_b_sound : forall E M k b off n,
  know_ok RSEGS E M k -> flat_b k b off n = true -> flat E (SA b off) n.
Proof.
  intros E M k b off n HK H. unfold flat_b in H. rewrite base_range_fk in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound RSEGS E M k b lo hi HK Hb) as Hr.
  unfold flat, estart. cbn [a_base a_off]. lia.
Qed.

Lemma kreadZ_kread : forall k b off n z,
  kreadZ RSEGS k b off n = Some z -> exists z0, kread RSEGS k b off n = Some (ELit z0) /\ z = (z0 mod two64)%Z.
Proof.
  intros k b off n z H. unfold kreadZ in H. unfold kread.
  destruct (know_lookup RSEGS k b off n false [] []) as [v scs hs|scs hs|]; try discriminate.
  destruct v; try discriminate. destruct scs; [|discriminate]. injection H as <-. eexists. split; reflexivity.
Qed.

Lemma kreadZ_rdn : forall E M k b off n z,
  know_ok RSEGS E M k -> kreadZ RSEGS k b off n = Some z -> (1 <= n <= 8)%nat ->
  flat E (SA b off) (Z.of_nat n) ->
  rdn RSEGS M (adenot E (SA b off)) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) /\ (0 <= z < two64)%Z.
Proof.
  intros E M k b off n z HK H Hn Hfl.
  destruct (kreadZ_kread k b off n z H) as (z0 & Hr & ->).
  pose proof (kread_rdn RSEGS E M k b off n (ELit z0) HK Hr ltac:(lia) ltac:(lia) Hfl) as Hrd.
  cbn [edenot] in Hrd. split; [| unfold two64; apply Z.mod_pos_bound; lia].
  rewrite Hrd. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (bv_unsigned (edenot E b) + off).
Proof. intros. unfold adenot, v_addi. reflexivity. Qed.

Lemma w2lb1 : forall z, word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with (2^8)%Z. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.

Lemma kread_bytes_rdn : forall E M k len b off zs,
  know_ok RSEGS E M k -> kread_bytes RSEGS len k b off = Some zs ->
  (0 <= bv_unsigned (edenot E b) + off)%Z -> (bv_unsigned (edenot E b) + off + Z.of_nat len <= 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; reflexivity.
  - cbn [kread_bytes] in H.
    destruct (kreadZ RSEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes RSEGS len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat, estart; cbn [a_base a_off]; lia).
    destruct (kreadZ_rdn E M k b off 1 z HK Hz ltac:(lia) Hfl) as [Hrd Hzr].
    rewrite adenot_SA in Hrd.
    destruct (IH b (off + 1)%Z rest HK Hrest ltac:(lia) ltac:(lia)) as [Hrd2 Hlen].
    split; [| cbn; lia].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app.
    + rewrite Hrd. rewrite w2lb1. reflexivity.
    + replace (Z_to_bv 64 (bv_unsigned (edenot E b) + off) + nat_to_word 1)%bv
        with (Z_to_bv 64 (bv_unsigned (edenot E b) + (off + 1))); [exact Hrd2|].
      apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
      change (Z.of_nat 1) with 1%Z. rewrite (Z.mod_small 1) by lia.
      rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma Wz_map : forall fd zs, Wz fd zs = map (WriteEv (Z_to_bv 64 fd)) (map (fun z => Z_to_bv 8 z) zs).
Proof. intros fd zs. unfold Wz. rewrite map_map. reflexivity. Qed.

Lemma node_exit_sound : forall cs code E R M model,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_exit cs = Some code ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros cs code E R M model HC Hec Hn.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & _ & _).
  unfold node_exit in Hn.
  assert (H : exists no c, reg_lit cs 17 = Some no /\ (no = 94 \/ no = 93) /\ reg_lit cs 10 = Some c /\ code = Z.land c 255).
  { destruct (reg_lit cs 17) as [no|]; [|discriminate].
    destruct (reg_lit cs 10) as [c|] eqn:H10;
    repeat match type of Hn with context [match ?no with _ => _ end] => destruct no; try discriminate end;
    try discriminate; injection Hn as <-; eexists _, c; (split; [reflexivity|]); split; auto. }
  destruct H as (no & c & H17 & Hno & H10 & ->).
  destruct (reg_lit_sound E cs R M model 17 no HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 c HC ltac:(lia) H10) as [R10 Hc].
  unfold cfg_of.
  assert (Hcode : Z_to_bv 64 (Z.land c 255) = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)).
  { apply bv_eq. rewrite !bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    assert (Hl : (0 <= Z.land c 255 < 256)%Z).
    { split; [apply Z.land_nonneg; lia|]. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound c (2^8) ltac:(lia)). lia. }
    rewrite !Z.mod_small; unfold two64 in Hc; try lia. }
  rewrite Hcode.
  eapply (rz_exit_at RSEGS R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) model w);
    [exact Hf | exact He | exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | | exact R10].
  destruct Hno as [-> | ->]; [left | right]; exact R17.
Qed.

(* [comment removed for export] *)

Lemma kwritable_sound : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable allkn k b off n = true -> (0 <= n)%Z ->
  store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true.
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest H).
  cbn [kentry_ok] in HKK.
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  2: { lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
       apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
       apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
       destruct (xinside_sound RSEGS E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
       unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
       destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
       unfold elenZ, estart in *. cbn [a_base a_off] in *.
       replace (bv_unsigned (edenot E b) + off)%Z
         with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk)))%Z by lia.
       apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  clear H. rename Hc0 into H.
  destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
  apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
  destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in H. rename H into H2.
  pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hx) as Hwl.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. unfold elenZ in Hs.
  unfold estart in Hs. cbn [a_base a_off] in Hs.
  replace (bv_unsigned (edenot E b) + off)%Z with (bv_unsigned (edenot E b) + wk + (off - wk))%Z by lia.
  apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable_x allkn k b off n = true ->
  (forall m, (Z.of_nat m <= elenZ E n)%Z ->
     store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
  /\ (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64)%Z.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable_x] in H.
  destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest H).
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4. cbn [a_base a_off] in Hs, F1, F2, F4.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : (bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off)%Z ->
                 (bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn)%Z ->
                 (forall m, (Z.of_nat m <= elenZ E n)%Z -> store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64)%Z).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off)%Z with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk)))%Z by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H. rename H into H2.
    pose proof (xhi_sound RSEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound RSEGS E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma ridx_val : forall r : bv 5, Z.of_nat (ridx r) = bv_unsigned r.
Proof. intros r. unfold ridx. pose proof (bv_unsigned_in_range 5 r). rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. apply bv_eq. rewrite <- H, ridx_val. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 5 r). unfold bv_wrap. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma v_lw_of_extz : forall old, (0 <= old < 2 ^ 32)%Z -> Z_to_bv 64 (extz true 4 old) = v_lw (Z_to_bv 64 old).
Proof.
  intros old Hold. unfold extz, v_lw. cbn [N.of_nat N.mul]. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma node_cas_sound : forall c cs cs' E R M model T,
  cs_ok E cs R M model -> node_cas RSEGS U0 c cs = Some cs' ->
  (forall R' M', cs_ok E cs' R' M' model -> realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros c cs cs' E R M model T HC Hn HK.
  (* [comment removed for export] *)
  assert (CORE : forall ra compute setregs pc',
    cas_core RSEGS U0 cs ra compute setregs pc' = Some cs' -> (0 < ra < 32)%nat ->
    exists b k ve new kn' (old : Z) hs,
      split_lit (reg cs ra) = (b, k)
      /\ compute (extK (kn cs) ve) = Some new
      /\ carry [SE (SA b k) 4 new] (kn cs) [] = (kn', [], hs)
      /\ cs' = CS (SS pc' (setregs (extK (kn cs) ve) new (s_regs (c_ss cs))) [] kn' (s_next (c_ss cs))) (c_maps cs) (c_nmaps cs) (c_live cs)
                  (slots_carry kn' [SE (SA b k) 4 new] (c_slots cs))
      /\ getr R (Z_to_bv 5 (Z.of_nat ra)) = adenot E (SA b k)
      /\ (bv_unsigned (adenot E (SA b k)) mod 4 = 0)%Z
      /\ rdn RSEGS M (adenot E (SA b k)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 old))
      /\ (0 <= old < 2 ^ 32)%Z
      /\ edenot E (extK (kn cs) ve) = v_lw (Z_to_bv 64 old)
      /\ store_ok RSEGS M (adenot E (SA b k)) 4 = true
      /\ flat E (SA b k) 4
      /\ hull_apart U0 (kn cs) b k (ELit 4) = true).
  { intros ra compute setregs pc' H Hra. unfold cas_core in H.
    destruct (split_lit (reg cs ra)) as [b k] eqn:Hs.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hhull]. apply andb_prop in Hcond as [Hcond Hkw]. apply andb_prop in Hcond as [Hal Hfl].
    apply Z.leb_le in Hal.
    pose proof (co_know _ _ _ _ _ HC) as HKN.
    destruct (know_lookup RSEGS (kn cs) b k 4 true [] []) as [ve scs hs0|scs hs0|] eqn:Hlk; try discriminate.
    destruct scs; [|discriminate].
    destruct (compute (extK (kn cs) ve)) as [new|] eqn:Hcomp; [|discriminate].
    destruct (carry [SE (SA b k) 4 new] (kn cs) []) as [[kn' scs2] hs] eqn:Hcar.
    destruct scs2; [|discriminate].
    lazymatch type of H with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. clear H.
    pose proof (flat_b_sound E M (kn cs) b k 4 HKN Hfl) as HF.
    pose proof (know_lookup_sound RSEGS E M (kn cs) b k 4 true [] [] HKN ltac:(lia) ltac:(lia)) as HL.
    rewrite Hlk in HL. destruct (HL ltac:(constructor) HF) as (bs & Hrd & Hlen & Hval).
    pose proof (bytes_le_to_Z_bound bs) as Hbb. rewrite Hlen in Hbb. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in Hbb.
    exists b, k, ve, new, kn', (bytes_le_to_Z bs), hs.
    pose proof (split_lit_denot E (reg cs ra) b k Hs) as Hden.
    assert (Hadr : adenot E (SA b k) = edenot E (reg cs ra)) by (rewrite Hden; reflexivity).
    repeat split; try assumption.
    - rewrite (reg_sound E cs R M model ra HC Hra). symmetry. exact Hadr.
    - destruct (ealign_sound RSEGS E M (kn cs) (reg cs ra) HKN) as [Hr [q Hq]]. rewrite Hadr, Hq.
      assert (Hd : (2 ^ 2 | 2 ^ ealign (kn cs) (reg cs ra))%Z) by (apply pow2_divide_le; lia).
      destruct Hd as [r' Hr']. rewrite Hr'. replace (q * (r' * 2 ^ 2))%Z with ((q * r') * 4)%Z by (change (2^2)%Z with 4%Z; ring).
      apply Z.mod_mul. lia.
    - rewrite Hrd. f_equal. symmetry. apply word_to_le_bytes_of_lez; [exact Hlen | lia].
    - lia.
    - lia.
    - rewrite (extK_denot RSEGS E M (kn cs) ve HKN). rewrite <- Hval. apply v_lw_of_extz. lia.
    - rewrite Hadr, Hden. replace 4%nat with (Z.to_nat 4) by reflexivity.
      eapply kwritable_sound; [exact HKN | exact HKN | exact Hkw | lia].
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia. }
  (* [comment removed for export] *)
  assert (LIBCAS : forall b k new, flat E (SA b k) 4 -> hull_apart U0 (kn cs) b k (ELit 4) = true ->
                   lib_ok (mem_denot E M [SE (SA b k) 4 new])).
  { intros b0 k0 new0 Hfl0 Hh0. eapply lib_ok_frame; [|exact (co_lib _ _ _ _ _ HC)].
    apply (log_hull_ok_sound E M (kn cs)); [exact (co_know _ _ _ _ _ HC) | cbn [log_flat]; split; [lia|]; split; [exact Hfl0 | exact I] |].
    unfold log_hull_ok. cbn [forallb]. change (Z.of_nat 4) with 4%Z. unfold hull_apart in Hh0. rewrite Hh0. reflexivity. }
  (* [comment removed for export] *)
  assert (REGS : forall (sr' : list expr) (R' : bvmap 5 word) (mods : list nat),
    (forall r : bv 5, (forall m, In m mods -> ridx r <> m) -> getr R' r = getr R r /\ nth (ridx r) sr' (ELit 0) = nth (ridx r) (s_regs (c_ss cs)) (ELit 0)) ->
    (forall r : bv 5, In (ridx r) mods -> getr R' r = edenot E (nth (ridx r) sr' (ELit 0))) ->
    regs_ok E sr' R').
  { intros sr' R' mods Hoth Hmod. apply regs_ok_pointwise. intros r Hr0.
    destruct (in_dec Nat.eq_dec (ridx r) mods) as [Hin|Hnin]; [exact (Hmod r Hin)|].
    destruct (Hoth r ltac:(intros m Hm X; apply Hnin; rewrite X; exact Hm)) as [-> ->].
    pose proof (co_regs _ _ _ _ _ HC r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [|exact X].
    exfalso. apply Hr0. apply bv_eq. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. exact Hb. }
  destruct c; unfold node_cas in Hn;
    (lazymatch type of Hn with (if ?x then _ else _) = _ => destruct x eqn:Hpc; [apply Z.eqb_eq in Hpc|discriminate] end).
  - (* [comment removed for export] *)
    unfold cas_or in Hn.
    destruct (CORE 14%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl & Hhull).
    assert (Hnew : mkAluK (kn cs) ALU_OR (extK (kn cs) ve) (reg cs 11) = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    destruct (cas_or_98ef8 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 11)) old Ra Hal Hrd Hold R11 Hst)
      as (R' & Hms & G10 & G12 & G13 & G15 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_or U0)) with (0x990b0%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_or_k U0)) with (0x990d0%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (v_or (Z_to_bv 64 old) (edenot E (reg cs 11)))))
      with (mem_denot E M [SE (SA b k) 4 new]).
    2:{ cbn [mem_denot]. f_equal. rewrite <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ (co_know _ _ _ _ _ HC)), Hve, alu_or.
        apply w2b4_or_sext. }
    apply HK. pose proof (LIBCAS b k new Hfl Hhull) as HLIB'. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL HLIB].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [15; 13; 12; 10]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 10%nat) | apply (Hm 12%nat) | apply (Hm 13%nat) | apply (Hm 15%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[H|[H|[]]]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G13, Hve. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
           rewrite G12, <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ HKN), Hve, alu_or. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10, Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
  - (* [comment removed for export] *)
    unfold cas_and in Hn.
    destruct (CORE 12%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl & Hhull).
    assert (Hnew : mkAluK (kn cs) ALU_AND (extK (kn cs) ve) (reg cs 13) = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 13 HC ltac:(lia)) as R13.
    destruct (cas_and_996d8 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 13)) old Ra Hal Hrd Hold R13 Hst)
      as (R' & Hms & G14 & G15 & G16 & G17 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_and U0)) with (0x99890%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_and_k U0)) with (0x998b0%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (v_and (Z_to_bv 64 old) (edenot E (reg cs 13)))))
      with (mem_denot E M [SE (SA b k) 4 new]).
    2:{ cbn [mem_denot]. f_equal. rewrite <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ (co_know _ _ _ _ _ HC)), Hve, alu_and.
        apply w2b4_and_sext. }
    apply HK. pose proof (LIBCAS b k new Hfl Hhull) as HLIB'. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL HLIB].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [17; 16; 15; 14]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 14%nat) | apply (Hm 15%nat) | apply (Hm 16%nat) | apply (Hm 17%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[H|[H|[]]]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 17)) with (17%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G17. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 16)) with (16%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G16, Hve. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
           rewrite G15, <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ HKN), Hve, alu_and. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
  - (* [comment removed for export] *)
    unfold cas_lock in Hn.
    destruct (CORE 13%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl & Hhull).
    destruct (expr_eqb (extK (kn cs) ve) (ELit 0) && expr_eqb (reg cs 11) (ELit 0))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hold0 H11z]. apply expr_eqb_eq in Hold0. apply expr_eqb_eq in H11z.
    assert (Hnew : reg cs 12 = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12.
    rewrite Hold0 in Hve. cbn [edenot] in Hve.
    assert (R11' : getr R (Z_to_bv 5 (Z.of_nat 11)) = v_lw (Z_to_bv 64 old)) by (rewrite R11, H11z; exact Hve).
    destruct (cas_lock_965f4 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 12)) old Ra Hal Hrd Hold R11' R12 Hst)
      as (R' & Hms & G14 & G15 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_lock U0)) with (0x967ac%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_lock_k U0)) with (0x967bc%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (edenot E (reg cs 12))))
      with (mem_denot E M [SE (SA b k) 4 new]) by (cbn [mem_denot]; rewrite <- Hnew; reflexivity).
    apply HK. pose proof (LIBCAS b k new Hfl Hhull) as HLIB'. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL HLIB].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [15; 14]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 14%nat) | apply (Hm 15%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, <- Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> SP.sr_vars_lt nx sr = true ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r) ->
  match rv with Some e => SP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq. clear -Hsv. revert i. induction sr as [|e t IH]; intros i; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; exact H2]. }
  assert (BASE : regs_ok (ext_call E nx R') (sr_fresh sr caller_saved nx) (match rv with Some e => regupd R' (Z_to_bv 5 10) (getr R (Z_to_bv 5 10)) | None => R' end)
          \/ True) by (right; exact I). clear BASE.
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  destruct rv as [e|].
  - destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
    destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10].
    + rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
      rewrite Ha0. apply (edenot_agree nx); [exact Hag | rewrite <- expr_vars_lt_eq; exact Hev].
    + destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
      * destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
        rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
        cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
      * rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
        rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
        destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
        exact X.
  - destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    * destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    * rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X.
Qed.

(* [comment removed for export] *)
Lemma know_ok_havoc : forall E M M' k b o n,
  know_ok RSEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_havoc k b o n).
Proof.
  intros E M M' k b o n HK Hout Hg. rewrite kn_havoc_eq. (* [comment removed for export] *) unfold kn_havoc_ref, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.   (* [comment removed for export] *)
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn|]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | |]; try constructor.
    eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

Lemma wview_off_image : forall M (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0xe6000 <= bv_unsigned x)%Z -> M x = None -> wview RSEGS M x = None.
Proof.
  intros M x Hx HM. unfold wview. rewrite HM. pose proof (u64_range x) as Hr.
  cbn -[Z.leb Z.add Z.of_N bv_unsigned andb].
  change (Z.of_N 0x10000%N) with 0x10000%Z. change (Z.of_N 0x32000%N) with 0x32000%Z.
  change (Z.of_N 0xac000%N) with 0xac000%Z. change (Z.of_N 0xb3000%N) with 0xb3000%Z.
  change (Z.of_N 0x22000%N) with 0x22000%Z. change (Z.of_N 0x7a000%N) with 0x7a000%Z.
  change (Z.of_N 0x7000%N) with 0x7000%Z. change (Z.of_N 0x33000%N) with 0x33000%Z.
  repeat (match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); cbn [andb] end); try reflexivity; exfalso; lia.
Qed.

Lemma kwritable_flat : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable allkn k b off n = true ->
  (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + n <= 2 ^ 64)%Z.
Proof.
  intros E M allkn k b off n Hall HK Hw. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  cbn [kwritable] in Hw. destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest Hw).
  cbn [kentry_ok] in HKK.
  lazymatch type of Hw with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  2: { lazymatch type of Hw with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest Hw)] end.
       apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
       apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
       destruct (xinside_sound RSEGS E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
       unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
       destruct HKK as [Hfl Hs]. destruct Hfl as (F1 & F2 & F3 & F4).
       unfold elenZ, estart in *. cbn [a_base a_off] in *. lia. }
  clear Hw. rename Hc0 into Hw.
  destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
  apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
  destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hw. rename Hw into H2.
  pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hx) as Hwl.
  destruct HKK as [(F1 & F2 & F3 & F4) _]. unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_ok_sound : forall E M k e n,
  know_ok RSEGS E M k -> rw_ok U0 k e n = true -> (0 < n)%Z ->
  let a := bv_unsigned (edenot E e) in
  store_ok RSEGS M (edenot E e) (Z.to_nat n) = true
  /\ (forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + n <= 0x10000 \/ 0xe6000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + n <= 2 ^ 64)%Z
  /\ (let (b, o) := split_lit e in bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
Proof.
  intros E M k e n HK H Hn. rewrite rw_ok_eq in H. destruct (split_lit e) as [b o] eqn:Hs.
  apply andb_prop in H as [Hw Hoff].
  pose proof (split_lit_denot E e b o Hs) as Hd. cbv zeta.
  pose proof (kwritable_flat E M k k b o n HK HK Hw) as FL.
  assert (Ha : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
  { rewrite Hd, u64_lit by lia. reflexivity. }
  rewrite Ha.
  pose proof (kwritable_sound E M k k b o n HK HK Hw ltac:(lia)) as Hst.
  rewrite off_image_eq, ISPAN_eq in Hoff. pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite u64_lit in Himg by lia.
  split; [rewrite Hd; exact Hst|]. split; [|split; [lia | split; [lia | split; [lia | reflexivity]]]].
  intros i Hi.
  pose proof (store_ok_all RSEGS M (Z.to_nat n) (Z_to_bv 64 (bv_unsigned (edenot E b) + o))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst
                (Z_to_bv 64 (bv_unsigned (edenot E b) + o + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

Lemma know_ok_havoc_e : forall E M M' k e n m,
  know_ok RSEGS E M k -> rw_ok U0 k e m = true -> (0 < m)%Z -> (0 <= n < 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned x < bv_unsigned (edenot E e) \/ bv_unsigned (edenot E e) + n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (havoc_e k e n).
Proof.
  intros E M M' k e n m HK Hrw Hm Hn Hout Hg. unfold havoc_e.
  destruct (rw_ok_sound E M k e m HK Hrw Hm) as (_ & _ & _ & _ & _ & Hsplit).
  destruct (split_lit e) as [b o] eqn:Hs.
  apply (know_ok_havoc E M); [exact HK | | exact Hg].
  intros x Hx. apply Hout. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite elenZ_lit in Hx by lia.
  rewrite Hsplit. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma rw_ok_x_sound : forall E M k e n,
  know_ok RSEGS E M k -> rw_ok_x U0 k e n = true ->
  let a := bv_unsigned (edenot E e) in
  let N := elenZ E n in
  (forall m, (Z.of_nat m <= N)%Z -> store_ok RSEGS M (edenot E e) m = true)
  /\ (forall i, (0 <= i < N)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + N <= 0x10000 \/ 0xe6000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + N <= 2 ^ 64)%Z
  /\ (let (b, o) := split_lit e in bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z)
  /\ (0 < N)%Z.
Proof.
  intros E M k e n HK H. rewrite rw_ok_x_eq in H. destruct (split_lit e) as [b o] eqn:Hs.
  apply andb_prop in H as [Hw Hoff]. apply andb_prop in Hw as [Hlo Hw].
  destruct (xlo k n) as [l|] eqn:Hxl; [|discriminate]. apply Z.ltb_lt in Hlo.
  pose proof (xlo_sound RSEGS E M k n l HK Hxl) as Hl.
  pose proof (split_lit_denot E e b o Hs) as Hd. cbv zeta.
  destruct (kwritable_x_sound E M k k b o n HK HK Hw) as (Hst & F1 & F2).
  assert (Ha : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
  { rewrite Hd, u64_lit by (unfold elenZ in F2; lia). reflexivity. }
  rewrite Ha.
  rewrite off_image_x_eq, ISPAN_eq in Hoff. pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite elenZ_lit in Himg by lia. rewrite u64_lit in Himg by lia.
  pose proof (u64_range (edenot E n)) as Hnr. unfold elenZ in *.
  split; [intros m Hm; rewrite Hd; apply Hst; exact Hm|].
  split; [|split; [lia | split; [lia | split; [lia | split; [reflexivity | lia]]]]].
  intros i Hi.
  pose proof (Hst (Z.to_nat (bv_unsigned (edenot E n))) ltac:(rewrite Z2Nat.id by lia; lia)) as Hst'.
  pose proof (store_ok_all RSEGS M (Z.to_nat (bv_unsigned (edenot E n))) (Z_to_bv 64 (bv_unsigned (edenot E b) + o))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst'
                (Z_to_bv 64 (bv_unsigned (edenot E b) + o + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

Lemma know_ok_havoc_x : forall E M M' k e n,
  know_ok RSEGS E M k -> rw_ok_x U0 k e n = true ->
  (forall x : word, (bv_unsigned x < bv_unsigned (edenot E e) \/ bv_unsigned (edenot E e) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (havoc_x k e n).
Proof.
  intros E M M' k e n HK Hrw Hout Hg. unfold havoc_x.
  destruct (rw_ok_x_sound E M k e n HK Hrw) as (_ & _ & _ & _ & _ & Hsplit & _).
  destruct (split_lit e) as [b o] eqn:Hs.
  apply (know_ok_havoc E M); [exact HK | | exact Hg].
  intros x Hx. apply Hout. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite Hsplit. exact Hx.
Qed.

Lemma apart_x_sound : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_x k e1 n1 e2 n2 = true ->
  rw_ok_x U0 k e1 n1 = true -> rw_ok_x U0 k e2 n2 = true ->
  (bv_unsigned (edenot E e1) + elenZ E n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H R1 R2. rewrite apart_x_eq in H.
  destruct (rw_ok_x_sound E M k e1 n1 HK R1) as (_ & _ & _ & _ & _ & Sa1 & _).
  destruct (rw_ok_x_sound E M k e2 n2 HK R2) as (_ & _ & _ & _ & _ & S2 & _).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite Sa1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma store_ok_prefix : forall M (a : word) n k, (k <= n)%nat -> store_ok RSEGS M a n = true -> store_ok RSEGS M a k = true.
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a k Hk H.
  - assert (k = 0)%nat by lia. subst k. reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [store_ok] in *.
    destruct (wview RSEGS M a); [|discriminate]. apply IH; [lia | exact H].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined : forall M (a : Z) k,
  (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat k)%Z -> M (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn RSEGS M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros M a k. revert a. induction k as [|k IH]; intros a Ha Hnw Hdef.
  - exists []. split; reflexivity.
  - cbn [rdn]. destruct (M (Z_to_bv 64 a)) as [b|] eqn:HM.
    2:{ exfalso. apply (Hdef 0%Z ltac:(lia)). rewrite Z.add_0_r. exact HM. }
    destruct (IH (a + 1)%Z ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 1 + i)%Z with (a + (1 + i))%Z by lia; apply Hdef; lia))
      as (bs & Hbs & Hlen).
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1%Z.
        rewrite Z.add_mod_idemp_l by lia. reflexivity. }
    rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma ehi_sound : forall E M k e hi, know_ok RSEGS E M k -> ehi k e = Some hi -> (bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M k e hi HK H. unfold ehi in H. destruct e;
    try (destruct (erange k _) as [[lo' hi']|] eqn:Her; [|discriminate]; injection H as <-; exact (proj2 (erange_sound RSEGS E M k _ lo' hi' HK Her))).
  injection H as <-. cbn [edenot]. rewrite u_lit64. lia.
Qed.

Lemma elo_sound : forall E M k e lo, know_ok RSEGS E M k -> elo k e = Some lo -> (lo <= bv_unsigned (edenot E e))%Z.
Proof.
  intros E M k e lo HK H. unfold elo in H. destruct e;
    try (destruct (erange k _) as [[lo' hi']|] eqn:Her; [|discriminate]; injection H as <-; exact (proj1 (erange_sound RSEGS E M k _ lo' hi' HK Her))).
  injection H as <-. cbn [edenot]. rewrite u_lit64. lia.
Qed.

Lemma apart_e_sound : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_e k e1 n1 e2 n2 = true ->
  rw_ok U0 k e1 n1 = true -> rw_ok U0 k e2 n2 = true -> (0 < n1)%Z -> (0 < n2)%Z ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2) \/ bv_unsigned (edenot E e2) + n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H R1 R2 Hn1 Hn2. rewrite apart_e_eq in H.
  destruct (rw_ok_sound E M k e1 n1 HK R1 Hn1) as (_ & _ & _ & _ & _ & Sa1).
  destruct (rw_ok_sound E M k e2 n2 HK R2 Hn2) as (_ & _ & _ & _ & _ & S2).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite Sa1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma apart_xe_sound : forall E M k e1 n1 e2 n2 m2,
  know_ok RSEGS E M k -> apart_x k e1 (ELit n1) e2 n2 = true ->
  rw_ok U0 k e1 n1 = true -> rw_ok U0 k e2 m2 = true -> (0 < n1 < 2 ^ 64)%Z -> (0 < m2)%Z ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 m2 HK H R1 R2 Hn1 Hm2. rewrite apart_x_eq in H.
  destruct (rw_ok_sound E M k e1 n1 HK R1 ltac:(lia)) as (_ & _ & _ & _ & _ & Sa1).
  destruct (rw_ok_sound E M k e2 m2 HK R2 Hm2) as (_ & _ & _ & _ & _ & S2).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite (elenZ_lit E n1) in Hd by lia.
  rewrite Sa1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma apart_e_loc : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_e k e1 n1 e2 n2 = true ->
  (let (b, o) := split_lit e1 in bv_unsigned (edenot E e1) = (bv_unsigned (edenot E b) + o)%Z) ->
  (let (b, o) := split_lit e2 in bv_unsigned (edenot E e2) = (bv_unsigned (edenot E b) + o)%Z) ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2) \/ bv_unsigned (edenot E e2) + n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H Sa1 S2. rewrite apart_e_eq in H.
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite Sa1, S2. exact Hd.
Qed.

Lemma apart_x_loc : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_x k e1 n1 e2 n2 = true ->
  (let (b, o) := split_lit e1 in bv_unsigned (edenot E e1) = (bv_unsigned (edenot E b) + o)%Z) ->
  (let (b, o) := split_lit e2 in bv_unsigned (edenot E e2) = (bv_unsigned (edenot E b) + o)%Z) ->
  (bv_unsigned (edenot E e1) + elenZ E n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H Sa1 S2. rewrite apart_x_eq in H.
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite Sa1, S2. exact Hd.
Qed.

Lemma ret_lit_sound : forall E cs R M model r,
  cs_ok E cs R M model -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ (0 <= r < two64)%Z.
Proof.
  intros E cs R M model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound E cs R M model 1 HC ltac:(lia)) as R1. rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.

(* [comment removed for export] *)
Lemma kept_of_not_caller_saved : forall (r : bv 5) (kept : list (bv 5)),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> In (Z_to_bv 5 (Z.of_nat k)) kept) ->
  r <> 0%bv -> ~ In (ridx r) caller_saved -> In r kept.
Proof.
  intros r kept Hk Hr0 Hn. pose proof (ridx_range r) as Hrr.
  assert (Hr : ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold caller_saved in Hn. cbn [In] in Hn.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ ridx r = k).
  { exists (ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (reg_of_ridx r k Hrk). apply Hk. exact Hink.
Qed.

Lemma slots_vars_lt_filter : forall b f ss, slots_vars_lt b ss = true -> slots_vars_lt b (List.filter f ss) = true.
Proof.
  intros b f ss H. unfold slots_vars_lt in *. apply forallb_forall. intros x Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (forallb_forall _ _) H x Hin).
Qed.

Lemma slots_vars_lt_keep : forall b k ub uk un ss, slots_vars_lt b ss = true -> slots_vars_lt b (slots_keep k ub uk un ss) = true.
Proof. intros. unfold slots_keep. apply slots_vars_lt_filter. assumption. Qed.

Lemma fresh_ok_slots : forall cs, fresh_ok nx0 cs = true -> slots_vars_lt (s_next (c_ss cs)) (c_slots cs) = true.
Proof.
  intros cs H. unfold fresh_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H Hs]. exact Hs.
Qed.

Lemma after_call_fresh : forall cs ret rv k' cs', after_call nx0 cs ret rv k' = Some cs' -> fresh_ok nx0 cs = true.
Proof.
  intros cs ret rv k' cs' H. unfold after_call in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma after_call_sound : forall cs ret rv k' cs' E R R' M M' model ss,
  after_call nx0 cs ret rv k' = Some cs' -> cs_ok E cs R M model ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r) ->
  match rv with Some e => getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok RSEGS E M' k' ->
  slots_ok E M' ss -> slots_vars_lt (s_next (c_ss cs)) ss = true ->
  lib_ok M' ->
  cs_ok (ext_call E (s_next (c_ss cs)) R') (set_slots cs' ss) R' M' model /\ pc (set_slots cs' ss) = ret.
Proof.
  intros cs ret rv k' cs' E R R' M M' model ss H HC Hkept Hrv HK' HSS Hssv HLIB'.
  unfold after_call in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  lazymatch type of H with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. subst cs'. clear H.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv].
  apply andb_prop in Hfresh as [Hsv _]. apply Nat.leb_le in Hnx0.
  split; [|reflexivity].
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL HLIB].
  constructor; cbn [set_slots c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - apply (regs_after_call E (s_regs (c_ss cs)) R R'); [exact HR | exact Hsv | exact Hkept |].
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_ext; [apply ext_call_agree | exact Hkv | exact HK'].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - eapply vm_ok_ext; [apply ext_call_agree | exact Hmv | exact (max1_le_0 _ _ Hnx0) | exact HV].   (* [comment removed for export] *)
  - eapply slots_ok_ext; [apply ext_call_agree | exact Hssv | exact HSS].
  - exact HLIB'.
Qed.

Lemma fresh_ok_nx0 : forall cs, fresh_ok nx0 cs = true -> (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs H. unfold fresh_ok in H. apply andb_prop in H as [_ H]. apply Nat.leb_le in H. exact (max1_le_l _ _ H).
Qed.

(* [comment removed for export] *)
Lemma fresh_ok_sp0 : forall cs, fresh_ok nx0 cs = true -> (SP0V < s_next (c_ss cs))%nat.
Proof.
  intros cs H. unfold fresh_ok in H. apply andb_prop in H as [_ H]. apply Nat.leb_le in H. exact (max1_le_0 _ _ H).
Qed.

Lemma after_call_nx0 : forall cs ret rv k' cs', after_call nx0 cs ret rv k' = Some cs' ->
  (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs ret rv k' cs' H. unfold after_call in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [apply fresh_ok_nx0; exact Hf | cbn [andb] in H; discriminate].
Qed.

End FX1.

(* [comment removed for export] *)
Definition enframe_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe U0 -> call_enframe RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Definition enframe_x_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe U0 -> call_enframe_x RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition enframe2_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe U0 -> call_enframe2 RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Definition freepro_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_freepro U0 -> call_freepro RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition stdio_write_sound_stmt : Prop := forall (fx : FPState) cs cs' fd bs E R M model T,
  cs_ok E cs R M model -> pc cs = t_stdio_write U0 ->
  node_stdio_write RSEGS U0 nx0 cs = Some (fd, bs, cs') ->
  T [] ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz fd bs) T).

(* [comment removed for export] *)
Definition lib_sound_stmt : Prop := forall (fx : FPState), LibIface.frm_zero fx -> forall cs cs' E R M model T,
  cs_ok E cs R M model -> (0 <= t_lib U0)%Z -> pc cs = t_lib U0 -> call_lib RSEGS U0 nx0 cs = Some cs' ->
  (forall (fx' : FPState), LibIface.frm_zero fx' -> forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of (fx:=fx') R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition mainret_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_main_ret U0 -> call_mainret U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition printf_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_printf U0 -> call_printf RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition exitcall_sound_stmt : Prop := forall (fx : FPState) cs bs code E R M model,
  cs_ok E cs R M model -> pc cs = t_exitc U0 -> node_exitcall RSEGS U0 cs = Some (bs, code) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz 1 bs) (t_exit (Z_to_bv 64 code) (m_fs model))).

(* [comment removed for export] *)
Definition inflate_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> (0 <= t_inflate U0)%Z -> pc cs = t_inflate U0 -> call_inflate RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Definition u2tail_sound_stmt : Prop := forall (fx : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> (0 <= t_u2tail U0)%Z -> pc cs = t_u2tail U0 -> call_u2tail U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Hypothesis call_enframe_sound : enframe2_sound_stmt.
Hypothesis call_freepro_sound : freepro_sound_stmt.
Hypothesis node_stdio_write_sound : stdio_write_sound_stmt.
Hypothesis call_lib_sound : lib_sound_stmt.
Hypothesis call_mainret_sound : mainret_sound_stmt.
Hypothesis call_printf_sound : printf_sound_stmt.
Hypothesis node_exitcall_sound : exitcall_sound_stmt.
Hypothesis call_inflate_sound : inflate_sound_stmt.
Hypothesis call_u2tail_sound : u2tail_sound_stmt.

Section FX2.
Context {fx : FPState}.
Hypothesis FRM : LibIface.frm_zero fx.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_okb_sound : forall E M k b off n,
  know_ok RSEGS E M k -> rw_okb U0 k b off n = true -> (0 < n)%Z ->
  let a := (bv_unsigned (edenot E b) + off)%Z in
  store_ok RSEGS M (Z_to_bv 64 a) (Z.to_nat n) = true
  /\ (forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + n <= 0x10000 \/ 0xe6000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + n <= 2 ^ 64)%Z.
Proof.
  intros E M k b off n HK H Hn. rewrite rw_okb_eq in H. apply andb_prop in H as [Hw Hoff]. cbv zeta.
  pose proof (kwritable_flat E M k k b off n HK HK Hw) as FL.
  pose proof (kwritable_sound E M k k b off n HK HK Hw ltac:(lia)) as Hst.
  rewrite off_image_eq, ISPAN_eq in Hoff. pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite u64_lit in Himg by lia.
  split; [exact Hst|]. split; [|lia].
  intros i Hi.
  pose proof (store_ok_all RSEGS M (Z.to_nat n) (Z_to_bv 64 (bv_unsigned (edenot E b) + off))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst
                (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kn_contra_sound : forall E M k, know_ok RSEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound RSEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    (destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.

Lemma node_call_sound : forall sm (args : list expr) cs cs' E R M model T,
  cs_ok E cs R M model ->
  match sm with
  | SumMemcpy => pc cs = t_memcpy U0 /\ call_memcpy U0 nx0 cs = Some cs'
  | SumLib => pc cs = t_lib U0 /\ ((0 <=? t_lib U0)%Z = true /\ call_lib RSEGS U0 nx0 cs = Some cs')
  | SumEnframe => pc cs = t_enframe U0 /\ call_enframe2 RSEGS U0 nx0 cs = Some cs'
  | SumFreePro => pc cs = t_freepro U0 /\ call_freepro RSEGS U0 nx0 cs = Some cs'
  | SumMainRet => pc cs = t_main_ret U0 /\ call_mainret U0 nx0 cs = Some cs'
  | SumPrintf => pc cs = t_printf U0 /\ call_printf RSEGS U0 nx0 cs = Some cs'
  | SumInflate => pc cs = t_inflate U0 /\ ((0 <=? t_inflate U0)%Z = true /\ call_inflate RSEGS U0 nx0 cs = Some cs')
  | SumU2Tail => pc cs = t_u2tail U0 /\ ((0 <=? t_u2tail U0)%Z = true /\ call_u2tail U0 nx0 cs = Some cs')
  end ->
  (forall (fx' : FPState), LibIface.frm_zero fx' -> forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of (fx:=fx') R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros sm args cs cs' E R M model T HC Hsm HKall.
  pose proof (HKall fx FRM) as HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct sm; destruct Hsm as [Hpc Hn].
  2:{ (* [comment removed for export] *)
      destruct Hn as [Hg Hn]. apply Z.leb_le in Hg. exact (call_lib_sound fx FRM cs cs' E R M model T HC Hg Hpc Hn HKall). }
  6:{ (* [comment removed for export] *)
      destruct Hn as [Hg Hn]. apply Z.leb_le in Hg. exact (call_inflate_sound fx cs cs' E R M model T HC Hg Hpc Hn HK). }
  6:{ (* [comment removed for export] *)
      destruct Hn as [Hg Hn]. apply Z.leb_le in Hg. exact (call_u2tail_sound fx cs cs' E R M model T HC Hg Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_enframe_sound fx cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_freepro_sound fx cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_mainret_sound fx cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_printf_sound fx cs cs' E R M model T HC Hpc Hn HK). }
  - (* [comment removed for export] *)
    unfold call_memcpy in Hn.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (ehi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
    match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hcond Hap].
    apply andb_prop in Hcond as [Hcond Hrs]. apply andb_prop in Hcond as [Hcond Hrd].
    apply andb_prop in Hcond as [Hn0 Hn40]. apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn40.
    destruct (ehi (kn cs) (reg cs 10)) as [dh|] eqn:Hdh; [|discriminate].
    destruct (ehi (kn cs) (reg cs 11)) as [sh|] eqn:Hsh; [|discriminate].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
    destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hnhi) as Hnle.
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hdh) as Hdle.
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hsh) as Hsle.
    set (d := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *. set (nw := edenot E (reg cs 12)) in *.
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 12) HKN Hrd) as (Dst & Ddef & Dimg & D0 & Dnw & Dspl & Dpos).
    fold d in Dst, Ddef, Dimg, D0, Dnw. unfold elenZ in Dst, Ddef, Dimg, Dnw, Dpos. fold nw in Dst, Ddef, Dimg, Dnw, Dpos.
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 11) (reg cs 12) HKN Hrs) as (Sst & Sdef & Simg & S0 & Snw & _ & _).
    fold sr in Sst, Sdef, Simg, S0, Snw. unfold elenZ in Sst, Sdef, Simg, Snw. fold nw in Sst, Sdef, Simg, Snw.
    pose proof (apart_x_sound E M (kn cs) _ _ _ _ HKN Hap Hrd Hrs) as Hdisj. unfold elenZ in Hdisj. fold d sr nw in Hdisj.
    pose proof (u64_range nw) as Hnwr.
    destruct (rdn_defined M (bv_unsigned sr) (Z.to_nat (bv_unsigned nw)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros i Hi; apply Sdef; rewrite Z2Nat.id in Hi by lia; lia)) as (bs & Hbs & Hlen).
    rewrite Z_to_bv_bv_unsigned in Hbs.
    assert (HOK : mcH M d sr (bv_unsigned nw) bs).
    { constructor.
      - lia.
      - exact Hlen.
      - rewrite Hlen. exact Hbs.
      - rewrite Hlen. apply Dst. rewrite Z2Nat.id by lia. lia.
      - lia.
      - lia.
      - lia. }
    pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12.
    destruct (ref_memcpy M d sr (bv_unsigned nw) bs (seg_rom RSEGS) HOK R (Z_to_bv 64 ret) Hrok R1 R10 R11
                ltac:(rewrite Z_to_bv_bv_unsigned; exact R12)) as (R' & Hms & Hkeeps).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_memcpy U0)) with (0xa6e20%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    destruct (after_call nx0 cs ret (Some (reg cs 10)) (havoc_x (kn cs) (reg cs 10) (reg cs 12))) as [csa|] eqn:Hac; [|discriminate].
    destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd. cbn in Dspl.
    injection Hn as <-.
    destruct (after_call_sound cs ret (Some (reg cs 10)) (havoc_x (kn cs) (reg cs 10) (reg cs 12)) csa E R R' M (wbytes M d bs) model
                (slots_keep (kn cs) db dk (reg cs 12) (c_slots cs)) Hac HC) as [HC' Hpc'].
    + intros r Hr0 Hnin. apply (keeps_getr R R' r Hkeeps).
      apply kept_of_not_caller_saved; [| exact Hr0 | exact Hnin].
      intros k Hk. cbn [In] in Hk. unfold callee_kept.
      repeat (destruct Hk as [<-|Hk]; [cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
        repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end; fail | ]).
      all: try (destruct Hk).
    + cbv delta [d] in R10. rewrite <- R10. apply (keeps_getr R R' _ Hkeeps). unfold callee_kept. cbn [In].
      do 6 right. left. apply bv_eq. reflexivity.
    + eapply know_ok_havoc_x; [exact HKN | exact Hrd | | apply wbytes_grows].
      intros x Hx. fold d in Hx. unfold elenZ in Hx. fold nw in Hx. apply wbytes_out; rewrite Hlen, Z2Nat.id by lia; lia.
    + eapply slots_keep_sound; [exact HKN | exact (co_slots _ _ _ _ _ HC) |].
      unfold estart, elenZ. cbn [a_base a_off]. fold nw. fold d in Dspl. rewrite <- Dspl.
      intros x Hx. apply wbytes_out; rewrite Hlen, Z2Nat.id by lia; lia.
    + apply slots_vars_lt_keep. apply fresh_ok_slots. eapply after_call_fresh. exact Hac.
    + (* [comment removed for export] *)
      eapply lib_ok_frame; [|exact (co_lib _ _ _ _ _ HC)]. intros x Hx. unfold HULL_LO, HULL_HI in Hx. cbn in Hx.
      fold d in Dimg. unfold elenZ in Dimg. fold nw in Dimg.
      pose proof (u64_range nw) as Hnwr'. pose proof (u64_range d) as Hdr'.
      apply wbytes_out; rewrite Hlen, Z2Nat.id by lia; [lia|]. rewrite (u64_lit x) by lia. lia.
    + rewrite <- Hpc'. apply (HK (ext_call E (s_next (c_ss cs)) R') R' (wbytes M d bs)); [|exact HC'].
      eapply env_agree_le; [apply ext_call_agree | eapply after_call_nx0; exact Hac].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_vars : forall bfuel fuel p cs s,
  check RSEGS IT U0 nx0 bfuel fuel cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros p cs s Hc; [discriminate|].
  cbn [check] in Hc.
  destruct p as [kf ks|k|k|k| |k|sm args k|c k|e mid k1 k2| | |r mid k1 k2| |body k].
  14: { (* [comment removed for export] *)
       destruct (collect RSEGS IT U0 nx0 bfuel cs body) as [[|cs1 rest]|c q cs']; try discriminate.
       destruct (merge RSEGS nx0 cs1 rest) as [csm|]; [|discriminate]. exact (IH k csm s Hc). }
  13: { discriminate. }
  12: { (* [comment removed for export] *)
       destruct (erange (kn cs) (reg cs r)) as [[lo hi]|]; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange (reg cs r) lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange (reg cs r) (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH k1 _ s1 H1). }
  10: { destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity. }
  9: { destruct (SP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
       destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv.
       rewrite (IH k1 _ s1 H1), (IH k2 _ s2 H2). reflexivity. }
  all: destruct (run_block_gc RSEGS IT U0 bfuel (STOPS U0) cs) as [cs1|] eqn:Hrb; [|discriminate].
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_mmap U0 nx0 cs1) as [[csf css]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel csf kf) as [sf|] eqn:Hf; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel css ks) as [ss|] eqn:Hs; [|discriminate]. injection Hc as <-.
    pose proof (IH kf csf sf Hf) as A. pose proof (IH ks css ss Hs) as B.
    unfold salt2. destruct sf; destruct ss; cbn [shape_vars_lt] in *; rewrite ?A, ?B; reflexivity.
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_munmap U0 cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_ioctl cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - destruct (Z.eqb (pc cs1) (t_stdio_write U0)); [|discriminate].
    destruct (node_stdio_write RSEGS U0 nx0 cs1) as [[[fd bs] cs2]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel cs2 k) as [s2|] eqn:H2; [|discriminate]. injection Hc as <-. cbn [shape_vars_lt].
    exact (IH k cs2 s2 H2).
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_exit cs1); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (negb (is_ecall_at RSEGS cs1) && existsb (Z.eqb (pc cs1)) (STOPS U0))%bool; [|discriminate].
    exact (IH k cs1 s Hc).
  - destruct sm;
      match type of Hc with (match ?r with _ => _ end = _) => destruct r as [cs2|] eqn:Hn; [|discriminate] end; exact (IH k cs2 s Hc).
  - destruct (node_cas RSEGS U0 c cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_exitc U0)); [|discriminate].
    destruct (node_exitcall RSEGS U0 cs1) as [[[|b bs] code]|]; [| |discriminate]; injection Hc as <-; reflexivity.
Qed.

Lemma node_mmap_nx0 : forall cs csf css, node_mmap U0 nx0 cs = Some (csf, css) ->
  (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs csf css Hn. unfold node_mmap in Hn.
  repeat match type of Hn with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | (_ && _)%bool => destruct x eqn:?HC; [|discriminate]
      | _ => destruct x; try discriminate
      end
  end.
  match goal with H : (_ && fresh_ok nx0 cs)%bool = true |- _ => apply andb_prop in H as [_ Hf]; apply fresh_ok_nx0; exact Hf end.
Qed.

(* [comment removed for export] *)

Lemma t_alt2_idem : forall T : TSet, t_eq (t_alt2 T T) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.

Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof.
  intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [|congruence]. intros n Hn. rewrite (A1 n Hn). apply A2. exact Hn.
Qed.
Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros b E. split; [intros; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
Definition ext_all (E : env) (next : nat) (R : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb next n && Nat.ltb n (next + 32))%bool then getr R (Z_to_bv 5 (Z.of_nat (n - next))) else ev E n) (eb E).
Lemma ext_all_agree : forall E next R, env_agree next E (ext_all E next R).
Proof.
  intros E next R. split; [|reflexivity]. intros n Hn. cbn [ext_all ev].
  destruct (Nat.leb_spec next n); [lia|]. reflexivity.
Qed.
Lemma ext_all_at : forall E next R i, (i < 32)%nat -> ev (ext_all E next R) (next + i)%nat = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros E next R i Hi. cbn [ext_all ev].
  replace (Nat.leb next (next + i) && Nat.ltb (next + i) (next + 32))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
      | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
      end; subst; reflexivity.
Qed.
Lemma sslot_eqb_eq : forall x y, sslot_eqb x y = true -> x = y.
Proof.
  intros [a1 a2 a3 a4 a5 a6 a7] [b1 b2 b3 b4 b5 b6 b7] H. unfold sslot_eqb in H. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p] in H.
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    end; subst; reflexivity.
Qed.
Lemma smap_eqb_eq : forall x y, smap_eqb x y = true -> x = y.
Proof.
  intros [a1 a2 a3] [b1 b2 b3] H. unfold smap_eqb in H. cbn [sm_base sm_len sm_exact] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply Bool.eqb_prop in H3. subst. reflexivity.
Qed.
Lemma list_eqb_eq : forall (X : Type) (f : X -> X -> bool), (forall x y, f x y = true -> x = y) ->
  forall a b, list_eqb f a b = true -> a = b.
Proof.
  intros X f Hf a. induction a as [|x a IH]; intros [|y b] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hf _ _ H1), (IH _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma existsb_kentry : forall K kn, existsb (kentry_eqb K) kn = true -> In K kn.
Proof.
  intros K kn H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.
Lemma existsb_sslot : forall x ss, existsb (sslot_eqb x) ss = true -> In x ss.
Proof.
  intros x ss H. apply existsb_exists in H as (x' & Hin & Heq). apply sslot_eqb_eq in Heq. subst x'. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma fold_max_ge_Z : forall (f : cstate -> Z) l z0 st,
  In st l -> (f st <= fold_right (fun cs m => Z.max (f cs) m) z0 l)%Z.
Proof.
  intros f l z0 st. induction l as [|a l IH]; intros Hin; [destruct Hin|].
  cbn [fold_right]. destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.
Lemma fold_max_ge_Z0 : forall (f : cstate -> Z) l z0,
  (z0 <= fold_right (fun cs m => Z.max (f cs) m) z0 l)%Z.
Proof. intros f l z0. induction l as [|a l IH]; cbn [fold_right]; lia. Qed.

(* [comment removed for export] *)
Definition acc_ok (acc : list (option expr)) (sr : list expr) : Prop :=
  length acc = length sr /\ forall i e, nth_error acc i = Some (Some e) -> nth_error sr i = Some e.

Lemma acc_ok_init : forall sr, acc_ok (map Some sr) sr.
Proof.
  intros sr. split; [apply length_map|]. intros i e H.
  rewrite nth_error_map in H. destruct (nth_error sr i); [cbn in H; congruence | discriminate].
Qed.

Lemma regs_meet_spec : forall acc sr,
  length acc = length sr ->
  length (regs_meet acc sr) = length sr
  /\ (forall i e, nth_error (regs_meet acc sr) i = Some (Some e) -> nth_error acc i = Some (Some e) /\ nth_error sr i = Some e).
Proof.
  induction acc as [|a acc IH]; intros [|e sr] Hl; cbn [regs_meet length] in *; try discriminate.
  - split; [reflexivity|]. intros [|i] e H; discriminate.
  - injection Hl as Hl. destruct (IH sr Hl) as [L S]. split; [rewrite L; reflexivity|].
    intros [|i] e0 H; cbn [nth_error] in H |- *.
    + destruct a as [e1|]; [|discriminate]. destruct (expr_eqb e1 e) eqn:Q; [|discriminate].
      injection H as <-. apply expr_eqb_eq in Q. subst e1. auto.
    + exact (S i e0 H).
Qed.

Lemma acc_ok_meet_new : forall acc sr, length acc = length sr -> acc_ok (regs_meet acc sr) sr.
Proof.
  intros acc sr Hl. destruct (regs_meet_spec acc sr Hl) as [L S]. split; [exact L|]. intros i e H. apply S. exact H.
Qed.
Lemma acc_ok_meet_old : forall acc sr sr0, length acc = length sr -> acc_ok acc sr0 -> acc_ok (regs_meet acc sr) sr0.
Proof.
  intros acc sr sr0 Hl [L0 S0]. destruct (regs_meet_spec acc sr Hl) as [L S]. split; [lia|].
  intros i e H. apply S0. apply S. exact H.
Qed.

Lemma merge_acc_ok : forall rest acc0 sr0 st,
  (forall cs, In cs rest -> length (s_regs (c_ss cs)) = length sr0) ->
  acc_ok acc0 sr0 ->
  let acc := fold_right (fun cs acc => regs_meet acc (s_regs (c_ss cs))) acc0 rest in
  acc_ok acc sr0 /\ (In st rest -> acc_ok acc (s_regs (c_ss st))).
Proof.
  intros rest acc0 sr0 st Hlen H0. induction rest as [|c rest IH]; cbn [fold_right].
  - split; [exact H0 | intros []].
  - destruct IH as [A B]; [intros cs Hcs; apply Hlen; right; exact Hcs|].
    assert (HL : length (fold_right (fun cs acc => regs_meet acc (s_regs (c_ss cs))) acc0 rest) = length (s_regs (c_ss c))).
    { destruct A as [L _]. rewrite L. symmetry. apply Hlen. left. reflexivity. }
    split; [apply acc_ok_meet_old; [exact HL | exact A]|].
    intros [<-|Hin]; [apply acc_ok_meet_new; exact HL|].
    apply acc_ok_meet_old; [exact HL | apply B; exact Hin].
Qed.

Lemma nth_regs_fill : forall acc j next i d,
  nth i (regs_fill acc j next) d
  = match nth_error acc i with
    | Some (Some e) => e
    | Some None => EVar (next + j + i)
    | None => d
    end.
Proof.
  induction acc as [|[e|] acc IH]; intros j next i d.
  - destruct i; reflexivity.
  - destruct i as [|i]; cbn [regs_fill nth nth_error]; [reflexivity|]. rewrite IH.
    destruct (nth_error acc i) as [[?|]|]; try reflexivity. f_equal. lia.
  - destruct i as [|i]; cbn [regs_fill nth nth_error]; [f_equal; lia|]. rewrite IH.
    destruct (nth_error acc i) as [[?|]|]; try reflexivity. f_equal. lia.
Qed.

Lemma regs_kept_lt_nth : forall b acc i e, regs_kept_lt b acc = true -> nth_error acc i = Some (Some e) -> expr_vars_lt b e = true.
Proof.
  intros b acc. induction acc as [|[e0|] acc IH]; intros [|i] e H Hn; cbn [regs_kept_lt nth_error] in *; try discriminate.
  - apply andb_prop in H as [H1 H2]. injection Hn as <-. exact H1.
  - apply andb_prop in H as [H1 H2]. exact (IH i e H2 Hn).
  - exact (IH i e H Hn).
Qed.

Lemma nth_error_nth' : forall (l : list expr) i e d, nth_error l i = Some e -> nth i l d = e.
Proof. intros l i e d H. revert l H. induction i; intros [|x l] H; cbn in *; try discriminate; [congruence | apply IHi; exact H]. Qed.
Lemma nth_error_none_nth : forall (l : list expr) i d, nth_error l i = None -> nth i l d = d.
Proof. intros l i d H. revert l H. induction i; intros [|x l] H; cbn in *; try discriminate; try reflexivity. apply IHi; exact H. Qed.

Lemma merge_sound : forall cs1 rest csm st E R M model,
  merge RSEGS nx0 cs1 rest = Some csm -> In st (cs1 :: rest) -> cs_ok E st R M model ->
  exists E', env_agree nx0 E E' /\ cs_ok E' csm R M model /\ pc csm = pc st.
Proof.
  intros cs1 rest csm st E R M model Hm Hin HC.
  unfold merge in Hm.
  match type of Hm with context [merge_kn ?a ?b ?c ?d ?e ?f] =>
    destruct (merge_kn a b c d e f) as [[kn' j] tr] eqn:Hmk end.
  match type of Hm with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
  injection Hm as <-.
  apply andb_prop in Hcond as [Hcond Hnx]. apply andb_prop in Hcond as [Hcond Hmv]. apply andb_prop in Hcond as [Hcond Hslv].
  apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hrv]. apply andb_prop in Hcond as [Hall Hkv1].
  apply Nat.leb_le in Hnx.
  set (next := fold_right (fun cs m => Nat.max (s_next (c_ss cs)) m) (s_next (c_ss cs1)) rest) in *.
  set (acc := fold_right (fun cs acc => regs_meet acc (s_regs (c_ss cs))) (map Some (s_regs (c_ss cs1))) rest) in *.
  set (others := map (fun cs => (s_know (c_ss cs), kimg_ivs (s_know (c_ss cs)))) rest) in *.
  (* [comment removed for export] *)
  assert (HX : exists (first : bool) (i : nat), if first then st = cs1 else nth_error rest i = Some st).
  { destruct Hin as [<-|Hin']; [exists true, 0%nat; reflexivity|].
    apply In_nth_error in Hin' as (i & Hi). exists false, i. exact Hi. }
  destruct HX as (first & i & HSt).
  (* [comment removed for export] *)
  assert (ST : s_pc (c_ss st) = s_pc (c_ss cs1) /\ c_maps st = c_maps cs1 /\ length (s_regs (c_ss st)) = length (s_regs (c_ss cs1))
               /\ SP.kn_vars_lt next (s_know (c_ss st)) = true).
  { destruct Hin as [<-|Hin']; [repeat split; try reflexivity; exact Hkv1|].
    pose proof (proj1 (forallb_forall _ _) Hall st Hin') as X.
    apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
    apply Z.eqb_eq in X1. apply Nat.eqb_eq in X3. apply (list_eqb_eq _ _ smap_eqb_eq) in X2. auto. }
  destruct ST as (Spc & Smaps & Slen & Skv).
  set (E1 := ext_all E next R).
  set (ws := map (fun p => edenot E (if first then SPM.sel_first p else SPM.sel_other i p)) tr).
  set (E' := SPM.ext_cells E1 (next + 32) ws).
  assert (Hag1 : env_agree next E E1) by apply ext_all_agree.
  assert (Hag2 : env_agree (next + 32) E1 E') by apply SPM.ext_cells_agree.
  assert (Hag : env_agree next E E').
  { eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]. }
  exists E'.
  split; [eapply env_agree_le; [exact Hag | exact (max1_le_l _ _ Hnx)]|].
  split; [|unfold pc; cbn [c_ss s_pc]; symmetry; exact Spc].
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL HLIB].
  (* [comment removed for export] *)
  assert (ACC : acc_ok acc (s_regs (c_ss st))).
  { pose proof (merge_acc_ok rest (map Some (s_regs (c_ss cs1))) (s_regs (c_ss cs1)) st) as MA.
    cbv zeta in MA. destruct MA as [A B].
    - intros cs Hcs. pose proof (proj1 (forallb_forall _ _) Hall cs Hcs) as X.
      apply andb_prop in X as [X _]. apply andb_prop in X as [X X3]. apply Nat.eqb_eq in X3. exact X3.
    - apply acc_ok_init.
    - destruct Hin as [<-|Hin']; [exact A | exact (B Hin')]. }
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    rewrite nth_regs_fill. destruct ACC as [AL AS].
    destruct (nth_error acc (ridx r)) as [[e|]|] eqn:Hn.
    + pose proof (AS _ _ Hn) as Hsr.
      rewrite <- (edenot_agree next E E' e Hag (regs_kept_lt_nth _ _ _ _ Hrv Hn)).
      pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      rewrite (nth_error_nth' _ _ _ (ELit 0) Hsr) in X. exact X.
    + cbn [edenot]. replace (next + 0 + ridx r)%nat with (next + ridx r)%nat by lia.
      rewrite <- (proj1 Hag2 (next + ridx r)%nat ltac:(pose proof (ridx_range r); lia)).
      unfold E1. rewrite (ext_all_at E next R (ridx r) (ridx_range r)). rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    + (* [comment removed for export] *)
      pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      assert (Hn' : nth_error (s_regs (c_ss st)) (ridx r) = None).
      { apply nth_error_None. apply nth_error_None in Hn. lia. }
      rewrite (nth_error_none_nth _ _ (ELit 0) Hn') in X. cbn [edenot] in X |- *. exact X.
  - (* [comment removed for export] *)
    refine (SPM.merge_kn_sound RSEGS _ _ others _ _ _ _ _ Hmk _ first i (s_know (c_ss st)) next E E' M _ HK _ Hag _).
    + intros o Ho. unfold others in Ho. apply in_map_iff in Ho as (cs & <- & _). reflexivity.
    + destruct first; [subst st; split; [reflexivity | intros x Hx; exact Hx]|].
      unfold others. rewrite nth_error_map, HSt. reflexivity.
    + first [exact Skv | rewrite <- kn_vars_lt_eq; exact Skv | rewrite kn_vars_lt_eq; exact Skv].
    + intros t p Hp. unfold E'. rewrite Nat.add_0_r.
      apply SPM.ext_cells_at. unfold ws. rewrite nth_error_map, Hp. reflexivity.
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    rewrite <- Smaps. destruct HV as [V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11]. constructor; try assumption.
    + eapply smaps_ok_ext; [exact Hag | rewrite Smaps; exact Hmv | exact V2].
    + eapply Z.le_trans; [exact V3|]. destruct Hin as [<-|Hin']; [apply fold_max_ge_Z0 | apply (fold_max_ge_Z c_nmaps); exact Hin'].
    + eapply Z.le_trans; [exact V4|]. destruct Hin as [<-|Hin']; [apply fold_max_ge_Z0 | apply (fold_max_ge_Z c_live); exact Hin'].
    + (* [comment removed for export] *)
      rewrite <- (proj1 Hag SP0V (max1_le_0 _ _ Hnx)). exact V9.
  - (* [comment removed for export] *)
    eapply slots_ok_ext; [exact Hag | exact Hslv |].
    unfold slots_ok in *. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx1 Hall'].
    destruct Hin as [<-|Hin'].
    + exact (proj1 (Forall_forall _ _) HSL x Hx1).
    + pose proof (proj1 (forallb_forall _ _) Hall' st Hin') as X. apply existsb_sslot in X.
      exact (proj1 (Forall_forall _ _) HSL x X).
  - exact HLIB.
Qed.

End FX2.

(* [comment removed for export] *)
Lemma collect_sound : forall bfuel p cs sts,
  collect RSEGS IT U0 nx0 bfuel cs p = DOk sts ->
  forall (fx : FPState), LibIface.frm_zero fx -> forall E R M model T,
  cs_ok E cs R M model ->
  (forall st, In st sts -> forall (fx' : FPState), LibIface.frm_zero fx' -> forall E' R' M' model',
      env_agree nx0 E E' -> cs_ok E' st R' M' model' -> m_fs model' = m_fs model ->
      realizes RSEGS (cfg_of (fx:=fx') R' (pc st) M' model') T) ->
  realizes RSEGS (cfg_of (fx:=fx) R (pc cs) M model) T.
Proof.
  intros bfuel p. induction p as [kf IHf ks IHs|k IH|k IH|k IH| |k IH|sm args k IH|c k IH|e mid k1 IH1 k2 IH2| | |r mid k1 IH1 k2 IH2| |body IHb k IHk];
    intros cs sts Hc fx FRM E R M model T HC HH; cbn [collect] in Hc.
  all: try discriminate.
  (* [comment removed for export] *)
  14: { (* [comment removed for export] *)
        destruct (collect RSEGS IT U0 nx0 bfuel cs body) as [[|cs1 rest]|] eqn:Hb; try discriminate.
        destruct (merge RSEGS nx0 cs1 rest) as [csm|] eqn:Hm; [|discriminate].
        apply (IHb cs (cs1 :: rest) Hb fx FRM E R M model T HC).
        intros st Hst fx' FRM' E' R' M' model' Hag HC' Hfs.
        destruct (merge_sound cs1 rest csm st E' R' M' model' Hm Hst HC') as (E'' & Hag' & HCm & Hpc).
        rewrite <- Hpc.
        apply (IHk csm sts Hc fx' FRM' E'' R' M' model' T HCm).
        intros st2 Hst2 fx3 FRM3 E3 R3 M3 model3 Hag3 HC3 Hfs3. apply (HH st2 Hst2 fx3 FRM3 E3 R3 M3 model3).
        - eapply env_agree_trans; [exact Hag|]. eapply env_agree_trans; [exact Hag' | exact Hag3].
        - exact HC3.
        - rewrite Hfs3. exact Hfs. }
  12: { (* [comment removed for export] *)
        destruct (erange (kn cs) (reg cs r)) as [[lo hi]|] eqn:Hr; [|discriminate].
        destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
        destruct (collect RSEGS IT U0 nx0 bfuel (set_kn cs (KRange (reg cs r) lo mid :: kn cs)) k1) as [a|] eqn:H1; [|discriminate].
        destruct (collect RSEGS IT U0 nx0 bfuel (set_kn cs (KRange (reg cs r) (mid+1) hi :: kn cs)) k2) as [b|] eqn:H2; [|discriminate].
        injection Hc as <-.
        destruct (split_sound cs (reg cs r) mid lo hi E R M model HC Hr) as [HCl HCr].
        destruct (Z.leb_spec (bv_unsigned (edenot E (reg cs r))) mid) as [Hle|Hgt].
        - apply (IH1 _ a H1 fx FRM E R M model T (HCl Hle)). intros st Hst. apply HH. apply in_or_app. left. exact Hst.
        - apply (IH2 _ b H2 fx FRM E R M model T (HCr ltac:(lia))). intros st Hst. apply HH. apply in_or_app. right. exact Hst. }
  10: { (* [comment removed for export] *) destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
        exact (kn_contra_sound E M (kn cs) (co_know _ _ _ _ _ HC) Hk). }
  all: destruct (run_block_gc RSEGS IT U0 bfuel (STOPS U0) cs) as [cs1|] eqn:Hrb; [|discriminate].
  all: try discriminate.
  all: destruct (run_block_gc_sound IT IT_ok bfuel (STOPS U0) cs cs1 E R M model Hrb HC) as (R1 & M1 & Hms & HC1 & Hmaps).
  all: eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_mmap U0 nx0 cs1) as [[csf css]|] eqn:Hn; [|discriminate].
    destruct (collect RSEGS IT U0 nx0 bfuel csf kf) as [a|] eqn:Hf; [|discriminate].
    destruct (collect RSEGS IT U0 nx0 bfuel css ks) as [b|] eqn:Hs; [|discriminate].
    injection Hc as <-.
    eapply rz_conseq; [|apply t_alt2_idem].
    pose proof (node_mmap_nx0 cs1 csf css Hn) as Xle.
    eapply (node_mmap_sound cs1 csf css E R1 M1 model); [exact HC1 | exact Hec | exact Hn | |].
    + intros R' M' HC'. apply (IHf csf a Hf fx FRM E R' M' model T HC'). intros st Hst. apply HH. apply in_or_app. left. exact Hst.
    + intros av R' M' model' HC' Hfs.
      apply (IHs css b Hs fx FRM (ext1 E (s_next (c_ss cs1)) av) R' M' model' T HC').
      intros st Hst fx' FRM' E' R2 M2 model2 Hag HC2 Hfs2. apply (HH st ltac:(apply in_or_app; right; exact Hst) fx' FRM' E' R2 M2 model2).
      * eapply env_agree_trans; [| exact Hag]. eapply env_agree_le; [apply ext1_agree | exact Xle].
      * exact HC2.
      * rewrite Hfs2. exact Hfs.
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_munmap U0 cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_munmap_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' model' HC' Hfs. apply (IH cs2 sts Hc fx FRM E R' M' model' T HC').
    intros st Hst fx' FRM' E' R2 M2 model2 Hag HC2 Hfs2. apply (HH st Hst fx' FRM' E' R2 M2 model2 Hag HC2). rewrite Hfs2. exact Hfs.
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_ioctl cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_ioctl_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' HC'. exact (IH cs2 sts Hc fx FRM E R' M' model T HC' HH).
  - (* [comment removed for export] *)
    destruct (negb (is_ecall_at RSEGS cs1) && existsb (Z.eqb (pc cs1)) (STOPS U0))%bool; [|discriminate].
    exact (IH cs1 sts Hc fx FRM E R1 M1 model T HC1 HH).
  - (* [comment removed for export] *)
    destruct sm.
    all: match type of Hc with (match ?rr with _ => _ end = _) => destruct rr as [cs2|] eqn:Hn; [|discriminate] end.
    all: lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hpc; [|discriminate] end.
    all: first [ apply andb_prop in Hpc as [Hgate Hpc]; apply Z.eqb_eq in Hpc | apply Z.eqb_eq in Hpc ].
    all: lazymatch type of Hn with
         | call_memcpy _ _ _ = _ => eapply (node_call_sound FRM SumMemcpy args cs1 cs2 E R1 M1)
         | call_lib _ _ _ _ = _ => eapply (node_call_sound FRM SumLib args cs1 cs2 E R1 M1)
         | call_enframe2 _ _ _ _ = _ => eapply (node_call_sound FRM SumEnframe args cs1 cs2 E R1 M1)
         | call_freepro _ _ _ _ = _ => eapply (node_call_sound FRM SumFreePro args cs1 cs2 E R1 M1)
         | call_mainret _ _ _ = _ => eapply (node_call_sound FRM SumMainRet args cs1 cs2 E R1 M1)
         | call_printf _ _ _ _ = _ => eapply (node_call_sound FRM SumPrintf args cs1 cs2 E R1 M1)
         | call_inflate _ _ _ _ = _ => eapply (node_call_sound FRM SumInflate args cs1 cs2 E R1 M1)
         | call_u2tail _ _ _ = _ => eapply (node_call_sound FRM SumU2Tail args cs1 cs2 E R1 M1)
         end; [exact HC1 | split; [exact Hpc | first [exact Hn | exact (conj Hgate Hn)]] |].
    all: intros fx' FRM' E' R' M' Hag HC'; apply (IH cs2 sts Hc fx' FRM' E' R' M' model T HC');
         intros st Hst fx2 FRM2 E2 R2 M2 model2 Hag2 HC2 Hfs2; apply (HH st Hst fx2 FRM2 E2 R2 M2 model2); [eapply env_agree_trans; [exact Hag | exact Hag2] | exact HC2 | exact Hfs2].
  - (* [comment removed for export] *)
    destruct (node_cas RSEGS U0 c cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_cas_sound c cs1 cs2 E R1 M1 model); [exact HC1 | exact Hn |].
    intros R' M' HC'. exact (IH cs2 sts Hc fx FRM E R' M' model T HC' HH).
  - (* [comment removed for export] *)
    destruct (negb (is_ecall_at RSEGS cs1) && (0 <=? t_join U0) && Z.eqb (pc cs1) (t_join U0))%bool; [|discriminate].
    injection Hc as <-.
    apply (HH cs1 ltac:(left; reflexivity) fx FRM E R1 M1 model); [apply env_agree_refl' | exact HC1 | reflexivity].
Qed.

Theorem check_sound : forall fuel bfuel p cs s,
  check RSEGS IT U0 nx0 bfuel fuel cs p = COk s ->
  forall (fx : FPState), LibIface.frm_zero fx -> forall E R M model, cs_ok E cs R M model ->
  realizes RSEGS (cfg_of (fx:=fx) R (pc cs) M model) (sd E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel p cs s Hc fx FRM E R M model HC; [discriminate|].
  cbn [check] in Hc.
  (* [comment removed for export] *)
  destruct p as [kf ks|k|k|k| |k|sm args k|c k|e mid k1 k2| | |r mid k1 k2| |body k].
  14: { (* [comment removed for export] *)
       destruct (collect RSEGS IT U0 nx0 bfuel cs body) as [[|cs1 rest]|c q cs'] eqn:Hb; try discriminate.
       destruct (merge RSEGS nx0 cs1 rest) as [csm|] eqn:Hm; [|discriminate].
       apply (collect_sound bfuel body cs (cs1 :: rest) Hb fx FRM E R M model _ HC).
       intros st Hst fx' FRM' E' R' M' model' Hag HC' Hfs.
       destruct (merge_sound cs1 rest csm st E' R' M' model' Hm Hst HC') as (E'' & Hag' & HCm & Hpc).
       rewrite <- Hpc, <- Hfs.
       rewrite (sd_agree nx0 E E'' (m_fs model') s);
         [ exact (IH bfuel k csm s Hc fx' FRM' E'' R' M' model' HCm)
         | eapply env_agree_trans; [exact Hag | exact Hag']
         | eapply check_vars; exact Hc ]. }
  13: { discriminate. }
  12: { (* [comment removed for export] *)
       destruct (erange (kn cs) (reg cs r)) as [[lo hi]|] eqn:Hr; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange (reg cs r) lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange (reg cs r) (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       destruct (shape_eqb s1 s2) eqn:Heq; [|discriminate]. injection Hc as <-.
       apply shape_eqb_eq in Heq. subst s2.
       destruct (split_sound cs (reg cs r) mid lo hi E R M model HC Hr) as [HCl HCr].
       destruct (Z.leb_spec (bv_unsigned (edenot E (reg cs r))) mid) as [Hle|Hgt].
       - exact (IH bfuel k1 _ s1 H1 fx FRM E R M model (HCl Hle)).
       - exact (IH bfuel k2 _ s1 H2 fx FRM E R M model (HCr ltac:(lia))). }
  10: { destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
        exact (kn_contra_sound E M (kn cs) (co_know _ _ _ _ _ HC) Hk). }
  9: { destruct (expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
       destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT U0 nx0 bfuel fuel (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       injection Hc as <-. cbn [sd].
       destruct (split_sound cs e mid lo hi E R M model HC Hr) as [HCl HCr].
       destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
       - exact (IH bfuel k1 _ s1 H1 fx FRM E R M model (HCl Hle)).
       - exact (IH bfuel k2 _ s2 H2 fx FRM E R M model (HCr ltac:(lia))). }
  all: destruct (run_block_gc RSEGS IT U0 bfuel (STOPS U0) cs) as [cs1|] eqn:Hrb; [|discriminate].
  all: destruct (run_block_gc_sound IT IT_ok bfuel (STOPS U0) cs cs1 E R M model Hrb HC) as (R1 & M1 & Hms & HC1 & Hmaps).
  all: eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_mmap U0 nx0 cs1) as [[csf css]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel csf kf) as [sf|] eqn:Hf; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel css ks) as [ss|] eqn:Hs; [|discriminate].
    injection Hc as <-.
    eapply rz_conseq; [|apply salt2_sound].
    pose proof (node_mmap_nx0 cs1 csf css Hn) as Xle.
    eapply (node_mmap_sound cs1 csf css E R1 M1 model); [exact HC1 | exact Hec | exact Hn | |].
    + intros R' M' HC'. exact (IH bfuel kf csf sf Hf fx FRM E R' M' model HC').
    + intros a R' M' model' HC' Hfs.
      rewrite (sd_agree nx0 E (ext1 E (s_next (c_ss cs1)) a) (m_fs model) ss).
      * rewrite <- Hfs. exact (IH bfuel ks css ss Hs fx FRM _ R' M' model' HC').
      * eapply env_agree_le; [apply ext1_agree | exact Xle].
      * eapply check_vars. exact Hs.
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_munmap U0 cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_munmap_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' model' HC' Hfs. rewrite <- Hfs. exact (IH bfuel k cs2 s Hc fx FRM E R' M' model' HC').
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_ioctl cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_ioctl_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' HC'. exact (IH bfuel k cs2 s Hc fx FRM E R' M' model HC').
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_stdio_write U0)) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
    destruct (node_stdio_write RSEGS U0 nx0 cs1) as [[[fd bs] cs2]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT U0 nx0 bfuel fuel cs2 k) as [s2|] eqn:H2; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_stdio_write_sound fx cs1 cs2 fd bs E R1 M1 model); [exact HC1 | exact Hpc | exact Hn | apply sd_has_nil |].
    intros E' R' M' Hag HC'. rewrite (sd_agree nx0 E E' (m_fs model) s2);
      [ exact (IH bfuel k cs2 s2 H2 fx FRM _ R' M' model HC') | exact Hag | eapply check_vars; exact H2 ].
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_exit cs1) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    destruct (negb (is_ecall_at RSEGS cs1) && existsb (Z.eqb (pc cs1)) (STOPS U0))%bool; [|discriminate].
    exact (IH bfuel k cs1 s Hc fx FRM E R1 M1 model HC1).
  - (* [comment removed for export] *)
    destruct sm.
    all: match type of Hc with (match ?r with _ => _ end = _) => destruct r as [cs2|] eqn:Hn; [|discriminate] end.
    all: lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hpc; [|discriminate] end.
    (* [comment removed for export] *)
    all: first [ apply andb_prop in Hpc as [Hgate Hpc]; apply Z.eqb_eq in Hpc | apply Z.eqb_eq in Hpc ].
    all: lazymatch type of Hn with
         | call_memcpy _ _ _ = _ => eapply (node_call_sound FRM SumMemcpy args cs1 cs2 E R1 M1)
         | call_lib _ _ _ _ = _ => eapply (node_call_sound FRM SumLib args cs1 cs2 E R1 M1)
         | call_enframe2 _ _ _ _ = _ => eapply (node_call_sound FRM SumEnframe args cs1 cs2 E R1 M1)
         | call_freepro _ _ _ _ = _ => eapply (node_call_sound FRM SumFreePro args cs1 cs2 E R1 M1)
         | call_mainret _ _ _ = _ => eapply (node_call_sound FRM SumMainRet args cs1 cs2 E R1 M1)
         | call_printf _ _ _ _ = _ => eapply (node_call_sound FRM SumPrintf args cs1 cs2 E R1 M1)
         | call_inflate _ _ _ _ = _ => eapply (node_call_sound FRM SumInflate args cs1 cs2 E R1 M1)
         | call_u2tail _ _ _ = _ => eapply (node_call_sound FRM SumU2Tail args cs1 cs2 E R1 M1)
         end; [exact HC1 | split; [exact Hpc | first [exact Hn | exact (conj Hgate Hn)]] |].
    all: intros fx' FRM' E' R' M' Hag HC'; rewrite (sd_agree nx0 E E' (m_fs model) s);
         [ exact (IH bfuel k cs2 s Hc fx' FRM' _ R' M' model HC') | exact Hag | eapply check_vars; exact Hc ].
  - (* [comment removed for export] *)
    destruct (node_cas RSEGS U0 c cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_cas_sound c cs1 cs2 E R1 M1 model); [exact HC1 | exact Hn |].
    intros R' M' HC'. exact (IH bfuel k cs2 s Hc fx FRM E R' M' model HC').
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_exitc U0)) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
    destruct (node_exitcall RSEGS U0 cs1) as [[bs code]|] eqn:Hn; [|discriminate].
    pose proof (node_exitcall_sound fx cs1 bs code E R1 M1 model HC1 Hpc Hn) as HX.
    destruct bs as [|b bs]; injection Hc as <-; cbn [sd]; [|exact HX].
    eapply rz_conseq; [exact HX|]. cbn [Wz map]. apply t_emit_nil_eq. apply t_exit_has_nil.
Qed.

End NX0.
End SPS.

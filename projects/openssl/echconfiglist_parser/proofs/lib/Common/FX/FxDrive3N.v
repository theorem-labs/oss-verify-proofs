(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dres3 : Type :=
| D3One (F : fstate) (L : fledger3) (n : int)
| D3Two (F1 : fstate) (L1 : fledger3) (n1 : int) (F2 : fstate) (L2 : fledger3) (n2 : int).

Definition dres3_in (x : fstate * fledger3 * int) (res : dres3) : Prop :=
  match res with
  | D3One F L n => x = (F, L, n)
  | D3Two F1 L1 n1 F2 L2 n2 => x = (F1, L1, n1) \/ x = (F2, L2, n2)
  end.

Section Drive3NDefs.
Local Open Scope uint63_scope.
Variable Rb Rc Lim : Z.
Variable keep : list int.

(* [comment removed for export] *)
Definition lazy_tag_free (t : int) (L3 : fledger3) : bool :=
  forallb (fun e => negb (fent_tag e =? t)) (fl_lazy L3).
Definition ex_tag_free (t : int) (L3 : fledger3) : bool :=
  forallb (fun e => negb (fent_tag e =? t)) (fl_ex L3).

(* [comment removed for export] *)
Definition grant_ledger3 (nr : bool) (L3 : fledger3) (L' : fledger) (e : fent) : fledger3 :=
  FL3 L' (e :: fl_all L3)
      (fl_ops L3 ++ [(if nr then OpLazy else OpGrant, e)])
      (if nr then e :: fl_lazy L3 else fl_lazy L3)
      (e :: fl_allow L3) (fl_Ab L3 + to_Z (snd e) + 8192)%Z
      (if nr then fl_E L3 else (fl_E L3 + to_Z (snd e))%Z)
      (fl_ex L3) (fl_ord L3) (fl_res L3).

(* [comment removed for export] *)
Definition sys_grant3 (nr : bool) (F : fstate) (L3 : fledger3) (n : int) (len : int) : option dres3 :=
  match sys_grant Rb Rc BIG RTgt F (fl3 L3) n len with
  | Some (DOne F' L' n') =>
      let L3' := grant_ledger3 nr L3 L' (n, 0, pg_up len) in
      if acct_ok Lim L3' then Some (D3One F' L3' n') else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition no_shadow_child (M : itrie region) (t : int) : bool :=
  match iget (t + 1) M with
  | Some rg' => match rg_kind rg' with RK_shadow _ => false | RK_plain => true end
  | None => true
  end.

(* [comment removed for export] *)
Definition unmap_ledger3 (L3 : fledger3) (L' : fledger) (t len : int) : fledger3 :=
  FL3 L' (drop_tag t (fl_all L3)) (fl_ops L3 ++ [(OpCut, (t, 0, len))]) (fl_lazy L3)
      (fl_allow L3) (fl_Ab L3) (fl_E L3) (fl_ex L3) (fl_ord L3) (fl_res L3).

(* [comment removed for export] *)
Definition pages_valid (rg : region) : bool :=
  iall (fun pn p => (pn <? 1125899906842624)
                    && iall (fun ci _ => (ci <? 512) && ((pn << 12) + (ci << 3) + 8 <=? rg_len rg)) (pg_cells p))
       (rg_pages rg).

(* [comment removed for export] *)
Definition sys_unmap3 (F : fstate) (L3 : fledger3) (n : int) (t off len : int) : option dres3 :=
  match sys_unmap keep F (fl3 L3) n t off len, iget t (f_mem F) with
  | Some (DOne F' L' n'), Some rg =>
      let L3' := unmap_ledger3 L3 L' t (rg_len rg) in
      if no_shadow_child (f_mem F) t && lazy_tag_free t L3 && ex_tag_free t L3 && pages_valid rg && acct_ok Lim L3'
      then Some (D3One F' L3' n') else None
  | _, _ => None
  end.

End Drive3NDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pg_dn_le x : pg_dn x <= x.
Proof. unfold pg_dn. Z.div_mod_to_equations. lia. Qed.
Lemma pg_upZ_ge x : x <= pg_upZ x.
Proof. unfold pg_upZ. Z.div_mod_to_equations. lia. Qed.
Lemma pg_dn_mod x : pg_dn x mod 4096 = 0.
Proof. unfold pg_dn. apply Z_mod_mult. Qed.
Lemma pg_upZ_mod x : pg_upZ x mod 4096 = 0.
Proof. unfold pg_upZ. apply Z_mod_mult. Qed.
Lemma pg_dn_al x : x mod 4096 = 0 -> pg_dn x = x.
Proof. intros H. unfold pg_dn. Z.div_mod_to_equations. lia. Qed.
Lemma pg_upZ_al x : x mod 4096 = 0 -> pg_upZ x = x.
Proof. intros H. unfold pg_upZ. Z.div_mod_to_equations. lia. Qed.

Lemma denA_width rho e : Z.max 0 (snd (denA rho e) - fst (denA rho e)) <= to_Z (snd e) + 8192.
Proof.
  destruct e as [[t off] len]. cbn [denA fst snd]. pose proof (i63_range len) as Hl.
  set (x := bv_unsigned (rho t) + to_Z off). unfold pg_dn, pg_upZ. Z.div_mod_to_equations. lia.
Qed.

Lemma denA_ext rho rho' (l : list fent) :
  (forall e, In e l -> rho' (fent_tag e) = rho (fent_tag e)) -> map (denA rho') l = map (denA rho) l.
Proof.
  intros H. apply map_ext_in. intros [[t off] len] He. cbn [denA].
  pose proof (H _ He) as E. cbn [fent_tag fst] in E. rewrite E. reflexivity.
Qed.

Lemma page_allowedb_cons iv A p : page_allowedb A p = true -> page_allowedb (iv :: A) p = true.
Proof. intros H. unfold page_allowedb in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.


(* [comment removed for export] *)
Lemma stable_den rho rho' (n : int) (l : list fent) :
  (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  Forall (fun e => to_Z (fent_tag e) < to_Z n) l ->
  map (den rho') l = map (den rho) l /\ map (denA rho') l = map (denA rho) l.
Proof.
  intros Hrho Hl. split; [apply map_den_ext | apply denA_ext]; intros e He;
    apply Hrho; exact (proj1 (Forall_forall _ _) Hl e He).
Qed.

Lemma pw_disj_map_In (f : fent -> word * word) : forall l e1 e2,
  pw_disj (map f l) -> In e1 l -> In e2 l -> e1 <> e2 -> e_disj (f e1) (f e2).
Proof.
  induction l as [|x l IH]; intros e1 e2 Hd H1 H2 Hne; [contradiction|].
  cbn [map pw_disj] in Hd. destruct Hd as [Hx Hd]. rewrite Forall_forall in Hx.
  destruct H1 as [<- | H1]; destruct H2 as [<- | H2].
  - contradiction.
  - apply Hx. apply in_map. exact H2.
  - apply e_disj_sym. apply Hx. apply in_map. exact H1.
  - exact (IH e1 e2 Hd H1 H2 Hne).
Qed.

Lemma drop_tag_In' t e l : In e l -> fent_tag e <> t -> In e (drop_tag t l).
Proof.
  intros Hin Hne. unfold drop_tag. apply filter_In. split; [exact Hin|].
  apply negb_true_iff. apply eqb_false_spec. exact Hne.
Qed.

Lemma lazy_tag_free_sound t L3 e : lazy_tag_free t L3 = true -> In e (fl_lazy L3) -> fent_tag e <> t.
Proof.
  unfold lazy_tag_free. intros H He. pose proof (proj1 (forallb_forall _ _) H e He) as Hb.
  apply negb_true_iff in Hb. apply eqb_false_spec in Hb. exact Hb.
Qed.

Lemma ex_tag_free_sound t L3 e : ex_tag_free t L3 = true -> In e (fl_ex L3) -> fent_tag e <> t.
Proof.
  unfold ex_tag_free. intros H He. pose proof (proj1 (forallb_forall _ _) H e He) as Hb.
  apply negb_true_iff in Hb. apply eqb_false_spec in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract (p : word) : forall l lo hi,
  lo <= hi -> hi < 2 ^ 64 ->
  page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hle Hhi H; [exact H|].
  cbn [maps_subtract] in H. unfold page_in_ranges in *. rewrite existsb_app in H. cbn [existsb].
  apply orb_true_iff in H as [H|H]; [|rewrite (IH lo hi Hle Hhi H); apply orb_true_r].
  apply orb_true_iff. left. cbn [fst snd].
  pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs.
  unfold iv_subtract in H. cbv zeta in H. rewrite existsb_app in H.
  set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
  apply orb_true_iff in H as [H|H].
  - destruct (A <? lo) eqn:El; [|discriminate H]. apply Z.ltb_lt in El. cbn [existsb fst snd] in H.
    rewrite orb_false_r in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2.
    rewrite u64_lit in H2 by lia. fold A in H1, H2.
    apply andb_true_iff. split; apply Z.leb_le; lia.
  - destruct (hi <? A + Z_) eqn:Er; [|discriminate H]. apply Z.ltb_lt in Er. cbn [existsb fst snd] in H.
    rewrite orb_false_r in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2.
    rewrite !u64_lit in H1, H2 by lia. rewrite u64_lit in H2 by lia.
    apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_subtract_keep (p : word) : forall l lo hi,
  (bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p l = true -> page_in_ranges p (maps_subtract l lo hi) = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hout H; [exact H|].
  cbn [maps_subtract]. unfold page_in_ranges in *. rewrite existsb_app. cbn [existsb] in H.
  apply orb_true_iff in H as [H|H]; [|rewrite (IH lo hi Hout H); apply orb_true_r].
  apply orb_true_iff. left. cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1, H2. unfold page_size in H2.
  pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs. pose proof (u64_range p) as Hp.
  unfold iv_subtract. cbv zeta. rewrite existsb_app.
  set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
  apply orb_true_iff. destruct Hout as [Hout|Hout].
  - left. rewrite (proj2 (Z.ltb_lt A lo)) by lia. cbn [existsb fst snd]. rewrite orb_false_r.
    rewrite u64_lit by lia. fold A. unfold page_size.
    apply andb_true_iff. split; apply Z.leb_le; lia.
  - right. rewrite (proj2 (Z.ltb_lt hi (A + Z_))) by lia. cbn [existsb fst snd]. rewrite orb_false_r.
    rewrite !u64_lit by lia. unfold page_size.
    apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_app (p : word) l1 l2 :
  page_in_ranges p (l1 ++ l2) = page_in_ranges p l1 || page_in_ranges p l2.
Proof. unfold page_in_ranges. apply existsb_app. Qed.

Lemma in_shadow_span x : in_shadow x -> in_span x.
Proof. unfold in_shadow, in_span, lsh_lo, lsh_hi, hsh_lo, hsh_hi, span_lo, span_hi. lia. Qed.

(* [comment removed for export] *)
Lemma exempted_ext rho rho' (l : list fent) x :
  (forall e, In e l -> den rho' e = den rho e) -> exempted rho l x -> exempted rho' l x.
Proof.
  intros H (e & z & He & Hz & Ex). exists e, z. rewrite (H e He). split; [exact He|]. split; [exact Hz | exact Ex].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3N.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation NE := (node_ext cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).
Local Abbreviation PX := (pext IM).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grant_succ_inv n rho F L ms m0 len a :
  (0 <? len)%uint63 = true -> (len <=? 4611686018427387904)%uint63 = true ->
  (pg_up len <=? 4611686018427387904)%uint63 = true -> tag_ok F n = true ->
  DI n rho F L ms m0 -> at_ecall F ->
  mmap_grant_na_b (m_vmmaps m0) a (page_round_up_Z (to_Z len)) = true ->
  let nZi := pg_up len in
  let nZ := page_round_up_Z (to_Z len) in
  let L' := FL ((n, 0%uint63, nZi) :: fl_maps L) (fl_na L) (fl_brk L) (fl_c L + 1) (fl_S L + to_Z nZi) in
  let ms' := sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)]) in
  DI (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n nZi) L' ms' (mmap_grant_model a nZ m0)
  /\ NE n rho F L ms m0 (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n nZi) L' ms' (mmap_grant_model a nZ m0)
  /\ sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + nZ)
  /\ to_Z nZi = nZ /\ 0 < nZ /\ nZ mod 4096 = 0 /\ to_Z n < 2 ^ 60 /\ 0 < to_Z n
  /\ regions_lt n (f_mem F).
Proof.
  intros Hpos Hle Hup Htag (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Ha.
  cbv zeta.
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec R0 len Hle) as HnZ.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn61]. apply ltb_spec in Hn0, Hn61. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn61.
  apply regions_lt_b_ok in Hlt.
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof Ha as Hg. apply mmap_grant_na_b_iff in Hg as (Hal & Hapos & Hatop & Hfree).
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [_ Htop].
  unfold page_size in Hal. unfold TASK_SIZE in Htop.
  assert (Hsep : sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + to_Z nZi)).
  { rewrite HnZ. apply (sep_from_free R0 mem0 rho (f_mem F) (m_vmmaps m0) a nZ Hcov); [lia | exact Hatop | exact Hfree]. }
  pose proof (fx_grant_sound segs IM n rho F ms a nZi HRn Hat Hn0 Hn61 Hlt
                ltac:(lia) ltac:(rewrite HnZ; exact HnZmod) Hal Hapos ltac:(lia) ltac:(lia) Hsep) as HRn'.
  rewrite HnZ in HRn'.
  set (rho' := rho_upd rho n a) in *.
  set (M' := iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)).
  assert (HM' : f_mem (fx_grant F n nZi) = M') by reflexivity.
  assert (Hmaps : vm_maps (m_vmmaps (mmap_grant_model a nZ m0)) = (a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m0))
    by reflexivity.
  assert (Hother : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t /\ iget t M' = Some rg).
  { intros t rg Hgt. split; [exact (regions_lt_rho R0 rho n a _ _ _ Hlt Hgt)|].
    unfold M'. rewrite iget_iset_other; [exact Hgt|]. intros ->. pose proof (Hlt _ _ Hgt). lia. }
  split.
  2:{ split; [|split; [rewrite <- HnZ; exact Hsep|]].
      2:{ repeat split; assumption. }
      constructor.
      - rewrite (to_Z_succ61 R0 n Hn61). lia.
      - intros t Ht. unfold rho'. apply rho_upd_other. apply (lt_neq R0). exact Ht.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_zeros_one. rewrite u64_lit by lia.
          replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
            by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
          reflexivity.
        + rewrite HM'. intros t rg Hgt Hxin. unfold M' in Hgt. rewrite iget_iset in Hgt.
          destruct (t =? n)%uint63 eqn:E.
          * apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. unfold in_ival in Hxin.
            cbn [rg_lo rg_len] in Hxin. unfold rho' in Hxin. rewrite rho_upd_same, to_Z_0, HnZ in Hxin. lia.
          * apply (Hno t rg Hgt). exact (in_ival_rho rho rho' t rg _ (proj1 (Hother t rg Hgt)) Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. destruct Hmir as (Hm1 & Hm2 & _). split.
        + cbn [fl_maps map]. rewrite Hmaps, E1. f_equal.
          * cbn [den]. rewrite to_Z_0, adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
          * symmetry. exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm1).
        + cbn [fl_na]. change (vm_noaccess (m_vmmaps (mmap_grant_model a nZ m0))) with (vm_noaccess (m_vmmaps m0)).
          rewrite E2. symmetry.
          exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm2). }
  split; [exact HRn'|].
  split. { unfold rho'. rewrite rho_upd_other; [exact H0|]. intros E. rewrite <- E, to_Z_0 in Hn0. lia. }
  split; [exact Hh|]. split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split.
  { cbn [fl_c fl_S]. rewrite HnZ.
    change (m_vmmaps (mmap_grant_model a nZ m0)) with (ledger_grant a (Z_to_bv 64 nZ) (m_vmmaps m0)).
    apply ledger_inv_grant; try assumption.
    rewrite <- (li_reserved _ _ _ _ _ Hli). exact Hfree. }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t rg Hgt. unfold M' in Hgt. rewrite iget_iset in Hgt.
    destruct (t =? n)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. cbn [rg_lo rg_len].
      rewrite to_Z_0. split; [lia|]. intros x Hx. unfold in_ival in Hx. cbn [rg_lo rg_len] in Hx.
      unfold rho' in Hx. rewrite rho_upd_same, to_Z_0, HnZ in Hx.
      left. exists (a, Z_to_bv 64 nZ). split.
      + apply in_app_iff. right. rewrite Hmaps. left. reflexivity.
      + unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite u64_lit by lia. lia.
    - destruct (Hcov t rg Hgt) as [Hne Hb]. split; [exact Hne|]. intros x Hx.
      apply (covered_mono (m_vmmaps m0)); [reflexivity | reflexivity | | ].
      + intros p Hp. rewrite Hmaps. right. exact Hp.
      + apply Hb. exact (in_ival_rho rho rho' t rg x (proj1 (Hother t rg Hgt)) Hx). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). split; [|split].
    - cbn [fl_maps]. constructor.
      + exists (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)). unfold M'. rewrite iget_iset_same. cbn [rg_lo rg_len].
        rewrite to_Z_0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite Hmaps. left. rewrite adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
      + eapply Forall_impl; [|exact Hm1]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
        apply (ent_ok_ext rho rho' (f_mem F) M' (vm_maps (m_vmmaps m0))); try assumption.
        * rewrite Eg, Hrg. reflexivity.
        * intros p Hp. rewrite Hmaps. right. exact Hp.
    - cbn [fl_na]. eapply Forall_impl; [|exact Hm2]. intros e He.
      destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
      apply (ent_ok_ext rho rho' (f_mem F) M' (vm_noaccess (m_vmmaps m0))); try assumption.
      + rewrite Eg, Hrg. reflexivity.
      + intros p Hp. exact Hp.
    - cbn [fl_brk]. destruct (Hother _ _ Hgb) as [Er Eg]. exists rgb. split; [exact Eg|].
      rewrite (adr_rho rho rho' _ _ Er). exact Hbrk. }
  split; [exact I|].
  split.
  { apply (XI_rho rho rho'); [|apply (XI_vm rho m0); [repeat split; reflexivity | exact HXI]].
    intros tx Htx. unfold rho'. apply rho_upd_other. apply (lt_neq R0). exact (Hxt tx Htx). }
  split; [intros tx Htx; rewrite (to_Z_succ61 R0 n Hn61); pose proof (Hxt tx Htx); lia|].
  (* [comment removed for export] *)
  rewrite HM'. intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem].
  destruct Hpr as (Hne0 & rgt & Hgt & Hpr2). destruct (Hother _ _ Hgt) as [Er Eg].
  split; [split; [exact Hne0 | exists rgt; split; [exact Eg | exact Hpr2]]|].
  intros rg x Hgx Hx. rewrite Eg in Hgx. injection Hgx as <-.
  apply (in_ival_rho rho rho' t rgt _ Er) in Hx.
  rewrite sysret_mem, apply_zeros_one.
  destruct (Hsep t rgt Hgt) as [Hs|Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
    unfold in_ival in Hx; rewrite ?HnZ in Hs; rewrite u64_lit by lia.
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    exact (Hmem rgt x Hgt Hx).
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    exact (Hmem rgt x Hgt Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma xpart_node n rho F L ms m n' rho' F' L' ms' m' :
  xpart mem0 fr0 fc0 rom0 hi brk0 rho F ms m ->
  NE n rho F L ms (erase m) n' rho' F' L' ms' (erase m') ->
  vm_brk (m_vmmaps m') = vm_brk (m_vmmaps m) ->
  xpart mem0 fr0 fc0 rom0 hi brk0 rho' F' ms' m'.
Proof.
  intros (X1 & X2 & X3 & X4 & X5) [Hn Hrho Efr Efc Erom Hvm Hsp Hhigh Hsb Hmb _] Ebrk.
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [|congruence].
  intros x Hx. destruct (X4 x Hx) as (Ht & Hno & Hm).
  change (alloc_top (m_vmmaps (erase m))) with (alloc_top (m_vmmaps m)) in Hhigh.
  destruct (Hhigh x Ht Hno) as [Em Hno']. split; [|split; [exact Hno' | congruence]].
  change (vm_init_sp (m_vmmaps (erase m'))) with (vm_init_sp (m_vmmaps m')) in Hsp.
  change (vm_init_sp (m_vmmaps (erase m))) with (vm_init_sp (m_vmmaps m)) in Hsp.
  unfold alloc_top in *. rewrite Hsp. exact Ht.
Qed.

Lemma dext_node n rho F L ms m n' rho' F' L' ms' m' :
  NE n rho F L ms (erase m) n' rho' F' L' ms' (erase m') ->
  vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m) ->
  vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m) ->
  dext n rho m n' rho' m'.
Proof.
  intros [Hn Hrho _ _ _ Hvm Hsp _ _ _ _] Hsb Hmb.
  split; [exact Hn|]. split; [exact Hrho|]. split.
  - destruct Hvm as (A1 & A2 & A3 & A4 & A5 & A6). repeat split; assumption.
  - repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grant_model3 (nr : bool) (a : word) (nZ : Z) (m : Model) : Model :=
  if nr then mmap_grant_nr_model a nZ m else mmap_grant_model a nZ m.

Lemma erase_grant_model3 nr a nZ m : erase (grant_model3 nr a nZ m) = mmap_grant_model a nZ (erase m).
Proof. destruct nr; destruct m as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma grant_model3_facts nr a nZ m :
  vm_maps (m_vmmaps (grant_model3 nr a nZ m)) = (a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m)
  /\ vm_noaccess (m_vmmaps (grant_model3 nr a nZ m)) = vm_noaccess (m_vmmaps m)
  /\ m_vm_materialized (grant_model3 nr a nZ m) = m_vm_materialized m
  /\ vm_limit (m_vmmaps (grant_model3 nr a nZ m)) = vm_limit (m_vmmaps m)
  /\ m_vm_lazy (grant_model3 nr a nZ m)
     = (if nr then lazy_interior a (Z_to_bv 64 nZ) else []) ++ m_vm_lazy m
  /\ vm_brk (m_vmmaps (grant_model3 nr a nZ m)) = vm_brk (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps (grant_model3 nr a nZ m)) = vm_start_brk (m_vmmaps m)
  /\ vm_mmap_base (m_vmmaps (grant_model3 nr a nZ m)) = vm_mmap_base (m_vmmaps m).
Proof. destruct nr; destruct m as [fd [maps lazy mat] io fs proc lim tm]; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_mono (p : word) l1 l2 :
  page_in_ranges p l2 = true -> page_in_ranges p (l1 ++ l2) = true.
Proof. intros H. rewrite page_in_ranges_app, H. apply orb_true_r. Qed.

Lemma grant3_succ n rho F L3 ms m nr len res a :
  sys_grant3 Rb Rc Lim nr F L3 n len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  mmap_grant_na_b (m_vmmaps m) a (page_round_up_Z (to_Z len)) = true ->
  let nZ := page_round_up_Z (to_Z len) in
  let ms' := sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)]) in
  let m' := grant_model3 nr a nZ m in
  exists L3', res = D3One (fx_grant F n (pg_up len)) L3' (n + 1)%uint63
    /\ D3 (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n (pg_up len)) L3' ms' m'
    /\ PX n rho F L3 ms m (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n (pg_up len)) L3' ms' m'
    /\ L3' = grant_ledger3 nr L3 (FL ((n, 0%uint63, pg_up len) :: fl_maps (fl3 L3)) (fl_na (fl3 L3))
                                     (fl_brk (fl3 L3)) (fl_c (fl3 L3) + 1) (fl_S (fl3 L3) + to_Z (pg_up len)))
                            (n, 0%uint63, pg_up len)
    /\ (bv_unsigned a + nZ <= span_lo \/ span_hi <= bv_unsigned a).
Proof.
  intros Hsys (HDI & HL & HS & HX) Hat Ha. cbv zeta.
  unfold sys_grant3 in Hsys.
  destruct (sys_grant Rb Rc BIG RTgt F (fl3 L3) n len) as [[F' L' n'|]|] eqn:Hg; try discriminate.
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hacct; [|discriminate] end.
  injection Hsys as <-.
  unfold sys_grant in Hg. cbv zeta in Hg.
  match type of Hg with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hg as <- <- <-.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  destruct (grant_succ_inv n rho F (fl3 L3) ms (erase m) len a Hpos Hle Hup Htag HDI Hat Ha)
    as (HDI' & Hne & Hsep & HnZ & HnZpos & HnZmod & Hn60 & Hn0 & Hlt).
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  set (rho' := rho_upd rho n a) in *. set (e := (n, 0%uint63, nZi)) in *.
  set (L' := FL (e :: fl_maps (fl3 L3)) (fl_na (fl3 L3)) (fl_brk (fl3 L3)) (fl_c (fl3 L3) + 1)
                (fl_S (fl3 L3) + to_Z nZi)) in *.
  set (m' := grant_model3 nr a nZ m).
  set (ms' := sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)])) in *.
  rewrite <- (erase_grant_model3 nr a nZ m) in HDI', Hne. fold m' in HDI', Hne.
  exists (grant_ledger3 nr L3 L' e). split; [reflexivity|].
  pose proof Ha as Hadm. apply mmap_grant_na_b_iff in Hadm as (Hal & Hapos & Hatop & Hfree).
  unfold page_size in Hal.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hattop. unfold two_pow_64 in Hattop.
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; pose proof (u64 a); lia).
  assert (Hrho : forall t, to_Z t < to_Z n -> rho' t = rho t) by (exact (ne_rho _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hne)).
  assert (Hrn : rho' n = a) by (unfold rho'; apply rho_upd_same).
  destruct (grant_model3_facts nr a nZ m) as (Hmaps' & Hna' & Hmat' & Hlim' & Hlazy' & Hbrk' & Hsbrk' & Hmb').
  fold m' in Hmaps', Hna', Hmat', Hlim', Hlazy', Hbrk', Hsbrk', Hmb'.
  cut (D3 (n + 1)%uint63 rho' (fx_grant F n nZi) (grant_ledger3 nr L3 L' e) ms' m'
       /\ (bv_unsigned a + nZ <= span_lo \/ span_hi <= bv_unsigned a)
       /\ mfr IM rho F L3 ms (n + 1)%uint63 rho' (fx_grant F n nZi) (grant_ledger3 nr L3 L' e) ms').
  { intros (HD' & Hm' & Hfr'). split; [exact HD'|].
    split; [split; [exact (dext_node _ _ _ _ _ _ _ _ _ _ _ _ Hne Hsbrk' Hmb') | exact Hfr']|].
    split; [reflexivity | exact Hm']. }
  assert (Hden_e : den rho' e = (a, Z_to_bv 64 nZ)).
  { unfold e. cbn [den]. rewrite to_Z_0, adr_0, Hrn, HnZ. reflexivity. }
  assert (Hregs : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t /\ iget t (f_mem (fx_grant F n nZi)) = Some rg).
  { intros t rg Hgt. pose proof (Hlt t rg Hgt) as Htn. split; [exact (Hrho t Htn)|].
    change (f_mem (fx_grant F n nZi)) with (iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)).
    rewrite iget_iset_other; [exact Hgt|]. intros ->. lia. }
  assert (Hnew : forall t rg, iget t (f_mem (fx_grant F n nZi)) = Some rg ->
            (t = n /\ rg = RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi))
            \/ (t <> n /\ iget t (f_mem F) = Some rg)).
  { intros t rg Hgt.
    change (f_mem (fx_grant F n nZi)) with (iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)) in Hgt.
    rewrite iget_iset in Hgt. destruct (t =? n)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. injection Hgt as <-. left. split; [exact E | reflexivity].
    - right. split; [|exact Hgt]. intros ->. rewrite Uint63.eqb_refl in E. discriminate. }
  (* [comment removed for export] *)
  assert (Hdisj : forall p, In p (vm_maps (m_vmmaps m)) -> e_disj (a, Z_to_bv 64 nZ) p).
  { intros p Hp. apply (region_free_In_disj _ _ _ p Hfree). apply in_app_iff. right. exact Hp. }
  destruct HL as [Hpi Hreg Hpw Hml Hsub HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz HopsR Hord Hopsf Hres].
  assert (Hmiss : bv_unsigned a + nZ <= span_lo \/ span_hi <= bv_unsigned a).
  { destruct HS as [_ Hcov _ _].
    destruct (Z_le_gt_dec (bv_unsigned a + nZ) span_lo) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec span_hi (bv_unsigned a)) as [Hh'|Hh']; [right; lia|]. exfalso.
    set (x := Z.max (bv_unsigned a) span_lo).
    assert (Hxs : in_span x) by (unfold in_span, x, span_lo, span_hi in *; lia).
    destruct (Hcov x Hxs) as (e0 & He0 & _ & Hpx).
    assert (Hp : In (den rho e0) (vm_maps (m_vmmaps m))) by (rewrite Hex; apply in_map; exact He0).
    pose proof (Hdisj _ Hp) as Hd.
    unfold e_disj, e_hi, e_lo, e_sz in Hd, Hpx. cbn [fst snd] in Hd. rewrite HnZw in Hd. unfold x in Hpx. lia. }
  apply Forall_app in Htags as [Ht1 Htags]. apply Forall_app in Htags as [Ht2 Ht3].
  destruct (stable_den rho rho' n _ Hrho Ht1) as [Eall _].
  destruct (stable_den rho rho' n _ Hrho Ht3) as [_ EA].
  pose proof (lazy_cov_tags _ _ n Hsub Ht1) as Ht4.
  assert (Hden_lt : forall e0 : fent, to_Z (fent_tag e0) < to_Z n -> den rho' e0 = den rho e0).
  { intros [[t0 o0] l0] Ht0. cbn [fent_tag fst] in Ht0. cbn [den]. unfold adr. rewrite (Hrho t0 Ht0). reflexivity. }
  destruct (ops_apply_ext rho rho' (fl_ops L3)) as [Eops_na Eops_lz].
  { intros o Ho. apply Hden_lt. apply (proj1 (Forall_forall _ _) Ht2). apply in_map. exact Ho. }
  assert (Hn1 : to_Z (n + 1)%uint63 = to_Z n + 1) by (exact (to_Z_succ61 R0 n Hn60)).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HDI')))) ) as Hli'.
  assert (HR0 : R segs IM rho F ms).
  { pose proof HDI as (HRn0 & H00 & _). exact (Rn_R _ _ _ _ _ _ HRn0 H00). }
  assert (HmemR' : mem_ok segs IM rho' (f_mem (fx_grant F n nZi)) (ms_mem ms')).
  { pose proof HDI' as (HRn1 & H01 & _). exact (R_mem _ _ _ _ _ (Rn_R _ _ _ _ _ _ HRn1 H01)). }
  (* [comment removed for export] *)
  assert (Hli_new : lazy_interior a (Z_to_bv 64 nZ) = [(a, Z_to_bv 64 nZ)]).
  { apply lazy_interior_aligned_lz; unfold page_size; rewrite ?HnZw; try assumption; lia. }
  assert (Hlazy2 : m_vm_lazy m' = (if nr then [(a, Z_to_bv 64 nZ)] else []) ++ m_vm_lazy m).
  { rewrite Hlazy'. destruct nr; [rewrite Hli_new|]; reflexivity. }
  assert (Hlzmono : forall p : word, page_in_ranges p (m_vm_lazy m) = true -> page_in_ranges p (m_vm_lazy m') = true).
  { intros p Hp. rewrite Hlazy2. apply page_in_ranges_mono. exact Hp. }
  assert (HdenA : denA rho' e = (bv_unsigned a, bv_unsigned a + nZ)).
  { unfold e. cbn [denA]. rewrite Hrn, to_Z_0, HnZ, Z.add_0_r.
    rewrite pg_dn_al by exact Hal. rewrite pg_upZ_al; [reflexivity|].
    rewrite Z.add_mod, Hal, HnZmod by lia. reflexivity. }
  apply Z.leb_le in Hacct. unfold acct_ok in Hacct.
  (* [comment removed for export] *)
  assert (HE' : eager_used m' <= fl_E (grant_ledger3 nr L3 L' e)).
  { rewrite (Cnt.eager_used_eu m'), Hmaps', Hna', Hlazy2.
    assert (Hwf' : Cnt.ivs_wf ((a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m))).
    { apply Cnt.ivs_wf_Forall. rewrite <- Hmaps'.
      pose proof (li_top _ _ _ _ _ Hli') as Htop'.
      change (vm_maps (m_vmmaps (erase m'))) with (vm_maps (m_vmmaps m')) in Htop'.
      change (alloc_top (m_vmmaps (erase m'))) with (alloc_top (m_vmmaps m')) in Htop'.
      pose proof (alloc_top_lt (m_vmmaps m')) as Hat'. unfold two_pow_64 in Hat'.
      eapply Forall_impl; [|exact Htop']. intros q [_ Hq]. lia. }
    rewrite (Cnt.eager_used_eu m) in HE.
    destruct nr; cbn [grant_ledger3 fl_E app].
    - pose proof (Cnt.eu_grant_nr_le (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) _ Hwf'). lia.
    - pose proof (Cnt.eu_grant_le (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) [] _ Hwf') as H1.
      cbn [app] in H1. unfold Cnt.S in H1. cbn [snd] in H1. rewrite HnZw in H1.
      unfold e. cbn [snd]. rewrite HnZ. lia. }
  assert (HAb' : A_bytes ((denA rho' e :: map (denA rho') (fl_allow L3)) ++ A0) <= fl_Ab L3 + to_Z (snd e) + 8192).
  { cbn [A_bytes fold_right app]. fold (A_bytes (map (denA rho') (fl_allow L3) ++ A0)). rewrite EA, HdenA. cbn [fst snd].
    unfold e. cbn [snd]. rewrite HnZ. unfold FxDrive3.allowed in HAb. clear - HAb HnZpos. lia. }
  assert (Hrange_e : e_lo (den rho' e) = bv_unsigned a /\ e_hi (den rho' e) = bv_unsigned a + nZ).
  { rewrite Hden_e. unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite HnZw. split; reflexivity. }
  (* [comment removed for export] *)
  assert (Hmfr : mfr IM rho F L3 ms (n + 1)%uint63 rho' (fx_grant F n nZi) (grant_ledger3 nr L3 L' e) ms').
  { exists [(if nr then OpLazy else OpGrant, e)]. split; [reflexivity|].
    split; [constructor; [cbn [snd]; unfold e; cbn [fent_tag fst]; lia | constructor]|].
    split; [|split].
    - intros x Hnt _. unfold ms'. rewrite sysret_mem, apply_zeros_one, HnZw.
      replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false; [reflexivity|].
      symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hnt.
      exists (if nr then OpLazy else OpGrant, e). split; [left; reflexivity|]. cbn [snd].
      rewrite (proj1 Hrange_e), (proj2 Hrange_e). lia.
    - intros x (t & rg & pn & p & j & Hg & Hpn & Hp & Hw & Hj & Hjl & ->).
      destruct (Hnew t rg Hg) as [[-> ->] | [Hne' Hgt0]].
      + right. exists (if nr then OpLazy else OpGrant, e). split; [left; reflexivity|]. cbn [snd].
        rewrite (proj1 Hrange_e), (proj2 Hrange_e).
        cbn [rg_len] in Hjl. rewrite HnZ in Hjl.
        pose proof (i63_range pn) as Hpn0.
        rewrite adr_unsigned by (rewrite ?Hrn; lia). rewrite Hrn. lia.
      + left. exists t, rg, pn, p, j. repeat (split; [assumption|]).
        unfold adr. rewrite (proj1 (Hregs t rg Hgt0)). reflexivity.
    - intros x (t & rg & pn & p & ci & Hg & Hp & Hci & j & Hj & ->). left.
      destruct (Hregs t rg Hg) as [Er Eg]. exists t, rg, pn, p, ci. split; [exact Eg|]. split; [exact Hp|]. split; [exact Hci|].
      exists j. split; [exact Hj|]. unfold adr. rewrite Er. reflexivity. }
  split; [|split; [exact Hmiss | exact Hmfr]].
  split; [replace (fl3 (grant_ledger3 nr L3 L' e)) with L' by reflexivity; exact HDI'|].
  split.
  { (* [comment removed for export] *)
    constructor; unfold FxDrive3.allowed; cbn [grant_ledger3 fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex map].
    - (* [comment removed for export] *)
      destruct Hpi as [P1 P2 P3 P4]. constructor; rewrite ?Hmat'; try assumption.
      + eapply Forall_impl; [|exact P3]. intros p Hp. rewrite EA. apply page_allowedb_cons. exact Hp.
      + rewrite Hlim'. cbn [grant_ledger3 fl_E fl_Ab] in HE', Hacct. clear - HE' HAb' Hacct Hlim. unfold fent in *. lia.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      apply (LZ_build segs IM rho rho' (m_vm_lazy m) (m_vm_lazy m') (map (denA rho) (fl_allow L3) ++ A0)
               ((denA rho' e :: map (denA rho') (fl_allow L3)) ++ A0) (f_mem F) (f_mem (fx_grant F n nZi)) (ms_mem ms')
               HmemR' Hreg).
      + intros pb Hpb. rewrite EA. apply page_allowedb_cons. exact Hpb.
      + intros t rg Hgt. destruct (Hnew t rg Hgt) as [[-> ->] | [Hne' Hgt0]].
        * left. right. exists (denA rho' e). split; [left; reflexivity|]. rewrite HdenA. cbn [fst snd rg_lo rg_len].
          rewrite Hrn, to_Z_0, HnZ. split; [exact Hal|]. split; [rewrite Z.add_mod, Hal, HnZmod by lia; reflexivity|]. lia.
        * right. destruct (Hregs t rg Hgt0) as [Er _]. split; [exact Hgt0|]. split; [exact Er|].
          intros z Hz Hpg. rewrite Hlazy2 in Hpg. rewrite page_in_ranges_app in Hpg.
          apply orb_true_iff in Hpg as [Hpg|Hpg]; [|exact Hpg]. exfalso.
          destruct nr; [|discriminate Hpg]. unfold page_in_ranges in Hpg. cbn [existsb fst snd] in Hpg.
          rewrite orb_false_r in Hpg.
          apply andb_true_iff in Hpg as [B1 B2]. apply Z.leb_le in B1, B2. rewrite HnZw in B2. unfold page_size in B2.
          pose proof (region_ok_nowrap_lz rho t rg (R_region_ok _ _ _ _ _ _ _ HR0 Hgt0)) as Hnw.
          pose proof (i63_range (rg_lo rg)) as Hlo0. pose proof (u64 (rho t)) as Hrt0.
          assert (Epb : bv_unsigned (page_base_of z) = z / 4096 * 4096).
          { unfold page_base_of, page_size. apply u64_lit. clear - Hz Hnw Hlo0 Hrt0. Z.div_mod_to_equations. lia. }
          rewrite Epb in B1, B2.
          destruct (Hsep t rg Hgt0) as [Hs|Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
            clear - Hs Hz B1 B2; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      assert (Hold : forall e0 (p : word), In e0 (fl_lazy L3) -> bv_unsigned p mod 4096 = 0 ->
                e_lo (den rho' e0) <= bv_unsigned p -> bv_unsigned p + 4096 <= e_hi (den rho' e0) ->
                page_in_ranges p (m_vm_lazy m') = true).
      { intros e0 p He0 Hp H1 H2. apply Hlzmono.
        rewrite (Hden_lt e0 (proj1 (Forall_forall _ _) Ht4 e0 He0)) in H1, H2. exact (Hpw e0 p He0 Hp H1 H2). }
      destruct nr; [|exact Hold].
      intros e0 p [<- | He0] Hp H1 H2; [|exact (Hold e0 p He0 Hp H1 H2)].
      rewrite Hlazy2. unfold page_in_ranges. cbn [app existsb fst snd]. rewrite Hden_e in H1, H2.
      unfold e_hi, e_lo, e_sz in H1, H2. cbn [fst snd] in H1, H2. unfold page_size.
      apply orb_true_iff. left. apply andb_true_iff. split; apply Z.leb_le; lia.
    - (* [comment removed for export] *)
      unfold mat_lazy. rewrite Hmat'. eapply Forall_impl; [|exact Hml]. intros p Hp. exact (Hlzmono p Hp).
    - (* [comment removed for export] *)
      assert (Hc0 : lazy_cov (e :: fl_all L3) (fl_lazy L3))
        by (apply (lazy_cov_mono (fl_all L3)); [intros e0 He0; right; exact He0 | exact Hsub]).
      destruct nr; [|exact Hc0].
      constructor; [|exact Hc0].
      split; [unfold e; cbn [snd]; rewrite HnZ; exact HnZpos | exists e; split; [left; reflexivity | apply ent_within_refl]].
    - exact HAb'.
    - rewrite Hlim'; exact Hlim.
    - rewrite Hmaps', Hex; cbn [map]; rewrite Hden_e, Eall; reflexivity.
    - rewrite Hna', Hexna, na_apply_snoc. unfold na_step. destruct nr; cbn [fst]; symmetry; apply Eops_na.
    - rewrite Hlazy2, Hexlz, lz_apply_snoc. unfold lz_step. destruct nr; cbn [fst snd app].
      + rewrite Hden_e, Eops_lz. reflexivity.
      + symmetry. apply Eops_lz.
    - constructor; [left; reflexivity | eapply Forall_impl; [|exact H9a]; intros e0 He0; right; exact He0].
    - constructor; [left; left; reflexivity|]. apply Forall_forall. intros e0 He0in.
      destruct (proj1 (Forall_forall _ _) H9b e0 He0in) as [He0|[He0|He0]];
        [left; right; exact He0 | right; left; exact He0 |].
      right; right.
      change (f_mem (fx_grant F n nZi)) with (iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)).
      rewrite iget_iset_other; [exact He0|]. intros E.
      pose proof (proj1 (Forall_forall _ _) Ht1 e0 He0in) as Hlt0. rewrite E in Hlt0. lia.
    - rewrite !Forall_app. rewrite Hn1. split; [|split].
      + constructor; [unfold e; cbn [fent_tag fst]; lia|]. eapply Forall_impl; [|exact Ht1]. cbv beta. intros; lia.
      + rewrite map_app, Forall_app; split.
        * eapply Forall_impl; [|exact Ht2]. cbv beta. intros; lia.
        * constructor; [unfold e; cbn [snd fent_tag fst]; lia | constructor].
      + constructor; [unfold e; cbn [fent_tag fst]; lia|]. eapply Forall_impl; [|exact Ht3]. cbv beta. intros; lia.
    - exact HE'.
    - exact Hacct.
    - rewrite Hna'. exact Hwfna.
    - rewrite Hlazy2. apply Forall_app. split; [|exact Hwflz].
      destruct nr; [|constructor]. constructor; [|constructor].
      unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite HnZw. lia.
    - intros o x p Ho Hp Hx. apply in_app_iff in Ho as [Ho | [<- | []]].
      + rewrite (Hden_lt (snd o)) in Hx by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
        exact (HopsR o x p Ho Hp Hx).
      + cbn [snd] in Hx. rewrite (proj1 Hrange_e), (proj2 Hrange_e) in Hx.
        assert (HpR : In p (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))).
        { apply in_app_iff. left. pose proof (li_reserved _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HDI)))))) as ER.
          change (vm_reserved (m_vmmaps (erase m))) with (vm_reserved (m_vmmaps m)) in ER. rewrite ER. exact Hp. }
        pose proof (region_free_In_disj _ _ _ p Hfree HpR) as Hd.
        unfold e_disj, e_hi, e_lo, e_sz in Hd. cbn [fst snd] in Hd. rewrite HnZw in Hd.
        unfold e_hi, e_lo, e_sz. lia.
    - (* [comment removed for export] *)
      apply (ords_ok_ext n rho); [rewrite Hn1; lia | exact Hrho | exact Hord].
    - (* [comment removed for export] *)
      assert (Etop : alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m)).
      { pose proof Hne as Hne2. destruct Hne2 as [_ _ _ _ _ _ Hsp2 _ _ _ _].
        change (vm_init_sp (m_vmmaps (erase m'))) with (vm_init_sp (m_vmmaps m')) in Hsp2.
        change (vm_init_sp (m_vmmaps (erase m))) with (vm_init_sp (m_vmmaps m)) in Hsp2.
        unfold alloc_top. rewrite Hsp2. reflexivity. }
      rewrite Forall_app. split.
      + apply Forall_forall. intros o Ho.
        assert (Hto : to_Z (fent_tag (snd o)) < to_Z n)
          by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
        apply (op_ok_ext n rho rho' m m' (fl_all L3) (e :: fl_all L3) o Hrho Hto Ht1 Etop).
        * intros e' [<-|He'] Hlt'; [|exact He']. exfalso. unfold e in Hlt'. cbn [fent_tag fst] in Hlt'. lia.
        * exact (proj1 (Forall_forall _ _) Hopsf o Ho).
      + constructor; [|constructor].
        assert (Hopnew : bv_unsigned (rho' (fent_tag e)) mod 4096 = 0
                  /\ (forall e', In e' (e :: fl_all L3) -> to_Z (fent_tag e') < to_Z (fent_tag e) -> e_disj (den rho' e') (den rho' e))
                  /\ e_hi (den rho' e) <= alloc_top (m_vmmaps m')).
        { split; [unfold e; cbn [fent_tag fst]; rewrite Hrn; exact Hal|]. split.
          - intros e' [<-|He'] Hlt'; [lia|]. rewrite Hden_e.
            rewrite (Hden_lt e') by (exact (proj1 (Forall_forall _ _) Ht1 e' He')).
            apply e_disj_sym. apply Hdisj. rewrite Hex. apply in_map. exact He'.
          - rewrite Hden_e, Etop. unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite HnZw. exact Hatop. }
        unfold op_ok. cbn [fst snd]. cbv zeta. destruct nr; exact Hopnew.
    - (* [comment removed for export] *)
      apply (ress_ok_ext n rho); [rewrite Hn1; lia | exact Hrho | exact Hres]. }
  split.
  { (* [comment removed for export] *)
    destruct HS as [Hz Hcov Hsp Hexc].
    assert (Hden0 : forall e0 : fent, fent_tag e0 = 0%uint63 -> den rho' e0 = den rho e0).
    { intros e0 Et0. apply Hden_lt. rewrite Et0, to_Z_0. lia. }
    pose proof (lazy_cov_tags _ _ n Hexc Ht1) as Ht5.
    constructor; cbn [grant_ledger3 fl_all fl_ex].
    - intros x Hx Hno Hnex.
      assert (Hno0 : no_region rho (f_mem F) (bv_unsigned x)).
      { intros t rg Hgt Hin. destruct (Hregs t rg Hgt) as [Er Eg]. apply (Hno t rg Eg).
        unfold in_ival in *. rewrite Er. exact Hin. }
      assert (Hout : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ)).
      { intros Hin. apply (Hno n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi))).
        - change (f_mem (fx_grant F n nZi)) with (iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)).
          apply iget_iset_same.
        - unfold in_ival. cbn [rg_lo rg_len]. rewrite Hrn, to_Z_0, HnZ. lia. }
      assert (Hnex0 : ~ exempted rho (fl_ex L3) (bv_unsigned x)).
      { intros Hc. apply Hnex. apply (exempted_ext rho rho'); [|exact Hc].
        intros e0 He0. exact (Hden_lt e0 (proj1 (Forall_forall _ _) Ht5 e0 He0)). }
      destruct (Hz x Hx Hno0 Hnex0) as [Z1 Z2]. unfold rview, wview in *. unfold ms'.
      rewrite sysret_mem, apply_zeros_one, HnZw.
      replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false.
      + split; assumption.
      + symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hout. lia.
    - intros x Hx. destruct (Hcov x Hx) as (e0 & He0 & Et0 & Hpx). exists e0.
      split; [right; exact He0|]. split; [exact Et0|]. rewrite (Hden0 e0 Et0). exact Hpx.
    - intros t rg Hgt. destruct (Hnew t rg Hgt) as [[-> ->] | [Hne' Hgt0]].
      + unfold span_ok. cbn [rg_kind rg_lo rg_len]. left. rewrite Hrn, to_Z_0, HnZ.
        destruct Hmiss as [Hl|Hh']; [left; exact Hl | right; lia].
      + destruct (Hregs t rg Hgt0) as [Er _]. pose proof (Hsp t rg Hgt0) as Hok. unfold span_ok in *.
        destruct (rg_kind rg) as [|p]; [rewrite Er; exact Hok|].
        destruct Hok as (Et & rgp & Hgp & Hrest). split; [exact Et|]. exists rgp.
        split; [exact (proj2 (Hregs p rgp Hgp)) | exact Hrest].
    - apply (lazy_cov_mono (fl_all L3)); [intros e0 He0; right; exact He0 | exact Hexc]. }
  exact (xpart_node _ _ _ _ _ _ _ _ _ _ _ _ HX Hne Hbrk').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sys_ok3 (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3) (res : dres3)
    (ms : machine_state) (m : Model) : Prop :=
  exists (I : Type) (i0 : I) (nx : I -> config),
    (forall e st, sstep_cfg segs cfg (mkCfg (ms_pend ms) m) e st <->
                  exists i, e = [] /\ st = SNext (nx i))
    /\ forall i, exists F' L3' n' rho',
         dres3_in (F', L3', n') res
         /\ D3 n' rho' F' L3' (cfg_ms (nx i)) (cfg_model (nx i))
         /\ PX n rho F L3 ms m n' rho' F' L3' (cfg_ms (nx i)) (cfg_model (nx i)).

(* [comment removed for export] *)
Definition pc_ok3 (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3) (res : dres3)
    (ms : machine_state) (m : Model) : Prop :=
  (forall T,
     (forall F' L3' n' rho' ms' m',
        dres3_in (F', L3', n') res -> D3 n' rho' F' L3' ms' m' ->
        PX n rho F L3 ms m n' rho' F' L3' ms' m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
     realizes_cfg cfg segs (mkCfg ms m) T)
  /\ (exists F' L3' n' rho' ms' m',
        dres3_in (F', L3', n') res /\ D3 n' rho' F' L3' ms' m'
        /\ PX n rho F L3 ms m n' rho' F' L3' ms' m'
        /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')).

(* [comment removed for export] *)
Lemma sys_grant3_inv nr F L3 n len res :
  sys_grant3 Rb Rc Lim nr F L3 n len = Some res ->
  (0 <? len)%uint63 = true /\ (len <=? 4611686018427387904)%uint63 = true
  /\ (pg_up len <=? 4611686018427387904)%uint63 = true /\ tag_ok F n = true
  /\ grant_fits Rb Rc BIG RTgt (fl3 L3) (to_Z (pg_up len)) = true
  /\ exists L', acct_ok Lim (grant_ledger3 nr L3 L' (n, 0%uint63, pg_up len)) = true.
Proof.
  intros Hsys. unfold sys_grant3 in Hsys.
  destruct (sys_grant Rb Rc BIG RTgt F (fl3 L3) n len) as [[F' L' n'|]|] eqn:Hg; try discriminate.
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hacct; [|discriminate] end.
  unfold sys_grant in Hg. cbv zeta in Hg.
  match type of Hg with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  repeat (split; [assumption|]). exists L'. exact Hacct.
Qed.

(* [comment removed for export] *)
Lemma grant3_steps n rho F L3 ms m nr len res :
  sys_grant3 Rb Rc Lim nr F L3 n len = Some res ->
  D3 n rho F L3 ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = (if nr then 16418 else 34) ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  let nZ := page_round_up_Z (to_Z len) in
  exists (I : Type) (i0 : I) (aof : I -> word),
    (forall e st, sstep_cfg segs cfg (mkCfg (ms_pend ms) m) e st <->
       exists i, e = [] /\
         st = SNext (mkCfg (sysret (ms_pend ms) (aof i)
                              (apply_zeros (ms_mem (ms_pend ms)) [(aof i, Z_to_bv 64 nZ)]))
                           (grant_model3 nr (aof i) nZ m)))
    /\ forall i, mmap_grant_na_b (m_vmmaps m) (aof i) nZ = true.
Proof.
  intros Hsys HD Hstep Hx8 Ha1 Ha2 Ha3 Ha5.
  destruct (sys_grant3_inv nr F L3 n len res Hsys) as (Hpos & Hle & Hup & Htag & Hfit & L0 & Hacct).
  pose proof HD as (HDI & HL & _).
  pose proof HDI as (HRn & H0 & Hh & _ & Hli & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  change (m_vmmaps (erase m)) with (erase_vm wb0 (m_vmmaps m)) in Hli.
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec R0 len Hle) as HnZ. cbv zeta.
  set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  destruct (ledger_inv_params_nonneg _ _ _ _ _ Hli) as [Hc0 HS0].
  unfold grant_fits in Hfit. apply andb_true_iff in Hfit as [Hpig _].
  apply Z.leb_le in Hpig. rewrite HnZ in Hpig.
  assert (Hpig' : page_size + (live_bytes R0 + fl_S (fl3 L3)) + (Z.of_nat (length R0) + fl_c (fl3 L3)) * (nZ + page_size) + nZ
                  <= alloc_lo_bound).
  { rewrite alloc_lo_bound_val. unfold page_size.
    assert ((Z.of_nat (length R0) + fl_c (fl3 L3)) * (nZ + 4096) <= (Rc + fl_c (fl3 L3)) * (nZ + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  destruct (mmap_grant_na_exists_inv R0 BIG _ _ _ nZ Hli ltac:(lia) Hpig') as [a0 Ha0].
  change (mmap_grant_na_b (m_vmmaps m) a0 nZ = true) in Ha0.
  destruct nr.
  - (* [comment removed for export] *)
    assert (Hargs : mmap_anon_nr_args (ms_pend ms) (to_Z len)) by (unfold mmap_anon_nr_args; repeat split; assumption).
    pose proof (mmap_anon_nr_step_iff_lz cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh
                  (ms_pend_svc ms) Hx8 Hargs (ex_intro _ a0 Ha0)) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
    exists {a : word | mmap_grant_na_b (m_vmmaps m) a nZ = true}, (exist _ a0 Ha0), (fun i => proj1_sig i).
    split; [|intros [a Ha]; exact Ha].
    intros e st. rewrite Hiff. split.
    + intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
    + intros ([a Ha] & -> & ->). exists a. repeat split. exact Ha.
  - (* [comment removed for export] *)
    assert (Hargs : mmap_anon_args (ms_pend ms) (to_Z len)) by (unfold mmap_anon_args; repeat split; assumption).
    assert (Hbud : vm_backing_used m + nZ <= vm_limit (m_vmmaps m)).
    { apply (lazy_part_budget IM R0 Lim mem0 rom0 hi na0 lz0 brk0 A0 n rho F L3 m nZ HL).
      apply Z.leb_le in Hacct. unfold acct_ok in Hacct. cbn [grant_ledger3 fl_E fl_Ab snd] in Hacct.
      rewrite HnZ in Hacct. pose proof (lp_E _ _ _ _ _ _ _ _ _ _ _ HL). clear - Hacct HnZpos. lia. }
    assert (Hex : exists a, mmap_grant_b m a nZ = true).
    { exists a0. apply mmap_grant_na_b_iff in Ha0 as (A1 & A2 & A3 & A4).
      apply mmap_grant_b_iff. repeat split; assumption. }
    pose proof (mmap_anon_step_iff_lz cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh
                  (ms_pend_svc ms) Hx8 Hargs Hex) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
    destruct Hex as [a1 Ha1'].
    exists {a : word | mmap_grant_b m a nZ = true}, (exist _ a1 Ha1'), (fun i => proj1_sig i).
    split.
    + intros e st. rewrite Hiff. split.
      * intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
      * intros ([a Ha] & -> & ->). exists a. repeat split. exact Ha.
    + intros [a Ha]. cbn [proj1_sig].
      apply mmap_grant_b_iff in Ha as (A1 & A2 & A3 & A4 & _). apply mmap_grant_na_b_iff. repeat split; assumption.
Qed.

Theorem sys_grant3_sound n rho F L3 ms m nr len res :
  sys_grant3 Rb Rc Lim nr F L3 n len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = (if nr then 16418 else 34) ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_ok3 n rho F L3 res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5.
  destruct (grant3_steps n rho F L3 ms m nr len res Hsys HD Hstep Hx8 Ha1 Ha2 Ha3 Ha5)
    as (I & i0 & aof & Hiff & Hadm).
  exists I, i0, (fun i => mkCfg (sysret (ms_pend ms) (aof i)
                            (apply_zeros (ms_mem (ms_pend ms)) [(aof i, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
                         (grant_model3 nr (aof i) (page_round_up_Z (to_Z len)) m)).
  split; [exact Hiff|].
  intros i. cbn [cfg_ms cfg_model].
  destruct (grant3_succ n rho F L3 ms m nr len res (aof i) Hsys HD Hat (Hadm i)) as (L3' & E & HD' & Hdx & _).
  exists (fx_grant F n (pg_up len)), L3', (n + 1)%uint63, (rho_upd rho n (aof i)).
  rewrite E. split; [reflexivity|]. split; [exact HD' | exact Hdx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unmap_succ_inv n rho F L ms m0 t off len res :
  sys_unmap keep F L n t off len = Some res ->
  DI n rho F L ms m0 -> at_ecall F ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  exists rg,
    let nw := Z_to_bv 64 (to_Z (rg_len rg)) in
    let L' := FL (drop_tag t (fl_maps L)) (drop_tag t (fl_na L)) (fl_brk L) (fl_c L - 1)
                 (fl_S L - to_Z (rg_len rg)) in
    let ms' := sysret (ms_pend ms) (Z_to_bv 64 0) (apply_unmaps (ms_mem (ms_pend ms)) [(rho t, nw)]) in
    let m0' := with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0 in
    iget t (f_mem F) = Some rg /\ t <> 0%uint63 /\ to_Z (rg_lo rg) = 0 /\ 0 < to_Z (rg_len rg)
    /\ bv_unsigned nw = to_Z (rg_len rg)
    /\ In (t, 0%uint63, rg_len rg) (fl_maps L)
    /\ ms_gpr (ms_pend ms) 0 = rho t
    /\ munmap_entry_args (ms_pend ms) m0 (to_Z len) nw
    /\ res = DOne (fx_unmap F t) L' n
    /\ DI n rho (fx_unmap F t) L' ms' m0'
    /\ NE n rho F L ms m0 n rho (fx_unmap F t) L' ms' m0'.
Proof.
  intros Hsys (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Ha0 Ha1.
  unfold sys_unmap in Hsys. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hsys as <-.
  repeat match type of Hchk with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hchk as [Hchk H] end.
  rename Hchk into Hoff.
  apply Uint63.eqb_spec in Hoff. subst off. rewrite to_Z_0, adr_0 in Ha0.
  apply negb_true_iff in Hc7. apply eqb_false_spec in Hc7.       (* [comment removed for export] *)
  apply ltb_spec in Hc6.                                         (* [comment removed for export] *)
  apply negb_true_iff in Hc5. apply eqb_false_spec in Hc5.       (* [comment removed for export] *)
  apply negb_true_iff in Hc4. apply mem_int_false in Hc4.        (* [comment removed for export] *)
  apply ltb_spec in Hc3. rewrite to_Z_0 in Hc3.                  (* [comment removed for export] *)
  apply leb_spec in Hc2. change (to_Z 4611686018427387904) with (2 ^ 62) in Hc2.
  apply Uint63.eqb_spec in Hc1.                                  (* [comment removed for export] *)
  apply Uint63.eqb_spec in Hc0.                                  (* [comment removed for export] *)
  apply mem_fent_In in Hc.
  assert (Hlo0 : to_Z (rg_lo rg) = 0) by (rewrite Hc1; reflexivity).
  pose proof (pg_up_spec R0 len Hc2) as Hup. rewrite Hc0 in Hup.
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hg) as Hreg.
  pose proof (R_regions_sep _ _ _ _ _ HR) as Hsep.
  pose proof (i63_range (rg_len rg)) as Hlenr.
  exists rg. cbv zeta.
  set (nw := Z_to_bv 64 (to_Z (rg_len rg))).
  assert (Hnw : bv_unsigned nw = to_Z (rg_len rg)) by (apply u64_lit; lia).
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk).
  assert (Hin : In (rho t, nw) (vm_maps (m_vmmaps m0))).
  { pose proof (proj1 (Forall_forall _ _) Hm1 _ Hc) as (rg' & _ & _ & _ & Hi).
    rewrite to_Z_0, adr_0 in Hi. exact Hi. }
  assert (Hargs : munmap_entry_args (ms_pend ms) m0 (to_Z len) nw).
  { apply (munmap_entry_args_of_inv R0 BIG (fl_c L) (fl_S L)); try assumption.
    - rewrite Hnw. exact Hup.
    - rewrite Ha0. exact Hin. }
  assert (Hival : forall x, in_ival rho t rg x <-> bv_unsigned (rho t) <= x < bv_unsigned (rho t) + to_Z (rg_len rg)).
  { intros x. unfold in_ival. rewrite Hlo0. lia. }
  assert (Hne_len : 0 < to_Z (rg_len rg)) by (pose proof (proj1 (Hcov t rg Hg)); lia).
  split; [reflexivity|]. split; [exact Hc7|]. split; [exact Hlo0|]. split; [exact Hne_len|].
  split; [exact Hnw|]. split; [exact Hc|]. split; [exact Ha0|]. split; [exact Hargs|].
  split; [reflexivity|].
  pose proof (fx_unmap_sound segs IM n rho F ms t rg HRn Hat Hg Hc7 Hc6 Hlo0) as HRn'.
  assert (Hother : forall t', t' <> t -> iget t' (iremove t (f_mem F)) = iget t' (f_mem F)).
  { intros t' Hne. apply iget_iremove_other. intros E. apply Hne. symmetry. exact E. }
  assert (HM' : f_mem (fx_unmap F t) = iremove t (f_mem F)) by reflexivity.
  split.
  2:{ constructor.
      - lia.
      - intros; reflexivity.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_unmaps_one, Hnw.
          replace ((bv_unsigned (rho t) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg)))
            with false; [reflexivity|].
          symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
          apply Z.leb_le in B1. apply Z.ltb_lt in B2.
          exact (Hno t rg Hg (proj2 (Hival _) (conj B1 B2))).
        + rewrite HM'. intros t' rg' Hg' Hxin.
          destruct (Uint63.eqb t' t) eqn:E.
          * apply Uint63.eqb_spec in E. subst t'. rewrite iget_iremove_same in Hg'. discriminate.
          * assert (Hne' : t' <> t) by (intros ->; rewrite Uint63.eqb_refl in E; discriminate).
            rewrite (Hother t' Hne') in Hg'. exact (Hno t' rg' Hg' Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2].
        assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
          by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ _ _ HR Hg')).
        split.
        + cbn [fl_maps].
          change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0)))
            with (map_remove (vm_maps (m_vmmaps m0)) (rho t)).
          rewrite E1. symmetry.
          apply (unmap_exact_maps R0 rho (f_mem F) t rg (fl_maps L) Hregs Hsep Hg Hlo0 Hne_len).
          * rewrite <- E1. exact (li_disj _ _ _ _ _ Hli).
          * rewrite <- E1. exact (li_pos _ _ _ _ _ Hli).
          * eapply Forall_impl; [|exact Hm1]. intros e He. exact (proj1 (proj1 (ent_ok_iff _ _ _ _) He)).
          * exact Hc.
        + cbn [fl_na].
          change (vm_noaccess (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0)))
            with (maps_subtract (vm_noaccess (m_vmmaps m0)) (bv_unsigned (rho t)) (bv_unsigned (rho t) + bv_unsigned nw)).
          rewrite Hnw, E2. symmetry.
          apply (unmap_exact_na R0 mem0 rho (f_mem F) (vm_noaccess (m_vmmaps m0)) t rg (fl_na L) Hregs Hsep Hg Hlo0); [|exact Hm2].
          eapply Forall_impl; [|exact (li_noacc _ _ _ _ _ Hli)]. intros q0 [Hq0 _]. exact Hq0. }
  split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|].
  split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split.
  { cbn [fl_c fl_S]. rewrite <- Hnw.
    exact (munmap_entry_inv R0 BIG (fl_c L) (fl_S L) m0 (rho t) nw Hli Hin). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t' rg' Hg'. rewrite iget_iremove in Hg'.
    destruct (t' =? t)%uint63 eqn:E; [discriminate|]. apply eqb_false_spec in E.
    destruct (Hcov t' rg' Hg') as [Hne Hb]. split; [exact Hne|]. intros x Hx.
    destruct (Hb x Hx) as [(p & Hp & Hpx) | Hat'].
    - left. exists p. split; [|exact Hpx]. apply in_app_iff in Hp. apply in_app_iff.
      destruct Hp as [Hp|Hp]; [left; exact Hp|]. right.
      change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0)))
        with (map_remove (vm_maps (m_vmmaps m0)) (rho t)).
      apply map_remove_keep; [exact Hp|].
      destruct (entry_eq_dec_prop p (rho t, nw)) as [Ep|Ep].
      + exfalso. subst p. unfold e_hi, e_lo, e_sz in Hpx. cbn [fst snd] in Hpx. rewrite Hnw in Hpx.
        exact (ival_disjoint R0 rho (f_mem F) t' t rg' rg x Hsep E Hg' Hg Hx (proj2 (Hival x) Hpx)).
      + exact (entries_base_neq _ _ _ _ _ p (rho t, nw) Hli Hp Hin Ep).
    - right. exact Hat'. }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. split; [|split].
    - cbn [fl_maps]. apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      pose proof (proj1 (Forall_forall _ _) Hm1 _ He) as Hok.
      destruct e as [[t' off'] len']. cbn [fent_tag fst] in Htag.
      destruct Hok as (rg' & Hg' & Hl1 & Hl2 & Hi).
      exists rg'. rewrite (Hother t' Htag). repeat split; try assumption.
      change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0)))
        with (map_remove (vm_maps (m_vmmaps m0)) (rho t)).
      apply map_remove_keep; [exact Hi|].
      apply (entries_base_neq _ _ _ _ _ _ (rho t, nw) Hli Hi Hin).
      intros Eq.
      pose proof (proj1 (Forall_forall _ _) (li_pos _ _ _ _ _ Hli) _ Hi) as Hpos. cbv beta in Hpos.
      destruct (ent_range R0 rho t' off' len' rg' (R_region_ok _ _ _ _ _ _ _ HR Hg') Hl1 Hl2) as [El Eh].
      unfold e_hi in Eh. rewrite El in Eh.
      assert (Hbase : bv_unsigned (rho t) = bv_unsigned (rho t') + to_Z off').
      { rewrite <- El. rewrite Eq. reflexivity. }
      apply (ival_disjoint R0 rho (f_mem F) t' t rg' rg (bv_unsigned (rho t)) Hsep Htag Hg' Hg).
      + unfold in_ival. lia.
      + apply Hival. lia.
    - cbn [fl_na]. apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      pose proof (proj1 (Forall_forall _ _) Hm2 _ He) as Hok.
      destruct e as [[t' off'] len']. cbn [fent_tag fst] in Htag.
      destruct Hok as (rg' & Hg' & Hl1 & Hl2 & Hi).
      exists rg'. rewrite (Hother t' Htag). repeat split; try assumption.
      change (vm_noaccess (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m0)) m0)))
        with (maps_subtract (vm_noaccess (m_vmmaps m0)) (bv_unsigned (rho t)) (bv_unsigned (rho t) + bv_unsigned nw)).
      pose proof (proj1 (Forall_forall _ _) (li_noacc _ _ _ _ _ Hli) _ Hi) as [Hpos _].
      destruct (ent_range R0 rho t' off' len' rg' (R_region_ok _ _ _ _ _ _ _ HR Hg') Hl1 Hl2) as [El Eh].
      apply maps_subtract_keep; [exact Hi | lia | exact Hpos |].
      rewrite El, Eh, Hnw.
      destruct (Hsep t' t rg' rg Htag Hg' Hg) as [Hd|Hd]; [left | right]; lia.
    - cbn [fl_brk]. exists rgb. split; [|exact Hbrk].
      rewrite Hother; [exact Hgb|]. intros E. apply Hc5. symmetry. exact E. }
  split; [exact I|].
  split; [apply (XI_vm rho m0); [repeat split; reflexivity | exact HXI]|]. split; [exact Hxt|].
  (* [comment removed for export] *)
  rewrite HM'. intros tk Htk. destruct (Hfr tk Htk) as [Hpr Hmem].
  assert (Hnek : tk <> t) by (intros ->; contradiction).
  split; [exact (pristine_eq _ _ _ (Hother tk Hnek) Hpr)|].
  intros rgk x Hgk Hx. rewrite (Hother tk Hnek) in Hgk.
  rewrite sysret_mem, apply_unmaps_one, Hnw.
  replace ((bv_unsigned (rho t) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg)))
    with false; [exact (Hmem rgk x Hgk Hx)|].
  symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  exact (ival_disjoint R0 rho (f_mem F) tk t rgk rg _ Hsep Hnek Hgk Hg Hx (proj2 (Hival _) (conj B1 B2))).
Qed.




(* [comment removed for export] *)
Lemma munmap_model_facts a n m :
  vm_maps (m_vmmaps (munmap_model a n m)) = map_remove (vm_maps (m_vmmaps m)) a
  /\ vm_noaccess (m_vmmaps (munmap_model a n m))
     = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  /\ m_vm_lazy (munmap_model a n m)
     = maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  /\ m_vm_materialized (munmap_model a n m)
     = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m)
  /\ vm_limit (m_vmmaps (munmap_model a n m)) = vm_limit (m_vmmaps m)
  /\ vm_brk (m_vmmaps (munmap_model a n m)) = vm_brk (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps (munmap_model a n m)) = vm_start_brk (m_vmmaps m)
  /\ vm_mmap_base (m_vmmaps (munmap_model a n m)) = vm_mmap_base (m_vmmaps m).
Proof. destruct m as [fd [maps lazy mat] io fs proc lim tm]; repeat split; reflexivity. Qed.

Lemma erase_munmap_model a n m :
  erase (munmap_model a n m) = with_vmmaps (ledger_unmap a n (m_vmmaps (erase m))) (erase m).
Proof. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Theorem sys_unmap3_sound n rho F L3 ms m t off len res :
  sys_unmap3 Lim keep F L3 n t off len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 215 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  sys_ok3 n rho F L3 res ms m.
Proof.
  intros Hsys (HDI & HL & HS & HX) Hat Hstep Hx8 Ha0 Ha1.
  unfold sys_unmap3 in Hsys.
  destruct (sys_unmap keep F (fl3 L3) n t off len) as [[F' L' n'|]|] eqn:Hg; try discriminate.
  destruct (iget t (f_mem F)) as [rg0|] eqn:Hg0; [|discriminate].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hsys as <-.
  apply andb_true_iff in Hchk as [Hchk Hacct]. apply andb_true_iff in Hchk as [Hchk Hpv].
  apply andb_true_iff in Hchk as [Hchk Hexf].
  apply andb_true_iff in Hchk as [Hchild Hlz].
  destruct (unmap_succ_inv n rho F (fl3 L3) ms (erase m) t off len _ Hg HDI Hat Ha0 Ha1)
    as (rg & Hgt & Ht0 & Hlo0 & Hlen & Hnw & Hwhole & Ha0' & Hargs & Eres & HDI' & Hne).
  rewrite Hgt in Hg0. injection Hg0 as <-.
  cbv zeta in *. injection Eres as -> -> ->.
  set (nw := Z_to_bv 64 (to_Z (rg_len rg))) in *.
  set (e0 := (t, 0%uint63, rg_len rg)) in *.
  set (L' := FL (drop_tag t (fl_maps (fl3 L3))) (drop_tag t (fl_na (fl3 L3))) (fl_brk (fl3 L3))
                (fl_c (fl3 L3) - 1) (fl_S (fl3 L3) - to_Z (rg_len rg))) in *.
  set (L3' := unmap_ledger3 L3 L' t (rg_len rg)) in *.
  set (ms' := sysret (ms_pend ms) (Z_to_bv 64 0) (apply_unmaps (ms_mem (ms_pend ms)) [(rho t, nw)])) in *.
  set (m' := munmap_model (rho t) nw m).
  rewrite <- (erase_munmap_model (rho t) nw m) in HDI', Hne. fold m' in HDI', Hne.
  change (munmap_entry_args (ms_pend ms) m (to_Z len) nw) in Hargs.
  pose proof HDI as (HRn & H0 & Hh & _ & Hli & _ & Hmir & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  change (m_vmmaps (erase m)) with (erase_vm wb0 (m_vmmaps m)) in Hli, Hmir.
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof (R_regions_sep _ _ _ _ _ HR) as Hsep.
  assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
    by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ _ _ HR Hg')).
  destruct HL as [Hpi Hreg Hpw Hml Hsub HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz HopsR Hord Hopsf Hres].
  destruct Hmir as (Hm1 & _ & _).
  change (vm_maps (erase_vm wb0 (m_vmmaps m))) with (vm_maps (m_vmmaps m)) in Hm1.
  pose proof (li_disj _ _ _ _ _ Hli) as Hpw0. pose proof (li_pos _ _ _ _ _ Hli) as Hposm.
  pose proof (li_aligned _ _ _ _ _ Hli) as Halm.
  change (vm_maps (erase_vm wb0 (m_vmmaps m))) with (vm_maps (m_vmmaps m)) in Hpw0, Hposm, Halm.
  pose proof Hpw0 as Hpwd. rewrite Hex in Hpwd.
  assert (He0all : In e0 (fl_all L3)) by (exact (proj1 (Forall_forall _ _) H9a e0 Hwhole)).
  assert (Hden0 : den rho e0 = (rho t, nw)).
  { unfold e0. cbn [den]. rewrite to_Z_0, adr_0. reflexivity. }
  pose proof (u64 (rho t)) as Hrt.
  pose proof (region_ok_nowrap rho t rg (Hregs t rg Hgt)) as Hnwrap.
  set (lo := bv_unsigned (rho t)) in *. set (hi' := lo + to_Z (rg_len rg)).
  assert (Hin0 : In (rho t, nw) (vm_maps (m_vmmaps m))).
  { rewrite Hex, <- Hden0. apply in_map. exact He0all. }
  assert (Hlo_al : lo mod 4096 = 0).
  { pose proof (proj1 (Forall_forall _ _) Halm _ Hin0) as [Hal0 _]. exact Hal0. }
  assert (Hposall : forall e, In e (fl_all L3) -> 0 < e_sz (den rho e)).
  { intros e He. apply (proj1 (Forall_forall _ _) Hposm). rewrite Hex. apply in_map. exact He. }
  (* [comment removed for export] *)
  assert (Hin_t : forall e, ent_in (f_mem F) e -> fent_tag e = t ->
            lo <= e_lo (den rho e) /\ e_hi (den rho e) <= hi').
  { intros e Hine Et. destruct (ent_in_range R0 rho (f_mem F) e Hregs Hine) as (rg' & Hg' & Hl & Hh').
    rewrite Et, Hgt in Hg'. injection Hg' as <-. rewrite Et in Hl, Hh'. unfold hi', lo. lia. }
  assert (Hdisj0 : forall e, In e (fl_all L3) -> fent_tag e <> t ->
            e_hi (den rho e) <= lo \/ hi' <= e_lo (den rho e)).
  { intros e He Hne'. assert (Hneq : e <> e0) by (intros ->; apply Hne'; reflexivity).
    pose proof (pw_disj_map_In (den rho) _ e e0 Hpwd He He0all Hneq) as Hd. rewrite Hden0 in Hd.
    unfold e_disj, e_hi, e_lo, e_sz in *. cbn [fst snd] in Hd. rewrite Hnw in Hd. unfold hi', lo. lia. }
  pose proof (li_top _ _ _ _ _ Hli) as Htopm.
  change (vm_maps (erase_vm wb0 (m_vmmaps m))) with (vm_maps (m_vmmaps m)) in Htopm.
  change (alloc_top (erase_vm wb0 (m_vmmaps m))) with (alloc_top (m_vmmaps m)) in Htopm.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hattop. unfold two_pow_64 in Hattop.
  assert (Hhi64 : hi' < 2 ^ 64).
  { pose proof (proj1 (Forall_forall _ _) Htopm _ Hin0) as [_ Hh0].
    unfold e_hi, e_lo, e_sz in Hh0. cbn [fst snd] in Hh0. rewrite Hnw in Hh0. unfold hi', lo. lia. }
  (* [comment removed for export] *)
  assert (Hcov_disj : forall l e, lazy_cov (fl_all L3) l -> In e l -> fent_tag e <> t ->
            e_hi (den rho e) <= lo \/ hi' <= e_lo (den rho e)).
  { intros l e Hc He Htag.
    destruct (lazy_cov_inside rho (fl_all L3) l (vm_maps (m_vmmaps m)) e Hc Hex) as (e' & He' & Et' & Hins); [|exact He|].
    - intros p Hp. pose proof (proj1 (Forall_forall _ _) Htopm p Hp) as [_ Hh0]. lia.
    - assert (Htag' : fent_tag e' <> t) by (rewrite Et'; exact Htag).
      destruct (Hdisj0 e' He' Htag') as [Hd|Hd]; unfold e_inside in Hins; [left | right]; lia. }
  (* [comment removed for export] *)
  pose proof (munmap_entry_step_iff_gen_lz cfg segs (ms_pend ms) (ms_reg ms 17) m (to_Z len) nw Hh
                (ms_pend_svc ms) Hx8 Hargs) as Hiff.
  rewrite Ha0' in Hiff. fold m' ms' in Hiff.
  exists unit, tt, (fun _ => mkCfg ms' m').
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _. cbn [cfg_ms cfg_model].
  destruct (munmap_model_facts (rho t) nw m) as (Fm & Fna & Flz & Fmat & Flim & Fbrk & Fsb & Fmb).
  fold m' lo in Fm, Fna, Flz, Fmat, Flim, Fbrk, Fsb, Fmb. rewrite Hnw in Fna, Flz, Fmat. fold hi' in Fna, Flz, Fmat.
  exists (fx_unmap F t), L3', n, rho. split; [reflexivity|].
  assert (HM' : f_mem (fx_unmap F t) = iremove t (f_mem F)) by reflexivity.
  assert (He0lo0 : e_lo (den rho e0) = lo /\ e_hi (den rho e0) = lo + to_Z (rg_len rg)).
  { rewrite Hden0. unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite Hnw. split; reflexivity. }
  split.
  2:{ split; [exact (dext_node _ _ _ _ _ _ _ _ _ _ _ _ Hne Fsb Fmb)|].
      exists [(OpCut, e0)]. split; [reflexivity|].
      split; [constructor; [cbn [snd]; exact (proj1 (Forall_forall _ _) (proj1 (proj1 (Forall_app _ _ _) Htags)) e0 He0all) | constructor]|].
      split; [|split].
      - intros x Hnt _. unfold ms'. rewrite sysret_mem, apply_unmaps_one, Hnw. fold lo.
        replace ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + to_Z (rg_len rg))) with false; [reflexivity|].
        symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hnt.
        exists (OpCut, e0). split; [left; reflexivity|]. cbn [snd]. rewrite (proj1 He0lo0), (proj2 He0lo0). lia.
      - intros x (t1 & rg1 & pn & p & j & Hg1 & Hrest). left. exists t1, rg1, pn, p, j. split; [|exact Hrest].
        rewrite HM', iget_iremove in Hg1. destruct (t1 =? t)%uint63; [discriminate | exact Hg1].
      - intros x (t1 & rg1 & pn & p & ci & Hg1 & Hp & Hci & j & Hj & ->).
        destruct (t1 =? t)%uint63 eqn:E.
        + (* [comment removed for export] *)
          apply Uint63.eqb_spec in E. subst t1. rewrite Hgt in Hg1. injection Hg1 as <-.
          right. exists (OpCut, e0). split; [left; reflexivity|]. cbn [snd]. rewrite (proj1 He0lo0), (proj2 He0lo0).
          assert (Hpn : to_Z pn < 2 ^ 50 /\ 0 <= to_Z ci < 512
                        /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg)).
          { pose proof (proj1 (iall_spec _ _) Hpv pn p Hp) as Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
            apply ltb_spec in Hb1. change (to_Z 1125899906842624) with (2 ^ 50) in Hb1. split; [exact Hb1|].
            destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|congruence].
            pose proof (proj1 (iall_spec _ _) Hb2 ci c Ec) as Hb3. apply andb_true_iff in Hb3 as [Hb3 Hb4].
            apply ltb_spec in Hb3. apply leb_spec in Hb4.
            change (to_Z 512) with 512 in Hb3. pose proof (i63_range ci) as Hci0. pose proof (i63_range pn) as Hpn0.
            split; [lia|].
            assert (E1 : to_Z (pn << 12) = to_Z pn * 4096).
            { rewrite lsl_spec. change (2 ^ to_Z 12) with 4096. apply Z.mod_small. change wB with (2 ^ 63). lia. }
            assert (E2 : to_Z (ci << 3) = to_Z ci * 8).
            { rewrite lsl_spec. change (2 ^ to_Z 3) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
            pose proof (i63_range (rg_len rg)) as Hlr0.
            rewrite !add_spec, E1, E2 in Hb4. change (to_Z 8) with 8 in Hb4. change wB with (2 ^ 63) in Hb4.
            rewrite (Z.mod_small (to_Z pn * 4096 + to_Z ci * 8)) in Hb4 by lia.
            rewrite Z.mod_small in Hb4 by lia. exact Hb4. }
          pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0.
          rewrite adr_unsigned by (fold lo; lia). fold lo. lia.
        + left. exists t1, rg1, pn, p, ci. split.
          * rewrite HM', iget_iremove, E. exact Hg1.
          * split; [exact Hp|]. split; [exact Hci|]. exists j. split; [exact Hj | reflexivity]. }
  assert (Hother : forall t' rg', iget t' (f_mem (fx_unmap F t)) = Some rg' -> t' <> t /\ iget t' (f_mem F) = Some rg').
  { intros t' rg' Hg'. rewrite HM', iget_iremove in Hg'. destruct (t' =? t)%uint63 eqn:E; [discriminate|].
    apply eqb_false_spec in E. split; [exact E | exact Hg']. }
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HDI'))))) as Hli'.
  apply Forall_app in Htags as [Ht1 Htags]. apply Forall_app in Htags as [Ht2 Ht3].
  assert (Hmaps' : vm_maps (m_vmmaps m') = map (den rho) (drop_tag t (fl_all L3))).
  { rewrite Fm, Hex. symmetry.
    apply map_den_drop_tag_remove. intros e He.
    destruct (fent_tag e =? t)%uint63 eqn:Et.
    - apply Uint63.eqb_spec in Et.
      destruct (entry_eq_dec_prop (den rho e) (rho t, nw)) as [E|E]; [rewrite E; apply bv_eqb_refl_true|].
      exfalso. destruct (proj1 (Forall_forall _ _) H9b e He) as [Hinm | [Et0 | Hno]];
        [| congruence | rewrite Et, Hgt in Hno; discriminate Hno].
      pose proof (proj1 (Forall_forall _ _) Hm1 e Hinm) as Hok. apply ent_ok_iff in Hok as [Hine _].
      destruct (Hin_t e Hine Et) as [I1 I2].
      rewrite <- Hden0 in E.
      pose proof (pw_disj_In _ _ _ Hpwd (in_map (den rho) _ _ He) (in_map (den rho) _ _ He0all) E) as Hd.
      rewrite Hden0 in Hd. pose proof (Hposall e He) as Hp.
      unfold e_disj, e_hi, e_lo, e_sz in *. cbn [fst snd] in Hd. rewrite Hnw in Hd. unfold hi', lo in *. lia.
    - apply eqb_false_spec in Et. apply bv_eqb_false_iff. intros E.
      pose proof (Hposall e He) as Hp. destruct (Hdisj0 e He Et) as [Hd|Hd];
        unfold e_hi, e_lo, e_sz in *; rewrite E in Hd; unfold hi', lo in *; lia. }
  assert (Hlohi : lo <= hi') by (unfold hi'; lia).
  assert (He0lo : e_lo (den rho e0) = lo /\ e_hi (den rho e0) = hi').
  { rewrite Hden0. unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite Hnw. split; reflexivity. }
  split; [exact HDI'|].
  split.
  { (* [comment removed for export] *)
    apply Z.leb_le in Hacct. unfold acct_ok in Hacct. cbn [L3' unmap_ledger3 fl_E fl_Ab] in Hacct.
    pose proof (li_disj_R _ _ _ _ _ Hli) as HdR.
    change (vm_maps (erase_vm wb0 (m_vmmaps m))) with (vm_maps (m_vmmaps m)) in HdR.
    assert (Hsub' : lazy_cov (drop_tag t (fl_all L3)) (fl_lazy L3)).
    { apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Hsub e He) as (Hpe & e' & He' & Hw).
      split; [exact Hpe|]. exists e'. split; [|exact Hw]. apply drop_tag_In'; [exact He'|].
      rewrite (proj1 Hw). exact (lazy_tag_free_sound t L3 e Hlz He). }
    assert (HE' : eager_used m' <= fl_E L3).
    { rewrite (Cnt.eager_used_eu m'), Fm, Fna, Flz. rewrite (Cnt.eager_used_eu m) in HE.
      assert (Hwfm : Cnt.ivs_wf (vm_maps (m_vmmaps m))).
      { apply Cnt.ivs_wf_Forall. eapply Forall_impl; [|exact Htopm]. intros q [_ Hq]. lia. }
      pose proof (Cnt.eu_unmap_le (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) (rho t) nw
                    Hwfm (proj2 (Cnt.ivs_wf_Forall _) Hwfna) (proj2 (Cnt.ivs_wf_Forall _) Hwflz) Hpw0 Hin0) as H1.
      cbv zeta in H1. rewrite Hnw in H1. fold lo hi' in H1. lia. }
    constructor; unfold FxDrive3.allowed; cbn [L3' unmap_ledger3 fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex].
    - destruct Hpi as [P1 P2 P3 P4]. constructor; rewrite ?Fmat.
      + apply List.NoDup_filter. exact P1.
      + apply Forall_forall. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) P2 p Hp).
      + apply Forall_forall. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) P3 p Hp).
      + rewrite Flim. unfold FxDrive3.allowed in HAb. clear - HE' HAb Hacct Hlim. lia.   (* [comment removed for export] *)
    - rewrite Flz. intros t' rg' pn p x Hg' Hpn Hp Hx Hxl Hlzp. destruct (Hother t' rg' Hg') as [_ Hg0'].
      apply (Hreg t' rg' pn p x Hg0' Hpn Hp Hx Hxl).
      exact (page_in_ranges_subtract _ _ lo hi' Hlohi Hhi64 Hlzp).
    - rewrite Flz. intros e p He Hp H1 H2. apply page_in_ranges_subtract_keep; [|exact (Hpw e p He Hp H1 H2)].
      destruct (Hcov_disj _ e Hsub He (lazy_tag_free_sound t L3 e Hlz He)) as [Hd|Hd]; [left | right]; lia.
    - unfold mat_lazy. rewrite Fmat, Flz. apply Forall_forall. intros p Hp.
      apply List.filter_In in Hp as [Hp Hout].
      apply page_in_ranges_subtract_keep; [|exact (proj1 (Forall_forall _ _) Hml p Hp)].
      unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout.
      destruct Hpi as [_ P2 _ _]. pose proof (proj1 (Forall_forall _ _) P2 p Hp) as Hpal.
      unfold page_aligned, page_size in Hpal.
      destruct Hout as [Hout|Hout]; [left; apply Z.leb_gt in Hout | right; apply Z.ltb_ge in Hout; exact Hout].
      clear - Hout Hpal Hlo_al. Z.div_mod_to_equations. lia.
    - exact Hsub'.
    - exact HAb.
    - rewrite Flim. exact Hlim.
    - exact Hmaps'.
    - rewrite Fna, Hexna, na_apply_snoc. unfold na_step. cbn [fst snd]. fold e0.
      rewrite (proj1 He0lo), (proj2 He0lo). reflexivity.
    - rewrite Flz, Hexlz, lz_apply_snoc. unfold lz_step. cbn [fst snd]. fold e0.
      rewrite (proj1 He0lo), (proj2 He0lo). reflexivity.
    - apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      apply drop_tag_In'; [exact (proj1 (Forall_forall _ _) H9a e He) | exact Htag].
    - apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      destruct (proj1 (Forall_forall _ _) H9b e He) as [Hm|[Hz|Hno]];
        [left; apply drop_tag_In'; assumption | right; left; exact Hz | right; right].
      change (f_mem (fx_unmap F t)) with (iremove t (f_mem F)). rewrite iget_iremove.
      destruct (fent_tag e =? t)%uint63; [reflexivity | exact Hno].
    - rewrite !Forall_app. split; [|split]; [| |exact Ht3].
      + apply Forall_forall; intros e He; apply drop_tag_In in He as [He _]. exact (proj1 (Forall_forall _ _) Ht1 e He).
      + rewrite map_app, Forall_app. split; [exact Ht2|]. constructor; [|constructor]. cbn [snd].
        exact (proj1 (Forall_forall _ _) Ht1 e0 He0all).
    - exact HE'.
    - exact Hacct.
    - rewrite Fna. apply Cnt.ivs_wf_Forall. apply Cnt.maps_subtract_wf; [apply Cnt.ivs_wf_Forall; exact Hwfna | exact Hlohi].
    - rewrite Flz. apply Cnt.ivs_wf_Forall. apply Cnt.maps_subtract_wf; [apply Cnt.ivs_wf_Forall; exact Hwflz | exact Hlohi].
    - intros o x p Ho Hp Hx. apply in_app_iff in Ho as [Ho | [<- | []]]; [exact (HopsR o x p Ho Hp Hx)|].
      cbn [snd] in Hx. fold e0 in Hx. rewrite (proj1 He0lo), (proj2 He0lo) in Hx.
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) HdR _ Hin0) p Hp) as Hd.
      unfold e_disj, e_hi, e_lo, e_sz in Hd. cbn [fst snd] in Hd. rewrite Hnw in Hd. fold lo hi' in Hd.
      unfold e_hi, e_lo, e_sz. lia.
    - (* [comment removed for export] *) exact Hord.
    - (* [comment removed for export] *)
      assert (Etop : alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m)).
      { pose proof Hne as Hne2. destruct Hne2 as [_ _ _ _ _ _ Hsp2 _ _ _ _].
        change (vm_init_sp (m_vmmaps (erase m'))) with (vm_init_sp (m_vmmaps m')) in Hsp2.
        change (vm_init_sp (m_vmmaps (erase m))) with (vm_init_sp (m_vmmaps m)) in Hsp2.
        unfold alloc_top. rewrite Hsp2. reflexivity. }
      rewrite Forall_app. split.
      + apply Forall_forall. intros o Ho.
        assert (Hto : to_Z (fent_tag (snd o)) < to_Z n)
          by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
        apply (op_ok_ext n rho rho m m' (fl_all L3) (drop_tag t (fl_all L3)) o (fun _ _ => eq_refl) Hto Ht1 Etop).
        * intros e' He' _. apply drop_tag_In in He' as [He' _]. exact He'.
        * exact (proj1 (Forall_forall _ _) Hopsf o Ho).
      + constructor; [|constructor]. unfold op_ok. cbn [fst snd]. cbv zeta. fold e0. split.
        * intros e' He' Hlt'. apply drop_tag_In in He' as [He' _].
          assert (Hneq' : e' <> e0) by (intros ->; unfold e0 in Hlt'; cbn [fent_tag fst] in Hlt'; lia).
          exact (pw_disj_map_In (den rho) _ e' e0 Hpwd He' He0all Hneq').
        * rewrite Etop, Hden0. exact (proj2 (proj1 (Forall_forall _ _) Htopm _ Hin0)).
    - (* [comment removed for export] *) exact Hres. }
  split.
  { (* [comment removed for export] *)
    destruct HS as [Hz Hcov Hsp Hexc].
    (* [comment removed for export] *)
    assert (Hmiss : forall x, in_span x -> ~ (lo <= x < hi')).
    { intros x Hx Hin. destruct (Hcov x Hx) as (e & He & Et & Hpx).
      assert (Htag : fent_tag e <> t) by (rewrite Et; intros E; apply Ht0; symmetry; exact E).
      destruct (Hdisj0 e He Htag); lia. }
    constructor; cbn [L3' unmap_ledger3 fl_all fl_ex].
    - intros x Hx Hno Hnex.
      assert (Hno0 : no_region rho (f_mem F) (bv_unsigned x)).
      { intros t' rg' Hg' Hin. destruct (Uint63.eqb t' t) eqn:E.
        - apply Uint63.eqb_spec in E. subst t'. rewrite Hgt in Hg'. injection Hg' as <-.
          apply (Hmiss _ (in_shadow_span _ Hx)). unfold in_ival in Hin. unfold hi', lo. lia.
        - apply eqb_false_spec in E. apply (Hno t' rg'); [|exact Hin].
          rewrite HM'. rewrite iget_iremove_other; [exact Hg'|]. intros E'. apply E. symmetry. exact E'. }
      destruct (Hz x Hx Hno0 Hnex) as [Z1 Z2]. unfold rview, wview in *. unfold ms'.
      rewrite sysret_mem, apply_unmaps_one, Hnw. fold lo hi'.
      replace ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi')) with false; [split; assumption|].
      symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply (Hmiss _ (in_shadow_span _ Hx)). lia.
    - intros x Hx. destruct (Hcov x Hx) as (e & He & Et & Hpx). exists e.
      split; [|split; assumption]. apply drop_tag_In'; [exact He|].
      rewrite Et. intros E. apply Ht0. symmetry. exact E.
    - intros t' rg' Hg'. destruct (Hother t' rg' Hg') as [Hne' Hg0'].
      pose proof (Hsp t' rg' Hg0') as Hok. unfold span_ok in *.
      destruct (rg_kind rg') as [|p] eqn:Ek; [exact Hok|].
      destruct Hok as (Et' & rgp & Hgp & Hrest). split; [exact Et'|]. exists rgp. split; [|exact Hrest].
      rewrite HM'. rewrite iget_iremove_other; [exact Hgp|]. intros E. subst p.
      unfold no_shadow_child in Hchild. rewrite <- Et', Hg0', Ek in Hchild. discriminate.
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Hexc e He) as (Hpe & e' & He' & Hw).
      split; [exact Hpe|]. exists e'. split; [|exact Hw]. apply drop_tag_In'; [exact He'|].
      rewrite (proj1 Hw). exact (ex_tag_free_sound t L3 e Hexf He). }
  exact (xpart_node _ _ _ _ _ _ _ _ _ _ _ _ HX Hne Fbrk).
Qed.

End Drive3N.

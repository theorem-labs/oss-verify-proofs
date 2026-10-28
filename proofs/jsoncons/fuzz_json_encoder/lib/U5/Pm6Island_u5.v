(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec SymStepR StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import IslInterp IslSound.
Import ListNotations. Import ISL.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISL0.
Import PML.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GUARD : Z := 0xfd280.           (* [comment removed for export] *)
Definition ABS_HI : Z := 0xfe000.
Definition FUEL : nat := 12100.

Definition KN0 : list (Z * abyte) :=
  [(NEED_LOCKS, BL 0); (LOCALE_LOCK, BL 0); (LOCALE_LOCK + 1, BL 0); (LOCALE_LOCK + 2, BL 0); (LOCALE_LOCK + 3, BL 0);
   (GUARD, BS 32 0 0); (GUARD + 1, BS 32 0 1); (GUARD + 2, BS 32 0 2); (GUARD + 3, BS 32 0 3);
   (GUARD + 4, BS 32 0 4); (GUARD + 5, BS 32 0 5); (GUARD + 6, BS 32 0 6); (GUARD + 7, BS 32 0 7)].
Definition C0 : ISL.cfg := CFG [RG 2 (- PMS.ISLAND_SCR) 0; RG 10 0 8] ABS_HI ll_prist_xsrc ((0x10000, IMG_RO_HI) :: ll_prist_xsrc) KN0 [].
Definition F0 (k : nat) : aval := if Nat.eqb k 4 then AL TP else AS k 0.
Definition S0 : ast := ST PC_LOCALE_CTOR (std_regs F0) (PositiveMap.empty _) [PositiveMap.empty _; PositiveMap.empty _] None.

Definition CSAVED : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition le_lit (n : nat) (v : Z) : list Z := map bv_unsigned (word_to_le_bytes n (Z_to_bv 64 v)).
Fixpoint zs_eqb (a b : list Z) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && zs_eqb a' b' | _, _ => false end.
Definition cell_is (C : ISL.cfg) (s : ast) (ad : aaddr) (n : nat) (v : Z) : bool :=
  match cell_lit RSEGS C s ad n with Some zs => zs_eqb zs (le_lit n v) | None => false end.

(* [comment removed for export] *)
Definition POST_ABS : list (Z * nat * Z) :=
  [(0xdba40, 1%nat, 1); (0xdba38, 8%nat, CLASSIC_IMP); (0xdb5c0, 1%nat, 0); (0xdb5c1, 1%nat, 0);
   (0xdb840, 1%nat, 0); (0xdb841, 1%nat, 0);      (* [comment removed for export] *)
   (NEED_LOCKS, 1%nat, 0); (LOCALE_LOCK, 4%nat, 0)].

(* [comment removed for export] *)
Definition res_chk (res : result) : bool :=
  match res with
  | RFin s v imm =>
      aval_eqb v (AS 1 0) && Z.eqb imm 0 && (match s_resv s with None => true | Some _ => false end) &&
      regs_same CSAVED (s_regs S0) (s_regs s) &&
      cell_is C0 s (ARg 1 0) 8 CLASSIC_IMP &&
      forallb (fun c => cell_is C0 s (AAbs (fst (fst c))) (snd (fst c)) (snd c)) POST_ABS
  | _ => false
  end.
Definition cert_chk : bool := res_chk (arun RSEGS C0 FUEL S0).

Lemma cert : cert_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Definition gbyte (M : mem) (a : Z) : byte :=
  match ISLS.rb RSEGS M (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Definition gbytes (M : mem) : list byte :=
  [gbyte M GUARD; gbyte M (GUARD + 1); gbyte M (GUARD + 2); gbyte M (GUARD + 3); gbyte M (GUARD + 4); gbyte M (GUARD + 5); gbyte M (GUARD + 6); gbyte M (GUARD + 7)].
Definition envE (R : bvmap 5 word) (M : mem) : nat -> word :=
  fun k => if (k <? 32)%nat then getr R (Z_to_bv 5 (Z.of_nat k)) else le_bytes_to_word (gbytes M).

(* [comment removed for export] *)
Definition guard_rom_chk : bool :=
  forallb (fun i => match seg_rom RSEGS (Z_to_bv 64 (GUARD + i)) with Some _ => true | None => false end) [0; 1; 2; 3; 4; 5; 6; 7].
Lemma guard_rom : guard_rom_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma gbyte_rb : forall M i, In i [0; 1; 2; 3; 4; 5; 6; 7] -> ISLS.rb RSEGS M (Z_to_bv 64 (GUARD + i)) = Some (gbyte M (GUARD + i)).
Proof.
  intros M i Hi. pose proof guard_rom as Hg. unfold guard_rom_chk in Hg. rewrite forallb_forall in Hg. specialize (Hg i Hi).
  unfold gbyte, ISLS.rb. destruct (M (Z_to_bv 64 (GUARD + i))); [reflexivity|].
  destruct (seg_rom RSEGS (Z_to_bv 64 (GUARD + i))); [reflexivity|discriminate].
Qed.

Lemma u8_rb : forall M a v, u8 M a v -> ISLS.rb RSEGS M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v H. unfold u8, L5.u8_at in H. cbn [rdn] in H. unfold ISLS.rb.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end); [|discriminate].
  injection H as ->. reflexivity.
Qed.

Lemma reg_of_nat : forall k (r : reg), bv_unsigned r = Z.of_nat k -> Z_to_bv 5 (Z.of_nat k) = r.
Proof. intros k r H. rewrite <- H. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Section Island.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.

Lemma init_ok0 : forall R M o sp r,
  entry L R M sp r PMS.ISLAND_SCR -> a0 R o -> ls_ok LS0 M -> obj_on_stack L sp o 8 -> L5.defined M o 8 ->
  ISLS.init_ok RSEGS C0 (envE R M) M.
Proof.
  intros R M o sp r (Hra & Hrok & Hsp & Htp & Hstk) Ha0 (Hro & (Hq1 & Hq2) & Hfoot & _) (Ho1 & Ho2 & Ho3) Hdo.
  destruct Hstk as (Hs16 & Hsfl & Hstop & Hwin & Hdef). unfold PMS.ISLAND_SCR in *.
  assert (HE2 : bv_unsigned (envE R M 2) = sp).
  { unfold envE. cbn [Nat.ltb Nat.leb]. rewrite (reg_of_nat 2 2%bv eq_refl), Hsp. apply ISLS.wz_small. lia. }
  assert (HE10 : bv_unsigned (envE R M 10) = o).
  { unfold envE. cbn [Nat.ltb Nat.leb]. unfold a0 in Ha0. rewrite (reg_of_nat 10 10%bv eq_refl), Ha0. apply ISLS.wz_small. lia. }
  constructor.
  - unfold C0, ABS_HI. cbn [c_abs_hi]. lia.
  - intros a ab Hin. cbn [c_kn0 C0 KN0] in Hin.
    assert (HG : ISLS.vden (envE R M) (AS 32 0) = le_bytes_to_word (gbytes M)) by (rewrite ISLS.vden_AS0; reflexivity).
    assert (HGB : word_to_le_bytes 8 (ISLS.vden (envE R M) (AS 32 0)) = gbytes M) by (rewrite HG; apply ISLS.le_roundtrip8; reflexivity).
    pose proof (ISLS.rdn_rb RSEGS M 4 LOCALE_LOCK _ Hq2) as H4.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
      try (cbn [ISLS.bden]; rewrite HGB; first [ rewrite <- (Z.add_0_r GUARD) at 1 | idtac ]; apply gbyte_rb; cbn; tauto).
    + apply u8_rb. exact Hq1.
    + rewrite <- (Z.add_0_r LOCALE_LOCK). apply (H4 0%nat). lia.
    + apply (H4 1%nat). lia.
    + apply (H4 2%nat). lia.
    + apply (H4 3%nat). lia.
  - intros a Hin. cbn [c_clear C0] in Hin. destruct (ISLS.in_ivs_true _ _ Hin) as (lo & hi & Hi & Hr).
    destruct Hi as [Hi|Hi]; [injection Hi as <- <-; apply Hro; exact Hr|].
    apply Hfoot. exists (lo, hi). split; [exact Hi | exact Hr].
  - intros a Hin. discriminate Hin.
  - intros j rg Hj. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; unfold ISLS.rbase; cbn [rg_k rg_lo rg_hi].
    + rewrite HE2. unfold C0, ABS_HI, PMS.ISLAND_SCR. cbn [c_abs_hi]. split; [lia|]. split; [lia|]. split.
      * rewrite (Z.div_mod sp 16) by lia. rewrite Hs16. replace (16 * (sp / 16) + 0) with ((2 * (sp / 16)) * 8) by lia. apply Z.mod_mul. lia.
      * intros off Hoff. replace (sp + off) with (sp - 4096 + (off + 4096)) by lia. apply Hdef. lia.
    + rewrite HE10. unfold C0, ABS_HI. cbn [c_abs_hi]. split; [lia|]. split; [lia|]. split; [exact Ho3|]. intros off Hoff. apply Hdo. lia.
  - intros j j' rg rg' Hj Hj' Hne. unfold ISLS.rbase.
    destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-;
    (destruct j' as [|[|j']]; cbn in Hj'; try (destruct j'; discriminate); injection Hj' as <-); try congruence;
    cbn [rg_k rg_lo rg_hi]; rewrite HE2, HE10; lia.
Qed.

(* [comment removed for export] *)
Lemma zs_eqb_eq : forall a b, zs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Lemma le_lit_bytes : forall n v, zbytes (le_lit n v) = word_to_le_bytes n (Z_to_bv 64 v).
Proof.
  intros n v. unfold zbytes, le_lit. rewrite map_map. induction (word_to_le_bytes n (Z_to_bv 64 v)) as [|b t IH]; [reflexivity|].
  cbn [map]. rewrite Z_to_bv_bv_unsigned, IH. reflexivity.
Qed.
Lemma cell_is_rdn : forall C E M0 s M ad n v, ISLS.msim C E M0 s M -> ISLS.init_ok RSEGS C E M0 -> cell_is C s ad n v = true ->
  rdn RSEGS M (ISLS.aden C E ad) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros C E M0 s M ad n v Hm IO H. unfold cell_is in H. destruct (cell_lit RSEGS C s ad n) as [zs|] eqn:Hc; [|discriminate].
  apply zs_eqb_eq in H. subst zs. rewrite (ISLS.cell_lit_sound RSEGS C E M0 IO s M ad n _ Hm Hc). rewrite le_lit_bytes. reflexivity.
Qed.
Lemma u8_of_le : forall M a v, 0 <= v < 256 -> rdn RSEGS M (Z_to_bv 64 a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 v)) -> u8 M a v.
Proof.
  intros M a v Hv H. unfold u8, L5.u8_at. rewrite H. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite ISLS.wz_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma envE_reg : forall R M k (rr : reg), (k < 32)%nat -> bv_unsigned rr = Z.of_nat k -> envE R M k = getr R rr.
Proof. intros R M k rr Hk Hr. unfold envE. destruct (Nat.ltb_spec k 32); [|lia]. rewrite (reg_of_nat k rr Hr). reflexivity. Qed.
Lemma entry_regs : forall R M pc a g v, getr R 4%bv = Z_to_bv 64 TP ->
  forall rr : reg, getr R rr = ISLS.vden (envE R M) (getreg (ST pc (std_regs F0) a g v) rr).
Proof.
  intros R M pc a g v Htp. apply ISLS.std_regs_ok. intros k Hk. unfold F0. destruct (Nat.eqb_spec k 4) as [->|Hne].
  - rewrite (reg_of_nat 4 4%bv eq_refl). exact Htp.
  - rewrite ISLS.vden_AS0. unfold envE. destruct (Nat.ltb_spec k 32); [reflexivity | lia].
Qed.
Lemma regs_pres : forall C E M S s' R R' M' rv',
  (forall rr : reg, getr R rr = ISLS.vden E (getreg S rr)) -> ISLS.sim C E M s' R' M' rv' ->
  regs_same CSAVED (s_regs S) (s_regs s') = true -> regs_preserved R R'.
Proof.
  intros C E M S s' R R' M' rv' Hreg0 Hsim' Hsame rr Hin.
  rewrite (ISLS.sm_regs _ _ _ _ _ _ _ Hsim' rr), (Hreg0 rr). unfold getreg. f_equal. symmetry.
  apply (ISLS.regs_same_sound CSAVED _ _ Hsame). unfold callee_saved_idx in Hin. unfold rnat, CSAVED.
  repeat (destruct Hin as [Hin|Hin]; [rewrite <- Hin; cbn; tauto|]). contradiction.
Qed.
(* [comment removed for export] *)
Lemma island_cps : forall (C : ISL.cfg) (S : ast) FU s' (fx : FPState) R M model K r E,
  arun RSEGS C FU S = RFin s' (AS 1 0) 0 -> s_resv s' = None ->
  ISLS.init_ok RSEGS C E M -> ISLS.sim C E M S R M None ->
  E 1%nat = Z_to_bv 64 r -> L5.ra_ok r -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall R' M', ISLS.sim C E M s' R' M' None -> srealizes RSEGS SCFG (@cfg fx R' r M' model) K) ->
  srealizes RSEGS SCFG (@cfg fx R (s_pc S) M model) K.
Proof.
  intros C S FU s' fx R M model K r E Hrun Hresv IO Hsim0 HE1 [Hr1 Hr2] Hh Hl Hcont.
  pose proof (@ISLS.arun_sound fx RSEGS C E M IO (seg_rom RSEGS) FU S R M None Hsim0) as Hs. rewrite Hrun in Hs.
  destruct Hs as (R' & M' & rv' & Hms & Hsim').
  assert (Hpc : v_jalr (ISLS.vden E (AS 1 0)) 0 = Z_to_bv 64 r).
  { rewrite ISLS.vden_AS0, HE1. unfold v_jalr, jalr_tgtZ. rewrite ISLS.wz_small by lia. rewrite Z.add_0_r, land_m2_even by exact Hr2. reflexivity. }
  assert (Hrv : rv' = None) by (rewrite (ISLS.sm_resv _ _ _ _ _ _ _ Hsim'), Hresv; reflexivity).
  rewrite Hpc, Hrv in Hms. rewrite !mkstR_None in Hms. rewrite Hrv in Hsim'.
  unfold cfg. eapply srz_msteps; [exact Hh | exact Hl | exact Hms |]. apply Hcont. exact Hsim'.
Qed.
Lemma res_chk_fin : forall res, res_chk res = true -> exists s', res = RFin s' (AS 1 0) 0 /\ s_resv s' = None /\
  regs_same CSAVED (s_regs S0) (s_regs s') = true /\ cell_is C0 s' (ARg 1 0) 8 CLASSIC_IMP = true /\
  forallb (fun c => cell_is C0 s' (AAbs (fst (fst c))) (snd (fst c)) (snd c)) POST_ABS = true.
Proof.
  intros [s' v imm|s'|c pc] Hc; try discriminate Hc. unfold res_chk in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hpost]. apply andb_true_iff in Hc. destruct Hc as [Hc Hobjc].
  apply andb_true_iff in Hc. destruct Hc as [Hc Hsame]. apply andb_true_iff in Hc. destruct Hc as [Hc Hresv].
  apply andb_true_iff in Hc. destruct Hc as [Hv Himm]. apply ISLS.aval_eqb_eq in Hv. apply Z.eqb_eq in Himm. subst v imm.
  exists s'. repeat split; try assumption. destruct (s_resv s'); [discriminate|reflexivity].
Qed.
Lemma obj_aden : forall C R M o, nth_error (c_rgs C) 1 = Some (RG 10 0 8) -> a0 R o -> 0 <= o < 2 ^ 64 ->
  ISLS.aden C (envE R M) (ARg 1 0) = Z_to_bv 64 o.
Proof.
  intros C R M o Hn Ha0 Ho. cbn [ISLS.aden]. rewrite Hn. unfold ISLS.rbase. cbn [rg_k]. rewrite (envE_reg R M 10 10%bv) by (reflexivity || lia).
  unfold a0 in Ha0. rewrite Ha0, ISLS.wz_small by lia. f_equal. lia.
Qed.

Theorem locale_ctor_first_ok : PMS.locale_ctor_first_spec L.
Proof.
  intros o sp r fx R M model K Hh Hl HK Hfp (Hent & Ha0 & Hls & Hobj & Hdo) Hcont.
  pose proof (init_ok0 R M o sp r Hent Ha0 Hls Hobj Hdo) as IO.
  destruct Hent as (Hra & Hrok & Hsp & Htp & Hstk).
  destruct Hstk as (Hs16 & Hsfl & Hstop & Hwin & Hdef). destruct Hobj as (Ho1 & Ho2 & Ho3). unfold PMS.ISLAND_SCR in *.
  pose proof (entry_regs R M PC_LOCALE_CTOR (PositiveMap.empty _) [PositiveMap.empty _; PositiveMap.empty _] None Htp) as Hreg0. fold S0 in Hreg0.
  assert (Hsim0 : ISLS.sim C0 (envE R M) M S0 R M None).
  { apply (ISLS.sim_init RSEGS C0 _ M IO); [exact Hreg0 | reflexivity | reflexivity | intros; apply PositiveMap.gempty | | reflexivity].
    intros j t Hj k. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; apply PositiveMap.gempty. }
  destruct (res_chk_fin (arun RSEGS C0 FUEL S0) cert) as (s' & Hrun & Hresv & Hsame & Hobjc & Hpost).
  change (Z_to_bv 64 PC_LOCALE_CTOR) with (Z_to_bv 64 (s_pc S0)).
  apply (island_cps C0 S0 FUEL s' fx R M model K r (envE R M) Hrun Hresv IO Hsim0); try assumption.
  intros R' M' Hsim'. clear Hrun. (* [comment removed for export] *)
  pose proof (ISLS.sm_mem _ _ _ _ _ _ _ Hsim') as Hm'.
  assert (HAT : atexit_cells M' []).      (* [comment removed for export] *)
  { destruct Hls as (_ & _ & _ & HAT0). apply (atexit_cells_agree M M' []); [|exact HAT0]. intros x Hx. unfold AX in Hx.
    apply (ISLS.msim_frame C0 _ M s' M' (Z_to_bv 64 x) Hm').
    + intros lo hi Hi Hr. rewrite ISLS.wz_small in Hr by lia. cbn in Hi. repeat (destruct Hi as [Hi|Hi]; [injection Hi as <- <-; lia|]). destruct Hi.
    + intros j rg Hj Hr. rewrite ISLS.wz_small in Hr by lia. unfold ISLS.rbase in Hr.
      destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; cbn [rg_k rg_lo rg_hi] in Hr.
      * rewrite (envE_reg R M 2 2%bv) in Hr by (reflexivity || lia). rewrite Hsp, ISLS.wz_small in Hr by lia. unfold PMS.ISLAND_SCR in Hr. lia.
      * rewrite (envE_reg R M 10 10%bv) in Hr by (reflexivity || lia). unfold a0 in Ha0. rewrite Ha0, ISLS.wz_small in Hr by lia. lia. }
  apply Hcont; [exact Hfp | | | |].
  - (* [comment removed for export] *)
    pose proof (cell_is_rdn C0 _ M s' M' (ARg 1 0) 8 CLASSIC_IMP Hm' IO Hobjc) as HOc.
    rewrite (obj_aden C0 R M o eq_refl Ha0) in HOc by lia.
    unfold POST_ABS in Hpost. cbn [forallb fst snd] in Hpost.
    repeat (apply andb_true_iff in Hpost; destruct Hpost as [?Hp Hpost]).
    repeat match goal with Hx : cell_is C0 s' (AAbs _) _ _ = true |- _ => apply (cell_is_rdn C0 _ M s' M' _ _ _ Hm' IO) in Hx; cbn [ISLS.aden] in Hx end.
    unfold errcat_guard, libc_quiet.
    repeat match goal with |- _ /\ _ => split end; first [ exact HOc | exact HAT | assumption | (apply u8_of_le; [lia | assumption]) ].
  - exact (regs_pres C0 _ M S0 s' R R' M' None Hreg0 Hsim' Hsame).
  - (* [comment removed for export] *)
    intros x Hout. apply (ISLS.msim_frame C0 _ M s' M' x Hm').
    + intros lo hi Hi Hr. apply (Hout (lo, hi - lo)); [right; right; apply (in_map (fun iv => (fst iv, snd iv - fst iv)) ll_prist_xsrc (lo, hi) Hi) | unfold L5.in_rng; cbn [fst snd]; lia].
    + intros j rg Hj Hr. unfold ISLS.rbase in Hr.
      destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; cbn [rg_k rg_lo rg_hi] in Hr.
      * rewrite (envE_reg R M 2 2%bv) in Hr by (reflexivity || lia). rewrite Hsp, ISLS.wz_small in Hr by lia. unfold PMS.ISLAND_SCR in Hr.
        apply (Hout (sp - 4096, 4096)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
      * rewrite (envE_reg R M 10 10%bv) in Hr by (reflexivity || lia). unfold a0 in Ha0. rewrite Ha0, ISLS.wz_small in Hr by lia.
        apply (Hout (o, 8)); [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - eapply ISLS.msim_grows; [exact (seg_rom RSEGS) | exact Hm'].
Qed.

(* [comment removed for export] *)
Definition KN1 : list (Z * abyte) :=
  (0xdba40, BL 1) :: combine [0xdba38; 0xdba38 + 1; 0xdba38 + 2; 0xdba38 + 3; 0xdba38 + 4; 0xdba38 + 5; 0xdba38 + 6; 0xdba38 + 7]
                         (map BL [80; 190; 13; 0; 0; 0; 0; 0]).
Definition C1 : ISL.cfg := CFG [RG 2 (-32) 0; RG 10 0 8] ABS_HI [] [] KN1 [].
Definition FUEL1 : nat := 40.
Definition res_chk1 (res : result) : bool :=
  match res with
  | RFin s v imm =>
      aval_eqb v (AS 1 0) && Z.eqb imm 0 && (match s_resv s with None => true | Some _ => false end) &&
      regs_same CSAVED (s_regs S0) (s_regs s) && cell_is C1 s (ARg 1 0) 8 CLASSIC_IMP &&
      (match PositiveMap.elements (s_abs s) with [] => true | _ => false end)
  | _ => false
  end.
Definition cert1_chk : bool := res_chk1 (arun RSEGS C1 FUEL1 S0).
Lemma cert1 : cert1_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ci_bytes : word_to_le_bytes 8 (Z_to_bv 64 CLASSIC_IMP) = zbytes [80; 190; 13; 0; 0; 0; 0; 0].
Proof. rewrite <- le_lit_bytes. f_equal. Qed.

Theorem locale_ctor_later_ok : PMS.locale_ctor_later_spec L.
Proof.
  intros o sp r fx R M model K Hh Hl HK Hfp (Hent & Ha0 & (Hg1 & Hg2) & _ & Hobj & Hdo) Hcont.
  destruct Hent as (Hra & Hrok & Hsp & Htp & Hstk).
  destruct Hstk as (Hs16 & Hsfl & Hstop & Hwin & Hdef). destruct Hobj as (Ho1 & Ho2 & Ho3).
  assert (HE2 : bv_unsigned (envE R M 2) = sp) by (rewrite (envE_reg R M 2 2%bv) by (reflexivity || lia); rewrite Hsp; apply ISLS.wz_small; lia).
  assert (HE10 : bv_unsigned (envE R M 10) = o) by (rewrite (envE_reg R M 10 10%bv) by (reflexivity || lia); unfold a0 in Ha0; rewrite Ha0; apply ISLS.wz_small; lia).
  assert (IO : ISLS.init_ok RSEGS C1 (envE R M) M).
  { constructor.
    - unfold C1, ABS_HI. cbn [c_abs_hi]. lia.
    - intros a ab Hin. cbn [c_kn0 C1 KN1 combine map] in Hin.
      pose proof (ISLS.rdn_rb RSEGS M 8 0xdba38 _ Hg2) as H8. rewrite ci_bytes in H8.
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply u8_rb; exact Hg1|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite <- (Z.add_0_r 0xdba38); apply (H8 0%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 1%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 2%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 3%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 4%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 5%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 6%nat); lia|].
      destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply (H8 7%nat); lia|]. contradiction.
    - intros a Hin. discriminate Hin.
    - intros a Hin. discriminate Hin.
    - intros j rg Hj. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; unfold ISLS.rbase; cbn [rg_k rg_lo rg_hi].
      + rewrite HE2. unfold C1, ABS_HI. cbn [c_abs_hi]. split; [lia|]. split; [lia|]. split.
        * rewrite (Z.div_mod sp 16) by lia. rewrite Hs16. replace (16 * (sp / 16) + 0) with ((2 * (sp / 16)) * 8) by lia. apply Z.mod_mul. lia.
        * intros off Hoff. replace (sp + off) with (sp - 32 + (off + 32)) by lia. apply Hdef. lia.
      + rewrite HE10. unfold C1, ABS_HI. cbn [c_abs_hi]. split; [lia|]. split; [lia|]. split; [exact Ho3|]. intros off Hoff. apply Hdo. lia.
    - intros j j' rg rg' Hj Hj' Hne. unfold ISLS.rbase.
      destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-;
      (destruct j' as [|[|j']]; cbn in Hj'; try (destruct j'; discriminate); injection Hj' as <-); try congruence;
      cbn [rg_k rg_lo rg_hi]; rewrite HE2, HE10; lia. }
  pose proof (entry_regs R M PC_LOCALE_CTOR (PositiveMap.empty _) [PositiveMap.empty _; PositiveMap.empty _] None Htp) as Hreg0. fold S0 in Hreg0.
  assert (Hsim0 : ISLS.sim C1 (envE R M) M S0 R M None).
  { apply (ISLS.sim_init RSEGS C1 _ M IO); [exact Hreg0 | reflexivity | reflexivity | intros; apply PositiveMap.gempty | | reflexivity].
    intros j t Hj k. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; apply PositiveMap.gempty. }
  pose proof cert1 as Hc. unfold cert1_chk in Hc.
  destruct (arun RSEGS C1 FUEL1 S0) as [s' v imm|s'|c pc] eqn:Hrun; try discriminate Hc. unfold res_chk1 in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hnoabs]. apply andb_true_iff in Hc. destruct Hc as [Hc Hobjc].
  apply andb_true_iff in Hc. destruct Hc as [Hc Hsame]. apply andb_true_iff in Hc. destruct Hc as [Hc Hresv].
  apply andb_true_iff in Hc. destruct Hc as [Hv Himm]. apply ISLS.aval_eqb_eq in Hv. apply Z.eqb_eq in Himm. subst v imm.
  assert (Hresv' : s_resv s' = None) by (destruct (s_resv s'); [discriminate|reflexivity]).
  change (Z_to_bv 64 PC_LOCALE_CTOR) with (Z_to_bv 64 (s_pc S0)).
  apply (island_cps C1 S0 FUEL1 s' fx R M model K r (envE R M) Hrun Hresv' IO Hsim0); try assumption.
  intros R' M' Hsim'. clear Hrun. (* [comment removed for export] *)
  pose proof (ISLS.sm_mem _ _ _ _ _ _ _ Hsim') as Hm'.
  apply Hcont; [exact Hfp | | | |].
  - pose proof (cell_is_rdn C1 _ M s' M' (ARg 1 0) 8 CLASSIC_IMP Hm' IO Hobjc) as HOc.
    rewrite (obj_aden C1 R M o eq_refl Ha0) in HOc by lia. exact HOc.
  - exact (regs_pres C1 _ M S0 s' R R' M' None Hreg0 Hsim' Hsame).
  - intros x Hout. apply (ISLS.msim_frame C1 _ M s' M' x Hm').
    + intros lo hi Hi. destruct Hi.
    + intros j rg Hj Hr. unfold ISLS.rbase in Hr.
      destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; cbn [rg_k rg_lo rg_hi] in Hr.
      * rewrite HE2 in Hr. apply (Hout (sp - 32, 32)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
      * rewrite HE10 in Hr. apply (Hout (o, 8)); [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - eapply ISLS.msim_grows; [exact (seg_rom RSEGS) | exact Hm'].
Qed.

End Island.
End ISL0.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import
  HRep HLib HRepFacts HStmts HCommon HFpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Export HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

Ltac nadd := repeat match goal with |- context [alu64 ALU_ADD (Z_to_bv 64 ?a) (Z_to_bv 64 ?k)] => first [rewrite (w_add a k) by lia | rewrite (w_addm a k) by lia] end.
Ltac nrw Hj := nadd; repeat match goal with |- context [?x + -1] => change (x + -1) with (x - 1) end;
               rewrite ?w_and, ?w_remu by lia; rewrite ?w_mul by lia; nadd; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r; rewrite ?Hj.

Section Blk.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC L MI.
    intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
  Qed.

  Lemma umap_foot_hb : forall {V : Type} NS obj bl bc (ents : list (Z * (Z * V))) a,
    umap_foot NS obj bl bc ents a ->
    (obj <= a < obj + 40) \/ exists b, In b (umap_blocks NS bl bc ents) /\ fst b <= a < fst b + snd b.
  Proof using.
    intros V NS obj bl bc ents a [Hh | [[Hbc Hb] | (p & Hp & Ha)]]; [left; exact Hh | right | right].
    - exists (bl, 8 * bc). split; [| cbn; lia]. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - exists (p, NS). split; [| cbn; lia]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff.
      apply in_map_iff in Hp. destruct Hp as (e & <- & He). exists e. split; [reflexivity | exact He].
  Qed.

  Lemma roomL_room_for : forall (A : AS MI) M model n,
    ainv MI A M model -> 0 <= n <= NMAX MI -> roomL MI A (live MI A) n -> room_for MI A n.
  Proof using AC L MI.
    intros A M model n AI Hn [HS HBG].
    destruct (Z.lt_ge_cases n (BIG MI)) as [Hs|Hb].
    - destruct (HS Hs) as [H1 H2]. eapply (room_small MI); [exact AI | lia | exact H1 | exact H2].
    - eapply (room_big MI); [exact AI | lia | apply HBG; lia].
  Qed.

  Lemma seg_rom_high : forall (x : word), 0x122000 <= bv_unsigned x -> seg_rom SEGS x = None.
  Proof using.
    intros x Hx. unfold seg_rom, memory_read.
    unfold SEGS, Plain.M.loaded_segments, Plain.Plain_loaded_segments.
    cbn [find_segment seg_base seg_size Plain.Plain_segment_000 Plain.Plain_segment_001 Plain.Plain_segment_002 Plain.Plain_segment_003].
    repeat (match goal with |- context [if ?c then _ else _] =>
              replace c with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; cbn; lia) end).
    reflexivity.
  Qed.
  Lemma rdn_defined_high : forall M n a bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs -> 0x122000 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    defined M a (Z.of_nat n).
  Proof using.
    intros M n. induction n as [|n IH]; intros a bs Hr Ha Han i Hi; [lia|].
    cbn [rdn] in Hr. destruct (M (Z_to_bv 64 a)) as [b|] eqn:HM.
    - destruct (Z.eq_dec i 0) as [->|Hnz]; [rewrite Z.add_0_r, HM; discriminate|].
      destruct (rdn SEGS M (Z_to_bv 64 a + 1) n) as [rest|] eqn:Hr'; [|discriminate Hr].
      rewrite SymExec3Sound.SX2S.w_add_1, u64_of_Z in Hr' by lia.
      replace (a + i) with ((a + 1) + (i - 1)) by lia. apply (IH (a + 1) rest Hr'); lia.
    - rewrite seg_rom_high in Hr; [discriminate Hr | rewrite u64_of_Z by lia; lia].
  Qed.
  Lemma cellw_high_defined : forall M a (w : N) v, cellw SEGS M a w v -> 0x122000 <= a -> a + Z.of_N w <= 2 ^ 64 ->
    defined M a (Z.of_N w).
  Proof using.
    intros M a w v [_ Hr] Ha Haw. rewrite <- N_nat_Z. eapply rdn_defined_high; [exact Hr | exact Ha | rewrite N_nat_Z; exact Haw].
  Qed.

  Lemma ro_clear_via_eff : forall (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    ro_clear L M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    ro_clear L M'.
  Proof using AC L MI HLimg_lo HLerr_rw.
    intros A A' M M' model W F RC AI EF HF HW.
    pose proof ceiling_lt as Hcl.
    eapply (ro_clear_frame L _ M M' RC (ef_frame _ _ _ _ _ _ _ _ _ EF)).
    intros a (Himg & Hnrw & Hnrel). pose proof (HLimg_lo _ Himg) as Hlt.
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - exact (Hnrw (HLerr_rw _ He)).
  Qed.

  Lemma apart_sub' : forall a k b m k' m', apart a k b m -> k' <= k /\ m' <= m -> apart a k' b m'.
  Proof using. unfold apart. intros. lia. Qed.
  Lemma apart_sym : forall a k b m, apart a k b m -> apart b m a k.
  Proof using. unfold apart. intros. lia. Qed.

  Lemma bseq_next_facts : forall bc, In bc BSEQ -> bc <> BSEQ_LAST ->
    In (bseq_next bc) BSEQ /\ bc < bseq_next bc /\ 8 * bseq_next bc <= 2 ^ 28
    /\ ((bc = 0 /\ bseq_next bc = 2) \/ (3 <= bseq_next bc /\ Z.land (bseq_next bc) (bseq_next bc - 1) <> 0)).
  Proof using.
    intros bc Hin Hlast. unfold BSEQ in Hin. unfold BSEQ_LAST in Hlast.
    repeat (destruct Hin as [<-|Hin];
      [ first [ exfalso; lia
              | match goal with |- context [bseq_next ?b] => let v := eval vm_compute in (bseq_next b) in change (bseq_next b) with v end;
                split; [inl | split; [lia | split; [lia | first [left; split; reflexivity | right; split; [lia | vm_compute; discriminate]]]]] ] |]).
    destruct Hin.
  Qed.

  Lemma nparg_not_pow2 : forall bc, In bc BSEQ -> bc <> 0 -> Z.land (2 * bc + 1) (2 * bc + 1 - 1) <> 0.
  Proof using.
    intros bc Hin Hnz. unfold BSEQ in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [exfalso; lia | vm_compute; discriminate] |]). destruct Hin.
  Qed.

  Lemma getr_other : forall R (r : reg) v r', r' <> r -> getr (regupd R r v) r' = getr R r'.
  Proof using. intros R r v r' Hne. unfold getr. rewrite regupd_other by exact Hne. reflexivity. Qed.

  Lemma accrue_no_flags : forall cs, accrue_csr cs no_flags = cs.
  Proof using.
    intros cs. unfold accrue_csr. change (fflags_bits no_flags) with 0. rewrite Z.lor_0_r. apply Z_to_bv_bv_unsigned.
  Qed.

  Lemma agree_block_via_eff : forall (A A' : AS MI) M M' model model' (W : Z * Z) (F : Z -> Prop) q m,
    eff MI A A' M M' W F -> ainv MI A M model -> ainv MI A' M' model' ->
    In (q, m) (live MI A) -> In (q, m) (live MI A') ->
    (forall a, q <= a < q + m -> ~ F a) -> alloc_ceiling <= fst W ->
    agree_on M M' q m.
  Proof using AC L MI HLrw_img HLerr_rw.
    intros A A' M M' model model' W F q m EF AI AI' Hl Hl' HF HW i Hi.
    pose proof ceiling_lt as Hcl.
    destruct (ai_live_block MI A M model q m AI Hl) as (_ & _ & Hq0 & Hqc & Hall).
    destruct (ai_live_block MI A' M' model' q m AI' Hl') as (_ & _ & _ & _ & Hall').
    destruct (Hall (q + i) ltac:(lia)) as (Ho & Hni & Hd). destruct (Hall' (q + i) ltac:(lia)) as (Ho' & _ & _).
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
    intros [H | [H | [H | [H | [H | H]]]]].
    - exact (Ho H). - exact (Ho' H). - destruct H as (_ & _ & Hn). exact (Hd Hn). - exact (HF (q + i) ltac:(lia) H).
    - unfold W_of in H. lia.
    - exact (Hni (HLrw_img _ (HLerr_rw _ H))).
  Qed.

  Lemma own_sx_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop),
    eff MI A A' M M' W F -> (forall a, owned MI A a -> ~ sx_region ST a) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) ->
    forall a, owned MI A' a -> ~ sx_region ST a.
  Proof using AC L MI ST HLrw_img.
    intros A A' M M' W0 F EF Hosx HF a Ho Hsx.
    pose proof (HLrw_img _ (sx_region_rw ST _ Hsx)) as Himg.
    destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho) as [Ho0 | [[Hni _] | Hf]];
      [exact (Hosx _ Ho0 Hsx) | exact (Hni Himg) | exact (HF _ Hf Himg)].
  Qed.

End Blk.

Lemma cell8_zeroed : forall M p (len : nat) i,
  0 <= p -> p + Z.of_nat len <= 2 ^ 64 -> 0 <= i -> 8 * i + 8 <= Z.of_nat len ->
  cell8 SEGS (wbytes M (Z_to_bv 64 p) (repeat (cbyte (Z_to_bv 64 0)) len)) (p + 8 * i) 0.
Proof.
  intros M p len i Hp Hpl Hi Hil. split; [cbn; lia|].
  transitivity (rdn SEGS (wbytes M (Z_to_bv 64 (p + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (p + 8 * i)) 8).
  - apply rdn_ext; [rewrite u64_of_Z by lia; cbn; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia. cbn in Hx.
    rewrite !wbytes_inside; rewrite ?repeat_length, ?length_N_to_le_bytes, ?u64_of_Z by lia; try (cbn; lia).
    rewrite nth_repeat_lt by lia.
    change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (cbyte (Z_to_bv 64 0)) 8). rewrite nth_repeat_lt by (cbn; lia). reflexivity.
  - change 8%nat with (length (word_to_le_bytes 8 (Z_to_bv 64 0))) at 2. apply rdn_wbytes_hit. rewrite length_N_to_le_bytes, u64_of_Z by lia. cbn. lia.
Qed.

Section Lnk.
Context {AC : AllocCeiling}.
  Context {V : Type}.
  #[local] Notation ent := (Z * (Z * V))%type.

  Definition hda (l : list ent) (t : Z) : Z := match l with [] => t | b :: _ => fst b end.
  Fixpoint lnk (M : mem) (Ls : list ent) (t : Z) : Prop :=
    match Ls with
    | [] => True
    | a :: Ls' => cell8 SEGS M (fst a) (hda Ls' t) /\ lnk M Ls' t
    end.
  Lemma lnk_chain : forall M Ls, chain SEGS M Ls <-> lnk M Ls 0.
  Proof using V.
    intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
    destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
  Qed.
  Lemma hd_app : forall (A B : list ent) t, hda (A ++ B) t = hda A (hda B t).
  Proof using V. intros [|a A] B t; reflexivity. Qed.
  Lemma hdaddr_hda : forall (A : list ent), hdaddr A = hda A 0.
  Proof using V. intros [|[a v] A]; reflexivity. Qed.
  Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
  Proof using V.
    intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
    rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
  Qed.
  Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (fst a) 8) ->
    (forall a, In a Ls -> 0 <= fst a /\ fst a + 8 <= 2 ^ 64) -> lnk M' Ls t.
  Proof using V.
    intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
    destruct HL as [Hc HL]. split.
    - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
    - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
  Qed.

  Definition lasta (t : Z) (l1 : list ent) : Z := last (map fst l1) t.
  Lemma lasta_snoc : forall t l1 y, lasta t (l1 ++ [y]) = fst y.
  Proof using V. intros t l1 y. unfold lasta. rewrite map_app. cbn. apply last_last. Qed.

  Lemma nodup_app_ne : forall (l1 l2 : list ent) b b',
    List.NoDup (map fst (l1 ++ l2)) -> In b l1 -> In b' l2 -> fst b <> fst b'.
  Proof using V.
    intros l1 l2 b b' Hnd H1 H2 Heq.
    revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
    cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
    destruct H1 as [<-|H1].
    - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
    - exact (IH Hnd' H1).
  Qed.
End Lnk.

Lemma nodup_app_ne_z : forall (l1 l2 : list Z) a b,
  List.NoDup (l1 ++ l2) -> In a l1 -> In b l2 -> a = b -> False.
Proof.
  intros l1 l2 a b Hnd H1 H2 Heq. subst b.
  revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
  cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
  destruct H1 as [<-|H1].
  - apply Hni. apply in_app_iff. right. exact H2.
  - exact (IH Hnd' H1).
Qed.

Ltac fp_flw MS Fx Dx Qrs Crd off znext :=
  eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
  [ norm_pc; eapply msteps_one; [reflexivity|];
    eapply fp_step_flw; [exact Fx | reflexivity | exact Dx | rewrite Qrs; change (bv_signed _) with off; apply v_addi_Z; lia | exact Crd]
  | cbn [fp_regs fp_csr]; rewrite flw_nan_box by lia; zpc znext ].

Ltac fp_fcvt_s_lu MS Fx Dx FZ Qrs n znext :=
  let md := fresh "md" in let Hst := fresh "Hst" in
  lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
    destruct (hp_step_fcvt_s_lu fx1 SEGS R _ M rom _ _ _ _ Fx eq_refl Dx FZ ltac:(right; reflexivity)) as [md Hst];
    cbv zeta in Hst; rewrite Qrs, (u64_of_Z n), (of_int_val md n) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst md; zpc znext ]
  end.

Ltac fp_fari MS Fx Dx FZ Ha Hb VAL znext :=
  let md := fresh "md" in let Hst := fresh "Hst" in
  lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
    destruct (hp_step_fari_s fx1 SEGS R _ M rom _ _ _ _ _ _ _ _ Fx eq_refl Dx FZ ltac:(right; reflexivity) Ha Hb ltac:(unfold one32; lia) ltac:(unfold one32; lia)) as [md Hst];
    cbv zeta in Hst; cbn [fari_op] in Hst; rewrite (VAL md) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst md; zpc znext ]
  end.

Ltac fp_flt MS Fx Dx Ha Hb a b znext :=
  let Hst := fresh "Hst" in
  lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
    pose proof (hp_step_fcmp_s fx1 SEGS R _ M rom _ _ _ _ _ _ _ Fx eq_refl Dx Ha Hb ltac:(lia) ltac:(lia)) as Hst;
    cbv zeta in Hst; cbn [fcmp_op] in Hst; rewrite (lt_val a b) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
    lazymatch type of Hst with context [bv_eqb ?r 0%bv] => replace (bv_eqb r 0%bv) with false in Hst by reflexivity end; cbv beta iota in Hst;
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst; zpc znext ]
  end.

Ltac fp_fcvt_lu_s MS Fx Dx FZ Ha n znext :=
  let md := fresh "md" in let Hmd := fresh "Hmd" in let Hst := fresh "Hst" in
  lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
    destruct (hp_step_fcvt_l_s fx1 SEGS R _ M rom _ false _ _ _ _ Fx eq_refl Dx FZ ltac:(left; vm_compute; discriminate) Ha ltac:(lia)) as (md & Hmd & Hst);
    cbv zeta in Hst; rewrite (to_lu_val md n) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
    lazymatch type of Hst with context [bv_eqb ?r 0%bv] => replace (bv_eqb r 0%bv) with false in Hst by reflexivity end; cbv beta iota in Hst;
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst Hmd md; zpc znext ]
  end.


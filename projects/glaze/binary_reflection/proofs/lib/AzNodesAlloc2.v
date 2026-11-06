(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.
Variable bcap ccap : Z.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis AINV_facts : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                    /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl).
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
(* [comment removed for export] *)
Hypothesis AINV_lazy : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, in_shc SHC (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, in_shv VSH (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (u a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV Lc Lf B C K M mdl').
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
(* [comment removed for export] *)
Hypothesis AINV_nolazy : forall Lc Lf B C K M mdl b n (a : word),
  AINV Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> b <= u a < b + n -> lz mdl a = false.
Hypothesis AINV_perm_nolazy : forall Lc Lf B C K M mdl (a : word),
  AINV Lc Lf B C K M mdl -> in_wins PERMc (u a) -> lz mdl a = false.
(* [comment removed for export] *)
Hypothesis AINV_top : forall Lc Lf B C K M mdl, AINV Lc Lf B C K M mdl -> CEIL_run <= SPTOPc.
(* [comment removed for export] *)
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
(* [comment removed for export] *)
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
(* [comment removed for export] *)
Hypothesis G_ro_lo_img : g_img_lo G <= g_ro_lo G.
(* [comment removed for export] *)
Hypothesis GKCAP_le : GKCAP <= KCAP.
Hypothesis FTOP_small : FTOPc <= 2 ^ 62.
(* [comment removed for export] *)
Hypothesis FPC_stop : forall M v lo, v <= lo -> FPC M v lo.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.
(* [comment removed for export] *)
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.   (* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis PERM_vsh : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_pshadow PERMc z -> in_shv VSH z = true \/ in_shc SHC z = true.
Hypothesis PERM_bnd : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_wins PERMc z -> z < two47.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation hid := (GPS.hid SHC VSH).
#[local] Notation Mr := (GPS.Mr SHC VSH).
#[local] Notation owned := (GPS.owned SWIN PERMc SPTOPc).
#[local] Notation frame_kept := (AzKnowLib.frame_kept SWIN PERMc SPTOPc G).
#[local] Notation shz := (AzKnowLib.shz G).


(* [comment removed for export] *)
Lemma lz_stack_false : forall Lc Lf B C K M mdl (a : word),
  AINV Lc Lf B C K M mdl -> CEIL_run <= u a -> lz mdl a = false.
Proof.
  intros Lc Lf B C K M mdl a HA Ha. destruct (lz mdl a) eqn:Hl; [|reflexivity]. exfalso.
  unfold lz, page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_facts _ _ _ _ _ _ _ HA) iv Hin) as (L0 & L1 & _).
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma lz_image_false : forall Lc Lf B C K M mdl (a : word),
  AINV Lc Lf B C K M mdl -> g_img_lo G <= u a < g_img_hi G -> lz mdl a = false.
Proof.
  intros Lc Lf B C K M mdl a HA Ha. destruct (lz mdl a) eqn:Hl; [|reflexivity]. exfalso.
  unfold lz, page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_facts _ _ _ _ _ _ _ HA) iv Hin) as (L0 & L1 & L2).
  rewrite A_img_hi, A_img_lo in L2. pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma hid_app_false : forall E cs mdl B C K M (a : word),
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  (in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a
   \/ in_wins SWIN (u a) \/ g_img_lo G <= u a < g_img_hi G) ->
  hid E cs mdl a = false.
Proof.
  intros E cs mdl B C K M a HA H. unfold GPS.hid.
  assert (LZ : lz mdl a = false).
  { destruct H as [Hb|[Hp|[Hs|[Hw|Hi]]]].
    - destruct Hb as (b & n & Hin & Hz). eapply AINV_nolazy; [exact HA | exact Hin | exact Hz].
    - eapply AINV_perm_nolazy; [exact HA | exact Hp].
    - eapply lz_stack_false; [exact HA | exact Hs].
    - destruct Hw as (lo & hi & Hin & Hz). pose proof (SWIN_img lo hi Hin). eapply lz_image_false; [exact HA | lia].
    - eapply lz_image_false; [exact HA | exact Hi]. }
  rewrite LZ. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hid_shadow_false : forall E cs mdl (a : word),
  (in_lshadow (blocks_den E (a_vis cs ++ a_fake cs)) (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a)) ->
  hid E cs mdl a = false.
Proof.
  intros E cs mdl a H. unfold GPS.hid. destruct (lz mdl a); [|reflexivity]. cbn [andb]. apply negb_false_iff.
  unfold vlz. destruct H as [Hl|[Hs|Hi]].
  - destruct Hl as (b & n & Hin & Hz). apply orb_true_intro. right.
    unfold in_shb. apply existsb_exists. unfold blocks_den in Hin. apply in_map_iff in Hin as [[eb en] [Heq Hin]].
    cbn in Heq. injection Heq as <- <-. exists (eb, en). split; [exact Hin|]. cbn [fst snd].
    destruct Hz as [Z1 Z2]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - apply orb_true_intro. left. apply orb_true_intro. left. apply SHC_stack. exact Hs.
  - apply orb_true_intro. left. apply orb_true_intro. left. apply SHC_image. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hid_pshadow_false : forall Lc Lf B C K M0 mdl0 E cs mdl (a : word),
  AINV Lc Lf B C K M0 mdl0 -> in_pshadow PERMc (u a) -> hid E cs mdl a = false.
Proof.
  intros Lc Lf B C K M0 mdl0 E cs mdl a HA H. unfold GPS.hid. destruct (lz mdl a); [|reflexivity]. cbn [andb]. apply negb_false_iff.
  unfold vlz. destruct (PERM_vsh _ _ _ _ _ _ _ _ HA H) as [Hv|Hc]; rewrite ?Hv, ?Hc; cbn; rewrite ?orb_true_r; reflexivity.
Qed.
Lemma Mr_pshadow : forall Lc Lf B C K M0 mdl0 E cs mdl M (a : word),
  AINV Lc Lf B C K M0 mdl0 -> in_pshadow PERMc (u a) -> Mr E cs mdl M a = M a.
Proof. intros. unfold GPS.Mr. apply mrestrict_visible. eapply hid_pshadow_false; eassumption. Qed.

(* [comment removed for export] *)
Lemma ghosts_ne_in : forall E M k gh g m,
  know_ok SEGS E M k -> wins_den E gh = PERMc ->
  In (g, m) (blocks_den E (ghosts_ne k gh)) -> In (g, g + m) PERMc /\ 1 <= m.
Proof.
  intros E M k gh g m HK Hperm Hin. unfold blocks_den, ghosts_ne in Hin. apply in_map_iff in Hin as [[g0 m0] [Heq Hin]].
  cbn [fst snd] in Heq. injection Heq as <- <-. apply filter_In in Hin as [Hin Hc]. cbn [snd] in Hc.
  destruct (xlo k m0) as [l|] eqn:Hl; [|discriminate]. apply Z.leb_le in Hc.
  pose proof (xlo_sound SEGS E M k m0 l HK Hl) as L. split; [|unfold uE; lia].
  rewrite <- Hperm. unfold wins_den. apply in_map_iff. exists (g0, m0). split; [reflexivity | exact Hin].
Qed.

Lemma pairs_vars_lt_filter : forall b f l, pairs_vars_lt b l = true -> pairs_vars_lt b (List.filter f l) = true.
Proof.
  intros b f l H. unfold pairs_vars_lt in *. apply forallb_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  exact (proj1 (forallb_forall _ _) H x Hx).
Qed.

(* [comment removed for export] *)
Lemma objs_ghost_ext : forall E M cs (X Y : list (expr * expr)) (P : Z * Z -> Prop),
  know_ok SEGS E M (kn cs) -> wins_den E (a_ghost cs) = PERMc ->
  (forall x, In x (blocks_den E (X ++ Y)) -> P x) ->
  forall x, In x (blocks_den E (X ++ Y ++ ghosts_ne (kn cs) (a_ghost cs))) -> P x \/ (In (fst x, fst x + snd x) PERMc /\ 1 <= snd x).
Proof.
  intros E M cs X Y P HK Hperm HP x Hx. rewrite app_assoc in Hx. rewrite AzNodesAlloc.blocks_den_app in Hx.
  apply in_app_iff in Hx as [Hx|Hx]; [left; exact (HP x Hx)|]. right. destruct x as [g m]. cbn [fst snd].
  exact (ghosts_ne_in E M (kn cs) (a_ghost cs) g m HK Hperm Hx).
Qed.

Lemma Mr_app : forall E cs mdl B C K M (a : word),
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  (in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a
   \/ in_wins SWIN (u a) \/ g_img_lo G <= u a < g_img_hi G) ->
  Mr E cs mdl M a = M a.
Proof. intros. unfold GPS.Mr. apply mrestrict_visible. eapply hid_app_false; eassumption. Qed.
Lemma Mr_shadow : forall E cs mdl M (a : word),
  (in_lshadow (blocks_den E (a_vis cs ++ a_fake cs)) (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a)) ->
  Mr E cs mdl M a = M a.
Proof. intros. unfold GPS.Mr. apply mrestrict_visible. apply hid_shadow_false. assumption. Qed.

(* [comment removed for export] *)
Lemma store_ok1_Mr : forall E cs mdl M (a : word),
  hid E cs mdl a = false -> RiscvSemantics.store_ok SEGS (Mr E cs mdl M) a 1 = RiscvSemantics.store_ok SEGS M a 1.
Proof.
  intros E cs mdl M a Hh. unfold GPS.Mr. cbn [RiscvSemantics.store_ok]. unfold wview, mrestrict. rewrite Hh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_ok_defined : forall M (a : word),
  ~ (g_img_lo G <= u a < g_img_hi G) -> RiscvSemantics.store_ok SEGS M a 1 = true -> M a <> None.
Proof.
  intros M a Ha Hs Hn. cbn [RiscvSemantics.store_ok] in Hs. unfold wview in Hs. rewrite Hn in Hs.
  rewrite (SEGS_out a Ha) in Hs. discriminate Hs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_den_cons : forall E p l, blocks_den E (p :: l) = (uE E (fst p), uE E (snd p)) :: blocks_den E l.
Proof. intros E [b n] l. reflexivity. Qed.

Lemma in_blocks_weaken : forall L L' z, (forall x, In x L -> In x L') -> in_blocks L z -> in_blocks L' z.
Proof. intros L L' z Hs (b & n & Hin & Hz). exists b, n. split; [apply Hs; exact Hin | exact Hz]. Qed.
Lemma in_blocks_app2 : forall L1 L2 z, in_blocks (L1 ++ L2) z -> in_blocks L1 z \/ in_blocks L2 z.
Proof.
  intros L1 L2 z (b & n & Hin & Hz). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists b, n; split; assumption.
Qed.

(* [comment removed for export] *)
Lemma uE_eadd_nowrap : forall E a b, uE E a + uE E b < 2 ^ 64 -> uE E (eadd a b) = uE E a + uE E b.
Proof.
  intros E a b H. unfold uE, eadd in *. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
  pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)). apply u64_lit. lia.
Qed.
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. intros. unfold uE. cbn [edenot]. apply u64_lit. lia. Qed.
Lemma wend_sound : forall E M k g e, know_ok SEGS E M k -> wend k g = Some e -> uE E (fst g) + uE E (snd g) <= e.
Proof.
  intros E M k [g m] e HK H. unfold wend in H. cbn [fst snd] in *.
  destruct (xhi k g) as [h|] eqn:Hh; [|discriminate]. destruct (xhi k m) as [mm|] eqn:Hm; [|discriminate].
  destruct (Z.ltb_spec (h + mm) two64) as [LT|GE]; [|discriminate].
  pose proof (xhi_sound SEGS E M k g h HK Hh) as B1. pose proof (xhi_sound SEGS E M k m mm HK Hm) as B2. unfold two64 in LT.
  destruct (xhi k (eadd g m)) as [j|] eqn:Hj; injection H as <-; [|unfold uE in *; lia].
  pose proof (xhi_sound SEGS E M k _ j HK Hj) as B3. pose proof (uE_eadd_nowrap E g m ltac:(unfold uE in *; lia)) as EQ. unfold uE in *. rewrite EQ in B3. lia.
Qed.

(* [comment removed for export] *)
Lemma ghosts_lo_arm_sound : forall E M k fl top bud (g : expr * expr) gb gk e l,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> CEIL_run <= sptop_den E top ->
  split_lit (fst g) = (gb, gk) -> wend k g = Some e -> xlo k (snd g) = Some l -> 1 <= l ->
  bflat_x k gb gk (snd g) = true ->
  (Z.leb e CEIL
   || (let '(fw, fwl) := floor_winI fl top bud in
       stack_x k fl top bud top && Z.ltb bud two47 && Z.leb e two47 && ranges_apart_x k gb gk (snd g) (a_base fw) (a_off fw) fwl))%bool = true ->
  u (edenot E gb) + gk + uE E (snd g) <= sptop_den E top.
Proof.
  intros E M k fl top bud g gb gk e l HK Hfl Htop Hgs He Hl Hl1 Hbf H.
  pose proof (wend_sound E M k g e HK He) as WE.
  assert (Hu : uE E (fst g) = u (edenot E gb) + gk).
  { destruct (bflat_x_sound SEGS E _ k gb gk (snd g) HK Hbf) as (F1 & F2 & F3). rewrite estart_SA in F1, F2, F3.
    unfold uE. rewrite (split_lit_denot E (fst g) gb gk Hgs). apply u64_lit. lia. }
  rewrite Hu in WE. pose proof GlzConst.ceil_lo as CL.
  apply orb_prop in H as [H|H].
  - apply Z.leb_le in H. unfold CEIL in H. lia.
  - destruct (floor_winI fl top bud) as [[fwb fwo] fwl] eqn:Hfw. cbn [a_base a_off] in H.
    apply andb_prop in H as [H Hap]. apply andb_prop in H as [H He47]. apply andb_prop in H as [Hst Hbud].
    apply Z.ltb_lt in Hbud. apply Z.leb_le in He47.
    pose proof (xlo_sound SEGS E M k (snd g) l HK Hl) as XL.
    unfold stack_x in Hst. apply andb_prop in Hst as [Htok Hlin].
    destruct (floor_term fl top bud) as [fb fo] eqn:Hft.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK Hlin) as L0. cbn [xt_den] in L0.
    destruct (split_lit top) as [tb tk] eqn:Hsp.
    destruct (AzKnowLib.top_ok_sound SEGS E M k fl top bud tb tk HK Htok Hsp) as (TOPEQ & Hb0 & TOPR & TOPN).
    assert (Htu : uE E top = u (edenot E tb) + tk) by (unfold uE; rewrite (split_lit_denot E top tb tk Hsp); apply u64_lit; lia).
    (* [comment removed for export] *)
    assert (FW : u (edenot E fwb) + fwo = u (edenot E fb) + fo /\ fwl = ELit (bud + WSTK)).
    { unfold floor_winI in Hfw. unfold floor_term in Hft. destruct fl as [f|].
      - injection Hfw as <- <- <-. injection Hft as <- <-. split; reflexivity.
      - rewrite Hsp in Hfw, Hft. injection Hfw as <- <- <-. injection Hft as <- <-. split; reflexivity. }
    destruct FW as [FW ->].
    pose proof (AzKnowLib.floor_term_sound SEGS E M k fl top bud fb fo HK Htok Hfl Hft) as FL.
    pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK Hap) as D. rewrite !estart_SA in D. cbn [a_base a_off] in D.
    rewrite (AzAPS.APS.elenZ_lit E (bud + WSTK)) in D by (unfold WSTK, GlzConst.WSTK, two47 in *; lia).
    rewrite TOPEQ. unfold elenZ, uE, WSTK, GlzConst.WSTK, two47 in *.
    destruct D as [D|D]; [lia|]. exfalso. clear - D FL FW XL Hl1 WE He47 Hb0 CL. lia.
Qed.

Lemma uE_eaddz : forall E a z, 0 <= uE E a + z < 2 ^ 64 -> uE E (eaddz a z) = uE E a + z.
Proof.
  intros E a z H. unfold uE, eaddz in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_one_M : forall M (a : word) bt,
  rdn SEGS M a 1 = Some [bt] -> in_hull A (u a) = false -> M a = Some bt.
Proof.
  intros M a bt H Hh.
  change (rdn SEGS M a 1) with
    (match (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) with
     | Some b0 => match rdn SEGS M (a + 1) 0 with Some rest => Some (b0 :: rest) | None => None end
     | None => None end) in H.
  destruct (M a) as [b0|] eqn:HM.
  - cbn [rdn] in H. injection H as ->. reflexivity.
  - rewrite (APS.seg_rom_off_hull SEGS A SEGS_in_hull a Hh) in H. discriminate H.
Qed.

Lemma kshok_sym_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> kshok_sym_x k b off n = true -> kentry_ok SEGS E M (KShOk (SA b off) n).
Proof.
  intros E M k b off n HK H. unfold kshok_sym_x in H. destruct n as [nn| | | | | | |]; try discriminate H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.leb_le in H. apply Z.leb_le in X4. apply Z.ltb_lt in X3. apply Z.leb_le in X2.
  destruct (xhi k (eaddz b off)) as [hi|] eqn:Hhi; [|discriminate X0]. apply Z.leb_le in X0.
  pose proof (ealign3_mod8 SEGS E M k b HK H) as Hb8. unfold uE in Hb8.
  destruct (bflat_x_sound SEGS E M k b off (ELit nn) HK X1) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
  cbn [edenot] in B2. rewrite (u_small nn) in B2 by lia.
  pose proof (xhi_sound SEGS E M k (eaddz b off) hi HK Hhi) as Hi.
  assert (EA : u (edenot E (eaddz b off)) = u (edenot E b) + off) by (unfold uE; apply (uE_eaddz E b off); unfold uE; lia).
  unfold uE in EA. rewrite EA in Hi.
  set (ub := u (edenot E b)) in *.
  pose proof (u64_range (edenot E b)) as UB. fold ub in UB.
  cbn [kentry_ok]. rewrite estart_SA. fold ub. unfold elenZ. cbn [edenot]. rewrite (u_small nn) by lia.
  split; [unfold flat; rewrite estart_SA; fold ub; lia|]. split; [unfold two47 in *; lia|].
  intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
  set (j := z / 8 - ub / 8).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Hj : off / 8 <= j <= (off + nn - 1) / 8) by (unfold j; clear - Hz Hb8 X4 X3 UB; split; nia).
  assert (SBz : SB + z / 8 = ub / 8 + (SB + j)) by (unfold j; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (IN : In j (map (fun i => off / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((off + nn - 1) / 8 - off / 8 + 1))))).
  { apply in_map_iff. exists (Z.to_nat (j - off / 8)). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) X j IN) as SZ. unfold shb_zero1 in SZ. apply existsb_exists in SZ as [K [HinK HK1]].
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as KOK.
  assert (ESH : forall o, estart E (SA (shb b) o) = ub / 8 + o).
  { intros o. rewrite estart_SA. rewrite (srl3_base_denot E (shb b) b eq_refl). fold ub. reflexivity. }
  assert (NH : in_hull A (SB + z / 8) = false).
  { unfold APS.in_hull. rewrite A_img_hi, A_img_lo. pose proof G_img_shlo as GS. unfold SHMAPLO in GS. apply Bool.andb_false_iff. right. apply Z.ltb_ge.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (0 <= z / 8) by (apply Z.div_pos; lia). unfold SB. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (ZR : 0 <= SB + z / 8 < 2 ^ 64).
  { split; [pose proof (Z.div_pos z 8); unfold SB; lia|].
    assert (z / 8 <= z) by (apply Z.div_le_upper_bound; lia). unfold two47, SB in *. lia. }
  destruct K as [[kb ko] w vv|[kb ko] zn|[kb ko] zn kb2|ilo ihi|e m|e rlo rhi|[kb ko] zn|a1 n1 a2 n2|[kb ko] zn fc|[kb ko] zn|[kb ko] zn|fv flo fd];
    try discriminate HK1.
  - (* [comment removed for export] *)
    destruct w as [|[|w]]; try discriminate HK1. destruct vv as [vz| | | | | | |]; try discriminate HK1. destruct vz; try discriminate HK1.
    apply andb_prop in HK1 as [E1 E2]. apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. subst kb ko.
    cbn [kentry_ok] in KOK. destruct KOK as (_ & Hfl & Hrd).
    assert (AD : adenot E (SA (shb b) (SB + j)) = Z_to_bv 64 (SB + z / 8)).
    { apply bv_eq. rewrite (flat_u E _ _ Hfl). rewrite ESH. rewrite (u_small (SB + z / 8)) by exact ZR. lia. }
    rewrite AD in Hrd. cbn [word_to_le_bytes edenot] in Hrd.
    apply (rdn_one_M M (Z_to_bv 64 (SB + z / 8))); [|rewrite (u_small (SB + z / 8)) by exact ZR; exact NH].
    rewrite Hrd. cbn. rewrite Z_to_bv_unsigned. reflexivity.
  - (* [comment removed for export] *)
    destruct zn as [zl| | | | | | |]; try discriminate HK1.
    apply andb_prop in HK1 as [E1 E4]. apply andb_prop in E1 as [E1 E3]. apply andb_prop in E1 as [E1 E2].
    apply expr_eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply Z.ltb_lt in E4. subst kb.
    cbn [kentry_ok] in KOK. destruct KOK as [Hfl Hz0]. rewrite ESH in Hz0. unfold elenZ in Hz0. cbn [edenot] in Hz0.
    assert (ZL0 : 0 <= zl) by lia.
    rewrite (u_small zl) in Hz0 by (unfold two47 in E4; lia).
    replace (SB + z / 8) with (ub / 8 + ko + (SB + j - ko)) by lia.
    apply Hz0. lia.
Qed.

Lemma kshok_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> kshok_x k b off n = true -> kentry_ok SEGS E M (KShOk (SA b off) n).
Proof.
  intros E M k b off n HK H. unfold kshok_x in H. apply orb_prop in H as [H|Hsym]; [|exact (kshok_sym_x_sound E M k b off n HK Hsym)].
  apply orb_prop in H as [H|H]; [exact (kshok_entailed_sound SEGS E M k k b off n HK HK H)|].
  unfold kshok_zero_x in H.
  destruct (xlo k (eaddz b off)) as [lo|] eqn:Hlo; [|discriminate]. destruct (xhi k (eaddz b off)) as [hi|] eqn:Hhi; [|discriminate].
  destruct (xhi k n) as [nhi|] eqn:Hnhi; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.leb_le in H. apply Z.leb_le in X1. rename X0 into Hbf. rename X into Hkz.
  destruct (bflat_x_sound SEGS E M k b off n HK Hbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
  pose proof (xlo_sound SEGS E M k (eaddz b off) lo HK Hlo) as Lo. pose proof (xhi_sound SEGS E M k (eaddz b off) hi HK Hhi) as Hi.
  pose proof (xhi_sound SEGS E M k n nhi HK Hnhi) as Nhi. pose proof (u64_range (edenot E n)) as NR.
  assert (EA : u (edenot E (eaddz b off)) = u (edenot E b) + off) by (unfold uE; apply (uE_eaddz E b off); unfold uE; lia).
  unfold uE in EA. rewrite EA in Lo, Hi.
  destruct (kzero_x_sound0 SEGS E M k k (ELit 0) (SB + lo / 8) (ELit ((hi + nhi + 7) / 8 - lo / 8)) HK HK Hkz) as (KZ & _ & _).
  rewrite estart_SA in KZ. cbn [edenot] in KZ. rewrite u_lit0 in KZ.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (CNT : 0 <= (hi + nhi + 7) / 8 - lo / 8 < 2 ^ 64) by (unfold two47 in *; lia).
  rewrite (APS.elenZ_lit E ((hi + nhi + 7) / 8 - lo / 8)) in KZ by lia.
  cbn [kentry_ok]. rewrite estart_SA. unfold elenZ. split; [|split].
  - unfold flat. rewrite estart_SA. lia.
  - unfold two47 in *. lia.
  - intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
    replace (SB + z / 8) with (0 + (SB + lo / 8) + (z / 8 - lo / 8)) by lia.
    apply KZ. unfold two47 in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma fpc_Mr_full : forall E cs mdl M v lo d,
  AX2S.fpc (Mr E cs mdl M) v lo d -> AX2S.fpc M v lo d.
Proof.
  intros E cs mdl M v lo d H. eapply AX2S.fpc_defmono; [exact H|].
  intros a Ha. unfold GPS.Mr, mrestrict in *. destruct (GPS.hid SHC VSH E cs mdl (Z_to_bv 64 a)); [exfalso; apply Ha; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma kn_readable_x_sound2 : forall E M k sb sk ne,
  know_ok SEGS E M k -> kn_readable_x k sb sk ne = true ->
  0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E ne <= 2 ^ 64
  /\ forall i, 0 <= i < elenZ E ne -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None.
Proof.
  intros E M k sb sk ne HK H. unfold kn_readable_x in H. apply existsb_exists in H as [K [HinK HKt]].
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  pose proof (u64_range (edenot E ne)) as Hne. unfold elenZ in *.
  assert (GEN : forall kb kk len (P : option byte -> Prop),
            xinside k sb sk ne kb kk len = true ->
            flat E (SA kb kk) (bv_unsigned (edenot E len)) ->
            (forall i, 0 <= i < bv_unsigned (edenot E len) -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
            (forall x, P x -> x <> None) ->
            0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + bv_unsigned (edenot E ne) <= 2 ^ 64
            /\ forall i, 0 <= i < bv_unsigned (edenot E ne) -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None).
  { intros kb kk len P Hx Hfl HP HPn.
    destruct (xinside_sound SEGS E M k sb sk ne kb kk len HK Hx) as [X1 X2]. unfold elenZ in X2.
    destruct Hfl as (F1 & F2 & F3 & F4).
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (estart E (SA sb sk) + i) with (estart E (SA kb kk) + (estart E (SA sb sk) - estart E (SA kb kk) + i)) by lia.
    apply HPn. apply HP. lia. }
  destruct K as [|[kb kk] len|[kb kk] len j| | | | | |[kb kk] len c|[kb kk] len | [kb kk] len | fv flo fd]; try discriminate; cbn [kentry_ok] in HKK; unfold elenZ in HKK.   (* [comment removed for export] *)
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as (Hfl & Hl & Hz). eapply (GEN kb kk len (fun x => exists b, x = Some b)); [exact HKt | exact Hfl | | intros x [b ->]; discriminate].
    intros i Hi. eexists. apply Hz. exact Hi.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 c))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x <> None)); [exact HKt | exact Hfl | exact Hz | intros x Hx; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_bytes : forall M n (a : word) bs,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn SEGS M a n = Some bs -> (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros M n a bs Hnw Hrd Hdef j Hj.
  pose proof (rdn_nth SEGS M n a bs j Hnw Hrd Hj) as H1. cbn [rdn] in H1.
  destruct (M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) as [b|] eqn:Hb.
  - injection H1 as <-. reflexivity.
  - exfalso. exact (Hdef (Z.of_nat j) ltac:(lia) Hb).
Qed.

(* [comment removed for export] *)
Lemma kfpc_frame_ok_sound : forall E M k v lo w,
  know_ok SEGS E M k -> kfpc_frame_ok SEGS k v lo = Some w ->
  uE E lo + 16 <= uE E v /\ uE E v mod 8 = 0 /\ uE E v < AX2S.FPC_HI
  /\ AX2S.defined M (uE E v - 16) (uE E v) /\ AX2S.m64 M (uE E v - 16) (uE E w).
Proof.
  intros E M k v lo w HK H. unfold kfpc_frame_ok in H.
  lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK Hc) as L16. cbn [xt_den] in L16.
  apply Z.leb_le in X1. pose proof (GPS.ealign3_mod8 SEGS E M k v HK X1) as V8. unfold uE in V8.
  destruct (xhi k v) as [h|] eqn:Hxh; [|discriminate]. apply Z.ltb_lt in X0. unfold two47 in X0. pose proof (xhi_sound SEGS E M k v h HK Hxh) as VH.
  destruct (kn_readable_x_sound2 E M k v (-16) (ELit 16) HK X) as (R1 & R2 & R3). rewrite estart_SA in R1, R2, R3.
  rewrite (APS.elenZ_lit E 16) in R2, R3 by lia.
  destruct (know_lookup SEGS k v (-16) 8 false [] []) as [w' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  destruct (lookup_piece SEGS E M k v (-16) 8 w hs HK ltac:(lia) HL) as (bs & Hrd & Hlen & Hbs).
  { unfold flat. rewrite estart_SA. change (Z.of_nat 8) with 8. lia. }
  rewrite estart_SA in Hrd. pose proof (u64_range (edenot E v)) as VR. pose proof (u64_range (edenot E w)) as WR. unfold uE in *.
  split; [lia|]. split; [exact V8|]. split; [unfold AX2S.FPC_HI; lia|]. split.
  - intros i Hi. replace i with (bv_unsigned (edenot E v) + -16 + (i - (bv_unsigned (edenot E v) - 16))) by lia. apply R3. lia.
  - exists bs. split; [|split; [exact Hlen|]].
    + intros i Hi. replace (bv_unsigned (edenot E v) - 16 + Z.of_nat i) with (bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E v) + -16)) + Z.of_nat i)
        by (rewrite u64_lit by lia; lia).
      apply (rdn_overlay_bytes M 8 _ bs); [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia | exact Hrd | | exact Hi].
      intros j Hj. rewrite u64_lit by lia. apply R3. change (Z.of_nat 8) with 8 in Hj. lia.
    + rewrite <- Hbs. unfold word_to_le_bytes. rewrite bytes_le_to_Z_of_le_bytes by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma kfpc_lower : forall M v lo lo' d,
  AX2S.fpc M v lo' d -> AX2S.kfpc_robust v lo' -> lo <= lo' -> AX2S.FPC_CEIL <= lo ->
  AX2S.fpc M v lo d /\ AX2S.kfpc_robust v lo.
Proof.
  intros M v lo lo' d HF HR Hle Hc. unfold AX2S.kfpc_robust in *. split; [|lia].
  destruct HR as [FR|ST].
  - destruct HF as [v0 lo0 d0 ST0 | v0 lo0 d0 w H16 H8 HH DEF RD CH].
    + apply AX2S.fpc_stop. lia.
    + apply (AX2S.fpc_frame M v0 lo d0 w); try assumption. lia.
  - apply AX2S.fpc_stop. lia.
Qed.

Lemma kfpc_entailed_sound : forall fact E M k fl top bud v lo d,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud ->
  kfpc_entailed SEGS fact k fl top bud v lo d = true ->
  AX2S.fpc M (uE E v) (uE E lo) d /\ (fact = true -> AX2S.kfpc_robust (uE E v) (uE E lo)).
Proof.
  intros fact E M k fl top bud v lo d HK Hfl H. unfold kfpc_entailed in H. apply orb_prop in H as [H|Hua].
  2:{ (* [comment removed for export] *)
    destruct (split_lit v) as [vb vc] eqn:Hsv. apply andb_prop in Hua as [Hal Hnz]. apply Z.leb_le in Hal.
    apply negb_true_iff in Hnz. apply Z.eqb_neq in Hnz.
    pose proof (AX2S.ealign_sound SEGS E M k vb HK) as [[_ A64] [q Hq]].
    pose proof (split_lit_denot E v vb vc Hsv) as Hd.
    assert (Hm : uE E v mod 8 <> 0).
    { unfold uE. rewrite Hd. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64).
      assert (P8 : 2 ^ ealign k vb = 8 * 2 ^ (ealign k vb - 3)).
      { replace (ealign k vb) with (3 + (ealign k vb - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
      set (t := (bv_unsigned (edenot E vb) + vc) / 2 ^ 64).
      assert (EQ : (bv_unsigned (edenot E vb) + vc) mod 2 ^ 64 = vc + (q * 2 ^ (ealign k vb - 3) - 2 ^ 61 * t) * 8).
      { rewrite Z.mod_eq by lia. fold t. rewrite Hq, P8. change (2 ^ 64) with (2 ^ 61 * 8). ring. }
      rewrite EQ, Z_mod_plus_full. exact Hnz. }
    split; [apply AX2S.fpc_stop; right; left; exact Hm | intros _; unfold AX2S.kfpc_robust; right; right; left; exact Hm]. }
  apply orb_prop in H as [H|Hfr]; [apply orb_prop in H as [H|H]; [apply orb_prop in H as [Hs|Hb]|]|].
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hs Hf]. pose proof (lin_ge0_sound SEGS E M k _ _ HK Hs) as L. cbn [xt_den] in L.
    split; [apply AX2S.fpc_stop; left; unfold uE; lia|]. intros ->. cbn [negb orb] in Hf.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK Hf) as L2. cbn [xt_den edenot] in L2.
    rewrite u64_lit in L2 by (unfold CEIL; lia). unfold AX2S.kfpc_robust, AX2S.FPC_CEIL, CEIL, uE in *. lia.
  - (* [comment removed for export] *)
    apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hvh]. apply andb_prop in Hb as [Hb Hbud]. apply andb_prop in Hb as [Hf Hst].
    destruct fact; [discriminate|]. split; [|intros X; discriminate X].
    apply Z.ltb_lt in Hbud. destruct (xhi k v) as [vh|] eqn:Hxv; [|discriminate]. apply Z.ltb_lt in Hvh.
    pose proof (xhi_sound SEGS E M k v vh HK Hxv) as VH.
    destruct (floor_term fl top bud) as [fb fo] eqn:Hft.
    unfold stack_x in Hst. apply andb_prop in Hst as [Htok Hlo]. rewrite Hft in Hlo.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK Hlo) as L. cbn [xt_den] in L.
    pose proof (AzKnowLib.floor_term_sound SEGS E M k fl top bud fb fo HK Htok Hfl Hft) as FL.
    destruct (split_lit top) as [tb tk] eqn:Hst. destruct (AzKnowLib.top_ok_sound SEGS E M k fl top bud tb tk HK Htok Hst) as (_ & Hb0 & _ & _).
    pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK Hap) as D.
    rewrite !estart_SA in D. cbn [a_base a_off] in D. rewrite (elenZ_lit E 1), (elenZ_lit E (bud + WSTK)) in D by (unfold WSTK, GlzConst.WSTK, two47 in *; lia).
    pose proof GlzConst.ceil_lo as CL. apply AX2S.fpc_stop. left. unfold WSTK, two47, uE in *. lia.
  - (* [comment removed for export] *)
    apply existsb_exists in H as (K & Hin & Hx).
    destruct K as [| | | | | | | | | | | v' lo' d']; try discriminate.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HF. cbn [kentry_ok] in HF. destruct HF as [HF HR].
    apply andb_prop in Hx as [Hx Hlo]. apply andb_prop in Hx as [Hv Hd]. apply expr_eqb_eq in Hv. subst v'. apply Nat.leb_le in Hd.
    enough (X : AX2S.fpc M (uE E v) (uE E lo) d' /\ AX2S.kfpc_robust (uE E v) (uE E lo)).
    { destruct X as [X1 X2]. split; [exact (AX2S.fpc_mono_d M _ _ d' d X1 Hd) | intros _; exact X2]. }
    apply orb_prop in Hlo as [Hlo|Hra]; [apply orb_prop in Hlo as [Heq|Hlw]|].
    + apply expr_eqb_eq in Heq. subst lo'. split; [exact HF | exact HR].
    + (* [comment removed for export] *)
      apply andb_prop in Hlw as [H1 H2]. pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as L1. cbn [xt_den] in L1.
      pose proof (AzKnowLib.stack_x_sound SEGS E M k fl top bud lo HK Hfl H2) as XL. pose proof ceil_rng as CR.
      apply (kfpc_lower M _ _ (uE E lo') d' HF HR); [unfold uE in *; lia|]. unfold AX2S.FPC_CEIL, uE in *. lia.
    + apply andb_prop in Hra as [H1 H2]. pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as L1. cbn [xt_den] in L1.
      pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as L2. cbn [xt_den] in L2.
      split; [|unfold AX2S.kfpc_robust, uE in *; lia].
      apply (AX2S.fpc_raise_lo M _ (uE E lo') (uE E lo) d' HF); unfold uE in *; lia.
  - (* [comment removed for export] *)
    destruct d as [|dd]; [discriminate|].
    destruct (kfpc_frame_ok SEGS k v lo) as [w|] eqn:Hfo; [|discriminate].
    destruct (kfpc_frame_ok_sound E M k v lo w HK Hfo) as (L16 & V8 & VH & DEF & RD).
    split; [|intros _; unfold AX2S.kfpc_robust; lia].
    apply (AX2S.fpc_frame M (uE E v) (uE E lo) dd (uE E w) L16 V8 VH DEF RD).
    apply orb_prop in Hfr as [Hst|Hf].
    + pose proof (lin_ge0_sound SEGS E M k _ _ HK Hst) as L. cbn [xt_den] in L. apply AX2S.fpc_stop. left. unfold uE. lia.
    + apply existsb_exists in Hf as (K & Hin & Hx).
      destruct K as [| | | | | | | | | | | v' lo' d']; try discriminate.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HF. cbn [kentry_ok] in HF. destruct HF as [HF _].
      apply andb_prop in Hx as [Hx Hd]. apply andb_prop in Hx as [Hv Hl]. apply expr_eqb_eq in Hv. apply expr_eqb_eq in Hl. subst v' lo'.
      apply Nat.leb_le in Hd. exact (AX2S.fpc_mono_d M _ _ d' dd HF Hd).
Qed.

(* [comment removed for export] *)
Lemma fpc_x_sound : forall E M k fl top bud s0 sp,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> fpc_x SEGS k fl top bud s0 sp = true -> AX2S.fpc M (uE E s0) (uE E sp) DMAXN.
Proof. intros E M k fl top bud s0 sp HK Hfl H. unfold fpc_x in H. exact (proj1 (kfpc_entailed_sound false E M k fl top bud s0 sp DMAXN HK Hfl H)). Qed.

(* [comment removed for export] *)
Lemma kfpc_entailed_fact_sound : forall E M k fl top bud v lo d,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> kfpc_entailed SEGS true k fl top bud v lo d = true -> kentry_ok SEGS E M (KFpc v lo d).
Proof.
  intros E M k fl top bud v lo d HK Hfl H. destruct (kfpc_entailed_sound true E M k fl top bud v lo d HK Hfl H) as [H1 H2].
  cbn [kentry_ok]. split; [exact H1 | exact (H2 eq_refl)].
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Kept.
Variables (E E' : env) (cs cs' : acs) (mdl mdl' : Model) (M M' : word -> option byte) (B C K B' C' K' : Z).
Variables (live objs : list (expr * expr)) (sp : expr) (stk : Z).
Hypothesis HA : AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl.
Hypothesis HA' : AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) B' C' K' M' mdl'.
(* [comment removed for export] *)
Hypothesis LIVE_pre : forall x, In x (blocks_den E live) -> In x (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)).
Hypothesis LIVE_post : forall x, In x (blocks_den E live) -> In x (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs')).
Hypothesis OBJS_pre : forall x, In x (blocks_den E objs) -> In x (blocks_den E (a_vis cs ++ a_fake cs)) \/ (In (fst x, fst x + snd x) PERMc /\ 1 <= snd x).   (* [comment removed for export] *)
Hypothesis OBJS_post : forall x, In x (blocks_den E objs) -> In x (blocks_den E' (a_vis cs' ++ a_fake cs')) \/ (In (fst x, fst x + snd x) PERMc /\ 1 <= snd x).
Hypothesis Hsp : CEIL_run + stk <= uE E sp.
Hypothesis Hstk0 : 0 <= stk.
(* [comment removed for export] *)
Variables (Lk Lfk : list (Z * Z)).
Hypothesis FR : forall a : word, nkept SWIN PERMc G Lk Lfk (scratch (uE E sp) stk) a -> M' a = M a.
Hypothesis LIVE_nk : forall a : word, in_blocks (blocks_den E live) (u a) -> in_blocks Lk (u a) \/ in_blocks Lfk (u a).
Hypothesis OBJS_nk : forall x, In x (blocks_den E objs) -> In x (Lk ++ Lfk) \/ (In (fst x, fst x + snd x) PERMc /\ 1 <= snd x).

Lemma Mr_kept_app : forall a : word,
  frame_kept stk (blocks_den E live) (u (edenot E sp)) a -> Mr E' cs' mdl' M' a = Mr E cs mdl M a.
Proof. pose proof sfloor_ge as SFG_.
  intros a Hk. pose proof (AINV_top _ _ _ _ _ _ _ HA) as HT.
  assert (VIS : forall EE ccs L1 L2, (forall x, In x (blocks_den E live) -> In x (L1 ++ L2)) ->
            L1 = blocks_den EE (a_vis ccs) -> L2 = blocks_den EE (a_fake ccs) ->
            in_blocks (L1 ++ L2) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a) \/ g_img_lo G <= u a < g_img_hi G).
  { intros EE ccs L1 L2 HL -> ->. unfold uE in Hsp. pose proof G_ro_lo_img as GRL. destruct Hk as [[Ho _]|[[Hi _]|[[Ht _]|Hge]]].
    - destruct Ho as [Hb|[Hp|[Hs|Hw]]]; [left; eapply in_blocks_weaken; [exact HL | exact Hb] | right; left; exact Hp | right; right; left; lia | right; right; right; left; exact Hw].
    - right; right; right; right. lia.
    - right; right; left. lia.
    - right; right; left. lia. }
  rewrite (Mr_app E' cs' mdl' B' C' K' M' a HA' (VIS E' cs' _ _ LIVE_post eq_refl eq_refl)).
  rewrite (Mr_app E cs mdl B C K M a HA (VIS E cs _ _ LIVE_pre eq_refl eq_refl)).
  apply FR. unfold nkept. unfold uE in Hsp. destruct Hk as [[Ho [Hns Hne]]|[[Hi Hnp]|[[Ht Hle]|Hge]]].
  - left. split; [|split; [exact Hns | intros He; exact (False_ind _ (Hne He))]]. destruct Ho as [Hb|[Hp|[Hs|Hw]]].
    + destruct (LIVE_nk a Hb) as [H1|H2]; [left; exact H1 | right; left; exact H2].
    + right; right; left. exact Hp.
    + right; right; right; left. lia.
    + right; right; right; right. exact Hw.
  - right; left. split; [exact Hi | exact Hnp].
  - left. split; [right; right; right; left; lia | split; [unfold scratch, uE in *; lia | intros _; right; right; lia]].
  - left. split; [right; right; right; left; lia | split; [unfold scratch, uE in *; lia | intros _; right; right; lia]].
Qed.

Lemma Mr_kept_shadow : forall a : word,
  shz E objs (uE E sp) (u a) -> Mr E' cs' mdl' M' a = Mr E cs mdl M a.
Proof.
  intros a Hz. pose proof (AINV_top _ _ _ _ _ _ _ HA) as HT.
  (* [comment removed for export] *)
  assert (CASE : (exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (u a)
                    /\ (In (bb, nn) (blocks_den E (a_vis cs ++ a_fake cs)) /\ In (bb, nn) (blocks_den E' (a_vis cs' ++ a_fake cs')) /\ In (bb, nn) (Lk ++ Lfk)))
                 \/ in_pshadow PERMc (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a)).
  { destruct Hz as [Hl|[Hs|Hi]].
    - destruct Hl as (bb & nn & Hin & Hsh).
      destruct (OBJS_pre _ Hin) as [V1|[P1 M1]]; [|right; left; exists bb, (bb + nn); split; [exact P1|]; split; [cbn [fst snd] in M1; lia|];
                                                    replace (bb + nn - bb) with nn by lia; exact Hsh].
      destruct (OBJS_post _ Hin) as [V2|[P1 M1]]; [|right; left; exists bb, (bb + nn); split; [exact P1|]; split; [cbn [fst snd] in M1; lia|];
                                                     replace (bb + nn - bb) with nn by lia; exact Hsh].
      destruct (OBJS_nk _ Hin) as [V3|[P1 M1]]; [|right; left; exists bb, (bb + nn); split; [exact P1|]; split; [cbn [fst snd] in M1; lia|];
                                                   replace (bb + nn - bb) with nn by lia; exact Hsh].
      left. exists bb, nn. split; [exact Hin|]. split; [exact Hsh|]. split; [exact V1 | split; [exact V2 | exact V3]].
    - right; right; left. exact Hs.
    - right; right; right. exact Hi. }
  destruct CASE as [(bb & nn & Hin & Hsh & V1 & V2 & V3)|[HP|HS]].
  - rewrite (Mr_shadow E' cs' mdl' M' a ltac:(left; exists bb, nn; split; [exact V2 | exact Hsh])).
    rewrite (Mr_shadow E cs mdl M a ltac:(left; exists bb, nn; split; [exact V1 | exact Hsh])).
    apply FR. unfold nkept. right; right; left. exists bb, nn. split; [exact V3 | exact Hsh].
  - rewrite (Mr_pshadow _ _ _ _ _ _ _ E' cs' mdl' M' a HA HP). rewrite (Mr_pshadow _ _ _ _ _ _ _ E cs mdl M a HA HP).
    apply FR. unfold nkept. right; right; right; right; right. exact HP.
  - rewrite (Mr_shadow E' cs' mdl' M' a (or_intror HS)). rewrite (Mr_shadow E cs mdl M a (or_intror HS)).
    apply FR. unfold nkept. destruct HS as [Hs|Hi]; [right; right; right; left; exact Hs | right; right; right; right; left; exact Hi].
Qed.
End Kept.

End Sound.

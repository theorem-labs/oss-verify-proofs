(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)

Section Frame.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_blocks_app : forall L1 L2 z, in_blocks (L1 ++ L2) z <-> in_blocks L1 z \/ in_blocks L2 z.
Proof.
  intros L1 L2 z. unfold in_blocks. split.
  - intros (b & n & Hin & Hz). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists b, n; split; assumption.
  - intros [(b & n & Hin & Hz)|(b & n & Hin & Hz)]; exists b, n; split; try assumption; apply in_app_iff; [left|right]; assumption.
Qed.


Lemma in_blocks_fusable : forall L z, in_blocks (map fusable L) z -> exists f m, In (f, m) L /\ f <= z < f + m - 8.
Proof.
  intros L z (b & n & Hin & Hz). apply in_map_iff in Hin as [[f m] [Heq Hin]]. unfold fusable in Heq. cbn [fst snd] in Heq.
  injection Heq as <- <-. exists f, m. split; [exact Hin | lia].
Qed.

Lemma map_fusable_app : forall L1 L2, map fusable (L1 ++ L2) = map fusable L1 ++ map fusable L2.
Proof. intros. apply map_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_shadow_apart : forall b m b' m' z,
  b + m <= b' -> b' mod 8 = 0 -> in_shadow SB b m z -> in_shadow SB b' m' z -> False.
Proof.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  intros b m b' m' z Hle Hal [H1 H2] [H3 H4]. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.


(* [comment removed for export] *)
Definition happ (L LF : list (Z * Z)) (a : word) : Prop :=
  in_blocks L (u a) \/ in_blocks (map fusable LF) (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a)
  \/ in_lshadow LF (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a).   (* [comment removed for export] *)

Record hprops : Prop := HPROPS {
  (* [comment removed for export] *)
  hp_frame : forall L LF B C K M M' mdl,
    AINVH L LF B C K M mdl -> (forall a, M' a <> M a -> happ L LF a /\ M' a <> None) -> AINVH L LF B C K M' mdl;
  (* [comment removed for export] *)
  hp_vm : forall L LF B C K M mdl mdl', AINVH L LF B C K M mdl -> m_vm mdl' = m_vm mdl -> AINVH L LF B C K M mdl';
  (* [comment removed for export] *)
  hp_mono : forall L LF B C K B' C' K' M mdl,
    AINVH L LF B C K M mdl -> B <= B' -> C <= C' -> K <= K' -> AINVH L LF B' C' K' M mdl;
  (* [comment removed for export] *)
  hp_lazy : forall L LF B C K M mdl,
    AINVH L LF B C K M mdl ->
    exists AA, A_wf AA /\ MInv AA mdl
      /\ (forall a : word, in_shc SHC (u a) = true -> page_allowedb AA (page_base a) = true)
      /\ (forall (a : word) b n, In (b, n) (L ++ LF) -> in_shadow SB b n (u a) -> page_allowedb AA (page_base a) = true)
      /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINVH L LF B C K M mdl');
  (* [comment removed for export] *)
  hp_facts : forall L LF B C K M mdl,
    AINVH L LF B C K M mdl ->
    Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                      /\ (u (fst iv) + u (snd iv) <= g_img_lo G \/ g_img_hi G <= u (fst iv))) (m_vm_lazy mdl);
  (* [comment removed for export] *)
  hp_zone : forall L LF B C K M mdl b m, AINVH L LF B C K M mdl -> In (b, m) L -> ablk_ok G b m /\ b mod 8 = 0;
  hp_fzone : forall L LF B C K M mdl f m, AINVH L LF B C K M mdl -> In (f, m) LF ->
    ablk_ok G f m /\ f mod 8 = 0 /\ m mod 8 = 0 /\ 8 <= m;
  hp_disj : forall L LF B C K M mdl L1 L2 b m b' m',
    AINVH L LF B C K M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b;
  hp_fdisj : forall L LF B C K M mdl F1 F2 f m f' m',
    AINVH L LF B C K M mdl -> LF = F1 ++ (f, m) :: F2 -> In (f', m') (F1 ++ F2) -> f + m <= f' \/ f' + m' <= f;
  hp_bfdisj : forall L LF B C K M mdl b m f n,
    AINVH L LF B C K M mdl -> In (b, m) L -> In (f, n) LF -> b + m <= f \/ f + n <= b;
  hp_perm : forall L L' LF LF' B C K M mdl,
    Permutation.Permutation L L' -> Permutation.Permutation LF LF' -> AINVH L LF B C K M mdl -> AINVH L' LF' B C K M mdl;
  (* [comment removed for export] *)
  hp_shc_stack : forall z, in_sshadow z -> in_shc SHC z = true;
  hp_shc_image : forall z, SB + g_ro_lo G / 8 <= z < SB + (g_img_hi G + 7) / 8 -> in_shc SHC z = true;
  (* [comment removed for export] *)
  hp_nolazy : forall L LF B C K M mdl b n (a : word),
    AINVH L LF B C K M mdl -> In (b, n) (L ++ LF) -> b <= u a < b + n -> lz mdl a = false;
  (* [comment removed for export] *)
  hp_errno : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G
}.
(* [comment removed for export] *)
Lemma G_privx (HP0 : hprops) (G_priv0 : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G) :
  forall lo hi, In (lo, hi) (g_privx G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Proof.
  intros lo hi [H|H]; [injection H as <- <-; pose proof (hp_errno HP0); lia | exact (G_priv0 lo hi H)].
Qed.
Hypothesis HP : hprops.

(* [comment removed for export] *)
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
(* [comment removed for export] *)
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.

(* [comment removed for export] *)
Lemma G_img_ceil : g_img_hi G <= CEIL_run.
Proof. pose proof ceil_rng as CR. pose proof G_img_shlo. unfold SHMAPLO in *. lia. Qed.
Lemma band_lits : SHMAPLO < SB /\ SB + CEIL_run / 8 < HEAPLO /\ HEAPLO = KHI /\ KHI < CEIL_run /\ CEIL_run <= PTRHI /\ PTRHI < two47
                  /\ CEIL_run mod 8 = 0.
Proof.
  pose proof ceil_rng as CR. pose proof ceil_pg as CP.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  unfold SHMAPLO, SB, HEAPLO, KHI, PTRHI, two47 in *. cbn. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma store_ok_defined : forall M (a : word),
  ~ (g_img_lo G <= u a < g_img_hi G) -> RiscvSemantics.store_ok SEGS M a 1 = true -> M a <> None.
Proof.
  intros M a Ha Hs Hn. cbn [RiscvSemantics.store_ok] in Hs. unfold wview in Hs. rewrite Hn in Hs.
  rewrite (SEGS_out a Ha) in Hs. discriminate Hs.
Qed.

(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).     (* [comment removed for export] *)
Variable HIDF : list (Z * Z).    (* [comment removed for export] *)
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.

(* [comment removed for export] *)
Definition zone (a : word) : Prop :=
  (in_blocks HID (u a) \/ in_blocks HIDF (u a) \/ SPTOPc <= u a
   \/ (g_ro_lo G <= u a < g_img_hi G /\ ~ in_wins (g_privx G) (u a))   (* [comment removed for export] *)
   \/ in_lshadow (HID ++ HIDF) (u a)
   \/ in_sshadow (u a)                                     (* [comment removed for export] *)
   \/ in_ishadow G (u a)                                   (* [comment removed for export] *)
   \/ (CEIL_run <= u a < SFLOOR))                          (* [comment removed for export] *)
  /\ ~ in_wins PERMc (u a) /\ ~ in_wins SWIN (u a).

(* [comment removed for export] *)
Definition perm_owned : Prop :=
  (forall z, in_wins PERMc z -> in_blocks HID z \/ in_blocks (map fusable HIDF) z \/ SPTOPc <= z \/ in_wins SWIN z)   (* [comment removed for export] *)
  /\ (forall z, in_wins PERMc z -> z < two47).

(* [comment removed for export] *)
Lemma swin_byte : forall z, in_wins SWIN z -> g_ro_hi G <= z < g_img_hi G /\ ~ in_wins (g_priv G) z.
Proof.
  intros z (lo & hi & Hin & Hz). destruct (SWIN_img lo hi Hin) as (S1 & S2 & S3). split; [lia|].
  intros (plo & phi & Hpin & Hpz). destruct (S3 plo phi Hpin); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dzone (a : word) : Prop := (CEIL_run <= u a < SPTOPc) \/ in_wins PERMc (u a) \/ errw G (u a).

Definition AINV_f (Lc Lf : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) : Prop :=
  AINVH (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K M mdl
  /\ perm_owned
  /\ (CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0)
  /\ (forall a, zone a -> M a = M0 a)
  /\ (forall a, dzone a -> M0 a <> None -> M a <> None).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma ablk_byte : forall b m x, ablk_ok G b m -> b <= x < b + m ->
  PTRLO <= x /\ x < CEIL_run /\ ~ (g_img_lo G <= x < g_img_hi G) /\ ~ (SHMAPLO <= x < KHI).
Proof. intros b m x (A1 & A2 & A3 & A4) Hx. unfold KHI, SHMAPLO in *. repeat split; lia. Qed.

Lemma ablk_shadow : forall b m z, ablk_ok G b m -> in_shadow SB b m z ->
  SB <= z /\ z < SB + CEIL_run / 8 /\ z < KHI /\ (z < SB + g_img_lo G / 8 \/ SB + g_img_hi G / 8 <= z).
Proof.
  intros b m z (A1 & A2 & A3 & A4) [S1 S2]. pose proof band_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof G_img_al as (I0 & I1 & I2).
  unfold PTRLO, SB, KHI, HEAPLO, PTRHI, two47 in *. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma ishadow_bounds : forall z, in_ishadow G z -> SB + g_img_lo G / 8 <= z /\ z < SB + g_img_hi G / 8 /\ z < KHI.
Proof.
  intros z [H1 H2]. pose proof G_img_al as (I0 & I1 & I2). pose proof G_ro_img as (R1 & R2 & R3). pose proof G_img_shlo as GS.
  unfold SB, KHI, SHMAPLO in *. repeat split; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Props.
Variables (Lc Lf : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model).
Hypothesis HAf : AINV_f Lc Lf B C K M mdl.

Let HA := proj1 HAf.
Let HPo : perm_owned := proj1 (proj2 HAf).
Let HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0 := proj1 (proj2 (proj2 HAf)).

(* [comment removed for export] *)
Lemma gowned_happ : forall a, gowned SWIN PERMc SPTOPc SB Lc Lf a -> happ (Lc ++ HID) (Lf ++ HIDF) a.
Proof. pose proof sfloor_ge as SFG_.
  intros a [Ho|Hsh].
  - destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
    + apply in_blocks_app in Hb as [Hb|Hf].
      * left. apply in_blocks_app. left. exact Hb.
      * right. left. rewrite map_fusable_app. apply in_blocks_app. left. exact Hf.
    + destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw']]].
      * left. apply in_blocks_app. right. exact Hh.
      * right. left. rewrite map_fusable_app. apply in_blocks_app. right. exact Hf.
      * right. right. left. pose proof HT. lia.
      * right. right. right. left. exact Hsw'.
    + right. right. left. lia.
    + right. right. right. left. exact Hsw.
  - right. right. right. right. left. destruct Hsh as (b & n & Hin & Hz). exists b, n. split; [|exact Hz].
    apply in_app_iff; left; exact Hin.
Qed.

(* [comment removed for export] *)
Lemma gowned_not_zone : forall a, gowned SWIN PERMc SPTOPc SB Lc Lf a -> zone a -> False.
Proof. pose proof sfloor_ge as SFG_.
  intros a Hg (Hz & Hnp & Hnsw).
  pose proof band_lits as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7). pose proof G_img_ceil as GC. pose proof G_ro_img as (GR0 & GR1 & GR2).
  pose proof G_img_al as (GA0 & GA1 & GA2). pose proof G_img_shlo as GS.
  pose proof HT as [HT1 HT2].
  (* [comment removed for export] *)
  assert (ZB : forall b m, In (b, m) (Lc ++ HID) -> ablk_ok G b m /\ b mod 8 = 0)
    by (intros b m Hin; exact (hp_zone HP _ _ _ _ _ _ _ b m HA Hin)).
  assert (ZF : forall f m, In (f, m) (Lf ++ HIDF) -> ablk_ok G f m /\ f mod 8 = 0 /\ m mod 8 = 0 /\ 8 <= m)
    by (intros f m Hin; exact (hp_fzone HP _ _ _ _ _ _ _ f m HA Hin)).
  assert (ZO : forall b m, In (b, m) (Lc ++ HID) \/ In (b, m) (Lf ++ HIDF) -> ablk_ok G b m /\ b mod 8 = 0).
  { intros b m [Hin|Hin]; [exact (ZB b m Hin)|]. destruct (ZF b m Hin) as (X1 & X2 & _). split; assumption. }
  (* [comment removed for export] *)
  assert (DBB : forall b n b' n', In (b, n) Lc -> In (b', n') HID -> b + n <= b' \/ b' + n' <= b).
  { intros b n b' n' Hin Hin'. destruct (in_split _ _ Hin) as (L1 & L2 & HL).
    eapply (hp_disj HP _ _ _ _ _ _ _ L1 (L2 ++ HID) b n b' n' HA).
    - rewrite HL. rewrite <- app_assoc. reflexivity.
    - rewrite app_assoc. apply in_app_iff. right. exact Hin'. }
  assert (DFF : forall f n f' n', In (f, n) Lf -> In (f', n') HIDF -> f + n <= f' \/ f' + n' <= f).
  { intros f n f' n' Hin Hin'. destruct (in_split _ _ Hin) as (F1 & F2 & HL).
    eapply (hp_fdisj HP _ _ _ _ _ _ _ F1 (F2 ++ HIDF) f n f' n' HA).
    - rewrite HL. rewrite <- app_assoc. reflexivity.
    - rewrite app_assoc. apply in_app_iff. right. exact Hin'. }
  assert (DBF : forall b n f m, In (b, n) (Lc ++ HID) -> In (f, m) (Lf ++ HIDF) -> b + n <= f \/ f + m <= b)
    by (intros b n f m Hin Hin'; exact (hp_bfdisj HP _ _ _ _ _ _ _ b n f m HA Hin Hin')).
  (* [comment removed for export] *)
  destruct Hg as [Ho|Hsh].
  - (* [comment removed for export] *)
    assert (APP : (exists b n, In (b, n) (Lc ++ map fusable Lf ++ map fusable HIDF) /\ b <= u a < b + n
                               /\ exists b0 n0, (In (b0, n0) (Lc ++ HID) \/ In (b0, n0) (Lf ++ HIDF)) /\ b0 <= b /\ b + n <= b0 + n0)
                  \/ SFLOOR <= u a < SPTOPc).
    { destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
      - left. destruct Hb as (b & n & Hin & Hbz). exists b, n. split; [rewrite app_assoc; apply in_app_iff; left; exact Hin|]. split; [exact Hbz|].
        apply in_app_iff in Hin as [Hin|Hin].
        + exists b, n. split; [left; apply in_app_iff; left; exact Hin | lia].
        + apply in_map_iff in Hin as [[f m] [Heq Hin]]. unfold fusable in Heq. cbn in Heq. injection Heq as <- <-.
          exists f, m. split; [right; apply in_app_iff; left; exact Hin | lia].
      - destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw']]].
        + exfalso. apply Hnp. exact Hp.
        + exfalso. apply Hnp. exact Hp.
        + exfalso. apply Hnp. exact Hp.
        + exfalso. apply Hnp. exact Hp.
      - right. exact Hst.
      - exfalso. exact (Hnsw Hsw). }
    destruct APP as [(b & n & Hin & Hbz & b0 & n0 & Hin0 & Hb0 & Hbn0)|Hst].
    + destruct (ZO b0 n0 Hin0) as [AB0 _].
      destruct (ablk_byte b0 n0 (u a) AB0 ltac:(lia)) as (P1 & P2 & P3 & P4).
      destruct Hz as [Hh|[Hhf|[Htop|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
      * (* [comment removed for export] *) destruct Hh as (b' & n' & Hin' & Hbz').
        apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
        -- destruct (DBB b n b' n' Hin Hin'). all: lia.
        -- apply in_map_iff in Hin as [[f m] [Heq Hinf]]. unfold fusable in Heq; cbn in Heq; injection Heq as <- <-.
           destruct (DBF b' n' f m ltac:(apply in_app_iff; right; exact Hin') ltac:(apply in_app_iff; left; exact Hinf)); lia.
        -- apply in_map_iff in Hin as [[f m] [Heq Hinf]]. unfold fusable in Heq; cbn in Heq; injection Heq as <- <-.
           destruct (DBF b' n' f m ltac:(apply in_app_iff; right; exact Hin') ltac:(apply in_app_iff; right; exact Hinf)); lia.
      * (* [comment removed for export] *) destruct Hhf as (f' & m' & Hin' & Hbz').
        apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
        -- destruct (DBF b n f' m' ltac:(apply in_app_iff; left; exact Hin) ltac:(apply in_app_iff; right; exact Hin')); lia.
        -- apply in_map_iff in Hin as [[f m] [Heq Hinf]]. unfold fusable in Heq; cbn in Heq; injection Heq as <- <-.
           destruct (DFF f m f' m' Hinf Hin'); lia.
        -- apply in_map_iff in Hin as [[f m] [Heq Hinf]]. unfold fusable in Heq; cbn in Heq; injection Heq as <- <-.
           (* [comment removed for export] *)
           exfalso. apply Hnp.
           destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
           ++ destruct Hb as (b2 & n2 & Hin2 & Hbz2). apply in_app_iff in Hin2 as [Hin2|Hin2].
              ** destruct (DBF b2 n2 f m ltac:(apply in_app_iff; left; exact Hin2) ltac:(apply in_app_iff; right; exact Hinf)); lia.
              ** apply in_map_iff in Hin2 as [[f2 m2] [Heq2 Hinf2]]. unfold fusable in Heq2; cbn in Heq2; injection Heq2 as <- <-.
                 destruct (DFF f2 m2 f m Hinf2 Hinf); lia.
           ++ exact Hp.
           ++ lia.
           ++ exfalso. exact (Hnsw Hsw).
      * lia.
      * lia.
      * (* [comment removed for export] *)
        destruct Hlsh as (b' & n' & Hin' & Hsh'). apply in_app_iff in Hin' as [Hin'|Hin'];
          (destruct (ZO b' n' ltac:(first [left; apply in_app_iff; right; exact Hin' | right; apply in_app_iff; right; exact Hin'])) as [AB' _]);
          destruct (ablk_shadow b' n' (u a) AB' Hsh') as (S1 & S2 & S3 & S4); lia.
      * unfold in_sshadow in Hssh. lia.
      * destruct (ishadow_bounds _ Hish) as (IS1 & IS2 & IS3). lia.
      * (* [comment removed for export] *) lia.
    + (* [comment removed for export] *)
      destruct Hz as [Hh|[Hhf|[Htop|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
      * destruct Hh as (b' & n' & Hin' & Hbz'). destruct (ZB b' n' ltac:(apply in_app_iff; right; exact Hin')) as [(_ & A2 & _) _]. lia.
      * destruct Hhf as (f' & m' & Hin' & Hbz'). destruct (ZF f' m' ltac:(apply in_app_iff; right; exact Hin')) as [(_ & A2 & _) _]. lia.
      * lia.
      * lia.
      * destruct Hlsh as (b' & n' & Hin' & Hsh'). apply in_app_iff in Hin' as [Hin'|Hin'];
          (destruct (ZO b' n' ltac:(first [left; apply in_app_iff; right; exact Hin' | right; apply in_app_iff; right; exact Hin'])) as [AB' _]);
          destruct (ablk_shadow b' n' (u a) AB' Hsh') as (S1 & S2 & S3 & S4); lia.
      * unfold in_sshadow in Hssh. lia.
      * destruct (ishadow_bounds _ Hish) as (IS1 & IS2 & IS3). lia.
      * (* [comment removed for export] *) lia.
  - (* [comment removed for export] *)
    destruct Hsh as (b & n & Hin0 & Hsh).
    assert (Hin : In (b, n) (Lc ++ Lf)) by (apply in_app_iff; right; exact Hin0).   (* [comment removed for export] *)
    assert (OB : ablk_ok G b n /\ b mod 8 = 0).
    { apply in_app_iff in Hin as [Hin|Hin]; apply ZO; [left | right]; apply in_app_iff; left; exact Hin. }
    destruct OB as [OA O3]. destruct (ablk_shadow b n (u a) OA Hsh) as (SH1 & SH2 & SH3 & SH4).
    destruct Hz as [Hh|[Hhf|[Htop|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
    + destruct Hh as (b' & n' & Hin' & Hbz'). destruct (ZB b' n' ltac:(apply in_app_iff; right; exact Hin')) as [AB' _].
      destruct (ablk_byte b' n' (u a) AB' Hbz') as (_ & _ & _ & P4). apply P4. unfold SHMAPLO, KHI in *. lia.
    + destruct Hhf as (f' & m' & Hin' & Hbz'). destruct (ZF f' m' ltac:(apply in_app_iff; right; exact Hin')) as [AB' _].
      destruct (ablk_byte f' m' (u a) AB' Hbz') as (_ & _ & _ & P4). apply P4. unfold SHMAPLO, KHI in *. lia.
    + lia.
    + unfold SB, SHMAPLO in *. lia.
    + destruct Hlsh as (b' & n' & Hin' & Hsh').
      assert (OB' : ablk_ok G b' n' /\ b' mod 8 = 0).
      { apply in_app_iff in Hin' as [Hin'|Hin']; apply ZO; [left | right]; apply in_app_iff; right; exact Hin'. }
      destruct OB' as [OA' O3'].
      assert (DJ : b + n <= b' \/ b' + n' <= b).
      { apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff in Hin' as [Hin'|Hin'].
        - exact (DBB b n b' n' Hin Hin').
        - exact (DBF b n b' n' ltac:(apply in_app_iff; left; exact Hin) ltac:(apply in_app_iff; right; exact Hin')).
        - destruct (DBF b' n' b n ltac:(apply in_app_iff; right; exact Hin') ltac:(apply in_app_iff; left; exact Hin)); lia.
        - exact (DFF b n b' n' Hin Hin'). }
      destruct DJ as [DJ|DJ].
      * exact (in_shadow_apart b n b' n' (u a) DJ O3' Hsh Hsh').
      * exact (in_shadow_apart b' n' b n (u a) DJ O3 Hsh' Hsh).
    + unfold in_sshadow in Hssh. lia.
    + destruct (ishadow_bounds _ Hish) as (IS1 & IS2 & IS3). pose proof G_ro_img. lia.
    + (* [comment removed for export] *) unfold HEAPLO, KHI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma AINV_f_pshadow : forall z, in_pshadow PERMc z ->
  (in_lshadow (HID ++ HIDF) z \/ in_sshadow z \/ in_ishadow G z) /\ SB <= z < HEAPLO.
Proof.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  pose proof band_lits as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7). pose proof G_img_al as (GA0 & GA1 & GA2).
  pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
  intros z (lo & hi & Hin & Hlt & [S1 S2]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  set (z1 := Z.max lo (8 * (z - SB))).
  assert (W1 : lo <= z1 < hi) by (subst z1; lia).
  assert (G1 : z1 / 8 = z - SB) by (subst z1; lia).
  pose proof (proj2 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as H47. unfold two47 in H47.
  destruct (proj1 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as [Hh|[Hf|[Hc|Hsw]]].
  - destruct Hh as (b & n & Hbin & Hbz). destruct (ZB b n ltac:(apply in_app_iff; right; exact Hbin)) as [(Y1 & Y2 & _ & _) _].
    clear ZB ZF GA1 GA2 BL7. split.
    + left. exists b, n. split; [apply in_app_iff; left; exact Hbin|]. unfold in_shadow. clear Y1 Y2 H47. lia.
    + unfold SB, HEAPLO, PTRLO, PTRHI in *. lia.
  - apply in_blocks_fusable in Hf as (f & m & Hfin & Hfz). destruct (ZF f m ltac:(apply in_app_iff; right; exact Hfin)) as ((Y1 & Y2 & _ & _) & _ & _).
    clear ZB ZF GA1 GA2 BL7. split.
    + left. exists f, m. split; [apply in_app_iff; right; exact Hfin|]. unfold in_shadow. clear Y1 Y2 H47. lia.
    + unfold SB, HEAPLO, PTRLO, PTRHI in *. lia.
  - clear ZB ZF GA1 GA2 BL7. split; [right; left|unfold SB, HEAPLO, PTRHI in *; lia]. unfold in_sshadow. unfold SB, HEAPLO, PTRHI in *. lia.
  - destruct (swin_byte z1 Hsw) as [SW1 _]. clear ZB ZF BL7. split; [right; right|unfold SB, HEAPLO, SHMAPLO in *; lia].
    unfold in_ishadow. unfold SB, SHMAPLO in *. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma AINV_f_pshadow_lo : forall lo hi z, In (lo, hi) PERMc -> lo < hi -> hi <= SPTOPc ->     (* [comment removed for export] *)
  (forall slo shi, In (slo, shi) SWIN -> hi <= slo \/ shi <= lo) ->
  in_shadow SB lo (hi - lo) z -> in_lshadow (HID ++ HIDF) z.
Proof.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros lo hi z Hin Hlt Hhi Hnsw [S1 S2].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  set (z1 := Z.max lo (8 * (z - SB))).
  assert (W1 : lo <= z1 < hi) by (subst z1; lia).
  assert (G1 : z1 / 8 = z - SB) by (subst z1; lia).
  destruct (proj1 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as [Hh|[Hf|[Hc|Hsw]]].
  - destruct Hh as (b & n & Hbin & Hbz). exists b, n. split; [apply in_app_iff; left; exact Hbin|]. unfold in_shadow. lia.
  - apply in_blocks_fusable in Hf as (f & m & Hfin & Hfz). exists f, m. split; [apply in_app_iff; right; exact Hfin|]. unfold in_shadow. lia.
  - exfalso. lia.
  - exfalso. destruct Hsw as (slo & shi & Hsin & Hsz). destruct (Hnsw slo shi Hsin); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End Props.

(* [comment removed for export] *)
Lemma AINV_f_frame : forall Lc Lf B C K M M' mdl,
  AINV_f Lc Lf B C K M mdl ->
  (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB Lc Lf a /\ M' a <> None) ->
  AINV_f Lc Lf B C K M' mdl.
Proof.
  pose proof G_ro_img as G_ro_img_kept.      (* [comment removed for export] *)
  intros Lc Lf B C K M M' mdl HAf Hch. pose proof HAf as (HA & HP' & HT & HF & HD).
  split; [|split; [exact HP' | split; [exact HT|split]]].
  - eapply (hp_frame HP); [exact HA|]. intros a Ha. destruct (Hch a Ha) as [Ho Hs]. split; [|exact Hs].
    exact (gowned_happ Lc Lf B C K M mdl HAf a Ho).
  - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne].
    + rewrite Heq. exact (HF a Hz).
    + exfalso. destruct (Hch a Hne) as [Ho _]. exact (gowned_not_zone Lc Lf B C K M mdl HAf a Ho Hz).
  - intros a Hd H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hd H0)|].
    exact (proj2 (Hch a Hne)).
Qed.

(* [comment removed for export] *)
Lemma AINV_f_vm : forall Lc Lf B C K M mdl mdl', AINV_f Lc Lf B C K M mdl -> m_vm mdl' = m_vm mdl -> AINV_f Lc Lf B C K M mdl'.
Proof.
  intros Lc Lf B C K M mdl mdl' (HA & HP' & HT & HF & HD) Hvm. split; [|split; [exact HP' | split; [exact HT | split; [exact HF | exact HD]]]].
  eapply (hp_vm HP); [exact HA | exact Hvm].
Qed.


(* [comment removed for export] *)
Definition VSHf : list (Z * Z) := HID ++ HIDF.
Lemma AINV_f_lazy : forall Lc Lf B C K M mdl,
  AINV_f Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, in_shc SHC (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, in_shv VSHf (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (u a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV_f Lc Lf B C K M mdl').
Proof.
  intros Lc Lf B C K M mdl (HA & HP' & HT & HF & HD).
  destruct (hp_lazy HP _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & Hshc & Hblk & Hmat).
  exists AA. split; [exact Hwf|]. split; [exact Hminv|]. split; [exact Hshc|]. split; [|split].
  - intros a Hv. unfold in_shv, VSHf in Hv. apply existsb_exists in Hv as [[b n] [Hin Hz]]. cbn [fst snd] in Hz.
    apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
    apply (Hblk a b n); [|unfold in_shadow; lia].
    apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left | right]; apply in_app_iff; right; exact Hin.
  - intros a b n Hin Hsh. apply (Hblk a b n); [|exact Hsh].
    apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left | right]; apply in_app_iff; left; exact Hin.
  - intros mdl' Hminv' Hsame. split; [|split; [exact HP' | split; [exact HT | split; [exact HF | exact HD]]]].
    apply Hmat; [exact Hminv' | exact Hsame].
Qed.

(* [comment removed for export] *)
Lemma AINV_f_facts : forall Lc Lf B C K M mdl,
  AINV_f Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                    /\ (u (fst iv) + u (snd iv) <= g_img_lo G \/ g_img_hi G <= u (fst iv))) (m_vm_lazy mdl).
Proof. intros Lc Lf B C K M mdl (HA & _). exact (hp_facts HP _ _ _ _ _ _ _ HA). Qed.

(* [comment removed for export] *)
Lemma AINV_f_zone : forall Lc Lf B C K M mdl b m,
  AINV_f Lc Lf B C K M mdl -> In (b, m) Lc -> ablk_ok G b m /\ b mod 8 = 0.
Proof. intros Lc Lf B C K M mdl b m (HA & _) Hin. eapply (hp_zone HP); [exact HA | apply in_app_iff; left; exact Hin]. Qed.
Lemma AINV_f_fzone : forall Lc Lf B C K M mdl f m,
  AINV_f Lc Lf B C K M mdl -> In (f, m) Lf -> ablk_ok G f m /\ f mod 8 = 0 /\ m mod 8 = 0 /\ 8 <= m.
Proof. intros Lc Lf B C K M mdl f m (HA & _) Hin. eapply (hp_fzone HP); [exact HA | apply in_app_iff; left; exact Hin]. Qed.
Lemma AINV_f_disj : forall Lc Lf B C K M mdl L1 L2 b m b' m',
  AINV_f Lc Lf B C K M mdl -> Lc = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof.
  intros Lc Lf B C K M mdl L1 L2 b m b' m' (HA & _) HL Hin.
  eapply (hp_disj HP _ _ _ _ _ _ _ L1 (L2 ++ HID) b m b' m' HA).
  - rewrite HL. rewrite <- app_assoc. reflexivity.
  - rewrite app_assoc. apply in_app_iff. left. exact Hin.
Qed.

Lemma AINV_f_bfdisj : forall Lc Lf B C K M mdl b m f n,
  AINV_f Lc Lf B C K M mdl -> In (b, m) Lc -> In (f, n) Lf -> b + m <= f \/ f + n <= b.
Proof.
  intros Lc Lf B C K M mdl b m f n (HA & _) Hin Hin'. eapply (hp_bfdisj HP); [exact HA | apply in_app_iff; left; exact Hin | apply in_app_iff; left; exact Hin'].
Qed.
Lemma AINV_f_nolazy : forall Lc Lf B C K M mdl b n (a : word),
  AINV_f Lc Lf B C K M mdl -> In (b, n) (Lc ++ HID ++ Lf ++ HIDF) -> b <= u a < b + n -> lz mdl a = false.
Proof.
  intros Lc Lf B C K M mdl b n a (HA & _) Hin Hz. eapply (hp_nolazy HP); [exact HA | | exact Hz].
  rewrite <- app_assoc. exact Hin.
Qed.




End Frame.

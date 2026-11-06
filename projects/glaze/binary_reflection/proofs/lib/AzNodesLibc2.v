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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
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
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.

(* [comment removed for export] *)
Hypothesis AINV_facts : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                    /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl).
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Hypothesis AINV_nolazy : forall Lc Lf B C K M mdl b n (a : word),
  AINV Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> b <= u a < b + n -> lz mdl a = false.
Hypothesis AINV_perm_nolazy : forall Lc Lf B C K M mdl (a : word),
  AINV Lc Lf B C K M mdl -> in_wins PERMc (u a) -> lz mdl a = false.
Hypothesis AINV_top : forall Lc Lf B C K M mdl, AINV Lc Lf B C K M mdl -> CEIL_run <= SPTOPc.
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.        (* [comment removed for export] *)
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
(* [comment removed for export] *)
Hypothesis AINV_zone : forall Lc Lf B C K M mdl b n,
  AINV Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> ablk_ok G b n.
(* [comment removed for export] *)
Hypothesis PERM_vsh : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_pshadow PERMc z -> in_shv VSH z = true \/ in_shc SHC z = true.
Hypothesis PERM_bnd : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_wins PERMc z -> z < two47.
Hypothesis PERM_mem : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_wins PERMc z -> z < SHMAPLO \/ KHI <= z.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation hid := (GPS.hid SHC VSH).
#[local] Notation Mr := (GPS.Mr SHC VSH).
#[local] Notation owned := (GPS.owned SWIN PERMc SPTOPc).
#[local] Notation frame_kept := (AzKnowLib.frame_kept SWIN PERMc SPTOPc G).
#[local] Notation shz := (AzKnowLib.shz G).
#[local] Notation Mr_app := (AzNodesAlloc2.Mr_app A SWIN PERMc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy SWIN_img).
#[local] Notation hid_app_false := (AzNodesAlloc2.hid_app_false A SWIN PERMc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy SWIN_img).
#[local] Notation Mr_shadow := (AzNodesAlloc2.Mr_shadow SHC VSH G SHC_stack SHC_image).
#[local] Notation hid_shadow_false := (AzNodesAlloc2.hid_shadow_false SHC VSH G SHC_stack SHC_image).
#[local] Notation Mr_pshadow := (AzNodesAlloc2.Mr_pshadow PERMc SHC VSH AINV PERM_vsh).
#[local] Notation cfgF := (GPS.cfgF).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Mr_some : forall E cs mdl M (a : word) b, Mr E cs mdl M a = Some b -> M a = Some b.
Proof. intros E cs mdl M a b H. unfold GPS.Mr, mrestrict in H. destruct (hid E cs mdl a); [discriminate | exact H]. Qed.

Lemma in_blocks_app : forall L1 L2 z, in_blocks (L1 ++ L2) z <-> in_blocks L1 z \/ in_blocks L2 z.
Proof.
  intros L1 L2 z. unfold in_blocks. split.
  - intros (b & n & Hin & Hz). apply in_app_iff in Hin as [Hin|Hin]; [left | right]; exists b, n; split; assumption.
  - intros [(b & n & Hin & Hz)|(b & n & Hin & Hz)]; exists b, n; split; [apply in_app_iff; left; exact Hin | exact Hz | apply in_app_iff; right; exact Hin | exact Hz].
Qed.

Lemma in_blocks_ffus2 : forall E fk z,
  in_blocks (blocks_den E (map ffus fk)) z -> in_blocks (map fusable (blocks_den E fk)) z.
Proof.
  intros E fk z (b & n & Hin & Hz). unfold blocks_den in Hin.
  apply in_map_iff in Hin as [p [Heq Hin]]. apply in_map_iff in Hin as [[b0 n0] [Hf Hin0]]. subst p.
  assert (BAD : uE E (snd (ffus (b0, n0))) = 0 -> False).
  { intros H0. cbn [fst snd] in Heq. injection Heq as E1 E2. rewrite <- E2, H0 in Hz. lia. }
  assert (Z0 : uE E (ELit 0) = 0) by (unfold uE; cbn [edenot]; apply u64_lit; lia).
  unfold ffus in Heq, BAD. cbn [fst snd] in Heq, BAD.
  destruct n0 as [m| | | | | | |]; try (exfalso; apply BAD; exact Z0).
  destruct (Z.leb 8 m && Z.ltb m two64)%bool eqn:Hc; [|exfalso; apply BAD; exact Z0].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  cbn [fst snd] in Heq. injection Heq as E1 E2. subst b n.
  exists (uE E b0), (uE E (ELit m) - 8). split.
  - apply in_map_iff. exists (uE E b0, uE E (ELit m)). split; [reflexivity|]. unfold blocks_den. apply in_map_iff.
    exists (b0, ELit m). split; [reflexivity | exact Hin0].
  - revert Hz. unfold uE. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hid_no_seg : forall E cs mdl B C K M (a : word),
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  hid E cs mdl a = true -> seg_rom SEGS a = None.
Proof.
  intros E cs mdl B C K M a HA Hh. unfold GPS.hid in Hh. apply andb_prop in Hh as [Hl _].
  unfold lz, page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_facts _ _ _ _ _ _ _ HA) iv Hin) as (L0 & L1 & L2).
  rewrite A_img_hi, A_img_lo in L2. pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite (SEGS_out a) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_Mr_full : forall E cs mdl B C K M n (a : word) bs,
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  rdn SEGS (Mr E cs mdl M) a n = Some bs -> rdn SEGS M a n = Some bs.
Proof.
  intros E cs mdl B C K M n. induction n as [|n IH]; intros a bs HA H; [exact H|].
  cbn [rdn] in H |- *.
  assert (BYTE : forall b, (match Mr E cs mdl M a with Some b => Some b | None => seg_rom SEGS a end) = Some b ->
                           (match M a with Some b => Some b | None => seg_rom SEGS a end) = Some b).
  { intros b Hb. unfold GPS.Mr, mrestrict in Hb. destruct (hid E cs mdl a) eqn:Hh.
    - rewrite (hid_no_seg E cs mdl B C K M a HA Hh) in Hb. discriminate.
    - exact Hb. }
  destruct (match Mr E cs mdl M a with Some b => Some b | None => seg_rom SEGS a end) as [b|] eqn:Hb; [|discriminate].
  rewrite (BYTE b eq_refl).
  destruct (rdn SEGS (Mr E cs mdl M) (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate].
  rewrite (IH _ _ HA Hr). exact H.
Qed.

(* [comment removed for export] *)
Lemma mem_x_sound : forall E M k b off n lo hi z,
  know_ok SEGS E M k -> mem_x k b off n lo hi = true ->
  lo <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= hi ->
  estart E (SA b off) <= z <= estart E (SA b off) + elenZ E n -> nmem z.
Proof.
  intros E M k b off n lo hi z HK H Hlo Hhi Hz. unfold mem_x in H. unfold nmem.
  apply orb_prop in H as [H|H].
  - unfold mem_lit_x in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2].
    + apply Z.leb_le in H1. apply Z.leb_le in H2. left. lia.
    + apply Z.leb_le in H1. apply Z.ltb_lt in H2. right. lia.
  - apply andb_prop in H as [H Hap]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK Hap) as D.
    rewrite (estart_SA E (ELit 0) SHMAPLO) in D. cbn [edenot] in D. rewrite (u64_lit 0) in D by lia.
    rewrite (elenZ_lit E SHMAPLEN) in D by (unfold SHMAPLEN, SHMAPLO, KHI; lia).
    unfold SHMAPLEN, SHMAPLO, KHI, SB, two47 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ixlo2_sound : forall E M k e lo, know_ok SEGS E M k -> AzIface.xlo2 k e = Some lo -> lo <= u (edenot E e).
Proof.
  intros E M k e lo HK H. unfold AzIface.xlo2 in H. destruct (xrange2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj1 (xrange2_sound SEGS E M k e l h HK Hb)).
Qed.
Lemma ixhi2_sound : forall E M k e hi, know_ok SEGS E M k -> AzIface.xhi2 k e = Some hi -> u (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold AzIface.xhi2 in H. destruct (xrange2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj2 (xrange2_sound SEGS E M k e l h HK Hb)).
Qed.

(* [comment removed for export] *)
Lemma shvis_x_sound : forall E M cs b off n endhi,
  know_ok SEGS E M (kn cs) -> wins_den E (a_ghost cs) = PERMc -> GPS.floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (mobjs cs) = true ->
  shvis_x G (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (mobjs cs) b off n endhi = true ->
  0 <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= 2 ^ 64 -> estart E (SA b off) < 2 ^ 64 ->
  estart E (SA b off) + elenZ E n <= endhi ->
  nshvis PERMc G (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (estart E (SA b off)) (elenZ E n).
Proof.
  intros E M cs b off n endhi HK Hperm Hfl Hbf H E1 E2 E3 E4 z Hz. unfold shvis_x in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|Hst]|].
  2:{ (* [comment removed for export] *)
      destruct (AzKnowLib.srange_x_sound SEGS E M (kn cs) _ _ _ b off n HK Hfl Hst) as (S1 & S2 & S3 & S4).
      right; right; left. rewrite estart_SA in Hz. unfold elenZ in Hz. lia. }
  - apply existsb_exists in H as [[lb0 ln] [Hin Hxi]]. cbn [fst snd] in Hxi.
    destruct (split_lit lb0) as [lb lk] eqn:Hls.
    destruct (xinside_sound SEGS E M (kn cs) b off n lb lk ln HK Hxi) as [X1 X2].
    pose proof (proj1 (forallb_forall _ _) Hbf (lb0, ln) Hin) as HB. cbn [fst snd] in HB. rewrite Hls in HB.
    destruct (bflat_x_sound SEGS E M (kn cs) lb lk ln HK HB) as (F1 & F2 & F3). rewrite estart_SA in F1, F2, F3.
    pose proof (split_lit_denot E lb0 lb lk Hls) as Hd. rewrite !estart_SA in X1, X2. rewrite estart_SA in Hz, E1, E2, E3.
    pose proof (u64_range (edenot E lb)) as R1. pose proof (u64_range (edenot E ln)) as R2. unfold elenZ in *.
    assert (Hu : uE E lb0 = u (edenot E lb) + lk) by (unfold uE; rewrite Hd; apply u64_lit; lia).
    assert (IN : In (uE E lb0, uE E ln) (blocks_den E (mobjs cs))).
    { unfold blocks_den. apply in_map_iff. exists (lb0, ln). split; [reflexivity | exact Hin]. }
    unfold mobjs in IN. rewrite !AzNodesAlloc.blocks_den_app in IN.
    apply in_app_iff in IN as [IN|IN]; [|apply in_app_iff in IN as [IN|IN]].
    + left. apply in_blocks_app. left. exists (uE E lb0), (uE E ln). split; [exact IN|]. rewrite Hu. unfold uE. lia.
    + left. apply in_blocks_app. right. apply (in_blocks_ffus2 E (a_fake cs) z). exists (uE E lb0), (uE E ln). split; [exact IN|]. rewrite Hu. unfold uE. lia.
    + right; left. unfold blocks_den in IN. apply in_map_iff in IN as [[p0 q0] [Heq Hpq]]. cbn [fst snd] in Heq. injection Heq as Ep Eq.
      exists (uE E p0), (uE E p0 + uE E q0). split.
      * rewrite <- Hperm. unfold wins_den. apply in_map_iff. exists (p0, q0). split; [reflexivity | exact Hpq].
      * rewrite Ep, Eq, Hu. unfold uE. lia.
  - destruct (xlo (kn cs) (eaddz b off)) as [lo|] eqn:Hlo; [|discriminate].
    pose proof (xlo_sound SEGS E M (kn cs) _ lo HK Hlo) as B1.
    assert (EA : u (edenot E (eaddz b off)) = estart E (SA b off)).
    { rewrite estart_SA. pose proof (uE_eaddz E b off). unfold uE in H0. rewrite estart_SA in E1, E2, E3. unfold elenZ in E2.
      pose proof (u64_range (edenot E n)). apply H0. lia. }
    rewrite EA in B1. unfold elenZ in *.
    apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
    right; right; right. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation bflatb k := (fun bl : expr * expr => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)).

(* [comment removed for export] *)
Lemma mend_hi_sound : forall E M k e ne ehi nhi,
  know_ok SEGS E M k -> uE E e <= ehi -> uE E ne <= nhi ->
  uE E e + uE E ne < 2 ^ 64 -> uE E e + uE E ne <= mend_hi k e ne ehi nhi.
Proof.
  intros E M k e ne ehi nhi HK B1 B2 Hnw. unfold mend_hi.
  destruct (xrange2 k (eadd e ne)) as [[jl j]|] eqn:Hj; [|unfold uE in *; lia].
  pose proof (xrange2_sound SEGS E M k _ jl j HK Hj) as [_ B3]. pose proof (uE_eadd_nowrap E e ne Hnw) as EQ. unfold uE in *. rewrite EQ in B3. lia.
Qed.

Lemma mem_ok_sound : forall entry needsrc apart cs ret db dk sb sk nlo nhi kh E fx R M model,
  cs_ok E cs fx R M model ->
  mem_ok A nx0 G entry needsrc apart cs = Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) ->
  let MR := Mr E cs model M in
  let dst := estart E (SA db dk) in let src := estart E (SA sb sk) in let n := uE E (reg cs 12) in
  let Lc := blocks_den E (a_vis cs) in let Lf := blocks_den E (a_fake cs) in
  exists spb spk,
  pc cs = entry /\ fresh_ok nx0 cs = true /\ length (s_regs (a_ss cs)) = 32%nat
  /\ ncall_pre SEGS SPTOPc G R M ret (uE E (reg cs 2)) MSTK_M
  /\ split_lit (reg cs 2) = (spb, spk) /\ uE E (reg cs 2) = uE E spb + spk
  /\ forallb (bflatb (kn cs)) (a_vis cs ++ a_fake cs ++ a_ghost cs) = true
  /\ forallb (bflatb (kn cs)) (mobjs cs) = true
  /\ split_lit (reg cs 10) = (db, dk) /\ split_lit (reg cs 11) = (sb, sk)
  /\ uE E (reg cs 10) = dst /\ u (getr R (Z_to_bv 5 10)) = dst /\ u (getr R (Z_to_bv 5 12)) = n
  /\ u (getr R (Z_to_bv 5 11)) = uE E (reg cs 11)
  /\ xlo (kn cs) (reg cs 12) = Some nlo /\ xhi (kn cs) (reg cs 12) = Some nhi /\ 0 <= nlo <= n /\ n <= nhi <= 2 ^ 40
  /\ elenZ E (reg cs 12) = n
  /\ ndst_pre SEGS SWIN PERMc SPTOPc G M Lc Lf dst n
  /\ (0 <= dst /\ dst + n <= two47)
  /\ (forall a : word, dst <= u a < dst + n -> ~ scratch (uE E (reg cs 2)) MSTK_M a)
  /\ (forall m B C K M0, AINV Lc Lf B C K M0 m -> forall a : word, dst <= u a < dst + n -> hid E cs m a = false)
  /\ (forall a : word, dst <= u a < dst + n -> u a < SB \/ HEAPLO <= u a)
  /\ (needsrc = true -> uE E (reg cs 11) = src /\ (0 <= src /\ src + n <= two47)
                        /\ nmem src /\ nmem (src + n) /\ nacc M src n /\ nshvis PERMc G Lc Lf src n
                        /\ (forall a : word, src <= u a < src + n -> ~ scratch (uE E (reg cs 2)) MSTK_M a)
                        /\ (apart = true -> dst + n <= src \/ src + n <= dst)
                        /\ (apart = false -> dst <> src \/ (forall i, 0 <= i < n -> M (Z_to_bv 64 (src + i)) <> None)))   (* [comment removed for export] *)
  /\ exists k0, kh = kn_havoc k0 db dk (reg cs 12) /\ know_ok SEGS E MR k0
     /\ forallb (bflatb kh) (a_vis cs ++ a_fake cs ++ a_ghost cs) = true.
Proof. pose proof sfloor_ge as SFG_.
  intros entry needsrc apart cs ret db dk sb sk nlo nhi kh E fx R M model HC H. cbv zeta.
  rewrite mem_ok_eq in H. unfold mem_ok_ref in H. rewrite havocD_eq in H.   (* [comment removed for export] *)
  destruct (call_ok_stk nx0 G MSTK_M entry cs) as [ret0|] eqn:Hco; [|discriminate].
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G MSTK_M entry cs ret0 E fx R M model
                ltac:(unfold MSTK_M; lia) HC Hco) as CO.
  cbv zeta in H. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  destruct (split_lit (reg cs 10)) as [db0 dk0] eqn:Hsd. destruct (split_lit (reg cs 11)) as [sb0 sk0] eqn:Hss.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo0|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi0|] eqn:Hnhi; [|discriminate].
  destruct (AzIface.xlo2 (kn cs) (reg cs 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (AzIface.xhi2 (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  cbv zeta in H.
  destruct (Z.eqb nhi0 0) eqn:Hz0.
  { (* [comment removed for export] *)
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hbfh; [|discriminate] end.
    injection H as -> -> -> -> -> -> -> <-.
    repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
    (* [comment removed for export] *)
    apply Z.leb_le in Hc. apply Z.eqb_eq in Hz0. subst nhi.
    pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
    set (MR := Mr E cs model M) in HK.
    pose proof (xlo_sound SEGS E MR (kn cs) (reg cs 12) nlo HK Hnlo) as Nlo.
    pose proof (xhi_sound SEGS E MR (kn cs) (reg cs 12) 0 HK Hnhi) as Nhi.
    pose proof (ixlo2_sound E MR (kn cs) (reg cs 10) dlo HK Hdlo) as Dlo.
    pose proof (ixhi2_sound E MR (kn cs) (reg cs 10) dhi HK Hdhi) as Dhi.
    pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10.
    pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11.
    pose proof (reg_sound E cs R 12 HR ltac:(lia)) as R12.
    pose proof (u64_range (edenot E (reg cs 12))) as NR.
    assert (N0 : uE E (reg cs 12) = 0) by (unfold uE in *; lia).
    assert (EnZ : elenZ E (reg cs 12) = 0) by exact N0.
    destruct (bflat_x_sound SEGS E MR (kn cs) db dk (reg cs 12) HK X1) as (B1 & B2 & B3).
    pose proof (split_lit_denot E (reg cs 10) db dk Hsd) as Hdd.
    assert (Hdst : uE E (reg cs 10) = estart E (SA db dk)).
    { unfold uE. rewrite Hdd, estart_SA. rewrite estart_SA in B1, B3. apply u64_lit. lia. }
    rewrite N0. remember (estart E (SA db dk)) as dst eqn:Edst.
    pose proof (mend_hi_sound E MR (kn cs) (reg cs 10) (reg cs 12) dhi 0 HK Dhi Nhi ltac:(rewrite Hdst, N0; lia)) as DE.
    rewrite Hdst, N0 in DE.
    assert (DR : dlo <= dst /\ dst <= dhi) by (rewrite <- Hdst; unfold uE in *; lia).
    assert (NMD : nmem dst) by (apply (mem_x_sound E MR (kn cs) db dk (reg cs 12) dlo _ _ HK X2); rewrite <- ?Edst, ?EnZ; lia).
    exists spb, spk.
    split; [exact Hpc|]. split; [exact Hfresh|]. split; [exact Hlen|].
    split.
    { unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
      split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha. }
    split; [reflexivity|]. split; [exact Hspv|]. split; [exact Hflat|]. split; [exact X0|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hdst|]. split; [rewrite <- Hdst; unfold uE; rewrite <- R10; reflexivity|]. split; [rewrite <- N0; unfold uE; rewrite <- R12; reflexivity|].
    split; [unfold uE; rewrite <- R11; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [exact EnZ|].
    split.
    { unfold ndst_pre. split; [lia|]. split; [exact NMD|]. split; [rewrite Z.add_0_r; exact NMD|].
      split; [intros z Hz; lia|]. split; [intros z Hz; lia|]. intros a Ha. lia. }
    split; [unfold nmem, two47, SB, KHI in *; lia|].
    split; [intros a Ha; lia|].
    split; [intros m B C K M0 _ a Ha; lia|].
    split; [intros a Ha; lia|].
    split.
    { intros Hns. subst needsrc. cbn [negb orb] in X.
      destruct (AzIface.xlo2 (kn cs) (reg cs 11)) as [slo|] eqn:Hslo; [|discriminate].
      destruct (AzIface.xhi2 (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
      apply andb_prop in X as [XM XB].
      pose proof (ixlo2_sound E MR (kn cs) (reg cs 11) slo HK Hslo) as Slo.
      pose proof (ixhi2_sound E MR (kn cs) (reg cs 11) shi HK Hshi) as Shi.
      destruct (bflat_x_sound SEGS E MR (kn cs) sb sk (reg cs 12) HK XB) as (S1 & S2 & S3).
      pose proof (split_lit_denot E (reg cs 11) sb sk Hss) as Hsd2.
      assert (Hsrc : uE E (reg cs 11) = estart E (SA sb sk)).
      { unfold uE. rewrite Hsd2, estart_SA. rewrite estart_SA in S1, S3. apply u64_lit. lia. }
      pose proof (mend_hi_sound E MR (kn cs) (reg cs 11) (reg cs 12) shi 0 HK Shi Nhi ltac:(rewrite Hsrc, N0; lia)) as SE.
      rewrite Hsrc, N0 in SE.
      assert (NMS : nmem (estart E (SA sb sk))).
      { apply (mem_x_sound E MR (kn cs) sb sk (reg cs 12) slo _ _ HK XM); rewrite ?EnZ; [rewrite <- Hsrc; unfold uE in *; lia | exact SE | lia]. }
      split; [exact Hsrc|].
      split; [unfold nmem, two47, SB, KHI in *; lia|].
      split; [exact NMS|]. split; [rewrite Z.add_0_r; exact NMS|].
      split; [intros z Hz; lia|]. split; [intros z Hz; lia|]. split; [intros a Ha; lia|].
      split; [intros _; lia|]. intros _. right. intros i Hi. lia. }
    exists (kn cs). split; [reflexivity|]. split; [exact HK|]. exact Hbfh. }
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  cbv zeta in H. match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hbfh; [|discriminate] end.
  injection H as -> -> -> -> -> -> -> <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename Hc into Hnlo0.
  (* [comment removed for export] *)
  rename X0 into XSC. rename X1 into X0. rename X2 into X1. rename X3 into X2. rename X4 into X3. rename X5 into X4. rename X6 into X5. rename X7 into X6.
  apply Z.leb_le in Hnlo0. apply Z.leb_le in X6.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in HK.
  pose proof (xlo_sound SEGS E MR (kn cs) (reg cs 12) nlo HK Hnlo) as Nlo.
  pose proof (xhi_sound SEGS E MR (kn cs) (reg cs 12) nhi HK Hnhi) as Nhi.
  pose proof (ixlo2_sound E MR (kn cs) (reg cs 10) dlo HK Hdlo) as Dlo.
  pose proof (ixhi2_sound E MR (kn cs) (reg cs 10) dhi HK Hdhi) as Dhi.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10.
  pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11.
  pose proof (reg_sound E cs R 12 HR ltac:(lia)) as R12.
  destruct (kwritable_x_sound SEGS E MR (kn cs) (kn cs) db dk (reg cs 12) HK HK X2) as (Wst & Wlo & Whi).
  pose proof (split_lit_denot E (reg cs 10) db dk Hsd) as Hdd.
  pose proof (u64_range (edenot E (reg cs 12))) as NR.
  pose proof (kshok_x_sound SEGS A G A_img_hi A_img_lo SEGS_in_hull G_img_shlo E MR (kn cs) db dk (reg cs 12) HK X1) as KSD. cbn [kentry_ok] in KSD.
  destruct KSD as (KFD & K47D & KSD).
  assert (Hdst : uE E (reg cs 10) = estart E (SA db dk)).
  { unfold uE. rewrite Hdd, estart_SA. destruct KFD as (F1 & F2 & F3 & F4). rewrite estart_SA in F1, F2. apply u64_lit. lia. }
  remember (estart E (SA db dk)) as dst eqn:Edst. remember (uE E (reg cs 12)) as n eqn:En.
  assert (EnZ : elenZ E (reg cs 12) = n) by (rewrite En; reflexivity).
  assert (OWN : forall a : word, dst <= u a < dst + n -> owned (blocks_den E (a_vis cs) ++ map fusable (blocks_den E (a_fake cs))) a).
  { intros a Ha.
    pose proof (owned_x_sound3 SEGS PERMc SPTOPc E MR (kn cs) (a_vis cs ++ map ffus (a_fake cs)) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) db dk (reg cs 12) a
                  HK ltac:(unfold mobjs in X4; first [rewrite <- app_assoc | rewrite app_assoc]; exact X4) (co_perm HC) (co_top HC) (co_floor HC)
                  ltac:(unfold mobjs in X3; first [rewrite <- app_assoc | rewrite app_assoc]; exact X3) ltac:(rewrite <- Edst, EnZ; exact Ha)) as O3.
    unfold owned3 in O3. unfold GPS.owned.
    destruct O3 as [Hb|[Hp|Hs]]; [| right; left; exact Hp | right; right; left; exact Hs].
    left. rewrite AzNodesAlloc.blocks_den_app in Hb. apply in_blocks_app in Hb as [Hb|Hb]; apply in_blocks_app; [left; exact Hb | right].
    exact (in_blocks_ffus2 E (a_fake cs) (u a) Hb). }
  assert (VIS : forall m B C K M0, AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M0 m ->
                forall a : word, dst <= u a < dst + n -> hid E cs m a = false).
  { intros m B C K M0 HA a Ha. eapply hid_app_false; [exact HA|].
    destruct (OWN a Ha) as [Hb|[Hp|[Hs|Hw]]]; [| right; left; exact Hp | right; right; left; lia | right; right; right; left; exact Hw].
    apply in_blocks_app in Hb as [Hb|Hb]; [left; apply in_blocks_app; left; exact Hb|].
    left. apply in_blocks_app. right. destruct Hb as (b0 & m0 & Hin & Hz). apply in_map_iff in Hin as [[b1 m1] [Heq Hin]].
    unfold fusable in Heq. cbn [fst snd] in Heq. injection Heq as <- <-. exists b1, m1. split; [exact Hin | lia]. }
  assert (OFFSH : forall a : word, dst <= u a < dst + n -> u a < SB \/ HEAPLO <= u a).
  { intros a Ha. pose proof GlzConst.ceil_lo as CL. pose proof G_img_shlo as GSL. destruct (OWN a Ha) as [Hb|[Hp|[Hs|Hw]]].
    - apply in_blocks_app in Hb as [Hb|Hb].
      + destruct Hb as (b0 & m0 & Hin & Hz). pose proof (AINV_zone _ _ _ _ _ _ _ b0 m0 (co_ainv HC) ltac:(apply in_app_iff; left; exact Hin)) as (Z1 & Z2 & Z3 & Z4).
        unfold SHMAPLO, KHI, HEAPLO, SB in *. lia.
      + destruct Hb as (b0 & m0 & Hin & Hz). apply in_map_iff in Hin as [[b1 m1] [Heq Hin]]. unfold fusable in Heq. cbn [fst snd] in Heq.
        injection Heq as <- <-. pose proof (AINV_zone _ _ _ _ _ _ _ b1 m1 (co_ainv HC) ltac:(apply in_app_iff; right; exact Hin)) as (Z1 & Z2 & Z3 & Z4).
        unfold SHMAPLO, KHI, HEAPLO, SB in *. lia.
    - pose proof (PERM_mem _ _ _ _ _ _ _ _ (co_ainv HC) Hp). unfold SHMAPLO, KHI, HEAPLO, SB in *. lia.
    - right. unfold HEAPLO in *. lia.
    - left. destruct Hw as (lo & hi & Hin & Hz). pose proof (SWIN_img lo hi Hin). unfold SHMAPLO, SB in *. lia. }
  exists spb, spk.
  split; [exact Hpc|]. split; [exact Hfresh|]. split; [exact Hlen|].
  split.
  { unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha. }
  split; [reflexivity|]. split; [exact Hspv|]. split; [exact Hflat|]. split; [exact X4|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hdst|]. split; [rewrite <- Hdst; unfold uE; rewrite <- R10; reflexivity|]. split; [rewrite En; unfold uE; rewrite <- R12; reflexivity|].
  split; [unfold uE; rewrite <- R11; reflexivity|].
  assert (NB : 0 <= nlo <= n /\ n <= nhi <= 2 ^ 40) by (subst n; unfold uE in *; lia).
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [exact EnZ|].
  assert (DE : dst + n <= mend_hi (kn cs) (reg cs 10) (reg cs 12) dhi nhi).
  { rewrite <- Hdst, En. apply (mend_hi_sound E MR (kn cs)); [exact HK | exact Dhi | exact Nhi |].
    rewrite Hdst, <- En. destruct KFD as (F1 & F2 & F3 & F4). rewrite <- ?Edst, ?EnZ in K47D. lia. }
  split.
  { (* [comment removed for export] *)
    unfold ndst_pre. split; [lia|].
    assert (DR : dlo <= dst /\ dst <= dhi) by (rewrite <- Hdst; unfold uE in *; lia).
    split; [apply (mem_x_sound E MR (kn cs) db dk (reg cs 12) dlo _ _ HK X5); rewrite <- ?Edst, ?EnZ; lia|].
    split; [apply (mem_x_sound E MR (kn cs) db dk (reg cs 12) dlo _ _ HK X5); rewrite <- ?Edst, ?EnZ; lia|].
    split.
    { (* [comment removed for export] *)
      intros z Hz. rewrite <- ?Edst, ?EnZ in KSD. destruct (KSD z Hz) as (bt & Hbt & Hv).
      exists bt. split; [exact (Mr_some _ _ _ _ _ _ Hbt) | exact Hv]. }
    split.
    { destruct KFD as (F1 & F2 & F3 & F4). rewrite <- ?Edst, ?EnZ in F1. rewrite <- ?Edst, ?EnZ in F2. rewrite <- ?Edst, ?EnZ in F4.
      pose proof (shvis_x_sound E MR cs db dk (reg cs 12) _ HK (co_perm HC) (co_floor HC) X4 X0) as SV. rewrite <- ?Edst, ?EnZ in SV. exact (SV F1 F4 F2 DE). }
    intros a Ha. split; [unfold ndst; exact (OWN a Ha)|].
    pose proof (VIS model _ _ _ _ (co_ainv HC) a Ha) as HH.
    rewrite <- (store_ok1_Mr SEGS SHC VSH E cs model M a HH). fold MR.
    rewrite <- ?Edst, ?EnZ in Wst, Wlo, Whi. pose proof (u64_range a) as AR.
    replace a with (Z_to_bv 64 (dst + (u a - dst))) by (apply bv_eq; rewrite u64_lit; lia).
    eapply (store_ok_bytes SEGS MR (Z_to_bv 64 dst) (Z.to_nat n)); [rewrite u64_lit by lia; lia | apply Wst; lia | rewrite !u64_lit by lia; lia]. }
  split; [destruct KFD as (F1 & F2 & F3 & F4); rewrite <- ?Edst, ?EnZ in F1; rewrite <- ?Edst, ?EnZ in K47D; unfold two47; lia|].
  split.
  { intros a Ha Hs. unfold scratch in Hs. apply orb_prop in XSC as [XSC|XSC].
    - pose proof (ranges_apart_x_sound SEGS E MR (kn cs) db dk (reg cs 12) spb (spk - MSTK_M) (ELit MSTK_M) HK XSC) as AP0.
      rewrite <- ?Edst, ?EnZ in AP0. rewrite estart_SA in AP0. rewrite (APS.elenZ_lit E MSTK_M) in AP0 by (unfold MSTK_M; lia).
      unfold uE in Hspv, Hs. lia.
    - (* [comment removed for export] *)
      unfold below_scratch_x in XSC. destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo2; [|discriminate]. apply Z.leb_le in XSC.
      pose proof (xlo_sound SEGS E MR (kn cs) (reg cs 2) splo HK Hsplo2) as SPL. unfold uE in Hs. lia. }
  split; [exact VIS|].
  split; [exact OFFSH|].
  split.
  { intros Hns. subst needsrc. cbn [negb orb] in X.
    destruct (AzIface.xlo2 (kn cs) (reg cs 11)) as [slo|] eqn:Hslo; [|discriminate].
    destruct (AzIface.xhi2 (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
    repeat match type of X with (_ && _)%bool = true => apply andb_prop in X as [X ?Y] end.
    (* [comment removed for export] *)
    rename Y into YMV. rename Y0 into Y. rename Y1 into YSC. rename Y2 into Y0. rename Y3 into Y1.
    pose proof (ixlo2_sound E MR (kn cs) (reg cs 11) slo HK Hslo) as Slo.
    pose proof (ixhi2_sound E MR (kn cs) (reg cs 11) shi HK Hshi) as Shi.
    pose proof (kshok_x_sound SEGS A G A_img_hi A_img_lo SEGS_in_hull G_img_shlo E MR (kn cs) sb sk (reg cs 12) HK Y1) as KS. cbn [kentry_ok] in KS.
    destruct KS as (KF & K47 & KS).
    pose proof (split_lit_denot E (reg cs 11) sb sk Hss) as Hsd2.
    assert (Hsrc : uE E (reg cs 11) = estart E (SA sb sk)).
    { unfold uE. rewrite Hsd2, estart_SA. destruct KF as (F1 & F2 & F3 & F4). rewrite estart_SA in F1, F2. apply u64_lit. lia. }
    assert (SR : slo <= estart E (SA sb sk) /\ estart E (SA sb sk) <= shi) by (rewrite <- Hsrc; unfold uE in *; lia).
    split; [exact Hsrc|].
    split; [destruct KF as (F1 & F2 & F3 & F4); rewrite ?EnZ in K47; unfold two47; lia|].
    assert (SE : estart E (SA sb sk) + n <= mend_hi (kn cs) (reg cs 11) (reg cs 12) shi nhi).
    { rewrite <- Hsrc, En. apply (mend_hi_sound E MR (kn cs)); [exact HK | exact Shi | exact Nhi |].
      rewrite Hsrc, <- En. rewrite ?EnZ in K47. lia. }
    split; [apply (mem_x_sound E MR (kn cs) sb sk (reg cs 12) slo _ _ HK X); rewrite <- ?Esrc, ?EnZ; lia|].
    split; [apply (mem_x_sound E MR (kn cs) sb sk (reg cs 12) slo _ _ HK X); rewrite <- ?Esrc, ?EnZ; lia|].
    split.
    { intros z Hz. rewrite EnZ in KS. destruct (KS z Hz) as (bt & Hbt & Hv).
      exists bt. split; [exact (Mr_some _ _ _ _ _ _ Hbt) | exact Hv]. }
    split.
    { destruct KF as (F1 & F2 & F3 & F4). rewrite ?EnZ in F4.
      pose proof (shvis_x_sound E MR cs sb sk (reg cs 12) _ HK (co_perm HC) (co_floor HC) X4 Y0) as SV. rewrite ?EnZ in SV. exact (SV F1 F4 F2 SE). }
    split.
    { intros a Ha Hs. unfold scratch in Hs. apply orb_prop in YSC as [YSC|YSC].
      - pose proof (ranges_apart_x_sound SEGS E MR (kn cs) sb sk (reg cs 12) spb (spk - MSTK_M) (ELit MSTK_M) HK YSC) as AP0.
        rewrite ?EnZ in AP0. rewrite (estart_SA E spb) in AP0. rewrite (APS.elenZ_lit E MSTK_M) in AP0 by (unfold MSTK_M; lia).
        unfold uE in Hspv, Hs. lia.
      - (* [comment removed for export] *)
        unfold below_scratch_x in YSC. destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo2; [|discriminate]. apply Z.leb_le in YSC.
        pose proof (xlo_sound SEGS E MR (kn cs) (reg cs 2) splo HK Hsplo2) as SPL. unfold uE in Hs. lia. }
    split.
    { intros Hap. subst apart. cbn [negb orb] in Y.
      pose proof (ranges_apart_x_sound SEGS E MR (kn cs) db dk (reg cs 12) sb sk (reg cs 12) HK Y) as AP'.
      rewrite <- ?Edst, ?EnZ in AP'. lia. }
    (* [comment removed for export] *)
    intros Hap. subst apart. cbn [orb] in YMV. apply orb_prop in YMV as [YMV|YMV].
    - left. unfold neq_x in YMV.
      assert (ES : estart E (SA sb sk) = bv_unsigned (edenot E sb) + sk) by (rewrite estart_SA; reflexivity).
      assert (ED : dst = bv_unsigned (edenot E db) + dk) by (rewrite Edst, estart_SA; reflexivity).
      rewrite ES, ED.
      apply orb_prop in YMV as [YMV|L3].
      + apply orb_prop in YMV as [L|L]; pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK L) as LL; cbn [xt_den] in LL; lia.
      + (* [comment removed for export] *)
        pose proof (ranges_apart_x_sound SEGS E MR (kn cs) _ _ _ _ _ _ HK L3) as D. rewrite !estart_SA in D. cbn [a_base a_off] in D.
        rewrite !(elenZ_lit E 1) in D by lia. lia.
    - right. destruct (kn_readable_x_sound2 SEGS E MR (kn cs) sb sk (reg cs 12) HK YMV) as (_ & _ & RD). rewrite EnZ in RD.
      intros i Hi HM. apply (RD i Hi). unfold MR, GPS.Mr, mrestrict.
      destruct (GPS.hid SHC VSH E cs model (Z_to_bv 64 (estart E (SA sb sk) + i))); [reflexivity | exact HM]. }
  exists k0. split; [reflexivity|]. split; [exact (k0_sound SEGS A E MR (kn cs) db dk (reg cs 12) (reg cs 10) k0 HK Hk0)|].
  exact Hbfh.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_sound_gen : forall E cs fx R M model mdl' M' B' C' K' kh (dst n : Z) spb spk K,
  cs_ok E cs fx R M model ->
  (forall Mh : word -> option byte,
      (forall x : word, u x < dst \/ dst + n <= u x -> Mh x = Mr E cs model M x) -> mem_grows (Mr E cs model M) Mh -> know_ok SEGS E Mh kh) ->
  forallb (bflatb kh) (a_vis cs ++ a_fake cs ++ a_ghost cs) = true ->
  split_lit (reg cs 2) = (spb, spk) -> uE E (reg cs 2) = uE E spb + spk -> SFLOOR + MSTK_M <= uE E (reg cs 2) ->
  0 <= dst -> dst + n <= 2 ^ 64 ->
  (forall a : word, dst <= u a < dst + n -> u a < SB \/ HEAPLO <= u a) ->
  (forall m B C K M0, AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M0 m ->
     forall a : word, dst <= u a < dst + n -> hid E cs m a = false) ->
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B' C' K' M' mdl' ->
  (forall a : word, dst <= u a < dst + n -> M' a <> None) ->
  (forall a : word, M' a <> M a -> (dst <= u a < dst + n) \/ scratch (uE E (reg cs 2)) MSTK_M a) ->
  scratch_ok SEGS M' (uE E (reg cs 2)) MSTK_M ->
  In K (mem_kept G cs kh (nxt cs)) -> kentry_ok SEGS E (Mr E cs mdl' M') K.
Proof. pose proof sfloor_ge as SFG_.
  intros E cs fx R M model mdl' M' B' C' K' kh dst n spb spk K HC HKH Hflat Hsp Hspv Hsplo D0 D1 OFFSH VIS HA' Hdef Hfr Hscr Hin.
  pose proof (co_know HC) as HK. pose proof (co_ainv HC) as HA.
  set (MR := Mr E cs model M) in *. set (MRp := Mr E cs mdl' M').
  set (ind := fun x : word => (Z.leb dst (u x) && Z.ltb (u x) (dst + n))%bool).
  set (MRh := fun x : word => if ind x then MRp x else MR x).
  assert (IND : forall x : word, ind x = true <-> dst <= u x < dst + n).
  { intros x. unfold ind. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  (* [comment removed for export] *)
  assert (APPVIS : forall m B0 C0 K0 M0 (a : word), AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B0 C0 K0 M0 m ->
            frame_kept MSTK_M (blocks_den E (a_vis cs ++ a_fake cs)) (u (edenot E (reg cs 2))) a -> hid E cs m a = false).
  { intros m B0 C0 K0 M0 a HAm Hk. pose proof (AINV_top _ _ _ _ _ _ _ HAm) as HT. eapply hid_app_false; [exact HAm|].
    destruct Hk as [[Ho _]|[[Hi _]|[[Ht _]|Hge]]].
    - destruct Ho as [Hb|[Hp|[Hs|Hw]]]; [| right; left; exact Hp | right; right; left; lia | right; right; right; left; exact Hw].
      rewrite !AzNodesAlloc.blocks_den_app in Hb. left. exact Hb.
    - right; right; right; right. lia.
    - right; right; left. lia.
    - right; right; left. unfold uE, MSTK_M in *. lia. }
  assert (KH : know_ok SEGS E MR kh).
  { apply HKH; [intros; reflexivity | apply mem_grows_refl]. }
  eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G MSTK_M E MRh MRp kh
            (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne kh (a_ghost cs))
            (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk (nxt cs) K ltac:(unfold MSTK_M; lia)).
  - (* [comment removed for export] *)
    apply HKH.
    + intros x Hx. unfold MRh. destruct (ind x) eqn:Hi; [|reflexivity].
      apply IND in Hi. lia.
    + intros x Hx. unfold MRh. destruct (ind x) eqn:Hi; [|exact Hx]. apply IND in Hi.
      unfold MRp, GPS.Mr. rewrite (mrestrict_visible _ _ _ (VIS mdl' _ _ _ _ HA' x Hi)). exact (Hdef x Hi).
  - first [rewrite <- app_assoc | rewrite app_assoc]; exact Hflat.
  - exact (co_perm HC).
  - exact (co_top HC).
  - exact Hsp.
  - pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
  - exact (co_floor HC).
  - (* [comment removed for export] *)
    intros a Hk. unfold MRh. destruct (ind a) eqn:Hi; [reflexivity|].
    assert (NI : ~ (dst <= u a < dst + n)) by (intros Hc; apply IND in Hc; rewrite Hc in Hi; discriminate).
    unfold MRp, MR, GPS.Mr.
    rewrite (mrestrict_visible _ _ _ (APPVIS mdl' _ _ _ _ a HA' Hk)).
    rewrite (mrestrict_visible _ _ _ (APPVIS model _ _ _ _ a HA Hk)).
    destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|].
    exfalso. destruct (Hfr a Hne) as [Hd|Hs]; [exact (NI Hd)|].
    unfold scratch in Hs. pose proof G_img_ceil. destruct Hk as [[Ho [Hns _]]|[[Hi2 _]|[[Ht Hle]|Hge]]]; unfold uE, MSTK_M in *; lia.
  - (* [comment removed for export] *)
    intros a Ha. unfold MRp.
    assert (HH : hid E cs mdl' a = false).
    { eapply hid_app_false; [exact HA'|]. right; right; left. unfold uE in *. lia. }
    unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite store_ok1_Mr by exact HH. apply Hscr. unfold scratch, uE in *. lia.
  - (* [comment removed for export] *)
    intros a Hew HMh. assert (Hai : g_img_lo G <= u a < g_img_hi G) by (unfold errw in Hew; pose proof G_errno_img; lia).
    unfold MRh in HMh. unfold MRp, MR, GPS.Mr in HMh |- *.
    rewrite (mrestrict_visible _ _ _ (hid_app_false _ _ _ _ _ _ _ a HA' (or_intror (or_intror (or_intror (or_intror Hai)))))).
    destruct (ind a) eqn:Hia; rewrite ?Hia in HMh.
    + rewrite (mrestrict_visible _ _ _ (hid_app_false _ _ _ _ _ _ _ a HA' (or_intror (or_intror (or_intror (or_intror Hai)))))) in HMh. exact HMh.
    + rewrite (mrestrict_visible _ _ _ (hid_app_false _ _ _ _ _ _ _ a HA (or_intror (or_intror (or_intror (or_intror Hai)))))) in HMh.
      destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact HMh|].
      destruct (Hfr a Hne) as [Hd|Hs]; [exfalso; apply IND in Hd; rewrite Hd in Hia; discriminate Hia | exact (proj1 (Hscr a Hs))].
  - (* [comment removed for export] *)
    intros a Hz. unfold MRh.
    assert (Hz3 : (in_lshadow (blocks_den E (a_vis cs ++ a_fake cs)) (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a)) \/ in_pshadow PERMc (u a)).
    { destruct Hz as [Hl|[Hs|Hi2]]; [| left; right; left | left; right; right; exact Hi2].
      - destruct Hl as (bb & nn & Hinb & Hsh). rewrite app_assoc, AzNodesAlloc.blocks_den_app in Hinb.
        apply in_app_iff in Hinb as [Hinb|Hinb]; [left; left; exists bb, nn; split; [exact Hinb | exact Hsh]|].
        right. destruct (ghosts_ne_in SEGS PERMc E MR _ (a_ghost cs) bb nn KH (co_perm HC) Hinb) as [Hw Hm].
        exists bb, (bb + nn). split; [exact Hw|]. split; [lia|]. replace (bb + nn - bb) with nn by lia. exact Hsh.
      - unfold in_sshadow. destruct Hs as [S1 S2]. split; [|exact S2].
        assert (SB + CEIL_run / 8 <= SB + uE E (reg cs 2) / 8) by (apply Z.add_le_mono_l; apply Z.div_le_mono; unfold MSTK_M in *; lia). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (LOW : u a < HEAPLO /\ SB <= u a).
    { pose proof G_img_shlo as GS. pose proof G_img_hull as GH. pose proof (u64_range (edenot E (reg cs 2))) as SPR.
      pose proof GlzConst.ceil_lo as CL0. pose proof GlzConst.ceil_hi as CH0. unfold GlzConst.PTRHI in CH0.
      destruct Hz3 as [[Hl|[Hs|Hi]]|Hp].
      - destruct Hl as (bb & nn & Hinb & Hsh). rewrite AzNodesAlloc.blocks_den_app in Hinb.
        pose proof (AINV_zone _ _ _ _ _ _ _ bb nn HA Hinb) as (Z1 & Z2 & Z3 & Z4). unfold GlzConst.PTRLO in Z1. unfold in_shadow in Hsh.
        clear - Z1 Z2 Hsh CL0 CH0. unfold HEAPLO, SB in *. lia.
      - destruct Hs as [S1 S2]. clear - S1 S2 CL0 CH0. unfold HEAPLO, SB in *. lia.
      - destruct Hi as [I1 I2]. clear - I1 I2 GH GS. unfold HEAPLO, SB, SHMAPLO in *. lia.
      - destruct Hp as (lo & hi & Hlin & Hlt & [P1 P2]).
        pose proof (PERM_bnd _ _ _ _ _ _ _ (hi - 1) HA ltac:(exists lo, hi; split; [exact Hlin | lia])) as B2.
        assert (B1 : 0 <= lo).
        { rewrite <- (co_perm HC) in Hlin. unfold wins_den in Hlin. apply in_map_iff in Hlin as [[gb gl] [Heq _]]. cbn in Heq.
          injection Heq as E1 E2. pose proof (u64_range (edenot E gb)). unfold uE in *. lia. }
        clear - B1 B2 P1 P2 Hlt. unfold two47, HEAPLO, SB in *. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (ind a) eqn:Hi.
    { exfalso. apply IND in Hi. destruct (OFFSH a Hi); lia. }
    assert (EQM : M' a = M a).
    { destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|].
      exfalso. destruct (Hfr a Hne) as [Hd|Hs]; [apply IND in Hd; rewrite Hd in Hi; discriminate|].
      unfold scratch, uE in Hs.
      pose proof GlzConst.ceil_lo as CL0. unfold HEAPLO, MSTK_M in Hs, LOW, Hsplo. unfold uE in Hsplo.
      destruct LOW as [LOW1 LOW2]. destruct Hs as [Hs1 Hs2].
      clear - Hs1 Hs2 LOW1 LOW2 Hsplo CL0 SFG_. lia. }
    unfold MRp, MR. destruct Hz3 as [Hz3|Hp].
    + rewrite (Mr_shadow E cs mdl' M' a Hz3). rewrite (Mr_shadow E cs model M a Hz3). exact EQM.
    + rewrite (Mr_pshadow _ _ _ _ _ _ _ E cs mdl' M' a HA Hp). rewrite (Mr_pshadow _ _ _ _ _ _ _ E cs model M a HA Hp). exact EQM.
  - unfold mem_kept in Hin. rewrite <- app_assoc. exact Hin.
Qed.

Lemma mem_kept_sound : forall E cs fx R M model mdl' M' B' C' K' k0 db dk (dst n : Z) spb spk K,
  cs_ok E cs fx R M model ->
  know_ok SEGS E (Mr E cs model M) k0 ->
  forallb (bflatb (kn_havoc k0 db dk (reg cs 12))) (a_vis cs ++ a_fake cs ++ a_ghost cs) = true ->
  split_lit (reg cs 2) = (spb, spk) -> uE E (reg cs 2) = uE E spb + spk -> SFLOOR + MSTK_M <= uE E (reg cs 2) ->
  estart E (SA db dk) = dst -> elenZ E (reg cs 12) = n -> 0 <= dst -> dst + n <= 2 ^ 64 ->
  (forall a : word, dst <= u a < dst + n -> u a < SB \/ HEAPLO <= u a) ->
  (forall m B C K M0, AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M0 m ->
     forall a : word, dst <= u a < dst + n -> hid E cs m a = false) ->
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B' C' K' M' mdl' ->
  (forall a : word, dst <= u a < dst + n -> M' a <> None) ->
  (forall a : word, M' a <> M a -> (dst <= u a < dst + n) \/ scratch (uE E (reg cs 2)) MSTK_M a) ->
  scratch_ok SEGS M' (uE E (reg cs 2)) MSTK_M ->
  In K (mem_kept G cs (kn_havoc k0 db dk (reg cs 12)) (nxt cs)) -> kentry_ok SEGS E (Mr E cs mdl' M') K.
Proof.
  intros E cs fx R M model mdl' M' B' C' K' k0 db dk dst n spb spk K HC HK0 Hflat Hsp Hspv Hsplo Edst En D0 D1 OFFSH VIS HA' Hdef Hfr Hscr Hin.
  eapply (kept_sound_gen E cs fx R M model mdl' M' B' C' K' _ dst n spb spk K HC); try eassumption.
  intros Mh Hout Hg. eapply know_ok_havoc; [exact HK0 | | exact Hg].
  intros x Hx. apply Hout. rewrite Edst, En in Hx. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
Definition mem_nspec (needsrc apart : bool) (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp dst src n : Z) (bs : list byte) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre SEGS SPTOPc G R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) = src -> u (getr R (Z_to_bv 5 12)) = n ->
    (apart = true -> dst + n <= src \/ src + n <= dst) ->
    (needsrc = true -> apart = false -> dst <> src \/ (forall i, 0 <= i < n -> M (Z_to_bv 64 (src + i)) <> None)) ->   (* [comment removed for export] *)
    ndst_pre SEGS SWIN PERMc SPTOPc G M Lc Lf dst n ->
    (needsrc = true -> nsrc_pre SEGS PERMc G M Lc Lf src n bs) ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) ->
    (needsrc = true -> forall a : word, src <= u a < src + n -> ~ scratch sp MSTK_M a) ->
    nmem_post SEGS AINV FXOK RZ R M mdl Lc Lf B C K ret sp dst n
              (fun i => if needsrc then Some (nth i bs (Z_to_bv 8 0)) else Some (Z_to_bv 8 (src mod 256))) T ->
    RZ (cfg fx R entry M mdl) T.

Lemma mem_nspec_of_copy : forall entry, copy_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> mem_nspec true true entry.
Proof.
  intros entry H fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HF HA PRE R10 R11 R12 AP MV DST SRC SC1 SC2 POST.
  eapply (H fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HF HA PRE R10 R11 R12 (AP eq_refl) DST (SRC eq_refl) SC1 (SC2 eq_refl)). exact POST.
Qed.
Lemma mem_nspec_of_move : forall entry, move_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> mem_nspec true false entry.
Proof.
  intros entry H fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HF HA PRE R10 R11 R12 AP MV DST SRC SC1 SC2 POST.
  eapply (H fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HF HA PRE R10 R11 R12 (MV eq_refl eq_refl) DST (SRC eq_refl) SC1 (SC2 eq_refl)). exact POST.
Qed.
Lemma mem_nspec_of_fill : forall entry, fill_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> mem_nspec false false entry.
Proof.
  intros entry H fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HF HA PRE R10 R11 R12 AP MV DST SRC SC1 SC2 POST.
  eapply (H fx R M mdl Lc Lf B C K ret sp dst (src mod 256) n T Hh HF HA PRE R10 ltac:(rewrite R11; reflexivity) R12 DST SC1). exact POST.
Qed.

(* [comment removed for export] *)
Definition facts_ok (needsrc : bool) (facts : acs -> expr -> Z -> expr -> Z -> Z -> Z -> option (list kentry * nat)) : Prop :=
  forall cs E MR db dk sb sk nlo nhi newf extra,
    know_ok SEGS E MR (kn cs) -> fresh_ok nx0 cs = true ->
    split_lit (reg cs 10) = (db, dk) -> split_lit (reg cs 11) = (sb, sk) ->
    xlo (kn cs) (reg cs 12) = Some nlo -> xhi (kn cs) (reg cs 12) = Some nhi ->
    0 <= nlo -> nlo <= uE E (reg cs 12) <= nhi ->
    0 <= estart E (SA db dk) -> estart E (SA db dk) + uE E (reg cs 12) <= two47 -> uE E (reg cs 10) = estart E (SA db dk) ->
    (needsrc = true -> 0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + uE E (reg cs 12) <= two47 /\ uE E (reg cs 11) = estart E (SA sb sk)) ->
    facts cs db dk sb sk nlo nhi = Some (newf, extra) ->
    kn_vars_lt (nxt cs + NCS + extra) newf = true
    /\ exists bs, (needsrc = true -> rdn SEGS MR (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat (uE E (reg cs 12))) = Some bs)
       /\ forall (MR' : word -> option byte) (R' : bvmap 5 word),
            (forall i, (i < Z.to_nat (uE E (reg cs 12)))%nat ->
               MR' (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat i)) =
                 (if needsrc then Some (nth i bs (Z_to_bv 8 0)) else Some (Z_to_bv 8 (uE E (reg cs 11) mod 256)))) ->
            exists vals, length vals = extra /\ know_ok SEGS (ext_call2 E (nxt cs) R' vals) MR' newf.

(* [comment removed for export] *)
Lemma fill_dst_facts_ok : facts_ok false fill_dst_facts.
Proof.
  intros cs E MR db dk sb sk nlo nhi newf extra HK Hfresh Hsd Hss Hnlo Hnhi Hnlo0 NB D0 D1 Hdst _ H.
  unfold fill_dst_facts in H. destruct (reg_lit cs 11) as [c|] eqn:Hc; [|discriminate]. injection H as <- <-. unfold two47 in D1.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & _).
  assert (Fdb : AP.expr_vars_lt (nxt cs) db = true).
  { eapply split_lit_vars; [exact Hsd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  assert (Fne : AP.expr_vars_lt (nxt cs) (reg cs 12) = true) by (unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia]).
  assert (Hcv : uE E (reg cs 11) mod 256 = c mod 256).
  { unfold reg_lit, lit_of in Hc. destruct (reg cs 11) as [z| | | | | | |] eqn:Hr; try discriminate. injection Hc as <-.
    unfold uE. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64. reflexivity. }
  split.
  - pose proof (expr_vars_lt_mono _ (nxt cs + NCS + 0) _ Fdb ltac:(lia)) as Fdb'.
    pose proof (expr_vars_lt_mono _ (nxt cs + NCS + 0) _ Fne ltac:(lia)) as Fne'.
    cbv zeta. repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      cbn [kn_vars_lt kentry_vars_lt andb]; unfold saddr_vars_lt, AP.saddr_vars_lt; cbn [a_base]; rewrite ?Fdb', ?Fne'; reflexivity.
  - exists []. split; [intros HH; discriminate|]. intros MR' R' HB. exists []. split; [reflexivity|].
    destruct (Z.ltb 0 nlo) eqn:Hpos; [|constructor]. apply Z.ltb_lt in Hpos.
    set (E2 := ext_call2 E (nxt cs) R' []). pose proof (ext_call2_agree E (nxt cs) R' []) as Hag. fold E2 in Hag.
    assert (ED : estart E2 (SA db dk) = estart E (SA db dk)).
    { rewrite !estart_SA. rewrite <- (edenot_agree' (nxt cs) E E2 db Hag Fdb). reflexivity. }
    assert (EN : elenZ E2 (reg cs 12) = uE E (reg cs 12)).
    { unfold elenZ, uE. rewrite <- (edenot_agree' (nxt cs) E E2 (reg cs 12) Hag Fne). reflexivity. }
    apply Forall_one. destruct (Z.eqb (c mod 256) 0) eqn:Hz; cbn [kentry_ok]; rewrite ED, EN.
    + apply Z.eqb_eq in Hz. split; [unfold flat; lia|]. intros i Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (HB (Z.to_nat i)) by lia. rewrite Hcv, Hz. reflexivity.
    + split; [unfold flat; lia|]. intros i Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (HB (Z.to_nat i)) by lia. rewrite Hcv. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq_firstn : forall {T} (bs : list T) (d : T) n k,
  (k + n <= length bs)%nat -> map (fun i => nth i bs d) (seq k n) = firstn n (skipn k bs).
Proof.
  intros T bs d n. induction n as [|n IH]; intros k Hk; [reflexivity|].
  cbn [seq map]. rewrite (IH (S k)) by lia.
  destruct (skipn k bs) as [|x r] eqn:Hs.
  - exfalso. pose proof (f_equal (@length T) Hs) as L. rewrite length_skipn in L. cbn in L. lia.
  - cbn [firstn]. f_equal.
    + pose proof (nth_skipn k bs 0 d) as X. rewrite Hs, Nat.add_0_r in X. cbn in X. exact (eq_sym X).
    + replace (S k) with (1 + k)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity.
Qed.
Lemma rdn_of_bytes : forall M (a : Z) n (bs : list byte),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (n <= length bs)%nat ->
  (forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn SEGS M (Z_to_bv 64 a) n = Some (firstn n bs).
Proof.
  intros M a n bs Ha Hnw Hlen HB.
  rewrite <- (skipn_O bs). rewrite <- (map_nth_seq_firstn bs (Z_to_bv 8 0) n 0) by lia.
  pose proof (rdn_of_nth SEGS M n (Z_to_bv 64 a) (fun i => nth i bs (Z_to_bv 8 0)) ltac:(rewrite u64_lit by lia; lia)) as R.
  rewrite u64_lit in R by lia. apply R. intros j Hj. cbn [rdn]. rewrite (HB j Hj). reflexivity.
Qed.

Lemma copy_dst_facts_ok : facts_ok true (copy_dst_facts SEGS).
Proof.
  intros cs E MR db dk sb sk nlo nhi newf extra HK Hfresh Hsd Hss Hnlo Hnhi Hnlo0 NB D0 D1 Hdst SRC H.
  destruct (SRC eq_refl) as (S0 & S1 & Hsrc). unfold two47 in D1, S1.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & _).
  assert (Fdb : AP.expr_vars_lt (nxt cs) db = true) by (eapply split_lit_vars; [exact Hsd|]; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia]).
  assert (Fsb : AP.expr_vars_lt (nxt cs) sb = true) by (eapply split_lit_vars; [exact Hss|]; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia]).
  assert (Fne : AP.expr_vars_lt (nxt cs) (reg cs 12) = true) by (unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia]).
  unfold copy_dst_facts in H. rewrite copyFB_eq in H.
  match type of H with (match ?r with Some _ => _ | None => None end) = _ => destruct r as [[newf0 extra0]|] eqn:Hr; [|discriminate] end.
  destruct (kn_vars_lt (nxt cs + NCS + extra0) newf0) eqn:Hkv; [|discriminate]. injection H as -> ->.
  split; [exact Hkv|].
  set (n := uE E (reg cs 12)) in *. set (dst := estart E (SA db dk)) in *. set (src := estart E (SA sb sk)) in *.
  pose proof (u64_range (edenot E (reg cs 12))) as NR.
  assert (EnZ : elenZ E (reg cs 12) = n) by reflexivity.
  (* [comment removed for export] *)
  assert (GEN : forall bs,
    rdn SEGS MR (Z_to_bv 64 src) (Z.to_nat n) = Some bs -> length bs = Z.to_nat n ->
    (forall (MR' : word -> option byte) (R' : bvmap 5 word),
       (forall i, (i < Z.to_nat n)%nat -> MR' (Z_to_bv 64 (dst + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
       exists vals, length vals = extra /\ know_ok SEGS (ext_call2 E (nxt cs) R' vals) MR' newf) ->
    exists bs0, (true = true -> rdn SEGS MR (Z_to_bv 64 src) (Z.to_nat n) = Some bs0)
      /\ forall (MR' : word -> option byte) (R' : bvmap 5 word),
           (forall i, (i < Z.to_nat n)%nat -> MR' (Z_to_bv 64 (dst + Z.of_nat i)) = (if true then Some (nth i bs0 (Z_to_bv 8 0)) else Some (Z_to_bv 8 (uE E (reg cs 11) mod 256)))) ->
           exists vals, length vals = extra /\ know_ok SEGS (ext_call2 E (nxt cs) R' vals) MR' newf).
  { intros bs Hrd Hlen HP. exists bs. split; [intros _; exact Hrd|]. intros MR' R' HB. apply HP. exact HB. }
  (* [comment removed for export] *)
  assert (AG : forall R' vals, let E2 := ext_call2 E (nxt cs) R' vals in
            estart E2 (SA db dk) = dst /\ estart E2 (SA sb sk) = src /\ elenZ E2 (reg cs 12) = n /\ eb E2 = eb E).
  { intros R' vals. pose proof (ext_call2_agree E (nxt cs) R' vals) as Hag. cbv zeta.
    rewrite !estart_SA. rewrite <- (edenot_agree' (nxt cs) E _ db Hag Fdb), <- (edenot_agree' (nxt cs) E _ sb Hag Fsb).
    unfold elenZ. rewrite <- (edenot_agree' (nxt cs) E _ (reg cs 12) Hag Fne).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. symmetry. exact (proj2 Hag). }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hn0.
  { (* [comment removed for export] *)
    injection Hr as <- <-. apply Z.eqb_eq in Hn0. assert (Zn : Z.to_nat n = 0%nat) by lia.
    apply (GEN []); [rewrite Zn; reflexivity | rewrite Zn; reflexivity |]. intros MR' R' _. exists []. split; [reflexivity | constructor]. }
  destruct (kblob_at (kn cs) sb sk (reg cs 12)) as [j|] eqn:Hkba.
  { (* [comment removed for export] *)
    injection Hr as <- <-.
    assert (HKB : kentry_ok SEGS E MR (KBlob (SA sb sk) (reg cs 12) j)).
    { unfold kblob_at in Hkba.
      destruct (List.find _ (kn cs)) as [K|] eqn:Hf; [|discriminate].
      apply find_some in Hf as [HinK HKt]. destruct K as [| |[b o] len j0| | | | | | | | |]; try discriminate.
      injection Hkba as ->. apply andb_prop in HKt as [HKt Hlen]. apply andb_prop in HKt as [Hb Ho].
      apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. apply expr_eqb_eq in Hlen. subst b o len.
      exact (proj1 (Forall_forall _ _) HK _ HinK). }
    cbn [kentry_ok] in HKB. destruct HKB as (BF & BL & BB). rewrite EnZ in BL, BB. fold src in BF, BB.
    apply (GEN (eb E j)).
    - rewrite <- (@firstn_all2 _ (Z.to_nat n) (eb E j)) at 1 by lia.
      apply rdn_of_bytes; [lia | lia | lia |].
      intros i Hi. replace (Z.of_nat i) with (Z.of_nat i) by reflexivity. rewrite (BB (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
    - lia.
    - intros MR' R' HB. exists []. split; [reflexivity|]. destruct (AG R' []) as (ED & ES & EN & EB).
      apply Forall_one. cbn [kentry_ok]. rewrite ED, EN, EB. split; [unfold flat; lia|]. split; [exact BL|].
      intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. rewrite (HB (Z.to_nat i)) by lia. reflexivity. }
  clear Hkba.
  destruct (Z.ltb 0 nlo && kzero_x (kn cs) (kn cs) sb sk (reg cs 12))%bool eqn:Hkz.
  { (* [comment removed for export] *)
    injection Hr as <- <-. apply andb_prop in Hkz as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    destruct (kzero_x_sound SEGS E MR (kn cs) (kn cs) sb sk (reg cs 12) HK HK Hkz) as (Zb & Zlo & Zhi). rewrite EnZ in Zb, Zhi. fold src in Zb, Zlo, Zhi.
    apply (GEN (repeat (Z_to_bv 8 0) (Z.to_nat n))).
    - rewrite <- (@firstn_all2 _ (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))) at 1 by (rewrite repeat_length; lia).
      apply rdn_of_bytes; [lia | lia | rewrite repeat_length; lia |].
      intros i Hi. rewrite nth_repeat_lt by exact Hi. apply Zb. lia.
    - apply repeat_length.
    - intros MR' R' HB. exists []. split; [reflexivity|]. destruct (AG R' []) as (ED & ES & EN & EB).
      apply Forall_one. cbn [kentry_ok]. rewrite ED, EN. split; [unfold flat; lia|].
      intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (HB (Z.to_nat i)) by lia. rewrite nth_repeat_lt by lia. reflexivity. }
  clear Hkz Hn0.
  (* [comment removed for export] *)
  assert (HAVOC : forall words,
    ((kwritable_x (kn cs) (kn cs) sb sk (reg cs 12) || kn_readable_x (kn cs) sb sk (reg cs 12)) && flat_x (kn cs) sb sk (reg cs 12))%bool = true ->
    8 * Z.of_nat words <= n -> Z.of_nat words <= Z.of_nat extra ->
    newf = map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)%nat)) (seq 0 words)
           ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then [KUnk (SA db dk) (reg cs 12)] else []) ->
    extra = words ->
    exists bs0, (true = true -> rdn SEGS MR (Z_to_bv 64 src) (Z.to_nat n) = Some bs0)
      /\ forall (MR' : word -> option byte) (R' : bvmap 5 word),
           (forall i, (i < Z.to_nat n)%nat -> MR' (Z_to_bv 64 (dst + Z.of_nat i)) = (if true then Some (nth i bs0 (Z_to_bv 8 0)) else Some (Z_to_bv 8 (uE E (reg cs 11) mod 256)))) ->
           exists vals, length vals = extra /\ know_ok SEGS (ext_call2 E (nxt cs) R' vals) MR' newf).
  { intros words Hsrcok Hw Hwe -> ->.
    apply andb_prop in Hsrcok as [Hrdbl Hsfl].
    destruct (flat_x_sound SEGS E MR (kn cs) sb sk (reg cs 12) HK Hsfl) as (F1 & F2 & F3). fold src in F1, F2. unfold n in *.
    (* [comment removed for export] *)
    assert (BS : exists bs, rdn SEGS MR (Z_to_bv 64 src) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n).
    { apply orb_prop in Hrdbl as [Hwr|Hrdx].
      - destruct (kwritable_x_sound SEGS E MR (kn cs) (kn cs) sb sk (reg cs 12) HK HK Hwr) as (Wst & _ & _). rewrite EnZ in Wst. fold src in Wst.
        apply (store_ok_rdn SEGS SEGS_wr); [rewrite u64_lit by lia; lia | apply Wst; lia].
      - destruct (kn_readable_x_sound2 SEGS E MR (kn cs) sb sk (reg cs 12) HK Hrdx) as (R1 & R2 & R3). rewrite EnZ in R2, R3. fold src in R1, R2, R3.
        assert (BY : forall i, (i < Z.to_nat n)%nat -> exists b, MR (Z_to_bv 64 (src + Z.of_nat i)) = Some b).
        { intros i Hi. destruct (MR (Z_to_bv 64 (src + Z.of_nat i))) as [b|] eqn:Hb; [exists b; reflexivity|]. exfalso. exact (R3 (Z.of_nat i) ltac:(lia) Hb). }
        exists (map (fun i => match MR (Z_to_bv 64 (src + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
        split; [|rewrite length_map, length_seq; reflexivity].
        pose proof (rdn_of_nth SEGS MR (Z.to_nat n) (Z_to_bv 64 src) (fun i => match MR (Z_to_bv 64 (src + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                      ltac:(rewrite u64_lit by lia; lia)) as RR. rewrite u64_lit in RR by lia. apply RR.
        intros j Hj. destruct (BY j Hj) as [b Hb]. cbn [rdn]. rewrite Hb. reflexivity. }
    destruct BS as (bs & Hrd & Hlen).
    apply (GEN bs Hrd Hlen). intros MR' R' HB.
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 words)).
    exists vals. split; [subst vals; rewrite length_map, length_seq; reflexivity|].
    set (E2 := ext_call2 E (nxt cs) R' vals). destruct (AG R' vals) as (ED & ES & EN & EB). fold E2 in ED, ES, EN, EB.
    pose proof (ext_call2_agree E (nxt cs) R' vals) as Hag2. fold E2 in Hag2.
    (* [comment removed for export] *)
    assert (RD' : rdn SEGS MR' (Z_to_bv 64 dst) (Z.to_nat n) = Some bs).
    { rewrite <- (@firstn_all2 _ (Z.to_nat n) bs) at 1 by lia. apply rdn_of_bytes; [lia | lia | lia | exact HB]. }
    apply Forall_app. split.
    - (* [comment removed for export] *)
      apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
      assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = dst + 8 * Z.of_nat i).
      { rewrite estart_SA. rewrite estart_SA in ED. lia. }
      cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
      rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
      subst vals. rewrite (nth_map_seq _ words i (Z_to_bv 64 0)) by lia.
      assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
      rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
      pose proof (rdn_skipn SEGS MR' (Z.to_nat n) (Z_to_bv 64 dst) bs (8 * i) RD' ltac:(lia)) as Sk.
      pose proof (rdn_firstn SEGS MR' (Z.to_nat n - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
      replace (Z_to_bv 64 (dst + 8 * Z.of_nat i)) with (Z_to_bv 64 dst + nat_to_word (8 * i))%bv; [exact Fi|].
      apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite (Z.mod_small dst) by lia. rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
    - apply Forall_app. split.
      + (* [comment removed for export] *)
        unfold kblob_prefix.
        destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
        apply find_some in HF as [HinK HKt].
        destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | | | | ]; try (now constructor).
        apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
        apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
        pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HKB. cbn [kentry_ok] in HKB.
        assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
        assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
        rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes). fold src in Bflat, Bbytes.
        apply Forall_one. cbn [kentry_ok]. rewrite En0', ED, EB.
        refine (conj _ (conj Blen _)); [unfold flat; lia|].
        intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (HB (Z.to_nat i)) by lia. f_equal.
        pose proof (rdn_nth SEGS MR (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat i) ltac:(rewrite u64_lit by lia; lia) Hrd ltac:(lia)) as RB1.
        rewrite u64_lit in RB1 by lia. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
        cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
      + (* [comment removed for export] *)
        destruct (Z.ltb 0 nlo) eqn:Hpos; [|constructor]. apply Z.ltb_lt in Hpos.
        apply Forall_one. cbn [kentry_ok]. rewrite ED, EN. split; [unfold flat; lia|].
        intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (HB (Z.to_nat i)) by lia. discriminate. }
  (* [comment removed for export] *)
  assert (WORDS : forall words, words = (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat) ->
                  8 * Z.of_nat words <= n).
  { intros words ->. destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:Hc; [|lia].
    repeat (apply andb_prop in Hc as [Hc ?Q]). apply Z.eqb_eq in Hc. apply Z.eqb_eq in Q1.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (reg cs 12) as [z| | | | | | |] eqn:Hne12;
    try (cbv iota in Hr; cbv beta in Hr;
         match type of Hr with (if ?c then _ else None) = _ => destruct c eqn:Hok; [|discriminate] end;
         injection Hr as <- <-; eapply (HAVOC _ ltac:(first [exact Hok | reflexivity]) (WORDS _ eq_refl) ltac:(lia) eq_refl eq_refl)).
  (* [comment removed for export] *)
  cbv iota in Hr. cbv beta in Hr.
  destruct (Z.leb nhi 2048 && flat_x (kn cs) sb sk (ELit z))%bool eqn:Hlit.
  - destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf.
    + injection Hr as <- <-. apply andb_prop in Hlit as [H2048 Hsfl]. apply Z.leb_le in H2048.
      destruct (flat_x_sound SEGS E MR (kn cs) sb sk (ELit z) HK Hsfl) as (F1 & F2 & F3). fold src in F1, F2.
      assert (Hn : n = nhi).
      { unfold xhi in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. unfold n, uE. cbn [edenot]. rewrite u_lit64. reflexivity. }
      pose proof S1 as S1'. pose proof D1 as D1'. pose proof Hn as Hn'. unfold n in S1', D1', Hn'.
      destruct (copy_facts_sound SEGS E MR (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HK Hcf ltac:(lia) ltac:(lia)
                  ltac:(fold src; lia) ltac:(fold src; lia) ltac:(fold dst; lia) ltac:(fold dst; lia)) as (bs & Hlen & Hrd & HKC).
      fold src in Hrd. fold dst in HKC. rewrite <- Hn in Hlen, Hrd, HKC.
      apply (GEN bs Hrd Hlen). intros MR' R' HB. exists []. split; [reflexivity|].
      set (E2 := ext_call2 E (nxt cs) R' []). destruct (AG R' []) as (ED & ES & EN & EB). fold E2 in ED, ES, EN, EB.
      pose proof (ext_call2_agree E (nxt cs) R' []) as Hag2. fold E2 in Hag2.
      (* [comment removed for export] *)
      assert (HK2 : know_ok SEGS E2 MR (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HK]).
      destruct (copy_facts_sound SEGS E2 MR (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HK2 Hcf ltac:(lia) ltac:(lia)
                  ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia)) as (bs2 & Hlen2 & Hrd2 & HKC2).
      rewrite ES, <- Hn in Hrd2. rewrite Hrd in Hrd2. injection Hrd2 as <-.
      apply HKC2. rewrite ED, <- Hn. rewrite <- (@firstn_all2 _ (Z.to_nat n) bs) at 1 by lia. apply rdn_of_bytes; [lia | lia | lia | exact HB].
    + match type of Hr with (if ?c then _ else None) = _ => destruct c eqn:Hok; [|discriminate] end.
      injection Hr as <- <-. eapply (HAVOC _ ltac:(first [exact Hok | reflexivity]) (WORDS _ eq_refl) ltac:(lia) eq_refl eq_refl).
  - match type of Hr with (if ?c then _ else None) = _ => destruct c eqn:Hok; [|discriminate] end.
    injection Hr as <- <-. eapply (HAVOC _ ltac:(first [exact Hok | reflexivity]) (WORDS _ eq_refl) ltac:(lia) eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem node_mem_sound : forall entry needsrc apart facts,
  (apart = true -> needsrc = true) ->
  facts_ok needsrc facts -> mem_nspec needsrc apart entry ->
  node1_stmt always (node_mem A nx0 G entry needsrc apart facts).
Proof.
  intros entry needsrc apart facts Han FOK MS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_mem in Hn.
  destruct (mem_ok A nx0 G entry needsrc apart cs) as [[[[[ret [db dk]] [sb sk]] [nlo nhi]] kh]|] eqn:Hmo; [|discriminate].
  destruct (facts cs db dk sb sk nlo nhi) as [[newf extra]|] eqn:Hf; [|discriminate].
  apply some_inj in Hn. subst cs'.
  destruct (mem_ok_sound entry needsrc apart cs ret db dk sb sk nlo nhi kh E fx R M model HC Hmo)
    as (spb & spk & Hpc & Hfresh & Hlen & PRE & R2 & Hspv & Hflat & Hbfm & Hsd & Hss & Hdst & R10 & R12 & R11
        & Hnlo & Hnhi & NB1 & NB2 & EnZ & DST & DB & DSC & VIS & OFFSH & SRC & (k0 & Ekh & HK0 & Hflath)).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in *.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof DST as (NB & Hm1 & Hm2 & Hacc & Hshv & Hown).
  pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & _ & Hsplo & Hsptop & _).
  (* [comment removed for export] *)
  destruct (FOK cs E MR db dk sb sk nlo nhi newf extra HK Hfresh Hsd Hss Hnlo Hnhi (proj1 NB1) (conj (proj2 NB1) (proj1 NB2))
              ltac:(lia) ltac:(lia) Hdst
              ltac:(intros Hns; destruct (SRC Hns) as (Hsrc & SB2 & _); split; [lia | split; [lia | exact Hsrc]])
              Hf) as [Hvars [bs [Hrd POST]]].
  set (v := nxt cs) in *.
  set (Lc := blocks_den E (a_vis cs)) in *. set (Lf := blocks_den E (a_fake cs)) in *.
  unfold cfgF. rewrite Hpc.
  apply (MS fx R M model Lc Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) ret (uE E (reg cs 2))
            (estart E (SA db dk)) (uE E (reg cs 11)) (uE E (reg cs 12)) bs T (co_halt HC) (co_fx HC) (co_ainv HC) PRE R10 R11 R12).
  - (* [comment removed for export] *) intros Hap. destruct (SRC (Han Hap)) as (Hsrc & _ & _ & _ & _ & _ & _ & AP & _). rewrite Hsrc. exact (AP Hap).
  - (* [comment removed for export] *) intros Hns Hap. destruct (SRC Hns) as (Hsrc & _ & _ & _ & _ & _ & _ & _ & MV). rewrite Hsrc. exact (MV Hap).
  - exact DST.
  - (* [comment removed for export] *) intros Hns. destruct (SRC Hns) as (Hsrc & _ & Sm1 & Sm2 & Sacc & Sshv & _ & _). rewrite Hsrc.
    split; [exact Sm1|]. split; [exact Sm2|]. split; [exact Sacc|]. split; [exact Sshv|].
    eapply rdn_Mr_full; [exact (co_ainv HC)|]. exact (Hrd Hns).
  - exact DSC.
  - intros Hns. destruct (SRC Hns) as (Hsrc & _ & _ & _ & _ & _ & SSC & _ & _). rewrite Hsrc. exact SSC.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Ha0 Hbytes Hfr Hscr HAINV' (Hh' & Hfs' & Hfds').
    set (MRp := Mr E cs mdl' M').
    assert (HLc : forall E', env_agree v E E' -> blocks_den E' (a_vis cs) = Lc) by (intros E' Hag; unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLf : forall E', env_agree v E E' -> blocks_den E' (a_fake cs) = Lf) by (intros E' Hag; unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
    (* [comment removed for export] *)
    assert (BY : forall i, (i < Z.to_nat (uE E (reg cs 12)))%nat ->
              MRp (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat i))
              = (if needsrc then Some (nth i bs (Z_to_bv 8 0)) else Some (Z_to_bv 8 (uE E (reg cs 11) mod 256)))).
    { intros i Hi. unfold MRp, GPS.Mr. rewrite mrestrict_visible; [exact (Hbytes i Hi)|].
      apply (VIS mdl' _ _ _ _ HAINV'). rewrite u64_lit by (unfold two47 in DB; lia). lia. }
    destruct (POST MRp R' BY) as [vals [Hvl HKnew]].
    set (E' := ext_call2 E v R' vals) in *.
    assert (Hag : env_agree v E E') by (unfold E'; apply ext_call2_agree).
    set (cs' := mem_post cs ret (reg cs 10) (newf ++ mem_kept G cs kh v) extra).
    assert (HMR : Mr E' cs' mdl' M' = MRp).
    { unfold MRp. rewrite (GPS.Mr_fields SHC VSH E' cs cs' mdl' M') by reflexivity. apply (GPS.Mr_agreeE nx0); [exact Hag | exact Hfresh]. }
    assert (HKN : know_ok SEGS E' (Mr E' cs' mdl' M') (kn cs')).
    { rewrite HMR. unfold cs'. cbn [mem_post kn a_ss s_know].
      unfold know_ok. apply Forall_app. split; [exact HKnew|].
      apply (know_ok_agree' SEGS v E E'); [exact Hag | unfold mem_kept; apply keep_owned_vars |].
      unfold know_ok. apply Forall_forall. intros K HKin. rewrite Ekh in HKin.
      eapply (mem_kept_sound E cs fx R M model mdl' M' _ _ _ k0 db dk (estart E (SA db dk)) (uE E (reg cs 12)) spb spk K HC HK0);
        try eassumption; try reflexivity.
      all: try (rewrite <- Ekh; exact Hflath).
      all: try (destruct DB as [DB1 DB2]; unfold two47, MSTK_M in *; lia).
      intros a Ha. pose proof (u64_range a). destruct DB as [DB1 DB2]. unfold two47 in DB2.
      replace a with (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat (Z.to_nat (u a - estart E (SA db dk))))).
      2:{ apply bv_eq. rewrite u64_lit; lia. }
      rewrite (Hbytes (Z.to_nat (u a - estart E (SA db dk)))) by lia. destruct needsrc; discriminate. }
    apply (Hk E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + assert (HA' : AINV (blocks_den E' (a_vis cs)) (blocks_den E' (a_fake cs)) (bcost E' (a_vis cs)) (bcount (a_vis cs)) (uE E' (a_meter cs)) M' mdl').
      { rewrite (HLc E' Hag), (HLf E' Hag). rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
        rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact HAINV'. }
      constructor; try (cbn [mem_post a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo a_abytes a_tidset]).
      * (* [comment removed for export] *)
        unfold ret_regs.
        set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved v).
        assert (Hsf : AP.sr_vars_lt (v + NCS) sr1 = true).
        { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ]. unfold caller_saved, NCS. cbn [length]. lia. }
        eapply (regs_ok_agree' (v + NCS)); [unfold E'; apply ext_call2_agree16 | |].
        -- apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | lia].
        -- subst sr1. apply (regs_after_call E _ R R' v (Some (reg cs 10)) (co_regs HC) Fsr (kept_ok_of_callee_saved _ _ Hkept)).
           split; [unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia]|].
           apply bv_eq. rewrite Ha0. unfold uE in Hdst. rewrite Hdst. reflexivity.
      * reflexivity.
      * (* [comment removed for export] *) exact HKN.
      * exact Hh'.
      * rewrite Hfs'. exact (co_fs HC).
      * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact (co_kcap HC).
      * rewrite (uE_agree v E E' (a_fbud cs) Hag Ffb). exact (co_fbud HC).
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.



(* [comment removed for export] *)
Theorem node_mcopy_sound : forall entry,
  copy_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> node1_stmt always (node_mcopy SEGS A nx0 G entry).
Proof. intros entry H. unfold node_mcopy. apply node_mem_sound; [intros _; reflexivity | apply copy_dst_facts_ok | apply mem_nspec_of_copy; exact H]. Qed.
Theorem node_mmove_sound : forall entry,
  move_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> node1_stmt always (node_mmove SEGS A nx0 G entry).
Proof. intros entry H. unfold node_mmove. apply node_mem_sound; [intros X; discriminate X | apply copy_dst_facts_ok | apply mem_nspec_of_move; exact H]. Qed.
Theorem node_mfill_sound : forall entry,
  fill_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ entry -> node1_stmt always (node_mfill A nx0 G entry).
Proof. intros entry H. unfold node_mfill. apply node_mem_sound; [intros X; discriminate X | apply fill_dst_facts_ok | apply mem_nspec_of_fill; exact H]. Qed.

(* [comment removed for export] *)
Theorem node_memcpy_sound : copy_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_memcpy G) ->
  OBL_memcpy SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_memcpy, node_memcpy. exact (node_mcopy_sound _ H). Qed.
Theorem node_amemcpy_sound : copy_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_amemcpy G) ->
  OBL_amemcpy SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_amemcpy, node_amemcpy. exact (node_mcopy_sound _ H). Qed.
Theorem node_memmove_sound : move_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_memmove G) ->
  OBL_memmove SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_memmove, node_memmove. exact (node_mmove_sound _ H). Qed.
Theorem node_amemmove_sound : move_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_amemmove G) ->
  OBL_amemmove SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_amemmove, node_amemmove. exact (node_mmove_sound _ H). Qed.
Theorem node_memset_sound : fill_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_memset G) ->
  OBL_memset SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_memset, node_memset. exact (node_mfill_sound _ H). Qed.
Theorem node_amemset_sound : fill_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ (g_amemset G) ->
  OBL_amemset SEGS A nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. unfold OBL_amemset, node_amemset. exact (node_mfill_sound _ H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis G_ro_img : g_ro_lo G <= g_ro_hi G <= g_img_hi G.

(* [comment removed for export] *)
Lemma img_strlen_from_spec : forall fuel a len,
  img_strlen_from SEGS a fuel = Some len ->
  0 <= len
  /\ (forall i, 0 <= i < len -> exists b, seg_rom SEGS (Z_to_bv 64 (a + i)) = Some b /\ u b <> 0)
  /\ (exists b0, seg_rom SEGS (Z_to_bv 64 (a + len)) = Some b0 /\ u b0 = 0).
Proof.
  induction fuel as [|fuel IH]; intros a len H; cbn [img_strlen_from] in H; [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:Hb; [|discriminate].
  destruct (Z.eqb_spec (u b) 0) as [Hz|Hnz].
  - injection H as <-. split; [lia|]. split; [intros i Hi; lia|]. exists b. rewrite Z.add_0_r. split; [exact Hb | exact Hz].
  - destruct (img_strlen_from SEGS (a + 1) fuel) as [l|] eqn:Hl; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) l Hl) as (L0 & Lnz & Lz). split; [lia|]. split.
    + intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne].
      * exists b. rewrite Z.add_0_r. split; [exact Hb | exact Hnz].
      * destruct (Lnz (i - 1) ltac:(lia)) as (b' & Hb' & Hnz'). exists b'. replace (a + i) with (a + 1 + (i - 1)) by lia. split; [exact Hb' | exact Hnz'].
    + destruct Lz as (b0 & Hb0 & Hz0). exists b0. replace (a + (l + 1)) with (a + 1 + l) by lia. split; [exact Hb0 | exact Hz0].
Qed.

(* [comment removed for export] *)
Lemma img_cov_sound : forall E M k lo hi, know_ok SEGS E M k -> img_cov k lo hi = true ->
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k lo hi HK H i Hi. unfold img_cov in H. apply existsb_exists in H as (K & Hin & HK').
  destruct K; try discriminate. apply andb_prop in HK' as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KK. cbn [kentry_ok] in KK. destruct KK as (_ & _ & KK). apply KK. lia.
Qed.

Lemma rdn1_rom : forall M (a : word) b, M a = None -> seg_rom SEGS a = Some b -> rdn SEGS M a 1 = Some [b].
Proof. intros M a b Hm Hr. cbn [rdn]. rewrite Hm, Hr. reflexivity. Qed.

Theorem node_strlen_sound :
  strlen_nspec SEGS PERMc SPTOPc G AINV FXOK RZ (g_strlen G) -> node1_stmt always (node_strlen SEGS nx0 G).
Proof. pose proof sfloor_ge as SFG_.
  intros MS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_strlen in Hn.
  destruct (call_ok_stk nx0 G MSTK_M (g_strlen G) cs) as [ret|] eqn:Hco; [|discriminate].
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G MSTK_M (g_strlen G) cs ret E fx R M model
                ltac:(unfold MSTK_M; lia) HC Hco) as CO.
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  destruct (reg_lit cs 10) as [s|] eqn:Hrl; [|discriminate].
  destruct (img_strlen_from SEGS s SLFUEL) as [len|] eqn:Hsl; [|discriminate].
  cbv zeta in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply some_inj in Hn. subst cs'.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  (* [comment removed for export] *)
  apply Z.leb_le in Hc. apply Z.leb_le in X3. apply Z.ltb_lt in X2.
  set (lo := s - s mod 8) in *. set (hi := s + len + 8 - (s + len) mod 8) in *.
  destruct (img_bytes SEGS lo (Z.to_nat (hi - lo))) as [zs|] eqn:Hib; [|discriminate]. clear X0.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in *.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  destruct (img_strlen_from_spec SLFUEL s len Hsl) as (L0 & Lnz & Lz).
  destruct (reg_lit_sound E cs R 10 s HR ltac:(lia) Hrl) as [R10 SR].
  assert (RO0 : 0 <= g_ro_lo G) by (pose proof G_img_hull; lia). assert (GSB : g_img_hi G <= SB) by (pose proof G_img_shlo; unfold SHMAPLO, SB in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (HLO : lo <= s /\ 0 <= lo) by (subst lo; lia).
  assert (HHI : s + len + 1 <= hi /\ hi <= SB - 1) by (subst hi; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  pose proof (img_cov_sound E MR (kn cs) lo hi HK X1) as IMG.
  assert (HULL : forall i, lo <= i < hi -> rdn SEGS M (Z_to_bv 64 i) 1 <> None).
  { intros i Hi.
    destruct (rdn_img SEGS MR (Z.to_nat (hi - lo)) (Z_to_bv 64 lo) zs) as (bs & Hbs & _).
    - rewrite u64_lit by (unfold SB in *; lia). unfold SB in *; lia.
    - intros j Hj. rewrite u64_lit by (unfold SB in *; lia). apply IMG. lia.
    - rewrite u64_lit by (unfold SB in *; lia). exact Hib.
    - pose proof (rdn_nth SEGS MR (Z.to_nat (hi - lo)) (Z_to_bv 64 lo) bs (Z.to_nat (i - lo))) as X1'.
      rewrite u64_lit in X1' by (unfold SB in *; lia).
      replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in X1' by lia.
      rewrite (rdn_Mr_full E cs model _ _ _ M 1 (Z_to_bv 64 i) _ (co_ainv HC) (X1' ltac:(unfold SB in *; lia) Hbs ltac:(lia))). discriminate. }
  (* [comment removed for export] *)
  pose proof (kshok_x_sound SEGS A G A_img_hi A_img_lo SEGS_in_hull G_img_shlo E MR (kn cs) (ELit s) 0 (ELit (len + 1)) HK X) as KS. cbn [kentry_ok] in KS.
  destruct KS as (KF & K47 & KS).
  assert (ES : estart E (SA (ELit s) 0) = s) by (rewrite estart_SA; cbn [edenot]; rewrite u64_lit by (unfold two64 in SR; lia); lia).
  assert (EL : elenZ E (ELit (len + 1)) = len + 1) by (apply APS.elenZ_lit; unfold SB in *; lia).
  rewrite ES, EL in KS, K47.
  set (v := nxt cs) in *.
  set (Lc := blocks_den E (a_vis cs)) in *. set (Lf := blocks_den E (a_fake cs)) in *.
  unfold cfgF. rewrite Hpc.
  apply (MS fx R M model Lc Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) ret (uE E (reg cs 2)) s len T
            (co_halt HC) (co_fx HC) (co_ainv HC)).
  - (* [comment removed for export] *)
    unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha.
  - change (Z.of_nat 10) with 10%Z in R10. rewrite R10. rewrite u64_lit by (unfold two64 in SR; lia). reflexivity.
  - (* [comment removed for export] *)
    unfold nstr_pre. split; [exact L0|]. split; [unfold SB in *; lia|].
    split; [unfold nmem; left; lia|]. split; [unfold nmem; left; lia|].
    split.
    { intros z Hz. destruct (KS z Hz) as (bt & Hbt & Hv). exists bt. split; [exact (Mr_some _ _ _ _ _ _ Hbt) | exact Hv]. }
    split.
    { intros z Hz. right. right. right. lia. }
    split.
    { intros i Hi. destruct (Lnz i Hi) as (b & Hb & Hnz). exists b. split.
      - eapply rdn_Mr_full; [exact (co_ainv HC)|]. apply rdn1_rom; [apply IMG; lia | exact Hb].
      - intros Heq. apply Hnz. rewrite Heq. reflexivity. }
    split.
    { destruct Lz as (b0 & Hb0 & Hz0). replace (Z_to_bv 8 0) with b0 by (apply bv_eq; rewrite Hz0; reflexivity).
      eapply rdn_Mr_full; [exact (co_ainv HC)|]. apply rdn1_rom; [apply IMG; lia | exact Hb0]. }
    intros i Hi. apply HULL. subst lo hi. lia.
  - (* [comment removed for export] *)
    intros a Ha Hs. unfold scratch in Hs. pose proof GlzConst.ceil_lo. unfold SB, MSTK_M in *. lia.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Ha0 Hfr Hscr HAINV' (Hh' & Hfs' & Hfds').
    set (MRp := Mr E cs mdl' M').
    assert (HLc : forall E', env_agree v E E' -> blocks_den E' (a_vis cs) = Lc) by (intros E' Hag; unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLf : forall E', env_agree v E E' -> blocks_den E' (a_fake cs) = Lf) by (intros E' Hag; unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
    set (E' := ext_call2 E v R' []) in *.
    assert (Hag : env_agree v E E') by (unfold E'; apply ext_call2_agree).
    set (cs' := mem_post cs ret (ELit len) (mem_kept G cs (kn cs) v) 0).
    assert (HMR : Mr E' cs' mdl' M' = MRp).
    { unfold MRp. rewrite (GPS.Mr_fields SHC VSH E' cs cs' mdl' M') by reflexivity. apply (GPS.Mr_agreeE nx0); [exact Hag | exact Hfresh]. }
    assert (HKN : know_ok SEGS E' (Mr E' cs' mdl' M') (kn cs')).
    { rewrite HMR. unfold cs'. cbn [mem_post kn a_ss s_know].
      apply (know_ok_agree' SEGS v E E'); [exact Hag | unfold mem_kept; apply keep_owned_vars |].
      unfold know_ok. apply Forall_forall. intros K HKin.
      eapply (kept_sound_gen E cs fx R M model mdl' M' _ _ _ (kn cs) 0 0 spb spk K HC).
      - intros Mh Hout _. unfold know_ok. apply Forall_forall. intros K0 HK0in.
        eapply kentry_ok_footprint; [exact (proj1 (Forall_forall _ _) HK K0 HK0in)|].
        intros x _. apply Hout. pose proof (u64_range x). lia.
      - exact Hflat.
      - exact Hsp.
      - exact Hspv.
      - exact Hsplo.
      - lia.
      - lia.
      - intros a Ha. exfalso. lia.
      - intros m B C K0 M0 _ a Ha. exfalso. lia.
      - exact HAINV'.
      - intros a Ha. exfalso. lia.
      - intros a Hne. right. exact (Hfr a Hne).
      - exact Hscr.
      - exact HKin. }
    apply (Hk E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + assert (HA' : AINV (blocks_den E' (a_vis cs)) (blocks_den E' (a_fake cs)) (bcost E' (a_vis cs)) (bcount (a_vis cs)) (uE E' (a_meter cs)) M' mdl').
      { rewrite (HLc E' Hag), (HLf E' Hag). rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
        rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact HAINV'. }
      constructor; try (cbn [mem_post a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo a_abytes a_tidset]).
      * (* [comment removed for export] *)
        unfold ret_regs.
        set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved v).
        assert (Hsf : AP.sr_vars_lt (v + NCS) sr1 = true).
        { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ]. unfold caller_saved, NCS. cbn [length]. lia. }
        eapply (regs_ok_agree' (v + NCS)); [unfold E'; apply ext_call2_agree16 | |].
        -- apply sr_vars_lt_upd; [exact Hsf|]. reflexivity.
        -- subst sr1. apply (regs_after_call E _ R R' v (Some (ELit len)) (co_regs HC) Fsr (kept_ok_of_callee_saved _ _ Hkept)).
           split; [reflexivity|]. apply bv_eq. cbn [edenot]. rewrite u64_lit by (unfold SB in *; lia). exact Ha0.
      * reflexivity.
      * (* [comment removed for export] *) exact HKN.
      * exact Hh'.
      * rewrite Hfs'. exact (co_fs HC).
      * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact (co_kcap HC).
      * rewrite (uE_agree v E E' (a_fbud cs) Hag Ffb). exact (co_fbud HC).
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.

Theorem node_strlen_obl : strlen_nspec SEGS PERMc SPTOPc G AINV FXOK RZ (g_strlen G) ->
  OBL_strlen SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros H. exact (node_strlen_sound H). Qed.

End Sound.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MSTK_C : Z := 2816.               (* [comment removed for export] *)

Section Checker.
Variable segs : list Segment.
Variable nx0 : nat.
Variable G : gtable.

Definition lin_eq (k : list kentry) (a b : xterms) : bool := (lin_ge0 k a b && lin_ge0 k b a)%bool.

(* [comment removed for export] *)
Definition ann_lens (cs : acs) (args : list expr) : option (expr * expr) :=
  match args with
  | [] => Some (esub (reg cs 12) (reg cs 10), esub (reg cs 13) (reg cs 10))
  | [lo; ln] => Some (lo, ln)
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_annotate (entry : Z) (args : list expr) (cs : acs) : option acs :=
  match call_ok_stk nx0 G MSTK_C entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let beg := reg cs 10 in let sp := reg cs 2 in let v := nxt cs in let ss := a_ss cs in
      match remove_block beg (a_vis cs), ann_lens cs args with
      | Some (n, live'), Some (lo, ln) =>
          if (lin_eq k [(reg cs 11, 0)] [(beg, 0); (n, 0)]
              && lin_eq k [(reg cs 12, 0)] [(beg, 0); (lo, 0)]
              && lin_eq k [(reg cs 13, 0)] [(beg, 0); (ln, 0)]
              && lin_ge0 k [(n, 0)] [(lo, 0)] && lin_ge0 k [(n, 0)] [(ln, 0)]
              && expr_vars_lt v ln
              && (lin_ge0 k [] [(lo, 0)] || kshok_x k beg 0 lo))%bool
          then Some (ACS (mk_ss ret (ret_regs (s_regs ss) v None)
                               (keep_owned G MSTK_C k (a_vis cs ++ a_fake cs ++ a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne k (a_ghost cs))
                                           (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v ++ [KShOk (SA beg 0) ln]) (v + NCS)%nat)
                         (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                         (a_meter cs) (a_fake cs) (a_fbud cs))
          else None
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition XNann (entry : Z) (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 8 then node_annotate entry args cs else XN0 id args cs.
End Checker.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
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
Variable G : gtable.
Hypothesis AINV_if : AzNodesAlloc3.ifacts A PERMc SPTOPc SHC VSH G AINV.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation Mr := (GPS.Mr SHC VSH).
#[local] Notation hid := (GPS.hid SHC VSH).
#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).
#[local] Notation nkept := (AzNSpec.nkept SWIN PERMc G).

(* [comment removed for export] *)
Definition addressable (M : word -> option byte) (lo hi : Z) : Prop :=
  forall z, lo <= z < hi -> exists b : byte, M (Z_to_bv 64 (SB + z / 8)) = Some b /\ (u b = 0 \/ z mod 8 < u b <= 7).

(* [comment removed for export] *)
Definition annot_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp beg n om nm : Z) L1 L2 T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre SEGS SPTOPc G R M ret sp MSTK_C ->
    Lc = L1 ++ (beg, n) :: L2 ->
    u (getr R (Z_to_bv 5 10)) = beg -> u (getr R (Z_to_bv 5 11)) = beg + n ->
    u (getr R (Z_to_bv 5 12)) = om -> u (getr R (Z_to_bv 5 13)) = nm ->
    beg <= om <= beg + n -> beg <= nm <= beg + n ->
    addressable M beg om ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, nkept (L1 ++ L2) Lf (scratch sp MSTK_C) a \/ beg <= u a < beg + n -> M' a = M a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        addressable M' beg nm ->
        scratch_ok SEGS M' sp MSTK_C ->
        AINV Lc Lf B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.
(* [comment removed for export] *)
Lemma Mr_kept_app_blk : forall E E' cs cs' mdl mdl' M M' B C K B' C' K' sp L1 L2 beg n Lf (a : word),
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) B' C' K' M' mdl' ->
  blocks_den E' (a_vis cs') = blocks_den E (a_vis cs) -> blocks_den E' (a_fake cs') = blocks_den E (a_fake cs) ->
  blocks_den E (a_vis cs) = L1 ++ (beg, n) :: L2 -> blocks_den E (a_fake cs) = Lf ->
  CEIL_run + MSTK_C <= sp ->
  (forall a : word, nkept (L1 ++ L2) Lf (scratch sp MSTK_C) a \/ beg <= u a < beg + n -> M' a = M a) ->
  frame_kept SWIN PERMc SPTOPc G MSTK_C (blocks_den E (a_vis cs ++ a_fake cs)) sp a -> Mr E' cs' mdl' M' a = Mr E cs mdl M a.
Proof.
  intros E E' cs cs' mdl mdl' M M' B C K B' C' K' sp L1 L2 beg n Lf a HA HA' HLc HLf HL HF Hsp FR Hk.
  pose proof AINV_if as (_ & _ & _ & AINV_top & _).
  pose proof (AINV_top _ _ _ _ _ _ _ HA) as HT.
  assert (VIS : in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a
                \/ in_wins SWIN (u a) \/ g_img_lo G <= u a < g_img_hi G).
  { destruct Hk as [[Ho _]|[[Hi _]|[[Ht _]|Hge]]].
    - destruct Ho as [Hb|[Hp|[Hs|Hw]]]; [left; rewrite <- blocks_den_app; exact Hb | right; left; exact Hp | right; right; left; pose proof sfloor_ge; lia | right; right; right; left; exact Hw].
    - right; right; right; right. lia.
    - right; right; left. lia.
    - right; right; left. unfold MSTK_C in Hsp. lia. }
  unfold GPS.Mr.
  rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if E' cs' mdl' B' C' K' M' a HA'
             ltac:(rewrite HLc, HLf; exact VIS))).
  rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if E cs mdl B C K M a HA VIS)).
  apply FR. unfold AzNSpec.nkept. destruct Hk as [[Ho [Hns Hne]]|[[Hi Hnp]|[[Ht Hle]|Hge]]].
  - destruct Ho as [Hb|[Hp|[Hs|Hw]]].
    + rewrite blocks_den_app, HL, HF in Hb. apply in_blocks_app2 in Hb as [Hb|Hb].
      * destruct Hb as (b0 & n0 & Hin & Hz). apply in_app_iff in Hin as [Hin|[Hin|Hin]].
        -- left. left. split; [left; exists b0, n0; split; [apply in_app_iff; left; exact Hin | exact Hz] | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
        -- right. injection Hin as <- <-. exact Hz.
        -- left. left. split; [left; exists b0, n0; split; [apply in_app_iff; right; exact Hin | exact Hz] | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
      * left. left. split; [right; left; exact Hb | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; left; exact Hp | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; right; left; pose proof sfloor_ge; lia | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; right; right; exact Hw | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
  - left. right; left. split; [exact Hi | exact Hnp].
  - left. left. split; [right; right; right; left; lia | split; [unfold scratch; lia | intros _; right; right; lia]].
  - left. left. split; [right; right; right; left; unfold MSTK_C in Hsp; lia | split; [unfold scratch; lia | intros _; right; right; unfold MSTK_C in Hsp; lia]].
Qed.
Lemma lin_eq_sound : forall E M k a b, know_ok SEGS E M k -> lin_eq k a b = true -> xt_den E a = xt_den E b.
Proof.
  intros E M k a b HK H. unfold lin_eq in H. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1). pose proof (lin_ge0_sound SEGS E M k _ _ HK H2). lia.
Qed.

Theorem node_annotate_sound : forall entry args,
  annot_nspec entry -> node1_stmt always (node_annotate nx0 G entry args).
Proof. pose proof sfloor_ge as SFG_.
  intros entry args NS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_annotate in Hn.
  destruct (call_ok_stk nx0 G MSTK_C entry cs) as [ret|] eqn:Hco; [|discriminate].
  assert (Hstk : 0 < MSTK_C < 2 ^ 40) by (unfold MSTK_C; lia).
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G MSTK_C entry cs ret E fx R M model Hstk HC Hco) as CO.
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  destruct (remove_block (reg cs 10) (a_vis cs)) as [[ne live']|] eqn:Hrb; [|discriminate].
  destruct (ann_lens cs args) as [[lo ln]|] eqn:Hlens; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hgate; [|discriminate] end.
  apply some_inj in Hn.
  apply andb_prop in Hgate as [Hgate Hsh]. apply andb_prop in Hgate as [Hgate Hvln]. apply andb_prop in Hgate as [Hgate Hlnn].
  apply andb_prop in Hgate as [Hgate Hlon]. apply andb_prop in Hgate as [Hgate Ha3]. apply andb_prop in Hgate as [Ha1 Ha2].
  destruct (remove_block_split _ _ _ _ Hrb) as (L1e & L2e & HL & HL').
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in HK.
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. change (Z.of_nat 10) with 10 in R10.
  pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (reg_sound E cs R 12 HR ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
  pose proof (reg_sound E cs R 13 HR ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
  set (v := nxt cs) in *.
  set (Lc := blocks_den E (a_vis cs)). set (Lf := blocks_den E (a_fake cs)).
  set (beg := uE E (reg cs 10)). set (n := uE E ne).
  (* [comment removed for export] *)
  pose proof (lin_eq_sound E MR (kn cs) _ _ HK Ha1) as Q1. pose proof (lin_eq_sound E MR (kn cs) _ _ HK Ha2) as Q2.
  pose proof (lin_eq_sound E MR (kn cs) _ _ HK Ha3) as Q3.
  pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK Hlon) as Q4. pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK Hlnn) as Q5.
  cbn [xt_den] in Q1, Q2, Q3, Q4, Q5.
  assert (HLc : Lc = blocks_den E L1e ++ (beg, n) :: blocks_den E L2e).
  { unfold Lc. rewrite HL, blocks_den_app. reflexivity. }
  assert (Hblk : In (beg, n) (Lc ++ Lf)) by (rewrite HLc; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  destruct (AINV_zone _ _ _ _ _ _ _ beg n (co_ainv HC) Hblk) as (Z1 & Z2 & Z3 & Z4).
  pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. unfold PTRLO in Z1.
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHV : forall EE ccs mm MM z, blocks_den EE (a_vis ccs) = Lc -> beg <= z < beg + n ->
            Mr EE ccs mm MM (Z_to_bv 64 (SB + z / 8)) = MM (Z_to_bv 64 (SB + z / 8))).
  { intros EE ccs mm MM z HLL Hz.
    apply (AzNodesAlloc2.Mr_shadow SHC VSH G SHC_stack SHC_image). left. rewrite blocks_den_app, HLL.
    exists beg, n. split; [rewrite HLc; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|].
    rewrite u64_lit by (unfold SB; lia).
    unfold in_shadow, SB. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold cfgF. rewrite Hpc.
  apply (NS fx R M model Lc Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) ret (uE E (reg cs 2)) beg n
            (uE E (reg cs 12)) (uE E (reg cs 13)) (blocks_den E L1e) (blocks_den E L2e) T (co_halt HC) (co_fx HC) (co_ainv HC)).
  - unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha.
  - exact HLc.
  - unfold beg, uE. rewrite R10. reflexivity.
  - rewrite R11. unfold beg, n, uE. lia.
  - unfold uE. rewrite R12. reflexivity.
  - unfold uE. rewrite R13. reflexivity.
  - pose proof (u64_range (edenot E lo)). unfold beg, n, uE. lia.
  - pose proof (u64_range (edenot E ln)). unfold beg, n, uE. lia.
  - (* [comment removed for export] *)
    intros z Hz. apply orb_prop in Hsh as [H0|Hks].
    + pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK H0) as Q0. cbn [xt_den] in Q0. pose proof (u64_range (edenot E lo)). unfold beg, uE in *. lia.
    + pose proof (AzNodesAlloc2.kshok_x_sound SEGS A G A_img_hi A_img_lo SEGS_in_hull G_img_shlo E MR (kn cs) (reg cs 10) 0 lo HK Hks) as KS.
      cbn [kentry_ok] in KS. destruct KS as (_ & _ & KS). rewrite estart_SA in KS. unfold elenZ in KS.
      destruct (KS z ltac:(unfold beg, uE in *; lia)) as (b & Hb & Hv). exists b. split; [|exact Hv].
      rewrite <- Hb. unfold MR. symmetry. apply (SHV E cs model M z eq_refl). unfold beg, n, uE in *. lia.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Hfr Hdef Hadr Hscr HAINV' (Hh' & Hfs' & Hfds').
    set (E' := ext_call E v R').
    assert (Hag : env_agree v E E') by apply ext_call_agree.
    assert (HLcE : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLfE : blocks_den E' (a_fake cs) = Lf) by (unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
    rewrite <- Hn in Hk.
    match type of Hk with context [GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ _ ?c _ _ _ _] => set (cs1 := c) in * end.
    assert (HA' : AINV (blocks_den E' (a_vis cs1)) (blocks_den E' (a_fake cs1)) (bcost E' (a_vis cs1)) (bcount (a_vis cs1))
                       (uE E' (a_meter cs1)) M' mdl').
    { unfold cs1. cbn [a_vis a_fake a_meter]. rewrite HLcE, HLfE. rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact HAINV'. }
    set (MR' := Mr E' cs1 mdl' M').
    assert (Hsub : forall x, In x live' -> In x (a_vis cs)).
    { intros x Hx. rewrite HL' in Hx. rewrite HL. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
    assert (Hbegv : expr_vars_lt v (reg cs 10) = true).
    { pose proof (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) (reg cs 10, ne) ltac:(rewrite HL; apply in_app_iff; right; left; reflexivity)) as X.
      cbn [fst snd] in X. apply andb_prop in X as [X _]. exact X. }
    apply (Hk E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + constructor; try (unfold cs1; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo]).
      * unfold ret_regs.
        pose proof (regs_after_call E (s_regs (a_ss cs)) R R' v None) as RA. cbn iota in RA. apply RA.
        -- exact HR.
        -- exact Fsr.
        -- apply kept_ok_of_callee_saved. exact Hkept.
        -- exact I.
      * reflexivity.
      * fold cs1. fold MR'.
        apply (know_ok_agree' SEGS v E E'); [exact Hag | |].
        { apply kn_vars_lt_app2; [apply keep_owned_vars|]. cbn [kn_vars_lt kentry_vars_lt]. unfold saddr_vars_lt. cbn [a_base]. rewrite Hbegv, Hvln. reflexivity. }
        unfold know_ok. apply Forall_app. split.
        -- apply Forall_forall. intros K0 HKin.
           assert (HKin3 : In K0 (keep_owned G MSTK_C (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                   (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
           { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
           assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
           { rewrite <- app_assoc. exact Hflat. }
           eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G MSTK_C E MR MR' (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                     (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K0
                     ltac:(unfold MSTK_C; lia) HK Hflat' (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].
           ++ pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
           ++ intros a Ha. unfold MR', MR.
              apply (Mr_kept_app_blk E E' cs cs1 model mdl' M M' _ _ _ _ _ _ (uE E (reg cs 2)) (blocks_den E L1e) (blocks_den E L2e) beg n Lf a (co_ainv HC) HA').
              ** unfold cs1. cbn [a_vis]. exact HLcE.
              ** unfold cs1. cbn [a_fake]. exact HLfE.
              ** exact HLc.
              ** reflexivity.
              ** exact (GPS.sfloor_stk _ _ Hsplo).
              ** exact Hfr.
              ** exact Ha.
           ++ intros a Ha. unfold MR'.
              assert (HH : hid E' cs1 mdl' a = false).
              { eapply (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA); [exact HA'|]. right; right; left. unfold uE in *. lia. }
              unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite (AzNodesAlloc2.store_ok1_Mr SEGS SHC VSH) by exact HH. apply Hscr. unfold scratch, uE in *. lia.
           ++ intros a Hew HMa.
              assert (Hai : g_img_lo G <= u a < g_img_hi G) by (unfold errw in Hew; lia).
              unfold MR', MR in *. unfold GPS.Mr in HMa |- *.
              rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA _ _ _ _ _ _ _ a HA' (or_intror (or_intror (or_intror (or_intror Hai)))))).
              rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA _ _ _ _ _ _ _ a (co_ainv HC) (or_intror (or_intror (or_intror (or_intror Hai)))))) in HMa.
              exact (Hdef a HMa).
           ++ intros a Ha. unfold MR', MR.
              assert (OP : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E (a_vis cs ++ a_fake cs))).
              { intros x Hx. rewrite !blocks_den_app in Hx |- *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact Hx].
                unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (Hsub y Hy)]. }
              assert (OQ : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs1 ++ a_fake cs1))).
              { intros x Hx. unfold cs1. cbn [a_vis a_fake]. rewrite blocks_den_app. rewrite HLcE, HLfE. unfold Lc, Lf. rewrite <- blocks_den_app. exact (OP x Hx). }
              assert (ONK : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x ((blocks_den E L1e ++ blocks_den E L2e) ++ Lf)).
              { intros x Hx. rewrite HL' in Hx. rewrite !blocks_den_app in Hx. exact Hx. }
              exact (AzNodesAlloc2.Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs1 model mdl' M M' _ _ _
                       (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) MSTK_C (co_ainv HC)
                       (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                       (blocks_den E L1e ++ blocks_den E L2e) Lf (fun a0 H0 => Hfr a0 (or_introl H0))
                       (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
        -- (* [comment removed for export] *)
           apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. rewrite estart_SA. unfold elenZ.
           pose proof (u64_range (edenot E ln)) as RL. pose proof (u64_range (edenot E (reg cs 10))) as RB.
           split; [unfold flat; rewrite estart_SA; unfold beg, n, uE in *; lia|]. split; [unfold beg, n, uE in *; lia|].
           intros z Hz. destruct (Hadr z ltac:(unfold beg, uE in *; lia)) as (b & Hb & Hv). exists b. split; [|exact Hv].
           rewrite <- Hb. unfold MR'. apply (SHV E' cs1 mdl' M' z); [unfold cs1; cbn [a_vis]; exact HLcE | unfold beg, n, uE in *; lia].
      * exact Hh'.
      * rewrite Hfs'. exact (co_fs HC).
      * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * fold cs1. exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact (co_kcap HC).
      * rewrite (uE_agree v E E' (a_fbud cs) Hag Ffb). exact (co_fbud HC).
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.
End Sound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable RZ : GPS.rz_t.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation zone := (AzFrame.zone SWIN G PERMc SPTOPc HID HIDF).
#[local] Notation perm_owned := (AzFrame.perm_owned SWIN PERMc SPTOPc HID HIDF).
#[local] Notation nkept := (AzNSpec.nkept SWIN PERMc G).
#[local] Notation scratch := AzNSpec.scratch.
#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
Definition h_annot_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp beg n om nm : Z) L1 L2 T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_C ->
    L = L1 ++ (beg, n) :: L2 ->
    u (getr R (Z_to_bv 5 10)) = beg -> u (getr R (Z_to_bv 5 11)) = beg + n ->
    u (getr R (Z_to_bv 5 12)) = om -> u (getr R (Z_to_bv 5 13)) = nm ->
    beg <= om <= beg + n -> beg <= nm <= beg + n ->
    addressable M beg om ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, M' a <> M a -> in_shadow SB beg n (u a) \/ scratch sp MSTK_C a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        addressable M' beg nm ->
        scratch_ok SEGS M' sp MSTK_C ->
        AINVH L LF B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

Lemma nkept_mono : forall L L' Lf scr a, (forall x, In x L -> In x L') -> nkept L Lf scr a -> nkept L' Lf scr a.
Proof.
  intros L L' Lf scr a Hs Hk. unfold AzNSpec.nkept in *.
  assert (IB : forall z, in_blocks L z -> in_blocks L' z) by (intros z (b & m & Hin & Hz); exists b, m; split; [exact (Hs _ Hin) | exact Hz]).
  destruct Hk as [[Ho [Hns He]]|[Hi|[Hl|[Hss|[Hish|Hp]]]]].
  - left. split; [|split; [exact Hns|]].
    + destruct Ho as [H|[H|H]]; [left; exact (IB _ H) | right; left; exact H | right; right; exact H].
    + intros Hw. destruct (He Hw) as [H|[H|H]]; [left; exact (IB _ H) | right; left; exact H | right; right; exact H].
  - right; left. exact Hi.
  - right; right; left. eapply in_lshadow_mono; [|exact Hl]. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hs _ Hx) | right; exact Hx].
  - right; right; right; left. exact Hss.
  - right; right; right; right; left. exact Hish.
  - right; right; right; right; right. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma bshadow_others : forall L1 L2 Lf B C K M mdl beg n z,
  AINVH ((L1 ++ (beg, n) :: L2) ++ HID) (Lf ++ HIDF) B C K M mdl ->
  in_shadow SB beg n z -> in_lshadow (((L1 ++ L2) ++ HID) ++ (Lf ++ HIDF)) z -> False.
Proof.
  intros L1 L2 Lf B C K M mdl beg n z HA Hz (b & m & Hin & Hsh).
  assert (HL : (L1 ++ (beg, n) :: L2) ++ HID = L1 ++ (beg, n) :: (L2 ++ HID)) by (rewrite <- app_assoc; reflexivity).
  assert (Hbeg : In (beg, n) ((L1 ++ (beg, n) :: L2) ++ HID)) by (apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ beg n HA Hbeg) as [_ B8].
  apply in_app_iff in Hin as [Hin|Hin].
  - assert (Hin' : In (b, m) (L1 ++ (L2 ++ HID))).
    { apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff in Hin as [Hin|Hin]|]; apply in_app_iff;
        [left; exact Hin | right; apply in_app_iff; left; exact Hin | right; apply in_app_iff; right; exact Hin]. }
    assert (Hbm : In (b, m) ((L1 ++ (beg, n) :: L2) ++ HID)).
    { rewrite HL. apply in_app_iff in Hin' as [H|H]; apply in_app_iff; [left; exact H | right; right; exact H]. }
    destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hbm) as [_ b8].
    destruct (hp_disj _ _ _ _ HP _ _ _ _ _ _ _ L1 (L2 ++ HID) beg n b m HA HL Hin') as [D|D].
    + exact (in_shadow_apart beg n b m z D b8 Hz Hsh).
    + exact (in_shadow_apart b m beg n z D B8 Hsh Hz).
  - destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as (_ & f8 & _).
    destruct (hp_bfdisj _ _ _ _ HP _ _ _ _ _ _ _ beg n b m HA Hbeg Hin) as [D|D].
    + exact (in_shadow_apart beg n b m z D f8 Hz Hsh).
    + exact (in_shadow_apart b m beg n z D B8 Hsh Hz).
Qed.
(* [comment removed for export] *)
Section BSh.
Variables (L1 L2 Lf : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) (beg n : Z).
Hypothesis HA : AINVH ((L1 ++ (beg, n) :: L2) ++ HID) (Lf ++ HIDF) B C K M mdl.
Hypothesis HPo : perm_owned.
Hypothesis HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0.

Let Hbeg : In (beg, n) (((L1 ++ (beg, n) :: L2) ++ HID) ++ (Lf ++ HIDF)).
Proof. apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity. Qed.
Let OBJ := obj_ablk SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF (L1 ++ (beg, n) :: L2) Lf B C K M mdl HA HPo HT.
Let SUB1 : forall x, In x ((L1 ++ L2) ++ Lf) -> In x (((L1 ++ L2) ++ HID) ++ (Lf ++ HIDF)).
Proof. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; apply in_app_iff; left; exact Hx | right; apply in_app_iff; left; exact Hx]. Qed.
Let SUB2 : forall x, In x (HID ++ HIDF) -> In x (((L1 ++ L2) ++ HID) ++ (Lf ++ HIDF)).
Proof. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; apply in_app_iff; right; exact Hx | right; apply in_app_iff; right; exact Hx]. Qed.
Let SUB3 : forall x, In x (((L1 ++ L2) ++ HID) ++ (Lf ++ HIDF)) -> In x (((L1 ++ (beg, n) :: L2) ++ HID) ++ (Lf ++ HIDF)).
Proof.
  intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact Hx].
  apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact Hx].
  apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma obj_byte_band : forall L z, (forall x, In x L -> In x (((L1 ++ L2) ++ HID) ++ (Lf ++ HIDF))) -> in_blocks L z -> ~ (SHMAPLO <= z < KHI).
Proof.
  intros L z HL (b & m & Hin & Hz).
  exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo b m z (OBJ b m (SUB3 _ (HL _ Hin))) Hz)))).
Qed.

Lemma bshadow_not_kept : forall (sp stk : Z) (a : word),
  in_shadow SB beg n (u a) -> nkept (L1 ++ L2) Lf (scratch sp stk) a \/ beg <= u a < beg + n -> False.
Proof.
  intros sp stk a Hz Hk.
  pose proof (ablk_shadow G G_ro_img G_img_al G_img_shlo beg n (u a) (OBJ beg n Hbeg) Hz) as (S1 & S2 & S3 & S4).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof G_ro_img as (GR0 & GR1 & GR2).
  assert (IMG : ~ (g_img_lo G <= u a < g_img_hi G)) by lia.
  assert (HIDB : forall z, in_blocks HID z -> ~ (SHMAPLO <= z < KHI)).
  { intros z Hb. apply (obj_byte_band HID z); [|exact Hb]. intros x Hx. apply in_app_iff; left; apply in_app_iff; right; exact Hx. }
  assert (HIDFB : forall z, in_blocks HIDF z -> ~ (SHMAPLO <= z < KHI)).
  { intros z Hb. apply (obj_byte_band HIDF z); [|exact Hb]. intros x Hx. apply in_app_iff; right; apply in_app_iff; right; exact Hx. }
  assert (SWB : in_wins SWIN (u a) -> False).
  { intros (lo & hi & Hin & Hw). destruct (SWIN_img lo hi Hin) as (W1 & W2 & _). lia. }
  destruct Hk as [Hk|Hb].
  2:{ exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo beg n (u a) (OBJ beg n Hbeg) Hb))) ltac:(lia)). }
  destruct Hk as [[Ho _]|[[Hi _]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - destruct Ho as [Hb|[Hf|[Hp|[Hc|Hw]]]].
    + apply (obj_byte_band (L1 ++ L2) (u a)); [|exact Hb|lia]. intros x Hx. apply in_app_iff; left; apply in_app_iff; left; exact Hx.
    + apply (obj_byte_band Lf (u a)); [|exact Hf|lia]. intros x Hx. apply in_app_iff; right; apply in_app_iff; left; exact Hx.
    + destruct (proj1 HPo _ Hp) as [Hh|[Hhf|[Hc|Hsw]]].
      * exact (HIDB _ Hh ltac:(lia)).
      * apply in_blocks_fusable in Hhf as (f & m & Hfin & Hfz). apply (HIDFB (u a)); [exists f, m; split; [exact Hfin | lia] | lia].
      * lia.
      * exact (SWB Hsw).
    + lia.
    + exact (SWB Hw).
  - lia.
  - exact (bshadow_others L1 L2 Lf B C K M mdl beg n (u a) HA Hz (in_lshadow_mono _ _ _ SUB1 Hl)).
  - destruct Hss. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - destruct (pshadow_cases SWIN G SHC AINVH HP G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF (L1 ++ (beg, n) :: L2) Lf B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs'|Hi']].
    + exact (bshadow_others L1 L2 Lf B C K M mdl beg n (u a) HA Hz (in_lshadow_mono _ _ _ SUB2 Hl)).
    + destruct Hs'. lia.
    + destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi'). lia.
Qed.

Lemma bshadow_not_zone : forall a : word, in_shadow SB beg n (u a) -> zone a -> False.
Proof. pose proof sfloor_ge as SFG_.
  intros a Hz (Hzn & _ & _).
  pose proof (ablk_shadow G G_ro_img G_img_al G_img_shlo beg n (u a) (OBJ beg n Hbeg) Hz) as (S1 & S2 & S3 & S4).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof G_ro_img as (GR0 & GR1 & GR2).
  destruct Hzn as [Hh|[Hhf|[Ht|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
  - apply (obj_byte_band HID (u a)); [|exact Hh|lia]. intros x Hx. apply in_app_iff; left; apply in_app_iff; right; exact Hx.
  - apply (obj_byte_band HIDF (u a)); [|exact Hhf|lia]. intros x Hx. apply in_app_iff; right; apply in_app_iff; right; exact Hx.
  - lia.
  - lia.
  - exact (bshadow_others L1 L2 Lf B C K M mdl beg n (u a) HA Hz (in_lshadow_mono _ _ _ SUB2 Hlsh)).
  - destruct Hssh. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - lia.
Qed.
End BSh.
Theorem annot_nspec_f : forall entry,
  h_annot_at entry -> annot_nspec SEGS SWIN PERMc SPTOPc AINVf FXOK RZ G entry.
Proof. pose proof sfloor_ge as SFG_.
  intros entry HN fx R M mdl Lc Lf B C K ret sp beg n om nm L1 L2 T Hh HFX HAf Hpre HLc R10 R11 R12 R13 Hom Hnm Hadr Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct Hpre as (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  subst Lc.
  assert (Hstk : 0 <= MSTK_C) by (unfold MSTK_C; lia).
  apply (HN fx R M mdl ((L1 ++ (beg, n) :: L2) ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp beg n om nm L1 (L2 ++ HID) T HFX Hh HA).
  - unfold hcall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact R2|]. split; [exact Hal|].
    split; [exact (GPS.sfloor_stk _ _ Hsplo)|]. split; [exact Hsphi|]. split; [exact R4|]. exact Hstk'.
  - rewrite <- app_assoc. reflexivity.
  - exact R10. - exact R11. - exact R12. - exact R13. - exact Hom. - exact Hnm. - exact Hadr.
  - intros fx' R' M' mdl' HFX' Hkept Hch Hdef Hadr' Hscr HA' Hnm'.
    apply (Hpost fx' R' M' mdl' HFX' Hkept).
    + intros a Hk. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso. destruct (Hch a Hne) as [Hs|Hs].
      * exact (bshadow_not_kept L1 L2 Lf _ _ _ M' mdl' beg n HA' HPo HT sp MSTK_C a Hs Hk).
      * destruct Hk as [Hk|Hb].
        -- apply (scratch_not_nkept SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img PERMc SPTOPc HID HIDF (L1 ++ (beg, n) :: L2) Lf _ _ _ M' mdl' HA' HPo HT sp MSTK_C a Hsplo Hstk Hs).
           eapply nkept_mono; [|exact Hk]. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
        -- assert (Hin : In (beg, n) (((L1 ++ (beg, n) :: L2) ++ HID) ++ (Lf ++ HIDF))).
           { apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity. }
           pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo beg n (u a)
                         (obj_ablk SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF (L1 ++ (beg, n) :: L2) Lf _ _ _ M' mdl' HA' HPo HT beg n Hin) Hb) as (_ & X & _).
           unfold AzNSpec.scratch in Hs. lia.
    + exact Hdef.
    + exact Hadr'.
    + exact Hscr.
    + split; [exact HA'|]. split; [exact HPo|]. split; [exact HT|]. split.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso. destruct (Hch a Hne) as [Hs|Hs].
        -- exact (bshadow_not_zone L1 L2 Lf _ _ _ M' mdl' beg n HA' HPo HT a Hs Hz).
        -- exact (scratch_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF (L1 ++ (beg, n) :: L2) Lf _ _ _ M' mdl' HA' HPo HT sp MSTK_C a Hsplo Hstk Hsptop Hs Hz).
      * intros a Hdz H0. exact (Hdef a (HD a Hdz H0)).
    + exact Hnm'.
Qed.
End Frame.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable RZ : GPS.rz_t.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Variable FTOPc : Z.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Variable KCAP : Z.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Variable entry : Z.
Hypothesis HANN : h_annot_at SEGS G FXOK AINVH RZ entry.

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

Theorem node_annotate_f : forall args,
  GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ always (node_annotate nx0 G entry args).
Proof.
  intros args.
  assert (SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G).
  { intros lo hi Hin. destruct (SWIN_img lo hi Hin) as (S1 & S2 & _). pose proof G_ro_img. lia. }
  assert (G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G) by (pose proof G_ro_img; pose proof G_img_al; lia).
  assert (G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G) by (pose proof (hp_errno _ _ _ _ HP); pose proof G_ro_img; lia).
  exact (node_annotate_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
           (AzFrameAlloc.If_ifacts SWIN G SHC G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo AINVH HP)
           A_img_hi A_img_lo SEGS_in_hull (hp_shc_stack _ _ _ _ HP) (hp_shc_image _ _ _ _ HP) SWIN_img' G_img_hull
           (AzFrame.G_img_ceil G G_img_al G_img_shlo) G_img_shlo G_errno_img entry args
           (annot_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0 entry HANN)).
Qed.

(* [comment removed for export] *)
Theorem XNann_sound : forall XN0,
  GPS.ext_stmt SEGS nx0 XN0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ ->
  GPS.ext_stmt SEGS nx0 (XNann nx0 G entry XN0) PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ.
Proof.
  intros XN0 H0 id args. unfold XNann. destruct (Nat.eqb id 8).
  - apply GPS.node1_stmt_N. exact (node_annotate_f args).
  - exact (H0 id args).
Qed.
End Inst.

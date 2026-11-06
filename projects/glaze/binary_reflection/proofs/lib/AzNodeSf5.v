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
Definition MSTK_SF : Z := 16.               (* [comment removed for export] *)

Section Checker.
Variable segs : list Segment.
Variable nx0 : nat.
Variable G : gtable.

(* [comment removed for export] *)
Definition node_setshadow (entry : Z) (cs : acs) : option acs :=
  match call_ok_stk nx0 G MSTK_SF entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let sp := reg cs 2 in let v := nxt cs in let ss := a_ss cs in
      let '(ab, ao) := split_lit (reg cs 10) in
      match srl3_base ab, reg cs 11 with
      | Some f, ELit m =>
          match remove_frame f (a_fake cs) with
          | Some (ELit n, fk') =>
              if (Z.eqb ao SB && Z.leb 1 m && Z.leb (8 * m) n && Z.ltb n two47)%bool
              then Some (ACS (mk_ss ret (ret_regs (s_regs ss) v None)
                               (keep_owned G MSTK_SF k (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ fk' ++ ghosts_ne k (a_ghost cs))
                                           (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v) (v + NCS)%nat)
                         (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                         (a_meter cs) (a_fake cs) (a_fbud cs))
              else None
          | _ => None
          end
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition XNsf5 (entry : Z) (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 52 then match args with [] => node_setshadow entry cs | _ => None end else XN0 id args cs.
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
Definition setsh_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp f n m : Z) F1 F2 T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre SEGS SPTOPc G R M ret sp MSTK_SF ->
    Lf = F1 ++ (f, n) :: F2 ->
    u (getr R (Z_to_bv 5 10)) = SB + f / 8 -> u (getr R (Z_to_bv 5 11)) = m -> 1 <= m -> 8 * m <= n ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, nkept Lc (F1 ++ F2) (scratch sp MSTK_SF) a \/ f <= u a < f + n -> M' a = M a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        scratch_ok SEGS M' sp MSTK_SF ->
        AINV Lc Lf B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Lemma Mr_kept_app_frm : forall E E' cs cs' mdl mdl' M M' B C K B' C' K' sp Lc F1 F2 f n (a : word),
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) B' C' K' M' mdl' ->
  blocks_den E' (a_vis cs') = blocks_den E (a_vis cs) -> blocks_den E' (a_fake cs') = blocks_den E (a_fake cs) ->
  blocks_den E (a_vis cs) = Lc -> blocks_den E (a_fake cs) = F1 ++ (f, n) :: F2 ->
  CEIL_run + MSTK_SF <= sp ->
  (forall a : word, nkept Lc (F1 ++ F2) (scratch sp MSTK_SF) a \/ f <= u a < f + n -> M' a = M a) ->
  frame_kept SWIN PERMc SPTOPc G MSTK_SF (blocks_den E (a_vis cs ++ a_fake cs)) sp a -> Mr E' cs' mdl' M' a = Mr E cs mdl M a.
Proof.
  intros E E' cs cs' mdl mdl' M M' B C K B' C' K' sp Lc F1 F2 f n a HA HA' HLc HLf HL HF Hsp FR Hk.
  pose proof AINV_if as (_ & _ & _ & AINV_top & _).
  pose proof (AINV_top _ _ _ _ _ _ _ HA) as HT.
  assert (VIS : in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a
                \/ in_wins SWIN (u a) \/ g_img_lo G <= u a < g_img_hi G).
  { destruct Hk as [[Ho _]|[[Hi _]|[[Ht _]|Hge]]].
    - destruct Ho as [Hb|[Hp|[Hs|Hw]]]; [left; rewrite <- blocks_den_app; exact Hb | right; left; exact Hp | right; right; left; pose proof sfloor_ge; lia | right; right; right; left; exact Hw].
    - right; right; right; right. lia.
    - right; right; left. lia.
    - right; right; left. unfold MSTK_SF in Hsp. lia. }
  unfold GPS.Mr.
  rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if E' cs' mdl' B' C' K' M' a HA'
             ltac:(rewrite HLc, HLf; exact VIS))).
  rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if E cs mdl B C K M a HA VIS)).
  apply FR. unfold AzNSpec.nkept. destruct Hk as [[Ho [Hns Hne]]|[[Hi Hnp]|[[Ht Hle]|Hge]]].
  - destruct Ho as [Hb|[Hp|[Hs|Hw]]].
    + rewrite blocks_den_app, HL, HF in Hb. apply in_blocks_app2 in Hb as [Hb|Hb].
      * left. left. split; [left; exact Hb | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
      * destruct Hb as (b0 & n0 & Hin & Hz). apply in_app_iff in Hin as [Hin|[Hin|Hin]].
        -- left. left. split; [right; left; exists b0, n0; split; [apply in_app_iff; left; exact Hin | exact Hz] | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
        -- right. injection Hin as <- <-. exact Hz.
        -- left. left. split; [right; left; exists b0, n0; split; [apply in_app_iff; right; exact Hin | exact Hz] | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; left; exact Hp | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; right; left; pose proof sfloor_ge; lia | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
    + left. left. split; [right; right; right; right; exact Hw | split; [exact Hns | intros He; exact (False_ind _ (Hne He))]].
  - left. right; left. split; [exact Hi | exact Hnp].
  - left. left. split; [right; right; right; left; lia | split; [unfold scratch; lia | intros _; right; right; lia]].
  - left. left. split; [right; right; right; left; unfold MSTK_SF in Hsp; lia | split; [unfold scratch; lia | intros _; right; right; unfold MSTK_SF in Hsp; lia]].
Qed.

Theorem node_setshadow_sound : forall entry,
  setsh_nspec entry -> node1_stmt always (node_setshadow nx0 G entry).
Proof. pose proof sfloor_ge as SFG_.
  intros entry NS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_setshadow in Hn.
  destruct (call_ok_stk nx0 G MSTK_SF entry cs) as [ret|] eqn:Hco; [|discriminate].
  assert (Hstk : 0 < MSTK_SF < 2 ^ 40) by (unfold MSTK_SF; lia).
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G MSTK_SF entry cs ret E fx R M model Hstk HC Hco) as CO.
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  destruct (split_lit (reg cs 10)) as [ab ao] eqn:Hs10.
  destruct (srl3_base ab) as [fe|] eqn:Hsrl; [|discriminate].
  destruct (reg cs 11) as [m| | | | | | |] eqn:Hr11; try discriminate.
  destruct (remove_frame fe (a_fake cs)) as [[ne fk']|] eqn:Hrf; [|discriminate].
  destruct ne as [n| | | | | | |]; try discriminate.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hgate; [|discriminate] end.
  apply some_inj in Hn.
  apply andb_prop in Hgate as [Hgate Hn47]. apply andb_prop in Hgate as [Hgate Hmn]. apply andb_prop in Hgate as [Hao Hm1].
  apply Z.eqb_eq in Hao. subst ao. apply Z.leb_le in Hm1. apply Z.leb_le in Hmn. apply Z.ltb_lt in Hn47. unfold two47 in Hn47.
  destruct (AzNodesAlloc3.remove_frame_split _ _ _ _ Hrf) as (F1e & F2e & HF & HF').
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in HK.
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. change (Z.of_nat 10) with 10 in R10.
  pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  set (v := nxt cs) in *.
  set (Lc := blocks_den E (a_vis cs)). set (Lf := blocks_den E (a_fake cs)).
  set (f := uE E fe).
  assert (Hun : uE E (ELit n) = n) by (unfold uE; cbn [edenot]; apply u64_lit; lia).
  assert (HLf : Lf = blocks_den E F1e ++ (f, n) :: blocks_den E F2e).
  { unfold Lf. rewrite HF, blocks_den_app. cbn [blocks_den map fst snd]. fold (uE E fe). fold (uE E (ELit n)). rewrite Hun. reflexivity. }
  unfold cfgF. rewrite Hpc.
  apply (NS fx R M model Lc Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) ret (uE E (reg cs 2)) f n m
            (blocks_den E F1e) (blocks_den E F2e) T (co_halt HC) (co_fx HC) (co_ainv HC)).
  - unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha.
  - exact HLf.
  - rewrite R10, (split_lit_denot E (reg cs 10) ab SB Hs10), (srl3_base_denot E ab fe Hsrl).
    pose proof (u64_range (edenot E fe)) as FR.
    assert (0 <= u (edenot E fe) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite u64_lit by (unfold SB; lia). unfold f, uE. lia.
  - rewrite R11, Hr11. cbn [edenot]. apply u64_lit. lia.
  - exact Hm1.
  - exact Hmn.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Hfr Hdef Hscr HAINV' (Hh' & Hfs' & Hfds').
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
    assert (Hsub : forall x, In x fk' -> In x (a_fake cs)).
    { intros x Hx. rewrite HF' in Hx. rewrite HF. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
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
        apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K0 HKin.
        assert (HKin3 : In K0 (keep_owned G MSTK_SF (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (a_vis cs ++ fk' ++ ghosts_ne (kn cs) (a_ghost cs))
                                (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
        { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
        assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
        { rewrite <- app_assoc. exact Hflat. }
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G MSTK_SF E MR MR' (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ fk' ++ ghosts_ne (kn cs) (a_ghost cs))
                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K0
                  ltac:(unfold MSTK_SF; lia) HK Hflat' (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].
        -- pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
        -- intros a Ha. unfold MR', MR.
           apply (Mr_kept_app_frm E E' cs cs1 model mdl' M M' _ _ _ _ _ _ (uE E (reg cs 2)) Lc (blocks_den E F1e) (blocks_den E F2e) f n a (co_ainv HC) HA').
           ** unfold cs1. cbn [a_vis]. exact HLcE.
           ** unfold cs1. cbn [a_fake]. exact HLfE.
           ** reflexivity.
           ** exact HLf.
           ** exact (GPS.sfloor_stk _ _ Hsplo).
           ** exact Hfr.
           ** exact Ha.
        -- intros a Ha. unfold MR'.
           assert (HH : hid E' cs1 mdl' a = false).
           { eapply (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA); [exact HA'|]. right; right; left. unfold uE in *. lia. }
           unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite (AzNodesAlloc2.store_ok1_Mr SEGS SHC VSH) by exact HH. apply Hscr. unfold scratch, uE in *. lia.
        -- intros a Hew HMa.
           assert (Hai : g_img_lo G <= u a < g_img_hi G) by (unfold errw in Hew; lia).
           unfold MR', MR in *. unfold GPS.Mr in HMa |- *.
           rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA _ _ _ _ _ _ _ a HA' (or_intror (or_intror (or_intror (or_intror Hai)))))).
           rewrite (mrestrict_visible _ _ _ (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV IFA _ _ _ _ _ _ _ a (co_ainv HC) (or_intror (or_intror (or_intror (or_intror Hai)))))) in HMa.
           exact (Hdef a HMa).
        -- intros a Ha. unfold MR', MR.
           assert (OP : forall x, In x (blocks_den E (a_vis cs ++ fk')) -> In x (blocks_den E (a_vis cs ++ a_fake cs))).
           { intros x Hx. rewrite !blocks_den_app in Hx |- *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
             unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (Hsub y Hy)]. }
           assert (OQ : forall x, In x (blocks_den E (a_vis cs ++ fk')) -> In x (blocks_den E' (a_vis cs1 ++ a_fake cs1))).
           { intros x Hx. unfold cs1. cbn [a_vis a_fake]. rewrite blocks_den_app. rewrite HLcE, HLfE. unfold Lc, Lf. rewrite <- blocks_den_app. exact (OP x Hx). }
           assert (ONK : forall x, In x (blocks_den E (a_vis cs ++ fk')) -> In x (Lc ++ (blocks_den E F1e ++ blocks_den E F2e))).
           { intros x Hx. rewrite HF' in Hx. rewrite !blocks_den_app in Hx. exact Hx. }
           exact (AzNodesAlloc2.Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs1 model mdl' M M' _ _ _
                    (a_vis cs ++ fk' ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) MSTK_SF (co_ainv HC)
                    (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                    Lc (blocks_den E F1e ++ blocks_den E F2e) (fun a0 H0 => Hfr a0 (or_introl H0))
                    (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
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
Definition h_setsh_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp f n m : Z) F1 F2 T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_SF ->
    LF = F1 ++ (f, n) :: F2 ->
    u (getr R (Z_to_bv 5 10)) = SB + f / 8 -> u (getr R (Z_to_bv 5 11)) = m -> 1 <= m -> 8 * m <= n ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, M' a <> M a -> in_shadow SB f n (u a) \/ scratch sp MSTK_SF a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        scratch_ok SEGS M' sp MSTK_SF ->
        AINVH L LF B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

Lemma nkept_monof : forall L Lf Lf' scr a, (forall x, In x Lf -> In x Lf') -> nkept L Lf scr a -> nkept L Lf' scr a.
Proof.
  intros L Lf Lf' scr a Hs Hk. unfold AzNSpec.nkept in *.
  assert (IB : forall z, in_blocks Lf z -> in_blocks Lf' z) by (intros z (b & m & Hin & Hz); exists b, m; split; [exact (Hs _ Hin) | exact Hz]).
  destruct Hk as [[Ho [Hns He]]|[Hi|[Hl|[Hss|[Hish|Hp]]]]].
  - left. split; [|split; [exact Hns|]].
    + destruct Ho as [H|[H|H]]; [left; exact H | right; left; exact (IB _ H) | right; right; exact H].
    + intros Hw. destruct (He Hw) as [H|[H|H]]; [left; exact H | right; left; exact (IB _ H) | right; right; exact H].
  - right; left. exact Hi.
  - right; right; left. eapply in_lshadow_mono; [|exact Hl]. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; exact (Hs _ Hx)].
  - right; right; right; left. exact Hss.
  - right; right; right; right; left. exact Hish.
  - right; right; right; right; right. exact Hp.
Qed.

(* [comment removed for export] *)
Section FSh.
Variables (Lc F1 F2 : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) (f n : Z).
Hypothesis HA : AINVH (Lc ++ HID) ((F1 ++ (f, n) :: F2) ++ HIDF) B C K M mdl.
Hypothesis HPo : perm_owned.
Hypothesis HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0.

Let Hfin : In (f, n) ((Lc ++ HID) ++ ((F1 ++ (f, n) :: F2) ++ HIDF)).
Proof. apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity. Qed.
Let OBJ := obj_ablk SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF Lc (F1 ++ (f, n) :: F2) B C K M mdl HA HPo HT.
Let SUB1 : forall x, In x (Lc ++ (F1 ++ F2)) -> In x ((Lc ++ HID) ++ ((F1 ++ F2) ++ HIDF)).
Proof. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; apply in_app_iff; left; exact Hx | right; apply in_app_iff; left; exact Hx]. Qed.
Let SUB2 : forall x, In x (HID ++ HIDF) -> In x ((Lc ++ HID) ++ ((F1 ++ F2) ++ HIDF)).
Proof. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; apply in_app_iff; right; exact Hx | right; apply in_app_iff; right; exact Hx]. Qed.
Let SUB3 : forall x, In x ((Lc ++ HID) ++ ((F1 ++ F2) ++ HIDF)) -> In x ((Lc ++ HID) ++ ((F1 ++ (f, n) :: F2) ++ HIDF)).
Proof.
  intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
  apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left | right; exact Hx].
  apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
Qed.

Lemma fshadow_others : forall z, in_shadow SB f n z -> in_lshadow ((Lc ++ HID) ++ ((F1 ++ F2) ++ HIDF)) z -> False.
Proof.
  intros z Hz (b & m & Hin & Hsh).
  assert (HLF : (F1 ++ (f, n) :: F2) ++ HIDF = F1 ++ (f, n) :: (F2 ++ HIDF)) by (rewrite <- app_assoc; reflexivity).
  assert (Hf : In (f, n) ((F1 ++ (f, n) :: F2) ++ HIDF)) by (apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f n HA Hf) as (_ & F8 & _).
  apply in_app_iff in Hin as [Hin|Hin].
  - destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as [_ b8].
    destruct (hp_bfdisj _ _ _ _ HP _ _ _ _ _ _ _ b m f n HA Hin Hf) as [D|D].
    + exact (in_shadow_apart b m f n z D F8 Hsh Hz).
    + exact (in_shadow_apart f n b m z D b8 Hz Hsh).
  - assert (Hin' : In (b, m) (F1 ++ (F2 ++ HIDF))).
    { apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff in Hin as [Hin|Hin]|]; apply in_app_iff;
        [left; exact Hin | right; apply in_app_iff; left; exact Hin | right; apply in_app_iff; right; exact Hin]. }
    assert (Hbm : In (b, m) ((F1 ++ (f, n) :: F2) ++ HIDF)).
    { rewrite HLF. apply in_app_iff in Hin' as [H|H]; apply in_app_iff; [left; exact H | right; right; exact H]. }
    destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hbm) as (_ & b8 & _).
    destruct (hp_fdisj _ _ _ _ HP _ _ _ _ _ _ _ F1 (F2 ++ HIDF) f n b m HA HLF Hin') as [D|D].
    + exact (in_shadow_apart f n b m z D b8 Hz Hsh).
    + exact (in_shadow_apart b m f n z D F8 Hsh Hz).
Qed.

(* [comment removed for export] *)
Lemma obj_byte_bandf : forall L z, (forall x, In x L -> In x ((Lc ++ HID) ++ ((F1 ++ F2) ++ HIDF))) -> in_blocks L z -> ~ (SHMAPLO <= z < KHI).
Proof.
  intros L z HL (b & m & Hin & Hz).
  exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo b m z (OBJ b m (SUB3 _ (HL _ Hin))) Hz)))).
Qed.

Lemma fshadow_not_kept : forall (sp stk : Z) (a : word),
  in_shadow SB f n (u a) -> nkept Lc (F1 ++ F2) (scratch sp stk) a \/ f <= u a < f + n -> False.
Proof.
  intros sp stk a Hz Hk.
  pose proof (ablk_shadow G G_ro_img G_img_al G_img_shlo f n (u a) (OBJ f n Hfin) Hz) as (S1 & S2 & S3 & S4).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof G_ro_img as (GR0 & GR1 & GR2).
  assert (IMG : ~ (g_img_lo G <= u a < g_img_hi G)) by lia.
  assert (HIDB : forall z, in_blocks HID z -> ~ (SHMAPLO <= z < KHI)).
  { intros z Hb. apply (obj_byte_bandf HID z); [|exact Hb]. intros x Hx. apply in_app_iff; left; apply in_app_iff; right; exact Hx. }
  assert (HIDFB : forall z, in_blocks HIDF z -> ~ (SHMAPLO <= z < KHI)).
  { intros z Hb. apply (obj_byte_bandf HIDF z); [|exact Hb]. intros x Hx. apply in_app_iff; right; apply in_app_iff; right; exact Hx. }
  assert (SWB : in_wins SWIN (u a) -> False).
  { intros (lo & hi & Hin & Hw). destruct (SWIN_img lo hi Hin) as (W1 & W2 & _). lia. }
  destruct Hk as [Hk|Hb].
  2:{ exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo f n (u a) (OBJ f n Hfin) Hb))) ltac:(lia)). }
  destruct Hk as [[Ho _]|[[Hi _]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - destruct Ho as [Hb|[Hf|[Hp|[Hc|Hw]]]].
    + apply (obj_byte_bandf Lc (u a)); [|exact Hb|lia]. intros x Hx. apply in_app_iff; left; apply in_app_iff; left; exact Hx.
    + apply (obj_byte_bandf (F1 ++ F2) (u a)); [|exact Hf|lia]. intros x Hx. apply in_app_iff; right; apply in_app_iff; left; exact Hx.
    + destruct (proj1 HPo _ Hp) as [Hh|[Hhf|[Hc|Hsw]]].
      * exact (HIDB _ Hh ltac:(lia)).
      * apply in_blocks_fusable in Hhf as (f0 & m0 & Hfin0 & Hfz). apply (HIDFB (u a)); [exists f0, m0; split; [exact Hfin0 | lia] | lia].
      * lia.
      * exact (SWB Hsw).
    + lia.
    + exact (SWB Hw).
  - lia.
  - exact (fshadow_others (u a) Hz (in_lshadow_mono _ _ _ SUB1 Hl)).
  - destruct Hss. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - destruct (pshadow_cases SWIN G SHC AINVH HP G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF Lc (F1 ++ (f, n) :: F2) B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs'|Hi']].
    + exact (fshadow_others (u a) Hz (in_lshadow_mono _ _ _ SUB2 Hl)).
    + destruct Hs'. lia.
    + destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi'). lia.
Qed.

Lemma fshadow_not_zone : forall a : word, in_shadow SB f n (u a) -> zone a -> False.
Proof. pose proof sfloor_ge as SFG_.
  intros a Hz (Hzn & _ & _).
  pose proof (ablk_shadow G G_ro_img G_img_al G_img_shlo f n (u a) (OBJ f n Hfin) Hz) as (S1 & S2 & S3 & S4).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof G_ro_img as (GR0 & GR1 & GR2).
  destruct Hzn as [Hh|[Hhf|[Ht|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
  - apply (obj_byte_bandf HID (u a)); [|exact Hh|lia]. intros x Hx. apply in_app_iff; left; apply in_app_iff; right; exact Hx.
  - apply (obj_byte_bandf HIDF (u a)); [|exact Hhf|lia]. intros x Hx. apply in_app_iff; right; apply in_app_iff; right; exact Hx.
  - lia.
  - lia.
  - exact (fshadow_others (u a) Hz (in_lshadow_mono _ _ _ SUB2 Hlsh)).
  - destruct Hssh. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - lia.
Qed.
End FSh.

Theorem setsh_nspec_f : forall entry,
  h_setsh_at entry -> setsh_nspec SEGS SWIN PERMc SPTOPc AINVf FXOK RZ G entry.
Proof. pose proof sfloor_ge as SFG_.
  intros entry HN fx R M mdl Lc Lf B C K ret sp f n m F1 F2 T Hh HFX HAf Hpre HLf R10 R11 Hm1 Hmn Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct Hpre as (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  subst Lf.
  assert (Hstk : 0 <= MSTK_SF) by (unfold MSTK_SF; lia).
  apply (HN fx R M mdl (Lc ++ HID) ((F1 ++ (f, n) :: F2) ++ HIDF) (B0 + B) (C0 + C) K ret sp f n m F1 (F2 ++ HIDF) T HFX Hh HA).
  - unfold hcall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact R2|]. split; [exact Hal|].
    split; [exact (GPS.sfloor_stk _ _ Hsplo)|]. split; [exact Hsphi|]. split; [exact R4|]. exact Hstk'.
  - rewrite <- app_assoc. reflexivity.
  - exact R10. - exact R11. - exact Hm1. - exact Hmn.
  - intros fx' R' M' mdl' HFX' Hkept Hch Hdef Hscr HA' Hnm'.
    apply (Hpost fx' R' M' mdl' HFX' Hkept).
    + intros a Hk. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso. destruct (Hch a Hne) as [Hs|Hs].
      * exact (fshadow_not_kept Lc F1 F2 _ _ _ M' mdl' f n HA' HPo HT sp MSTK_SF a Hs Hk).
      * destruct Hk as [Hk|Hb].
        -- apply (scratch_not_nkept SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img PERMc SPTOPc HID HIDF Lc (F1 ++ (f, n) :: F2) _ _ _ M' mdl' HA' HPo HT sp MSTK_SF a Hsplo Hstk Hs).
           eapply nkept_monof; [|exact Hk]. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
        -- assert (Hin : In (f, n) ((Lc ++ HID) ++ ((F1 ++ (f, n) :: F2) ++ HIDF))).
           { apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity. }
           pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f n (u a)
                         (obj_ablk SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF Lc (F1 ++ (f, n) :: F2) _ _ _ M' mdl' HA' HPo HT f n Hin) Hb) as (_ & X & _).
           unfold AzNSpec.scratch in Hs. lia.
    + exact Hdef.
    + exact Hscr.
    + split; [exact HA'|]. split; [exact HPo|]. split; [exact HT|]. split.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso. destruct (Hch a Hne) as [Hs|Hs].
        -- exact (fshadow_not_zone Lc F1 F2 _ _ _ M' mdl' f n HA' HPo HT a Hs Hz).
        -- exact (scratch_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF Lc (F1 ++ (f, n) :: F2) _ _ _ M' mdl' HA' HPo HT sp MSTK_SF a Hsplo Hstk Hsptop Hs Hz).
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
Hypothesis HSF : h_setsh_at SEGS G FXOK AINVH RZ entry.

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

Theorem node_setshadow_f :
  GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ always (node_setshadow nx0 G entry).
Proof.
  assert (SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G).
  { intros lo hi Hin. destruct (SWIN_img lo hi Hin) as (S1 & S2 & _). pose proof G_ro_img. lia. }
  assert (G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G) by (pose proof G_ro_img; pose proof G_img_al; lia).
  assert (G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G) by (pose proof (hp_errno _ _ _ _ HP); pose proof G_ro_img; lia).
  exact (node_setshadow_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
           (AzFrameAlloc.If_ifacts SWIN G SHC G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo AINVH HP)
           A_img_hi A_img_lo (hp_shc_stack _ _ _ _ HP) (hp_shc_image _ _ _ _ HP) SWIN_img' G_img_hull
           (AzFrame.G_img_ceil G G_img_al G_img_shlo) G_errno_img entry
           (setsh_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0 entry HSF)).
Qed.

(* [comment removed for export] *)
Theorem XNsf5_sound : forall XN0,
  GPS.ext_stmt SEGS nx0 XN0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ ->
  GPS.ext_stmt SEGS nx0 (XNsf5 nx0 G entry XN0) PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ.
Proof.
  intros XN0 H0 id args. unfold XNsf5. destruct (Nat.eqb id 52).
  - destruct args as [|x l].
    + apply GPS.node1_stmt_N. exact node_setshadow_f.
    + apply GPS.node1_stmt_N. intros cs cs' E fx R M model T _ _ Hn _. discriminate Hn.
  - exact (H0 id args).
Qed.
End Inst.

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
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.LazyFrame OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module GPS.
(* [comment removed for export] *)
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FX : Type := FPState.
Definition mkstF (fx : FX) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  @mkst fx regs pc mem rom.


Definition cfgF (SEGS : list Segment) (fx : FX) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

(* [comment removed for export] *)
Definition blocks_den (E : env) (L : list (expr * expr)) : list (Z * Z) :=
  map (fun p => (uE E (fst p), uE E (snd p))) L.

(* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.   (* [comment removed for export] *)
Fixpoint bcost (E : env) (L : list (expr * expr)) : Z :=
  match L with [] => 0 | p :: r => uE E (snd p) + MBLK + bcost E r end.
Definition bcount (L : list (expr * expr)) : Z := Z.of_nat (length L).

Definition in_blocks (Lc : list (Z * Z)) (z : Z) : Prop :=
  exists b n, In (b, n) Lc /\ b <= z < b + n.
Definition in_wins (W : list (Z * Z)) (z : Z) : Prop :=
  exists lo hi, In (lo, hi) W /\ lo <= z < hi.

(* [comment removed for export] *)
Definition wins_den (E : env) (L : list (expr * expr)) : list (Z * Z) :=
  map (fun p => (uE E (fst p), uE E (fst p) + uE E (snd p))) L.
Definition sptop_den (E : env) (e : expr) : Z :=
  if Z.eqb (uE E e) 0 then 2 ^ 64 else uE E e.     (* [comment removed for export] *)

(* [comment removed for export] *)
Class stk_floor {RC : run_ceil} := STKFLOOR { SFLOOR : Z ; sfloor_ge : CEIL_run <= SFLOOR }.
#[global] Instance stk_floor_default {RC : run_ceil} : stk_floor := {| SFLOOR := CEIL_run ; sfloor_ge := Z.le_refl _ |}.

Lemma sfloor_stk {RC : run_ceil} {SFL : stk_floor} : forall stk sp, SFLOOR + stk <= sp -> CEIL_run + stk <= sp.
Proof. intros stk sp H. pose proof sfloor_ge. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned {RC : run_ceil} {SFL : stk_floor} (SWIN PERM : list (Z * Z)) (TOP : Z) (Lc : list (Z * Z)) (a : word) : Prop :=
  in_blocks Lc (bv_unsigned a) \/ in_wins PERM (bv_unsigned a) \/ (SFLOOR <= bv_unsigned a < TOP) \/ in_wins SWIN (bv_unsigned a).

(* [comment removed for export] *)
Definition floor_sem {RC : run_ceil} {SFL : stk_floor} (E : env) (fl : option expr) (top : expr) (bud : Z) : Prop :=
  match fl with
  | Some f => SFLOOR <= uE E f
  | None => SFLOOR + bud <= sptop_den E top
  end.

(* [comment removed for export] *)
Definition rz_t : Type := config -> TSet -> Prop.
Definition RZ_SILENT1 (SEGS : list Segment) (RZ : rz_t) : Prop :=
  forall c c' T, AsVocab.AsanAcct.node_ok SEGS c unit (fun _ => []) (fun _ => c') -> RZ c' T -> RZ c T.


Definition RZ_EXIT (SEGS : list Segment) (RZ : rz_t) : Prop :=
  forall ms model x8,
    m_halted model = None -> ms_svc_pending ms = Some x8 -> ExitSim.is_exit_no x8 ->
    RZ (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Definition RZ_CONSEQ (RZ : rz_t) : Prop :=
  forall c T T', RZ c T -> t_eq T T' -> RZ c T'.
(* [comment removed for export] *)
Lemma RZ_SILENT1_realizes : forall SEGS, RZ_SILENT1 SEGS (realizes SEGS).
Proof. intros SEGS c c' T. apply rz_silent1. Qed.


Lemma RZ_EXIT_realizes : forall SEGS, RZ_EXIT SEGS (realizes SEGS).
Proof. intros SEGS ms model x8. apply rz_exit. Qed.
Lemma RZ_CONSEQ_realizes : forall SEGS, RZ_CONSEQ (realizes SEGS).
Proof. intros SEGS c T T'. apply rz_conseq. Qed.

(* [comment removed for export] *)
Definition in_shadow (SB b n : Z) (z : Z) : Prop := SB + b / 8 <= z < SB + (b + n + 7) / 8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fusable (p : Z * Z) : Z * Z := (fst p, snd p - 8).
(* [comment removed for export] *)
Definition HEAPLO : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition gowned {RC : run_ceil} {SFL : stk_floor} (SWIN PERM : list (Z * Z)) (TOP SB : Z) (Lc Lf : list (Z * Z)) (a : word) : Prop :=
  owned SWIN PERM TOP (Lc ++ map fusable Lf) a
  \/ (exists b n, In (b, n) Lf /\ in_shadow SB b n (bv_unsigned a)).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
(* [comment removed for export] *)
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.           (* [comment removed for export] *)
Variable nx0 : nat.            (* [comment removed for export] *)
Variable LIMIT : Z.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ISP0 : expr := ELit 0.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XA : nat -> list expr -> acs -> option (acs * acs).   (* [comment removed for export] *)
Variable XT : nat -> list expr -> acs -> option (Z * list spiece * Z).   (* [comment removed for export] *)
Variable KC : nat.

(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Variable SHC : list (Z * Z).
Definition in_shc (z : Z) : bool := existsb (fun iv => (fst iv <=? z) && (z <? snd iv))%bool SHC.
(* [comment removed for export] *)
Variable VSH : list (Z * Z).
Definition in_shv (z : Z) : bool :=
  existsb (fun p => (SB + fst p / 8 <=? z) && (z <? SB + (fst p + snd p + 7) / 8))%bool VSH.

(* [comment removed for export] *)
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
(* [comment removed for export] *)
Variable FTOPc : Z.
(* [comment removed for export] *)
Hypothesis AINV_frame : forall Lc Lf B C K M M' mdl,
  AINV Lc Lf B C K M mdl -> (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB Lc Lf a /\ M' a <> None) ->
  AINV Lc Lf B C K M' mdl.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis AINV_lazy : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, in_shc (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, in_shv (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (bv_unsigned a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV Lc Lf B C K M mdl').
(* [comment removed for export] *)
Hypothesis AINV_facts : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL_run
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))) (m_vm_lazy mdl).

(* [comment removed for export] *)
Variable FXOK : FX -> Prop.

(* [comment removed for export] *)
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Hypothesis HOLES_same : forall h E fs, HOLES h E fs = HOLES 0%nat E fs.

(* [comment removed for export] *)
Variable RZ : rz_t.
Hypothesis RZ_silent1 : RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : RZ_CONSEQ RZ.

#[local] Notation cfg := (cfgF SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lz (model : Model) (a : word) : bool := page_in_ranges (page_base a) (m_vm_lazy model).
Definition in_shb (E : env) (L : list (expr * expr)) (z : Z) : bool :=
  existsb (fun p => (SB + uE E (fst p) / 8 <=? z) && (z <? SB + (uE E (fst p) + uE E (snd p) + 7) / 8))%bool L.
Definition vlz (E : env) (cs : acs) (z : Z) : bool :=
  (in_shc z || in_shv z || in_shb E (a_vis cs ++ a_fake cs) z)%bool.
Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  (lz model a && negb (vlz E cs (bv_unsigned a)))%bool.
Definition Mr (E : env) (cs : acs) (model : Model) (M : word -> option byte) : word -> option byte :=
  mrestrict (hid E cs model) M.

Record cs_ok (E : env) (cs : acs) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := CS_OK {
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E (Mr E cs model M) (kn cs);      (* [comment removed for export] *)
  co_halt  : m_halted model = None;
  co_fs    : m_fs model = FS0;
  co_fds   : APS.fds_ok E (a_fd cs) model;                   (* [comment removed for export] *)
  co_ainv  : AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs))
                  (uE E (a_meter cs)) M model;               (* [comment removed for export] *)
  co_uinv  : UINV E;
  co_fx    : FXOK fx;
  co_perm  : wins_den E (a_ghost cs) = PERMc;
  co_top   : sptop_den E (a_brk cs) = SPTOPc;
  co_kcap  : uE E (a_meter cs) <= KCAP;                      (* [comment removed for export] *)
  co_fbud  : Z.of_nat (length (a_fake cs)) + uE E (a_fbud cs) <= FTOPc;  (* [comment removed for export] *)
  co_floor : floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)   (* [comment removed for export] *)
}.
Arguments co_regs {E cs fx R M model} _.
Arguments co_log {E cs fx R M model} _.
Arguments co_know {E cs fx R M model} _.
Arguments co_halt {E cs fx R M model} _.
Arguments co_fs {E cs fx R M model} _.
Arguments co_fds {E cs fx R M model} _.
Arguments co_ainv {E cs fx R M model} _.
Arguments co_uinv {E cs fx R M model} _.
Arguments co_fx {E cs fx R M model} _.
Arguments co_perm {E cs fx R M model} _.
Arguments co_top {E cs fx R M model} _.
Arguments co_kcap {E cs fx R M model} _.
Arguments co_fbud {E cs fx R M model} _.
Arguments co_floor {E cs fx R M model} _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RUN_SOUND : Prop :=
  forall t K fuel stops pc sr kn nx E M R fx,
    itab_sound SEGS t -> regs_ok E sr R -> know_ok SEGS E M kn ->
    AzSymRun3.sr_vars_lt nx sr = true -> AzSymRun3.kn_vars_lt nx kn = true -> FXOK fx ->
    let ss' := sym_execTX SEGS t K fuel true stops (SS pc sr [] kn nx) in
    exists E' R' fx', env_agree nx E E'
      /\ (nx <= s_next ss')%nat
      /\ regs_ok E' (s_regs ss') R'
      /\ log_flat E' (s_log ss')
      /\ know_ok SEGS E' M (s_know ss')
      /\ FXOK fx'
      /\ msteps SEGS (mkstF fx R (Z_to_bv 64 pc) M (seg_rom SEGS))
                     (mkstF fx' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' M (s_log ss')) (seg_rom SEGS)).
Hypothesis RUN_sound : RUN_SOUND.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model T,
    cs_ok E cs fx R M model -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition node1_stmtN (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model (T : TSet),
    T [] ->
    cs_ok E cs fx R M model -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.
Lemma node1_stmt_N : forall pre node, node1_stmt pre node -> node1_stmtN pre node.
Proof. intros pre node H cs cs' E fx R M model T _ HC Hp Hn Hk. exact (H cs cs' E fx R M model T HC Hp Hn Hk). Qed.

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmtN always (XN id args).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E fx R M model T,
    cs_ok E cs fx R M model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).

(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E fx R M model T,
    cs_ok E cs fx R M model -> XB id args cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csb) M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.

(* [comment removed for export] *)
Definition alt2_stmt : Prop :=
  forall id args cs csa csb E fx R M model Ta Tb,
    cs_ok E cs fx R M model -> XA id args cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csb) M' model') Tb) ->
    RZ (cfg fx R (pc cs) M model) (t_alt2 Ta Tb).

(* [comment removed for export] *)
Definition term_stmt : Prop :=
  forall id args cs fd ps code E fx R M model,
    cs_ok E cs fx R M model -> XT id args cs = Some (fd, ps, code) ->
    RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) (t_exit (Z_to_bv 64 code) (m_fs model))).

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E fx R M model, cs_ok E ch fx R M model ->
    RZ (cfg fx R (pc ch) M model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Fixpoint gplan_ok (p : plan) : bool :=
  let fix lalts_ok (l : list (acs * plan * plan)) : bool :=
    match l with [] => true | (_, b, k) :: r => gplan_ok b && gplan_ok k && lalts_ok r end in
  let fix valts_ok (l : list (acs * plan)) : bool :=
    match l with [] => true | (_, k) :: r => gplan_ok k && valts_ok r end in
  match p with
  | PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k | PHavoc _ k
  | PHavocBig _ k | PFresh _ _ _ k | PExt _ _ k | PEmit _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PFactVia _ _ _ _ k | PFactLe _ _ _ k | PFactScale _ _ _ k
  | PFactLeR _ _ _ _ k | PFactR _ _ _ _ k | PFactLeX _ _ _ _ _ k | PFactX _ _ _ _ _ k => gplan_ok k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2 | PBranch k1 k2 | PBranchP k1 k2 | PCaseReg _ _ k1 k2
  | PAlt2 _ _ k1 k2 => gplan_ok k1 && gplan_ok k2
  | PLoop _ _ _ _ body k => gplan_ok body && gplan_ok k
  | PLoopM _ _ alts _ => lalts_ok alts
  | PVia _ _ _ karms k => gplan_ok karms && gplan_ok k
  | PViaM _ alts _ karms => gplan_ok karms && valts_ok alts
  | PContra | PNext | PHandoff _ | PExit | PMerge _ | PNextW _ | PMergeW _ _ | PHandoffW _ _ | PContraH _ | PTerm _ _ => true
  | PShDisj _ _ _ _ _ | PSys _ _ | PMmap _ _ | PMmapIn _ _ _ | PMmapInH _ _ _ | PMprotect _ _ | PBrk2 _ _ | PX _ _ _
  | PSpin | PFog _ _ _ | PFogNew _ _ _ | PGhost _ _ _ | PUnvis _ _ _ | PHavocBrk _ _ _ | PUnreach | PMmapW _ _ _ _ _ | PMmapH _ _ => false
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma RZ_msteps_restricted_T : forall (H : word -> bool) (HH : H_off_segments SEGS H) AA ms msr' model T,
  lazy_cover H (m_vm_lazy model) AA -> A_wf AA -> MInv AA model ->
  m_halted model = None ->
  msteps SEGS (restrict H ms) msr' ->
  (forall model', MInv AA model' -> same_but_materialized model model' -> hclean H msr' ->
                  RZ (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  RZ (mkCfg ms model) T.
Proof.
  intros H HH AA ms msr' model T.
  exact (AsVocab.AsanAcct.rz_msteps_restricted' SEGS H HH SEGS_wx (fun c => RZ c T) (fun c c' Hn Hr => RZ_silent1 c c' T Hn Hr) AA ms msr' model).
Qed.
Lemma RZ_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses SEGS ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  RZ (mkCfg ms' model) T -> RZ (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply RZ_silent1; [eapply (node_instr_disjoint SEGS); eassumption | exact Hc].
Qed.
(* [comment removed for export] *)
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis node_alt2_sound : alt2_stmt.   (* [comment removed for export] *)
Hypothesis node_term_sound : term_stmt.   (* [comment removed for export] *)
Hypothesis HS_sound : holes_stmt.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_denot_outside : forall E M log (a : word),
  log_flat E log ->
  (forall b w v, In (SE b w v) log -> bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a) ->
  mem_denot E M log a = M a.
Proof.
  intros E M log a. induction log as [|[b w v] rest IH]; intros Hlf Hout; [reflexivity|].
  cbn [mem_denot]. cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hlf').
  pose proof (Hout b w v) as Ha. specialize (Ha (or_introl eq_refl)).
  pose proof (flat_u E b (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Hlen : length (word_to_le_bytes w (edenot E v)) = w) by apply length_N_to_le_bytes.
  destruct Ha as [Ha|Ha].
  - rewrite wbytes_below; [| rewrite Hlen, Hu; lia | rewrite Hu; lia].
    apply IH; [exact Hlf' | intros b' w' v' Hin; apply (Hout b' w' v'); right; exact Hin].
  - rewrite wbytes_above; [| rewrite Hlen, Hu; lia].
    apply IH; [exact Hlf' | intros b' w' v' Hin; apply (Hout b' w' v'); right; exact Hin].
Qed.

Lemma wbytes_same_or_some : forall m addr bs (a : word),
  wbytes m addr bs a = m a \/ exists b, wbytes m addr bs a = Some b.
Proof.
  intros m addr bs. revert m addr. induction bs as [|b rest IH]; intros m addr a; [left; reflexivity|].
  cbn [wbytes]. destruct (IH (fun x => if bv_eqb x addr then Some b else m x) (addr + 1)%bv a) as [H|H].
  - rewrite H. destruct (bv_eqb a addr); [right; exists b; reflexivity | left; reflexivity].
  - right. exact H.
Qed.

Lemma mem_denot_same_or_some : forall E M log (a : word),
  mem_denot E M log a = M a \/ exists b, mem_denot E M log a = Some b.
Proof.
  intros E M log a. induction log as [|[b w v] rest IH]; [left; reflexivity|]. cbn [mem_denot].
  destruct (wbytes_same_or_some (mem_denot E M rest) (adenot E b) (word_to_le_bytes w (edenot E v)) a) as [H|H].
  - rewrite H. exact IH.
  - right. exact H.
Qed.

Lemma in_blocks_den : forall E live b n z,
  In (b, n) live -> uE E b <= z < uE E b + uE E n -> in_blocks (blocks_den E live) z.
Proof.
  intros E live b n z Hin Hz. exists (uE E b), (uE E n). split; [|exact Hz].
  unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

Lemma u_add_off : forall (x : word) (off : Z),
  0 <= bv_unsigned x + off < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (Z_to_bv 64 off))) = bv_unsigned x + off.
Proof.
  intros x off H. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

(* [comment removed for export] *)
Lemma log_flat_In : forall E log b w v, log_flat E log -> In (SE b w v) log -> (w <= 8)%nat /\ flat E b (Z.of_nat w).
Proof.
  intros E log b w v. induction log as [|[b' w' v'] rest IH]; intros Hlf Hin; [destruct Hin|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hf & Hr).
  destruct Hin as [Heq|Hin]; [injection Heq as -> -> ->; split; assumption | exact (IH Hr Hin)].
Qed.

(* [comment removed for export] *)
Lemma in_wins_den : forall E perm b n z,
  In (b, n) perm -> uE E b <= z < uE E b + uE E n -> in_wins (wins_den E perm) z.
Proof.
  intros E perm b n z Hin Hz. exists (uE E b), (uE E b + uE E n). split; [|exact Hz].
  unfold wins_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma in_floor_sound : forall E M k fl top bud b off n (a : word),
  know_ok SEGS E M k -> in_floor k fl top bud b off n = true ->
  floor_sem E fl top bud ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  SFLOOR <= bv_unsigned a < sptop_den E top /\ sptop_den E top < 2 ^ 64.
Proof.
  intros E M k fl top bud b off n a HK Hf Hfl Ha. unfold in_floor in Hf.
  destruct (split_lit top) as [tb tk] eqn:Hsp.
  destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|discriminate].
  destruct fl as [f|]; cbn [floor_sem] in Hfl.
  { (* [comment removed for export] *)
    apply andb_prop in Hf as [Hf L2]. apply andb_prop in Hf as [Hf L1]. apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H3.
    pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK L1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK L2) as X2.
    cbn [xt_den] in X1, X2. pose proof (u64_range (edenot E tb)) as Rt. pose proof (u64_range a) as Ra.
    assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
    { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. unfold two64 in *. lia. }
    rewrite estart_SA in Ha. unfold elenZ in Ha. pose proof GlzConst.ceil_lo as CL.
    assert (Hnz : uE E top <> 0) by (unfold uE in *; lia).
    unfold sptop_den in *. destruct (Z.eqb_spec (uE E top) 0) as [Hz|Hz]; [exfalso; exact (Hnz Hz)|].
    pose proof (u64_range (edenot E top)). unfold uE in *. lia. }
  apply andb_prop in Hf as [Hg Hx]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
  pose proof (xinside_sound SEGS E M k b off n tb (tk - bud) (ELit bud) HK Hx) as [X1 X2].
  rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite (APS.elenZ_lit E bud) in X2 by (unfold CEIL, two64 in *; lia).
  pose proof (u64_range (edenot E tb)) as Rt. pose proof (u64_range a) as Ra.
  assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
  { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. unfold CEIL, two64 in *. lia. }
  assert (Hnz : uE E top <> 0) by (unfold CEIL in *; lia).
  unfold sptop_den in *. destruct (Z.eqb_spec (uE E top) 0) as [Hz|Hz]; [exfalso; exact (Hnz Hz)|].
  rewrite estart_SA in Ha. pose proof (u64_range (edenot E top)). unfold uE in *. lia.
Qed.

Lemma store_owned_sound : forall E M k live perm fl top bud b off n v (a : word),
  know_ok SEGS E M k -> store_owned k (live ++ perm) fl top bud (SE (SA b off) n v) = true -> (n <= 8)%nat ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> floor_sem E fl top bud ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + Z.of_nat n ->
  owned SWIN PERMc SPTOPc (blocks_den E live) a.
Proof.
  intros E M k live perm fl top bud b off n v a HK Hs Hn8 Hperm Htop Hfl Ha. unfold store_owned in Hs. apply orb_prop in Hs as [Hs|Hs].
  - apply existsb_exists in Hs as [[lb0 ln] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct (split_lit lb0) as [lb lk] eqn:Hsp.
    apply andb_prop in Hx as [Hx Hbr0].
    destruct (base_range k lb) as [[blo bhi]|] eqn:Hbr; [|discriminate]. apply Z.leb_le in Hbr0.
    pose proof (base_range_sound SEGS E M k lb blo bhi HK Hbr) as [Hblo _].
    pose proof (xinside_sound SEGS E M k b off (ELit (Z.of_nat n)) lb lk ln HK Hx) as [X1 X2].
    rewrite APS.elenZ_lit in X2 by lia.
    pose proof (split_lit_denot E lb0 lb lk Hsp) as Hd.
    rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite !estart_SA in Ha. unfold elenZ in X2.
    pose proof (u64_range (edenot E lb)). pose proof (u64_range a). pose proof (u64_range (edenot E ln)).
    assert (Hu : uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold uE; rewrite Hd; apply u64_lit; lia).
    apply in_app_iff in Hin as [Hin|Hin].
    + left. eapply (in_blocks_den E live lb0 ln); [exact Hin|]. rewrite Hu. unfold uE. lia.
    + right. left. rewrite <- Hperm. eapply (in_wins_den E perm lb0 ln); [exact Hin|]. rewrite Hu. unfold uE. lia.
  - right. right. left. rewrite <- Htop.
    eapply (proj1 (in_floor_sound E M k fl top bud b off (ELit (Z.of_nat n)) a HK Hs Hfl _)). Unshelve.
    rewrite (APS.elenZ_lit E) by (pose proof (u64_range a); lia). exact Ha.
Qed.


(* [comment removed for export] *)
Lemma srl3_base_denot : forall E b xb, srl3_base b = Some xb ->
  bv_unsigned (edenot E b) = bv_unsigned (edenot E xb) / 8.
Proof.
  intros E b xb H. unfold srl3_base in H.
  destruct b as [| |op x y| | | | |]; try discriminate.
  destruct op; try discriminate. destruct y as [z| | | | | | |]; try discriminate.
  destruct (Z.eq_dec z 3) as [->|Hne].
  - injection H as ->. rewrite u_srl_lit. reflexivity.
  - exfalso. destruct z as [|q|q]; try discriminate; repeat (destruct q; try discriminate). apply Hne. reflexivity.
Qed.

Lemma ealign3_mod8 : forall E M k e, know_ok SEGS E M k -> 3 <= ealign k e -> uE E e mod 8 = 0.
Proof.
  intros E M k e HK H. destruct (ealign_sound SEGS E M k e HK) as [A1 [q Hq]]. unfold uE. rewrite Hq.
  replace (2 ^ ealign k e) with (8 * 2 ^ (ealign k e - 3)) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Zmult_mod, Z.mul_comm. rewrite (Zmult_mod 8). rewrite Z_mod_same_full. rewrite Z.mul_0_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shadow_objs_x_sound : forall E M k objs xb off nn z,
  know_ok SEGS E M k -> 3 <= ealign k xb -> shadow_objs_x k objs xb off nn = true ->
  bv_unsigned (edenot E xb) / 8 + off <= z < bv_unsigned (edenot E xb) / 8 + off + nn ->
  exists bb ln, In (bb, ln) (blocks_den E objs) /\ in_shadow SB bb ln z.
Proof.
  intros E M k objs xb off nn z HK Hal H Hz. pose proof (ealign3_mod8 E M k xb HK Hal) as Hx8. unfold uE in Hx8.
  set (X := bv_unsigned (edenot E xb)) in *. pose proof (u64_range (edenot E xb)) as HXr. fold X in HXr.
  unfold shadow_objs_x in H. apply existsb_exists in H as [[lb0 ln] [Hin H]]. cbn [fst snd] in H.
  destruct (split_lit lb0) as [lb lk] eqn:Hsp.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?Y] end.
  apply expr_eqb_eq in H. subst lb. apply Z.eqb_eq in Y1. apply Z.leb_le in Y0.
  destruct (xlo k ln) as [nlo|] eqn:Hnlo; [|discriminate]. destruct (base_range k xb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  repeat match type of Y with (_ && _)%bool = true => apply andb_prop in Y as [Y ?W] end.
  apply Z.leb_le in Y. apply Z.leb_le in W0. apply Z.ltb_lt in W. unfold two64 in W.
  pose proof (xlo_sound SEGS E M k ln nlo HK Hnlo) as Bn. pose proof (base_range_sound SEGS E M k xb blo bhi HK Hbr) as [B1 B2]. fold X in B1, B2.
  pose proof (u64_range (edenot E ln)) as Hnr.
  exists (uE E lb0), (uE E ln). split.
  - unfold blocks_den. apply in_map_iff. exists (lb0, ln). split; [reflexivity | exact Hin].
  - assert (Hu : uE E lb0 = X + lk).
    { unfold uE. rewrite (split_lit_denot E lb0 xb lk Hsp). apply u64_lit. lia. }
    rewrite Hu. unfold in_shadow, uE.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
Qed.

Lemma shadow_owned_sound : forall E M k objs top b off n (a : word),
  know_ok SEGS E M k -> shadow_owned k objs top b off n = true -> sptop_den E top = SPTOPc ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + Z.of_nat n ->
  exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (bv_unsigned a).
Proof.
  intros E M k objs top b off n a HK H Htop Ha. unfold shadow_owned in H.
  assert (LIT : b = ELit 0 -> shadow_lit_owned objs off (Z.of_nat n) = true ->
            exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (bv_unsigned a)).
  { (* [comment removed for export] *)
    intros -> HL. unfold shadow_lit_owned in HL. apply existsb_exists in HL as [[ob on] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct ob as [lb| | | | | | |]; try discriminate. destruct on as [ln| | | | | | |]; try discriminate.
    repeat match type of Hx with (_ && _)%bool = true => apply andb_prop in Hx as [Hx ?X] end.
    apply Z.leb_le in Hx. repeat match goal with HH : (_ <=? _) = true |- _ => apply Z.leb_le in HH | HH : (_ <? _) = true |- _ => apply Z.ltb_lt in HH end.
    exists lb, ln. split.
    - unfold blocks_den. apply in_map_iff. exists (ELit lb, ELit ln). split; [|exact Hin]. cbn [fst snd]. unfold uE. rewrite !edenot_lit, !u64_lit by (unfold two64 in *; lia). reflexivity.
    - unfold in_shadow. unfold estart in Ha. cbn [a_base a_off] in Ha. rewrite edenot_lit, u64_lit in Ha by lia.
      split; [lia|]. nia. }
  destruct b as [z| | | | | | |]; [destruct z; [exact (LIT eq_refl H) | |]|..]; clear LIT;
  (destruct (srl3_base _) as [xb|] eqn:Hb; [|discriminate];
   apply andb_prop in H as [Hal H]; apply Z.leb_le in Hal;
   rewrite estart_SA in Ha; rewrite (srl3_base_denot E _ xb Hb) in Ha;
   eapply (shadow_objs_x_sound E M k objs xb off (Z.of_nat n)); [exact HK | exact Hal | exact H | lia]).
Qed.

Lemma store_gowned_sound : forall E M k live perm objs fl top bud b off n v (a : word),
  know_ok SEGS E M k -> store_gowned k (live ++ perm) objs fl top bud (SE (SA b off) n v) = true -> (n <= 8)%nat ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> floor_sem E fl top bud ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + Z.of_nat n ->
  owned SWIN PERMc SPTOPc (blocks_den E live) a
  \/ (exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (bv_unsigned a)).
Proof.
  intros E M k live perm objs fl top bud b off n v a HK Hs Hn8 Hperm Htop Hfl Ha. unfold store_gowned in Hs.
  apply orb_prop in Hs as [Hs|Hs].
  - left. eapply store_owned_sound; eassumption.
  - right. eapply shadow_owned_sound; eassumption.
Qed.

Lemma log_gowned_sound : forall E M k live perm objs fl top bud log (a : word),
  know_ok SEGS E M k -> log_gowned k (live ++ perm) objs fl top bud log = true -> log_flat E log ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> floor_sem E fl top bud ->
  mem_denot E M log a <> M a ->
  owned SWIN PERMc SPTOPc (blocks_den E live) a
  \/ (exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (bv_unsigned a)).
Proof.
  intros E M k live perm objs fl top bud log a HK Hown Hlf Hperm Htop Hfl Hne.
  set (P := owned SWIN PERMc SPTOPc (blocks_den E live) a
            \/ (exists bb nn, In (bb, nn) (blocks_den E objs) /\ in_shadow SB bb nn (bv_unsigned a))).
  assert (CASE : forall b w v, In (SE b w v) log ->
            (bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a) \/ P).
  { intros [bb bo] w v Hin. unfold log_gowned in Hown.
    pose proof (proj1 (forallb_forall _ _) Hown _ Hin) as Hs.
    destruct (Z_lt_ge_dec (bv_unsigned a) (estart E (SA bb bo))) as [Hlt|Hge]; [left; left; exact Hlt|].
    destruct (Z_lt_ge_dec (bv_unsigned a) (estart E (SA bb bo) + Z.of_nat w)) as [Hlt2|Hge2]; [|left; right; lia].
    right. unfold P. eapply store_gowned_sound; [exact HK | exact Hs | exact (proj1 (log_flat_In E log _ w v Hlf Hin)) | exact Hperm | exact Htop | exact Hfl | lia]. }
  assert (ALL : (forall b w v, In (SE b w v) log -> bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a) \/ P).
  { clear Hne. induction log as [|[b w v] rest IH]; [left; intros ? ? ? []|].
    assert (Hlf' : log_flat E rest) by (cbn [log_flat] in Hlf; tauto).
    assert (Hown' : log_gowned k (live ++ perm) objs fl top bud rest = true).
    { unfold log_gowned in *. cbn [forallb] in Hown. apply andb_prop in Hown as [_ H]. exact H. }
    destruct (CASE b w v (or_introl eq_refl)) as [Hbw|Ho]; [|right; exact Ho].
    destruct (IH Hown' Hlf') as [Hall|Ho].
    - intros b' w' v' Hin'. apply (CASE b' w' v'). right. exact Hin'.
    - left. intros b' w' v' [Heq|Hin']; [injection Heq as <- <- <-; exact Hbw | apply (Hall b' w' v'); exact Hin'].
    - right. exact Ho. }
  destruct ALL as [Hall|Ho]; [|exact Ho].
  exfalso. apply Hne. apply mem_denot_outside; [exact Hlf | exact Hall].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_den_agree : forall b E E' live,
  env_agree b E E' -> pairs_vars_lt b live = true -> blocks_den E' live = blocks_den E live.
Proof.
  intros b E E' live Hag H. unfold blocks_den. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma bcost_agree : forall b E E' live,
  env_agree b E E' -> pairs_vars_lt b live = true -> bcost E' live = bcost E live.
Proof.
  intros b E E' live Hag H. induction live as [|[x n] r IH]; [reflexivity|].
  unfold pairs_vars_lt in H. cbn [forallb fst snd] in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [_ Hn].
  cbn [bcost snd]. unfold uE at 1 2. rewrite <- (edenot_agree' b E E' _ Hag Hn). rewrite (IH H2). reflexivity.
Qed.

Lemma pairs_vars_lt_app_l : forall b l1 l2, pairs_vars_lt b (l1 ++ l2) = true -> pairs_vars_lt b l1 = true.
Proof. intros b l1 l2 H. unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. Qed.
Lemma pairs_vars_lt_app_r : forall b l1 l2, pairs_vars_lt b (l1 ++ l2) = true -> pairs_vars_lt b l2 = true.
Proof. intros b l1 l2 H. unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma wins_den_agree : forall b E E' l,
  env_agree b E E' -> pairs_vars_lt b l = true -> wins_den E' l = wins_den E l.
Proof.
  intros b E E' l Hag H. unfold wins_den. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma sptop_den_agree : forall b E E' e,
  env_agree b E E' -> AP.expr_vars_lt b e = true -> sptop_den E' e = sptop_den E e.
Proof.
  intros b E E' e Hag H. unfold sptop_den, uE. rewrite <- (edenot_agree' b E E' _ Hag H). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma owned_ffus : forall S P T E vis fk a,
  owned S P T (blocks_den E (vis ++ map ffus fk)) a -> owned S P T (blocks_den E vis ++ map fusable (blocks_den E fk)) a.
Proof.
  intros S P T E vis fk a [Hb|Ho]; [left | right; exact Ho].
  destruct Hb as (b & n & Hin & Hz). unfold blocks_den in Hin. rewrite map_app in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists b, n. split; [apply in_or_app; left; exact Hin | exact Hz].
  - apply in_map_iff in Hin as [p [Heq Hin]]. apply in_map_iff in Hin as [[b0 n0] [Hf Hin0]]. subst p.
    assert (BAD : uE E (snd (ffus (b0, n0))) = 0 -> False).
    { intros H0. cbn [fst snd] in Heq. injection Heq as E1 E2. rewrite <- E2, H0 in Hz. lia. }
    assert (Z0 : uE E (ELit 0) = 0) by (unfold uE; cbn [edenot]; apply u64_lit; lia).
    unfold ffus in Heq, BAD. cbn [fst snd] in Heq, BAD.
    destruct n0 as [m| | | | | | |]; try (exfalso; apply BAD; exact Z0).
    destruct (Z.leb 8 m && Z.ltb m two64)%bool eqn:Hc; [|exfalso; apply BAD; exact Z0].
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
    cbn [fst snd] in Heq. injection Heq as E1 E2. subst b n.
    exists (uE E b0), (uE E (ELit m) - 8). split.
    + apply in_or_app. right. apply in_map_iff. exists (uE E b0, uE E (ELit m)). split; [reflexivity|].
      apply in_map_iff. exists (b0, ELit m). split; [reflexivity | exact Hin0].
    + unfold uE in *. cbn [edenot] in *. rewrite !u64_lit in * by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_ok_parts2 : forall cs, fresh_ok nx0 cs = true ->
  pairs_vars_lt (nxt cs) (a_fake cs) = true /\ AP.expr_vars_lt (nxt cs) (a_meter cs) = true.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  split; assumption.
Qed.
(* [comment removed for export] *)
Lemma fresh_ok_parts3 : forall cs, fresh_ok nx0 cs = true -> AP.expr_vars_lt (nxt cs) (a_fbud cs) = true.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  assumption.
Qed.

Lemma uE_agree : forall b E E' e, env_agree b E E' -> AP.expr_vars_lt b e = true -> uE E' e = uE E e.
Proof. intros b E E' e Hag H. unfold uE. rewrite <- (edenot_agree' b E E' _ Hag H). reflexivity. Qed.

Lemma existsb_exteq : forall {X : Type} (P Q : X -> bool) l, (forall x, In x l -> P x = Q x) -> existsb P l = existsb Q l.
Proof.
  intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma in_shb_agree : forall b E E' L z,
  env_agree b E E' -> pairs_vars_lt b L = true -> in_shb E' L z = in_shb E L z.
Proof.
  intros b E E' L z Hag H. unfold in_shb. apply existsb_exteq. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  rewrite (uE_agree b E E' _ Hag H1), (uE_agree b E E' _ Hag H2). reflexivity.
Qed.

Lemma hid_agree : forall E E' cs model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> hid E' cs model = hid E cs model.
Proof.
  intros E E' cs model Hag Hf. destruct (fresh_ok_parts nx0 cs Hf) as (_ & _ & _ & Fallow & _ & _ & _).
  destruct (fresh_ok_parts2 cs Hf) as [Ffk _].
  apply functional_extensionality. intros a. unfold hid, vlz. f_equal. f_equal. f_equal.
  apply (in_shb_agree (nxt cs)); [exact Hag|].
  unfold pairs_vars_lt in *. rewrite !forallb_app in *. apply andb_prop in Fallow as [F1 F2].
  rewrite F1, Ffk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hid_model : forall E cs m m', m_vm_lazy m' = m_vm_lazy m -> hid E cs m' = hid E cs m.
Proof. intros E cs m m' H. apply functional_extensionality. intros a. unfold hid, lz. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hid_fields : forall E cs cs' m,
  a_vis cs' = a_vis cs -> a_fake cs' = a_fake cs -> a_ghost cs' = a_ghost cs -> hid E cs' m = hid E cs m.
Proof. intros E cs cs' m H1 H2 H3. apply functional_extensionality. intros a. unfold hid, vlz. rewrite H1, H2. reflexivity. Qed.


Lemma Mr_fields : forall E cs cs' m M,
  a_vis cs' = a_vis cs -> a_fake cs' = a_fake cs -> a_ghost cs' = a_ghost cs -> Mr E cs' m M = Mr E cs m M.
Proof. intros. unfold Mr. rewrite (hid_fields E cs cs' m) by assumption. reflexivity. Qed.

Lemma Mr_agreeE : forall E E' cs m M,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> Mr E' cs m M = Mr E cs m M.
Proof. intros. unfold Mr. rewrite (hid_agree E E' cs m) by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Ltac gpsa_know cs :=
  match goal with |- know_ok _ _ (Mr ?E2 ?cs2 ?m ?MM) _ =>
    rewrite (Mr_fields E2 cs cs2 m MM) by reflexivity;
    first [ assumption
          | match goal with H : env_agree _ ?E0 E2 |- _ => rewrite (Mr_agreeE E0 E2 cs m MM) by assumption; assumption end ]
  end.

(* [comment removed for export] *)
Lemma floor_sem_agree : forall b E E' ms top bud,
  env_agree b E E' -> AP.expr_vars_lt b top = true -> AP.maps_vars_lt b ms = true ->
  floor_sem E (acs_floor ms) top bud -> floor_sem E' (acs_floor ms) top bud.
Proof.
  intros b E E' ms top bud Hag Htop Hms H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *.
  - rewrite (sptop_den_agree b E E' top Hag Htop). exact H.
  - cbn [AP.maps_vars_lt forallb am_base am_len] in Hms. apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _].
    unfold uE in *. rewrite <- (edenot_agree' b E E' f Hag Hf). exact H.
Qed.

(* [comment removed for export] *)
Lemma floor_sem_xfer : forall E E' ms top top' bud bud',
  (forall f l kd r, ms = AM f l kd :: r -> uE E' f = uE E f) ->
  sptop_den E' top' = sptop_den E top -> bud' <= bud ->
  floor_sem E (acs_floor ms) top bud -> floor_sem E' (acs_floor ms) top' bud'.
Proof.
  intros E E' ms top top' bud bud' Hf Ht Hb H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *.
  - rewrite Ht. lia.
  - rewrite (Hf f l kd r eq_refl). exact H.
Qed.

(* [comment removed for export] *)
Lemma floor_sem_weaken : forall E ms top bud bud',
  bud' <= bud -> floor_sem E (acs_floor ms) top bud -> floor_sem E (acs_floor ms) top bud'.
Proof.
  intros E ms top bud bud' Hle H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *; [lia | exact H].
Qed.

Lemma cs_ok_agree : forall E E' cs fx R M model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok E cs fx R M model -> cs_ok E' cs fx R M model.
Proof.
  intros E E' cs fx R M model Hag Hf HC.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 cs Hf) as [Ffk Fmt]. pose proof (fresh_ok_parts3 cs Hf) as Ffb.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - unfold Mr. rewrite (hid_agree E E' cs model Hag Hf). eapply know_ok_agree'; eassumption.
  - eapply APS.fds_ok_agree; eassumption.
  - rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffk).
    rewrite (bcost_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). assumption.
  - eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
  - rewrite (wins_den_agree (nxt cs) E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). assumption.
  - rewrite (sptop_den_agree (nxt cs) E E' (a_brk cs) Hag Fbrk). assumption.
  - rewrite (uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). assumption.
  - rewrite (uE_agree (nxt cs) E E' (a_fbud cs) Hag Ffb). assumption.
  - eapply (floor_sem_agree (nxt cs) E E'); [exact Hag | exact Fbrk | exact Fmaps | assumption].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_frame : forall E cs fx R M model ss' fx' R' M',
  cs_ok E cs fx R M model ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] -> know_ok SEGS E (Mr E cs model M') (s_know ss') -> FXOK fx' ->
  (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) a /\ M' a <> None) ->
  cs_ok E (with_ss cs ss') fx' R' M' model.
Proof.
  intros E cs fx R M model ss' fx' R' M' HC HR HL HK HF Hown.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    cbn [with_ss a_ss a_vis a_fake a_meter a_totsz a_eager kn]; try assumption.   (* [comment removed for export] *)
  eapply AINV_frame; [exact CA | exact Hown].
Qed.

Lemma fds_ok_model : forall E f m m',
  m_fds m' = m_fds m -> m_fs m' = m_fs m -> APS.fds_ok E f m -> APS.fds_ok E f m'.
Proof.
  intros E f m m' H1 H2 H. destruct f as [|k len off|]; cbn [APS.fds_ok] in *; rewrite ?H1, ?H2; exact H.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_frame_mat : forall E cs fx R M model ss' fx' R' M' model',
  cs_ok E cs fx R M model ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] -> know_ok SEGS E (Mr E cs model' M') (s_know ss') -> FXOK fx' ->
  (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) a /\ M' a <> None) ->
  same_but_materialized model model' ->
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M model' ->
  cs_ok E (with_ss cs ss') fx' R' M' model'.
Proof.
  intros E cs fx R M model ss' fx' R' M' model' HC HR HL HK HF Hown Hsame HA.
  pose proof (same_but_materialized_frame model model' Hsame) as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & Hhalt & _).
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    cbn [with_ss a_ss a_vis a_fake a_meter a_totsz a_eager kn]; try assumption.
  - rewrite Hhalt. exact CH.
  - rewrite Hfs. exact CF.
  - eapply fds_ok_model; [exact Hfds | exact Hfs | exact CD].
  - eapply AINV_frame; [exact HA | exact Hown].
Qed.

Lemma cs_ok_set_kn : forall E cs fx R M model k',
  cs_ok E cs fx R M model -> know_ok SEGS E (Mr E cs model M) k' -> cs_ok E (set_kn cs k') fx R M model.
Proof.
  intros E cs fx R M model k' HC HK.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    cbn [set_kn with_ss a_ss a_vis a_fake a_meter a_totsz a_eager kn mk_ss s_regs s_log s_know]; try assumption; try reflexivity.
Qed.

Lemma cs_gc_ok : forall gb E cs fx R M model, cs_ok E cs fx R M model -> cs_ok E (cs_gc gb cs) fx R M model.
Proof.
  intros gb E cs fx R M model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know HC).
Qed.

Lemma cs_ok_bump : forall E cs fx R M model d, cs_ok E cs fx R M model -> cs_ok E (bump cs d) fx R M model.
Proof.
  intros E cs fx R M model d HC.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_fake a_meter a_totsz a_eager]; try assumption; try reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_base_le' : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma page_in_ranges_bounds' : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma H_off_segments_hid : forall E cs model Lc Lf B C K M,
  AINV Lc Lf B C K M model -> H_off_segments SEGS (hid E cs model).
Proof.
  intros E cs model Lc Lf B C K M HA a Hh.
  pose proof (AINV_facts _ _ _ _ _ _ _ HA) as HLB.
  unfold hid in Hh. apply andb_prop in Hh as [Hl _]. unfold lz in Hl.
  (* [comment removed for export] *)
  unfold page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. unfold page_size in Hb2.
  pose proof (proj1 (Forall_forall _ _) HLB iv Hin) as (L0 & L1 & L2).
  pose proof (page_base_le' a) as (P1 & P2 & _).
  apply SEGS_in_hull. unfold APS.in_hull. apply andb_false_iff.
  destruct L2 as [L2|L2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

Lemma lazy_cover_hid : forall E cs model AA,
  (forall a : word, in_shc (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true) ->
  (forall a : word, in_shv (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true) ->
  (forall (a : word) b n, In (b, n) (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) ->
     in_shadow SB b n (bv_unsigned a) -> page_allowedb AA (page_base a) = true) ->
  lazy_cover (hid E cs model) (m_vm_lazy model) AA.
Proof.
  intros E cs model AA H1 H2 H3 w Hlz Hh.
  unfold hid in Hh. unfold lz in Hh. rewrite Hlz in Hh. cbn [andb] in Hh. apply negb_false_iff in Hh.
  unfold vlz in Hh. apply orb_prop in Hh as [Hh|Hb]; [apply orb_prop in Hh as [Hc|Hv]; [exact (H1 w Hc) | exact (H2 w Hv)]|].
  unfold in_shb in Hb. apply existsb_exists in Hb as [[b n] [Hin Hz]]. cbn [fst snd] in Hz.
  apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
  apply (H3 w (uE E b) (uE E n)).
  - unfold blocks_den. rewrite <- map_app. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
  - unfold in_shadow. lia.
Qed.

(* [comment removed for export] *)
Lemma run_block_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb false KC bfuel stops cs = Some cs' -> cs_ok E cs fx R M model ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb Hrb HC Hk.
  rewrite run_block_eq in Hrb. unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (fresh_ok_mono nx0 gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  unfold own_live, own_shobjs in Hrb. destruct (log_gowned k ((a_vis cs ++ map ffus (a_fake cs)) ++ a_ghost cs) (a_fake cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (s_log ss')) eqn:Hown; [|discriminate]. cbn [negb] in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  (* [comment removed for export] *)
  set (H := hid E cs model).
  set (Mr0 := Mr E cs model M). assert (HMr0 : Mr0 = mrestrict H M) by reflexivity.
  pose proof (co_ainv HC) as HA.
  destruct (AINV_lazy _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & Hshc & Hshv & Hblk & Hmat).
  pose proof (H_off_segments_hid E cs model _ _ _ _ _ _ HA) as HH.
  pose proof (lazy_cover_hid E cs model AA Hshc Hshv Hblk) as Hcov.
  (* [comment removed for export] *)
  pose proof (RUN_sound IT KC bfuel stops p sr k nx E Mr0 R fx IT_ok HR HK Fsr Fkn (co_fx HC)) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & fx' & Hag & Hle & HR' & Hlf & HK' & HF' & Hms).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs fx R M model Hagc Hf HC) as HC'.
  unfold cfgF, pc. rewrite Hss. cbn [a_ss s_pc].
  (* [comment removed for export] *)
  assert (Hms' : msteps SEGS (restrict H (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)))
                             (mkstF fx' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' Mr0 (s_log ss')) (seg_rom SEGS))).
  { unfold restrict, mkstF, mkst. cbn. rewrite <- HMr0. exact Hms. }
  eapply (RZ_msteps_restricted_T H HH AA); [exact Hcov | exact Hwf | exact Hminv | exact (co_halt HC) | exact Hms' |].
  intros model' Hminv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' Mr0 (s_log ss')) kn').
  { eapply (carry_sound SEGS E' Mr0); [exact Hc | exact Hlf | exact HK' | constructor]. }
  specialize (Hk E' fx' R' (munrestrict H M (mem_denot E' Mr0 (s_log ss'))) model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  apply Hk; [| pose proof (same_but_materialized_frame model model' Hsame) as SF; rewrite Hsame; unfold with_vm_backing; destruct model; reflexivity].
  assert (Fallow' : pairs_vars_lt nx (a_vis cs) = true) by exact (pairs_vars_lt_app_l _ _ _ Fallow).
  assert (Hhid' : hid E' cs model' = H).
  { unfold H. rewrite (hid_model E' cs model model') by (rewrite Hsame; apply m_vm_lazy_wvb).
    apply hid_agree; [exact Hagc | exact Hf]. }
  assert (HOWN : forall a : word, munrestrict H M (mem_denot E' Mr0 (s_log ss')) a <> M a ->
            gowned SWIN PERMc SPTOPc SB (blocks_den E' (a_vis cs)) (blocks_den E' (a_fake cs)) a
            /\ munrestrict H M (mem_denot E' Mr0 (s_log ss')) a <> None).
  { intros a Ha. unfold munrestrict in Ha |- *.
    destruct (H a) eqn:EH; [exfalso; apply Ha; reflexivity|].
    assert (Hne : mem_denot E' Mr0 (s_log ss') a <> Mr0 a).
    { intros X. apply Ha. rewrite X, HMr0. unfold mrestrict. rewrite EH. reflexivity. }
    split.
    2:{ destruct (mem_denot_same_or_some E' Mr0 (s_log ss') a) as [Hs|[b Hb]]; [exfalso; exact (Hne Hs) | rewrite Hb; discriminate]. }
    (* [comment removed for export] *)
    assert (OWN : owned SWIN PERMc SPTOPc (blocks_den E' (a_vis cs ++ map ffus (a_fake cs))) a
              \/ (exists bb nn, In (bb, nn) (blocks_den E' (a_fake cs)) /\ in_shadow SB bb nn (bv_unsigned a))).
    { eapply log_gowned_sound; [| exact Hown | exact Hlf | | | | exact Hne].
      - eapply know_ok_agree'; [exact Hag | rewrite kn_vars_lt_eq; exact Fkn | exact HK].
      - rewrite (wins_den_agree nx E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      - rewrite (sptop_den_agree nx E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      - eapply (floor_sem_agree nx E E'); [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)]. }
    destruct OWN as [Ho|Hsh].
    - left. apply owned_ffus. exact Ho.
    - right. destruct Hsh as (bb & nn & Hin & Hz). exists bb, nn. split; [exact Hin | exact Hz]. }
  eapply cs_ok_frame_mat; [exact HC' | exact HR' | reflexivity | | exact HF' | exact HOWN | exact Hsame |].
  - cbn [mk_ss s_know]. unfold Mr. rewrite Hhid'. rewrite mrestrict_munrestrict.
    (* [comment removed for export] *)
    replace (mrestrict H (mem_denot E' Mr0 (s_log ss'))) with (mem_denot E' Mr0 (s_log ss')); [exact HKc|].
    apply functional_extensionality. intros a. unfold mrestrict. destruct (H a) eqn:EH; [|reflexivity].
    pose proof (Hclean a EH) as HX. cbn [ms_mem mkstF mkst] in HX. first [exact HX | symmetry; exact HX].
  - (* [comment removed for export] *)
    rewrite (blocks_den_agree nx E E' (a_vis cs) Hag Fallow').
    rewrite (blocks_den_agree (nxt cs) E E' (a_fake cs) Hagc (proj1 (fresh_ok_parts2 cs Hf))).
    rewrite (bcost_agree nx E E' (a_vis cs) Hag Fallow').
    rewrite (uE_agree (nxt cs) E E' (a_meter cs) Hagc (proj2 (fresh_ok_parts2 cs Hf))).
    apply Hmat; [exact Hminv' | exact Hsame].
Qed.

Lemma run_block_gc_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb false KC bfuel stops cs = Some cs' -> cs_ok E cs fx R M model ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb false KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound; [exact Hgb | exact Hrb | exact HC |].
  intros E' fx' R' M' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1).
  apply (Hk E' fx' R' M' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.

(* [comment removed for export] *)
Lemma restricted_run_sound : forall E cs fx R M model msr' T,
  cs_ok E cs fx R M model ->
  msteps SEGS (restrict (hid E cs model) (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))) msr' ->
  (forall model',
      same_but_materialized model model' ->
      hid E cs model' = hid E cs model ->
      m_halted model' = None -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
      AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M model' ->
      hclean (hid E cs model) msr' ->
      RZ (mkCfg (unrestrict (hid E cs model) M msr') model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros E cs fx R M model msr' T HC Hms Hk.
  pose proof (co_ainv HC) as HA.
  destruct (AINV_lazy _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & Hshc & Hshv & Hblk & Hmat).
  pose proof (H_off_segments_hid E cs model _ _ _ _ _ _ HA) as HH.
  pose proof (lazy_cover_hid E cs model AA Hshc Hshv Hblk) as Hcov.
  unfold cfgF.
  eapply (RZ_msteps_restricted_T (hid E cs model) HH AA);
    [exact Hcov | exact Hwf | exact Hminv | exact (co_halt HC) | exact Hms |].
  intros model' Hminv' Hsame Hclean.
  pose proof (same_but_materialized_frame model model' Hsame) as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & Hhalt & _).
  cbn [ms_mem mkstF mkst] . apply Hk.
  - exact Hsame.
  - apply hid_model. rewrite Hsame. apply m_vm_lazy_wvb.
  - rewrite Hhalt. exact (co_halt HC).
  - exact Hfs.
  - exact Hfds.
  - apply Hmat; [exact Hminv' | exact Hsame].
  - exact Hclean.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma forget_sound : forall E cs fx R M model ixs,
  cs_ok E cs fx R M model -> cs_ok E (set_kn cs (drop_ixs ixs 0 (kn cs))) fx R M model.
Proof.
  intros E cs fx R M model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know HC) K Hin).
Qed.

Lemma droprange_sound : forall E cs fx R M model b n,
  cs_ok E cs fx R M model -> cs_ok E (node_droprange cs b n) fx R M model.
Proof.
  intros E cs fx R M model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk]. rewrite droprange_sel_eq.
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

Lemma gckeep_sound : forall E cs fx R M model ws,
  cs_ok E cs fx R M model -> cs_ok E (set_kn cs (kn_keep (kn cs) ws)) fx R M model.
Proof.
  intros E cs fx R M model ws HC. apply cs_ok_set_kn; [exact HC|]. unfold kn_keep. apply know_ok_filter. exact (co_know HC).
Qed.

Lemma bump_sound : forall E cs fx R M model m cs',
  cs_ok E cs fx R M model -> node_bump cs m = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [apply cs_ok_bump; exact HC | reflexivity].
Qed.

Lemma split_sound : forall cs e mid lo hi E fx R M model,
  cs_ok E cs fx R M model -> brange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) fx R M model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) fx R M model).
Proof.
  intros cs e mid lo hi E fx R M model HC Hr.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know HC)]).
Qed.

(* [comment removed for export] *)
Lemma probe_lin_facts_sound : forall E M k e (one : bool),
  know_ok SEGS E M k ->
  (if one then 1 <= bv_unsigned (edenot E e) else bv_unsigned (edenot E e) <= 0)%Z ->
  know_ok SEGS E M (probe_lin_facts k e one).
Proof.
  intros E M k e one HK Hv. unfold probe_lin_facts.
  assert (SUBD : forall a b, bv_unsigned (edenot E (esub a b)) = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64).
  { intros a b. unfold esub. rewrite mkAlu_denot. apply u_sub64. }
  assert (XH : forall d h0, (bv_unsigned (edenot E d) <= h0)%Z ->
            (bv_unsigned (edenot E d) <= match xhi k d with Some h' => Z.min h' h0 | None => h0 end)%Z).
  { intros d h0 Hd. destruct (xhi k d) as [h'|] eqn:Hh; [|exact Hd]. pose proof (xhi_sound SEGS E M k d h' HK Hh). lia. }
  assert (GEN : forall x0 y0, e = EAlu ALU_SLTU x0 y0 -> let x := conc_expr k x0 in let y := conc_expr k y0 in
    know_ok SEGS E M (if one then match xhi k y, xlo k x with
                                  | Some hy, Some lx => let d := esub y x in
                                      let h := match xhi k d with Some h' => Z.min h' (hy - lx) | None => hy - lx end in
                                      KRange d 1 h :: match xhi k x with Some hx => if (lin_atomic x || Z.ltb (hy - 1) hx)%bool then [KRange x lx (Z.min hx (hy - 1))] else [] | None => [] end
                                                   ++ match xlo k y with Some ly => if (lin_atomic y || Z.ltb ly (lx + 1))%bool then [KRange y (Z.max ly (lx + 1)) hy] else [] | None => [] end
                                  | _, _ => [] end
                      else match xhi k x, xlo k y with
                           | Some hx, Some ly => let d := esub x y in
                               let h := match xhi k d with Some h' => Z.min h' (hx - ly) | None => hx - ly end in
                               KRange d 0 h :: match xlo k x with Some lx => if (lin_atomic x || Z.ltb lx ly)%bool then [KRange x (Z.max lx ly) hx] else [] | None => [] end
                                            ++ match xhi k y with Some hy => if (lin_atomic y || Z.ltb hx hy)%bool then [KRange y ly (Z.min hy hx)] else [] | None => [] end
                           | _, _ => [] end)).
  { intros x0 y0 He. cbv zeta. set (x := conc_expr k x0). set (y := conc_expr k y0). subst e. cbn [edenot] in Hv. rewrite u_sltu64 in Hv.
    rewrite <- (conc_expr_sound SEGS E M k x0 HK) in Hv. rewrite <- (conc_expr_sound SEGS E M k y0 HK) in Hv. fold x in Hv. fold y in Hv.
    pose proof (u64_range (edenot E x)) as Rx. pose proof (u64_range (edenot E y)) as Ry.
    destruct one.
    - destruct (xhi k y) as [hy|] eqn:Hy; [|constructor]. destruct (xlo k x) as [lx|] eqn:Hx; [|constructor].
      pose proof (xhi_sound SEGS E M k y hy HK Hy). pose proof (xlo_sound SEGS E M k x lx HK Hx).
      destruct (Z.ltb_spec (bv_unsigned (edenot E x)) (bv_unsigned (edenot E y))); [|lia].
      cbv zeta. constructor.
      + cbn [kentry_ok].
        assert (Hd : bv_unsigned (edenot E (esub y x)) = bv_unsigned (edenot E y) - bv_unsigned (edenot E x)) by (rewrite SUBD, Z.mod_small by lia; reflexivity).
        split; [rewrite Hd; lia|]. apply XH. rewrite Hd. lia.
      + apply Forall_app. split.
        * destruct (xhi k x) as [hx|] eqn:Hhx; [|constructor]. destruct (lin_atomic x || Z.ltb (hy - 1) hx)%bool; [|constructor]. pose proof (xhi_sound SEGS E M k x hx HK Hhx).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
        * destruct (xlo k y) as [ly|] eqn:Hly; [|constructor]. destruct (lin_atomic y || Z.ltb ly (lx + 1))%bool; [|constructor]. pose proof (xlo_sound SEGS E M k y ly HK Hly).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
    - destruct (xhi k x) as [hx|] eqn:Hx; [|constructor]. destruct (xlo k y) as [ly|] eqn:Hy; [|constructor].
      pose proof (xhi_sound SEGS E M k x hx HK Hx). pose proof (xlo_sound SEGS E M k y ly HK Hy).
      destruct (Z.ltb_spec (bv_unsigned (edenot E x)) (bv_unsigned (edenot E y))); [lia|].
      cbv zeta. constructor.
      + cbn [kentry_ok].
        assert (Hd : bv_unsigned (edenot E (esub x y)) = bv_unsigned (edenot E x) - bv_unsigned (edenot E y)) by (rewrite SUBD, Z.mod_small by lia; reflexivity).
        split; [rewrite Hd; lia|]. apply XH. rewrite Hd. lia.
      + apply Forall_app. split.
        * destruct (xlo k x) as [lx|] eqn:Hlx; [|constructor]. destruct (lin_atomic x || Z.ltb lx ly)%bool; [|constructor]. pose proof (xlo_sound SEGS E M k x lx HK Hlx).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
        * destruct (xhi k y) as [hy|] eqn:Hhy; [|constructor]. destruct (lin_atomic y || Z.ltb hx hy)%bool; [|constructor]. pose proof (xhi_sound SEGS E M k y hy HK Hhy).
          constructor; [|constructor]. cbn [kentry_ok]. lia. }
  destruct e as [| |op x y| | | | |]; try constructor. destruct op; try constructor; try (apply (GEN x y); reflexivity).
  (* [comment removed for export] *)
  destruct x as [| |op2 a b| | | | |]; try (apply (GEN _ y); reflexivity).
  destruct op2; try (apply (GEN _ y); reflexivity).
  destruct y as [z| | | | | | |]; try (apply (GEN _ _); reflexivity).
  destruct (Z.eq_dec z 1) as [->|Hz].
  2: { destruct z as [|p|p]; try (apply (GEN _ _); reflexivity); destruct p as [p|p|]; try (apply (GEN _ _); reflexivity);
       exfalso; apply Hz; reflexivity. }
  destruct one.
  2: { (* [comment removed for export] *)
       destruct b as [c| | | | | | |]; try constructor.
       cbn [edenot] in Hv. rewrite u_sltu64 in Hv. rewrite u_sub64 in Hv. rewrite (u_lit64a c) in Hv.
       change (bv_unsigned (Z_to_bv 64 1)) with 1 in Hv.
       pose proof (u64_range (edenot E a)) as Ra.
       match type of Hv with context [if ?x then _ else _] => destruct x eqn:Hc end; [cbn in Hv; lia|].
       apply Z.ltb_ge in Hc. rewrite Zminus_mod_idemp_r in Hc.
       assert (Hne : bv_unsigned (edenot E a) <> c).
       { intros He. rewrite He, Z.sub_diag, Z.mod_0_l in Hc; lia. }
       assert (GENc : know_ok SEGS E M
                 match xlo k a, xhi k a with
                 | Some l, Some h => if Z.eqb l c then [KRange a (c + 1) h] else if Z.eqb h c then [KRange a l (c - 1)] else []
                 | _, _ => [] end).
       { destruct (xlo k a) as [l|] eqn:Hl; [|constructor]. destruct (xhi k a) as [h|] eqn:Hh; [|constructor].
         pose proof (xlo_sound SEGS E M k a l HK Hl). pose proof (xhi_sound SEGS E M k a h HK Hh).
         destruct (Z.eqb_spec l c); [constructor; [cbn [kentry_ok]; lia | constructor]|].
         destruct (Z.eqb_spec h c); [constructor; [cbn [kentry_ok]; lia | constructor]|]. constructor. }
       destruct c as [|p|p]; try exact GENc.
       (* [comment removed for export] *)
       destruct (xhi k a) as [h|] eqn:Hh; [|constructor].
       constructor; [|constructor]. cbn [kentry_ok]. split; [lia | exact (xhi_sound SEGS E M k a h HK Hh)]. }
  cbn [edenot] in Hv. rewrite u_sltu64 in Hv. rewrite u_sub64 in Hv.
  change (bv_unsigned (Z_to_bv 64 1)) with 1 in Hv.
  pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
  match type of Hv with context [if ?c then _ else _] => destruct c eqn:Hc end; [|cbn in Hv; lia].
  apply Z.ltb_lt in Hc.
  assert (Hm0 : (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64 = 0) by (pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) (2 ^ 64) ltac:(lia)); lia).
  assert (Heq : bv_unsigned (edenot E a) = bv_unsigned (edenot E b)).
  { destruct (Z.le_gt_cases (bv_unsigned (edenot E b)) (bv_unsigned (edenot E a))).
    - rewrite Z.mod_small in Hm0 by lia. lia.
    - rewrite <- (Z.mod_add _ 1) in Hm0 by lia. rewrite Z.mod_small in Hm0 by lia. lia. }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; rewrite SUBD, Heq, Z.sub_diag, Z.mod_0_l by lia; lia.
Qed.

Lemma fact_sound : forall E cs fx R M model K,
  cs_ok E cs fx R M model -> fact_ok (kn cs) K = true -> cs_ok E (add_kn cs [K]) fx R M model.
Proof.
  intros E cs fx R M model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know HC) | exact H] | exact (co_know HC)].
Qed.

Lemma factvia_ok_sound : forall E M k e via lo hi,
  know_ok SEGS E M k -> factvia_ok k e via lo hi = true -> kentry_ok SEGS E M (KRange e lo hi).
Proof.
  intros E M k e via lo hi HK H. unfold factvia_ok in H.
  destruct (xlo2 k via) as [l1|] eqn:H1; [|discriminate]. destruct (xhi2 k via) as [h1|] eqn:H2; [|discriminate].
  destruct (xlo2 k (esub e via)) as [l2|] eqn:H3; [|discriminate]. destruct (xhi2 k (esub e via)) as [h2|] eqn:H4; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.leb_le in H. apply Z.leb_le in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
  pose proof (APS.xlo2_sound SEGS E M k via l1 HK H1) as B1. pose proof (APS.xhi2_sound SEGS E M k via h1 HK H2) as B2.
  pose proof (APS.xlo2_sound SEGS E M k (esub e via) l2 HK H3) as B3. pose proof (APS.xhi2_sound SEGS E M k (esub e via) h2 HK H4) as B4.
  unfold esub in B3, B4. rewrite mkAlu_denot, u_sub64 in B3, B4.
  cbn [kentry_ok]. pose proof (u64_range (edenot E e)) as Re. pose proof (u64_range (edenot E via)) as Rv.
  unfold two64 in *.
  assert (Hm : (bv_unsigned (edenot E e) - bv_unsigned (edenot E via)) mod 2 ^ 64
               = bv_unsigned (edenot E e) - bv_unsigned (edenot E via)
               \/ (bv_unsigned (edenot E e) - bv_unsigned (edenot E via)) mod 2 ^ 64
               = bv_unsigned (edenot E e) - bv_unsigned (edenot E via) + 2 ^ 64).
  { destruct (Z.leb_spec (bv_unsigned (edenot E via)) (bv_unsigned (edenot E e))).
    - left. apply Z.mod_small. lia.
    - right. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct Hm as [Hm|Hm]; rewrite Hm in B3, B4; lia.
Qed.

Lemma factle_ok_sound : forall E M k e big hi,
  know_ok SEGS E M k -> factle_ok k e big hi = true -> kentry_ok SEGS E M (KRange e 0 hi).
Proof.
  intros E M k e big hi HK H. unfold factle_ok in H. apply andb_prop in H as [Hge Hb].
  destruct (xhi2 k big) as [hb|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hb.
  pose proof (lin_ge0_sound SEGS E M k [(big, 0)] [(e, 0)] HK Hge) as Hle. cbn [xt_den] in Hle.
  pose proof (APS.xhi2_sound SEGS E M k big hb HK Hx) as B. cbn [kentry_ok]. pose proof (u64_range (edenot E e)). lia.
Qed.

Lemma factscale_ok_sound : forall E M k e c hi,
  know_ok SEGS E M k -> factscale_ok k e c hi = true -> kentry_ok SEGS E M (KRange e 0 hi).
Proof.
  intros E M k e c hi HK H. unfold factscale_ok in H.
  destruct (xlo k e) as [l0|] eqn:H0; [|discriminate]. destruct (xhi k e) as [h0|] eqn:H1; [|discriminate].
  destruct (xhi2 k (escale c e)) as [h|] eqn:H2; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.leb_le in X.
  pose proof (xlo_sound SEGS E M k e l0 HK H0) as B0. pose proof (xhi_sound SEGS E M k e h0 HK H1) as B1.
  pose proof (APS.xhi2_sound SEGS E M k (escale c e) h HK H2) as B2.
  unfold escale in B2. rewrite mkMd_denot, u_mul64 in B2. cbn [edenot] in B2. rewrite u_lit64a in B2.
  cbn [kentry_ok]. pose proof (u64_range (edenot E e)) as Re. unfold two64 in *.
  assert (Hh : 0 <= h) by (pose proof (Z.mod_pos_bound (c mod 2 ^ 64 * bv_unsigned (edenot E e)) (2 ^ 64) ltac:(lia)); lia).
  split; [lia|].
  destruct (Z.eq_dec (bv_unsigned (edenot E e)) 0) as [Hz|Hnz].
  { rewrite Hz. apply (Z.le_trans _ (h / c)); [apply Z.div_pos; lia | exact X0]. }
  rewrite (Z.mod_small c) in B2 by nia. rewrite Z.mod_small in B2 by nia.
  apply (Z.le_trans _ (h / c)); [|exact X0]. apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

Lemma casedisj_sound : forall cs b1 b2 csa csb E fx R M model,
  cs_ok E cs fx R M model -> node_casedisj cs b1 b2 = Some (csa, csb) ->
  (cs_ok E csa fx R M model /\ pc csa = pc cs) \/ (cs_ok E csb fx R M model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb E fx R M model HC H. unfold node_casedisj in H.
  pose proof (co_know HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound SEGS E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound SEGS E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj_sound SEGS E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.

Lemma havoc_sound : forall E cs fx R M model rs cs',
  cs_ok E cs fx R M model -> node_havoc nx0 cs rs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC'.
  destruct HC' as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

Lemma havocbig_sound : forall E cs fx R M model K cs',
  cs_ok E cs fx R M model -> node_havocbig nx0 cs K = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs fx R M model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts nx0 cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt nx0 cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 fx R M model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC2|].
  replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
  apply kn_bigsubst_sound; [exact (co_know HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
  intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
  unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
  eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
  clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
  induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
  cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
  destruct x as [a w v| | | | | | | | | |  | fv flo fd]; try (apply IH; assumption).
  destruct (bigb K v); [|apply IH; assumption].
  destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

Lemma fresh_sound : forall r logc base cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_fresh nx0 cs r logc base = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros r logc base cs cs' E fx R M model HC Hn. rewrite node_fresh_eq in Hn. unfold node_fresh_ref in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know HC) as HK.
  pose proof (xlo2_sound SEGS E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (xhi2_sound SEGS E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hcpos : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (HKf : know_ok SEGS E' (Mr E cs model M)
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|rewrite <- (Mr_agreeE E E' cs model M Hag Hfresh); exact (co_know HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (residue_fact_sound SEGS E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC' as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_fake a_meter a_totsz a_eager]; try assumption; try gpsa_know cs.
  - apply regs_ok_respell; [exact CR | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma intro_sound : forall E cs fx R M model lo hi cs',
  cs_ok E cs fx R M model -> node_intro nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (KRange (EVar v) lo hi :: s_know (a_ss cs)) (S v)))
    with (set_kn (bump cs 1) (KRange (EVar v) lo hi :: kn cs)).
  2:{ unfold set_kn, bump, with_ss, mk_ss, kn. cbn. rewrite Nat.add_1_r. reflexivity. }
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC'|].
  constructor; [|exact (co_know HC')]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

Lemma join_sound : forall b off n cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_join SEGS cs b off n = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros b off n cs cs' E fx R M model HC Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound SEGS E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  split; [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 SEGS _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.

Lemma abstractcell_sound : forall E cs fx R M model b n cs',
  cs_ok E cs fx R M model -> node_abstractcell A cs b n = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact SEGS_in_hull | exact HULL_ok | exact (co_know HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know HC) | intros; reflexivity].
Qed.

Lemma havocwords_sound : forall E cs fx R M model bs cs',
  cs_ok E cs fx R M model -> node_havocwords nx0 cs bs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok SEGS bs E _ (kn cs) (nxt cs) (co_know HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC2 | gpsa_know cs].
Qed.

Lemma respell_sound : forall E cs fx R M model r e cs',
  cs_ok E cs fx R M model -> node_respell cs r e = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound SEGS E _ (kn cs) (reg cs r) e (co_know HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_sound : forall E cs fx R M model n,
  cs_ok E cs fx R M model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs fx R M model n HC Hn. rewrite (co_regs HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs fx R M model n z,
  cs_ok E cs fx R M model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs fx R M model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs fx R M model n HC Hn), He. auto.
Qed.

Lemma is_ecall_at_sound : forall cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|]; [|discriminate].
  exists w. unfold two64 in H4. repeat split; auto.
Qed.

(* [comment removed for export] *)
Definition ependF (fx : FX) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := @fp_regs fx; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := @fp_csr fx;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecallF : forall fx regs pc mem rom w,
  fetch_word SEGS pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step SEGS (mkstF fx regs pc mem rom) = MachineOk (ependF fx regs pc mem rom (getr regs 17)).
Proof.
  intros fx regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkstF mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota. reflexivity.
Qed.

Lemma ms_gpr_ependF0 : forall fx regs pc mem rom x8, ms_gpr (ependF fx regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs ependF]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rz_step_ecall : forall ms model ms' T,
  m_halted model = None ->
  RiscvSemantics.step SEGS ms = MachineOk ms' -> ms_svc_pending ms = None -> ms_svc_pending ms' <> None ->
  RZ (mkCfg ms' model) T -> RZ (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hstep Hsvc Hsvc' Hc.
  unfold RiscvSemantics.step, drop_access_report in Hstep.
  destruct (RiscvSemantics.step_accesses SEGS ms) as [[ms1 rs]| |] eqn:Hsa; try discriminate.
  cbn [access_value] in Hstep. injection Hstep as ->.
  destruct (step_accesses_ecall_shape SEGS ms ms' rs Hsa Hsvc') as (-> & _).
  eapply (RZ_step_disjoint ms model ms' []); [exact Hh | exact Hsvc | exact Hsa | | exact Hc].
  intros a n lo sz Hin _. destruct Hin.
Qed.

Lemma node_exit_sound : forall cs code E fx R M model,
  cs_ok E cs fx R M model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
  RZ (cfg fx R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros cs code E fx R M model HC Hec Hn.
  destruct (is_ecall_at_sound cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  unfold node_exit in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [c0|] eqn:H10.
  2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
  destruct (reg_lit_sound E cs fx R M model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
  assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
  { destruct a7 as [|p|p]; try discriminate;
      repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
  destruct H94 as [Ha7 ->].
  assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
  { destruct Ha7 as [-> | ->].
    - left. exact (proj1 (reg_lit_sound E cs fx R M model 17 94 HC ltac:(lia) H17)).
    - right. exact (proj1 (reg_lit_sound E cs fx R M model 17 93 HC ltac:(lia) H17)). }
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E10 in G10. rewrite E17 in G17.
  unfold cfgF. rewrite <- (bv_and_255 c0 Hc0).
  eapply rz_step_ecall; [exact (co_halt HC) | eapply step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  rewrite <- G10. rewrite <- (ms_gpr_ependF0 fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS) (getr R 17)).
  eapply RZ_exit; [exact (co_halt HC) | reflexivity |].
  destruct G17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_den_psubst : forall E J e l,
  blocks_den E (map (psubst J e) l) = blocks_den (upd E J (edenot E e)) l.
Proof.
  intros E J e l. unfold blocks_den. rewrite map_map. apply map_ext. intros [b n]. unfold psubst. cbn [fst snd].
  unfold uE. rewrite !esubst_denot. reflexivity.
Qed.

Lemma wins_den_psubst : forall E J e l,
  wins_den E (map (psubst J e) l) = wins_den (upd E J (edenot E e)) l.
Proof.
  intros E J e l. unfold wins_den. rewrite map_map. apply map_ext. intros [b n]. unfold psubst. cbn [fst snd].
  unfold uE. rewrite !esubst_denot. reflexivity.
Qed.

Lemma sptop_den_esubst : forall E J e x, sptop_den E (esubst J e x) = sptop_den (upd E J (edenot E e)) x.
Proof. intros. unfold sptop_den, uE. rewrite esubst_denot. reflexivity. Qed.
Lemma floor_sem_msubst : forall E J e ms top bud,
  floor_sem E (acs_floor (map (msubst J e) ms)) (esubst J e top) bud <-> floor_sem (upd E J (edenot E e)) (acs_floor ms) top bud.
Proof.
  intros. destruct ms as [|[f l kd] r]; cbn [map msubst acs_floor floor_sem am_base am_len am_kind];
    [rewrite sptop_den_esubst; tauto | unfold uE; rewrite esubst_denot; tauto].
Qed.
Lemma bcost_psubst : forall E J e l, bcost E (map (psubst J e) l) = bcost (upd E J (edenot E e)) l.
Proof.
  intros E J e l. induction l as [|[b n] r IH]; [reflexivity|]. cbn [map bcost psubst fst snd]. unfold uE. rewrite esubst_denot, IH. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma in_shb_psubst : forall E J e L z, in_shb E (map (psubst J e) L) z = in_shb (upd E J (edenot E e)) L z.
Proof.
  intros E J e L z. unfold in_shb. rewrite APS.existsb_map'. apply existsb_exteq. intros [b n] _.
  unfold psubst. cbn [fst snd]. unfold uE. rewrite !esubst_denot. reflexivity.
Qed.
Lemma hid_inst : forall E J e inv model, hid E (inst inv J e) model = hid (upd E J (edenot E e)) inv model.
Proof.
  intros E J e inv model. apply functional_extensionality. intros a. unfold hid, vlz.
  cbn [inst a_vis a_fake a_ghost]. rewrite <- !map_app, in_shb_psubst. reflexivity.
Qed.
Lemma Mr_inst : forall E J e inv model M, Mr E (inst inv J e) model M = Mr (upd E J (edenot E e)) inv model M.
Proof. intros. unfold Mr. rewrite hid_inst. reflexivity. Qed.
Lemma uE_esubst : forall E J e x, uE E (esubst J e x) = uE (upd E J (edenot E e)) x.
Proof. intros. unfold uE. rewrite esubst_denot. reflexivity. Qed.

Lemma cs_ok_inst : forall E J e inv fx R M model, (nx0 <= J)%nat -> s_log (a_ss inv) = [] ->
  cs_ok E (inst inv J e) fx R M model <-> cs_ok (upd E J (edenot E e)) inv fx R M model.
Proof.
  intros E J e inv fx R M model HJ Hlog.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  pose proof (blocks_den_psubst E J e (a_vis inv)) as HV.
  pose proof (blocks_den_psubst E J e (a_fake inv)) as HVF.
  pose proof (wins_den_psubst E J e (a_ghost inv)) as HG.
  pose proof (sptop_den_esubst E J e (a_brk inv)) as HB.
  pose proof (bcost_psubst E J e (a_vis inv)) as HBC.
  pose proof (uE_esubst E J e (a_meter inv)) as HMT.
  pose proof (uE_esubst E J e (a_fbud inv)) as HFB.   (* [comment removed for export] *)
  pose proof (Mr_inst E J e inv model M) as HMR.
  pose proof (floor_sem_msubst E J e (a_maps inv) (a_brk inv) (a_ylo inv)) as HFL.
  assert (AG' : env_agree nx0 (upd E J (edenot E e)) E).
  { destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2]. }
  split; intros HC; destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    rewrite ?HMR in *;
    cbn [inst a_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_fake a_meter a_fbud a_fd a_ghost a_brk a_ylo a_maps mk_ss] in *; try assumption; try reflexivity;
    unfold bcount in *; rewrite ?length_map in *;
    first [ apply regs_ok_inst; assumption
          | apply (proj1 (regs_ok_inst _ _ _ _ _)); assumption
          | apply know_ok_ksubst; assumption
          | apply (proj1 (know_ok_ksubst _ _ _ _ _ _)); assumption
          | apply APS.fds_ok_inst; assumption
          | apply (proj1 (APS.fds_ok_inst _ _ _ _ _)); assumption
          | rewrite <- HV, <- HVF, <- HBC, <- HMT; assumption
          | rewrite HV, HVF, HBC, HMT; assumption
          | rewrite <- HG; assumption
          | rewrite HG; assumption
          | rewrite <- HB; assumption
          | rewrite HB; assumption
          | rewrite <- HMT; assumption
          | rewrite HMT; assumption
          | rewrite <- HFB; assumption
          | rewrite HFB; assumption
          | apply (proj1 HFL); assumption
          | apply (proj2 HFL); assumption
          | eapply UINV_agree; [exact AG | assumption]
          | eapply UINV_agree; [exact AG' | assumption] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tenv (E : env) (th : list expr) : env :=
  Env (fun n => if Nat.ltb n (length th) then edenot E (nth n th (ELit 0)) else ev E n) (eb E).

Lemma tsubst_denot : forall E th x, edenot E (tsubst th x) = edenot (tenv E th) x.
Proof.
  intros E th x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [tsubst edenot]; try reflexivity.
  - cbn [tenv ev]. destruct (Nat.ltb n (length th)); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.
Lemma estart_atsubst : forall E th a, estart E (atsubst th a) = estart (tenv E th) a.
Proof. intros E th [b o]. unfold atsubst, estart. cbn [a_base a_off]. rewrite tsubst_denot. reflexivity. Qed.
Lemma adenot_atsubst : forall E th a, adenot E (atsubst th a) = adenot (tenv E th) a.
Proof. intros E th [b o]. unfold atsubst, adenot. cbn [a_base a_off]. rewrite tsubst_denot. reflexivity. Qed.
Lemma kentry_ok_ktsubst : forall E th M K,
  kentry_ok SEGS E M (ktsubst th K) <-> kentry_ok SEGS (tenv E th) M K.
Proof.
  intros E th M K. set (E' := tenv E th).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n | a n | fv flo fd]; cbn [ktsubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_atsubst, ?adenot_atsubst, ?tsubst_denot; fold E'; tauto.
Qed.
Lemma know_ok_ktsubst : forall E th M k,
  know_ok SEGS E M (map (ktsubst th) k) <-> know_ok SEGS (tenv E th) M k.
Proof.
  intros E th M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ktsubst E th M K); assumption.
Qed.
Lemma regs_ok_tsubst : forall E th sr R,
  regs_ok E (map (tsubst th) sr) R <-> regs_ok (tenv E th) sr R.
Proof.
  intros E th sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (tsubst th) sr) (ELit 0))
                     = edenot (tenv E th) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (tsubst th (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply tsubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.
Lemma blocks_den_ptsubst : forall E th l, blocks_den E (map (ptsubst th) l) = blocks_den (tenv E th) l.
Proof.
  intros E th l. unfold blocks_den. rewrite map_map. apply map_ext. intros [b n]. unfold ptsubst. cbn [fst snd].
  unfold uE. rewrite !tsubst_denot. reflexivity.
Qed.
Lemma bcost_ptsubst : forall E th l, bcost E (map (ptsubst th) l) = bcost (tenv E th) l.
Proof.
  intros E th l. induction l as [|[b n] r IH]; [reflexivity|]. cbn [map bcost ptsubst fst snd].
  unfold uE. rewrite tsubst_denot, IH. reflexivity.
Qed.
Lemma bcost_perm : forall E l l', Permutation.Permutation l l' -> bcost E l = bcost E l'.
Proof. intros E l l' HP. induction HP; cbn [bcost]; lia. Qed.
Lemma bcount_perm : forall l l' : list (expr * expr), Permutation.Permutation l l' -> bcount l = bcount l'.
Proof. intros l l' HP. unfold bcount. rewrite (Permutation.Permutation_length HP). reflexivity. Qed.
Lemma wins_den_ptsubst : forall E th l, wins_den E (map (ptsubst th) l) = wins_den (tenv E th) l.
Proof.
  intros E th l. unfold wins_den. rewrite map_map. apply map_ext. intros [b n]. unfold ptsubst. cbn [fst snd].
  unfold uE. rewrite !tsubst_denot. reflexivity.
Qed.
Lemma sptop_den_tsubst : forall E th x, sptop_den E (tsubst th x) = sptop_den (tenv E th) x.
Proof. intros. unfold sptop_den, uE. rewrite tsubst_denot. reflexivity. Qed.
(* [comment removed for export] *)
Lemma in_shb_ptsubst : forall E th L z, in_shb E (map (ptsubst th) L) z = in_shb (tenv E th) L z.
Proof.
  intros E th L z. unfold in_shb. rewrite APS.existsb_map'. apply existsb_exteq. intros [b n] _.
  unfold ptsubst. cbn [fst snd]. unfold uE. rewrite !tsubst_denot. reflexivity.
Qed.
Lemma uE_tsubst : forall E th x, uE E (tsubst th x) = uE (tenv E th) x.
Proof. intros. unfold uE. rewrite tsubst_denot. reflexivity. Qed.
Lemma fds_ok_ftsubst : forall E th f model, APS.fds_ok E (ftsubst th f) model <-> APS.fds_ok (tenv E th) f model.
Proof.
  intros E th f model. destruct f as [|k l o|]; cbn [ftsubst APS.fds_ok]; try tauto.
  rewrite !uE_tsubst, !tsubst_denot. replace (eb (tenv E th)) with (eb E) by reflexivity. tauto.
Qed.


(* [comment removed for export] *)
Lemma th_id_below_agree : forall lo th E, th_id_below lo th = true -> env_agree lo E (tenv E th).
Proof.
  intros lo th E H. unfold th_id_below in H. split; [|reflexivity]. intros n Hn. cbn [tenv ev].
  destruct (Nat.ltb_spec n (length th)) as [Hlt|Hge]; [|reflexivity].
  pose proof (proj1 (forallb_forall _ _) H n ltac:(apply in_seq; lia)) as Hi. cbn beta in Hi.
  destruct (nth_error th n) as [x|] eqn:Hx; [| apply nth_error_None in Hx; lia].
  destruct x as [z|j| | | | | |]; try discriminate. apply Nat.eqb_eq in Hi. subst j.
  rewrite (nth_error_nth _ _ _ Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kpure_entails_sound : forall E M k K,
  know_ok SEGS E M k -> kpure_entails k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. rewrite kpure_entails_eq in H. destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|[b1 o1] n1 [b2 o2] n2|a n c|a n | a n | fv flo fd]; try discriminate; cbn [kentry_ok kpure_entails_ref] in *.
  - (* [comment removed for export] *)
    apply andb_prop in H as [Hm Hd]. apply Z.ltb_lt in Hm. apply Z.eqb_eq in Hd.
    destruct (ealign_sound SEGS E M k e HK) as [A1 [q Hq]]. split; [lia|].
    apply Z.mod_divide in Hd; [|lia]. destruct Hd as [r Hr]. rewrite Hq, Hr.
    rewrite Z.mul_assoc. apply Z_mod_mult.
  - (* [comment removed for export] *)
    apply orb_prop in H as [H|H].
    + destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
      apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      pose proof (APS.xlo2_sound SEGS E M k e l HK Hl). pose proof (APS.xhi2_sound SEGS E M k e h HK Hh). lia.
    + assert (HH : (krange_lin k e lo hi || (lin_ge0 k [(e, 0)] [(ELit 0, lo)] && lin_ge0 k [(ELit 0, hi)] [(e, 0)])
                    || (lin_ge0d 2 k [(e, 0)] [(ELit 0, lo)] && lin_ge0d 2 k [(ELit 0, hi)] [(e, 0)]))%bool = true) by (destruct e; try discriminate H; exact H).
      clear H. apply orb_prop in HH as [HH|HH]; [apply orb_prop in HH as [HL|HH]|].
      3: { apply andb_prop in HH as [H1 H2].
           pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H2) as A2.
           cbn [xt_den edenot] in A1, A2. rewrite u_small in A1, A2 by (pose proof two64_pos; lia). lia. }
      2: { apply andb_prop in HH as [H1 H2].
           pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
           cbn [xt_den edenot] in A1, A2. rewrite u_small in A1, A2 by (pose proof two64_pos; lia). lia. }
      { (* [comment removed for export] *)
        unfold krange_lin in HL. rewrite !lin_testd12_eq in HL. repeat (apply andb_prop in HL as [HL ?X]).
        apply Z.leb_le in HL. apply Z.ltb_lt in X1.
        assert (LT : forall t, (lin_testd 1 k (fst (lin_of e)) (snd (lin_of e)) t || lin_testd 2 k (fst (lin_of e)) (snd (lin_of e)) t)%bool = true ->
                     exists lo' hi', t lo' hi' = true /\ (lo' <= fst (lin_of e) + tden E (snd (lin_of e)) <= hi')%Z).
        { intros t Ht. apply orb_prop in Ht as [Ht|Ht]; [exact (lin_testd_sound 1 SEGS E M k _ _ _ HK Ht) | exact (lin_testd_sound 2 SEGS E M k _ _ _ HK Ht)]. }
        destruct (LT _ X0) as (l1 & h1 & T1 & B1).
        destruct (LT _ X) as (l2 & h2 & T2 & B2).
        apply Z.leb_le in T1. apply Z.leb_le in T2.
        pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq.
        pose proof (u64_range (edenot E e)) as Re. unfold two64 in *.
        cbn beta in T1, T2.
        set (V := (fst (lin_of e) + tden E (snd (lin_of e)))%Z) in *.
        change (2 ^ 64)%Z with 18446744073709551616%Z in *.
        assert (Hq0 : q = 0) by (destruct (Z.le_gt_cases 1 q); [nia|]; destruct (Z.le_gt_cases q (-1)); [nia|lia]).
        subst q. lia. }
  - (* [comment removed for export] *)
    exact (APS.disj_x_sound SEGS E M k b1 o1 n1 b2 o2 n2 HK H).
Qed.
Lemma kn_ent_sound : forall E M k tk, know_ok SEGS E M k -> kn_ent A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. rewrite kn_ent_eq in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. apply orb_prop in HK1 as [H1|H1]; [|rewrite <- kpure_entails_eq in H1].
  - assert (H2 : kn_incl_h A k [K] = true) by (unfold kn_incl_h; cbn [forallb]; rewrite H1; reflexivity).
    exact (Forall_inv (kn_incl_h_sound SEGS A SEGS_in_hull HULL_ok E M k [K] HK H2)).
  - exact (kpure_entails_sound E M k K HK H1).
Qed.

Lemma entails_sound : forall E cs ch fx R M model,
  cs_ok E cs fx R M model -> entails A cs ch = true -> cs_ok E ch fx R M model /\ pc ch = pc cs.
Proof.
  intros E cs ch fx R M model HC H. apply entails_imp in H. unfold entails_ref in H.   (* [comment removed for export] *)
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hvis end.
  match goal with Hk : kn_ent A (kn cs) (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  (* [comment removed for export] *)
  match goal with Hq : list_eqb pair_eqb (a_fake cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hq; rename Hq into Hfake end.
  match goal with Hm : expr_eqb (a_meter cs) _ = true |- _ => apply expr_eqb_eq in Hm; rename Hm into Hmeter end.
  match goal with Hm : expr_eqb (a_fbud cs) _ = true |- _ => apply expr_eqb_eq in Hm; rename Hm into Hfbud end.   (* [comment removed for export] *)
  match goal with Hd : afd_eqb (a_fd cs) _ = true |- _ => apply afd_eqb_eq in Hd; rename Hd into Hfd end.
  assert (HMR : Mr E ch model M = Mr E cs model M) by (apply Mr_fields; symmetry; assumption).
  match goal with Hm : list_eqb amap_eqb (a_maps cs) _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    rewrite <- ?Hregs, <- ?Hvis, <- ?Hghost, <- ?Hbrk, <- ?Hfake, <- ?Hmeter, <- ?Hfbud, <- ?Hfd, <- ?Hmaps, ?HMR; try assumption.
  2:{ (* [comment removed for export] *) eapply floor_sem_weaken; [|exact CFL]. assumption. }
  exact (kn_ent_sound _ _ _ _ CK Hkn).
Qed.
(* [comment removed for export] *)
Lemma regs_ent_sound : forall E M k ts cs0 i,
  know_ok SEGS E M k -> regs_ent k i ts cs0 = true ->
  length ts = length cs0 /\ forall n, (i + n <> 0)%nat -> edenot E (nth n ts (ELit 0)) = edenot E (nth n cs0 (ELit 0)).
Proof.
  intros E M k ts. induction ts as [|t ts IH]; intros cs0 i HK H; destruct cs0 as [|c cs0]; try discriminate; cbn [regs_ent] in H.
  - split; [reflexivity|]. intros [|n] _; reflexivity.
  - apply andb_prop in H as [H1 H2]. destruct (IH cs0 (S i) HK H2) as [Hlen Hn]. split; [cbn; lia|].
    intros [|n] Hnz; cbn [nth].
    + apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
      * apply Nat.eqb_eq in H1. lia.
      * apply expr_eqb_eq in H1. subst. reflexivity.
      * symmetry. exact (respell_ok_sound SEGS E M k c t HK H1).
    + apply Hn. lia.
Qed.

Lemma entails_t_sound : forall lo E cs T th fx R M model,
  cs_ok E cs fx R M model -> entails_t A lo cs T th = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof.
  intros lo E cs T th fx R M model HC H Hlo. apply entails_t_imp in H. unfold entails_t_ref in H.   (* [comment removed for export] *)
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : th_id_below lo th = true |- _ => rename Hl into Hid end.
  match goal with Hl : regs_ent _ _ _ _ = true |- _ => rename Hl into Hregs end.
  match goal with Hl : kn_ent _ _ _ = true |- _ => rename Hl into Hkn end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_vis T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hvis end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_ghost T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hgh end.
  match goal with Hl : expr_eqb (tsubst th (a_brk T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hbrk end.
  (* [comment removed for export] *)
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_fake T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hfake end.
  match goal with Hl : expr_eqb (tsubst th (a_meter T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hmeter end.
  match goal with Hl : expr_eqb (tsubst th (a_fbud T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hfbud end.   (* [comment removed for export] *)
  match goal with Hl : afd_eqb (ftsubst th (a_fd T)) _ = true |- _ => apply afd_eqb_eq in Hl; rename Hl into Hfd end.
  match goal with Hl : Z.leb (a_ylo T) (a_ylo cs) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hylo end.
  match goal with Hl : list_eqb amap_eqb (a_maps cs) (a_maps T) = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hl; rename Hl into Hmaps end.
  match goal with Hl : AP.maps_vars_lt lo (a_maps T) = true |- _ => rename Hl into Hmv end.
  set (E' := tenv E th). exists E'.
  assert (Hag : env_agree lo E E') by (apply th_id_below_agree; exact Hid).
  assert (HMR : Mr E' T model M = Mr E cs model M).
  { unfold Mr. f_equal. apply functional_extensionality. intros a. unfold hid, vlz. unfold E'.
    rewrite <- in_shb_ptsubst, !map_app, Hvis, Hfake. reflexivity. }
  split; [exact Hag|]. split; [|symmetry; exact Hpc].
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; try assumption.
  - (* [comment removed for export] *)
    apply (proj1 (regs_ok_tsubst E th (s_regs (a_ss T)) R)).
    destruct (regs_ent_sound E _ (kn cs) _ _ 0%nat CK Hregs) as [Hlen Hn].
    intros r. rewrite (CR r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
    intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
    change (bv_unsigned r = 0). pose proof (u5_range r). lia.
  - (* [comment removed for export] *)
    rewrite HMR. apply (proj1 (know_ok_ktsubst E th _ (kn T))). eapply kn_ent_sound; [exact CK | exact Hkn].
  - (* [comment removed for export] *) unfold E'. apply fds_ok_ftsubst. rewrite Hfd. exact CD.
  - (* [comment removed for export] *)
    unfold E'. rewrite <- !blocks_den_ptsubst, <- bcost_ptsubst, <- uE_tsubst, Hvis, Hfake, Hmeter. unfold bcount in *.
    rewrite <- (length_map (ptsubst th)), Hvis. exact CA.
  - (* [comment removed for export] *) eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Hlo] | exact CU].
  - (* [comment removed for export] *) unfold E'. rewrite <- wins_den_ptsubst, Hgh. exact CP.
  - (* [comment removed for export] *) unfold E'. rewrite <- sptop_den_tsubst, Hbrk. exact CT.
  - (* [comment removed for export] *) unfold E'. rewrite <- uE_tsubst, Hmeter. exact CK2.
  - (* [comment removed for export] *) unfold E'. rewrite <- uE_tsubst, Hfbud, <- (length_map (ptsubst th)), Hfake. exact CFB.
  - (* [comment removed for export] *)
    rewrite <- Hmaps. eapply (floor_sem_xfer E E' (a_maps cs) (a_brk cs) (a_brk T) (a_ylo cs) (a_ylo T)); [| | exact Hylo | exact CFL].
    + intros f l kd r Hm. unfold uE. rewrite <- Hmaps, Hm in Hmv. cbn [AP.maps_vars_lt forallb am_base am_len] in Hmv.
      apply andb_prop in Hmv as [Hmv _]. apply andb_prop in Hmv as [Hf _].
      rewrite <- (edenot_agree' lo E E' f Hag Hf). reflexivity.
    + unfold E'. rewrite <- sptop_den_tsubst, Hbrk. reflexivity.
Qed.

Lemma entails_tw_sound : forall lo hi w E cs T fx R M model,
  cs_ok E cs fx R M model -> entails_tw A lo hi w cs T = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof. intros lo hi w E cs T fx R M model HC H Hlo. rewrite entails_tw_eq in H. apply andb_prop in H as [_ H]. eapply entails_t_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cs_ok_reenv : forall b E E' cs sr' fx R M model,
  cs_ok E cs fx R M model -> env_agree b E E' -> (nx0 <= b)%nat ->
  AP.kn_vars_lt b (kn cs) = true -> pairs_vars_lt b (a_vis cs) = true ->
  pairs_vars_lt b (a_ghost cs) = true -> AP.expr_vars_lt b (a_brk cs) = true -> AP.maps_vars_lt b (a_maps cs) = true ->
  fd_vars_lt b (a_fd cs) = true -> pairs_vars_lt b (a_fake cs) = true -> AP.expr_vars_lt b (a_meter cs) = true ->   (* [comment removed for export] *)
  AP.expr_vars_lt b (a_fbud cs) = true ->   (* [comment removed for export] *)
  regs_ok E' sr' R ->
  cs_ok E' (set_regs cs sr') fx R M model.
Proof.
  intros b E E' cs sr' fx R M model HC Hag Hb Hkn Hvis Hgh Hbrk Hmv Hfd Hfk Hmt Hfb HR.
  assert (HMR : Mr E' (set_regs cs sr') model M = Mr E cs model M).
  { unfold Mr. rewrite (hid_fields E' cs (set_regs cs sr') model) by reflexivity. f_equal.
    apply functional_extensionality. intros a. unfold hid, vlz. rewrite (in_shb_agree b E E'); [reflexivity | exact Hag |].
    unfold pairs_vars_lt in *. rewrite !forallb_app, Hvis, Hfk. reflexivity. }
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; rewrite ?HMR;
    cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_fake a_meter a_fbud a_fd a_ghost a_brk] in *; try assumption; try reflexivity.
  - eapply know_ok_agree'; eassumption.
  - eapply APS.fds_ok_agree; eassumption.
  - rewrite (blocks_den_agree b E E' (a_vis cs) Hag Hvis). rewrite (bcost_agree b E E' (a_vis cs) Hag Hvis).
    rewrite (blocks_den_agree b E E' (a_fake cs) Hag Hfk). rewrite (uE_agree b E E' (a_meter cs) Hag Hmt). assumption.
  - eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
  - rewrite (wins_den_agree b E E' (a_ghost cs) Hag Hgh). assumption.
  - rewrite (sptop_den_agree b E E' (a_brk cs) Hag Hbrk). assumption.
  - rewrite (uE_agree b E E' (a_meter cs) Hag Hmt). assumption.
  - rewrite (uE_agree b E E' (a_fbud cs) Hag Hfb). assumption.
  - cbn [a_ylo a_maps]. eapply (floor_sem_agree b E E'); [exact Hag | exact Hbrk | exact Hmv | assumption].
Qed.

Lemma entails_h_sound : forall lo hi E cs T fx R M model,
  cs_ok E cs fx R M model -> entails_h A lo hi cs T = true -> (nx0 <= lo)%nat -> length (s_regs (a_ss T)) = 32%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof.
  intros lo hi E cs T fx R M model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hvis end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  match goal with Hk : AP.kn_vars_lt lo (kn T) = true |- _ => rename Hk into Hknv end.
  match goal with Hk : pairs_vars_lt lo (a_vis T) = true |- _ => rename Hk into Hvisv end.
  match goal with Hk : pairs_vars_lt lo (a_ghost T) = true |- _ => rename Hk into Hghv end.
  match goal with Hk : AP.expr_vars_lt lo (a_brk T) = true |- _ => rename Hk into Hbrkv end.
  match goal with Hk : AP.maps_vars_lt lo (a_maps T) = true |- _ => rename Hk into Hmapsv end.
  match goal with Hk : fd_vars_lt lo (a_fd T) = true |- _ => rename Hk into Hfdv end.
  match goal with Hk : pairs_vars_lt lo (a_fake T) = true |- _ => rename Hk into Hfkv end.
  match goal with Hk : AP.expr_vars_lt lo (a_meter T) = true |- _ => rename Hk into Hmtv end.
  match goal with Hk : AP.expr_vars_lt lo (a_fbud T) = true |- _ => rename Hk into Hfbv end.   (* [comment removed for export] *)
  match goal with Ha : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hq : list_eqb pair_eqb (a_fake cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hq; rename Hq into Hfake end.
  match goal with Hm : expr_eqb (a_meter cs) _ = true |- _ => apply expr_eqb_eq in Hm; rename Hm into Hmeter end.
  match goal with Hm : expr_eqb (a_fbud cs) _ = true |- _ => apply expr_eqb_eq in Hm; rename Hm into Hfbud end.   (* [comment removed for export] *)
  match goal with Hd : afd_eqb (a_fd cs) _ = true |- _ => apply afd_eqb_eq in Hd; rename Hd into Hfd end.
  match goal with Hm : list_eqb amap_eqb (a_maps cs) _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (HMR : Mr E Tc model M = Mr E cs model M).
  { apply Mr_fields; unfold Tc; cbn [set_regs with_ss a_vis a_fake a_ghost]; symmetry; assumption. }
  assert (HC1 : cs_ok E Tc fx R M model).
  { destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; rewrite ?HMR;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_fake a_meter a_fbud a_fd a_ghost a_brk a_ylo a_maps];
           rewrite <- ?Hvis, <- ?Hghost, <- ?Hbrk, <- ?Hfake, <- ?Hmeter, <- ?Hfbud, <- ?Hfd, <- ?Hmaps; first [assumption | reflexivity | lia | eapply floor_sem_weaken; [|exact CFL]; assumption]).
    unfold Tc. cbn [set_regs with_ss a_ss mk_ss s_know kn]. eapply kn_incl_h_sound; [exact SEGS_in_hull | exact HULL_ok | exact CK | exact Hkn]. }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti mt fk fb]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs HC)].
Qed.

Lemma diamond_join_sound : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E fx R M model, cs_ok E ca fx R M model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj fx R M model /\ pc csj = pc ca)
  /\ (forall E fx R M model, cs_ok E cb fx R M model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj fx R M model /\ pc csj = pc cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E fx R M model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T fx R M model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T fx R M model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  Lemma blocks_den_rename : forall E l,
    pvars_all fw bw l = true -> blocks_den (ren_env bw E) (map (prename fw) l) = blocks_den E l.
  Proof.
    intros E l Hv. unfold blocks_den. rewrite map_map. apply map_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. unfold uE. rewrite !(ER E) by assumption. reflexivity.
  Qed.

  Lemma bcost_rename : forall E l,
    pvars_all fw bw l = true -> bcost (ren_env bw E) (map (prename fw) l) = bcost E l.
  Proof.
    intros E l Hv. induction l as [|[b n] r IH]; [reflexivity|].
    unfold pvars_all in Hv. cbn [forallb fst snd] in Hv. apply andb_prop in Hv as [H12 Hr]. apply andb_prop in H12 as [H1 H2].
    cbn [map bcost prename fst snd]. unfold uE at 1 2. rewrite (ER E) by assumption. rewrite (IH Hr). reflexivity.
  Qed.

  Lemma wins_den_rename : forall E l,
    pvars_all fw bw l = true -> wins_den (ren_env bw E) (map (prename fw) l) = wins_den E l.
  Proof.
    intros E l Hv. unfold wins_den. rewrite map_map. apply map_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. unfold uE. rewrite !(ER E) by assumption. reflexivity.
  Qed.

  Lemma sptop_den_rename : forall E e,
    evars_all (ren_ok fw bw) e = true -> sptop_den (ren_env bw E) (erename fw e) = sptop_den E e.
  Proof. intros E e Hv. unfold sptop_den, uE. rewrite (ER E) by assumption. reflexivity. Qed.

  Lemma uE_rename : forall E e,
    evars_all (ren_ok fw bw) e = true -> uE (ren_env bw E) (erename fw e) = uE E e.
  Proof. intros E e Hv. unfold uE. rewrite (ER E) by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma floor_sem_rename : forall E ms top bud,
    forallb (fun m => evars_all (ren_ok fw bw) (am_base m) && evars_all (ren_ok fw bw) (am_len m))%bool ms = true ->
    evars_all (ren_ok fw bw) top = true ->
    floor_sem E (acs_floor ms) top bud -> floor_sem (ren_env bw E) (acs_floor (map (mrename fw) ms)) (erename fw top) bud.
  Proof.
    intros E ms top bud Hms Htop H. destruct ms as [|[f l kd] r]; cbn [map mrename acs_floor floor_sem am_base am_len am_kind] in *.
    - rewrite (sptop_den_rename E top Htop). exact H.
    - apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _]. unfold uE in *. rewrite (ER E) by assumption. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma in_shb_rename : forall E l z,
    pvars_all fw bw l = true -> in_shb (ren_env bw E) (map (prename fw) l) z = in_shb E l z.
  Proof.
    intros E l z Hv. unfold in_shb. rewrite APS.existsb_map'. apply existsb_exteq. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. unfold uE. rewrite !(ER E) by assumption. reflexivity.
  Qed.
  Lemma Mr_rename : forall E cs nx model M,
    pvars_all fw bw (a_vis cs) = true -> pvars_all fw bw (a_fake cs) = true -> pvars_all fw bw (a_ghost cs) = true ->
    Mr (ren_env bw E) (rename_cs fw cs nx) model M = Mr E cs model M.
  Proof.
    intros E cs nx model M H1 H2 H3. unfold Mr. f_equal. apply functional_extensionality. intros a.
    unfold hid, vlz. cbn [rename_cs a_vis a_fake a_ghost]. rewrite <- !map_app. rewrite in_shb_rename; [reflexivity|].
    unfold pvars_all in *. rewrite !forallb_app, H1, H2. reflexivity.
  Qed.

  Lemma cs_ok_rename : forall E cs fx R M model nx,
    csvars_all (ren_ok fw bw) cs = true -> s_log (a_ss cs) = [] ->
    cs_ok E cs fx R M model -> cs_ok (ren_env bw E) (rename_cs fw cs nx) fx R M model.
  Proof.
    intros E cs fx R M model nx Hv Hlog HC.
    unfold csvars_all in Hv.
    apply andb_prop in Hv as [Hv Hfb]. (* [comment removed for export] *) apply andb_prop in Hv as [Hv Hmt]. apply andb_prop in Hv as [Hv Hfk].   (* [comment removed for export] *)
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    pose proof (Mr_rename E cs nx model M Hvis Hfk Hgh) as HMR.
    destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; rewrite ?HMR;
      cbn [rename_cs a_ss a_totsz a_eager a_vis a_fake a_meter a_fbud a_fd a_ghost a_brk a_ylo kn mk_ss s_regs s_log s_know s_pc s_next] in *; try assumption.
    - apply (regs_ok_rename m fw bw Hfw Hbw); assumption.
    - reflexivity.
    - apply (know_ok_rename SEGS m fw bw Hfw Hbw); assumption.
    - apply (APS.fds_ok_rename m fw bw Hfw Hbw); assumption.
    - rewrite (blocks_den_rename E (a_vis cs) Hvis), (bcost_rename E (a_vis cs) Hvis), (blocks_den_rename E (a_fake cs) Hfk),
              (uE_rename E (a_meter cs) Hmt). unfold bcount in *. rewrite length_map. assumption.
    - eapply UINV_agree; [eapply env_agree_le; [apply (ren_agree m bw Hbw gb Hm) | exact Hgb] | assumption].
    - rewrite (wins_den_rename E (a_ghost cs) Hgh). assumption.
    - rewrite (sptop_den_rename E (a_brk cs) Hbrk). assumption.
    - rewrite (uE_rename E (a_meter cs) Hmt). assumption.
    - rewrite (uE_rename E (a_fbud cs) Hfb), length_map. assumption.
    - cbn [a_maps]. apply floor_sem_rename; assumption.
  Qed.
End RenameCS.

Lemma rename_sound : forall gb E cs fx R M model m cs',
  (nx0 <= gb)%nat -> cs_ok E cs fx R M model -> node_rename gb cs m = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros gb E cs fx R M model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ _ =>
    change (cs_ok (ren_env bw E) (rename_cs fw cs NX) fx R M model) end.
  apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log HC) | exact HC].
Qed.

Lemma compact_sound : forall gb E cs fx R M model cs',
  (nx0 <= gb)%nat -> cs_ok E cs fx R M model -> node_compact gb cs = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof. intros gb E cs fx R M model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation CHECK := (AP.checkA SEGS IT A nx0 LIMIT ISP0 XN XE XB XA XT HS KC false).   (* [comment removed for export] *)

Lemma sd_agree : forall D E E' fs s,
  env_agree nx0 E E' -> shape_vars_lt nx0 s = true -> sd D E fs s = sd D E' fs s.
Proof.
  intros D E E' fs s Hag. induction s; cbn [sd shape_vars_lt]; intros Hv; try reflexivity.
  - (* [comment removed for export] *) rewrite IHs by exact Hv. unfold Wp.
    replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros p. destruct p; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in Hv as [Hv H3]. apply andb_prop in Hv as [H1 H2].
    rewrite (edenot_agree' nx0 E E' e Hag H1), IHs1, IHs2 by assumption. reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - left. apply is_prefix_nil.
  - left. exact IHs1.
  - destruct (bv_unsigned (edenot E e) <=? mid); assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.

Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LCOK (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | None => True
  | Some (LC h nxs lo hi hx) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ (hx = true -> t_eq D (HOLES 0%nat E fs))) /\
              forall nx, In nx nxs -> forall E' fx' R' M' m', env_agree lo E E' -> cs_ok E' nx fx' R' M' m' -> m_fs m' = fs ->
                RZ (cfg fx' R' h M' m') D
  | Some (JC j jss sk b lo jx) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ (jx = true -> t_eq D (HOLES 0%nat E fs))) /\
              forall js, In js jss -> forall E' fx' R' M' m', env_agree b E E' -> cs_ok E' js fx' R' M' m' -> m_fs m' = fs ->
                RZ (cfg fx' R' (pc js) M' m') (sd D E' fs sk)
  end.

Lemma LCOK_bnd : forall lc D E fs, LCOK lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi hx|j js sk b lo jx]|] D E fs HL; cbn [LCOK lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.

Lemma LCOK_raise : forall lc b D E fs, LCOK lc D E fs -> (nx0 <= b)%nat -> LCOK (AP.lc_raise lc b) D E fs.
Proof.
  intros [[h nx lo hi hx|j js sk b0 lo jx]|] b D E fs HL Hb; cbn [LCOK AP.lc_raise] in *.
  - destruct HL as [(H1 & H2 & H3) HL]. split; [split; [exact H1 | split; [lia | exact H3]] | exact HL].
  - exact HL.
  - split; [split; [exact Hb | split; [lia | intros H; discriminate H]]|]. intros nx [].
Qed.


Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
  match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.

Lemma LCOK_agree_gb : forall lc D E E' fs,
  LCOK lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK lc D E' fs.
Proof.
  intros [[h nx lo hi hx|j js sk b lo jx]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK lc_bnd] in *.
  - destruct HL as [(Hn0 & Hlh & Hx) HL]. split.
    + split; [exact Hn0 | split; [exact Hlh |]].
      intros Hhx. rewrite <- (HOLES_agree 0%nat E E' fs ltac:(eapply env_agree_le; [exact Hag | lia])). exact (Hx Hhx).
    + intros nx1 Hin E2 fx' R' M' m' Hag2; apply (HL nx1 Hin); (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
  - destruct HL as [(Hn0 & Hlh & Hx) HL]; (split; [split; [exact Hn0 | split; [exact Hlh |]]|]).
    + intros Hjx. rewrite <- (HOLES_agree 0%nat E E' fs ltac:(eapply env_agree_le; [exact Hag | lia])). exact (Hx Hjx).
    + intros js1 Hin E2 fx' R' M' m' Hag2; apply (HL js1 Hin); (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

Lemma LCOK_agree : forall lc D E E' fs cs,
  LCOK lc D E fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> LCOK lc D E' fs.
Proof.
  intros [c|] D E E' fs cs HL Hg Hag; [|exact I]. eapply LCOK_agree_gb; [exact HL|].
  cbn [lc_guard] in Hg. apply Nat.leb_le in Hg. eapply env_agree_le; [exact Hag | exact Hg].
Qed.

Lemma LCOK_xmode : forall lc D E fs, LCOK lc D E fs -> lc_xmode lc = true -> t_eq D (HOLES 0%nat E fs).
Proof.
  intros [[h0 nx0' lo0 hi0 hx0|j0 js0 sk0 b0 lo0 jx0]|] D E fs HL Hxm; cbn [lc_xmode] in Hxm; try discriminate Hxm;
    cbn [LCOK] in HL; [destruct hx0; [|discriminate Hxm] | destruct jx0; [|discriminate Hxm]];
    destruct HL as [(_ & _ & Hx) _]; exact (Hx eq_refl).
Qed.

Lemma cont_agree : forall bfuel fuel lc k cs cs' s E model D,
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall E fx R M model, cs_ok E cs' fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s)) ->
  forall E' fx' R' M' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
    RZ (cfg fx' R' (pc cs') M' model') (sd D E (m_fs model) s).
Proof.
  intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' fx' R' M' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars SEGS IT A nx0 LIMIT HS XN XE XB ISP0 KC XA XT false _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' fx' R' M' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma sd_holes_only_eq : forall D E fs s, holes_only s = true -> t_eq (sd D E fs s) (HOLES 0%nat E fs).
Proof.
  intros D E fs s. induction s; cbn [holes_only sd]; intros H; try discriminate.
  - (* [comment removed for export] *) apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2.
    repeat match goal with IH : holes_only ?x = true -> t_eq _ _, HH : holes_only ?x = true |- _ => pose proof (IH HH tr); clear IH end. tauto.
  - apply andb_prop in H as [H1 H2]. destruct (Z.leb _ _); [apply IHs1; exact H1 | apply IHs2; exact H2].
  - rewrite (HOLES_same h). intros tr. tauto.
Qed.
(* [comment removed for export] *)
Lemma shape_eqv_transfer : forall D E fs s1 s2 c,
  AP.shape_eqv s1 s2 = true -> RZ c (sd D E fs s2) -> RZ c (sd D E fs s1).
Proof.
  intros D E fs s1 s2 c H HR. unfold AP.shape_eqv in H. apply orb_prop in H as [H|H].
  - apply shape_eqb_eq in H. subst. exact HR.
  - apply andb_prop in H as [H1 H2]. eapply RZ_conseq; [exact HR|].
    intros tr. pose proof (sd_holes_only_eq D E fs s1 H1 tr). pose proof (sd_holes_only_eq D E fs s2 H2 tr). tauto.
Qed.


(* [comment removed for export] *)
Lemma sd_next_or_holes_D : forall D E fs s,
  next_or_holes s = true -> t_eq D (HOLES 0%nat E fs) -> t_eq (sd D E fs s) D.
Proof.
  intros D E fs s Hs HD. induction s; cbn [next_or_holes sd] in *; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. destruct (Z.leb _ _); [apply IHs1; exact H1 | apply IHs2; exact H2].
  - rewrite (HOLES_same h). intros tr. pose proof (HD tr). tauto.
  - intros tr. tauto.
Qed.

(* [comment removed for export] *)
Lemma check_next_sound : forall lc cs p w s E fx R M model D,
  AP.check_next A lc cs p w = COk s ->
  cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros lc cs p w s E fx R M model D Hc HC HL. unfold AP.check_next in Hc.
  destruct lc as [[h nxs lo hi hx|j' js' sk' b' lo' jx']|]; [|discriminate|discriminate].
  destruct (Z.eqb (pc cs) h && existsbL (fun nx => entails_tw A lo hi w cs nx) nxs)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
  apply andb_prop in Ht as [Hpc Hex]. apply Z.eqb_eq in Hpc. rewrite existsbL_eq in Hex. apply existsb_exists in Hex as [nx [Hin Hent]].
  cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & _) HL].
  destruct (entails_tw_sound lo hi w E cs nx fx R M model HC Hent Hn0) as (E' & Hag & HC' & Hpc').
  rewrite Hpc. exact (HL nx Hin E' fx R M model Hag HC' eq_refl).
Qed.
Lemma check_merge_sound : forall lc cs p j w s E fx R M model D,
  AP.check_merge A nx0 lc cs p j w = COk s ->
  cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros lc cs p j w s E fx R M model D Hc HC HL. unfold AP.check_merge in Hc.
  destruct lc as [[h nx lo hi hx|j' jss sk' b' lo' jx']|]; [discriminate| |discriminate].
  destruct (Nat.eqb j j' && shape_vars_lt nx0 sk' && existsbL (fun js => Z.eqb (pc cs) (pc js) && entails_tw A lo' (nxt js) w cs js) jss)%bool eqn:Ht; [|discriminate].
  injection Hc as <-.
  apply andb_prop in Ht as [Ht Hex]. apply andb_prop in Ht as [_ Hsv]. rewrite existsbL_eq in Hex. apply existsb_exists in Hex as [js [Hin Hje]].
  apply andb_prop in Hje as [Hpc Hent]. apply Z.eqb_eq in Hpc.
  cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & _) HJ].
  destruct (entails_tw_sound lo' (nxt js) w E cs js fx R M model HC Hent ltac:(clear -Hn0 Hbl; lia)) as (E' & Hag & HC' & Hpc').
  assert (Hn0l : (nx0 <= lo')%nat) by lia.
  rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
  exact (HJ js Hin E' fx R M model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
Qed.

(* [comment removed for export] *)
Lemma listZ_eqb_refl : forall l, APC.listZ_eqb l l = true.
Proof. induction l; cbn; [reflexivity|]. rewrite Z.eqb_refl, IHl. reflexivity. Qed.
Lemma spieces_eqb_refl : forall l, APC.spieces_eqb l l = true.
Proof.
  induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH.
  destruct a; cbn; [rewrite listZ_eqb_refl | rewrite Nat.eqb_refl]; reflexivity.
Qed.
Lemma shape_eqb_refl : forall s, shape_eqb s s = true.
Proof.
  induction s; cbn [shape_eqb]; try reflexivity.
  - apply Z.eqb_refl.
  - rewrite Z.eqb_refl, spieces_eqb_refl, IHs. reflexivity.
  - rewrite IHs1, IHs2. reflexivity.
  - rewrite APS.expr_eqb_refl', Z.eqb_refl, IHs1, IHs2. reflexivity.
  - apply Nat.eqb_refl.
Qed.
Lemma shape_eqv_refl : forall s, AP.shape_eqv s s = true.
Proof. intros s. unfold AP.shape_eqv. rewrite shape_eqb_refl. reflexivity. Qed.
Lemma shape_eqv_trans : forall a b c, AP.shape_eqv a b = true -> AP.shape_eqv b c = true -> AP.shape_eqv a c = true.
Proof.
  intros a b c H1 H2. unfold AP.shape_eqv in *.
  apply orb_prop in H1 as [H1|H1]; [apply shape_eqb_eq in H1; subst; exact H2|].
  apply andb_prop in H1 as [Ha Hb].
  apply orb_prop in H2 as [H2|H2]; [apply shape_eqb_eq in H2; subst; rewrite Ha, Hb; cbn; apply orb_true_r|].
  apply andb_prop in H2 as [_ Hc]. rewrite Ha, Hc. cbn. apply orb_true_r.
Qed.
Lemma check_each_ok : forall chk p cs0 css s,
  AP.check_each chk p cs0 css = COk s ->
  forall cs k, In (cs, k) css -> exists s', chk cs k = COk s' /\ AP.shape_eqv s s' = true.
Proof.
  intros chk p cs0 css. induction css as [|[c ck] rest IH]; intros s Hc cs k Hin; [discriminate|].
  cbn [AP.check_each] in Hc. destruct rest as [|c2 rest2].
  - destruct Hin as [He|[]]. injection He as <- <-. exists s. split; [exact Hc | apply shape_eqv_refl].
  - destruct (chk c ck) as [s1|] eqn:H1; [|discriminate].
    destruct (AP.check_each chk p cs0 (c2 :: rest2)) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:He; [|discriminate]. injection Hc as <-.
    destruct Hin as [Hx|Hin].
    + injection Hx as <- <-. exists s1. split; [exact H1 | apply shape_eqv_refl].
    + destruct (IH s2 eq_refl cs k Hin) as (s' & Hs' & Hev). exists s'. split; [exact Hs'|].
      eapply shape_eqv_trans; [exact He | exact Hev].
Qed.
Lemma check_bodies_ok : forall chk p cs0 css,
  AP.check_bodies chk p cs0 css = COk SNext -> forall cs b, In (cs, b) css -> chk cs b = COk SNext.
Proof.
  intros chk p cs0 css. induction css as [|[c cb] rest IH]; intros Hc cs b Hin; [destruct Hin|].
  cbn [AP.check_bodies] in Hc. destruct (chk c cb) as [sb|] eqn:H1; [|discriminate].
  destruct sb; try discriminate. destruct Hin as [Hx|Hin]; [injection Hx as <- <-; exact H1 | exact (IH Hc cs b Hin)].
Qed.
Lemma check_bodies_next : forall chk p cs0 css sb, AP.check_bodies chk p cs0 css = COk sb -> sb = SNext.
Proof.
  intros chk p cs0 css. induction css as [|[c cb] rest IH]; intros sb Hc; cbn [AP.check_bodies] in Hc.
  - injection Hc as <-. reflexivity.
  - destruct (chk c cb) as [s1|]; [|discriminate]. destruct s1; try discriminate. exact (IH sb Hc).
Qed.
Lemma loop_okM_facts : forall cs J N alts nhi,
  AP.loop_okM nx0 cs J N alts = Some nhi ->
  forall a, In a alts -> loop_ok nx0 cs J N (AP.la_inv a) = Some nhi /\ pc (AP.la_inv a) = pc cs
                        /\ nxt (AP.la_inv a) = nxt (AP.la_inv (hd a alts)).
Proof.
  intros cs J N alts nhi H a Hin. unfold AP.loop_okM in H. destruct alts as [|a0 rest]; [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hf; [|discriminate] end.
  pose proof (proj1 (forallb_forall _ _) Hf a Hin) as Hi. cbn beta in Hi.
  apply andb_prop in Hi as [Hi Hlk]. apply andb_prop in Hi as [Hpc Hnx]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hnx.
  cbn [hd]. split; [|split; [exact Hpc | exact Hnx]].
  destruct (loop_ok nx0 cs J N (AP.la_inv a)) as [n1|] eqn:Hl; [|discriminate].
  (* [comment removed for export] *)
  unfold loop_ok in H, Hl.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  match type of Hl with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  rewrite Hl in H. exact H.
Qed.
(* [comment removed for export] *)
Lemma gplan_ok_lalts : forall alts a, gplan_ok (PLoopM 0 (ELit 0) alts []) = true -> In a alts ->
  gplan_ok (AP.la_body a) = true /\ gplan_ok (AP.la_k a) = true.
Proof.
  intros alts. induction alts as [|[[i b] k] r IH]; intros a H Hin; [destruct Hin|].
  cbn [gplan_ok] in H. fold gplan_ok in H.
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hb Hk].
  destruct Hin as [<-|Hin]; [split; [exact Hb | exact Hk]|]. apply IH; [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. exact Hr.
Qed.
Lemma gplan_ok_valts : forall alts ka a, gplan_ok (PViaM 0 alts 0 ka) = true -> In a alts -> gplan_ok (snd a) = true.
Proof.
  intros alts ka. induction alts as [|[j k] r IH]; intros a H Hin; [destruct Hin|].
  cbn [gplan_ok] in H. fold gplan_ok in H.
  apply andb_prop in H as [Hka H]. apply andb_prop in H as [Hk Hr].
  destruct Hin as [<-|Hin]; [exact Hk|]. apply IH; [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. rewrite Hka, Hr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma start_ok_sound : forall E cs N e0 fx R M model,
  cs_ok E cs fx R M model -> AP.start_ok cs N e0 = true ->
  bv_unsigned (edenot E e0) <= bv_unsigned (edenot E N) /\
  (forall E', env_agree (nxt cs) E E' -> edenot E e0 = edenot E' e0).
Proof.
  intros E cs N e0 fx R M model HC H.
  assert (GEN : (AP.expr_vars_lt (nxt cs) e0 && lin_ge0 (kn cs) [(N, 0%Z)] [(e0, 0%Z)])%bool = true ->
            bv_unsigned (edenot E e0) <= bv_unsigned (edenot E N) /\
            (forall E', env_agree (nxt cs) E E' -> edenot E e0 = edenot E' e0)).
  { intros G. apply andb_prop in G as [Gv Gl]. split.
    - pose proof (lin_ge0_sound SEGS E _ (kn cs) [(N, 0%Z)] [(e0, 0%Z)] (co_know HC) Gl) as Hle. cbn [xt_den] in Hle. lia.
    - intros E' Hag. exact (edenot_agree' (nxt cs) E E' e0 Hag Gv). }
  unfold AP.start_ok in H. destruct e0 as [z| | | | | | |]; try (exact (GEN H)).
  destruct z as [|p|p]; try (exact (GEN H)).
  split; [| intros E' _; reflexivity]. cbn [edenot]. rewrite u_small by lia. pose proof (u64_range (edenot E N)). lia.
Qed.

(* [comment removed for export] *)
Lemma check_loop_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p lJ lN alts lw s,
  (forall a, In a alts -> gplan_ok (AP.la_body a) = true /\ gplan_ok (AP.la_k a) = true) ->
  AP.check_loop A nx0 (CHECK bfuel fuel) lc cs p lJ lN alts lw = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p lJ lN alts lw s Hgalts Hc E fx R M model D HC HL Hg HD.
  unfold AP.check_loop in Hc.
  destruct (AP.loop_okM nx0 cs lJ lN alts) as [nhi|] eqn:HloM; [|discriminate].
  destruct alts as [|a0 rest] eqn:Halts; [discriminate|]. rewrite <- Halts in *.
  assert (Hin0 : In a0 alts) by (rewrite Halts; left; reflexivity).
  set (inv0 := AP.la_inv a0) in *.
  cbv zeta in Hc.
  set (e0 := AP.loop_start lw lJ) in Hc.
  destruct (AP.start_ok cs lN e0 && existsbL (fun a => entails_tw A (Datatypes.S lJ) (nxt inv0) lw cs (inst (AP.la_inv a) lJ e0)) alts)%bool eqn:Hex; [|discriminate].
  apply andb_prop in Hex as [Hst Hex]. rewrite existsbL_eq in Hex.
  destruct (AP.check_each (fun js k => CHECK bfuel fuel (AP.lc_raise lc (nxt js)) js k) p cs (map (fun a => (inst (AP.la_inv a) lJ lN, AP.la_k a)) alts)) as [sk|] eqn:Hk; [|discriminate].
  cbv zeta in Hc.
  match type of Hc with context [AP.check_bodies ?f ?pp ?c0 ?l] =>
    destruct (AP.check_bodies f pp c0 l) as [sb|] eqn:Hbody; [|discriminate] end.
  pose proof (check_bodies_next _ _ _ _ _ Hbody) as ->.
  enough (MAIN : RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) sk)).
  { destruct (lc_xmode lc && next_or_holes sk)%bool eqn:Hxn; injection Hc as <-; [|exact MAIN].
    apply andb_prop in Hxn as [Hxm Hnoh]. cbn [sd].
    pose proof (sd_next_or_holes_D D E (m_fs model) sk Hnoh (LCOK_xmode lc D E (m_fs model) HL Hxm)) as Heq.
    eapply RZ_conseq; [exact MAIN|]. intros tr. pose proof (Heq tr). tauto. }
  clear Hc s. rename sk into s.
  (* [comment removed for export] *)
  assert (FACTS : forall a, In a alts -> loop_ok nx0 cs lJ lN (AP.la_inv a) = Some nhi /\ pc (AP.la_inv a) = pc cs /\ nxt (AP.la_inv a) = nxt inv0).
  { intros a Hin. destruct (loop_okM_facts cs lJ lN alts nhi HloM a Hin) as (H1 & H2 & H3). rewrite Halts in H3. cbn [hd] in H3.
    split; [exact H1 | split; [exact H2 | exact H3]]. }
  destruct (FACTS a0 Hin0) as (Hlo0 & Hpc0 & _).
  destruct (loop_ok_facts nx0 cs lJ lN inv0 nhi Hlo0) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
  destruct (fresh_ok_parts nx0 cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
  pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know HC) FxN) as HNv.
  set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
  set (D0 := sd D E (m_fs model) s).
  assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
  set (h := pc cs) in *.
  pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
  assert (Hg' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
  { destruct lc as [c|]; cbn [lc_guard] in Hg; [apply Nat.leb_le in Hg; exact Hg | lia]. }
  assert (Q : forall m j a E' fx' R' M' m', In a alts -> j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
             cs_ok E' (inst (AP.la_inv a) lJ (ELit j)) fx' R' M' m' -> m_fs m' = m_fs model ->
             RZ (cfg fx' R' h M' m') D0).
  { induction m as [|m IHm]; intros j a E' fx' R' M' m' Hin Hj Hj0 Hag HCj Hfs; set (inv := AP.la_inv a) in *.
    - (* [comment removed for export] *)
      destruct (FACTS a Hin) as (Hloi & Hpci & Hnxi).
      destruct (loop_ok_facts nx0 cs lJ lN inv nhi Hloi) as (_ & _ & _ & Flogi & _ & _ & _ & _).
      assert (HNe : edenot E' lN = edenot E' (ELit j)).
      { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
      assert (HCN : cs_ok E' (inst inv lJ lN) fx' R' M' m').
      { apply (proj2 (cs_ok_inst E' lJ lN inv fx' R' M' m' ltac:(lia) Flogi)). rewrite HNe.
        apply (proj1 (cs_ok_inst E' lJ (ELit j) inv fx' R' M' m' ltac:(lia) Flogi)). exact HCj. }
      destruct (check_each_ok _ _ _ _ _ Hk (inst inv lJ lN) (AP.la_k a) (in_map (fun a' => (inst (AP.la_inv a') lJ lN, AP.la_k a')) _ _ Hin)) as (s' & Hk' & Hev).
      unfold D0. apply (shape_eqv_transfer D E (m_fs model) s s' _ Hev).
      rewrite (sd_agree D E E' (m_fs model) s' ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB ISP0 KC XA XT false _ _ _ _ _ _ Hk')).
      rewrite <- Hfs. replace h with (pc (inst inv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpci).
      apply (IH (AP.lc_raise lc (nxt (inst inv lJ lN))) (AP.la_k a) _ s' (proj2 (Hgalts a Hin)) Hk' E' fx' R' M' m' D HCN); [|exact HD].
      rewrite Hfs. apply LCOK_raise; [| rewrite (nxt_inst inv lJ lN); unfold inv; rewrite Hnxi; clear -Fle FJ FJh; lia]. eapply LCOK_agree_gb; [exact HL | eapply env_agree_le; [exact Hag | exact Hg']].
    - (* [comment removed for export] *)
      destruct (FACTS a Hin) as (Hloi & Hpci & Hnxi).
      destruct (loop_ok_facts nx0 cs lJ lN inv nhi Hloi) as (_ & _ & _ & Flogi & Fleni & _ & _ & _).
      set (E'' := upd E' lJ (Z_to_bv 64 j)).
      assert (Hjlt : j < Nv) by lia.
      assert (HCinv : cs_ok E'' inv fx' R' M' m').
      { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
        apply (proj1 (cs_ok_inst E' lJ (ELit j) inv fx' R' M' m' ltac:(lia) Flogi)). exact HCj. }
      assert (Hag'' : env_agree (nxt cs) E E'').
      { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
      assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
      assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
      assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi inv) fx' R' M' m').
      { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know HCinv)].
        constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
        - rewrite HJ'', u_small by lia. lia.
        - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
          rewrite Z.mod_small by lia. lia. }
      replace h with (pc (loop_body_state lJ lN nhi inv)) by exact Hpci.
      pose proof (check_bodies_ok _ _ _ _ Hbody (loop_body_state lJ lN nhi inv) (AP.la_body a)
                    (in_map (fun a' => (loop_body_state lJ lN nhi (AP.la_inv a'), AP.la_body a')) _ _ Hin)) as Hb1.
      refine (IH _ (AP.la_body a) _ SNext (proj1 (Hgalts a Hin)) Hb1 E'' fx' R' M' m' D0 HCb _ HD0).
      cbn [LCOK]. split.
      { split; [lia|]. split; [lia|].
        intros Hho. unfold D0. rewrite Hfs.
        rewrite <- (HOLES_agree 0%nat E E'' (m_fs model) ltac:(eapply env_agree_le; [exact Hag'' | exact Fle])).
        apply orb_prop in Hho as [Hho|Hxn].
        - intros tr. exact (sd_holes_only_eq D E (m_fs model) s Hho tr).
        - apply andb_prop in Hxn as [Hxm Hnoh].
          pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as HxD.
          eapply t_eq_trans; [exact (sd_next_or_holes_D D E (m_fs model) s Hnoh HxD) | exact HxD]. }
      intros nx Hinx E3 fx3 R3 M3 m3 Hag3 HC3 Hfs3.
      apply in_map_iff in Hinx as (a' & <- & Hin'). set (inv' := AP.la_inv a') in *.
      destruct (FACTS a' Hin') as (Hloi' & _ & _).
      destruct (loop_ok_facts nx0 cs lJ lN inv' nhi Hloi') as (_ & _ & _ & Flogi' & _ & _ & _ & _).
      assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
      assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
      { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
      set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
      apply (IHm (j + 1) a' E4 fx3 R3 M3 m3); [exact Hin' | lia | lia | | | rewrite Hfs3; exact Hfs].
      + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
        eapply env_agree_le; [apply upd_agree | exact FJ].
      + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) inv' fx3 R3 M3 m3 ltac:(lia) Flogi')).
        unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
        apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) inv' fx3 R3 M3 m3 ltac:(lia) Flogi')). exact HC3. }
  apply existsb_exists in Hex as [a1 [Hin1 Hent]].
  destruct (FACTS a1 Hin1) as (Hlo1 & _ & Hnx1). rewrite <- Hnx1 in Hent.
  destruct (loop_ok_facts nx0 cs lJ lN (AP.la_inv a1) nhi Hlo1) as (_ & _ & _ & Flog1 & _ & _ & _ & _).
  destruct (entails_tw_sound (Datatypes.S lJ) (nxt (AP.la_inv a1)) lw E cs (inst (AP.la_inv a1) lJ e0) fx R M model HC Hent ltac:(lia)) as (E1 & Hag1 & HC1 & _).
  (* [comment removed for export] *)
  destruct (start_ok_sound E cs lN e0 fx R M model HC Hst) as [Hle0 Hag0]. fold Nv in Hle0.
  set (j0 := bv_unsigned (edenot E e0)) in *. pose proof (u64_range (edenot E e0)) as Rj0. fold j0 in Rj0.
  assert (He1 : edenot E1 e0 = edenot E1 (ELit j0)).
  { rewrite <- (Hag0 E1 ltac:(eapply env_agree_le; [exact Hag1 | lia])). change (edenot E1 (ELit j0)) with (Z_to_bv 64 j0).
    apply bv_eq. rewrite u_small by lia. reflexivity. }
  assert (HC1' : cs_ok E1 (inst (AP.la_inv a1) lJ (ELit j0)) fx R M model).
  { apply (proj2 (cs_ok_inst E1 lJ (ELit j0) (AP.la_inv a1) fx R M model ltac:(lia) Flog1)). rewrite <- He1.
    apply (proj1 (cs_ok_inst E1 lJ e0 (AP.la_inv a1) fx R M model ltac:(lia) Flog1)). exact HC1. }
  unfold D0 in Q. apply (Q (Z.to_nat (Nv - j0)) j0 a1 E1 fx R M model); [exact Hin1 | lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1' | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma check_via_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p vj alts vlo vka s,
  gplan_ok vka = true -> (forall a, In a alts -> gplan_ok (snd a) = true) ->
  AP.check_via nx0 (CHECK bfuel fuel) lc cs p vj alts vlo vka = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p vj alts vlo vka s Hgpa Hgpk Hc E fx R M model D HC HL Hg HD.
  unfold AP.check_via in Hc.
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hv; [|discriminate] end.
  apply andb_prop in Hv as [Hv Hne].
  destruct (AP.check_each (fun js k => CHECK bfuel fuel (AP.lc_raise lc (nxt js)) js k) p cs alts) as [sk|] eqn:Hk; [|discriminate].
  pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
  (* [comment removed for export] *)
  destruct alts as [|[js0 k0] rest] eqn:Halts; [discriminate|]. rewrite <- Halts in *.
  assert (Hv0 : via_ok nx0 cs js0 vlo = true) by (apply (proj1 (forallb_forall _ _) Hv (js0, k0)); rewrite Halts; left; reflexivity).
  unfold via_ok in Hv0. repeat match type of Hv0 with (_ && _)%bool = true => apply andb_prop in Hv0 as [Hv0 ?X] end.
  repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
  assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
  { destruct lc as [c|]; [cbn [lc_guard] in Hg; apply Nat.leb_le in Hg; exact Hg | lia]. }
  apply (IH (Some (JC vj (map fst alts) sk (nxt cs) vlo (lc_xmode lc))) vka cs s Hgpa Hc E fx R M model D HC); [|exact HD].
  cbn [LCOK]. split; [split; [lia | split; [lia |]]|].
  { (* [comment removed for export] *)
    intros Hxm. exact (LCOK_xmode lc D E (m_fs model) HL Hxm). }
  intros js Hin E' fx' R' M' m' Hag HC' Hfs. rewrite <- Hfs.
  apply in_map_iff in Hin as ([js' k] & Hjs & Hin). cbn [fst] in Hjs. subst js'.
  destruct (check_each_ok _ _ _ _ _ Hk js k Hin) as (s' & Hk' & Hev).
  apply (shape_eqv_transfer D E' (m_fs m') sk s' _ Hev).
  apply (IH (AP.lc_raise lc (nxt js)) k js s' (Hgpk (js, k) Hin) Hk' E' fx' R' M' m' D HC'); [|exact HD].
  assert (Hvj : via_ok nx0 cs js vlo = true) by (apply (proj1 (forallb_forall _ _) Hv (js, k)); exact Hin).
  unfold via_ok in Hvj. repeat match type of Hvj with (_ && _)%bool = true => apply andb_prop in Hvj as [Hvj ?Y] end.
  repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
  rewrite Hfs. apply LCOK_raise; [|lia]. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
Qed.

(* [comment removed for export] *)
Lemma check_branch_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p e k1 k2 s,
  gplan_ok k1 = true -> gplan_ok k2 = true ->
  AP.check_branch (CHECK bfuel fuel lc) cs p e k1 k2 = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p e k1 k2 s Hgk1 Hgk2 Hc E fx R M model D HC HL Hg HD.
  assert (SAME : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' fx R M model ->
            nxt cs = nxt cs' -> RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk HC' Hn. apply (IH lc k cs' s' Hgk Hk E fx R M model D HC'); [|exact HD].
    eapply LCOK_agree; [exact HL | | apply env_agree_refl]. unfold lc_guard in *. rewrite <- Hn. exact Hg. }
  unfold AP.check_branch in Hc. rewrite ?brangeM_fe, ?branch_probes_eq in Hc. cbv beta iota zeta in Hc.
  destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
  destruct (Z.leb lo 0 && Z.ltb 0 hi)%bool.
  2: { cbn [negb] in Hc. destruct (Z.leb hi 0); [exact (SAME k1 _ s Hgk1 Hc HC eq_refl) | exact (SAME k2 _ s Hgk2 Hc HC eq_refl)]. }
  cbn [negb] in Hc.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
  assert (HCl : bv_unsigned (edenot E e) <= 0 -> cs_ok E (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) fx R M model).
  { intros Hm. apply cs_ok_set_kn; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact (co_know HC)].
    apply (probe_lin_facts_sound E _ (kn cs) e false (co_know HC)). exact Hm. }
  assert (HCr : 0 < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) fx R M model).
  { intros Hm. apply cs_ok_set_kn; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact (co_know HC)].
    apply (probe_lin_facts_sound E _ (kn cs) e true (co_know HC)). lia. }
  destruct (kn_contra (kn (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)))) eqn:Hk1.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
    - exact (SAME k2 _ s Hgk2 Hc (HCr ltac:(lia)) eq_refl). }
  destruct (kn_contra (kn (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)))) eqn:Hk2.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exact (SAME k1 _ s Hgk1 Hc (HCl Hle) eq_refl).
    - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (0+1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
  destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
  destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
  + exact (SAME k1 _ s1 Hgk1 H1 (HCl Hle) eq_refl).
  + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME k2 _ s2 Hgk2 H2 (HCr ltac:(lia)) eq_refl).
Qed.

Theorem check_soundA : forall fuel bfuel lc p cs s,
  gplan_ok p = true ->
  CHECK bfuel fuel lc cs p = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hgp Hc E fx R M model D HC HL HD; [discriminate|].
  cbn [AP.checkA] in Hc. rewrite ?fact_okM_fe, ?factle_okM_fe, ?factvia_okM_fe in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' fx' R' M' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' ->
            m_fs model' = m_fs model -> RZ (cfg fx' R' (pc cs') M' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  assert (SAME : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' fx R M model ->
            RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk HC'. refine (CONT k cs' s' Hgk Hk E fx R M model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lw lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|nw|mwj mww|bkf bkt|crr crmid crk1 crk2|fve fvv fvlo fvhi fvk|hwh hww|fle flb flhi flk|fse fsc fshi fsk|flr flo flb2 flh2 flk2|frr fro frlo frhi frk|fxr fxph fxe fxb fxhi fxk|gxr gxph gxe gxlo gxhi gxk|cth|mJ mN malts mw|wj walts wlo wka|bpz bpnz|aid aargs aka akb| |wlo whi wkr wkl wkh|hka hkb|tid targs];
    cbn [gplan_ok] in Hgp; try discriminate Hgp;
    repeat match type of Hgp with (_ && _)%bool = true => apply andb_prop in Hgp as [Hgp ?X] end.
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ false KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
    intros E' fx' R' M' model' Hag HC1 Hfs. exact (CONT k cs1 s Hgp Hc E' fx' R' M' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hgp Hc HC) | exact (SAME k2 _ s Hgp2 Hc HC)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 Hgp H1 (HCl Hle)).
    + exact (SAME k2 _ s2 Hgp2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (brange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hgp Hc HC) | exact (SAME ck2 _ s Hgp2 Hc HC)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound cs ce cmid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hgp2 Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hgp Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 Hgp H1 (HCl Hle)).
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME ck2 _ s2 Hgp2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (casedisj_sound cs db1 db2 csa csb E fx R M model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 Hgp H1 HC').
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME dk2 _ s2 Hgp2 H2 HC').
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound SEGS E _ (kn cs) (co_know HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
    exact (SAME k _ s Hgp Hc (fact_sound E cs fx R M model K HC Hf)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (join_sound jb joff jn cs cs1 E fx R M model HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hgp Hc (forget_sound E cs fx R M model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hgp Hc (droprange_sound E cs fx R M model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hgp Hc (gckeep_sound E cs fx R M model gws HC)).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs fx R M model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs fx R M model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs fx R M model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fresh_sound r logc fb cs cs1 E fx R M model HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_sound xid xargs cs cs1 E fx R M model); [apply sd_has_nil; exact HD | exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hgp Hc).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_emit_sound eid eargs cs fd ps cs1 E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 Hgp H1).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    (* [comment removed for export] *)
    destruct (kn_contra (kn csa)) eqn:Hka.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD | | exact (CONT kb2 csb s Hgp2 Hc)].
      intros E' fx' R' M' model' Hag HC' Hfs. exfalso. exact (kn_contra_sound SEGS E' _ _ (co_know HC') Hka). }
    destruct (kn_contra (kn csb)) eqn:Hkb.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD | exact (CONT kb1 csa s Hgp Hc) |].
      intros E' fx' R' M' model' Hag HC' Hfs. exfalso. exact (kn_contra_sound SEGS E' _ _ (co_know HC') Hkb). }
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv sa sb) eqn:Hse; [|discriminate]. injection Hc as <-.
    eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD
      | exact (CONT kb1 csa sa Hgp H1) |].
    intros E' fx' R' M' model' Hag HC' Hfs. eapply shape_eqv_transfer; [exact Hse|]. exact (CONT kb2 csb sb Hgp2 H2 E' fx' R' M' model' Hag HC' Hfs).
  - (* [comment removed for export] *)
    rename X into Hgpk. rename Hgp into Hgpb.
    eapply (check_loop_sound fuel bfuel (IH bfuel)); [ | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a [<-|[]]. split; [exact Hgpb | exact Hgpk].
  - (* [comment removed for export] *)
    eapply check_next_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    unfold AP.check_handoff in Hc.
    destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
    change (if entails A cs ch then true else entails_tw A nx0 (nxt ch) [] cs ch) with (entails A cs ch || entails_tw A nx0 (nxt ch) [] cs ch)%bool in Hc.   (* [comment removed for export] *)
    destruct (entails A cs ch || entails_tw A nx0 (nxt ch) [] cs ch)%bool eqn:He; [|discriminate].
    assert (HR : RZ (cfg fx R (pc cs) M model) (HOLES h E (m_fs model))).
    { apply orb_prop in He as [He|He].
      - destruct (entails_sound E cs ch fx R M model HC He) as [HC' Hpc].
        pose proof (HS_sound h ch Hh E fx R M model HC') as HR. rewrite Hpc in HR. exact HR.
      - destruct (entails_tw_sound nx0 (nxt ch) [] E cs ch fx R M model HC He ltac:(lia)) as (E' & Hag & HC' & Hpc).
        pose proof (HS_sound h ch Hh E' fx R M model HC') as HR. rewrite Hpc in HR.
        rewrite (HOLES_agree h E E' (m_fs model) Hag). exact HR. }
    destruct (lc_xmode lc) eqn:Hxm; injection Hc as <-; cbn [sd]; [|exact HR].
    pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as Hx.
    eapply RZ_conseq; [exact HR|]. rewrite (HOLES_same h). intros tr. pose proof (Hx tr). tauto.
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs fx R M model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT ik cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { destruct (run_block_gc SEGS IT _ false KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
      intros E' fx' R' M' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hgp Hc E' fx' R' M' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ false KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ false KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' fx' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hgp Hc E'' fx' R' M' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' fx' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hgp Hc E'' fx' R' M' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs fx R M model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB ISP0 KC XA XT false _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hgp | exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs fx R M model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB ISP0 KC XA XT false _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hgp | exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    rename X into Hgpk. rename Hgp into Hgpa.
    eapply (check_via_sound fuel bfuel (IH bfuel)); [exact Hgpa | | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a [<-|[]]. exact Hgpk.
  - (* [comment removed for export] *)
    eapply check_merge_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs fx R M model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME ak _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs fx R M model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hwk cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs fx R M model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME rsk _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    eapply check_next_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    eapply check_merge_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate]. cbv zeta in Hc.
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [ | | exact Hc | exact HC | exact HL | exact Hg | exact HD];
      destruct pos; assumption.
  - (* [comment removed for export] *)
    rename X into Hgp2. cbv zeta in Hc.
    set (ce := reg cs crr) in Hc.
    destruct (brange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo crmid && Z.ltb crmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi crmid); [exact (SAME crk1 _ s Hgp Hc HC) | exact (SAME crk2 _ s Hgp2 Hc HC)]. }
    cbn [negb] in Hc.
    destruct (split_sound cs ce crmid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo crmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
      - exact (SAME crk2 _ s Hgp2 Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (crmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
      - exact (SAME crk1 _ s Hgp Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo crmid :: kn cs)) crk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (crmid+1) hi :: kn cs)) crk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
    + exact (SAME crk1 _ s1 Hgp H1 (HCl Hle)).
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME crk2 _ s2 Hgp2 H2 (HCr ltac:(lia))).  - (* [comment removed for export] *)
    destruct (factvia_ok (kn cs) fve fvv fvlo fvhi) eqn:Hf; [|discriminate].
    refine (SAME fvk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factvia_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    unfold AP.check_handoff in Hc.
    destruct (HS hwh) as [ch|] eqn:Hh; [|discriminate].
    change (if entails A cs ch then true else entails_tw A nx0 (nxt ch) hww cs ch) with (entails A cs ch || entails_tw A nx0 (nxt ch) hww cs ch)%bool in Hc.   (* [comment removed for export] *)
    destruct (entails A cs ch || entails_tw A nx0 (nxt ch) hww cs ch)%bool eqn:He; [|discriminate].
    assert (HR : RZ (cfg fx R (pc cs) M model) (HOLES hwh E (m_fs model))).
    { apply orb_prop in He as [He|He].
      - destruct (entails_sound E cs ch fx R M model HC He) as [HC' Hpc].
        pose proof (HS_sound hwh ch Hh E fx R M model HC') as HR. rewrite Hpc in HR. exact HR.
      - destruct (entails_tw_sound nx0 (nxt ch) hww E cs ch fx R M model HC He ltac:(lia)) as (E' & Hag & HC' & Hpc).
        pose proof (HS_sound hwh ch Hh E' fx R M model HC') as HR. rewrite Hpc in HR.
        rewrite (HOLES_agree hwh E E' (m_fs model) Hag). exact HR. }
    destruct (lc_xmode lc) eqn:Hxm; injection Hc as <-; cbn [sd]; [|exact HR].
    pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as Hx.
    eapply RZ_conseq; [exact HR|]. rewrite (HOLES_same hwh). intros tr. pose proof (Hx tr). tauto.
  - (* [comment removed for export] *)
    destruct (factle_ok (kn cs) fle flb flhi) eqn:Hf; [|discriminate].
    refine (SAME flk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    destruct (factscale_ok (kn cs) fse fsc fshi) eqn:Hf; [|discriminate].
    refine (SAME fsk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factscale_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (eaddz (reg cs flr) flo) flb2 flh2) eqn:Hf; [|discriminate].
    refine (SAME flk2 _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (eaddz (reg cs frr) fro) frlo frhi)) eqn:Hf; [|discriminate].
    refine (SAME frk _ s Hgp Hc _). exact (fact_sound E cs fx R M model _ HC Hf).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (APC.esubst fxph (reg cs fxr) fxe) (APC.esubst fxph (reg cs fxr) fxb) fxhi) eqn:Hf; [|discriminate].
    refine (SAME fxk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (APC.esubst gxph (reg cs gxr) gxe) gxlo gxhi)) eqn:Hf; [|discriminate].
    refine (SAME gxk _ s Hgp Hc _). exact (fact_sound E cs fx R M model _ HC Hf).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound SEGS E _ (kn cs) (co_know HC) Hk).
  - (* [comment removed for export] *)
    eapply (check_loop_sound fuel bfuel (IH bfuel)); [ | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a Hin. exact (gplan_ok_lalts malts a Hgp Hin).
  - (* [comment removed for export] *)
    rename X into Hgpv.
    eapply (check_via_sound fuel bfuel (IH bfuel)); [exact Hgp | | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a Hin. eapply (gplan_ok_valts walts wka a); [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. rewrite Hgp, Hgpv. reflexivity.
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate].
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [exact Hgp | exact Hgp2 | exact Hc | exact HC | exact HL | exact Hg | exact HD].
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (XA aid aargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa aka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb akb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    eapply (node_alt2_sound aid aargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD | apply sd_has_nil; exact HD
      | exact (CONT aka csa sa Hgp H1) | exact (CONT akb csb sb Hgp2 H2)].
  - (* [comment removed for export] *)
    destruct (XT tid targs cs) as [[[fd ps] code]|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    exact (node_term_sound tid targs cs fd ps code E fx R M model HC Hn).
Qed.

End Sound.

(* [comment removed for export] *)

Arguments co_regs {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_log {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_know {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_halt {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_fs {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_fds {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_ainv {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_uinv {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_fx {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_perm {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_top {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_kcap {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_fbud {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
Arguments co_floor {SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model} _.
End GPS.

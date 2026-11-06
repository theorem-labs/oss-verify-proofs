(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt CXXRep CXXLib CXXLib2 HeapSR_iface CXXHeap XRep XA_leaves XL_mutex XA_alloc XS_sp XA_registry XA_sched_ctor2 XA_sched_ctor5 XA_sched_dtor XS_ctor XS_ctor2 XS_dtor XS_dtor4 XA_sched_hdr XFuzz_stmt XFuzz_stmt2 XUbsan XH_fuzzA XH_fuzzB XH_fuzzC XH_fuzzH.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim STree Malloc Prog.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 Set StepFast.sf_check := true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac lia ::= lia2w.
(* [comment removed for export] *)
Local Ltac slia_consumed_abort :=
  match goal with
  | |- context [(?A + ?s <= ?A \/ ?h <= ?A)%Z] =>
      first [ assert (A < A + s /\ A < h)%Z by (zify_prune; xlia_noeuclid); fail 2 | fail ]
  | |- _ => idtac
  end.
Local Ltac slia ::= first [ exact I | slia_consumed_abort; slia2w ].
(* [comment removed for export] *)
Tactic Notation "callZc" uconstr(SPEC) tactic3(CLR) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | CLR; post_callZ segs m ]
  end.
Local Ltac clr_stk := idtac; match goal with STx : stk _ _ _ _ |- _ => clear STx end.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac fast_eassumption :=
  first [ lazymatch goal with
          | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
          | |- ro_cells _ _ ?A _ => match goal with H : ro_cells _ _ A _ |- _ => exact H end
          | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
          | |- u8arr _ _ ?A _ => match goal with H : u8arr _ _ A _ |- _ => exact H end
          end
        | eassumption ].
Local Ltac fast_assumption :=
  lazymatch goal with
  | |- ?G => tryif has_evar G then assumption else
             first [ lazymatch G with
                     | rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
                     | ro_cells _ _ ?A _ => match goal with H : ro_cells _ _ A _ |- _ => exact H end
                     | bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
                     | u8arr _ _ ?A _ => match goal with H : u8arr _ _ A _ |- _ => exact H end
                     end
                   | assumption ]
  end.
(* [comment removed for export] *)
Ltac2 fit_clear_arith () : unit :=
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if Bool.and (LiaTuning.zt_is_local id)
                     (Bool.and (LiaTuning.zt_is_prop ty) (Bool.or (LiaTuning.zt_plain_arith ty) (LiaTuning.zt_twoway ty)))
                then Some id else None
      end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac qtauto :=
  first [ solve [ lazymatch goal with H : _ |- _ => clear - H end; tauto ]     (* [comment removed for export] *)
        | solve [ ltac2:(Control.enter fit_clear_arith); tauto ]             (* [comment removed for export] *)
        | tauto ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_of_ids : forall (LB : list block), List.NoDup (map blk_id LB) -> List.NoDup LB.
Proof.
  induction LB as [|b LB IH]; intros ND; [constructor|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  constructor; [| apply IH; exact ND']. intros K. apply NI. apply in_map. exact K.
Qed.

Lemma NoDup_ids_perm : forall (L L' : list block), Permutation L L' -> List.NoDup (map blk_id L) -> List.NoDup (map blk_id L').
Proof. intros L L' PE ND. eapply Permutation_NoDup; [apply Permutation_map; exact PE| exact ND]. Qed.

(* [comment removed for export] *)
Lemma mine_fresh : forall (mine LB : list block) b,
  List.NoDup (map blk_id (mine ++ LB)) -> In b mine -> ~ In (blk_id b) (map blk_id LB).
Proof.
  intros mine LB b ND IN K. rewrite map_app in ND. eapply (NoDup_app_disjoint _ _ (blk_id b) ND); [apply in_map; exact IN| exact K].
Qed.

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma lb_remove_perm : forall L x,
    List.NoDup (map blk_id L) -> In x L -> Permutation L (x :: hs_lb_remove H (blk_id x) L).
  Proof.
    induction L as [|c L IH]; intros x ND IN; [destruct IN|].
    cbn in ND. inversion ND as [|y l NI ND']; subst.
    destruct IN as [<-|IN].
    - destruct c as [[pc Ac] nc]. cbn. rewrite (proj1 (hh_lb_remove H HH)) by exact NI. apply Permutation_refl.
    - assert (NE : blk_id c <> blk_id x).
      { intros E. apply NI. rewrite E. apply in_map. exact IN. }
      rewrite (hh_lb_remove_cons_ne H HH) by exact NE.
      eapply Permutation_trans; [apply perm_skip; apply IH; [exact ND'| exact IN]|]. apply perm_swap.
  Qed.

  (* [comment removed for export] *)
  Lemma bperm_free : forall LBc x rest,
    List.NoDup (map blk_id LBc) -> Permutation LBc (x :: rest) ->
    Permutation (hs_lb_remove H (blk_id x) LBc) rest /\ List.NoDup (map blk_id (hs_lb_remove H (blk_id x) LBc)).
  Proof.
    intros LBc x rest ND PE.
    assert (IN : In x LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PE| left; reflexivity]).
    pose proof (lb_remove_perm _ _ ND IN) as P1. split.
    - eapply Permutation_cons_inv. eapply Permutation_trans; [apply Permutation_sym; exact P1| exact PE].
    - pose proof (NoDup_ids_perm _ _ P1 ND) as ND1. cbn in ND1. inversion ND1; subst. fast_assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_not_client_gen : forall s LBc LB m1 b SP a,
    hs_RHEAP H s LBc m1 -> (forall b', In b' LB -> In b' LBc) -> In b LBc -> ~ In (blk_id b) (map blk_id LB) ->
    hceil <= SP -> rclient_addr LB SP a -> a + 1 <= blk_addr b \/ blk_addr b + blk_size b <= a.
  Proof.
    intros s LBc LB m1 b SP a HP SUB IN NI CE HC.
    pose proof (hh_blocks H HH _ _ _ _ HP IN) as (R1 & R2 & R3 & R4 & R5).
    destruct HC as [HC|[[HC _]|(b' & Hb' & Hr)]]; [right; lia| lia|].
    destruct (hh_disj H HH _ _ _ _ _ HP IN (SUB _ Hb')) as [D|D]; [| lia| lia].
    intros E. apply NI. rewrite E. apply in_map. exact Hb'.
  Qed.

  (* [comment removed for export] *)
  Definition fzXg (P : Z) (LB LBc : list block) (a : Z) : Prop :=
    (hceil <= a < P + 512) \/ (exists b, In b LBc /\ ~ In (blk_id b) (map blk_id LB) /\ blk_addr b <= a < blk_addr b + blk_size b).

  Lemma fzXg_not_client : forall s LBc LB m1 P a,
    hs_RHEAP H s LBc m1 -> (forall b', In b' LB -> In b' LBc) -> hceil <= P + 512 ->
    rclient_addr LB (P + 512) a -> fzXg P LB LBc a -> False.
  Proof.
    intros s LBc LB m1 P a HP SUB CE HC [K|(b & Hb & NI & K)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [lia| hcb; lia|].
      pose proof (hh_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & R4 & _). lia.
    - pose proof (fresh_not_client_gen _ _ _ _ _ _ _ HP SUB Hb NI CE HC). lia.
  Qed.

  Lemma xp_lift_gen : forall s LBc LB m1 m0 m m' P SP X,
    xpres LB (P + 512) XH_X m0 m ->
    xpres LBc SP X m m' -> SP <= P + 512 -> hceil <= P + 512 ->
    hs_RHEAP H s LBc m1 -> (forall b', In b' LB -> In b' LBc) ->
    (forall a, rin_ivs X a -> fzXg P LB LBc a \/ (XH_LO <= a < XH_HI)) ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s LBc LB m1 m0 m m' P SP X X0 XP LE CE HP SUB HX.
    eapply xpres_trans; [exact X0|]. intros a Ha [HC NX]. apply XP; [exact Ha|]. split.
    - destruct HC as [K|[K|(b & Hb & K)]]; [left; lia| right; left; exact K| right; right].
      exists b. split; [apply SUB; exact Hb| exact K].
    - intros R. destruct (HX a R) as [K|K].
      + exact (fzXg_not_client _ _ _ _ _ _ HP SUB CE HC K).
      + apply NX. apply rin_ivs_XH. exact K.
  Qed.

  Lemma xp_lift_munch_gen : forall s LBc LB m1 m0 m m' P W,
    xpres LB (P + 512) XH_X m0 m ->
    munch W m m' -> wmono usegs m m' -> hceil <= P + 512 ->
    hs_RHEAP H s LBc m1 -> (forall b', In b' LB -> In b' LBc) ->
    Forall (fun iv : Z * Z => forall a, fst iv <= a < snd iv -> fzXg P LB LBc a \/ (XH_LO <= a < XH_HI)) W ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s LBc LB m1 m0 m m' P W X0 MU WM CE HP SUB FW.
    eapply xpres_trans; [exact X0|]. eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC NX]. clear MU WM X0. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as F1. cbn in F1. split; [| apply IH; exact (Forall_inv_tail FW)].
    intros R. destruct (F1 a R) as [K|K].
    - exact (fzXg_not_client _ _ _ _ _ _ HP SUB CE HC K).
    - apply NX. apply rin_ivs_XH. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma xp_lift_free_gen : forall s LBc LB m1 m0 m m' P SP p A n,
    xpres LB (P + 512) XH_X m0 m ->
    hs_RHEAP H s LBc m1 -> (forall b', In b' LB -> In b' LBc) ->
    In (p, A, n) LBc -> ~ In p (map blk_id LB) ->
    rheap_pres (hs_lb_remove H p LBc) SP m m' -> SP <= P + 512 -> hceil <= P + 512 ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s LBc LB m1 m0 m m' P SP p A n X0 HP SUB IN NI RP LE CE.
    eapply (xp_lift_gen s LBc LB m1 m0 m m' P SP [(A, A + n)]); [exact X0| | exact LE| exact CE| exact HP| exact SUB|].
    - eapply (xpres_free H HH); [exact HP| exact IN| exact RP|]. intros a Ha. cbn. left. exact Ha.
    - intros a [R|[]]. left. right. exists (p, A, n). split; [exact IN|]. split; [exact NI| cbn; cbn in R; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma in_pin : forall s L m p0 A n p,
    hs_RHEAP H s L m -> In (p0, A, n) L -> 0 < n -> In (p, A, n) L -> p = p0.
  Proof.
    intros s L m p0 A n p HP IN0 N0 IN. destruct (bptr_eq_dec p p0) as [E|NE]; [exact E|]. exfalso.
    destruct (hh_disj H HH _ _ _ _ _ HP IN IN0) as [D|D]; [cbn; exact NE| cbn in D; lia| cbn in D; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma AllocImpl_reix : forall s L L' m m0 p0 a,
    hs_RHEAP H s L m0 -> In (p0, a, SZ_ALLOCIMPL) L -> In (p0, a, SZ_ALLOCIMPL) L' -> AllocImpl L m a -> AllocImpl L' m a.
  Proof.
    intros s L L' m m0 p0 a HP IN IN' (p & j & INp & C). exists p, j. split; [| exact C].
    rewrite (in_pin _ _ _ _ _ _ _ HP IN ltac:(unfold SZ_ALLOCIMPL; lia) INp). exact IN'.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
  Lemma Registry_reix : forall s L L' m m0 p0 r o f lk,
    hs_RHEAP H s L m0 -> In (p0, r, NEWSZ_REG) L -> In (p0, r, NEWSZ_REG) L' -> Registry L m r o f lk -> Registry L' m r o f lk.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.PState); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.block); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.HeapSR_iface.hs_RHEAP); constr:(H); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.NEWSZ_REG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.Registry); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.PMutex); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.O_REG_MUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.O_REG_OWNER); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.SZ_REG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.CookieCells); constr:(@kc__2); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XH_fuzzJ.HCW.W.in_pin); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@kc__1 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))); constr:(@kc__1 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr))|] [|@j7; @j0; @p; @__ff; @__varmap; @__wit; @__arith; @C; @INp; @H0; @x; @IN'; @IN; @HP; @lk; @f; @o; @r; @p0; @m0; @m; @L'; @L; @s|] "#'y#B$%#J#Z#\#I#P#0#c#d#g###2#6#3#4#:#1#5#7#.#9#;#<#,#=#(#-#/#$#8#%#?#+#@#'#)#>#&#*#x#H#`#n#w#t#u#K#G#L#M#W#U#T#_#A#o#p#r#z#v#y#q#s#|#}$#$$$%$&#~$'#m#l#k#i#E#X#Y#b#[#O#N#f#e#a#S#]#^#Q#h#F#{#V#j#R6#n%#o'#p%#q&#r'#s&#t$#u$#v&#w%#x%#y$#z)#{$#|$#}$#~$$#'$$(1SAVS:FCVS:#C1#XSBSCS)S2S+'FCS+S4''C#G('#S)'FCS5S+'*C#G(*#S)/S%S)S5S+S4S73SD3#3#USE#USF#1#'FCS0S,'4C#G(4#M.SG.#.#.#.#.#.#.#-#S.US;E&E$#$DHS,#%S,I+H#S8%S,J)S)*#)S2*#&E#,&E&#$DH)#%S,K0L$DH$##&##/##2##?#j#$s###,s#$#j#%s#%#,s#&#j#&F#,F#/S-S%S2S8S5S+j##$#'FCS0S%'s#<C#G(s#<#O$DRS%@%S%I+R#S2%S%J)S,*#&E@s#'&E$#$DR'#%S%K$DR#=#%##,##/##1#j#$s#=#,s#>#j#%s#?#,s#@#j#&F#U#L'FCS0S-'s#TC#G(s#T#P$DMS-s#8%S-I+M#S)%S-J)S%*#&E;s#?&E$#$DM'#%S-K$DM#s#5#%##,##/##1#j#$s#U#,s#V#j#%s#W#,s#X#'FCS7H's#jC#G(s#j#S#$DOHs#N%HI+O#S,%HJ)S-*#&E9s#U&E$#$DO'#%HK$DO#s#K#%##,##/##1#j#$s#k#,s#l#j#%s#m#,s#n#/OMS-S%S,S)j##$#'FCS4R's$&C#G(s$&#N$DPRs#f%RI+P#S%%RJ)H*#&E;s#m&E$#$DP'#%RK$DP#s#c#%##,##/##1#j#$s$'#,s$(#j#%s$)#U#L'FCS+M's$<C#G(s$<#S$$DS#Ms#|%MI+S##S-%MJ)R*#&E9s$'&E$#$DS#'#%MK$DS##s#y#%##,##/##1#j#$s$=#,s$>#'FCS5O's$PC#G(s$P#S/-s$7S0&E#s$6$DNO#%OI+N#H%OJ)M*#&E9s$=&E$#$DN'#%OK$DN#s$3#%##,##/##3#j#$s$S#,s$T#/S$NOMRHj##$#'FCS8P's$hC#G(s$h#S&-s$OS7&E#s$N$DS$P#%PI+S$#R%PJ)O*#&E;s$U&E$#$DS$'#%PK$DS$#s$K#%##,##/##3#j#$s$k#U#L'FCS2S#'s$~C#G(s$~#Q-s$eS4&E#s$d$DS/S##%S#I+S/#M%S#J)P*#&E9s$k&E$#$DS/'#%S#K$DS/#s$a#%##,##/##3#'FCS)N's%6C#G(s%6#S'-s$yS+&E#s$x$DS&N#%NI+S&#O%NJ)S#*#&E7s%#&E$#$DS&'#%NK0S.$DS&$##&##-##0##4#/S'QS$NS#Pj##$#-s%1S5&E#s%0$DQS$#%S$I+Q#P%S$J)N*#&E7s%7&E$#$DQ'#%S$K0S0$DQ$##&##-##0#'FCS%S/'s%^C#G(s%^#S*-s%ES2&E#s%D$DS(S&#%S&I+S(#N%S&J)S/*#)S$*#&E#s%M&E&#$DS()#%S&K0S4$DS($##&##/##2#'FCS0S*'s%tC#G(s%t#SH$DS3S*s%X%S*I+S3#Q%S*J)S(*#)S'*#&E#s%a&E&#$DS3)#%S*K$DS3#s%W#%##.##1##3#j#$s%w#,s%x#j#%s%y#,s%z#j#&F#'FCMS('s&1C#G(s&1#S3$DS1S(s%q%S(I+S1#S&%S(J)Q*#&E#s%x&E;#$DS1'#%S(K$DS1#s%n#%##,##/##1#j#$s&2#,s&3#j#%s&4#'FCRS''s&FC#G(s&F#S1-s&-S,&E#s&,$DS6S'#%S'I+S6#S/%S'J)S&*#&E#s&3&E;#$DS6'#%S'K$DS6#s&)#%##,##/##3#j#$s&I#'FCHQ's&[C#G(s&[#S6-s&BS)&E#s&A$DS*Q#%QI+S*#S$%QJ&Es#Zs&F&E7#$DS*%#%QK0S+$DS*$##&##+##.#'FCLS''s&mC#G(s&m#S1j#&F#US;S<1S<USICUSJCUSKCVS=CS92s&j2#2#2#USL#VS=C#XSMC)SN#[SO+SPS>S>S?#SQVSR,S?VSSSTSUWSVCS9S.XSWLS0$#l#''&#l#(32#l#)65#VSXS9-l#*$#L_SYS3S1S(S'QGHNS##S.ZSZFS';PH#XS[s#/@#L4s&zs#3S+#4s&{s#IS)#4Fs#_H#j#+s#y#j#,s$1#V#S.Lj##s$6#j##s$\#YS\s$]s$Ls$I#Lj#-s$a#j#$s'(#V#S.Lj##s$x#j#.s'+#5s',s%7s%4#Lj#-s%M#j#%s'.#V#S.Lj##s%d#j#.s'1#5s'2s&#s%|#Lj#-s&9#j#&F#V#S.Lj##s&R#j#.F#5Fs&os&l#Lj#-s'?#j#/s'A#j#0s'E#j#1s'I#j#2C#j#3C#j#4C#j#5C#j#6F#j#7S@#j#8S@#j#9s'R#j#:s'V#j#;S]##"). Qed.
  Lemma ConfigSvc_reix : forall s L L' m m0 p0 c S,
    hs_RHEAP H s L m0 -> In (p0, c, NEWSZ_CFG) L -> In (p0, c, NEWSZ_CFG) L' -> ConfigSvc L m c S -> ConfigSvc L' m c S.
  Proof.
    intros s L L' m m0 p0 c S HP IN IN' (p & j4 & j7 & INp & C). exists p, j4, j7. split; [| exact C].
    rewrite (in_pin _ _ _ _ _ _ _ HP IN ltac:(unfold NEWSZ_CFG; lia) INp). exact IN'.
  Qed.
  Lemma Scheduler_reix : forall s L L' m m0 p0 sb S,
    hs_RHEAP H s L m0 -> In (p0, sb, NEWSZ_SCH) L -> In (p0, sb, NEWSZ_SCH) L' -> Scheduler L m sb S -> Scheduler L' m sb S.
  Proof.
    intros s L L' m m0 p0 sb S HP IN IN' (p & j50 & jm & j109 & je & jt & j219 & j7 & INp & C). exists p, j50, jm, j109, je, jt, j219, j7.
    split; [| exact C]. rewrite (in_pin _ _ _ _ _ _ _ HP IN ltac:(unfold NEWSZ_SCH; lia) INp). exact IN'.
  Qed.

  (* [comment removed for export] *)
  Lemma in_after_free : forall s L m b p,
    hs_RHEAP H s L m -> In b L -> blk_id b <> p -> In b (hs_lb_remove H p L).
  Proof. intros s L m b p HP IN NE. apply (hh_lb_remove_keep H HH); [exact (hh_nodup H HH _ _ _ HP)| exact IN| exact NE]. Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fz_ours4 (W : fzw) : list block :=
  [(w_p8 W, w_va W, 8); (w_p6 W, w_q W, SZ_SPCI_IMPL); (w_p5 W, w_v W, NEWSZ_SSVC); (w_p4 W, w_schedb W, NEWSZ_SCH);
   (w_p3 W, w_cfgb W, NEWSZ_CFG); (w_p2 W, w_regb W, NEWSZ_REG); (w_p1 W, w_allocb W, SZ_ALLOCIMPL)].

(* [comment removed for export] *)
Definition fb_inv (FB : fbv) (FBB : list block) : Prop :=
  (FB = FB_empty /\ FBB = [])
  \/ (exists pf, FBB = [(pf, fb_begin FB, fb_cap FB)] /\ 0 < fb_begin FB /\ fb_begin FB <= fb_end FB /\ fb_end FB <= hceil).

Lemma NoDup_hd_ne : forall {A} (a b : A) l, List.NoDup (a :: l) -> In b l -> a <> b.
Proof. intros A a b l ND IN E. subst. inversion ND; subst. contradiction. Qed.

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis RHEAP_canary : forall s LB m, hs_RHEAP H s LB m -> CanaryReads m.
  Variable FT : mem -> Prop.
  Hypothesis FT_local : ft_local FT.

  Definition fzK4 (gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P lo B : Z) (ra s0 s1 : word) (LB : list block) (m0 : mem) (mo : Model) : config -> Prop :=
    fun c => exists rax t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m (s' : PState) (errv : word) (W : fzw) (LBc : list block)
                    (FB : fbv) (FBB : list block) (c8 : cell) (cS cE : list cell),
      cfg_ms c = MS (mkR rax (Z_to_bv 64 P) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_FZ_RET_SDT) fc None m (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m /\ stk usegs m lo P
      /\ rw_cells usegs m (errno_addr tp) [C4 errv] /\ hs_rauxv_ok H m B
      /\ hs_RHEAP H s' LBc m /\ Permutation LBc ((fz_ours4 W ++ FBB) ++ LB)
      /\ rw_cells usegs m (P + 392) (IoCtxCells (w_allocb W) (w_regb W) (w_schedb W))
      /\ AllocImpl LBc m (w_allocb W)
      /\ Registry LBc m (w_regb W) (P + 392) (w_v W) 0
      /\ ConfigSvc LBc m (w_cfgb W) (cfg_hdr (P + 392))
      /\ Scheduler LBc m (w_schedb W) (mkSCH (sched_hdr (P + 392) (w_cfgb W)) 0 0 0)
      /\ StreamSvc LBc m (w_v W) (ssvc_hdr (P + 392) (w_schedb W)) (w_q W)
      /\ ImplBlock LBc m (w_q W) (mkIMPL (mkSPC VP_SPCI_IMPL 1 1 1) 0 (w_va W) [] 1)
      /\ rw_cells usegs m P [c8] /\ csize c8 = 8%nat /\ stk usegs m (P + 8) (P + 360)
      /\ rw_cells usegs m (P + 360) cS /\ cells_size cS = 32%nat
      /\ rw_cells usegs m (P + 416) (FlatBufCells FB) /\ fb_inv FB FBB
      /\ rw_cells usegs m (P + 464) cE /\ cells_size cE = 24%nat
      /\ rw_cells usegs m (P + 488) [C8 s1; C8 s0; C8 ra]
      /\ HStat FT m
      /\ xpres LB (P + 512) XH_X m0 m.

  (* [comment removed for export] *)
  Definition fz_final (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P lo B : Z) (LB : list block) (m0 : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LB' : list block),
      cfg_ms c = MS (mkR ra (Z_to_bv 64 (P + 512)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (P + 512)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LB' m' /\ Permutation LB' LB
      /\ HStat FT m'
      /\ xpres LB (P + 512) XH_X m0 m'.

  Lemma fz_HJ : forall gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32)
      (P D N lo B : Z) (ra s0 s1 : word) (LB : list block) (m0 : mem) (mo : Model) (c : config),
    fz_pure H P D N lo B ra LB -> XImg m0 -> tp = Z_to_bv 64 RATP ->
    fzK4 gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P lo B ra s0 s1 LB m0 mo c ->
    hs_SR H (fz_final ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P lo B LB m0 mo) c.
  Proof.
    intros until c. intros PU XI TP K4.
    pose proof PU as (AL & CEIL & LO & PB & BHI & P47 & RAE & NR & DAL & D0 & DNH & INB & DEMP & BUD & BUDC).
    unfold FUZZ_STACK in LO. clear BUD BUDC INB DEMP DAL D0 DNH NR. hcb.
    destruct c as [ms moc]. unfold fzK4 in K4. cbn [cfg_ms cfg_model] in K4.
    destruct K4 as (rax & t0 & t1 & t2 & s0x & s1x & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & s' & errv & W & LBc & FB & FBB & c8 & cS & cE
                    & -> & KREL & MP & MI & ST & ERR & AUX & HP & PERM & IOC & AI & REG & CFG & SCH & SSVC & IMPL & FRP & SZ8 & STK8 & FRS & SZS & FBC & FBI & FRE & SZE & SAV & HS & XP).
    destruct W as [p1 allocb p2 regb p3 cfgb p4 schedb p5 v p6 q p7 stb p8 va p9 A].
    cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A] in *.
    unfold fz_ours4 in PERM. cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A app] in PERM.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = RERRNO) by (unfold RATP, RERRNO; rewrite unsigned_lit; lia).
    subst tp. rewrite EA in ERR. 
    assert (AL48 : (P + -48) mod 16 = 0) by (clear - AL; Z.div_mod_to_equations; lia).
    assert (AL392 : (P + 392) mod 8 = 0) by (clear - AL; Z.div_mod_to_equations; lia).
    change (alg 16 P) in AL. change (alg 16 (P + -48)) in AL48. change (alg 8 (P + 392)) in AL392.
    (* [comment removed for export] *)
    pose proof (hh_nodup H HH _ _ _ HP) as NDc.
    pose proof (NoDup_ids_perm _ _ PERM NDc) as NDm. cbn [map blk_id fst snd app] in NDm. rewrite map_app in NDm.
    assert (SUB : forall b, In b LB -> In b LBc).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn. do 7 right. apply in_or_app. right. exact Hb. }
    assert (INo : forall b, In b [(p8, va, 8); (p6, q, SZ_SPCI_IMPL); (p5, v, NEWSZ_SSVC); (p4, schedb, NEWSZ_SCH); (p3, cfgb, NEWSZ_CFG); (p2, regb, NEWSZ_REG); (p1, allocb, SZ_ALLOCIMPL)] -> In b LBc).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn in Hb |- *. qtauto. }
    pose proof (INo (p8, va, 8) ltac:(cbn; qtauto)) as IN8. pose proof (INo (p6, q, SZ_SPCI_IMPL) ltac:(cbn; qtauto)) as IN6.
    pose proof (INo (p5, v, NEWSZ_SSVC) ltac:(cbn; qtauto)) as IN5. pose proof (INo (p4, schedb, NEWSZ_SCH) ltac:(cbn; qtauto)) as IN4.
    pose proof (INo (p3, cfgb, NEWSZ_CFG) ltac:(cbn; qtauto)) as IN3. pose proof (INo (p2, regb, NEWSZ_REG) ltac:(cbn; qtauto)) as IN2.
    pose proof (INo (p1, allocb, SZ_ALLOCIMPL) ltac:(cbn; qtauto)) as IN1. clear INo.
    unfold SZ_SPCI_IMPL, NEWSZ_SSVC, NEWSZ_SCH, NEWSZ_CFG, NEWSZ_REG, SZ_ALLOCIMPL in IN8, IN6, IN5, IN4, IN3, IN2, IN1.
    pose proof (hh_blocks H HH _ _ _ _ HP IN8) as (E1 & _ & _ & E4 & _). cbn in E1, E4.
    pose proof (hh_blocks H HH _ _ _ _ HP IN6) as (Q1 & Q2 & _ & Q4 & _). cbn in Q1, Q2, Q4. change (alg 16 q) in Q2.
    pose proof (hh_blocks H HH _ _ _ _ HP IN5) as (V1 & V2 & _ & V4 & _). cbn in V1, V2, V4.
    pose proof (hh_blocks H HH _ _ _ _ HP IN4) as (S1 & S2 & _ & S4 & _). cbn in S1, S2, S4.
    pose proof (hh_blocks H HH _ _ _ _ HP IN3) as (Y1 & Y2 & _ & Y4 & _). cbn in Y1, Y2, Y4.
    pose proof (hh_blocks H HH _ _ _ _ HP IN2) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
    pose proof (hh_blocks H HH _ _ _ _ HP IN1) as (A1 & A2 & _ & A4 & _). cbn in A1, A2, A4.
    (* [comment removed for export] *)
    assert (V8 : v mod 8 = 0) by (clear - V2; Z.div_mod_to_equations; lia).
    assert (S8 : schedb mod 8 = 0) by (clear - S2; Z.div_mod_to_equations; lia).
    assert (C8' : cfgb mod 8 = 0) by (clear - Y2; Z.div_mod_to_equations; lia).
    assert (R8 : regb mod 8 = 0) by (clear - R2; Z.div_mod_to_equations; lia).
    assert (A8 : allocb mod 8 = 0) by (clear - A2; Z.div_mod_to_equations; lia).
    change (alg 16 v) in V2. change (alg 16 schedb) in S2. change (alg 16 cfgb) in Y2. change (alg 16 regb) in R2. change (alg 16 allocb) in A2.
    change (alg 8 v) in V8. change (alg 8 schedb) in S8. change (alg 8 cfgb) in C8'. change (alg 8 regb) in R8. change (alg 8 allocb) in A8.
    assert (OFF : forall b b', In b LBc -> In b' LBc -> b <> b' -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb' NE. exact (blocks_neq_disjoint H HH _ _ _ _ _ HP Hb Hb' NE). }
    assert (NE52 : p5 <> p2).
    { pose proof NDm as ND'. do 2 (apply List.NoDup_cons_iff in ND'; destruct ND' as [_ ND']).
      intros E. exact (NoDup_hd_ne p5 p2 _ ND' ltac:(cbn; qtauto) E). }
    assert (H1HY : forall mm sh, rw_cells usegs mm (P + 392) (IoCtxCells allocb regb schedb) ->
              Registry LBc mm regb (P + 392) v 0 -> StreamSvc LBc mm v (ssvc_hdr (P + 392) schedb) q ->
              ImplBlock LBc mm q (mkIMPL (mkSPC VP_SPCI_IMPL 1 1 1) 0 va [] 1) ->
              Scheduler LBc mm schedb (mkSCH (sched_hdr (P + 392) cfgb) 0 0 sh) -> ConfigSvc LBc mm cfgb (cfg_hdr (P + 392)) ->
              XStatics mm -> mem_inv usegs mm ->
              fzH1_hyps mm P allocb regb cfgb schedb v q va 1 lo LBc sh).
    { intros mm sh K1 K2 K3 K4 K5 K6 K7 K9. unfold fzH1_hyps, NEWSZ_REG, NEWSZ_SSVC, NEWSZ_SCH, NEWSZ_CFG, SZ_SPCI_IMPL.
      pose proof (hh_blocks H HH _ _ _ _ HP IN4) as (_ & _ & _ & _ & S5). cbn in S5.
      repeat match goal with |- _ /\ _ => split end; try fast_assumption; try lia.
      - destruct (OFF _ _ IN5 IN6 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN8 IN6 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN2 IN6 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN2 IN4 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN5 IN4 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN3 IN6 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN3 IN4 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN6 IN4 ltac:(congruence)); cbn in *; lia.
      - destruct (OFF _ _ IN8 IN4 ltac:(congruence)); cbn in *; lia. }
    (* [comment removed for export] *)
    eapply (hh_evt_then H HH); [exact KREL| |].
    { eapply fzH1a; [apply H1HY; try fast_assumption; eapply XStatics_xpres0; [exact XI| exact XP]| exact ST| unfold FZ_H1_STACK, SSVC_SHUTDOWN_STACK, MTX_UNLOCK_STACK; lia]. }
    intros ms1 PO. unfold fzH1a_post in PO.
    destruct PO as (ra1 & x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & vs1 & vs0 & j0 & j8
                    & -> & MU & WM & MI1 & ST1 & FRX & SSVC1 & IMPL1 & SCH1).
    unfold SZ_SCH in MU.
    (* [comment removed for export] *)
    assert (FR : forall b, In b ([(p8, va, 8); (p6, q, 96); (p5, v, 79); (p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)] ++ FBB) ->
                 ~ In (blk_id b) (map blk_id LB)).
    { intros b Hb. eapply (mine_fresh _ LB b); [| exact Hb]. rewrite map_app, map_app. cbn [map blk_id fst snd app]. exact NDm. }
    (* [comment removed for export] *)
    assert (STEPH1 : forall ma mb hi, hi <= P -> munch [(lo, hi); (q + 32, q + 72); (schedb, schedb + 272)] ma mb -> wmono usegs ma mb ->
              hs_RHEAP H s' LBc ma -> hs_rauxv_ok H ma B -> xpres LB (P + 512) XH_X m0 ma -> HStat FT ma -> rw_cells usegs ma RERRNO [C4 errv] ->
              hs_RHEAP H s' LBc mb /\ hs_rauxv_ok H mb B /\ xpres LB (P + 512) XH_X m0 mb /\ HStat FT mb /\ rw_cells usegs mb RERRNO [C4 errv]).
    { intros ma mb hi HI MUx WMx HPx AUXx XPx HSx ERRx.
      pose proof (hh_blocks H HH _ _ _ _ HP IN6) as (_ & _ & _ & _ & Q5). cbn in Q5.
      pose proof (hh_blocks H HH _ _ _ _ HP IN4) as (_ & _ & _ & _ & S5). cbn in S5.
      split. { eapply (hh_RHEAP_frame H HH); [exact HPx| exact MUx| exact WMx|].
        constructor; [left; cbn; lia|]. constructor; [right; right; exists (p6, q, 96); split; [exact IN6| cbn; lia]|].
        constructor; [right; right; exists (p4, schedb, 287); split; [exact IN4| cbn; lia]| constructor]. }
      split. { eapply (hh_rauxv_frame H HH); [exact AUXx| exact MUx| exact WMx|]. unfold RAUXV_CELL in *.
        constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      split. { eapply (xp_lift_munch_gen H HH s' LBc LB ma); [exact XPx| exact MUx| exact WMx| lia| exact HPx| exact SUB|].
        constructor; [cbn; intros a Ha; left; left; lia|].
        constructor; [cbn; intros a Ha; left; right; exists (p6, q, 96); split; [exact IN6|]; split; [apply FR; cbn; qtauto| cbn; lia]|].
        constructor; [cbn; intros a Ha; left; right; exists (p4, schedb, 287); split; [exact IN4|]; split; [apply FR; cbn; qtauto| cbn; lia]| constructor]. }
      split. { eapply HStat_munch_keep; [exact FT_local| exact HSx| exact MUx|]. unfold XH_LO, XH_HI.
        constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      eapply (rw_cells_transport usegs _ ma mb); [exact ERRx| exact MUx| exact WMx| unfold RERRNO in *; cbn; lia]. }
    destruct (STEPH1 _ _ P ltac:(lia) MU WM HP AUX XP HS ERR) as (HP1 & AUX1 & XP1 & HS1 & ERR1). clear ERR.
    mu_frame MU WM P. eapply (stk_transport_disjoint usegs _ m m1) in STK8; [| exact MU| exact WM| cbn; lia].
    eapply (Registry_transport _ _ m m1) in REG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN6 ltac:(congruence)) as X1. pose proof (OFF _ _ IN2 IN4 ltac:(congruence)) as X2. unfold NEWSZ_REG. cbn in X1, X2 |- *.
        lia. }
    eapply (ConfigSvc_transport _ _ m m1) in CFG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN3 IN6 ltac:(congruence)). pose proof (OFF _ _ IN3 IN4 ltac:(congruence)). unfold NEWSZ_CFG. cbn in *. lia. }
    eapply (AllocImpl_transport _ _ m m1) in AI; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN1 IN6 ltac:(congruence)). pose proof (OFF _ _ IN1 IN4 ltac:(congruence)). unfold SZ_ALLOCIMPL. cbn in *. lia. }
    clear MU WM MI ST AUX XP HS HP SSVC IMPL SCH.
    (* [comment removed for export] *)
    eapply (hh_evt_then H HH); [exact KREL| |].
    { eapply fzH1b; [apply H1HY; try fast_assumption; eapply XStatics_xpres0; [exact XI| exact XP1]| exact ST1| unfold FZ_H1_STACK, SSVC_SHUTDOWN_STACK, MTX_UNLOCK_STACK; lia]. }
    intros ms2 PO. unfold fzH1b_post in PO.
    destruct PO as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m2 & -> & MU & WM & MI2 & ST2 & SSVC2 & IMPL2 & SCH2).
    unfold SZ_SCH in MU.
    destruct (STEPH1 _ _ (P + -48) ltac:(lia) MU WM HP1 AUX1 XP1 HS1 ERR1) as (HP2 & AUX2 & XP2 & HS2 & ERR2). clear ERR1.
    mu_frame MU WM P. eapply (stk_transport_disjoint usegs _ m1 m2) in STK8; [| exact MU| exact WM| cbn; lia].
    eapply (Registry_transport _ _ m1 m2) in REG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN6 ltac:(congruence)). pose proof (OFF _ _ IN2 IN4 ltac:(congruence)). unfold NEWSZ_REG. cbn in *. lia. }
    eapply (ConfigSvc_transport _ _ m1 m2) in CFG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN3 IN6 ltac:(congruence)). pose proof (OFF _ _ IN3 IN4 ltac:(congruence)). unfold NEWSZ_CFG. cbn in *. lia. }
    eapply (AllocImpl_transport _ _ m1 m2) in AI; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN1 IN6 ltac:(congruence)). pose proof (OFF _ _ IN1 IN4 ltac:(congruence)). unfold SZ_ALLOCIMPL. cbn in *. lia. }
    clear MU WM MI1 ST1 AUX1 XP1 HS1 HP1 SSVC1 IMPL1 SCH1 STEPH1 H1HY.
    (* [comment removed for export] *)
    pose proof (destroy_alloc_ssvc_spec H HH) as DS. unfold destroy_alloc_ssvc_stmt in DS.
    eapply (hh_seq H HH).
    { eapply DS with (v := v) (implb := q) (ioc := P + 392) (allocb := allocb) (regb := regb) (schedb := schedb) (vb := va) (lo := lo) (B := B)
                     (LB := LBc) (s := s') (S := ssvc_hdr (P + 392) schedb) (ist := []);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI2 | exact ST2 | exact KREL | rewrite EA; exact ERR2 | exact HP2 | exact AUX2 | exact AI | exact SSVC2 | exact IMPL2 | exact IOC | exact AL392
                     | eapply XStatics_xpres0; [exact XI| exact XP2]
                     | unfold DALL_SSVC_STACK, DOBJ_SSVC_STACK, SHCOUNT_DTOR_IMPL_STACK, RFREE_STACK; lia ]. }
    intros [ms3 mo3] PO. unfold destroy_alloc_ssvc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m3 & s3' & pv & pi & pq
                    & -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & INV & INI & INQ & HP3 & AI3 & XS3 & IOC3 & XPC).
    rewrite (unsigned_lit (P + -48)) in ST3, XPC by lia. rewrite EA in ERR3.
    apply (hh_mpres_trans H HH _ _ _ MP) in MP3. clear MP.
    unfold NEWSZ_SSVC, SZ_SPCI_IMPL in INV, INI, INQ, XPC.
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP2 IN5 ltac:(lia) INV) in HP3, AI3.
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP2 IN6 ltac:(lia) INI) in HP3, AI3.
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP2 IN8 ltac:(lia) INQ) in HP3, AI3.
    clear INV INI INQ pv pi pq DS.
    set (L3 := hs_lb_remove H p5 (hs_lb_remove H p6 (hs_lb_remove H p8 LBc))) in *.
    assert (PN3 : Permutation L3 ([(p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)] ++ FBB ++ LB) /\ List.NoDup (map blk_id L3)).
    { destruct (bperm_free H HH _ _ _ NDc PERM) as [PE1 ND1]. cbn [blk_id fst snd] in PE1, ND1.
      destruct (bperm_free H HH _ _ _ ND1 PE1) as [PE2 ND2]. cbn [blk_id fst snd] in PE2, ND2.
      destruct (bperm_free H HH _ _ _ ND2 PE2) as [PE3 ND3]. cbn [blk_id fst snd] in PE3, ND3.
      subst L3. unfold SZ_SPCI_IMPL, NEWSZ_SSVC, NEWSZ_SCH, NEWSZ_CFG, NEWSZ_REG, SZ_ALLOCIMPL in *. split; [exact PE3| exact ND3]. }
    destruct PN3 as [PERM3 ND3].
    assert (SUB3 : forall b, In b LB -> In b L3).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM3|]. cbn. do 4 right. apply in_or_app. right. exact Hb. }
    assert (IN4' : In (p4, schedb, 287) L3) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3|]; cbn; qtauto).
    assert (IN3' : In (p3, cfgb, 71) L3) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3|]; cbn; qtauto).
    assert (IN2' : In (p2, regb, 79) L3) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3|]; cbn; qtauto).
    assert (IN1' : In (p1, allocb, 16) L3) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3|]; cbn; qtauto).
    (* [comment removed for export] *)
    xp_frame XPC P.
    eapply (xpres_stk _ _ _ m2 m3) in STK8; [| exact XPC| lia| repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    assert (XP3 : xpres LB (P + 512) XH_X m0 m3).
    { eapply (xp_lift_gen H HH s' LBc LB m2); [exact XP2| exact XPC| lia| lia| exact HP2| exact SUB|].
      intros a [R|[R|[R|[]]]]; cbn in R; left; right.
      - exists (p5, v, 79). split; [exact IN5|]. split; [apply FR; cbn; qtauto| cbn; lia].
      - exists (p6, q, 96). split; [exact IN6|]. split; [apply FR; cbn; qtauto| cbn; lia].
      - exists (p8, va, 8). split; [exact IN8|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS3 : HStat FT m3).
    { eapply (HStat_xpres_keep FT _ (P + -48) _); [exact FT_local| exact HS2| exact XPC|].
      pose proof (hh_blocks H HH _ _ _ _ HP2 IN5) as (_ & _ & _ & _ & V5). pose proof (hh_blocks H HH _ _ _ _ HP2 IN6) as (_ & _ & _ & _ & Q5).
      pose proof (hh_blocks H HH _ _ _ _ HP2 IN8) as (_ & _ & _ & _ & E5). cbn in V5, Q5, E5.
      intros a Ha [R|[R|[R|[]]]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    eapply (Scheduler_xpres _ _ _ m2 m3) in SCH2; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN4 IN5 ltac:(congruence)). pose proof (OFF _ _ IN4 IN6 ltac:(congruence)). pose proof (OFF _ _ IN4 IN8 ltac:(congruence)).
        unfold NEWSZ_SCH. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (Scheduler_reix H HH _ _ L3) in SCH2; [| exact HP2| exact IN4| exact IN4'].
    eapply (ConfigSvc_xpres _ _ _ m2 m3) in CFG; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN3 IN5 ltac:(congruence)). pose proof (OFF _ _ IN3 IN6 ltac:(congruence)). pose proof (OFF _ _ IN3 IN8 ltac:(congruence)).
        unfold NEWSZ_CFG. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (ConfigSvc_reix H HH _ _ L3) in CFG; [| exact HP2| exact IN3| exact IN3'].
    eapply (Registry_xpres _ _ _ m2 m3) in REG; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN2 IN5 ltac:(congruence)). pose proof (OFF _ _ IN2 IN6 ltac:(congruence)). pose proof (OFF _ _ IN2 IN8 ltac:(congruence)).
        unfold NEWSZ_REG. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (Registry_reix H HH _ _ L3) in REG; [| exact HP2| exact IN2| exact IN2'].
    clear MI2 ST2 AUX2 HP2 XP2 HS2 SSVC2 IMPL2 AI IOC ERR2 XPC SUB IN8 IN6 IN5 IN4 IN3 IN2 IN1 NDc PERM OFF.
    rename IN4' into IN4. rename IN3' into IN3. rename IN2' into IN2. rename IN1' into IN1.
    assert (OFF : forall b b', In b L3 -> In b' L3 -> b <> b' -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb' NE. exact (blocks_neq_disjoint H HH _ _ _ _ _ HP3 Hb Hb' NE). }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_DSV)) with (Z_to_bv 64 P_FZ_RET_DSV)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_DSV; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL3| |].
    { eapply fzH2; [exact REG| unfold NEWSZ_REG; lia| exact SCH2| lia| unfold NEWSZ_SCH; lia| | exact S8| lia| lia| exact MI3].
      pose proof (OFF _ _ IN2 IN4 ltac:(congruence)). unfold NEWSZ_REG, NEWSZ_SCH. cbn in *. lia. }
    intros ms4 PO. unfold fzH2_post in PO.
    destruct PO as (w0 & w1 & w2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & w3 & w4 & w5 & w6 & m4 & -> & MU & WM & MI4 & REG4). clear REG.
    eapply (rw_cells_transport usegs _ m3 m4) in ERR3; [| exact MU| exact WM|].
    2:{ pose proof (hh_blocks H HH _ _ _ _ HP3 IN2) as (_ & _ & _ & _ & R5). cbn in R5. unfold RERRNO in *. cbn. lia. }
    mu_frame MU WM P.
    eapply (stk_transport_disjoint usegs _ m3 m4) in ST3; [| exact MU| exact WM| cbn; lia].
    eapply (stk_transport_disjoint usegs _ m3 m4) in STK8; [| exact MU| exact WM| cbn; lia].
    eapply (Scheduler_transport _ _ m3 m4) in SCH2; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN4 ltac:(congruence)). unfold NEWSZ_SCH. cbn in *. lia. }
    eapply (ConfigSvc_transport _ _ m3 m4) in CFG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN3 ltac:(congruence)). unfold NEWSZ_CFG. cbn in *. lia. }
    eapply (AllocImpl_transport _ _ m3 m4) in AI3; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN1 ltac:(congruence)). unfold SZ_ALLOCIMPL. cbn in *. lia. }
    assert (HP4 : hs_RHEAP H s3' L3 m4).
    { eapply (hh_RHEAP_frame H HH); [exact HP3| exact MU| exact WM|].
      constructor; [right; right; exists (p2, regb, 79); split; [exact IN2| cbn; lia]| constructor]. }
    assert (AUX4 : hs_rauxv_ok H m4 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX3| exact MU| exact WM|]. unfold RAUXV_CELL in *.
      pose proof (hh_blocks H HH _ _ _ _ HP3 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia| constructor]. }
    assert (XP4 : xpres LB (P + 512) XH_X m0 m4).
    { eapply (xp_lift_munch_gen H HH s3' L3 LB m3); [exact XP3| exact MU| exact WM| lia| exact HP3| exact SUB3|].
      constructor; [| constructor]. cbn. intros a Ha. left. right. exists (p2, regb, 79). split; [exact IN2|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS4 : HStat FT m4).
    { eapply HStat_munch_keep; [exact FT_local| exact HS3| exact MU|]. unfold XH_LO, XH_HI.
      pose proof (hh_blocks H HH _ _ _ _ HP3 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia| constructor]. }
    clear MU WM MI3 AUX3 XP3 HS3 HP3.
    (* [comment removed for export] *)
    pose proof (destroy_alloc_sched_spec H HH) as DS. unfold destroy_alloc_sched_stmt in DS.
    eapply (hh_seq H HH).
    { eapply DS with (sb := schedb) (ioc := P + 392) (allocb := allocb) (regb := regb) (schedb := schedb) (lo := lo) (B := B)
                     (LB := L3) (s := s3') (S := mkSCH (sched_hdr (P + 392) cfgb) 0 0 1);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI4 | exact ST3 | exact KREL3 | rewrite EA; exact ERR3 | exact HP4 | exact AUX4 | exact AI3 | exact SCH2 | exact AL392 | fast_assumption
                     | eapply XStatics_xpres0; [exact XI| exact XP4]
                     | unfold DALL_STACK, DOBJ_STACK, ATD_STACK, RFREE_STACK; lia ]. }
    intros [ms5 mo5] PO. unfold destroy_alloc_sched_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0' & z1' & z2' & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3' & z4' & z5' & z6' & m5 & s5' & px
                    & -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5 & INX & HP5 & AI5 & XS5 & IOC5 & XPC).
    rewrite (unsigned_lit (P + -48)) in ST5, XPC by lia. rewrite EA in ERR5.
    apply (hh_mpres_trans H HH _ _ _ MP3) in MP5. clear MP3.
    unfold NEWSZ_SCH in INX, XPC. rewrite (in_pin H HH _ _ _ _ _ _ _ HP4 IN4 ltac:(lia) INX) in HP5, AI5. clear INX px DS.
    set (L5 := hs_lb_remove H p4 L3) in *.
    destruct (bperm_free H HH _ _ _ ND3 PERM3) as [PERM5 ND5]. cbn [blk_id fst snd] in PERM5, ND5. fold L5 in PERM5, ND5.
    assert (SUB5 : forall b, In b LB -> In b L5).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM5|]. cbn. do 3 right. apply in_or_app. right. exact Hb. }
    assert (IN3' : In (p3, cfgb, 71) L5) by (eapply Permutation_in; [apply Permutation_sym; exact PERM5|]; cbn; qtauto).
    assert (IN2' : In (p2, regb, 79) L5) by (eapply Permutation_in; [apply Permutation_sym; exact PERM5|]; cbn; qtauto).
    assert (IN1' : In (p1, allocb, 16) L5) by (eapply Permutation_in; [apply Permutation_sym; exact PERM5|]; cbn; qtauto).
    xp_frame XPC P.
    eapply (xpres_stk _ _ _ m4 m5) in STK8; [| exact XPC| lia| repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    assert (XP5 : xpres LB (P + 512) XH_X m0 m5).
    { eapply (xp_lift_gen H HH s3' L3 LB m4); [exact XP4| exact XPC| lia| lia| exact HP4| exact SUB3|].
      intros a [R|[]]; cbn in R; left; right. exists (p4, schedb, 287). split; [exact IN4|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS5 : HStat FT m5).
    { eapply (HStat_xpres_keep FT _ (P + -48) _); [exact FT_local| exact HS4| exact XPC|].
      pose proof (hh_blocks H HH _ _ _ _ HP4 IN4) as (_ & _ & _ & _ & S5). cbn in S5. intros a Ha [R|[]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    eapply (ConfigSvc_xpres _ _ _ m4 m5) in CFG; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN3 IN4 ltac:(congruence)). unfold NEWSZ_CFG. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (ConfigSvc_reix H HH _ _ L5) in CFG; [| exact HP4| exact IN3| exact IN3'].
    eapply (Registry_xpres _ _ _ m4 m5) in REG4; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN2 IN4 ltac:(congruence)). unfold NEWSZ_REG. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (Registry_reix H HH _ _ L5) in REG4; [| exact HP4| exact IN2| exact IN2'].
    clear MI4 ST3 AUX4 HP4 XP4 HS4 SCH2 AI3 IOC3 ERR3 XPC SUB3 IN4 IN3 IN2 IN1 ND3 PERM3 OFF.
    rename IN3' into IN3. rename IN2' into IN2. rename IN1' into IN1.
    assert (OFF : forall b b', In b L5 -> In b' L5 -> b <> b' -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb' NE. exact (blocks_neq_disjoint H HH _ _ _ _ _ HP5 Hb Hb' NE). }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_DSV)) with (Z_to_bv 64 P_FZ_RET_DSV)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_DSV; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL5| |].
    { pose proof (hh_blocks H HH _ _ _ _ HP5 IN3) as (C1 & _ & _ & C4 & _). cbn in C1, C4.
      eapply fzH3; [exact REG4| unfold NEWSZ_REG; lia| exact CFG| lia| unfold NEWSZ_CFG; lia| | exact C8'| lia| lia| exact MI5].
      pose proof (OFF _ _ IN2 IN3 ltac:(congruence)). unfold NEWSZ_REG, NEWSZ_CFG. cbn in *. lia. }
    intros ms6 PO. unfold fzH3_post in PO.
    destruct PO as (w0' & w1' & w2' & f1' & f2' & f3' & f4' & f5' & f6' & f7' & w3' & w4' & w5' & w6' & m6 & -> & MU & WM & MI6 & REG6). clear REG4.
    eapply (rw_cells_transport usegs _ m5 m6) in ERR5; [| exact MU| exact WM|].
    2:{ pose proof (hh_blocks H HH _ _ _ _ HP5 IN2) as (_ & _ & _ & _ & R5). cbn in R5. unfold RERRNO in *. cbn. lia. }
    mu_frame MU WM P.
    eapply (stk_transport_disjoint usegs _ m5 m6) in ST5; [| exact MU| exact WM| cbn; lia].
    eapply (stk_transport_disjoint usegs _ m5 m6) in STK8; [| exact MU| exact WM| cbn; lia].
    eapply (ConfigSvc_transport _ _ m5 m6) in CFG; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN3 ltac:(congruence)). unfold NEWSZ_CFG. cbn in *. lia. }
    eapply (AllocImpl_transport _ _ m5 m6) in AI5; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN1 ltac:(congruence)). unfold SZ_ALLOCIMPL. cbn in *. lia. }
    assert (HP6 : hs_RHEAP H s5' L5 m6).
    { eapply (hh_RHEAP_frame H HH); [exact HP5| exact MU| exact WM|].
      constructor; [right; right; exists (p2, regb, 79); split; [exact IN2| cbn; lia]| constructor]. }
    assert (AUX6 : hs_rauxv_ok H m6 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX5| exact MU| exact WM|]. unfold RAUXV_CELL in *.
      pose proof (hh_blocks H HH _ _ _ _ HP5 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia| constructor]. }
    assert (XP6 : xpres LB (P + 512) XH_X m0 m6).
    { eapply (xp_lift_munch_gen H HH s5' L5 LB m5); [exact XP5| exact MU| exact WM| lia| exact HP5| exact SUB5|].
      constructor; [| constructor]. cbn. intros a Ha. left. right. exists (p2, regb, 79). split; [exact IN2|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS6 : HStat FT m6).
    { eapply HStat_munch_keep; [exact FT_local| exact HS5| exact MU|]. unfold XH_LO, XH_HI.
      pose proof (hh_blocks H HH _ _ _ _ HP5 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia| constructor]. }
    clear MU WM MI5 AUX5 XP5 HS5 HP5.
    (* [comment removed for export] *)
    pose proof (destroy_alloc_config_spec H HH) as DS. unfold destroy_alloc_config_stmt in DS.
    eapply (hh_seq H HH).
    { eapply DS with (c := cfgb) (ioc := P + 392) (allocb := allocb) (regb := regb) (schedb := schedb) (lo := lo) (B := B)
                     (LB := L5) (s := s5') (S := cfg_hdr (P + 392));
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI6 | exact ST5 | exact KREL5 | rewrite EA; exact ERR5 | exact HP6 | exact AUX6 | exact AI5 | exact CFG | exact AL392 | fast_assumption
                     | eapply XStatics_xpres0; [exact XI| exact XP6]
                     | unfold DALL_STACK, DOBJ_STACK, ATD_STACK, RFREE_STACK; lia ]. }
    intros [ms7 mo7] PO. unfold destroy_alloc_config_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0'' & z1'' & z2'' & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3'' & z4'' & z5'' & z6'' & m7 & s7' & px
                    & -> & KREL7 & MP7 & MI7 & ST7 & ERR7 & AUX7 & INX & HP7 & AI7 & XS7 & IOC7 & XPC).
    rewrite (unsigned_lit (P + -48)) in ST7, XPC by lia. rewrite EA in ERR7.
    apply (hh_mpres_trans H HH _ _ _ MP5) in MP7. clear MP5.
    unfold NEWSZ_CFG in INX, XPC. rewrite (in_pin H HH _ _ _ _ _ _ _ HP6 IN3 ltac:(lia) INX) in HP7, AI7. clear INX px DS.
    set (L7 := hs_lb_remove H p3 L5) in *.
    destruct (bperm_free H HH _ _ _ ND5 PERM5) as [PERM7 ND7]. cbn [blk_id fst snd] in PERM7, ND7. fold L7 in PERM7, ND7.
    assert (SUB7 : forall b, In b LB -> In b L7).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM7|]. cbn. do 2 right. apply in_or_app. right. exact Hb. }
    assert (IN2' : In (p2, regb, 79) L7) by (eapply Permutation_in; [apply Permutation_sym; exact PERM7|]; cbn; qtauto).
    assert (IN1' : In (p1, allocb, 16) L7) by (eapply Permutation_in; [apply Permutation_sym; exact PERM7|]; cbn; qtauto).
    xp_frame XPC P.
    eapply (xpres_stk _ _ _ m6 m7) in STK8; [| exact XPC| lia| repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    assert (XP7 : xpres LB (P + 512) XH_X m0 m7).
    { eapply (xp_lift_gen H HH s5' L5 LB m6); [exact XP6| exact XPC| lia| lia| exact HP6| exact SUB5|].
      intros a [R|[]]; cbn in R; left; right. exists (p3, cfgb, 71). split; [exact IN3|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS7 : HStat FT m7).
    { eapply (HStat_xpres_keep FT _ (P + -48) _); [exact FT_local| exact HS6| exact XPC|].
      pose proof (hh_blocks H HH _ _ _ _ HP6 IN3) as (_ & _ & _ & _ & C5). cbn in C5. intros a Ha [R|[]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    eapply (Registry_xpres _ _ _ m6 m7) in REG6; [| exact XPC|].
    2:{ pose proof (OFF _ _ IN2 IN3 ltac:(congruence)). unfold NEWSZ_REG. cbn in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (Registry_reix H HH _ _ L7) in REG6; [| exact HP6| exact IN2| exact IN2'].
    clear MI6 ST5 AUX6 HP6 XP6 HS6 CFG AI5 IOC5 ERR5 XPC SUB5 IN3 IN2 IN1 ND5 PERM5 OFF.
    rename IN2' into IN2. rename IN1' into IN1.
    assert (OFF : forall b b', In b L7 -> In b' L7 -> b <> b' -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb' NE. exact (blocks_neq_disjoint H HH _ _ _ _ _ HP7 Hb Hb' NE). }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_DSV)) with (Z_to_bv 64 P_FZ_RET_DSV)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_DSV; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL7| |].
    { eapply fzH4; [exact REG6| unfold NEWSZ_REG; lia| lia| exact R8| exact IOC7| exact FRX| exact ST7| lia| lia| lia| exact MI7]. }
    intros ms8 PO. unfold fzH4_post in PO.
    destruct PO as (v0 & v1 & v2 & k3 & k4 & k5 & k6 & k7 & v3 & v4 & v5 & v6 & m8 & j0' & -> & MU & WM & MI8 & ST8 & REG8 & FRX8). clear REG6 FRX ST7.
    eapply (stk_transport_disjoint usegs _ m7 m8) in STK8; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in ERR7; [| exact MU| exact WM|].
    2:{ pose proof (hh_blocks H HH _ _ _ _ HP7 IN2) as (_ & _ & _ & _ & R5). cbn in R5. unfold RERRNO in *. cbn. lia. }
    eapply (rw_cells_transport usegs _ m7 m8) in IOC7; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in FRP; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in FRS; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in FBC; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in FRE; [| exact MU| exact WM| cbn; lia].
    eapply (rw_cells_transport usegs _ m7 m8) in SAV; [| exact MU| exact WM| cbn; lia].
    eapply (AllocImpl_transport _ _ m7 m8) in AI7; [| exact MU| exact WM|].
    2:{ pose proof (OFF _ _ IN2 IN1 ltac:(congruence)). unfold SZ_ALLOCIMPL. cbn in *. lia. }
    assert (HP8 : hs_RHEAP H s7' L7 m8).
    { eapply (hh_RHEAP_frame H HH); [exact HP7| exact MU| exact WM|].
      constructor; [right; right; exists (p2, regb, 79); split; [exact IN2| cbn; lia]|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX8 : hs_rauxv_ok H m8 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX7| exact MU| exact WM|]. unfold RAUXV_CELL in *.
      pose proof (hh_blocks H HH _ _ _ _ HP7 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (XP8 : xpres LB (P + 512) XH_X m0 m8).
    { eapply (xp_lift_munch_gen H HH s7' L7 LB m7); [exact XP7| exact MU| exact WM| lia| exact HP7| exact SUB7|].
      constructor; [cbn; intros a Ha; left; right; exists (p2, regb, 79); split; [exact IN2|]; split; [apply FR; cbn; qtauto| cbn; lia]|].
      constructor; [cbn; intros a Ha; left; left; lia| constructor]. }
    assert (HS8 : HStat FT m8).
    { eapply HStat_munch_keep; [exact FT_local| exact HS7| exact MU|]. unfold XH_LO, XH_HI.
      pose proof (hh_blocks H HH _ _ _ _ HP7 IN2) as (_ & _ & _ & _ & R5). cbn in R5. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    clear MU WM MI7 AUX7 XP7 HS7 HP7.
    (* [comment removed for export] *)
    pose proof (atd_spec H HH P_UB_ATD_REG ltac:(unfold atd_entry_ok; qtauto)) as DS. unfold atd_stmt in DS.
    destruct (Registry_open _ _ _ _ _ _ REG8) as (pr & rj0 & rj7 & INR & RR0 & RPMC & RLK & RALM & RROF & RRCK).
    unfold NEWSZ_REG in INR. rewrite (in_pin H HH _ _ _ _ _ _ _ HP8 IN2 ltac:(lia) INR) in INR.
    pose proof AI7 as (pa & ja & INA & CA).
    eapply (hh_seq H HH).
    { eapply DS with (AT := P + -40) (pobj := regb) (allocb := allocb) (lo := lo) (B := B) (LB := L7) (s := s7') (p := p2) (j7 := rj7);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI8 | exact ST8 | exact KREL7 | rewrite EA; exact ERR7 | exact HP8 | exact AUX8 | exact A8 | fast_assumption
                     | exact IN2 | exact RRCK | exact (ro_cell0 _ _ _ _ CA)
                     | eapply XStatics_xpres0; [exact XI| exact XP8]
                     | unfold ATD_STACK, RFREE_STACK; lia
                     | unfold P_FZ_RET_ATD; cbn; lia ].
      unfold ExcFrame in FRX8. pose proof (rw_cells_ro_cell _ _ _ _ 8 _ FRX8 eq_refl) as K. cbn [cells_size csize Nat.add Z.of_nat take drop] in K.
      replace (P + -48 + 8) with (P + -40) in K by lia. exact K. }
    intros [ms9 mo9] PO. unfold atd_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (n0 & n1 & n2 & o0 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & n3 & n4 & n5 & n6 & m9 & s9'
                    & -> & KREL9 & MP9 & MI9 & ST9 & ERR9 & AUX9 & HP9 & HPRES).
    rewrite (unsigned_lit (P + -48)) in ST9, HPRES by lia. rewrite EA in ERR9.
    apply (hh_mpres_trans H HH _ _ _ MP7) in MP9. clear MP7 DS RR0 RPMC RLK RALM RROF RRCK REG8.
    set (L9 := hs_lb_remove H p2 L7) in *.
    destruct (bperm_free H HH _ _ _ ND7 PERM7) as [PERM9 ND9]. cbn [blk_id fst snd] in PERM9, ND9. fold L9 in PERM9, ND9.
    assert (SUB9 : forall b, In b LB -> In b L9).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM9|]. cbn. right. apply in_or_app. right. exact Hb. }
    assert (IN1' : In (p1, allocb, 16) L9) by (eapply Permutation_in; [apply Permutation_sym; exact PERM9|]; cbn; qtauto).
    hp_frame HPRES P.
    eapply (xpres_stk _ _ _ m8 m9) in STK8; [| apply xpres_of_heap_pres; exact HPRES| lia| apply Forall_nil].
    assert (AI9 : AllocImpl L9 m9 allocb).
    { exists pa, ja. unfold SZ_ALLOCIMPL in INA |- *. rewrite (in_pin H HH _ _ _ _ _ _ _ HP8 IN1 ltac:(lia) INA). split; [exact IN1'|].
      eapply rheap_pres_rw_cells; [exact HPRES| exact CA|]. right; right. exists (p1, allocb, 16). split; [exact IN1'| cbn; lia]. }
    assert (XP9 : xpres LB (P + 512) XH_X m0 m9).
    { eapply (xp_lift_free_gen H HH s7' L7 LB m8); [exact XP8| exact HP8| exact SUB7| exact IN2| | exact HPRES| lia| lia].
      apply (FR (p2, regb, 79)). cbn. qtauto. }
    assert (HS9 : HStat FT m9).
    { eapply (HStat_xpres_keep FT L7 (P + -48) [(regb, regb + 79)]); [exact FT_local| exact HS8| |].
      - eapply (xpres_free H HH); [exact HP8| exact IN2| exact HPRES| intros a Ha; cbn; left; exact Ha].
      - pose proof (hh_blocks H HH _ _ _ _ HP8 IN2) as (_ & _ & _ & _ & R5). cbn in R5. intros a Ha [R|[]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    clear MI8 ST8 AUX8 XP8 HS8 AI7 ERR7 SUB7 IN2 ND7 PERM7 OFF INA CA INR HPRES HP8 pa ja pr rj0 rj7.
    rename IN1' into IN1x.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_ATD)) with (Z_to_bv 64 P_FZ_RET_ATD)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_ATD; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL9| |].
    { eapply fzH5; [exact IOC7| exact AI9| eapply XStatics_xpres0; [exact XI| exact XP9]| lia| exact A8| unfold SZ_ALLOCIMPL; lia| lia| lia| exact MI9]. }
    intros ms10 PO. unfold fzH5_post in PO.
    destruct PO as (u0 & u1 & u2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & u3 & u4 & u5 & u6 & -> & _ & _ & _).
    (* [comment removed for export] *)
    pose proof (allocimpl_destroy_spec H HH) as DS. unfold allocimpl_destroy_stmt in DS.
    pose proof AI9 as (pa & ja & INA & CA). unfold SZ_ALLOCIMPL in INA.
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP9 IN1x ltac:(lia) INA) in INA.
    eapply (hh_seq H HH).
    { eapply DS with (a := allocb) (p := p1) (lo := lo) (B := B) (LB := L9) (s := s9');
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI9 | exact ST9 | exact KREL9 | rewrite EA; exact ERR9 | exact HP9 | exact AUX9 | exact INA | exact CA | fast_assumption
                     | eapply XStatics_xpres0; [exact XI| exact XP9]
                     | unfold ALLOCIMPL_DESTROY_STACK, RFREE_STACK; lia ]. }
    intros [ms11 mo11] PO. unfold allocimpl_destroy_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (n0' & n1' & n2' & o0' & o1' & o2' & o3' & o4' & o5' & o6' & o7' & n3' & n4' & n5' & n6' & m11 & s11'
                    & -> & KREL11 & MP11 & MI11 & ST11 & ERR11 & AUX11 & HP11 & XPC).
    rewrite (unsigned_lit (P + -48)) in ST11, XPC by lia. rewrite EA in ERR11.
    apply (hh_mpres_trans H HH _ _ _ MP9) in MP11. clear MP9.
    unfold SZ_ALLOCIMPL in XPC.
    set (L11 := hs_lb_remove H p1 L9) in *.
    destruct (bperm_free H HH _ _ _ ND9 PERM9) as [PERM11 ND11]. cbn [blk_id fst snd] in PERM11, ND11. fold L11 in PERM11, ND11.
    xp_frame XPC P.
    eapply (xpres_stk _ _ _ m9 m11) in STK8; [| exact XPC| lia| repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    assert (XP11 : xpres LB (P + 512) XH_X m0 m11).
    { eapply (xp_lift_gen H HH s9' L9 LB m9); [exact XP9| exact XPC| lia| lia| exact HP9| exact SUB9|].
      intros a [R|[]]; cbn in R; left; right. exists (p1, allocb, 16). split; [exact IN1x|]. split; [apply FR; cbn; qtauto| cbn; lia]. }
    assert (HS11 : HStat FT m11).
    { eapply (HStat_xpres_keep FT _ (P + -48) _); [exact FT_local| exact HS9| exact XPC|].
      pose proof (hh_blocks H HH _ _ _ _ HP9 IN1x) as (_ & _ & _ & _ & A5). cbn in A5. intros a Ha [R|[]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    clear MI9 ST9 AUX9 HP9 XP9 HS9 AI9 ERR9 XPC SUB9 IN1x ND9 PERM9 DS INA CA.
    (* [comment removed for export] *)
    assert (STM : stk usegs m11 P (P + 416)).
    { pose proof (stk_of_rw_cells usegs _ _ _ FRP) as K0. cbn [cells_size] in K0. rewrite SZ8 in K0. replace (P + Z.of_nat (8 + 0)) with (P + 8) in K0 by lia.
      eapply stk_merge; [exact K0| | lia].
      eapply stk_merge; [exact STK8| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ FRS) as K1. rewrite SZS in K1. replace (P + 360 + Z.of_nat 32) with (P + 392) in K1 by lia.
      eapply stk_merge; [exact K1| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ IOC7) as K2. cbn [cells_size csize Nat.add IoCtxCells length] in K2.
      replace (P + 392 + 24) with (P + 416) in K2 by lia. exact K2. }
    clear FRP STK8 FRS IOC7.
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_ADS)) with (Z_to_bv 64 P_FZ_RET_ADS)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_ADS; lia| reflexivity]).
    destruct FBI as [[-> ->]|(pf & -> & FB1 & FB2 & FB3)].
    - (* [comment removed for export] *)
      cbn [app] in PERM11.
      eapply (hh_evt H HH); [exact KREL11| |].
      { eapply fzI0; [exact FRX8| exact ST11| exact STM| exact FBC| exact FRE| exact SZE| exact SAV| lia| lia| lia| exact RAE| exact MI11]. }
      intros ms12 PO. unfold fz_ret_post in PO. unfold fz_final. cbn [cfg_ms cfg_model].
      destruct PO as (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m12 & -> & MU & WM & MI12 & ST12).
      rewrite (unsigned_lit (P + 512)) in ST12 by lia.
      do 14 eexists. exists m12, errv, s11', L11.
      split; [reflexivity|]. split; [exact KREL11|]. split; [exact MP11|]. split; [exact MI12|]. split; [exact ST12|].
      split. { rewrite EA. eapply (rw_cells_transport usegs _ m11 m12); [exact ERR11| exact MU| exact WM| exact I]. }
      split. { eapply (hh_rauxv_frame H HH); [exact AUX11| exact MU| exact WM| constructor]. }
      split. { eapply (hh_RHEAP_frame H HH); [exact HP11| exact MU| exact WM| constructor]. }
      split; [exact PERM11|].
      split. { eapply HStat_munch_keep; [exact FT_local| exact HS11| exact MU| constructor]. }
      eapply xpres_trans; [exact XP11|]. eapply xpres_of_munch_gen; [exact MU| exact WM| intros; exact I].
    - (* [comment removed for export] *)
      assert (INF : In (pf, fb_begin FB, fb_cap FB) L11) by (eapply Permutation_in; [apply Permutation_sym; exact PERM11| left; reflexivity]).
      eapply (hh_evt_then H HH); [exact KREL11| |].
      { eapply fzI1; [exact FRX8| exact FBC| exact FB1| exact FB2| exact FB3| lia| lia| exact MI11]. }
      intros ms12 PO. unfold fzI1_post in PO. destruct PO as (-> & _ & _ & _).
      (* [comment removed for export] *)
      pose proof (stk_release usegs _ _ _ _ ST11 FRX8 ltac:(lia)) as STP. cbn [cells_size csize Nat.add ExcFrame length] in STP.
      replace (P + -48 + 48) with P in STP by lia. clear ST11 FRX8.
      pose proof (stk_merge usegs _ _ _ _ STP STM ltac:(lia)) as ST416.
      pose proof (hh_opdel2 H HH) as OD. unfold opdel2_sr_stmt, free_sr_stmt_at in OD.
      eapply (hh_seq H HH).
      { eapply OD with (lo := lo) (B := B) (LB := L11) (s := s11') (p := pf) (n := fb_cap FB); rewrite ?unsigned_lit by lia; try reflexivity.
        all: try solve [ unfold RFREE_STACK; lia | lia | exact MI11 | exact KREL11 | rewrite EA; exact ERR11 | exact HP11 | exact AUX11 | exact INF | exact STP ]. }
      intros [ms13 mo13] PO. unfold free_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m13 & s13' &
                      -> & KREL13 & MP13 & MI13 & ST13 & ERR13 & AUX13 & HPRES & HP13).
      rewrite (unsigned_lit P) in ST13, HPRES by lia. rewrite EA in ERR13.
      apply (hh_mpres_trans H HH _ _ _ MP11) in MP13. clear MP11.
      destruct (bperm_free H HH _ _ _ ND11 PERM11) as [PERM13 ND13]. cbn [blk_id fst snd] in PERM13, ND13.
      hp_frame HPRES P.
      assert (XP13 : xpres LB (P + 512) XH_X m0 m13).
      { eapply (xp_lift_free_gen H HH s11' L11 LB m11); [exact XP11| exact HP11| | exact INF| | exact HPRES| lia| lia].
        - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM11|]. right. exact Hb.
        - apply (FR (pf, fb_begin FB, fb_cap FB)). apply in_or_app. right. left. reflexivity. }
      assert (HS13 : HStat FT m13).
      { eapply (HStat_xpres_keep FT L11 P [(fb_begin FB, fb_begin FB + fb_cap FB)]); [exact FT_local| exact HS11| |].
        - eapply (xpres_free H HH); [exact HP11| exact INF| exact HPRES| intros a Ha; cbn; left; exact Ha].
        - pose proof (hh_blocks H HH _ _ _ _ HP11 INF) as (_ & _ & _ & _ & F5). cbn in F5. intros a Ha [R|[]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 P_FZ_RET_DEL)) with (Z_to_bv 64 P_FZ_RET_DEL)
        by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_DEL; lia| reflexivity]).
      eapply (xpres_stk _ _ _ m11 m13) in STM; [| apply xpres_of_heap_pres; exact HPRES| lia| apply Forall_nil].
      pose proof (stk_merge usegs _ _ _ _ ST13 STM ltac:(lia)) as ST416'.
      eapply (hh_evt H HH); [exact KREL13| |].
      { eapply fzJ; [exact SAV| exact FBC| reflexivity| exact FRE| exact SZE| exact ST416'| lia| lia| lia| exact RAE| exact MI13]. }
      intros ms14 PO. unfold fz_ret_post in PO. unfold fz_final. cbn [cfg_ms cfg_model].
      destruct PO as (q0' & q1' & q2' & r1' & r2' & r3' & r4' & r5' & r6' & r7' & q3' & q4' & q5' & q6' & m14 & -> & MU & WM & MI14 & ST14).
      rewrite (unsigned_lit (P + 512)) in ST14 by lia.
      do 14 eexists. exists m14, errv, s13', (hs_lb_remove H pf L11).
      split; [reflexivity|]. split; [exact KREL13|]. split; [exact MP13|]. split; [exact MI14|]. split; [exact ST14|].
      split. { rewrite EA. eapply (rw_cells_transport usegs _ m13 m14); [exact ERR13| exact MU| exact WM| exact I]. }
      split. { eapply (hh_rauxv_frame H HH); [exact AUX13| exact MU| exact WM| constructor]. }
      split. { eapply (hh_RHEAP_frame H HH); [exact HP13| exact MU| exact WM| constructor]. }
      split; [exact PERM13|].
      split. { eapply HStat_munch_keep; [exact FT_local| exact HS13| exact MU| constructor]. }
      eapply xpres_trans; [exact XP13|]. eapply xpres_of_munch_gen; [exact MU| exact WM| intros; exact I].
  Qed.
End W.
End HCW.

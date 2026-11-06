(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep N8Kit N8Kit2 N8Kit3 X8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac gen_andi :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Z.land ?a 7 + ?k)] => generalize (Z_to_bv 64 (Z.land a 7 + k))
  | |- context [Z_to_bv 64 (Z.land ?a 7)] => generalize (Z_to_bv 64 (Z.land a 7))
  end.

(* [comment removed for export] *)
Ltac slow_refute V1 V2 KV K2 :=
  exfalso; revert K2; rewrite ?Z.add_0_r;
  first [ rewrite land7_mod8 by lia | idtac ];
  rewrite !bv_signed_small by (rewrite unsigned_lit; Z.div_mod_to_equations; lia);
  rewrite !unsigned_lit by (Z.div_mod_to_equations; lia); clear - V1 V2 KV; intros K2; lia.

(* [comment removed for export] *)
Ltac shchk_brv_ge V1 V2 :=
  lazymatch type of V1 with 0 <= ?v < 8 =>
    let KV := fresh "KV" in let K2 := fresh "K2" in
    step; if_cases KV; zify_cond KV; rewrite ?(unsigned_lit v) in KV by (clear - V1; lia);
    [ (* [comment removed for export] *)
      zstep; first [ step; if_cases K2 | zstep; step; if_cases K2 ]; zify_cond K2;
      [ slow_refute V1 V2 KV K2
      | clear KV K2; step ]
    | clear KV ]
  end.

Ltac shchk_join_with BR :=
  lazymatch goal with
  | |- evt _ _ _ =>
      let X := fresh "X" in let K := fresh "K" in
      evar (X : Prop);
      cut X; [ intros K; BR; [ gen_andi; exact K | unfold X in K; apply K ] | unfold X; clear X ]
  end.
(* [comment removed for export] *)
Ltac shchk_join V1 V2 := shchk_join_with ltac:(idtac; shchk_brv V1 V2).
Ltac shchk_join_ge V1 V2 := shchk_join_with ltac:(idtac; shchk_brv_ge V1 V2).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac join_frameA LOW HIGH base :=
  lazymatch type of LOW with rw_cells _ ?mx _ ?cs1 =>
  lazymatch type of HIGH with rw_cells _ _ ?ah ?cs2 =>
    let J := fresh "FRJ" in
    assert (J : rw_cells asegs mx base (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app asegs mx base cs1 cs2)); split; [exact LOW | cbn [cells_size csize Nat.add];
            lazymatch goal with |- rw_cells _ _ ?a _ => replace a with ah by lia end; exact HIGH]);
    clear LOW HIGH; cbn [app] in J; rename J into LOW
  end end.

Ltac split_frameA FR cs1 cs2 LOW HIGH :=
  lazymatch type of FR with rw_cells _ ?mx ?base _ =>
    apply (proj1 (rw_cells_app asegs mx base cs1 cs2)) in FR;
    destruct FR as [LOW HIGH]; cbn [cells_size csize Nat.add] in HIGH;
    repeat match type of HIGH with
    | rw_cells _ _ (Z.add (Z.add ?b ?c) (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (c + Z.of_nat k)%Z in
        replace (Z.add (Z.add b c) (Z.of_nat k)) with (Z.add b v) in HIGH by lia
    | rw_cells _ _ (Z.add ?b (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in HIGH
    end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section PSIDE.
  Context {HCEIL : HeapCeil}.

  Definition pside (m : mem) (lo shi : Z) (ACC SHV : list (Z * Z)) : Prop :=
    aside m lo shi ACC SHV /\ AXStatics m.

  (* [comment removed for export] *)
  Definition pwin (iv : Z * Z) : Prop := awin iv /\ (0x125e40 <= fst iv \/ snd iv <= 0x115000).

  Lemma pwin_stack : forall l h, aceil <= l -> pwin (l, h).
  Proof.
    intros l h Hl. split; [apply awin_stack; exact Hl|]. pose proof aceil_facts as (AF & _). left. cbn [fst]. lia.
  Qed.
  Lemma pwin_aapp : forall A n l h, aapp A n -> A <= l -> h <= A + n -> pwin (l, h).
  Proof.
    intros A n l h AP Hl Hh. split; [eapply awin_aapp; eauto|]. left. cbn [fst].
    destruct AP as [[L1 L2]|[L1 L2]]; unfold AIMG_TOP, AHI_LO in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pwin_httpcat : pwin (AG_HTTP_CAT, AG_HTTP_CAT + 64).
  Proof.
    split; [| left; cbn [fst]; unfold AG_HTTP_CAT; lia].
    apply awin_img; [| unfold AG_HTTP_CAT, AIMG_TOP; lia].
    apply aconst_ok_intro; unfold AG_HTTP_CAT, ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
      ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP;
      rewrite ?ASHADOW_BASE_val; lia.
  Qed.

  Lemma pside_transport : forall W m m' lo shi ACC SHV,
    pside m lo shi ACC SHV -> munch W m m' -> wmono asegs m m' -> Forall pwin W -> pside m' lo shi ACC SHV.
  Proof.
    intros W m m' lo shi ACC SHV (AS & XS) MU WM FW. split.
    - eapply aside_transport; [exact AS| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv (K & _). exact K.
    - eapply AXStatics_transport; [exact XS| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv (_ & K). exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma pside_aconst : forall m lo shi ACC SHV, pside m lo shi ACC SHV -> ACONST m.
  Proof. intros m lo shi ACC SHV ((K & _) & _). exact K. Qed.
  Lemma pside_stack0 : forall m lo shi ACC SHV, pside m lo shi ACC SHV -> stack0 m lo shi.
  Proof. intros m lo shi ACC SHV ((_ & K & _) & _). exact K. Qed.
  Lemma pside_statics : forall m lo shi ACC SHV, pside m lo shi ACC SHV -> AXStatics m.
  Proof. intros m lo shi ACC SHV (_ & K). exact K. Qed.
  Lemma pside_acc : forall m lo shi ACC SHV o n, pside m lo shi ACC SHV -> In (o, n) ACC -> accessible m o n.
  Proof. intros m lo shi ACC SHV o n ((_ & _ & K & _) & _) IN. exact (proj1 (Forall_forall _ _) K _ IN). Qed.
  Lemma pside_shvis : forall m lo shi ACC SHV o n, pside m lo shi ACC SHV -> In (o, n) SHV -> shvis m o (o + n).
  Proof. intros m lo shi ACC SHV o n ((_ & _ & _ & K) & _) IN. exact (proj2 (proj2 (proj2 (proj1 (Forall_forall _ _) K _ IN)))). Qed.
End PSIDE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AOBJ.
  Context {HCEIL : HeapCeil}.

  Definition aobj (m : mem) (A n : Z) : Prop :=
    0 <= n /\ accessible m A n /\ shvis m A (A + n) /\ in_app_mem A (A + n) /\ awin (A, A + n).

  Lemma aobj_stack : forall m lo shi A n,
    stack0 m lo shi -> lo + 64 <= A -> 0 <= n -> A + n + 64 <= shi -> aobj m A n.
  Proof.
    intros m lo shi A n SK HA Hn HB. pose proof (stack0_bounds _ _ _ SK) as [B1 B2].
    split; [exact Hn|]. split; [eapply stack0_accessible; [exact SK| lia| lia| lia]|].
    split; [eapply stack0_shvis; [exact SK| lia| lia| lia]|].
    split; [eapply stack0_in_app_mem; [exact SK| lia| lia]|].
    apply awin_stack. lia.
  Qed.
  Lemma aobj_aapp : forall m A n,
    aapp A n -> 0 <= n -> accessible m A n -> shvis m A (A + n) -> aobj m A n.
  Proof.
    intros m A n AP Hn AC SV. pose proof (aapp_bounds _ _ AP Hn) as (B1 & B2 & B3 & B4 & B5).
    split; [exact Hn|]. split; [exact AC|]. split; [exact SV|].
    split; [eapply aapp_in_app_mem; [exact AP| lia| lia]|].
    eapply awin_aapp; [exact AP| lia| lia].
  Qed.

  Lemma aobj_acc : forall m A n, aobj m A n -> accessible m A n.
  Proof. intros m A n (_ & K & _). exact K. Qed.
  Lemma aobj_awin : forall m A n, aobj m A n -> awin (A, A + n).
  Proof. intros m A n (_ & _ & _ & _ & K). exact K. Qed.
  Lemma aobj_pos : forall m A n, aobj m A n -> 0 <= A /\ 0 <= n /\ A + n <= AAPP_HI.
  Proof. intros m A n (Hn & (A0 & A1 & _) & _). lia. Qed.
  (* [comment removed for export] *)
  Lemma aobj_sub_acc : forall m A n a k, aobj m A n -> A <= a -> 0 <= k -> a + k <= A + n -> accessible m a k.
  Proof. intros m A n a k (_ & K & _) ? ? ?. eapply accessible_sub; [exact K| lia| lia| lia]. Qed.
  Lemma aobj_sub_shvis : forall m A n a k, aobj m A n -> A <= a -> 0 <= k -> a + k <= A + n -> shvis m a (a + k).
  Proof.
    intros m A n a k (Hn & (A0 & A1 & _) & K & _) ? ? ?. eapply shvis_sub; [exact K| lia| lia| lia| lia| lia].
  Qed.
  Lemma aobj_sub_inapp : forall m A n a k, aobj m A n -> A <= a -> a + k <= A + n -> in_app_mem a (a + k).
  Proof. intros m A n a k (_ & _ & _ & K & _) ? ?. eapply in_app_mem_sub; [exact K| lia| lia]. Qed.
  Lemma aobj_sub_aconst : forall m A n a k, aobj m A n -> A <= a -> a + k <= A + n -> aconst_ok (a, a + k).
  Proof.
    intros m A n a k (_ & _ & _ & _ & (K & _)) ? ?. intros x Hx. apply K. cbn [fst snd] in *. lia.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma aobj_transport : forall W m m' A n,
    aobj m A n -> munch W m m' -> wmono asegs m m' -> Forall awin W -> aobj m' A n.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8LeafKit.AOBJ.aobj); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.accessible); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shvis); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8Kit.awin); constr:(HCEIL); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AAPP_HI); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mrd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.byte_ok); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.accessible_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8Kit.awin_outside_sh); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shvis_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_lo_le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_lo); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_hi_ge); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh_mono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsWalk.sh_ge_lowsh); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8Kit.awin_disjoint_shland); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ASHADOW_BASE_val); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO)|] [|@v; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__x3; @__x4; @Hx; @__sat4; @Ha; @__x5; @__sat10; @__sat9; @H0; @H5; @r0; @q0; @H8; @H7; @H6; @H4; @r; @q; @H3; @H2; @H1; @H; @__x6; @__x7; @__x8; @H10; @H9; @__sat5; @z; @__sat6; @__sat7; @__sat8; @KM; @KL; @LE; @G3; @G2; @G1; @L3; @L2; @L1; @_H; @A1; @A0; @FW; @WM; @MU; @AW; @IA; @SV; @AC; @Hn; @n; @A; @m'; @m; @W|] "#09#h%-#s$G#w##$H$F#$#%$O#(#~#A#'#&#+#)#*$&#B$N#-#.#1#0$)#,#/#C#D$z#3#4#8#:#;#7#>#?#@$8#F#J#f#q#2#6#9#=#h$Z#L#Y#5#<#E$>#G#K#O#M#P#S#U#V#W#X#\#]#^#_#`$v${#a%&%*%+#k#n#}$=$P$I$V$W#H#I#N#Q#R#T#Z#[$n$m$q$s#g%%%$#b#c#e%)%,#l#r$($/$2$1$3$?$A$C$E$Q$S$X$Y$T$6$5$]$c$f$o$p$r$u$t$x$w$y$|$}$~#d%#%-%(%.%'$\#m#{#x#v#p$*$-$_$M$b$^$K$J$D$h$0$:$##|$@$[#u#z$L$<$;$a#t#y$,$.$+$B$g$$$%$'$R$4$d$`$e$i$j$k$l#o$9$7$UU$X%$Y%$Z%$[$$\%$]&$^%$_$$`$$a$$b'$c*$d+$e%$f$$g&$h'#r%$i%$j'$k&$l($m&$n%$o$$p%$q%$r&$s&$t$$u&$v%$w%$x%$y&$z&${&$|%$}'$~%%#&%$%%%%%&%%'%%(%%)$%*%%+&%,%US`S|&S>&#&#&#&#&#Q#USa#Q(USa#US}#k##&#>PIF%EI?OJI#JI9OJ#5J$3CCJ%4M#$%#$'#$*#$,#ERLOFS$RLVS~CCUSbMG$#Q>S#RLk##$#k##(#k##*#j##,#?LPJ#PJ9LP#5P$3CCP%4M#$%#$'#$*#%EP?S#LO#LO9S#L#5L$3CCL%4M#$%#$'#$*#?QRL#RL9QR#5R$3CCR%4M#$%#$'#$*#ES'S,QFS$S'S,Gs#(s#'S->S(S'S,k##$#k##&#k##(#j##*##S#R9S,S##5S#$3CCS#%4M#$%#$'#?S'QS##S,Q9S(S,#5S,$3CCS,%4M#$%#$'##S'S,9S-S'#5S'$3CCS'%4M#$%#$'#ES)S*S-FS$S)S*Gs#Fs#ES1>S?S)S*k##$#k##&#k##(#j##*##S(S'5S(#3CCS($4M#$%##S-S(9S)S-##S*S-5S*#3CCS*$4M#$%##S)S*5S)#3CCS)$4M#$%#ESGS2S1FS$SGS2Gs#_s#^S6>S@SGS2k##$#k##&#k##(#j##*##S?S)3CCS?#4M##S1S?5S1##S2S13CCS2#4M#ES3S6S@FS$S3S6Gs#os#nS4?S4S3S6%ESA#SAS3%#S+%S4F#S4SA'F#$%#%EF@s$5'F#$%#1JUT##AS$S7#UT$FVT%s$5#(s$5%#VT&FJ$$#$+#j#$C#BC#k##2#k#%C#$8#$;#>S5S4SAj##$#%:S+%S5F#S5S4'F#$%#AS$S87(s$G#5$#4$<#j#$C#BC#k##)#k#%C#$/#%ES5#SHS5%#S+%SBF#SBSH'F#$%#AS$Ns#'(s$W#s#%$#s#$$s#,#j#$C#BC#k##)#k#%C#$/#%.S+%S7F#S7SB'F#$%#AS$S%s#5(s$e#s#3$#s#2$s#:#j#$C#BC#k##)#k#%C#$/#>S8S7SBj##$#%S8F#S8S7'F#$%#AS$S.s#D(s$t#s#B$#s#A$s#I#j#$C#BC#k##)#k#%C#%-S+%NF#NS9'F#$%#AS$SIs#Q(s%%#s#O$#s#N$s#V#j#$C#BC#k##)#k#%C#%ES9?S%NS99S%N/5N03CCN14M#$%#$'#$)#%S%F#S%N'F#$%#'IS+;Sc;#<C#<C%<CSc2C$#2C&#R#SJUT'S:SS:$#US`S:UT(CCCJ6C$I#UT)CUT*C*S>:C#:CS>-C$S&#.'HDDG#KZSd(HDDGO[Se)HDDG$#UT+DHCE-C#S&*.-HDDG#K-C%S&+./HDDG#K/0HDDG%(#/1HDDG*)#VT,2GTSfSgVT-FJ(Sf#Sgm$%#WT.CEIXT/FJ$#l#&*)#l#'<;#l#(A@#j#)C#j#*C#j#+SC#%IF$#J%EJk####k##%#k#)C#k#*C#k#+SC##S/S.'J#YF#S/JIQl#,.&#m##s%oCCO6C#Js#1CCP6C$I#ZSds#0HDDGR:Cs&%7C#s#0-Cs#0SD#.s#4HDDG#K[Ses#5HDDG'#:Cs&+-C'S&#.s#8HDDG#K-Cs#6SD%.s#:HDDG#K/s#;HDDG%s#3#/s#<HDDG)s#4#l#&#s#-s#'l#'1s#?#l#(s#Es#D#j#)C#j#*C#j#-C#j#.C#j#+SC#'Fs%s$O##OP%#J'JPk##$#k##'#k#)C#k#*C#k#-C#k#.C#k#+SC#%S/J[F#S/S.S+JIOl#,1%#m##s#dIs&=s#es#,#$s&>s#fm#$#YT0MS;IS(#j#/s#j#j#%C#\T1S/S.S%NS9S3S(#VT2NL,N%#N@s&O#%#'N#)'%(C#E$%#$)#,S%%#S%#$+'S%#)&-(C#E$%#$(#,S.1##S.S%+#1#=#&KS;'#j##*##*9'S.#),;(C#E$%#,S/%#S/,SI##A'SI#)%s##(C#E$%#,S;##s#''S;#)%s#)(C#E$%#,SK1##SKS;+#1#=#&KS<'#j##*#)*s#4(C#E,Sh##s#7'Sh#,Si)#s#:(C#E#S<Si,S<J#s#>%E$%Es#@,SE)#s#B%E#k##&#k##(#6Cs$JIs$K-Cs$?S&s#p.s$IHDDG#K7Cs$Gs#r-Cs$BS&#.s$LHDDG#K/s$MHDDG&s$E#/s$NHDDGs$As$F#l#&#s$?s$9l#'+s$Q#l#(s$Ws$V#j#)C#j#*C##JP%E#k##s$7#k##s%t#k#)C#k#*C#XFSLSES1SKl#,*$#l#0?8#%EBm#$#VT3s#$#+s#%%s#&##s#'s#a'%#)&s#c(C#E$%#$(##SLS<+#%$##%s#j'%#)&s#l(C#E$%#$(#1s#1#SESL+#1#=#&KSM'#j##)##(s#w'(#))s#y(C#E$%##SNSE+#%$##SjSN+##$s$%'$#)%s$'(C#E$%##SMSj+##$s$,'$#)%s$.(C#E$%#,SO1##SOSM+#1#=#&KSP'#j##*#)'s$9(C#E#SkSO+##$s$='$##SlSk+#)#s$A(C#E#SPSl+#L#s$E(Cs$FEUT4##SmSP+#0#s$JDs$K#)%s$L#$#(C'#k##*#M)s$P'Es$Q#SQSm+#)#s$T%E#'$s$V$$#k##)#N(s$Y's$ZE#SRSQ+#)#s$]'s$^#%$E$$#k##)#O(s$b#SSSR+#0#s$e(C#Ek##s###P&s$h#STSS+#)#s$k(C#$k##s#)#0&s$n#SFST+#)#s$q,SnL#s$s,So0#s$uDs$v#)%s$w#$#(C'#k##s#5#M)s${,SU)#s$}%E#'$s%#$$#k##s#2#N(s%&,SV)#s%('s%)#%$E$$#k##s#0#O(s%-,SW0#s%/(C#Ek##s#I#P&s%2,SX)#s%4(C#$k##s#N#0&s%7,SY)#s%9VSpEs%:TSq#m##s#IUL#'Fs%>$s']#US*&%EQ'Qs%B$$#@s):*s);*#*#*#@#VT5(#'E)%E%VT6+&'E#k##%#k##'#%E/WT70+Ij##Sr#j#1%#%E*k##Sr#k#1(#VSpE6TSq#m##1UI#;s&k;#<C#<C%2C#s&l2C%#VT8Cs%bWT9C#s&oUT:S>VT;C#;+<C#WSZC%#WSZC&-2C-s&x2C$#2C&#2C,#R#SJVSs0#SS:#s&x6Cs&vJs&HCCL6Cs&xP#6C%I#HCs%u-C#S0s&n.s&xHDDG#KZT<s&yHDDG#*s&y:C#WS[C(#&s&|:C#7C%#-Cs&}S0#.s'%HDDG#K/s'&HDDG+s&z#-C'S0s&z.s'(HDDG#K7Cs''s&Q7C#2-Cs'(SD#.s',HDDG#KHCs#FQs#CWT=C$#-C)S&#.s'1HDDG#K-Cs'/S&%.s'3HDDG#K/s'4HDDG%s',#/s'5HDDG+s'-#/s'6HDDG0s'.#/s'7HDDG3s'/#l#&#s'(s&~l#'Bs':#l#(s#'s'?#j#)C#j#*C#j#-C#j#.C#j#2C#k##s$WT>Ds&@L##O(CI#k##&#(COE#s&]s&E'J#%s)ls#X%Os#Yk##$#k##&#k##)#k##+#k#)C#k#*C#k#-C#k#.C#k#2C##StS=+#]FS)S*StS=#S@S6S3S<l#,9&#l#3s#Ys#e#l#4s#as#^#l#3s#ls#f#l#5s#ws#t#l#6s#{s#y#l#7s$$C#l#8s$'C#l#9s$-s$)#l#:s$3s$/#l#;s$;s$5#l#6s$Cs$=#l#<s$Ls$E#l#=s$OC#l#>s$SC#l#?s$Zs$U#l#@s$as$\#l#As$ks$c#l#5s$us$m#l#Bs%%s$w#%s%'S+m#$#WT?s%$S+F1s%%1S+%$#,SQJs${s&p%Es$|)s$ls&r%E#k##s&6#k##&#,SRJ#s&w%E$,ST)#s&z%E#k##s&>#k##'#,SSL#s'#0)s'$Ds'%###*(C,#k##s%?#M.s'),SF)#s'+%E#'$s'-$$#k##s%<#N(s'0)s$ys'1's'2#%$E$$#k##s%9#Os$~s'6(Cs$|Ek##s%P#Ps%#s'9(Cs$ws$xk##s%S#VSus$zs'<m#Sv##SVSU+#L#s'@#SWSV+#0#s'CDs'D#)%s'E#$#(C'#k##s%_#M)s'I#SXSW+#)#s'L%E#'$s'N$$#k##s%]#N(s'Q#SYSX+#)#s'T's'U#%$E$$#k##s%\#O(s'Y#S\SY+#0#s'\(C#Ek##s%v#P&s'_#SwS\+#)#s'b(C#$k##s%|#VSu&s'em#Sv#UOs%-#SxSw+#)#s'j%E#'$s'l$$#US(s%4,T@)#s'p%E#'$s'r$$#;s$l;#<C#WSZCs$p#2Cs$ms)(2C$#;'<C#2Cs$|s${2Cs$t#2C%#2Cs$z#R#SJVSs*#SS:#s).CCS#6C#Ls)-6Cs).J#CCQ6C#Rs)06Cs(_P#6C&I#:Cs%FWS[Cs$t#7C#s$p-Cs$nS0#.s)3HDDG#K/s)4HDDGs$us),#&s%M:C#WS[Cs${#:Cs%P7C$#-Cs)7S0#.s);HDDG#K/s)<HDDGs$}s)4#-Cs$|S0s)4.s)>HDDG#K-Cs$tS&s${.s)@HDDG#K-C+S0s)8.s)BHDDG#K7Cs)@s%+-Cs)BSD#.s)EHDDG#K/s)FHDDGs'[s)>s)9/s)GHDDGs)<s)?#/s)HHDDG%s)@#/s)IHDDG)s)A#/s)JHDDG,s)B#/s)KHDDG/s)C#/s)LHDDG2s)D#/s)MHDDG;s)E#l#&#s)>s)8l#'s##s)P#l#(s#+s)U#j#)C#j#*C#j#-C#j#.C#j#2C#j#CC#j#DC#j#EC#Ds(XQ##R(CL#k##s$z##&L(CJ#k##s$}#(CS#E%s,)S##Ls(a'S##k##s&$s&$k##s&%#k##%#k##)#k##)#k##+#k##-#k##1#k#)C#k#*C#k#-C#k#.C#k#2C#k#CC#k#DC#k#EC##S=Sy+#0#s(u,S=0#s(w)&s(x)%s(ydF'%$(#S=Sy&QS)S@S5S8S9SNS\l#,s#&+#l#5s#ls#g#l#;s#ts#n#,Sx%E#m#%#l#Fs#ys#z#l#Gs$%s#|#l#9s$,s$'#l#:s$5s$.#l#;s$>s$7#l#6s$Hs$@#l#<s$Ls$M#l#?s$Qs$O#l#@s$Us$S#l#As$\s$W#l#5s$ds$^#l#Bs$ks$f#l#0s$ts$n#l#Hs$|s$w#%Es$~m#$#VTAs%$#1s%%%S]#1s$|1s';=#$*s%|*#*#*#*#*#*#*#*#*#*#*#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#@#0s%8s+u#F#0s'Ts+w#F#=#%#&#&s-O&#&#&#&#&#&#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#@#%s#*#j#IC#%S]s#0j#IC#ZSzCS^#Fs#4S_0s%rs,K#s#6#%S]#0s(%s,N#F#0s'Ds,P#F#%%#j#IC#ZSzCS^#Js#>S_#s#?s#<#s#@(%$##SnSF+#VS{#s,Z%E$%Es,\#SUSo+#0#s,_%E#k##'#k##)#VS{s(0s,c%Es(10s(#s,e%E#k##-#k##&#J-s*L%E.%Es%gk##s)m#k##%#Js(,s*Q%Es(-%Es'}k##s)r#k##%#ULs'ZHCs#^7C#s+%HCs#3-C$S&#.s+\HDDG#K7C's+ZWTBC'#7C$#-C#S&(.s+aHDDG#K/s+bHDDG(s+Z#l#&#s+Ss+Ml#'s){s+e#l#(s+ls+j#j#)C#j#*C##s#nI%#s#B#s#pJ=#%#&#%#s#Fk##'#k#)C#k#*C#0s%{s-10s(;s-2WF$#Ql#,/&#l#4@s('#l#0s#&B#l#Hs#,s#(#l#Js#3s#.#l#Ks#=s#5#l#Ls('s($#l#4s(2s(,#0s&`s-<#s$'##s$(s#N=#$#%#%#s#Zm#)#l#Ms#Ms#J#l#Ns#Xs#U#ZTCCs$/s#\#S^S_#s$Os$M%#TDm#%#[TEMSFs$Rs$PNF#l#Ns$Vs$T#l#Ms&}s&z#l#Os'#s'$#j#Ps)L#j#Qs)Q#V#IFj##s)W#j##s)e#8s)fs)ds)[#Fj#Bs)k#j#Rs)s#V#IFj##s)x#j##s*/#8s*0s*+s*##Fl#Bs*<s*4#j#Ss*`#j#Ts*d#V#IFj##s*i#j##s*w#8s*xs*vs*m#Fj#Bs*|#j#Us+'#V#IFj##s++#j##s+?#8s+@s+;s+2#Fl#Bs+Ls+C#]TFS/S.S%Ns,sS2S(S'#Is,fs,dS*S-Is,hs,d$#Is,js,ds+Q#Is,ls,dSH#j#Vs,n#j#Ws,{#V#IFj##s,~#j##s->#8s-?s-3s-0#Fj#Bs-A#j#Xs-Q#V#IFj##s-T#j##s-~#8s.#s-gs-d#Fl#BS-s.%#j#Ys.'#j#Zs.)#j#[s.+#j#\s.-#j#]s.1#V#IFj##s.5#j##s.D#8s.Es.Cs.:#Fj#Bs.H#j#^s.N#V#IFj##s.R#j##s.e#8s.fs.bs.Y#Fj#Bs.i#j#_s.q#V#IFj##s.t#j##s/0#8s/1s/*s.}#Fj#Bs/3#j#`s/=#V#IFj##s/@#j##s/^#8s/_s/Vs/K#Fj#Bs/a#j#aC#j#bC#j#cs/e#j#dTG#j#es/s##"). Qed.

  (* [comment removed for export] *)
  Lemma acc_transport_awin : forall W m m' a n,
    accessible m a n -> munch W m m' -> Forall awin W -> accessible m' a n.
  Proof.
    intros W m m' a n AC MU FW. pose proof AC as (A0 & A1 & _).
    eapply accessible_transport; [exact AC| exact MU|]. intros x Hx. apply awin_outside_sh; [exact FW| lia].
  Qed.
  Lemma aconst_transport_awin : forall W m m',
    ACONST m -> munch W m m' -> wmono asegs m m' -> Forall awin W -> ACONST m'.
  Proof.
    intros W m m' AC MU WM FW. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv (K & _). exact K.
  Qed.
End AOBJ.


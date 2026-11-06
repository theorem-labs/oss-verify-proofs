(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep N8Kit N8Kit2 N8Kit3 X8Kit.
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
    assert (J : rw_cells bsegs mx base (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app bsegs mx base cs1 cs2)); split; [exact LOW | cbn [cells_size csize Nat.add];
            lazymatch goal with |- rw_cells _ _ ?a _ => replace a with ah by lia end; exact HIGH]);
    clear LOW HIGH; cbn [app] in J; rename J into LOW
  end end.

Ltac split_frameA FR cs1 cs2 LOW HIGH :=
  lazymatch type of FR with rw_cells _ ?mx ?base _ =>
    apply (proj1 (rw_cells_app bsegs mx base cs1 cs2)) in FR;
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
  Definition pwin (iv : Z * Z) : Prop := awin iv /\ (0x12a180 <= fst iv \/ snd iv <= 0x119000).

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
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin); constr:(HCEIL); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin_img); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.aconst_ok_intro); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHBASE_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMEMCPYP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AINITED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AHIEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ADYING_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.APGSZ_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACANPOISON_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AVERBOSITY_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_TLSGA_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ATSD_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREGISTERED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACOVFLAG_CELL); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.Tauto.X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ASHADOW_BASE_val); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@Corelib.Init.Logic.or_introl)|] [|@__ff; @__varmap; @__wit; @__arith; @z; @__x1; @__p1; @__sat0; @__sat1|] "#/D#'#l#C#.#D#B#I#J###/#S#%#3#$#,#<#N#O#T#U#V#W#X#Y#Z#[#\#]#^#_#a#b#'#j#l#-#+#7#8#;#=#>#?#A#K#M#Q#P#R#L#c#e#f#g#&#`#h#i#k#:#9#m#*#2#6#5#F#E#4#H#1#0#@#G#d/#`$#a$#b%#c'#d*#e%#f%#g$#h%#i*#j&#k+#M##########*#+J#XS4DDJ#VS5O#$+##$###$#######$#$###$#############*#WS6DD7#M##$###$###$#########$#$###############*##6$#$#####$#########################*#$M####$###$#$#$#$#$#$#$#$###$#$###$#########*##s#>####$###$#$#########$#########*#$s#N##$###$#$#$#$###$#$#$#######*##9########*#$8####$#####$#####$#$#######*#$*##########*#$s#U$#$#$#$#$#####$###$#$###$#$#$#####*##2$#####$#####$#$###########*##s#M##########$#$#$#####*#$s#%##$#######*#$s#1##########$###$#####*#$s$\$#$#$#$###$#$#$#######*#$s$j##########$#$#$#$#######*##s#D$#$#######*##s$A$#####$###$#######*#$s#J##########*#$s$l########$###$#$#$#$#####$#$#######*#$0##########$###$#######*##s%P##############*#$s#k####$#$###########*##s%Z########################*##s$]######$#############################*#%s%}s&6WS7DDs&L$s&S$#####$#########################*#%5s%~(7#US8PUS9PUS:DUS;DUS<D$M####$#$###################$#####$#########*#)Ds&))Ds'$-D$#)Ds&C&D$G#'?FCCE#H#s'$####$###$#$#$#$###$#$#########*#)Ds&/&D#G:'s#3FCCE#H,s#4FCCE7#VS=s#5EVS>QRVS?ILWS@Q#Rm$%#WSADKNXSBIL$#l#$*)#l#%s#?s#>#l#&s#Bs#A#+s&Ns'H%#s&f%s&?s&P($#l#''#Im##$%s'Ms&k%s&DJ($#m#&#$s'L##$#$#####$###$#$#$#$#######*#)Ds&G&Ds#@G#'s#[FCCE#H*s#Y)D#-D'#&D#Gs#G's#`FCCE#H,s#aFCCE(#l#$#s#/s#)l#%s#es#d#l#&s#hs#g#%s#(s&S+s&T,%#s&v(%#l#''#Im##$%s'sS#+S#2%#J(%#m#'##s#H########*#)Ds&^&Ds#]G#'s#xFCCE#H*s())D#-D'#&D#Gs#d's#}FCCE#H,s#~FCCE(#l#$#s#Ls#Fl#%s$&s$%#l#&s$)s$(#%s#Es&j+s&k,%#s'7(%#l#''#Im##$%s(4S$+S$2%#J(%#m#'#$s#F####$#$#####$###$#$#######*#)Ds&u&Ds$'G#'s$BFCCE#H*s(R)D#-D'#&D#Gs$.'s$GFCCE#H,s$HFCCE(#l#$#s#rs#ll#%s$Ls$K#l#&s$Os$N#%s#ks'%+s'&,%#s'](%#l#''#Im##$%s(ZS%+S%2%#J(%#m#'#$A##########*#)Ds'0&Ds$EG#'s$`FCCE#H#s$^*#)D#-D(#&D#Gs$M's$fFCCE#H,s$gFCCE)#l#$#s$5s$/l#%s$ks$j#l#&s$ns$m#%s$.s'=+s'>,%#s'|(%#l#''#Im##$%s(yS&+S&2%#J(%#m#'#$s$t$#$#$#$#$###$#####$#####$#$#$#####*#)Ds'H&Ds$pG#'s%/FCCE#H*s)>)D#-D'#&D#Gs$w's%4FCCE#H,s%5FCCE(#l#$#s$_s$Yl#%s%9s%8#l#&s%<s%;#%s$Xs'T+s'U,%#s(J(%#l#''#Im##$%s)GS'+S'2%#J(%#m#'##s#)$###$#########$###########*#)Ds'_&Ds%:G#'s%UFCCE#H*s)c)D#-D'#&D#Gs%A's%ZFCCE#H,s%[FCCE(#l#$#s%)s%#l#%s%_s%^#l#&s%bs%a#%s$~s'k+s'l,%#s(p(%#l#''#Im##$%s)mS(+S(2%#J(%#m#'##s$}####$#$#$###$#$#$#####*#)Ds'w&Ds%^G#'s%yFCCE#H*M)D#-D'#&D#Gs%e's%~FCCE#H,s&#FCCE(#l#$#s%Ms%Gl#%s&'s&&#l#&s&*s&)#%s%Fs('+s((,%#s)8(%#l#''#Im##$%s*5S)+S)2%#J(%#m#'#$s#k##$#######*#)Ds(2&Ds%|G#'s&;FCCE#H$s#x$#$###$###$#####*#)Ds(3&D#Gs&/'s&HFCCE#H,s&IFCCE0#l#$#s%ss%ml#%s&Ms&L#l#&s&Ps&O#%s%ls(F%s(;s)]($#l#'&#Im##$%s*Zs(K%s(@J($#m#&#$s*W######$###$#$#$#$#######*#)Ds(D&Ds&KG#'s&fFCCE#H$1######$#$#$#######*#)Ds(D&D#Gs&['s&tFCCE#H,s&uFCCE1#l#$#s&Cs&=l#%s&ys&x#l#&s&|s&{#%s&<s(Y%s(Ls*-($#l#'&#Im##$%s+*s(^%s(QJ($#m#&##s$9$#$#######*#)Ds(T&Ds&pG#'s'/FCCE#H-D%s$]&D#Gs&u's'2FCCE#H,s'3FCCE&#l#$#s&]s&Wl#%s'7s'6#l#&s':s'9#%s&Vs(^+s(_s$f%#s*H(%#l#''#Im##$%s+ES*+S*s$l%#J(%#m#'##s&z$#$#####$#######*#)Ds(h&Ds'3G#'s'NFCCE#H-D%s$V&D#Gs'8's'QFCCE#H,s'RFCCE&#l#$#s&|s&vl#%s'Vs'U#l#&s'Ys'X#%s&us(r+s(ss$_%#s*g(%#l#''#Im##$%s+dS++S+s$e%#J(%#m#'#$s$P##########*#)Ds(}&Ds'OG#'s'jFCCE#H-D%s$r&D#Gs'T's'mFCCE#H,s'nFCCE&#l#$#s'<s'6l#%s'rs'q#l#&s'us't#%s'5s)++s),s${%#s+'(%#l#''#Im##$%s,$S,+S,s%%%#J(%#m#'#$s't$#####$#$#####$#########*#)Ds)1&Ds'rG#'s(1FCCE#H$1######$###########*#)Ds)2&D#Gs(&'s(?FCCE#H,s(@FCCE1#l#$#s'js'dl#%s(Ds(C#l#&s(Gs(F#%s'cs)F%s):s+T($#l#'&#Im##$%s,Qs)K%s)?J($#m#&##s,J$#$#############*#)Ds)C&Ds(>G#'s(YFCCE#H-D%s%a&D#Gs(C's(\FCCE#H,s(]FCCE&#l#$#s(+s(%l#%s(as(`#l#&s(ds(c#%s($s)M+s)Ns%j%#s+r(%#l#''#Im##$%s,oS-+S-s%p%#J(%#m#'#$s&O##########$###########*#)Ds)Z&Ds(`G#'s({FCCE#H-D%s%_&D#Gs(e's(~FCCE#H,s)#FCCE&#l#$#s(Ms(Gl#%s)'s)&#l#&s)*s))#%s(Fs)d+s)es%h%#s,8(%#l#''#Im##$%s-5S.+S.s%n%#J(%#m#'#$s)1$#$#$#$#$#$#$#$#$#$#$#$#$###############################*##s-Z##################*#VS/s*.s&c+I#%s(|#$s)W############################*#VS/s*-s&v+I#%#s-#(6#j#(D#VS0s*Fs&{%Ks*G%Ks&}%K=k##$#k##&#VS0s*8s'%%Ks*9%K/k##)#k##%#VSCDN)DK)Ds*S&D$G#'s*&FCCE#HUSDC&D'Gs'/'s*)FCCE#HVSEDM&D*G#'s*,FCCE#H.s*-FCCE&(#.s*.FCCE*)#)Ds#>-D#(&Ds)sG#'s*2FCCE#HZSFs*3FCCESG,s*4FCCE$#.s*5FCCE)0#l#$#s)_s)Yl#%7s*8#l#&s*<s*;#j#)D#j#*S1#%KLk##s#%#k##s#'#+s#MN%s)^#(#Lk##&#k#)D#k#*S1#+s#Ss#4%#s-TWI#s#ILl#'/&#l#+s#-s#)#l#,s#4s#/#+s#Ys#M%s)j#(#)m#&#ZSHDs#]s#:#SISJUS2SK%s.X#US2S3%#J(%#m#(#gSLJs.]s)ks)Ds)'s(]s(>s'ps'Js'&s&^s&2s%rs%Ss%7s$gs$Hs$&#)Ds*q&Ds*=G#'s*XFCCE#Hl#$#s*&s)|l#%s*\s*[#l#&s*_s*^#%s){s*wl#'$#Im##$%s.gS3m#$#YSMOJs.i.#)Ds.?&D#Gs*K's*dFCCE#Hl#$#s*2s*,l#%s*hs*g#l#&s*ks*j#%s.Es-wl#'$#Im##$%s.HJm#$#m##s++WSNs+,s*t#XSOs.us*t0##"). Qed.

  Lemma pside_transport : forall W m m' lo shi ACC SHV,
    pside m lo shi ACC SHV -> munch W m m' -> wmono bsegs m m' -> Forall pwin W -> pside m' lo shi ACC SHV.
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
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma aobj_stack : forall m lo shi A n,
    stack0 m lo shi -> lo + 64 <= A -> 0 <= n -> A + n + 64 <= shi -> aobj m A n.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0); constr:(HCEIL); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0_bounds); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8LeafKit.AOBJ.aobj); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.accessible); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0_accessible); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0_shvis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0_in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin_stack); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__x3; @B2; @B1; @H; @HB; @Hn; @HA; @SK; @n; @A; @shi; @lo; @m|] "#%o#1#o#5#U#V#-#T#%###$#.#+#\#]#&#7#*#0#=#)#/#,#A#'#<#L#:#N#b#c#o#p#m#6#(#>#@#C#E#F#G#I#H#K#M#P#Q#S#^#_#a#e#d#f#`#g#J#h#i#l#q#k#j#B#4#8#9#X#W#?#R#;#Y#D#O#Z#[#n0#b%#c%#d'#e*#f%#g+#h$#i&#j'#k%#l%#m%#n%XS2PS(OH)S))#)#)#)#)#US+#$S(###H#S#H$S(O$#'##S3YS4PLQS$OUS5P##Q#QS$#S$S''$#'&##(L#LQ#QS''$#'&#WS6FQS$j##$##S&L#LS''$##2F#KF#FS''$##S#S&WS7RFS&$FS&WS8RF#VS9F$XS:CCF%VS;P#'%#''#'*#US<S*US=S*,CHUS>CXS,C$J#US?CUS@C-CS).Cs#0*C$#-Cs#8%C$M#&(GDDE#NUSAD%C)M&&+GDDE#N(,GDDE&%#VSB-EVSCS-S.VSDIHWSES-#S.m$%#WSFCS#JXSGIH$#l#$*)#l#%76#l#&<;#j#'C#j#(C#$Is#E##J#JHk##$#k#'C#k#(C#WIKRLl#)*$##S%Fm#$#,CJ.CS#%C#Ms#$&s#&GDDE#N(s#'GDDE#@#l#$#=7l#%(s#*#l#&s#0s#/#j#'C##S#I#S#Jk##$#k#'C#VIFQl#)($#m##s#B,COXS,Cs#8J#*Cs#4s#1*C#s#4USHS)-C#%C%M#&s#:GDDE#N%C(M%&s#<GDDE#N(s#=GDDE%s#6#l#$#s#3s#-l#%-s#@#l#&s#Fs#E#j#'C#j#(C#j#*C#$IJ$#s#q##H$JH##Ok##%#k#'C#k#(C#k#*C#XIS%FKS$l#)-$##s#]Km#$#^SIPRS%KFS&Ls#1A#(s#RGDDEs#Ls#Ks#Ll#$#s#Hs#Bl#%s#Vs#U#l#&s#[s#Z#j#'C#j#(C#$Js$(##Hk##s#B#k#'C#k#(C#l#)(#s#@$S%s$.##Fm#%#%Cs#?Ms#]&s#bGDDE#N%Cs#bMs#0&s#dGDDE#N(s#eGDDE%s#^#l#$#s#[s#Ul#%s#is#h#l#&s#ns#m#j#'C#j#(C##Js#&k##s#A#k#'C#k#(C#WIFKQl#)($##Fs$#m#$#(s#sGDDEs#;s#ls#;l#$#s#is#cl#%s#Cs#v#l#&s#|s#{#j#'C#j#(C#j#*C#$s#5s$J##Ok##s#8#k#'C#k#(C#k#*C#l#))#s#5$s$3s$Q##Km#%#^SJPRS%KFs$6Ls#&4#US+s$Y.C#*Cs#T#%C#Ms#R&s$-GDDE#N(s$.GDDEs#Rs$'#l#$#s$$s#zl#%s#Zs$1#l#&s$7s$6#j#'C#j#(C#j#*C#$s#L.##Ok##s#O#k#'C#k#(C#k#*C#l#))#s#L$s$J5##Km#%#]SKPRS%KFs$MLs#{#US/S0US/#/C#/C%/CS0WS1C$#WS1C&#VSL#SMWSNS*#s$N%Cs$HMs#o&s$JGDDE#N*Cs#qs$I%C#Ms$H&s$MGDDE#N(s$NGDDE#s$Gs$E(s$OGDDE's$H#l#$#s$Es$?l#%s#{s$R#l#&,s$W#j#'C#j#(C#j#*C##IH$Os%'##H#HOk##$#k##'#k#'C#k#(C#k#*C#YIRKs%'HLl#)-$#m##s$uXSOPFs$p#+s$os$ms#&#+s$qs$ms#>#+s$ts$ms#r#+s$vs$mS$#j#+s$x#j#,s$|#V#JIj##s%##j##s%-#YSPs%.s%+s%(#Il#-s%6s%0#j#.s%8#j#/s%<#j#0s%>#j#1s%H#j#2C#j#3C#j#4C#j#5C#j#6SQ##"). Qed.
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

  Lemma aobj_transport : forall W m m' A n,
    aobj m A n -> munch W m m' -> wmono bsegs m m' -> Forall awin W -> aobj m' A n.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8LeafKit.AOBJ.aobj); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.accessible); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin); constr:(HCEIL); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mrd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.byte_ok); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.accessible_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin_outside_sh); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_lo_le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_lo); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_hi_ge); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh_mono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsWalk.sh_ge_lowsh); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin_disjoint_shland); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ASHADOW_BASE_val); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AHI_LO)|] [|@v; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__x3; @__x4; @Hx; @__sat4; @Ha; @__x5; @__sat10; @__sat9; @H0; @H5; @r0; @q0; @H8; @H7; @H6; @H4; @r; @q; @H3; @H2; @H1; @H; @__x6; @__x7; @__x8; @H10; @H9; @__sat5; @z; @__sat7; @__sat6; @__sat8; @KM; @KL; @LE; @G3; @G2; @G1; @L3; @L2; @L1; @_H; @A1; @A0; @FW; @WM; @MU; @AW; @IA; @SV; @AC; @Hn; @n; @A; @m'; @m; @W|] "#09#h%-#s$G#w##$H$F#$#%$O#(#~#A#&#'#+#)#*$&#B$N#-#.#1#0$)#,#/#C#D$z#3#4#8#:#;#7#>#?#@$8#F#J#f#q#2#6#9#=#h$Z#L#5#<#E$>#G#K#O#M#P#S#U#V#W#X#Y#]#^#_#`$v${#a%&%*%+#k#n#}$=$P$I$V$W#H#I#N#Q#R#T#Z#[#\$n$m$q$s#g%%%$#b#c#e%)%,#l#r$($/$2$1$3$?$A$C$E$Q$S$X$Y$T$6$5$]$c$f$o$p$r$u$t$x$w$y$|$}$~#d%#%-%(%.%'$\#m#{#x#v#p$*$-$_$M$b$^$K$J$D$h$0$:$##|$@$[#u#z$L$<$;$a#t#y$,$.$+$B$g$$$%$'$R$4$d$`$e$i$j$k$l#o$9$7$UU$X%$Y%$Z%$[$$\%$]&$^%$_$$`$$a$$b'$c*$d+$e%$f$$g&$h'#q%$i%$j'$k&$l($m&$n%$o$$p%$q%$r&$s&$t$$u&$v%$w%$x%$y&$z&${&$|%$}'$~%%#&%$%%%%%&%%'%%(%%)$%*%%+&%,%US_S|&S>&#&#&#&#&#Q#US`#Q(US`#US}#k##&#>OIF%EI?PJI#JI9PJ#5J$3CCJ%4M#$%#$'#$*#$,#ERLPFS$RLVS~CCUSaMG$#Q>S#RLk##$#k##(#k##*#j##,#?LOJ#OJ9LO#5O$3CCO%4M#$%#$'#$*#%EO?S#LP#LP9S#L#5L$3CCL%4M#$%#$'#$*#?QRL#RL9QR#5R$3CCR%4M#$%#$'#$*#ES'S,QFS$S'S,Gs#(s#'S->S(S'S,k##$#k##&#k##(#j##*##S#R9S,S##5S#$3CCS#%4M#$%#$'#?S'QS##S,Q9S(S,#5S,$3CCS,%4M#$%#$'##S'S,9S-S'#5S'$3CCS'%4M#$%#$'#ES)S*S-FS$S)S*Gs#Fs#ES1>S?S)S*k##$#k##&#k##(#j##*##S(S'5S(#3CCS($4M#$%##S-S(9S)S-##S*S-5S*#3CCS*$4M#$%##S)S*5S)#3CCS)$4M#$%#ESFS2S1FS$SFS2Gs#_s#^S6>S@SFS2k##$#k##&#k##(#j##*##S?S)3CCS?#4M##S1S?5S1##S2S13CCS2#4M#ES3S6S@FS$S3S6Gs#os#nS4?S4S3S6%ESA#SAS3%#S+%S4F#S4SA'F#$%#%EF@s$5'F#$%#1JUT##AS$S7#UT$FVT%s$5#(s$5%#VT&FJ$$#$+#j#$C#BC#k##2#k#%C#$8#$;#>S5S4SAj##$#%:S+%S5F#S5S4'F#$%#AS$S87(s$G#5$#4$<#j#$C#BC#k##)#k#%C#$/#%ES5#SGS5%#S+%SBF#SBSG'F#$%#AS$Ns#'(s$W#s#%$#s#$$s#,#j#$C#BC#k##)#k#%C#$/#%.S+%S7F#S7SB'F#$%#AS$S%s#5(s$e#s#3$#s#2$s#:#j#$C#BC#k##)#k#%C#$/#>S8S7SBj##$#%S8F#S8S7'F#$%#AS$S.s#D(s$t#s#B$#s#A$s#I#j#$C#BC#k##)#k#%C#%-S+%NF#NS9'F#$%#AS$SHs#Q(s%%#s#O$#s#N$s#V#j#$C#BC#k##)#k#%C#%ES9?S%NS99S%N/5N03CCN14M#$%#$'#$)#%S%F#S%N'F#$%#'IS+;Sb;#<C#<C%<CSb2C$#2C&#R#SIUT'S:SS:$#US_S:UT(CCCJ6C$I#UT)CUT*C*S>:C#:CS>-C$S&#.'HDDG#KZSc(HDDGP[Sd)HDDG$#UT+DHCE-C#S&*.-HDDG#K-C%S&+./HDDG#K/0HDDG%(#/1HDDG*)#VT,2GTSeSfVT-FJ(Se#Sfm$%#WT.CEIXT/FJ$#l#&*)#l#'<;#l#(A@#j#)C#j#*C#j#+SC#%IF$#J%EJk####k##%#k#)C#k#*C#k#+SC##S/S.'J#YF#S/JIQl#,.&#m##s%oCCP6C#Js#1CCO6C$I#ZScs#0HDDGR:Cs&%7C#s#0-Cs#0SD#.s#4HDDG#K[Sds#5HDDG'#:Cs&+-C'S&#.s#8HDDG#K-Cs#6SD%.s#:HDDG#K/s#;HDDG%s#3#/s#<HDDG)s#4#l#&#s#-s#'l#'1s#?#l#(s#Es#D#j#)C#j#*C#j#-C#j#.C#j#+SC#'Fs%s$P##PO%#J'JOk##$#k##'#k#)C#k#*C#k#-C#k#.C#k#+SC#%S/J[F#S/S.S+JIPl#,1%#m##s#dIs&=s#es#,#$s&>s#fm#$#YT0MS;IS(#j#/s#j#j#%C#\T1S/S.S%NS9S3S(#VT2NL,N%#N@s&O#%#'N#)'%(C#E$%#$)#,S%%#S%#$+'S%#)&-(C#E$%#$(#,S.1##S.S%+#1#=#&KS;'#j##*##*9'S.#),;(C#E$%#,S/%#S/,SH##A'SH#)%s##(C#E$%#,S;##s#''S;#)%s#)(C#E$%#,SJ1##SJS;+#1#=#&KS<'#j##*#)*s#4(C#E,Sg##s#7'Sg#,Sh)#s#:(C#E#S<Sh,S<J#s#>%E$%Es#@,SE)#s#B%E#k##&#k##(#6Cs$JIs$K-Cs$?S&s#p.s$IHDDG#K7Cs$Gs#r-Cs$BS&#.s$LHDDG#K/s$MHDDG&s$E#/s$NHDDGs$As$F#l#&#s$?s$9l#'+s$Q#l#(s$Ws$V#j#)C#j#*C##JO%E#k##s$7#k##s%t#k#)C#k#*C#XFSKSES1SJl#,*$#l#0?8#%EBm#$#VT3s#$#+s#%%s#&##s#'s#a'%#)&s#c(C#E$%#$(##SKS<+#%$##%s#j'%#)&s#l(C#E$%#$(#1s#1#SESK+#1#=#&KSL'#j##)##(s#w'(#))s#y(C#E$%##SMSE+#%$##SiSM+##$s$%'$#)%s$'(C#E$%##SLSi+##$s$,'$#)%s$.(C#E$%#,SN1##SNSL+#1#=#&KSO'#j##*#)'s$9(C#E#SjSN+##$s$='$##SkSj+#)#s$A(C#E#SOSk+#L#s$E(Cs$FEUT4##SlSO+#0#s$JDs$K#)%s$L#$#(C'#k##*#M)s$P'Es$Q#SPSl+#)#s$T%E#'$s$V$$#k##)#N(s$Y's$ZE#SQSP+#)#s$]'s$^#%$E$$#k##)#O(s$b#SRSQ+#0#s$e(C#Ek##s###P&s$h#SSSR+#)#s$k(C#$k##s#)#0&s$n#STSS+#)#s$q,SmL#s$s,Sn0#s$uDs$v#)%s$w#$#(C'#k##s#5#M)s${,So)#s$}%E#'$s%#$$#k##s#2#N(s%&,SU)#s%('s%)#%$E$$#k##s#0#O(s%-,SV0#s%/(C#Ek##s#I#P&s%2,SW)#s%4(C#$k##s#N#0&s%7,SX)#s%9VSpEs%:TSq#m##s#IUL#'Fs%>$s']#US*&%EQ'Qs%B$$#@s):*s);*#*#*#@#VT5(#'E)%E%VT6+&'E#k##%#k##'#%E/WT70+Ij##Sr#j#1%#%E*k##Sr#k#1(#VSpE6TSq#m##1UI#;s&k;#<C#<C%2C#s&l2C%#VT8Cs%bWT9C#s&oUT:S>VT;C#;+<C#WSYC%#WSYC&-2C-s&x2C$#2C&#2C,#R#SIVSs0#SS:#s&x6Cs&vJs&HCCL6Cs&xO#6C%I#HCs%u-C#S0s&n.s&xHDDG#KZT<s&yHDDG#*s&y:C#WSZC(#&s&|:C#7C%#-Cs&}S0#.s'%HDDG#K/s'&HDDG+s&z#-C'S0s&z.s'(HDDG#K7Cs''s&Q7C#2-Cs'(SD#.s',HDDG#KHCs#FQs#CWT=C$#-C)S&#.s'1HDDG#K-Cs'/S&%.s'3HDDG#K/s'4HDDG%s',#/s'5HDDG+s'-#/s'6HDDG0s'.#/s'7HDDG3s'/#l#&#s'(s&~l#'Bs':#l#(s#'s'?#j#)C#j#*C#j#-C#j#.C#j#2C#k##s$WT>Ds&@L##P(CI#k##&#(CPE#s&]s&E'J#%s)ls#X%Ps#Yk##$#k##&#k##)#k##+#k#)C#k#*C#k#-C#k#.C#k#2C##StS=+#]FS)S*StS=#S@S6S3S<l#,9&#l#3s#Ys#e#l#4s#as#^#l#3s#ls#f#l#5s#ws#t#l#6s#{s#y#l#7s$$C#l#8s$'C#l#9s$-s$)#l#:s$3s$/#l#;s$;s$5#l#6s$Cs$=#l#<s$Ls$E#l#=s$OC#l#>s$SC#l#?s$Zs$U#l#@s$as$\#l#As$ks$c#l#5s$us$m#l#Bs%%s$w#%s%'S+m#$#WT?s%$S+F1s%%1S+%$#,SPJs${s&p%Es$|)s$ls&r%E#k##s&6#k##&#,SQJ#s&w%E$,SS)#s&z%E#k##s&>#k##'#,SRL#s'#0)s'$Ds'%###*(C,#k##s%?#M.s'),ST)#s'+%E#'$s'-$$#k##s%<#N(s'0)s$ys'1's'2#%$E$$#k##s%9#Os$~s'6(Cs$|Ek##s%P#Ps%#s'9(Cs$ws$xk##s%S#VSus$zs'<m#Sv##SUSo+#L#s'@#SVSU+#0#s'CDs'D#)%s'E#$#(C'#k##s%_#M)s'I#SWSV+#)#s'L%E#'$s'N$$#k##s%]#N(s'Q#SXSW+#)#s'T's'U#%$E$$#k##s%\#O(s'Y#S[SX+#0#s'\(C#Ek##s%v#P&s'_#SwS[+#)#s'b(C#$k##s%|#VSu&s'em#Sv#UPs%-#SxSw+#)#s'j%E#'$s'l$$#US(s%4,T@)#s'p%E#'$s'r$$#;s$l;#<C#WSYCs$p#2Cs$ms)(2C$#;'<C#2Cs$|s${2Cs$t#2C%#2Cs$z#R#SIVSs*#SS:#s).CCS#6C#Ls)-6Cs).J#CCQ6C#Rs)06Cs(_O#6C&I#:Cs%FWSZCs$t#7C#s$p-Cs$nS0#.s)3HDDG#K/s)4HDDGs$us),#&s%M:C#WSZCs${#:Cs%P7C$#-Cs)7S0#.s);HDDG#K/s)<HDDGs$}s)4#-Cs$|S0s)4.s)>HDDG#K-Cs$tS&s${.s)@HDDG#K-C+S0s)8.s)BHDDG#K7Cs)@s%+-Cs)BSD#.s)EHDDG#K/s)FHDDGs'[s)>s)9/s)GHDDGs)<s)?#/s)HHDDG%s)@#/s)IHDDG)s)A#/s)JHDDG,s)B#/s)KHDDG/s)C#/s)LHDDG2s)D#/s)MHDDG;s)E#l#&#s)>s)8l#'s##s)P#l#(s#+s)U#j#)C#j#*C#j#-C#j#.C#j#2C#j#CC#j#DC#j#EC#Ds(XQ##R(CL#k##s$z##&L(CJ#k##s$}#(CS#E%s,)S##Ls(a'S##k##s&$s&$k##s&%#k##%#k##)#k##)#k##+#k##-#k##1#k#)C#k#*C#k#-C#k#.C#k#2C#k#CC#k#DC#k#EC##S=Sy+#0#s(u,S=0#s(w)&s(x)%s(ydF'%$(#S=Sy&QS)S@S5S8S9SMS[l#,s#&+#l#5s#ls#g#l#;s#ts#n#,Sx%E#m#%#l#Fs#ys#z#l#Gs$%s#|#l#9s$,s$'#l#:s$5s$.#l#;s$>s$7#l#6s$Hs$@#l#<s$Ls$M#l#?s$Qs$O#l#@s$Us$S#l#As$\s$W#l#5s$ds$^#l#Bs$ks$f#l#0s$ts$n#l#Hs$|s$w#%Es$~m#$#VTAs%$#1s%%%S\#1s$|1s';=#$*s%|*#*#*#*#*#*#*#*#*#*#*#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#@#0s%8s+u#F#0s'Ts+w#F#=#%#&#&s-O&#&#&#&#&#&#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#@#%s#*#j#IC#%S\s#0j#IC#ZSzCS]#Fs#4S^0s%rs,K#s#6#%S\#0s(%s,N#F#0s'Ds,P#F#%%#j#IC#ZSzCS]#Js#>S^#s#?s#<#s#@(%$#VS{s%|s,X%Es%}%Es,Z0s(*s,[%E#k##%#k##'#Js(0s*B%Es(1#SnSm+#)#s*F%E#k##s)f#k##(#Js(,s*J%Es(-)s'|s*L%E#k##s)l#k##&#VS{s%os,m%Es%p0s%es,o%E#k##9#k##&#UOs'ZHCs#^7C#s+%HCs#3-C$S&#.s+\HDDG#K7C's+ZWTBC'#7C$#-C#S&(.s+aHDDG#K/s+bHDDG(s+Z#l#&#s+Ss+Ml#'s){s+e#l#(s+ls+j#j#)C#j#*C##s#nI%#s#B#s#pJ=#%#&#%#s#Fk##'#k#)C#k#*C#0s%{s-10s(;s-2WF$#Ql#,/&#l#J@s('#l#0s#'B#l#Hs#.s#)#l#Ks(%s'~#l#Js(0s(*#l#Ls#9s#2#l#4s#As#;#0s&`s-<#s$'##s$(s#N=#$#%#%#s#Zm#)#l#Ms#Ms#J#l#Ns#Xs#U#ZTCCs$/s#\#S]S^#s$Os$M%#TDm#%#[TEMSTs$Rs$PNF#l#Ns$Vs$T#l#Ms&}s&z#l#Os'#s'$#j#Ps)L#j#Qs)Q#V#IFj##s)W#j##s)e#8s)fs)ds)[#Fj#Bs)k#j#Rs)s#V#IFj##s)x#j##s*/#8s*0s*+s*##Fl#Bs*<s*4#j#Ss*`#j#Ts*d#V#IFj##s*i#j##s*w#8s*xs*vs*m#Fj#Bs*|#j#Us+'#V#IFj##s++#j##s+?#8s+@s+;s+2#Fl#Bs+Ls+C#]TFS/S.S%Ns,sS2S(S'#Is,fs,dS*S-Is,hs,d$#Is,js,ds+Q#Is,ls,dSG#j#Vs,n#j#Ws,{#V#IFj##s,~#j##s->#8s-?s-3s-0#Fj#Bs-A#j#Xs-Q#V#IFj##s-T#j##s-~#8s.#s-gs-d#Fl#BS-s.%#j#Ys.'#j#Zs.)#j#[s.+#j#\s.-#j#]s.1#V#IFj##s.5#j##s.D#8s.Es.Cs.:#Fj#Bs.H#j#^s.N#V#IFj##s.R#j##s.e#8s.fs.bs.Y#Fj#Bs.i#j#_s.q#V#IFj##s.t#j##s/0#8s/1s/*s.}#Fj#Bs/3#j#`s/=#V#IFj##s/@#j##s/^#8s/_s/Vs/K#Fj#Bs/a#j#aC#j#bC#j#cs/e#j#dTG#j#es/s##"). Qed.

  (* [comment removed for export] *)
  Lemma acc_transport_awin : forall W m m' a n,
    accessible m a n -> munch W m m' -> Forall awin W -> accessible m' a n.
  Proof.
    intros W m m' a n AC MU FW. pose proof AC as (A0 & A1 & _).
    eapply accessible_transport; [exact AC| exact MU|]. intros x Hx. apply awin_outside_sh; [exact FW| lia].
  Qed.
  Lemma aconst_transport_awin : forall W m m',
    ACONST m -> munch W m m' -> wmono bsegs m m' -> Forall awin W -> ACONST m'.
  Proof.
    intros W m m' AC MU WM FW. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv (K & _). exact K.
  Qed.
End AOBJ.


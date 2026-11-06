(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages AsHSTab BoStartupHSF BoStartupCerts AsMainVM BoMainState BoMainFacts LazyRestrict LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asiv (p : lin * lin) : siv := (fst p, lcat (fst p) (snd p)).
Definition sivZ (E : env) (s : siv) : Z * Z := (lden E (fst s), lden E (snd s) - lden E (fst s)).   (* [comment removed for export] *)

Fixpoint all_pairs_disjB (bc : bctx) (l : list siv) : bool :=
  match l with [] => true | x :: r => forallb (fun y => disjoint_decB bc x y) r && all_pairs_disjB bc r end.
Definition cross_disjB (bc : bctx) (l1 l2 : list siv) : bool :=
  forallb (fun x => forallb (fun y => disjoint_decB bc x y) l2) l1.
Definition boundsB (bc : bctx) (lo hi : Z) (l : list siv) : bool :=
  forallb (fun s => le_linB bc (lconst lo) (fst s) && le_linB bc (snd s) (lconst hi)) l.

Section CheckSound.
  Variable segs : list Segment.
  Variable E : env.
  Variable M : word -> option byte.
  Variable fk : list kentry.
  Hypothesis KN : know_ok segs E M fk.
  #[local] Notation bc := (mkbc fk).

  Lemma disjoint_decB_soundZ : forall x y, disjoint_decB bc x y = true ->
    lden E (snd x) <= lden E (fst y) \/ lden E (snd y) <= lden E (fst x).
  Proof. intros x y H. rewrite disjoint_decB_eqf in H. exact (disjoint_dec_sound segs E M fk KN x y H). Qed.

  Lemma all_pairs_disjB_sound : forall l, all_pairs_disjB bc l = true -> pairwise_apart (map (sivZ E) l).
  Proof.
    induction l as [|x l IH]; intros H; cbn [all_pairs_disjB map pairwise_apart]; [exact I|].
    apply andb_prop in H as [H1 H2]. unfold sivZ at 1. cbn [fst snd]. split; [|exact (IH H2)].
    apply Forall_map. apply Forall_forall. intros y Hy. cbn [fst snd].
    pose proof (proj1 (forallb_forall _ _) H1 y Hy) as D. apply disjoint_decB_soundZ in D. unfold sivZ. cbn [fst snd]. lia.
  Qed.

  Lemma cross_disjB_sound : forall l1 l2, cross_disjB bc l1 l2 = true ->
    forall x y, In x l1 -> In y l2 -> lden E (snd x) <= lden E (fst y) \/ lden E (snd y) <= lden E (fst x).
  Proof.
    intros l1 l2 H x y Hx Hy. unfold cross_disjB in H.
    pose proof (proj1 (forallb_forall _ _) H x Hx) as H1. pose proof (proj1 (forallb_forall _ _) H1 y Hy) as H2.
    exact (disjoint_decB_soundZ x y H2).
  Qed.

  Lemma boundsB_sound : forall lo hi l, boundsB bc lo hi l = true ->
    Forall (fun s => lo <= lden E (fst s) /\ lden E (snd s) <= hi) l.
  Proof.
    intros lo hi l H. apply Forall_forall. intros s Hs. pose proof (proj1 (forallb_forall _ _) H s Hs) as H1.
    apply andb_prop in H1 as [H1 H2]. rewrite le_linB_eqf in H1, H2.
    apply (le_lin_sound segs E M fk KN) in H1. apply (le_lin_sound segs E M fk KN) in H2. rewrite lconst_den in H1, H2. lia.
  Qed.
End CheckSound.

(* [comment removed for export] *)
Definition STKS : siv := ((-8388608, [(32768, EVar 0); (4096, EVar 6)]), (281474968322048, [(32768, EVar 0); (4096, EVar 6)])).  (* [comment removed for export] *)
Definition HULLS : siv := ((65536, []), (6832128, [])).                   (* [comment removed for export] *)
Definition SHHS : siv := ((2147446784, []), (17594333495296, [])).       (* [comment removed for export] *)
Definition placedB (bc : bctx) (l : list siv) : bool :=
  forallb (fun s => le_linB bc (lconst 4096) (fst s) && le_linB bc (snd s) (lconst (2 ^ 47))
                    && disjoint_decB bc s STKS && disjoint_decB bc s HULLS && disjoint_decB bc s SHHS) l.

Section CheckSound2.
  Variable segs : list Segment.
  Variable E : env.
  Variable M : word -> option byte.
  Variable fk : list kentry.
  Hypothesis KN : know_ok segs E M fk.
  #[local] Notation bc := (mkbc fk).
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
  Lemma placedB_sound : forall l, placedB bc l = true ->
    Forall (fun s => 4096 <= lden E (fst s) /\ lden E (snd s) <= 2 ^ 47
                     /\ (lden E (snd s) <= lden E (fst STKS) \/ lden E (snd STKS) <= lden E (fst s))
                     /\ (lden E (snd s) <= 65536 \/ 6832128 <= lden E (fst s))
                     /\ (lden E (snd s) <= 2147446784 \/ 17594333495296 <= lden E (fst s))) l.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazyChk.placedB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(fk); constr:(@Corelib.Init.Datatypes.true); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@kc__1); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.Forall_forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.lden); constr:(E); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazyChk.STKS); constr:(@Corelib.Init.Logic.proj1); constr:(@Stdlib.Lists.List.forallb); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.le_linB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.lconst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.disjoint_decB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazyChk.HULLS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazyChk.SHHS); constr:(@Stdlib.Lists.List.forallb_forall); constr:(@Corelib.Init.Datatypes.andb_prop); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.le_lin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.le_linB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.le_lin_sound); constr:(segs); constr:(M); constr:(KN); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.lconst_den); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazyChk.disjoint_decB_soundZ); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.OR)|] [|@x; @l; @P; @A; @s; @b; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat7; @__sat6; @__x2; @__x3; @__x4; @H4; @H3; @H2; @H5; @H1; @Hs; @H0; @H|] "#*x#G$;#Y#w###M#_#Q#$$.#%$/$-#&#e#'#l#P#m$3$5#(#}#*#+#t#u#v#]#)#,#-#/#0#1#4#?#@#A#R#j#g#.#2#5#6#q#r#:#s#>#x#B#|#~$$$(#F#K#O#N#G#W#X#b#n#f#3#7#8#9#;#<#=#{$#$&$%$'$*$,$6$7$9$:$8$<$;$>#Z#\#c#L#^#V#`#i#a#d#k#h$1$0#[$2#U#S$+#o#p$)$4#z#J#T#y$=$?@#z%#{$#|$#}&#~%$#%$$&$%&$&&$'%$(&$)%$*'$+*$,$$-%$.&$/($0+$1&$2)$3%$4%$5'$6$$7&$8+$9'$:*;SKUSLRVSM#E&F#Hk##ESN;I<KIE3PEKUPIk##$#k#$N#k##'#3NEIUNIk##$#k#$K#<NKIk##$#()#<PNKk##,#j##%#j##$Ej##.#WSOKIE40*&$#j#%7#j#&9#j#'S8#k#%:.k#&<#k#'S8#VSPCC$S-$#$#$#$#$#$#$#$#$#$#$#1#)CCE'G##%#+CCE'G#14%5%#%#%#1#VSQ(##*#)CCO'G##-#+CCO'G###3,&#$8$#$#$#1##7#%S-$#$#%#%#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#1#%S-$#%#$#$#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#1###s#I,s#2#%s#2%#%#%#%#%#%#%#%#%#%#%#%#$#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#1##s#f#%s#W%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#1###s$.,s#$#(s#D#(s#{#(s$'#(s$2#j#(s$C#3s$DENUS9s$8*s$e#s$8US9s$.*s$gs$7#.%#-s$iEO.$#-s$kEQ.$#-s$mES#.$#j#(s$P#WS:s$Q#P&F#H3s$SES.U&I&F#Hk##%#k#$s$W#k##(#3s$YES&k###'k#$s$[#WS:s$\.S&&F#Hk##%#WSRs$_1PZSS*$#NIE)CCK*s%%?#+CCK*s%'#?.%#-s%)KO.$#-s%+KQ.$#-s%-KS#6$#E&F%H&F%H($#)CCN*s%3s#-#+CCN*s%5#s#-.%#-s%7NO.$#-s%9NQ.$#&F#H-s%<NS#&F#H(%#)CCP'G##s$q#+CCP'G###s$h#$s$f#s$d(,$##'s$_#s$1+,$##*s#o#s#O.,$#(&#(*#(.#(2#j##6#-s%SPS#&F#H)CCS&*s%Vs#P#+CCS&*s%X#s#P.%#-s%ZS&O.$#-s%\S&Q.$#&F#H-s%_S.S#&F#H)CCS(*s%bs#\#+CCS(*s%d#s#\.%#-s%fS(O.$#-s%hS(Q6$#I&F%H&F%H($#)CCS)*s%ns#h#+CCS)*s%p#s#h.%#-s%rS)O.$#&F#H-s%uS)Q&F#H(%#)CCS/'G##s%N#+CCS/'G###s%E#$s%C#s%A(,$##'s%<#s$j+,$##*s$L#s$,.,$#(&#(*#(.#(2#j##6#-s&0S/Q&F#H)CCS0*s&3s$-#+CCS0*s&5#s$-.%#-s&7S0O.$#&F#H-s&:S;Q&F#H)CCS1*s&=s$7#+CCS1*s&?#s$7.%#-s&AS1O6$#I&F%H&F%H($#)CCS2*s&Gs$A#+CCS2*s&I#s$A.%#&F#H-s&LS2O&F#H(%#)CCS3'G##s&%#+CCS3'G###s%x#$s%v#s%t(,$##'s%o#s%A+,$##*s%##s$_.,$#(&#(*#(.#(2#j##6#-s&cS3O&F#H)CCS<*s&fs$`#+CCS<*s&h#s$`.%#&F#H-s&kSTO&F#H)CCS4*s&ns$h#+CCS4*s&p#s$h6%#I&F&H&F%H($#)CCS=*s&vs$p#&F#H+CCS=*s&y#s$q&F#H(&#)CCS>'G##s&R#+CCS>'G###s&I#$s&G#s&E(,$##'s&@#s%n+,$##*s%P#s%0.,$#(&#(*#(.#(2#j##6#*s'43s%,&F#H)CCSU*s'7s%1#&F#H+CCSV*s':#s%2&F#H)CCSW*s'=s%7#&FEHj#)F#WS?Rs%:&WS@Rs%;'7F'%I$#&F%H+CCSA*s'E#s%=WS?R$s%>WS@R%s%?7F%+I$#&F%H)CCSX\SBS*GS+RS,s%E#I'Gs%F'G%#$#+CCSY\SBS*GS+RS,#s%HI'G$'Gs%J#$#)CCSC'G##E#j#*D#VSDGs',7D/$Is'-#)CCSZ'G##s'0#+CCS5'G###Ej#*D#VSDGs')7D2$Is'*#+CCSC'G###s'-=S*GS+RS,S5OS;#+s',)CCS5'G##s',#,&#=S*GS+RS,S6QS4+CCS6'G#)CCQ'G##%#+CCQ'G#)CCS6'G##%#,(#=S*GS+RS,S7S#SA+CCS7'G#)CCS#'G##%#+CCS#'G#)CCS7'G##%#,(#)CCSE'G##s'Z#+CCSE'G###s'Q#$s'O#s'M(,$##'s'H#s&v+,$##*s&X#s&8.,$#(&#(*#(.#VS[s'ds'_VSFS's'e#S's'aVSFS's'ak##$#k##&##S's'jWS\s'ks'fIj##SG#j#+%##S's'hk##SG#k#+(#VS]S's'qVSHS^#m##0UI#US_SI;SI8DIUS`DUSaD2Ds($9DS-/D$S$#0&MJJL#S%USbJ5(MJJL$#$VSc)LVSHFHVSdEK&F#Hm$%#WSeDS'IXSfEK$#l#,*)#l#-32#l#.65#j#/D##s(5E#s(6Ik##$#k#/D#)CCSJ'G#VE#S)l#0*&#l#1As#-#l#2s#)s#&#l#1s#3s#.#2Ds(:USgs(7WShD$#/D@S$#0s##MJJL#S%5s#$MJJL#?#l#,#>8l#-s#(s#'#l#.s#+s#*#j#/D##Es(>#Is(?k##$#k#/D#+CCSJ'G#VE#S(l#0*&#l#1s#6s#B#l#2s#>s#;#l#1s#Hs#C#8DPUSiD>D$K#8DN>D$I#9Ds(f/Ds#8S$#0s#;MJJL#S%9Ds(B9Ds(i/D$S$#0s#?MJJL#S%?s#@MJJL'#5s#AMJJL#s#<#l#,#s#;s#5l#--s#D#l#.s#Hs#G#j#/D#j#3D#j#4D#j#5D##EI#KN,$##IK#NP,$#k##&#k#/D#k#3D#k#4D#k#5D#YEs#=s(cs(fs#(S.l#0/$#l#1s#[s#g#l#2s#cs#`#l#1s#ms#h#8DK>D#Is#'2Ds(c/Ds#ZS$#0s#]MJJL#S%2Ds(7/D#S$s#(0s#`MJJL#S%?s#aMJJL&#5s#bMJJL#s#]#l#,#s#\s#Vl#-,s#e#l#.s#is#h#j#/D#j#3D##Es(p#s(BI,$##Is(s#s(EK,$#k##&#k#/D#k#3D#WEs#Zs#ES&l#0-$#l#1s#xs$(#l#2s$$s#}#l#1s$.s$)#2Ds(//Ds#uS$#0s#xMJJL#S%2Ds'm/D#S$s#C0s#{MJJL#S%?s#|MJJL&#5s#}MJJL#s#x#l#,#s#ws#ql#-s#'s$$#l#.s$(s$'#j#/D#j#3D##Es(<#s'xI,$##Is(?#s'{K,$#k##&#k#/D#k#3D#WEs#us#`Pl#0-$#l#1s$7s$C#l#2s$?s$<#l#1s$Is$D#:s$Qs$N>#:s$Us$Ns#<#:s$Ys$Ns#b#:s$]s$Ns#x#l#6s$ls$a#l#7s$ys$n#l#8s%$s${#l#9s%)s%&#l#:s%3s%0#l#9s%=s%:#l#:s%Cs%@#l#9s%Gs%F#l#:s%Ns%M#j#9s%V#j#:s%Z#V#IEj##s%_#j##s%z#4s%{s%xs%c#El#:s&&s&##j#8s&,#j#:s&/#V#IEj##s&7#j##s&Q#4s&Rs&Ps&;#El#:s&\s&Y#j#7s&d#j#:s&g#V#IEj##s&q#j##s'/#4s'0s'.s&u#El#:s'<s'9#j#6s'F#j#:s'I#V#IEj##s'U#j##s'o#4s'ps'ns'Y#El#:s'~s'{#l#:s(.s(9#j#;s(K#j#(s*2#XEs*3s(NK#l#<s*8s*5#j#=s*R#j#%s*V##"). Qed.
End CheckSound2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KPSk (g : bool) : list (nat * Z) :=
  [(K_B04, 65536); (K_B05, 3727360); (K_B06, 137439023104); (K_B08, 8388608); (K_B09, 4096); (K_B10, 65536); (K_B11, 4096); (K_B12, 4096);
   (K_B16, 11571200); (K_B20 g, 4096); (K_B21 g, 1048576); (K_B22 g, 8388608); (K_B23 g, 4096)]
  ++ (if g then [] else [(K_META, 8192)]).
Definition ksiv (kc : nat * Z) : siv := (pg (fst kc), pgo (snd kc) (fst kc)).
Definition KPS (g : bool) : list siv := map ksiv (KPSk g).
Lemma KPSk_pos : forall g, Forall (fun kc => 0 < snd kc) (KPSk g).
Proof. intros [|]; repeat constructor. Qed.
Lemma ksiv_den : forall E kc, lden E (fst (ksiv kc)) = 4096 * vE E (fst kc) /\ lden E (snd (ksiv kc)) = snd kc + 4096 * vE E (fst kc).
Proof. intros E [k c]. unfold ksiv, pg, pgo, lden. cbn [fst snd tden]. rewrite ?uE_var. lia. Qed.
(* [comment removed for export] *)
Definition KPSX (g : bool) : list siv := KPS g ++ (if g then [(pg 5, pgo 8192 5)] else []).
(* [comment removed for export] *)
Definition APPS (g : bool) : list siv :=
  map asiv (firstn 1 (DG_vis g) ++ skipn 2 (DG_vis g) ++ [(pg K_B13, (4096, []))]).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LZS (g : bool) (cls : nat) : list siv := tl (DG_lazy g).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vis_nwB (bc : bctx) (l : list (expr * expr)) : bool :=
  forallb (fun p => lin_nowrapRB bc (fst p) && lin_nowrapRB bc (snd p)) l.

Definition lz_check (g : bool) (cls : nat) (ch : acs) : bool :=
  let bc := mkbc (kn_arith (kn ch)) in
  all_pairs_disjB bc (KPSX g) && cross_disjB bc (APPS g) (LZS g cls) && placedB bc (KPS g ++ [(pg K_B13, pgo 4096 K_B13)])
  && (if g then has_fact (kn ch) (KRange (EVar 5) 1668 524276) else true)
  && vis_nwB bc (a_vis ch ++ a_ghost ch)
  && list_eqb pair_eqb (a_ghost ch) [(EMd Instr.M_MUL (ELit 4096) (EVar K_B13), ELit 4096)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint evz (e : expr) (acc : list Z) : list Z :=
  match e with
  | ELit _ => acc
  | EVar w => Z.of_nat w :: acc
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evz a (evz b acc)
  | EExt _ _ _ a => evz a acc
  | EBlob _ _ _ _ => acc
  end.
Definition zmem (z : Z) (l : list Z) : bool := existsb (Z.eqb z) l.
Definition zinter (l1 l2 : list Z) : bool := existsb (fun z => zmem z l2) l1.
Definition lin_vz (l : lin) : list Z := flat_map (fun t => evz (snd t) []) (snd l).
Definition lin_hasZ (vl : list Z) (e : expr) (ve : list Z) : bool := match e with ELit _ => true | _ => zinter vl ve end.
Definition kdisj_preZ (vx vr : list Z) (b1 b2 : expr) (vb1 vb2 : list Z) : bool :=
  (lin_hasZ vx b1 vb1 && lin_hasZ vr b2 vb2) || (lin_hasZ vx b2 vb2 && lin_hasZ vr b1 vb1).

Lemma zeqb_of_nat : forall v w, Z.eqb (Z.of_nat v) (Z.of_nat w) = Nat.eqb v w.
Proof. intros v w. destruct (Z.eqb_spec (Z.of_nat v) (Z.of_nat w)) as [E|E]; destruct (Nat.eqb_spec v w) as [F|F]; try reflexivity; exfalso; lia. Qed.
Lemma zmem_evz : forall v e acc, zmem (Z.of_nat v) (evz e acc) = mentions_var v e || zmem (Z.of_nat v) acc.
Proof.
  intros v e. induction e as [z|w|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros acc; cbn [evz mentions_var];
    try reflexivity; try (rewrite IHa, IHb; destruct (mentions_var v a); reflexivity); try (apply IHa).
  unfold zmem. cbn [existsb]. rewrite zeqb_of_nat. reflexivity.
Qed.
Lemma existsb_evz : forall e1 e2 acc,
  existsb (fun z => zmem z (evz e1 [])) (evz e2 acc) = shares_var e1 e2 || existsb (fun z => zmem z (evz e1 [])) acc.
Proof.
  intros e1 e2. induction e2 as [z|w|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros acc; cbn [evz shares_var];
    try reflexivity; try (rewrite IHa, IHb; destruct (shares_var e1 a); reflexivity); try (apply IHa).
  cbn [existsb]. rewrite zmem_evz. cbn [zmem existsb]. rewrite orb_false_r. reflexivity.
Qed.
Lemma existsb_flat_map : forall (A B : Type) (f : B -> bool) (g : A -> list B) l, existsb f (flat_map g l) = existsb (fun a => existsb f (g a)) l.
Proof. intros A B f g l. induction l as [|a l IH]; [reflexivity|]. cbn [flat_map existsb]. rewrite existsb_app, IH. reflexivity. Qed.
Lemma existsb_ext' : forall (A : Type) (f g : A -> bool) l, (forall a, f a = g a) -> existsb f l = existsb g l.
Proof. intros A f g l H. induction l as [|a l IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma lin_has_Z : forall l e, lin_has l e = lin_hasZ (lin_vz l) e (evz e []).
Proof.
  intros l e. unfold lin_has, lin_hasZ, zinter, lin_vz. destruct e; try reflexivity;
    (rewrite existsb_flat_map; apply existsb_ext'; intros t; rewrite existsb_evz; cbn [existsb]; rewrite orb_false_r; reflexivity).
Qed.
Lemma kdisj_pre_Z : forall x r b1 b2, kdisj_pre x r b1 b2 = kdisj_preZ (lin_vz (fst x)) (lin_vz (fst r)) b1 b2 (evz b1 []) (evz b2 []).
Proof. intros. unfold kdisj_pre, kdisj_preZ. rewrite !lin_has_Z. reflexivity. Qed.

Definition kdp : Type := (expr * expr * list Z * list Z * siv * siv)%type.
Definition kdprep1 (bc : bctx) (K : kentry) : list kdp :=
  match K with
  | KDisj a1 n1 a2 n2 =>
      match lin_ofaB bc a1, lin_ofxB bc n1, lin_ofaB bc a2, lin_ofxB bc n2 with
      | Some f1, Some m1, Some f2, Some m2 => [(a_base a1, a_base a2, evz (a_base a1) [], evz (a_base a2) [], (f1, lcat f1 m1), (f2, lcat f2 m2))]
      | _, _, _, _ => []
      end
  | _ => []
  end.
Definition kdprep (bc : bctx) : list kdp := flat_map (kdprep1 bc) (bc_fk bc).
Definition sivz : Type := (siv * list Z)%type.
Definition mksz (x : siv) : sivz := (x, lin_vz (fst x)).
Definition kdisjP1 (bc : bctx) (x r : sivz) (p : kdp) : bool :=
  let '(b1, b2, vb1, vb2, s1, s2) := p in
  if negb (kdisj_preZ (snd x) (snd r) b1 b2 vb1 vb2) then false
  else (insideB bc (fst x) (fst s1) (snd s1) && insideB bc (fst r) (fst s2) (snd s2)) || (insideB bc (fst x) (fst s2) (snd s2) && insideB bc (fst r) (fst s1) (snd s1)).
Definition disjoint_decP (bc : bctx) (prep : list kdp) (x r : sivz) : bool :=
  le_linB bc (snd (fst x)) (fst (fst r)) || le_linB bc (snd (fst r)) (fst (fst x)) || existsb (kdisjP1 bc x r) prep.
Fixpoint all_pairs_disjP (bc : bctx) (prep : list kdp) (l : list sivz) : bool :=
  match l with [] => true | x :: r => forallb (fun y => disjoint_decP bc prep x y) r && all_pairs_disjP bc prep r end.
Definition cross_disjP (bc : bctx) (prep : list kdp) (l1 l2 : list sivz) : bool :=
  forallb (fun x => forallb (fun y => disjoint_decP bc prep x y) l2) l1.
Definition placedP (bc : bctx) (prep : list kdp) (l : list sivz) : bool :=
  let S1 := mksz STKS in let S2 := mksz HULLS in let S3 := mksz SHHS in
  forallb (fun s => le_linB bc (lconst 4096) (fst (fst s)) && le_linB bc (snd (fst s)) (lconst (2 ^ 47))
                    && disjoint_decP bc prep s S1 && disjoint_decP bc prep s S2 && disjoint_decP bc prep s S3) l.

Lemma kdisjP1_eq : forall bc x r K, existsb (kdisjP1 bc (mksz x) (mksz r)) (kdprep1 bc K) = kdisj1B bc x r K.
Proof.
  intros bc x r K. destruct K; try reflexivity. cbn [kdprep1 kdisj1B]. rewrite kdisj_pre_Z.
  repeat match goal with |- context [match ?o with Some _ => _ | None => _ end] => destruct o end;
    cbn [existsb kdisjP1 mksz fst snd]; rewrite ?orb_false_r; try reflexivity;
    match goal with |- context [negb ?b] => destruct b end; reflexivity.
Qed.
Lemma disjoint_decP_eq : forall bc x r, disjoint_decP bc (kdprep bc) (mksz x) (mksz r) = disjoint_decB bc x r.
Proof.
  intros bc x r. unfold disjoint_decP, disjoint_decB, kdisjB, kdprep. cbn [mksz fst snd]. f_equal.
  rewrite existsb_flat_map. apply existsb_ext'. intros K. apply kdisjP1_eq.
Qed.
Lemma forallb_map' : forall (A B : Type) (f : B -> bool) (g : A -> B) l, forallb f (map g l) = forallb (fun a => f (g a)) l.
Proof. intros A B f g l. induction l as [|a l IH]; [reflexivity|]. cbn [map forallb]. rewrite IH. reflexivity. Qed.
Lemma forallb_ext' : forall (A : Type) (f g : A -> bool) l, (forall a, f a = g a) -> forallb f l = forallb g l.
Proof. intros A f g l H. induction l as [|a l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma all_pairs_disjP_eq : forall bc l, all_pairs_disjP bc (kdprep bc) (map mksz l) = all_pairs_disjB bc l.
Proof.
  intros bc l. induction l as [|x l IH]; [reflexivity|]. cbn [map all_pairs_disjP all_pairs_disjB]. rewrite IH, forallb_map'. f_equal.
  apply forallb_ext'. intros y. apply disjoint_decP_eq.
Qed.
Lemma cross_disjP_eq : forall bc l1 l2, cross_disjP bc (kdprep bc) (map mksz l1) (map mksz l2) = cross_disjB bc l1 l2.
Proof.
  intros bc l1 l2. unfold cross_disjP, cross_disjB. rewrite forallb_map'. apply forallb_ext'. intros x. rewrite forallb_map'.
  apply forallb_ext'. intros y. apply disjoint_decP_eq.
Qed.
Lemma placedP_eq : forall bc l, placedP bc (kdprep bc) (map mksz l) = placedB bc l.
Proof.
  intros bc l. unfold placedP, placedB. cbv zeta. rewrite forallb_map'. apply forallb_ext'. intros s. cbn [mksz fst snd].
  fold (mksz s). rewrite !disjoint_decP_eq. reflexivity.
Qed.

Definition lz_checkP (g : bool) (cls : nat) (ch : acs) : bool :=
  let bc := mkbc (kn_arith (kn ch)) in
  let prep := kdprep bc in
  all_pairs_disjP bc prep (map mksz (KPSX g)) && cross_disjP bc prep (map mksz (APPS g)) (map mksz (LZS g cls))
  && placedP bc prep (map mksz (KPS g ++ [(pg K_B13, pgo 4096 K_B13)]))
  && (if g then has_fact (kn ch) (KRange (EVar 5) 1668 524276) else true)
  && vis_nwB bc (a_vis ch ++ a_ghost ch)
  && list_eqb pair_eqb (a_ghost ch) [(EMd Instr.M_MUL (ELit 4096) (EVar K_B13), ELit 4096)].
Lemma lz_checkP_eq : forall g cls ch, lz_checkP g cls ch = lz_check g cls ch.
Proof. intros g cls ch. unfold lz_checkP, lz_check. cbv zeta. rewrite all_pairs_disjP_eq, cross_disjP_eq, placedP_eq. reflexivity. Qed.

Lemma HS_lz_check : forall h ch, HSF_both h = Some ch -> lz_check (hole_granted h) (hole_class h) ch = true.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_both_table fold_right fst snd] in Hh.
  do 6 (destruct Hh as [[-> ->]|Hh]; [rewrite <- lz_checkP_eq; vm_cast_no_check (@eq_refl bool true)|]).   (* [comment removed for export] *)
  destruct Hh.
Qed.

Lemma vis_nwB_sound : forall segs E M fk l, know_ok segs E M fk -> vis_nwB (mkbc fk) l = true ->
  map (fun p => (uE E (fst p), uE E (snd p))) l = map (fun p => (lden E (lin_of (fst p)), lden E (lin_of (snd p)))) l.
Proof.
  intros segs E M fk l KN H. apply map_ext_in. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) H p Hp) as H1. apply andb_prop in H1 as [H1 H2]. rewrite lin_nowrapRB_eqf in H1, H2.
  unfold uE. rewrite (lin_nowrapR_sound segs E M fk _ KN H1), (lin_nowrapR_sound segs E M fk _ KN H2). reflexivity.
Qed.

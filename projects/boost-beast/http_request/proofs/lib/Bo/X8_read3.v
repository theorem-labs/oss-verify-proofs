(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_A_kit4 X8_S_kit3 X8_R_read X8_R_readB X8_read_stmt X8_read2.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma put_X_Forall : forall (Q : Z * Z -> Prop) m P S L ns ls em b es insz E,
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz ->
  Q (P, P + 242) -> Q (E, E + 24) -> Q (AG_HTTP_CAT, AG_HTTP_CAT + 64) -> Q (AG_FIELD_TABLE, AG_FIELD_TABLE + 3456) ->
  (forall e d, em !! e = Some d -> Q (e, e + 48)) ->
  (forall x s, In (x, s) es -> Q (x, x + 24 + s)) ->
  Forall Q (put_X P E L es).
Proof.
  intros Q m P S L ns ls em b es insz E FC MB Q1 Q2 Q3 Q4 QL QB. unfold put_X.
  constructor; [exact Q1|]. constructor; [exact Q2|]. constructor; [exact Q3|]. constructor; [exact Q4|].
  apply Forall_app. split.
  - unfold elemsW. apply Forall_forall. intros [u v] IN. apply in_map_iff in IN. destruct IN as (e & Euv & INe). injection Euv as <- <-.
    pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
    destruct (proj1 (DOM e) ltac:(apply (proj2 (list_elem_of_In _ _)); exact INe)) as [d Hd]. exact (QL e d Hd).
  - clear - QB. induction es as [|[x s] es IH]; [constructor|]. cbn [mb_elemsW]. constructor; [apply QB; left; reflexivity|].
    apply IH. intros x' s' IN. apply QB. right. exact IN.
Qed.

(* [comment removed for export] *)
Lemma em_elem_facts : forall m P S L ns ls em e d,
  AFieldsC m (P + 80) S L ns ls em -> em !! e = Some d -> 0 < e /\ 60 <= esize d /\ e + esize d <= aceil /\ aapp e (esize d) /\ AIMG_TOP <= e.
Proof.
  intros m P S L ns ls em e d FC Hd. pose proof FC as (_ & _ & _ & _ & _ & _ & _ & _ & [EM1 _] & _).
  destruct (EM1 e d Hd) as (K0 & _ & K1 & _ & K2 & _). pose proof (esize_ge d). pose proof (aapp_bounds _ _ K2 ltac:(lia)) as (B1 & _). repeat split; try assumption; lia.
Qed.
Lemma mb_elem_facts : forall m b es insz x s,
  AMBuf m b es insz -> In (x, s) es -> 0 < x /\ 0 <= s /\ s + 24 <= mb_block_size s /\ x + mb_block_size s <= aceil /\ aapp x (mb_block_size s) /\ AIMG_TOP <= x.
Proof.
  intros m b es insz x s MB IN. destruct (mb_addr_ok_elem _ _ _ _ (AMBraw_addr_ok _ _ _ _ _ _ _ (proj1 MB)) IN) as (K0 & _ & S0 & S24 & _ & XT & XCE & _ & AP & _).
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma put_X_hi : forall m P S L ns ls em b es insz E A k,
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz -> aapp P PARSER_SIZE -> aapp E 24 -> aceil <= A ->
  Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) (put_X P E L es).
Proof.
  intros m P S L ns ls em b es insz E A k FC MB APP APE HA. pose proof aceil_facts as (AF1 & _).
  pose proof (aapp_bounds _ _ APP ltac:(unfold PARSER_SIZE; lia)) as (_ & P2 & _). pose proof (aapp_bounds _ _ APE ltac:(lia)) as (_ & E2 & _). unfold PARSER_SIZE in P2.
  eapply put_X_Forall; [exact FC| exact MB| | | | | |]; cbn [fst snd].
  - right. lia. - right. lia. - right. unfold AG_HTTP_CAT. lia. - right. unfold AG_FIELD_TABLE. lia.
  - intros e d Hd. destruct (em_elem_facts _ _ _ _ _ _ _ _ _ FC Hd) as (_ & G & K & _). right. lia.
  - intros x s IN. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & _ & S24 & K & _). right. lia.
Qed.

(* [comment removed for export] *)
Lemma put_X_obj : forall m P S L ns ls em b es insz E O n,
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz ->
  (O + n <= P \/ P + 242 <= O) -> (O + n <= E \/ E + 24 <= O) -> AIMG_TOP <= O ->
  elems_off em O n -> body_off es O n ->
  Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) (put_X P E L es).
Proof.
  intros m P S L ns ls em b es insz E O n FC MB DP DE OT EO BO.
  eapply put_X_Forall; [exact FC| exact MB| | | | | |]; cbn [fst snd].
  - exact DP. - exact DE. - right. unfold AG_HTTP_CAT, AIMG_TOP in *. lia. - right. unfold AG_FIELD_TABLE, AIMG_TOP in *. lia.
  - intros e d Hd. destruct (em_elem_facts _ _ _ _ _ _ _ _ _ FC Hd) as (_ & G & _). destruct (EO e d Hd); [left| right]; lia.
  - intros x s IN. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & _ & S24 & _). destruct (BO x s IN); [left| right]; lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma put_X_img : forall m P S L ns ls em b es insz E A k,
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz -> aapp P PARSER_SIZE -> aapp E 24 -> A + k <= AG_HTTP_CAT ->
  Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) (put_X P E L es).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.gmap.gmap); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.Z_countable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.node); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.lnode); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_fields.elt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_mbuf.mbe); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_fields.AFieldsC); constr:(HCEIL); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_mbuf.AMBuf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_put_stmt.PARSER_SIZE); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_bounds); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@kc__1); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_put_stmt.put_X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read3.HCW.put_X_Forall); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_FIELD_TABLE); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap_lookup); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read3.HCW.em_elem_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_fields.esize); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read3.HCW.mb_elem_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.mb_block_size)|] [|@__ff; @__varmap; @__wit; @__arith; @iv; @__x1; @__x2; @__x3; @K; @_H2; @H0; @_H1; @_H0; @_H; @a; @Hd; @d; @e; @_H3; @IN; @s; @x; @E1; @P1; @HA; @APE; @APP; @MB; @FC; @k; @A; @E; @insz; @es; @b; @em; @ls; @ns; @L; @S; @P; @m|] "#+q#M$C#Q#[###$#3#%#r#n#~#4#.#&#/#+#)#1#*#'#o#0#m#6#-#5#7#($%#8#X#,#c#2#s#t#:#=#<#;#T#U#e#@#G#9#`#h#>$>#D#H#K#x#y#z#f$4$5$2$8$7#A#?#F#V#W#Y#Z#a#g#i#j#l#u#w#{#|#v$#$&$)$1$6$0$;$<$?$A$@$B$C#C#B$E$F#J#L$.#P#d#}#\#^#b$$$*$G#_$D#]$'$+$,$=#q#p#k$/$9#R#S$-$($3$:>$)%$*%$+%$,$$-&$.%$/%$0$$1$$2$$3$$4($5&$6&$7'$8%$9'$:*$;&$<+#%($=$$>'$?'$@&$A%$B%8C9CS9S:SR9CS9S:SS9CS9S:S/8ST&S?+#&#&#&#&#-#%M#\SUDO#S)S0PS#QYSVDS&QS,S$'DS&S1+S?&#&#&#-#'DS,#%S,S$##S;USWS@8S@USXCUSYCUSZC2CI+9+#&#&#&#-#2C#3C*S3#4,S'JJS%#S4VS[-S%VS\SFSGVS]EHWSHSF#SGm$%#WS^CIFXS_EH$#l#$*)#l#%76#l#&:9##I0l#'$#Em##$#IS1m#$#YSIDGS1H##KG%GS1US`D#$#(%S-(IGUSaD#'#$%#$'#$)#$-##KL%LS1##.($S-(IL$#,$%#$'#$*#VSbCC%S0P/CCE#$#0CCE##S0)%#j#()#:S*S0GM;+$#j##-#%S*S1##A($S-(IS*$#?$%#$'##KS(%S+S1##s#)($S-(IS+$#s#'$%#$'#2Cs#T3Cs#LS3#4s#NS'JJS%#S4l#$#s#Ds#>l#%s#Rs#Q#l#&s#Us#T##Is#Zl#'$#Em##$YSIDOs#]Q##KO%Os#_##s#;($S-(IO$#s#9$%#$'#$*##KS&%S&s#h##s#D($S-(IS&$#s#B$%#$'#$*#%RS&##s#7#s#6R)$#j#(s#<#:S5RS.G;s#>$#j##*#%Rs#x##s#T($S-(IR$#s#R$%#$'##KS2%Gs$$##s#\($S-$#s#X$%#%LG##s#L#s#KL)$#j#(s#Q#%GS2##S6+s$4+#&#&#+#&#-#%S6###GUSJSKUSJ#<C#<C%<CSKWSLC$#WSLC&#VSc#SdWSeS@#s$=VSMCHVSMCNXSNC$F#+s$G+#&#&#+#&#&#&#&#&#&#&#&#&#&#&#&#&#&#-#+S?&#+#&#&#&#&#+#&#&#&#&#&#&#&#&#&#&#&#&#&#&#-#&8+#&#+#+#+#+#+#+#+#+#&#+#+#&#+#&#&#&#&#-#+-&#&#&#+#&#&#&#&#-#2CB=Cs%83C$S3#4s%.S'JJS%#S4USfJ=CS?=Cs%HWSgC$#&s#Q&#&#&#&#&#&#+#&#&#+#&#&#&#&#-#2Cs#%3C4S3#4s%ES'JJS%#S43C6S3<4s%GS'JJS%#S46s%HS'JJS%%;#6s%IS'JJS%=<#l#$#s%?s%9l#%s#ms%L#l#&s#qs%O#j#)C#j#*C#j#+C##s#GH%FH##s#4%HN##S$k##%#k##(#k#)C#k#*C#k#+C#7SAGLS#Ml#'.$#m##s$75s$8s$/#1CCS6s$1/CC##s$<#0CC%##G)%#m#)##s$AL%Ls%n##G7S*GLHMl#'<2#m##'5(&#1CCL(/CC##s$J#0CC%##G)%#m#)##s$OS;&s&/&#&#&#&#-#%S;###GXSNCs$DFs%~6s%}S'JJS%s#:s#Ps#:l#$#s%ss%ml#%%s&$#l#&s&(s&'#j#)C#j#*C#%EF##s#fk###s#5k#)C#k#*C#WEGLMl#')$##s$fs#lm#$#m##;5<4#1CCS;6/CC##s$l#0CC%##G)%#m#)##s$qSB+s&E+#&#&#&#&#&#&#&#-#%SB###G+s#j&#+#&#&#&#&#-#2Cs$&3Cs#{S3#4s&PS'JJS%#S46s&QS'JJS%s#js$$#l#$#s&Gs&Al#%s#5s&T#l#&s&Xs&W#j#)C#j#*C##s#ds$/k##s#2#k#)C#k#*C#l#''#s#1#s%8s$4m#$#m##s#'5s#(<#1CCSB>/CC##s%>#0CC%##G)%#m#)#UShS/XSiCS9S:S/ZSjCS/s'&#FS5VSkS/EWSH&$#_SlSOS<SPSAS6S7S8HFLE(IH-s%E,F#$#%H$##s&U'DH&#KH$$#$&#$)#$-#(IN,H#/#%N$##s&`'DN&#KN$$#$&#$)#$,#%S.S+##S$&s'3-#%S$###S.)'#j##*#,N#A#%S$$##s&r'DS$&#KS$$$#$&#$)#(IS,,S,#s#+#%Q$##s&|'DQ&#KQ$$#$&#$)#,Q#s#4#%S#$##s')'DS#&#KS#$$#$&#$)#%S7S8##P%Ps#%##S7)%#j##(#,S#%P###s'7'DP%#KP$$#$&#,P#s#J#,S0%S)###s'@'DS)%#KS)$$#$&#,S)%M###s'G'DM%#KM$$#$&#%S<SP##O%Os#B##S<)%#j##(#,M'DO#$#s&y,O%S&###s'W,S&'DR##KR$$#,R'DS2#$#s&b%SCSm##G%Gs#U##SC)%#j##(#,G'DL##KS*%S=SQ##S(%S(s#^##S=7S+S=SDFSnl#'s%=s%3#m##'5(&#j#,+#j#--#V#FEj##s'u#j##9#.:s&y3#Ej#.=#j#/B#V#FEj##s#'#j##s#5#.s#6s#3s#,#Ej#.s#:#j#0s#B#V#FEj##s#F#j##s#[#.s#\s#Vs#O#Ej#.s#_#j#1s#i#V#FEj##s#l#j##s$,#.s$-s$$s#w#El#2s$;s$/#j#3s$=#j#4S/#j#5C#%S(S*%Hs$%1CCH#/CC##&#0CC%##S()%#k##s$H#k#4S/#k#5C#m#.#1CCFEWSos(*#S.\SpSOS5S>S.HFGE#IF%Fs(e*F#$#%H$##s(D'DH&$#s$M$%#$(#$,#$s$X##IH%Hs(q*H#$#%N$##s(P'DN&$#s$N$%#$(#$,#$s$X#%S$s(|%#N##S.)s$P#j##'##IN%Ns)&*N#$#%S$$##s(a'DS$&$#s$M$%#$(#$,##IS,%S,s)1*S,#$#%Q$##s(l'DQ&$#s$N$%#$(#$,##IQ%Qs)<*Q#$#%S#$##s(w'DS#&$#s$P$%#$(#$,#%Ps)F%#S###S7)s$R#j##'#%S#s)K*S##$#%P$##s)*'DP&$#s$Q$%#$(##IP%S0s)U*S0#$#%S)$##s)4'DS)&$#s$R$%#$(#%S)s)^*S)#$#%M$##s)='DM&$#s$T$%#$(#%s(fM##S<)s$U#j##&#*M%O###s)H'DO%$#s(o$%#*O#s(q#*S&%R###s)P'DR%$#s$V$%#*R%S2###s)V'DS2%$#s(\$%#%s(]S2##SC)s$Z#j##&#*S2'DG#$#s)b*G%L###s)c*L'DS*#$#s$]*S*'DS(#$#s)D%SDS=##S+%S+s*5%#S(##SD)&#j##)##KS+*S+'DS.##KS>%SESq##S5%S5s*@%#S>##SE7S8SESrFSQl#'s'Ks'A#m##(5)&#j#,,#j#6.#V#FEj##2#j##<#.=s)^5#Ej#.@#j#-s#$#V#FEj##s#)#j##s#4#.s#5s#3s#.#Ej#.s#9#j#/s#@#V#FEj##s#D#j##s#U#.s#Vs#Qs#L#Ej#.s#Z#j#0s#d#V#FEj##s#g#j##s$$#.s$%s#xs#r#Ej#.s$'#j#1s%}#V#FEj##s$5#j##s&@#.s&As$Hs$B#El#2s$`s$T#j#7s$b#j#8C#j#9C#%s$VF1CCH#/CC##s$u#0CC%##S()%#k##s$l#k#8C#k#9C#m#-#hSss)ISAS6S7S8S5S>S.S+S(S*LRS&s'fs'Xs'6s&ds$r#:S6LS8S(;s*>s)K#m#%#j#1s)R#j#:s)X#V#FEj##s)[#j##s)s#.s)ts)ms)d#El#.s*#s)v#j#1s*.#j#;s*6#V#FEj##s*9#j##s*T#.s*Us*Ns*B#El#.s*cs*W#j#<s+'#j#=s+*#j#>s+1#j#?s+3#j#@s+5#j#AC#j#BC#j#CC#j#DC#j#Es+C#j#FC#j#Gs+F#j#Hs+H#j#Is+J#j#Js+L#j#Ks+M#j#LC#j#MSt##"). Qed.

(* [comment removed for export] *)
Lemma put_X_noshadow : forall m P S L ns ls em b es insz E,
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz -> aapp P PARSER_SIZE -> aapp E 24 ->
  Forall noshadow (put_X P E L es).
Proof.
  intros m P S L ns ls em b es insz E FC MB APP APE.
  pose proof (aapp_not_shadowland _ _ APP) as NP. pose proof (aapp_not_shadowland _ _ APE) as NE. unfold PARSER_SIZE in NP.
  eapply put_X_Forall; [exact FC| exact MB| | | | | |]; unfold noshadow; cbn [fst snd].
  - clear - NP. lia. - exact NE. - left. unfold AG_HTTP_CAT, ALOWSH_LO. lia. - left. unfold AG_FIELD_TABLE, ALOWSH_LO. lia.
  - intros e d Hd. destruct (em_elem_facts _ _ _ _ _ _ _ _ _ FC Hd) as (_ & G & _ & AP & _). pose proof (aapp_not_shadowland _ _ AP). lia.
  - intros x s IN. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & _ & S24 & _ & AP & _). pose proof (aapp_not_shadowland _ _ AP). lia.
Qed.

(* [comment removed for export] *)
Lemma put_X_fbblk : forall m P S L ns ls em b es insz E (FB : fbv),
  AFieldsC m (P + 80) S L ns ls em -> AMBuf m b es insz ->
  (P + PARSER_SIZE <= fb_begin FB \/ fb_end FB <= P) -> (E + 24 <= fb_begin FB \/ fb_end FB <= E) -> AIMG_TOP <= fb_begin FB ->
  (forall e, e ∈ L -> e + 48 <= fb_begin FB \/ fb_end FB <= e) ->
  (forall x s, In (x, s) es -> x + 24 + s <= fb_begin FB \/ fb_end FB <= x) ->
  Forall (fun iv : Z * Z => fb_end FB <= fst iv \/ snd iv <= fb_begin FB) (put_X P E L es).
Proof.
  intros m P S L ns ls em b es insz E FB FC MB DP DE BT DL DB.
  pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
  eapply put_X_Forall; [exact FC| exact MB| | | | | |]; cbn [fst snd].
  - unfold PARSER_SIZE in DP. lia. - lia. - right. unfold AG_HTTP_CAT, AIMG_TOP in *. lia. - right. unfold AG_FIELD_TABLE, AIMG_TOP in *. lia.
  - intros e d Hd. destruct (DL e ltac:(apply (proj2 (DOM e)); rewrite Hd; eexists; reflexivity)); lia.
  - intros x s IN. destruct (DB x s IN); lia.
Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma fb_window : forall s0 LB LF m a FB ds,
  as_RHEAP H s0 LB m -> AFlatBuf LB m a FB ds -> FB <> FB_empty ->
  bytes_at bsegs m (fb_in FB) ds
  /\ aobj LB LF (fb_in FB) (zlength ds) /\ accessible m (fb_in FB) (zlength ds) /\ shvis m (fb_in FB) (fb_in FB + zlength ds)
  /\ (exists pf, In (pf, fb_begin FB, fb_cap FB) LB) /\ 0 < fb_begin FB /\ 0 < fb_cap FB /\ AIMG_TOP <= fb_begin FB /\ fb_end FB <= aceil
  /\ aapp (fb_begin FB) (fb_cap FB)
  /\ fb_begin FB <= fb_in FB <= fb_out FB /\ fb_out FB <= fb_last FB <= fb_end FB /\ zlength ds = fb_size FB.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.as_St); constr:(H); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.fframe); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fbv); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.as_RHEAP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AFlatBuf); constr:(HCEIL); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.FlatBufCells); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_ok); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prelim.zlength); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_size); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.FB_empty); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_begin); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_in); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_end); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_out); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_cap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8SRKit.aobj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.accessible); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_last); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rblock_range); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False_ind); constr:(@kc__3); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wr_at); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_bytes); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Logic.True); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.SysStep.rw_cells_bytes_at); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.app); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_app); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_bounds); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8SRKit.aobj_block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable_accessible); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis_sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsCXXHeap.ah_blk_shvis); constr:(HH); constr:(@Corelib.Init.Logic.ex_intro); constr:(@kc__3 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr))|] [|@junk; @pre; @pf; @p; @K; @l; @bs2; @bs1; @a; @m; @segs; @n; @x; @y; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__p1; @__p2; @__arith; @z5; @H5; @z4; @H4; @cstr1; @cstr0; @cstr; @L0; @z; @__x4; @__x5; @__x6; @Ha; @__sat6; @__sat7; @_H; @AF1; @H0; @T1; @BY; @L3; @L2; @L1; @_H0; @WF; @BCH; @e; @BCE; @BAP; @B0; @S2; @S1; @CP; @RB; @INf; @NE; @ADR; @BLK; @SZ; @FOK; @FBC; @RH; @ds; @FB; @LF; @LB; @s0|] "#L6$I&&$R$~##$y%]$i$]#$$Z%5%^%\#%%$#&#'#(#)%1%h#*$S#,$e#-#:#.#4%i#0#@#+#2#8#<#=#A#D#9#E#`%6#1#7#>#I#b#c#i$8#/#5#6#;#B#F#J#S#d#f#h#g#k#m#l#y#~$k$I#3#H#O#[#n#p#u$%%G$.#W#]#^#e#j#o#q#s#t#x#|$)%M$=#?#L#_#a#{$'$2%`$3$5$:$6$;#C#N%.%-#Q#U#V#Z#z#}$$$($+$/$0$1%O%X%g$9$N$`#K#R#Y#r#w$&$*%N%V%f%l$7%w$A$F$W#G#T#X%2%0%4$#$-%P$4$,$?$M$U$q#M#P#\#v$a$x%Q%a%j%v$<$@%,$T$^${%/%3%8%R%S%o%p$>$B$C$D$H$L$O$P$X$Y%%%+%7%:%;%<%=%A%D%E%C%J%I%U%T%Y%[%_%k%m%q%r%n%>%s%u%t%x%z%{$E%}%~&#&$%|&&&'&%&(%($Q$_%#$l$g$}$h$o$j$p$m$n$|$f$t$V$s%'%&%e$z$b$c$v$w$u%B%?%c%b$[$\%Z%9$d%y%@$r%H%K%)%*%F%L%W%dU%U%%V%%W%$j&%X$%Y%%Z&%[$%\%%]$%^$#f$%_%$k%%`'%a%%b'%c$%d$#5$%e$%f&%g$%h&%i%%j$%k&%l&%m'%n%%o%%p'%q*%r(%s'%t+%u&%v$%w'%x/%y&%z'%{$%|&%}%%~/&#%#%'&$'&%%UTrTSUT5TsUT5Tt4TF4#4#UTT#UTc#UT5#XTuTSS$S#QZTvKS$RQOJUTdQEIS#R#WT6KS'Q;)O<Q&C$#&S(QS*H#'S$-S$%#$.#+#J/3S#+#S#*S$,S$%$#.#+#EUTUH)H$#)H*#)H-#EIS22#j#$>#2?#j#%@#2A#k##8#'R5RKS$$#k##<##'##@##s#$##s#&#&S(RS*H#-S#3IS'#R;s#0R?S)S2%#=S'&$0'%>S'(#VTeFCVTe#C1FCEs#+5S$1&C$#:&#S+j#&F#2F#'S#(D#5S#(D#$P&*S#UTwK$$#8K*($+:,S#$<##%#7S#$&#$$,#$#<S#&CA##%##*##/##1##5##7##:##=##s#&##s#)##s#+##s#.#k##s#1#j##s#4#WT6KS2R;s#_Q<R&C$#'S'-S'%#$.#+#J/s#gS$+#S$*S',S'%$#.#+#E)H#s#V)H)#)H,#EIS)1#j#$s#q#2s#r#j#%s#s#2s#t#k##s#K#KS's#<s#:k##s#M##%##;##?#UTdS#EIS'S$#WT6KS+S$;s$#S#<S$&C$#&S(S$S*H#'S)-S)%#$.#+#J/s$-S2+#S2*S),S)%$#.#+#E)H#s#x)H)#)H,#EIS-1#j#$s$7#2s$8#j#%s$9#2s$:#k##7#5S'KS)s#:#k##:##&##>##B#WT6KS-S';s$DS$<S'&C$#&S(S'S*H#'S+-S+%#$.#+#J/s$NS)+#S)*S+,S+%$#.#+#E)H#s$=)H)#)H,#EISE1#j#$s$X#2s$Y#j#%s$Z#2s$[#k##7#'S25S2KS+$#k##;##'##?##s###&S(S2S*H#3IS-s#@S2;s$hS2?S0SEs#B#=S-s#C$0s#D%>S-s#E#1FCEs#&5S+1s$<C$#:s$<#S=j#&F#2F#(Ds#M5S)(D#$Ps#P$s#Js$68Ks#R&$s#Ss#R$s#Ss#L#$#7S)$s#O#$$s#Q#$#<S)&C;##%##*##.##0##2##4##7##9##@##s####s#%##s#(#k##s#*#j##s#-#;s%4S'<S2&C$#'S--S-%#$.#+#J/s%<S++#S+*S-,S-%$#.#+#E)H#s%+)H)#)H,#EIS01#j#$s%F#2s%G#j#%s%H#2s%I#k##s#C#KS-s$&s#6k##s#E##%##;#WT6KS0S);s%QS)<S+&C$#&S(S+S*H#'S0-S0%#$.#+#J/s%[SE+#SE*S0,S0%$#.#+#E)H#s%J)H)#)H,#EIS31#j#$s%e#2s%f#j#%s%g#2s%h#k##7#5S-KS0s#7#k##:##&##>#;s%pS+<S-&C$#&S(S-S*H#'S=-S=%#$.#+#J/s%zS0+#S0*S=,S=%$#.#+#E)H#s%i)H)#)H,#EISX1#j#$s&(#2s&)#j#%s&*#2s&+#k##7#'SE5SEKS=$#k##;##'##?#&S(SES*H#3IS3s#=SE;s&7SE?S.SXs#?#=S3s#@$0s#A%>S3s#B#1FCEs#%5S=1s%gC$#:s%g#SFj#&F#2F#(Ds#J5S0(D#$Ps#M$s#Gs%a8Ks#O&$s#Ps#O$s#Ps#I#$#7S0$s#L#$$s#N#$#<S0&C;##%##*##.##0##2##4##7##9##@##s####s#%##s#(#k##s#*#j##s#-#'S3-S3%#$.#+#J/s&dS=+#S=*S3,S3%$#.#+#E)H#s&S)H)#)H,#EIS.1#j#$s&n#2s&o#j#%s&p#2s&q#k##s#@#KS3s#|s#3k##s#B##%#&S(S=S*H#'S.-S.%#$.#+#J/s&~SX+#SX*S.,S.%$#.#+#E)H#s&m)H)#)H,#EISG1#j#$s',#2s'-#j#%s'.#2s'/#k##7#5S3KS.s#2#k##:##&#&S(S3S*H#'SF-SF%#$.#+#J/s'=S.+#S.*SF,SF%$#.#+#E)H#s',)H)#)H,#EIS>1#j#$s'G#2s'H#j#%s'I#2s'J#k##7#'SX5SXKSF$#k##;##'#&S(SXS*H#3ISGs#8SX;s'USX?S4S>s#:#=SGs#;$0s#<%>SGs#=#1FCEs#$5SF1s')C$#:s')#S9j#&F#2F#(Ds#E5S.(D#$Ps#H$s#Bs'#8Ks#J&$s#Ks#J$s#Ks#D#$#7S.$s#G#$$s#I#$#<S.&C;##%##*##.##0##2##4##7##9##@##s####s#%##s#(#k##s#*#j##s#-#KSGs#b>k##s#-#&S(S.S*H#'S>-S>%#$.#+#J/s(*SG+#SG*S>,S>%$#.#+#E)H#s'u)H)#)H,#EIS91#j#$s(4#2s(5#j#%s(6#2s(7#k##7#&S(SFS*H#'SG5SGKS4$#k##&#&S(SGS*H#&S(S>S*'S41FCE#5S41s'oC$#:s'o#S5NK'%(D&-S4$*#,S4$%##%#7S4$&#*S4$%##%##(##.##0##2#j#'F#2F#O:#3IS,3S>;s(\S>?S5SH5#=S,6$07%>S,8#'S91FCE#5S91s(1C$#:s(1#S6j#&F#2F#(Ds#'$Ps#($;s()8Ks#*s#(<S4&C3##=##s####'##)##+##s#,##.##0##8##;##=##@#j##B#&S(S4S*-S93ISH#S4;s(~S4?S6S5%#=SH&$0'%>SH(#'S,1FCE#5S,1s(SC$#:s(S#S?j#&F#2F#(Ds#+(Ds#*$Ps#-*S9$#s(M8Ks#0s#.$s#16,S9$8##%#7S9$&#$$+#$#<S9&C=##%##*##/##1##4##6##8##:##B##s#%##s#'##s#*#UOEVTx$#j#(s#/#U#Ej##s#j#NKs#Ls#J#;7#s#$##%##s#L#j#'F#2F#NKs#1s#/(Ds#0-S,$s#4#,S,$%##%#7S,$&#*S,$%##%##(##.##0##s#<#j#'F#2F#3IS52S9;s)iS9?S?S64#=S55$06%>S57#'SH1FCE#5SH1s)>C$#:s)>#Spj#&F#2F#(Ds#P$Ps#Q$:s)68Ks#Ss#Q<S,&C3##<##B##'##)##+##s#+##.##0##8##;##=##@#j##B#NK<:(D;-SH$?#,SH$%##%#7SH$&#*SH$%##%##(##.##0##s#'#j#'F#U#E'S51FCE#5S51s)jC$#:s)j#S1NK'%(D&-S5$*#,S5$%##%#7S5$&#*S5$%##%##(##.##0##2#'S61FCJ#5S61s*#C$#:s*##S7NK'%(D&-S6$*#,S6$%##%#7S6$&#*S6$%##%##(##.##0##2#-S?3IS1#S6;s*jS6?SIS7%#=S1&$0'%>S1(#'Sp1FCE#5Sp1s*?C$#:s*?#S}j#&F#2F#'S?(D#5S?(D#$P&*S?$#s*;8K)'$*8,S?$:##%#7S?$&#$$+#$#<S?&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#NKA?#73#@##%#1FCQs#,1s*gC#s#+:s*g#S}'S15S1NK$#(D$-S1$'#,S1$%##%#7S1$&#*S1$%##%##(##.##0#'S75S7NK$#(D$-S7$'#,S7$%##%#7S7$&#*S7$%##%##(##.##0#-SI3IS8#S7;s+dS7?SJS:%#=S8&$0'%>S8(#'S}1FCE#5S}1s+9C$#:s+9#TGj#&F#2F#'SI(D#5SI(D#$P&*SI$#s+58K)'$*8,SI$:##%#7SI$&#$$+#$#<SI&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/##62#?#NKs#*s#(5S8(D#'S8-S8$$#,S8$%##%#7S8$&#*S8$%##%##(##/#5S:(D#'S:-S:$$#,S:$%##%#7S:$&#*S:$%##%##(##/#-SJ3ISY#S:;s,VS:?SKS@%#=SY&$0'%>SY(#'TG1FCE#5TG1s,+C$#:s,+#T7j#&F#2F#'SJ(D#5SJ(D#$P&*SJ$#s,'8K)'$*8,SJ$:##%#7SJ$&#$$+#$#<SJ&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/##62(Ds#''SY-SY$$#,SY$%##%#7SY$&#*SY$%##%##(#'S@-S@$$#,S@$%##%#7S@$&#*S@$%##%##(#-SK3ISq#S@;s-AS@?S~TV%#=Sq&$0'%>Sq(#'T71FCE#5T71s,rC$#:s,r#SZj#&F#2F#'SK(D#5SK(D#$P&*SK$#s,n8K)'$*8,SK$:##%#7SK$&#$$+#$#<SK&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#-T7$s#)#,T7$%##%#,Sq7Sq$$#*Sq$%##%#'TV5TVNK$#'S~(D#4s-~UT##VT$&#&C#D5S~$D#8K*$0+%$#s-C#%##'##*##/#-SZ3IT%#S~;s./S~?SLT8%#=T%&$0'%>T%(#'TW1FCE#5TW1s-`C$#:s-`#THj#&F#2F#'SZ(D#5SZ(D#$P&*SZ$#s-\8K)'$*8,SZ$:##%#7SZ$&#$$+#$#<SZ&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#VT$As#;&C#D$DA0s#$B$#s-y#?##&##(#(Ds#0'T%VT$#s#E&C#D5T%$D#8K'$0(%$#s.)#%##'##*#'T8VT$#s#P&C#D5T8$D#8K'$0(%$#s.4#%##'##*#-SL3IT&#T8;s.{T8?SbT'%#=T&&$0'%>T&(#'TH1FCE#5TH1s.PC$#:s.P#TIj#&F#2F#'SL(D#5SL(D#$P&*SL$#s.L8K)'$*8,SL$:##%#7SL$&#$$+#$#<SL&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#$D?0B@$#s.g#=##&#VT$s#-s$0&C#D5T&$D#'T&8K#%0$&$#s.q#%##(#5T'$D#'T'8K#%0$&$#s.y#%##(#-Sb3IT9#T';s/cT'?S[T(%#=T9&$0'%>T9(#'TI1FCE#5TI1s/8C$#:s/8#TXj#&F#2F#'Sb(D#5Sb(D#$P&*Sb$#s/48K)'$*8,Sb$:##%#7Sb$&#$$+#$#<Sb&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#0A?$#s/N#<#$Ds#)'T95T98K$#0%$$#s/U#%#'T(5T(8K$#0%$$#s/[#%#-S[3ISc#T(;s0DT(?SrSd%#=Sc&$0'%>Sc(#'TX1FCE#5TX1s/uC$#:s/u#S;j#&F#2F#'S[(D#5S[(D#$P&*S[$#s/q8K)'$*8,S[$:##%#7S[$&#$$+#$#<S[&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#j##s#/#0A?$#s0/8Ks#*s#('Sc5Sc0$#$#s04USqSK'S;-S;%#$.#+#J/s0|Sr+#Sr*S;,S;%$#.#+#E)H#s0k)H)#)H,#EISA1#j#$s1*#2s1+#j#%s1,#2s1-#'Ss-Ss%#$.#+#J/s14S;+#S;*Ss,Ss%$#.#+#E)H#s1#)H)#)H,#EISB1#j#$s1>#2s1?#j#%s1@#2s1A#3ISAs#)Sr;s1DSr?SMSBs#+#=SAs#,$0s#-%>SAs#.#1FCE<%6=1s0tC$#:s0t#Sej#&F#2F#(Ds#6%s#0s#7(D#$Ps#9$s#3s0n8Ks#;&$s#<s#;$s#<s#5#$#7S;$s#8#$$s#:#$#<S;&C;##%##*##.##0##2##4##7##9##@##s####s#%##s#(#j##s#*#'SA-SA%#$.#+#J/s1pSs+#Ss*SA,SA%$#.#+#E)H#s1_)H)#)H,#EISM1#j#$s1z#2s1{#j#%s1|#U#E'SB-SB%#$.#+#J/s2(SA+#SA*SB,SB%$#.#+#E)H#s1s)H)#)H,#EISe1#j#$s22#2s23#'SM-SM%#$.#+#O/s2:SB+#SB*SM,SM%$#.#+#E)H#s2))H)#)H,#EISN1#j#$s2D#2s2E#3ISN3SB;s2HSB?SOSP5#=SN6$07%>SN8#'Se1FCE#*Se%#%1s1zC%#:s1z#SCj#&F#2F#(DB%<s##(D#$Ps#%$?s1t8Ks#'&$s#(s#'$s#(A#$#7SM$s#$#$$s#&#$#<SM&C=##%##*##.##0##2##4##7##9##B##s#%##s#'##s#*#j##s#,#-Se%#s#'.#+#Q/s2uSM+#SM,Se%s#+#.#+#E)H#s2c)H(#)H+#EISPs#3#j#$s2~#U#E'SN-SN%#$.#+#R/s3*Se+#Se*SN,SN%$#.#+#E)H#s2u)H)#)H,#EISO1#'SP-SP%#$.#+#S#/s3:SN+#SN*SP,SP%$#.#+#J)H#s3))H)#)H,#EISC1#'SO-SO%#$.#+#S$/s3JSP+#SP*SO,SO%$#.#+#O)H#s39)H)#)H,#XTfISf1#UTJ$6#XTKISf4##&#-SC3ISQ#SO;s3[SO?SRSS%#=SQ&$0'%>SQ(#'Sf1FCE#*Sf%#%1s31C%#:s31#S\j#&F#2F#'SC(D#*SC%#%(D#$P'$&s3-8K)&$*9,SC$;##%#7SC$&#$$.#$#<SC&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#-#j##s#0#%s#0A.#+#S'/s4.SO+#SO%s#$=.#+#Q)H#s3w)H'#)H*#UTJ#6#XTKISQs#.#-Sf%#s#8.#+#S2/s4=SC+#SC,Sf%s#<#.#+#R)H#s4+)H(#)H+#XTfISSs#D#-SQ'SQ%$#.#+#S)/s4LSf+#Sf*SQ,SQ%$#.#+#S#)H#s4;)H)#)H,#UTg#UTL$3ISR2##%#'SS-SS%#$.#+#S+/s4_SQ+#SQ*SS,SS%$#.#+#S$)H#s4N)H)#)H,#UTJ#6#XTKIS\3#-SR3ISg#SS;s4nSS?ShS]%#=Sg&$0'%>Sg(#'S\1FCE#*S\%#%1s4DC%#:s4D#T:j#&F#2F#'SR(D#*SR%#%(D#$P'$&s4@8K)&$*9,SR$;##%#7SR$&#$$.#$#<SR&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#-#k##s#0#j##s#C#UTLs#53IS\s#D#%s#3s#$.#+#S-/s5DSS+#SS%s#'@.#+#S')H#s51)H'#)H*#UTg#-S\%#s#9.#+#SE/s5QSR+#SR,S\%s#=#.#+#S2)H#s5?)H(#)H+#UTL#3IS]s#F#'Sg-Sg%#$.#+#S0/s5aS\+#S\*Sg,Sg%$#.#+#S))H#s5P)H)#)H,#UTJ#6#XTKISh3#-S]'S]%$#.#&Ls1l#/s5sSg&L##*S],S]%$#.#&Ls3?###S<#)##,#-Sh3ISi#S];s6#S]?S^Sj%#=Si&$0'%>Si(#'T:1FCE#*T:%#%1s5UC%#:s5U#TYj#&F#2F#'Sh(D#*Sh%#%(D#$P'$&s5Q8K)&$*9,Sh$;##%#7Sh$&#$$.#$#<Sh&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#-#j##s#0#/s6OS]&L##/s6QS-%B;.#&L%###S<#(#-T:%#s#2.#&Ls2:#/s6[T:&L##*Si,Si%$#.#&Ls3E###S<#)#/s6dSi&L##*Sj,Sj%$#.#&Ls2d###S<#)#-S^3IT;#Sj;s6oSj?STSk%#=T;&$0'%>T;(#'TY1FCE#*TY%#%1s6EC%#:s6E#T)j#&F#2F#'S^(D#*S^%#%(D#$P'$&s6A8K)&$*9,S^$;##%#7S^$&#$$.#$#<S^&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#-#j##s#0#/s7?S3%@9.#&L%###S</s7DS^&L##*T;,T;%$#.#&Ls2k###S</s7LSF*Sk,Sk%$#.#&L'###S<-ST3ISt#Sk;s7USk?T*Sl%#=St&$0'%>St(#'T)1FCE#*T)%#%1s7+C%#:s7+#SUj#&F#2F#'ST(D#*ST%#%(D#$P'$&s7'8K)&$*9,ST$;##%#7ST$&#$$.#$#<ST&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#-#j##s#0#/s8%S>,T)%s#)#.#&L&#'Sl-Sl%#$.#+#S6/s8/St+#St*Sl,Sl%$#.#+#S9)H#s7z)H)#)H,#YTyISU1#S4UTL$3ISU3#UTUs8<Gs8=S,#'SUGs8?T*EGs8@Sp#3IT+%#j#)s8A#VTzs8CS,ZThs8C)$ES,#'T*Gs8FSlS,Gs8GS?#3ITM%#UT5T{4s-,4#UTT#UTc#UT|s8Nk##$#Gs8PJE3RQO#3S#RQO/s8SO6#0Q#3S#R#J#'#k##)#3RQOJ/s8ZJ6#0O#3RQ#E#'#Gs8_OJ3S#RQ#k##%##,#3S$S#RQ/s8dQ6#0R#3S$S##O#'#k##+#j##*#Gs8kQO3S$S#R#k##8#j###Jj##9#YT}RQOJED;2)$#j#*s8q#j#+s8r#j#,C#j#-s#(#j#.s#/#k#*s8vAk#+s8w#k#,C#k#-s#-#k#.s#4#'TMGs8}SUS5ZEIS_$S1#J3IS_%S1/s9$S16#0(#3IS_#(#'#'T+3IT<#S7/s9+S76#0&#Gs9.TMS63IT<$##(#-S_3ISu#T+/s93T+6#?SmT,&#=Su'$0(%>Su)#'T<1FCE#*T<%#%1s8fC%#:s8f#T=j#&F#2F#'S_(D#*S_%#%(D#$P'$&s8b8K)&$*:,S_$<##%#7S_$&#$$.#$#%)B&C@##%##*##/##1##3##5##9##<##s#%##s#(##s#*##s#.#j##s#1#/s9`SI6#0s###Gs9cT+S?3ISu$#3IT,s#.S}'Su/s9gS86#0%#Gs9jT<S13ISm$#/s9lS:'Sm6E0$#Gs9pT,SI3IT-$#j#/L#-T,'T,%$#.#ZThL-'E#S.6$0'#Gs9zSuS73IT=$#-Sm%#2.#6#05#&C'#AD'08#&C*#UTZCj#0CE&CJEUT~#j#1C#j#0C#@C10JEXU#CCU$#@C#j#-C#j#/C#@Cs#&@Cs#&j#0L#ADEj#0C#@C;PCLCCSV3S%$S`<<#PLCCCS%S%44'<8#fU%CCCCCCT[555T[+s#.s#.*<9#JCC7672@@1<9#*Sm,Sm%$#.#&Ls#A#AD%&Cs#B#UTZL6J&C#s#8&LJEVU&JEWU'%$#j#1L#j#0L#@Cs#KU80@C1PCLCCSVs#)S%:S`22#JLC.S%s#+'s#Ps#O&2%#L20#S+/s:TSm&L##6$&C##@C$JLC5S%s#2.'%#'%#L'%#S3/s:[SY-T-'T-%$#.#&L'#6(AD&&C$#@C%Us#.)@C*PCLCCSVs#?S%s#0S`++#JLCs#$S%s#A=/)&+%#L+(#S>/s:jS@M#6$$D#/s:nSJM#6$$D#/s:rTNM#6$$D#-T.'T.%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#-T/'T/%$#AD#*T0,T0%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#*Sv,Sv%$#AD#UT\TiUT\#UT\#VTOC#UU(TFVU)C#VTOC'WTjC$#VTOCTiWT1C$#WT1C)#VT>#T?VTOC.WT1C#'WT1C*#VT>#T?VT>)T?UTUSn)Sn$#)Sn&#)Sn+#UT5SnVT2COVT2CQSC$J#UU*CUU+CZT]#NGGMS#9TFTC#TCTFTCs;]WT3C$#BC&T@#C*NGGM#S&[Sw+NGGM*#VT^CDBC'S/#C.NGGM#S&BC,T@%C0NGGM#S&[Sw1NGGM%#[U,2NGGM)#UU-GBC/S/0C5NGGM#S&ZT]6NGGMS$[Sw7NGGM$#WTAC35BC5T@#C:NGGM#S&F;NGGM&*#F<NGGM,+#VU.=M@TkTlVU/EO&Tk#Tlm$%#WU0CDJXU1EO$#l#2*)#l#3s#'s#&#l#4s#,s#+#j#5C#j#6C#j#7C#j#8SW#j#9SW#%EJ&CO##Q#$%D&COD#$#O&#$OJ##S#0QR&CO#k##%#k##(#k#5C#k#6C#k#7C#k#8SW#k#9SW#-TP,TP$$#'TP%&#(D#[E&#Q%(RSPl#:<*#l#;s#aC#l#<s#ns#f#l#=s#sC#l#>s$$s#x#l#?s$+s$)#l#@s$0s$.#l#As$5s$3#l#Bs$8s$>#l#Bs$Hs$K#l#Bs$Ps$^#XU2s%#s$|s$f#m##s%$'T=-T=%#$.#6#0'#Gs<NT=S83ITNE#j#CC#ZU3C&#J*EGs<RSmS}3ITQ,#-TQZEISa#T-S:J3ISa$T-/s<WT-6#0'#3ISa#S:#'#-TN3IT.#TQ/s<^TQ6#0&#3IT.#SJ#'#-Sa3IT/#TN?SvT0$s$O=T/%s$P0&s$Q>T/'#1FCEs$P*T.%#s$R1s<9C%#:s<9#Sxj#&F#2F#'Sa(D#*Sa%#%(D#$P'$&s<58K)&$*7,Sa$9##%#7Sa$&#$$.#$#%)?&Cs$k##%##*##/##1##3##5##9##<##s#$##s#'##s#)##s#+#j##s#.#3IT/s#*TG3IT0s$xSa/s=5T.6#0s$o#3ISv#S@'T0%s$n#/s=;SK.s$n&L$#6%&C#s$n@C$Us%fs$s@Cs$tPCLCCSVs%wS%s%hS`s$us$u#JLCs%\S%s%ys%U+(&*%#L*(#SF/s=FT0&L##6$&C##@C$JLCs%cS%s&$s%\'%#'%#L'%#S,/s=MTW-Sx'Sx%$#.#&L'#6(AD&&C$#@C%Us%|)@C*PCLCCSVs&1S%s%~S`++#JLCs%rS%s&3s%k/)&+%#L+(#Sp/s=\T%M#6$$D#/s=`S~M#6$$D#/s=dSyM#6$$D#-TB'TB%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#-SD'SD%$#AD#*T4,T4%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#*Sz,Sz%$#AD#UU4CSCs%;J#BCs%.T_s%2Cs%9NGGM#S&BCs%0S/s%4Cs%;NGGM#S&Fs%<NGGM%s%+#l#2#s$~s$xl#3)s%?#l#4s%Hs%D#j#5C#j#6C#(Ds$t%JO$D#k##%#k#5C#k#6C#'T`*T`WE$#Sil#:,&#l#;9C#l#<s#&>#l#=s#+C#l#>s#8s#0#l#?s#?s#=#l#@s#Ds#B#l#As#Is#G#l#Bs#Ls#R#l#Bs#\s#_#l#Bs#ds#j#$Ds#pm#$#YU5Ks#ss#rSL#$Ps#t0s#us#t$#s=l($TC(Ds#xUU6K$s=p##%##'##)##,#'Sv$P#%s&($0%#$#s=y($TC(D(##.#%##'##+#3ISys#uSv/s>fSv6#?TBS{s#x#=Sys#y$0s#z%>Sys#{#1FCEs%7*TP%#s%91s><C%#:s><#SDj#&F#2F#(Ds$&*Sx%#s$((D#$Ps$*$&s>78Ks$,&$s$-s$.,Sx$s$0##%#7Sx$&#$$.#$#%)s$6&C>##%##*##/##1##3##5##9##;##s####s#&##s#(##s#,#j##s#.#0s$D>$#s>Q($TC#s##s#A#$##&#$Ps%b'Sy*Sy%#$0%#$#s>[($TC(D(##s#L#%##'#-S{3ISD#Sy?SzT4$s$@=SD%s$A0&s$B>SD'#1FCEs$A*TB%#s$C1s>xC%#:s>x#S|j#&F#2F#'S{(D#*S{%#%(D#$P'$&s>t8K)&$*7,S{$9##%#7S{$&#$$.#$#%)?&Cs$\##%##*##/##1##3##5##9##<##s#$##s#'##s#)#/s?pSZ%>7.#&L%#6&AD&&C$#@C%Us(A)@C*PCLCCSVs(RS%s(CS`++#JLCs(7S%s(Ts(0-)&+%#L+(#S,/s?}S{&L##6$&C##@C$JLCs(>S%s([s(7'%#'%#L'%#Sp/s@(T&.s$m&L$#6%&C#s$o@C$Us(Ss$r@Cs$sPCLCCSVs(dS%s(US`s$ts$t#JLCs(IS%s(fs(B+(&*%#L*(#S8/s@3T'M#6$$D#/s@7SLM#6$$D#/s@;SzM#6$$D#-T`%#s$`QD#(D$AD%&C#&#%#$(D&C&D#$#O&#-So'So%$#AD#*Tm,Tm%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#*TR,TR%$#AD#BCs'dS/s'cCs'iNGGM#S&ZT]s'jNGGMR[Sws'kNGGM$#Fs'lNGGM#s'[%l#2#s'Rs'Ll#3s%9s'o#l#4s'xs't#j#5C#j#6C#j#8SW#$EJ##O$JOk##$#k#5C#k#6C#k#8SW#-TD,TD$$#'TDR$&#Sjl#:/(#l#;;C#l#<s#(@#l#=s#-C#l#>s#:s#2#l#?s#@s#>#l#@s#Es#C#l#As#Js#H#l#Bs#Ms#S#l#Bs#Ys#\#l#Bs#as#g#m##s$'WT1Cs(Fs(;VT>#T?)Sn#s(:VT2CRVT2CS$SC$O#VT2CS#SC#Qs%^SC%J#9sA2TC#WT3C#s(6BCs(6T@#Cs(<NGGM#S&4s(;TC#BC(S/#Cs(@NGGM#S&TCsA:BC&S/#Cs(CNGGM#S&[Sws(DNGGM&#WTACs(As(@WT3C's(CWTACs(D#BC%S/#Cs(INGGM#S&Fs(JNGGM(s(9#Fs(KNGGM1s(:#l#2#s(1s(+l#38s(N#l#4?s(S#j#5C#j#6C#j#7C#j#DC#j#EC#j#FC#%RE&CJ#$S#S$$S$R#$#0OQ%S#R0R#$%#k##'#k##+#k#5C#k#6C#k#7C#k#DC#k#EC#k#FC#7TD*TD/sA^Ta6#\E&s#M%s#K#s#NSxSil#:9(#l#;s#cC#l#<s#ps#h#l#=s#uC#l#>s$&s#z#l#?s$,s$*#l#@s$1s$/#l#As$6s$4#l#Bs$9s$?#l#Bs$Es$H#l#Bs$Ms$S#0s$ws$t$s%%#m#%#m##$^U7SzT4STs${s$xs%,s&hS^s#N#UU8K9s(z9#9#9#9#9#9#9#9#9#9#9#9#4#9#9#9#9#9#9#9#9#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#UT##$#sA_9s#%9#9#9#9#9#9#9#9#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#4#UT##$sB%##s#%#4s,{4#4#4#4#4#UT##VT$sB.#&C#D0sB0%(s&|##s&|##&##0#/sBvTB6#=Szs'b#0s'c$>Szs'd#'T41FCE#%s'c$1sBKC$#:sBK#Soj#&F#2F#(Ds'k*SD%#s'm(D#$Ps'o$&sBF8Ks'q&$s'rs's,SD$s'u##%#7SD$&#$$.#$#%)s'{&C=##%##*##/##1##3##5##9##;##s####s#&#j##s#*#-S|=So#s%d0$s%e>So%#1FCEs'f%s'fs'g1sBqC$#:sBq#Taj#&F#2F#'S|(D#*S|%#%(D#$P'$&sBm8K)&$*4,S|$6##%#7S|$&#$$.#$#%)<&Cs%~##%##*##/##1##3##5##9##<##s###UT,Su/sChTH%=6.#&L%#6&AD&&C$#@C%Us,9)@C*PCLCCSVs,JS%s,;S`++#JLCs,/S%s,Ls,(-)&+%#L+(#Sp/sCuS|&L##6$&C##@C$JLCs,6S%s,Ss,/'%#'%#L'%#S8/sC|T(.s&3&L$#6%&C#s&5@C$Us,Ks&8@Cs&9PCLCCSVs,\S%s,MS`s&:s&:#JLCs,AS%s,^s,:+(&*%#L*(#S@/sD+S[M#6$$D#/sD/TIM#6$$D#/sD3TRM#6$$D#%s&%s%~QD#(D$AD%&C#&#%#$(D&C&D#$#O&#-Tn'Tn%$#AD#*To,To%$#QD#(D$AD%&C#&#%#$(D&C&D#$#O&#*Tp,Tp%$#AD#-TE,TE$$#'TER$&#STl#:s&Ps&I#l#;)C#l#<6.#l#=;C#l#>s#(@#l#?s#-s#+#l#@s#2s#0#l#As#7s#5#l#Bs#:s#@#l#Bs#Fs#I#l#Bs#Ns#T#m##s#o7TE*TE/sDhU96#\E&6%4#7SDSkl#:s&#s%n#l#;:C#l#<s#'?#l#=s#,C#l#>s#9s#1#l#?s#>s#<#l#@s#Cs#A#l#As#Hs#F#l#Bs#Ks#Q#l#Bs#Ws#Z#l#Bs#_s#e#0s$,s$)$s$5#m#%#UT#sD}9s&N9#9#UT##VU:'#(D($D%VU;*&(D#k##%#k##'#$D.WU</+Jj##S<#j#G%#$D*k##S<#k#G(#)Sns,Es,CSCs)cQs,>SCs,@J#TCs%{VT^Cs%-BC$S/#Cs,@NGGM#S&[Sws,ANGGMs,@#WT3Cs,=s,>WTACs,?#BC#S/)Cs,ENGGM#S&VT^CAUTT?WU=C$#BC(S/#Cs,JNGGM#S&Fs,KNGGM(s,:#Fs,LNGGM-s,;#l#2#s,2s,,l#34s,O#l#47s,T#j#5C#j#6C#j#7C#j#8SW#$Os%C#Q#%OJ0J#$#Q%QO0O#$#s#.k##&#k##*#k#5C#k#6C#k#7C#k#8SW#*Tq'TqZEs%tsDu$#S=SCl#:4&#l#Hs#2s#/#l#Is#=s#7#l#;s#hC#l#<s#us#m#l#=s#zC#l#>s$+s$##l#?s$0s$.#l#@s$5s$3#l#As$:s$8#l#Bs$=s$C#l#Bs$Is$L#l#Bs$Qs$W#$s#Ps#Em#$#$s#RTCm#$#]U>Sos$~s${s%,s(1s$cs#es#R#_U?KTSU@TaTRSoSUs%#s$|T4T)VT2CJBCs,oT_s,uCs,zNGGM#S&BCs,qS/s,wCs,|NGGM#S&Fs,}NGGM%s,l#l#2#s,cs,]l#3)s-$#l#4s--s-)#j#5C#(DE$DJk##$#k#5C#VEs$&Sjl#:($#l#;s$,C#l#<s$9s$1#l#=s$>C#l#>s$Ks$C#l#?s$Ps$N#l#@s$Us$S#l#As$Zs$X#l#Bs$]s$c#l#Bs$is$l#l#Bs$qs$w#$Ds%>m#$#BCs-.S/s-3Cs-9NGGM#S&BCs-6S/s'SCs-;NGGM#S&Fs-<NGGM%s-+#l#2#s,~s,xl#3s*es-?#l#4s-Hs-D#j#5C#j#6C#0JO$J#k##?#k#5C#k#6C#WEs$2s$FS#l#:)$#l#;s$IC#l#<s$Vs$N#l#=s$[C#l#>s$hs$`#l#?s$ms$k#l#@s$rs$p#l#As$ws$u#l#Bs$zs%$#l#Bs%*s%-#l#Bs%2s%8#$s%es%cm#$#BCs-KT_s#qCs-VNGGM#S&BCs-MS/s#rCs-XNGGM#S&Fs-YNGGM%s-H#Fs-ZNGGMs#>s-I#l#2#s-@s-:l#3s+'s-]#l#4s$%s-b#j#5C#j#6C#(Ds#h$Ds#ek##$#k##s#?#k#5C#k#6C#Rs$Ss$bSjT*l#:*$#l#;s$hC#l#<s$us$m#l#=s$zC#l#>s%+s%##l#?s%0s%.#l#@s%5s%3#l#As%:s%8#l#Bs%=s%C#l#Bs%Is%L#l#Bs%Qs%W#$Ds$Pm#$#_UASos%|s$Rs&*s&(s#[s#?s$cs$PB#XUBFs&#SUT)Fs-vNGGMs#Zs-es#Zl#2#s-\s-Vl#3s#^s-y#l#4s.&s-~#j#5C#(DJk##s#X#k#5C#l#:&#s#Vl#;s%#C#l#<s%0s%(#l#=s%5C#l#>s%Bs%:#l#?s%Gs%E#l#@s%Ls%J#l#As%Qs%O#l#Bs%Ts%Z#l#Bs%`s%c#l#Bs%hs%n#m##s&4Fs..NGGMs+Ss-ys+Sl#2#s-ps-jl#3s+Ws.1#l#4s.:s.6#j#5C#j#6C#(Ds+Ok##s+Q#k#5C#k#6C#WEs%4s%%T*l#:($#l#;s%:C#l#<s%Gs%?#l#=s%LC#l#>s%Ys%Q#l#?s%^s%\#l#@s%cs%a#l#As%hs%f#l#Bs%ks%q#l#Bs%ws%z#l#Bs&#s&)#m##s&HFs.ENGGMs):s.4s):l#2#s.+s.%l#3s+ns.H#l#4s.Qs.M#j#5C#j#6C#k##s)6s)4k#5C#k#6C#WEs%JPS.l#:'$#l#;s%PC#l#<s%]s%U#l#=s%bC#l#>s%os%g#l#?s%ts%r#l#@s%ys%w#l#As%~s%|#l#Bs&%s&+#l#Bs&1s&4#l#Bs&9s&?#m##s&]WT3Cs.Ws.XWTACs.Y#BC#S/s.XCs.^NGGM#S&Fs._NGGM#s.Ns)Tl#2#s.Es.?l#3s.cs.b#l#4s.ks.g#j#5C#j#6C#j#7C#%EO0O#$#Jk###s)Rk#5C#k#6C#k#7C#Rs%isF~s%ZSPl#:+$#l#;s%oC#l#<s%|s%t#l#=s&%C#l#>s&2s&*#l#?s&7s&5#l#@s&<s&:#l#As&As&?#l#Bs&Ds&J#l#Bs&Ps&S#l#Bs&Xs&^#m##s&{m#Scs&{[Sws.{NGGMs)os)pFs.|NGGM#s.ks)ql#2#s.bs.\l#3s,Is/##l#4s/,s/(#j#5C#j#6C#j#8SW##Os)nk###s)mk#5C#k#6C#k#8SW#$s&(s&+R#s&+s&,STl#:*%#l#;s&/C#l#<s&<s&4#l#=s&AC#l#>s&Ns&F#l#?s&Ss&Q#l#@s&Xs&V#l#As&]s&[#l#Bs&`s&f#l#Bs&ls&o#l#Bs&ts&z#m##s'7Is':s'8s&)#$s&)s&(R#s&*s&:Skl#:s*)s)~#l#;s&>C#l#<s&Ks&C#l#=s&PC#l#>s&]s&U#l#?s&bs&`#l#@s&gs&e#l#As&ls&j#l#Bs&os&u#l#Bs&{s&~#l#Bs''s'-#m##s'C$s&Gs&7R#s&7s&8Skl#:s#'B#l#;s&LC#l#<s&Ys&Q#l#=s&^C#l#>s&ks&c#l#?s&ps&n#l#@s&us&s#l#As&zs&x#l#Bs&}s''#l#Bs'-s'0#l#Bs'5s';#m##s'PIs'Rs'Q1#WTjCs/ms/fWT1C#s/kVT>#T?)Sn#s/dWT3Cs/Ws/YBCs/YT@#Cs/^NGGM#S&Fs/_NGGM#s/N#l#2#s/Es/?l#3s/cs/b#l#4)s/g#j#5C#j#6C#j#7C#&CEs-%%OQ&CJ#k##%#k#5C#k#6C#k#7C#Rs&ls&ks&XSDl#:+$#l#;s&oC#l#<s&|s&t#l#=s'%C#l#>s'2s'*#l#?s'7s'5#l#@s'<s':#l#As'As'?#l#Bs'Ds'J#l#Bs'Ps'S#l#Bs'Xs'^#m##s'pIs'ss'qs#%#Is'xs'qs#C#Is'}s'qs#`#Is(#s'qs#b#Is(%s'qs$&#Is('s'qs$=#Is(+s'qs$U#Is(.s'qs$j#Is(5s'qs$l#Is(8s'qs%k#j#Js(d#j#Ks(r#V#JEj##s(g#j##s(u#Ds(vs(is(@#El#Ls)ms(i#Is,;s+qs)o#Is,=s+qS$#j#Js,@#j#Ms,K#V#JEj##s,N#j##s-.#Ds-/s-'s,V#El#Ls-=s-2#j#Js.T#j#Ns.Y#V#JEj##s.\#j##s/3#Ds/4s/0s._#El#Ns/=s/7#l#Ls2ys2t#l#Ns/Cs/A#l#Ls/Ns1p#l#Ns1{s1w#j#Ns2,#j#Js23#V#JEj##s26#j##s2q#Ds2rs2ms2=#El#Ns2{s2u#l#Ls3(s3##l#Ns3[s3W#l#Ns3gs3e#3ISUs3vSt;sIDSt?T+TMs3x#=SUs3y$0s3z%>SUs3{#1FCEs3b*T*%#s3d1sHuC%#:sHu#S_j#&F#2F#(Ds4(%s3~s4)(D#$Ps4+$s4%sHo8Ks4-&$s4.s4-$s4.s4'#$#7Sl$s4*#$$s4,#$#<Sl&C<##%##*##.##0##2##4##7##9##A##s#$##s#&##s#)#m#s#+#j#JS<#j#Os4F#V#JEj##S<#j##s4}#Ds4~S<s4O#Ej#Ls5)#j#Ps50#V#JEj##s54#j##s5o#Ds5ps5js5;#Ej#Ls5s#j#Qs5}#V#JEj##s6'#j##s6h#Ds6is6`s61#Oj#Rs6o#j#Js7&#j#Ss76#V#JEj##s7D#j##s8/#Ds80s8.s7H#Ej#Ls8A#V#JEj##s8Q#j##s96#Ds97s94s8a#El#LEs9H#j#Ts9Y#j#$sJ/#V#JEj##s9l#j#0sJ2#YTbsJ3s:Ms9~#Ej#Ls:_#j#%sJ5#V#JEj##s:t#j#0sJ8#YTbsJ9s;Ws;.#El#Us<#s;k#-Sd3IS;#Sc;sJ>Sc?SASs%#=S;&$0'%>S;(#'Sr1FCE#5Sr1sIoC$#:sIo#SBj#&F#2F#'Sd(D#5Sd(D#$P&*Sd$#sIk8K)'$*8,Sd$:##%#7Sd$&#$$+#$#<Sd&C?##%##*##/##1##4##6##9##<##s#$##s#'##s#)##s#,#m#s#/#j#Vs<R#j#Ws<W#V#JEj##s<Z#j##s=1#Ds=2s=0s<^#Ej#Ls=6#j#Rs==#V#JEj##s=@#j##s=w#Ds=xs=ss=E#Ej#Ls={#j#Js>(#V#JEj##s>,#j##s>g#Ds>hs>as>3#Ej#Ls>l#j#Xs>x#V#JEj##s>{#j##s?b#Ds?cs?Ws?)#El#LS)s?f#j#Ys?j#j#Zs?q#V#JEj##s@+#j##s@P#Ds@Qs@Ls?z#Ej#Ls@X#j#[s@e#V#JEj##s@h#j##sAH#DsAIsA=s@k#Ej#LsAL#j#\sA\#V#JEj##sA_#j##sBA#DsBBsB5sAc#Ej#LsBF#j#]sBX#V#JEj##sB]#j##sCC#DsCDsC5sBc#Ej#LsCJ#j#&F#V#JEj##sCb#j#0F#YTbFsD;sCv#Ej#LsDM#U#Ej##sEK#ZUCsEcsELsE+sDW#S+j#^sEe#j#_sEh#j#`sEo#V#JEj##sF,#j##sF_#DsF`sF\sF0#Ej#LsFx#j#asG^#V#JEj##sG:#j##sH?#DsH@sH$sGT#Ej#LsHD#j#bsHd#V#JEj##sHg#j##sIt#DsIusIUsI)#Ej#LsIw#j#csJ=#V#JEj##sJA#j##sKZ#DsK[sK8sJa#Ej#LsK^#j#dsK`#j#esKb#j#fS(#j#,C#j#-UD#j#gsKl#j#hsKn#j#isKp##"). Qed.


(* [comment removed for export] *)
Lemma rin_elemsW : forall L a, rin_ivs (elemsW L) a -> exists e, In e L /\ e <= a < e + 48.
Proof.
  induction L as [|y L IH]; intros a R; cbn in R; [destruct R|].
  destruct R as [R|R]; [exists y; split; [left; reflexivity| exact R]|]. destruct (IH a R) as (e & IN & K). exists e. split; [right; exact IN| exact K].
Qed.

Lemma xpres_put_hread : forall LBn LBin (SPp SP : Z) P E fb stb L es XS m m',
  xpres H (LBn ++ LBin) SPp (put_X P E L es ++ XS) m m' ->
  (forall e, e ∈ L -> blk_fresh H LBin SP e 48) -> (forall x s, In (x, s) es -> blk_fresh H LBin SP x (24 + s)) -> SPp <= SP ->
  xpres H LBin SP (hread_X P E fb stb [] [] ++ XS) m m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_mbuf.mbe); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.xpres); constr:(HCEIL); constr:(H); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_put_stmt.put_X); constr:(@stdpp.base.elem_of); constr:(@stdpp.base.list_elem_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_pst.blk_fresh); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8SRKit.xpres_reLB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read_stmt.hread_X); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.aclient_addr); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rin_ivs); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsCXXHeap.aclient_addr_weaken); constr:(@Stdlib.Lists.List.in_or_app); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8SRKit.aclient_addr_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.aclient_range); constr:(@kc__2); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_FIELD_TABLE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_insert2.elemsW); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_mbuf.mb_elemsW); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.and_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SPCI_STATE); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Classes.Morphisms.iff_impl_subrelation); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rin_ivs_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read3.HCW.rin_elemsW); constr:(@Corelib.Init.Logic.ex); constr:(@kc__3); constr:(@kc__1); constr:(@Corelib.Init.Logic.proj2); constr:(@stdpp.base.list_elem_of_In); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep_mbuf.mb_elemsW_In); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z))|] [|@e; @s; @x; @Hb; @b; @H4; @H5; @H7; @H6; @H8; @H9; @H10; @H11; @H12; @H3; @H2; @H1; @H0; @R; @lemma; @Ha; @__ff; @__varmap; @__wit; @__arith; @__sat0; @__sat1; @__x1; @__x2; @__p1; @__p2; @__sat2; @o; @K; @INe; @a; @es; @__x3; @INx; @s0; @CR; @NX; @C; @LE; @FRB; @FRL; @XP; @m'; @m; @XS; @L; @stb; @fb; @E; @P; @SP; @SPp; @LBin; @LBn|] "#6x#V$V###[$)#$$@$&$%#7#.#5#)#2#6#&#%#3#0#9#(#/#1#4#8#:#;#<#?#B#D#*#,#>#F#A#H#=$+#@$A$?#'#C#E#-#+#s#V#Z#`#a#J#G#I$E#M#O#K#L#N#Q#P#S#R$S#j$D#\#f#p#v#w#U#T$.$/$0$8$:$I$J#^#]#_#e#u#{#z#}#~$1$6$5$7$9$;$<$>$F$H$L$K$M$G$T$W#o#n#t#r$$#m#x#b#|#k#h#y$,$($2$'#g$*$##i$B$=#l$Q$P#Y$N$-$C#c#d#q$O$R$V$U$4$3N$1%$2%$3%$4%$5%$6%#0$$7&$8&$9&$:$$;'$<&$=$#1$$>%$?$$@$$A($B)$C$$D'$E*$F'$G&$H+$I$$J'##$#K$$K%$L%$M'$N($O$#5$$P%$Q%$R)$S*##)$T($U(=SB=D=SUVSdDD=#*SBS&KCS?S0S;P*&#Q[SeSCSD%S>#FCUSfDDD+#CM7SS-#-#-#-#4#ZSVSCSDS'S&F#k##*#k#$D#:DDFC,4#S04*'#FZSVSCSDRS'Q#k##&#k#%D#k#&D##S#S&*SBRNEDESUZSWS&KS>S1$#*@#MCS&KS?S0*B#M#S@C-SS4#-$-#-#-#-#4#VSg)#$C#%-#YSXSCSDS(NFZSWNS'S#S&54*s#1#S1(#QUSY#*SBJOYSXSCSD#LPCRNS&K*s#7#S>(#PUSY#,SBCJ,SBFS$,SBFS)+$#CYShSBS$S)F#j#''#j#(SB#^SiSCSD/OLS(PFS;#ZSjSCSDJLS;Q4SSZSkSCSDJLS;##LS%7s#>7#-#-#7#-#4#'L#$S%#%,##S(S%'S(s#>$S%#%%##IS%'Is#,$S%#%%##HS%7s#P7#-#-#-#-#-#-#-#4#'H#$S%#%/#3S'0S#*s#h$#*s#i#S&(#S%&(#&7#&<#&A#j###E#OM'Os#'$M#%%##S@S0$S0s#K#LS07s#U-#-#-#4#'L#$S0#%*##S(S0'S(S7$S0#%%##JS0'Js#:$S0#%%##OS0'Os#u$S0#%%##IS0$S0s#9%$##HS0$S0s#.%$#(S'S0&$#&(#&,#&1#&6#&;#$S?s#n#S$S1'S$s#P$S1##JS1'Js#$$S1#%%##OS1'OS7$S1#%%#%-+#S)S1'S)s$7$S1#%%##IS1$S1s#W%$##HS1$S1s#L%$#(RS1&$#&(#&,#&1#&3#&8#'S*s#l$S>##S$K'S$s#@$K#%%##S*S&'S*s#D$S&#%%##S$S&'S$S7$S&#%%##S,S&'S,s#{$S&#%%##S+S&'S+s$Z$S&#%%##IS&$S&s#z%$##HS&$S&s#o%$#(OS&&$#&(#&,#&1#&6#/;#CUS1#j#)A#k##BE#S+S#'S+s#d$S##%%##S*S#'S*S7$S##%%##S6S#'S6s$?$S##%%##S,S#'S,s$z$S##%%##IS#$S#s$>%$##HS#$S#s$3%$#(JS#&$#&(#&,#&1#&6#+;#CUS>#j#*s#%#k##s#&E'S,s$'$S'##S6N'S6s$*$N#.%#FC)#j#+(#j#,s#*#k##*Ek##s#,##S+S''S+S7$S'#%%##S,N'S,S7$N#%%##S-N'S-s$j$N#%%##S2N'S2s%I$N#%%##IN$Ns$i%$##HN$Ns$^%$#(S$N&$#&(#&,#&1#/6#C1#j#)<#k##=E#S6R'S6S7$R#%%##S8R'S8s%)$R#%%##S-R'S-s%d$R#%%##IR$Rs%(%$##HR$Rs$y%$#(S*R&$#&(#&,#&1#+6#C)#j#+@#k##AE'S2S7$S(##S-L'S-S7$L#.%#FC)#j#-(#j#*s#%#k##*Ek##s#'##S4S('S4s%K$S(#%%##S.L'S.s%O$L#%%##S4L'S4s&.$L#%%##IL$Ls%N%$##HL$Ls%C%$#(S,L&$#&(#&,#/1#C1#j#)7#k##8E#S<O'S<s%e$O#%%##S.O'S.s&D$O#%%##IO$Os%d%$##HO$Os%Y%$#(S6O&$#&(#&,#+1#C)#j#-;#k##<E'S/s%z$J##S=S)'S=s%}$S)#.%#FC)#j#.(#j#+@#k##*Ek##B#?S>#S=S$'S=s&b$S$#%%##S3S*'S3s&f$S*#%%##IS*$S*s&*%$##HS*$S*s%{%$#(S4S*&$#&(#/,#C@#j#)2#k##3E#SFS+'SFs&w$S+#%%##IS+$S+s&;%$##HS+$S+s&0%$#(S.S+&$#&(#+,#CF#j#.6#k##7E'S5s'+$S,##SGS6'SGs'.$S6#.%#FC)#j#/(#j#-;#k##*Ek##=##IS,$S,s&S%$##IS6$S6s&V%$##HS6$S6s&K%$#(S/S6&$#/(#C1#j#)-#k##.E#IS2$S2s&b%$##HS2$S2s&W%$#(S=S2&$#+(#C)#j#/1#k##2E$S-s&m#IS8$S8s&o.$#FC)#j#0'#j#.4#k##)Ek##6##HS-$S-s&i%$##HS8$S8s&l%$#(SFS8/$#C1#j#))#k##*E#HS4$S4s&t%$#(S5S4+$#C)#j#0-#k##.E$S.s&{#HS<$S<s&}.$#FC)#j#1'#j#/0#k##)Ek##2##SIS.'SIs&m$S.#%%##SLS.'SLS7$S.#%%##SJS.'SJs'H$S.#%%##SMS.'SMs('$S.#%%##IS.$S.s'G%$##HS.%#?(SGS.&$#&'#&+#&0#&5#&:#A#S1l#/B@#l#0s#+s#*#l#)s#4s#3#l#.s#As#?#l#/s#Js#I#l#)s#Ws#V#l#-s#hs#f#l#.s#ss#r#l#)s$)s$(#l#+s$>E#l#)s$?s$A#l#+s$Cs$A#l#-s$Ns$M#l#)s$es$d#l#*s%%s%##l#+s%0s%/#l#)s%Ls%K#l#,s%ms%k#l#*s%xs%w#l#)s&=s&<#j#2s&a#j#3s'$#5s'%s'#s&e#Qj#4s''#j#5s'L#5s'Ms'Ls'*#M@#j#6s'P#U#Cj##s'v##LM'Ls(V$M#%%##IM$Ms'v%$##HM$Ms'k%$#3N0S'*s(t$#*s(u#S#(#M&(#&,#&0#3R0N*s(|$#*s(}#S'(#S0&s'M#&s'Q#&s'U#j###E#JS?'Js(q$S?#%%##S@S1$S1s(^$S>s(_#S*K'S*s(x$K##S)K'S)S7$K#%%##S+K'S+s(H$K#%%#%-+#IK$Ks(D%$##HK$Ks(9%$#(LK&$#&(#&,#&.#&3#&s'E##S,S'%#s&a#S2S''S2s(\$S'#%%##S6S''S6s);$S'#%%##IS'$S's([%$##HS'$S's(P%$#(S)S'&$#&(#&,#&1#&s&h#/7#CUK#j#)s':#k##s';E%s&ys&w&s&js&W+$#CUS&#j#*+#k##,E'S2s(J$R##S-S('S-s(M$S(#.%#FC)#j#+(#j#,s'+#k##*Ek##s'-##S2S(%#s&G#S8S('S8s)b$S(#%%##IS($S(s)&%$##HS($S(s(w%$#(S+S(&$#&(#&,#&s&I#/2#C1#j#)s&r#k##s&sE%s&Zs&X&s&Ks&=+$#C)#j#++#k##,E'S8S7$O##S4J'S4S7$J#.%#FC)#j#-(#j#*s&h#k##*Ek##s&j##S/J%#s&2#S<J'S<s*,$J#%%##IJ$Js)L%$##HJ$Js)A%$#(S2J&$#&(#&,#/1#C1#j#)s&W#k##s&XE%s&Ds&B#S/S)'S/s*?$S)#%%##IS)$S)s)_%$##HS)$S)s)T%$#(S-S)&$#&(#&,#+1#C)#j#-8#k##9E'S3s)u$S$##SFS*'SFs)x$S*#.%#FC)#j#.(#j#+s&_#k##*Ek##s&a#1s&Gj#)s&V#)s&8j#.s&K#?S##IS-%#s%n(S3S-&s%e#/%#C@#j#)s%}#k##s%~E%s%ts%s&s%hs%g+$#CF#j#/+#k##,E$S4s*..s%Gs%FFC)#j#0%#j#.s%~#k##'Ek##s&$#/s%Is%HC1#j#)s%n#k##s%oE%s%is%h(SES<+$#C)#j#0s%P#k##s%QE$S/s*1#HS=$S=s*3.$#FC)#j#1'#j#/s%u#k##)Ek##s%w##SJS/'SJs*#$S/#%%##SMS/'SMS7$S/#%%##SNS/'SNs*Z$S/#%%##SOS/'SOs+9$S/#%%##IS/$S/s*Y%$##HS/%#?(SKS/&$#&'#&+#&0#&5#&:#A#Ml#/B@#l#0s#+s#*#l#)s#2s#1#l#.s#8s#6#l#/s#?s#>#l#)s#Fs#E#l#-s#NE#l#)s#Os&z#l#-s&|s&z#l#.s#Rs'*#l#)s#Us'<#l#+s#Zs#X#l#-s#es#d#l#)s#ys#x#l#*s$3s$1#l#+s$>s$=#l#)s$Es$D#l#,s$\s$Z#l#*s$gs$f#l#)s$ns$m#j#2s)`#j#3s%E#5s%Fs%Ds%.#Qj#4s%H#j#5s%K#5s%Ls%Ks)z#S?UM#j#6s%O#U#Cj##s*M##IS?$S?s+(%$##HS?$S?s*y%$#3S(0R*s,&$#*s,'#N(#S?&(#&,#3L0S(*s,-$#*s,.#R(#S1&s*<#&s*@#j###E#IS>$S>s+=%$##S@K$Ks+i$S&s+j&s)ps)X#S2R%#s%1&s))s(r/$#CUS##j#)s%<#k##s%=E%s%6s%4&s%-s$z+$#CUS'#j#*+#k##,E'S8s+*$L##S4O'S4s+-$O#.%#FC)#j#+(#j#,s%D#k##*Ek##s%F##S8O%#s%#&s(]s(O/$#C1#j#)s%.#k##s%/E%s%(s%&&s${s$m+$#C)#j#++#k##,E'S.S7$S)##S<S$'S<S7$S$#.%#FC)#j#-(#j#*s%6#k##*Ek##s%8##S3S$%#s$e#IS$$S$s+v%$##HS$$S$s+k%$#(S8S$&$#&(#&s(\#/-#C1#j#)s%*#k##s%+E%s$ss$q&s(^s(U+$#C)#j#-+#k##,E'S5s,6$S+##SGS,'SGs,9$S,#.%#FC)#j#.(#j#+s%%#k##*Ek##s%'##S5S,%#s(O#HS,$S,s,-%$#(S<S,&$#&s(I#/)#C1#j#)s(g#k##s(hE%s(Ys(W&s(Ls(G+$#C)#j#.+#k##,E'SEs-.$S2##SKS-'SKs-1$S-#.%#FC)#j#/(#j#-s(g#k##*Ek##s(i#1s%3j#)s(Q#)s%/j#/s%7#?R/s$\s$[C@#j#)s%%#k##s%&E%s$|s${(SLS=+$#CF#j#0s$c#k##s$dE$S3s,V#HSF$SFs,X.$#FC)#j#1'#j#/s%,#k##)Ek##s%.##SNS3'SNs,H$S3#%%##SOS3'SOS7$S3#%%##SPS3'SPs-#$S3#%%##SQS3'SQs-^$S3#%%##IS3$S3s,~%$##HS3%#?(SIS3&$#&'#&+#&0#&5#&:#A#Pl#/B@#l#0s#+s#*#l#)s#2s#1#l#.s#6E#l#)s#7s%]#l#.s%_s%]#l#/s#:s%e#l#)s#=s%l#l#-s#Bs#@#l#.s#Ms#L#l#)s#Ts#S#l#+s#bs#`#l#-s#ms#l#l#)s#ts#s#l#*s$*s$(#l#+s$5s$4#l#)s$<s$;#l#,s$Es$C#l#*s$Ps$O#l#)s$Ws$V#j#2s'E#j#3s+d#5s+es+ds$`#Qj#4s$b#j#5s$e#5s$fs$es'V#S>US?#j#6s$i#U#Cj##s,Q##HS>$S>s-?%$#3O0L*s.H$#*s.I#S((#S>&(#3J0O*s.N$#*s.O#L(#K&s'p#j###E#S@S#$S#s.*$S's.+&s'Ss'R#S8L%#s$n&s'0s'//$#CUN#j#)s$y#k##s$zE%s$ss$q&s$js$i+$#CUR#j#*+#k##,E'S.s-G$J##S<S)'S<s-J$S)#.%#FC)#j#+(#j#,s%%#k##*Ek##s%'##S.S)%#s$n&s'#s&q/$#C1#j#)s$y#k##s$zE%s$ss$q&s$js$`+$#C)#j#++#k##,E'S/S7$S*##S=S+'S=S7$S+#.%#FC)#j#-(#j#*s%%#k##*Ek##s%'##S5S+%#s$e&s*[s*R/$#C1#j#)s$p#k##s$qE%s$js$h&s$as$[+$#C)#j#-+#k##,E'SEs.J$S6##SKS2'SKs.M$S2#.%#FC)#j#.(#j#+s$x#k##*Ek##s$z##SES2%#s$`&s*Is*D/$#C1#j#)s$k#k##s$lE%s$es$c&s'5s'3+$#C)#j#.+#k##,E'SLs/=$S8##SIS4'SIs/@$S4#.%#FC)#j#/(#j#-s$s#k##*Ek##s$u##IS4%#s'9&s*As*@/$#C1#j#)s'C#k##s'DE+s*%s)}C)#j#/)#k##*E$S<s.o.s&vs&uFC)#j#0%#j#.s*/#k##'Ek##s*1#1s$zj#)s'@#)s$vj#0s&z#?O#SPS5'SPs.V$S5#%%##SQS5'SQS7$S5#%%##SZS5'SZs/1$S5#%%##S[S5'S[s/l$S5#%%##IS5$S5s/0%$##HS5$S5s/%%$#(SJS5&$#&(#&,#&1#&6#&;#A#Cl#/AE#l#)Bs%1#l#/s%3s%1#l#0s#%s%;#l#)s#(s%B#l#.s#-s#+#l#/s#4s#3#l#)s#9s#8#l#-s#Bs#@#l#.s#Ms#L#l#)s#Ts#S#l#+s#]s#[#l#-s#hs#g#l#)s#os#n#l#*s#xs#v#l#+s$'s$&#l#)s$.s$-#l#,s$7s$5#l#*s$Bs$A#l#)s$Is$H#j#2s-(#j#3s-E#5s-Fs-Es$R#Qj#4s$T#j#5s$W#5s$Xs$Ws&r#S&US>#j#6s.8#U#Cj##s)p#3S)0J*s0T$#*s0U#O(#S&3S$0S)*s0Y$#*s0Z#J(#S#(%S#&#s.%VS\%#3S*0S$*s0a$#*s0b#S)(#S'(%S'&#s)lWS]%#Cj#7+#WS^1JS#V$#Cj##'E3S+0S**s0m$#(#N3S,0S+*s0q$#(#R(&R(&R&$#VS\&#3S60S,*s0y$#(#S((&S((&S(&$#WS]&#Cj#7+#WS^32RV$#Cj##'E3S2(#LWSlS-OC,DCS8#CJ'Cs0{$J#%%#%'#j#$D#2D#,DCS4#CS)$S)*%$#%&#j#$D#2D#j###E,DCS.#CS$$S$2%$#%&#j#$D#U#C,DCS<#CS*$S*9%$#%&#,DFS/#FS+'Fs1;$S+#%%#%'#j###E#QS,'Qs1A$S,#%%#,DPS3#S;S2'S;s1F$S2#%%#DDs1Xs1PS%S5,DMSGk##$#,DS%S5DDs1\s1TMSGk##$#WSmDS5S%XSn'$#FVSos1;s15$S@s1<#S@s17$S@s17k##$#k##&##S@s1AWSps1Bs1<Fj##S_#j#8%##S@s1>k##S_#k#8(#ES`=S`USqDUSrDUSsDBDS@BDs108D$ST#9&S:GGS9#SHVSt'S9VSuSaSbVSvCQWSwSa#Sbm$%#WSxDS@FXSyCQ$#l#9*)#l#:10#l#;43#$S@s1=l#<$#Cl#=;8#l#>s#%@#m##&ZS.S%s#(S-s1BS*#'S-s1C##S%'S%s1y##S-&%#'S8s1H##M'Ms1~##S8&%#j###E'S4s1N##S0GDQ>D#Qs#'GDF>D$Q#HDs21;D#s#'HDs1s8D$SR#9s#,S:GGS9#SHUSzG8D&SR(9s#/S:GGS9#SHIs#0S:GGS9S;Js#1S:GGS9$#Is#2S:GGS9S%<s#3S:GGS9$(#<s#4S:GGS9*)#l#9#s#0s#*l#:1s#7#l#;s#;s#:#j#?D#j#@D#j#ASA#j#BSA#'Cs1h##F#QF%#Pk###S%k##&#k#?D#k#@D#k#ASA#k#BSA#'Ks2J$S=#KE#KS=PMl#<0&#l#>s#Rs#O#l#Cs#\s#W#m##Ej#5s#,#U#Cj##s#4#'S0s2T##S4BDs2V;Ds#+#8D#SRs#.9s#US:GGS9#SH8Ds#0ST%9s#WS:GGS9#SHJs#XS:GGS9s#*#<s#YS:GGS9#s#.s#)<s#ZS:GGS9's#/#l#9#s#Vs#Pl#:s#7s#]#l#;s#as#`#j#?D#j#@D#j#ASA#j#BSA##s$-C$Fs$(%P#k###S%k##&#k#?D#k#@D#k#ASA#k#BSA##KS=KE#KS=PMl#<.%#l#>s#vs#s#l#Cs$$s#{#m##Ej#5B#U#Cj##s#V#6s#Ys#Ws#Us#'#Cl#Ds#as#\#j#Es$4#j#Fs$9#V#FCj##s$<#j##s$G#Ls$Hs$Ds$B#Cj#5s$J#j#$D#V#FCj##s$R#j#&D#MDs$]s$[#Cl#$s$ls$d#j#6s$n#U#Cj##s$y#0S6(#L0F(#C,s3?s3.S;#FP'Fs3.'#C$P#%&#%(#j#%D#2D#j#&D#2D#k##.#,s3Ks3:P#FQ$Q-%$#%&#j#%D#2D#j#&D#2D#0Q(#Fk##%#%/#,s3Xs3GS%#FS;$S;:%$#%&#j#%D#2D#j#&D#2D#k##.#j##-#0P(#Qk##>#j###Fj##?#VS{FCLA5)$#j#GD#j#Hs3l#k#GDs#$k#Hs3n#WCS-JF,s3os3^S4#FS$$S$s#1%$#%&#j#%D#2D#j#&D#2D#,s3xs3gS.#FS*$S*s#:%$#%&#j#%D#2D#j#&D#2D#j###E,s4&s3qS<$S+s#C%s%?#%%#j#%D#2D#j#&D#U#C,s4.s3yS/#FS,$S,s#L%$#%&#j#%D#2D#:DDQC,s46#S=#QS6'Qs4%'#C$S6#%&#%(#j#%D#2D#j###E:DDPC,s4A#S3#PS2'Ps40'#C$S2#%&#%(#j#%D#U#C:DDS;C,s4K#SF#S;S-'S;s4:'#C$S-#%&#%(#:DDS%F,s4S#S5#S%S8'S%s4B'#F$S8#%&#%(#j###E#MS4'Ms4I'#Q$S4#%&#:DDS0P,s4a#SE#S?S<'S?s4P'#S;$S<#%&#l#>s%^s%[s%Fl#Cs%hs%c#m##s%I[S3S1S%FS/s4)S-#'S/s4*##S1's4ZS%'S1###S/&&#'S=s40##S>'s4`M'S>###S=&&#j###E'S3s47##K'Ns4g'#K$SE#KE#NSEPMl#<s%4s%*#l#>s%vs%s#l#Cs&$s%{#m##Ej#5+#U#Cj##4#'s4rS0'K###S3>Ds%UPs%yGDP>D#Fs%{>D%P#BDs4yHDs3t;D$#;Ds%V#8D#SRs%Y9s&$S:GGS9#SH;Ds%Y(;D#(8Ds%]ST#9s&(S:GGS9#SHJs&)S:GGS9s%U#Is&*S:GGS9M<s&+S:GGS9$s%\#<s&,S:GGS9*s%]#l#9#s&(s%~l#:2s&/#l#;s&3s&2#j#?D#j#@D#j#ID#j#ASA#j#BSA#'s53Q'F###C's#oP$F#%S;#k###Mk##'#k#?D#k#@D#k#ID#k#ASA#k#BSA##NSE[CE#KNSEPMl#<2%#l#>s&Ms&J#l#Cs&Ws&R#m##Ej#5s#0#U#Cj##s#D#6s#Hs#Es#Cs#6#Cl#Ds#Qs#K#j#Es#V#j#Js#\#V#FCj##s#`#j##s#m#Ls#ns#is#g#Cj#5s#q#j#KD#V#FCj##s#|#j#&D#MDs$.s$,#Cj#5s$8#j#&D#V#FCj##s$B#j#&D#MDs$Ns$L#Cl#6s$`s$W#l#5s$ds$b#j#6s%8#U#Cj##s'V#6s'Xs'Ws'Qs%=#Cl#6s'Ss'_#j#6s'g#U#Cj##s's#+s2Ys2XC+s2]s2X#+s2as2X#+s2fs2X#+s2ks2X#+s,Fs,E#US##j#6s2z#U#Cj##s/.#6s'~s//s'x-#Cl#6s'zs(*#j#6s(2#U#Cj##s*:#6s/Ls*;s*9s(:#Cj#5s*A#U#Cj##s,^#6s4@s,_s,]s*M#Cj#5s,f#U#Cj##s/n#6s4es/os/ms,v#Cj#5s/w#U#Cj##s5)#6s5Hs5*s5(s00#Fl#Ls5Vs5T#j#6s5a#m##s5a.s5fs5bs5Z#j#Ms5i#j#Ns5n#j#8s5p#j#GD#`S|SCSDNs6(S#S's6$s5~S%S;P#j#Os6*#j#Ps6,#j#Qs65#j#Rs6A#j#SSc#j#TSc#j#Us6H#j#Hs6K#j#Vs6M#j#WD#j#XD#j#YD#j#ZD#j#[D#j#\D#j#]s6U#j#^s6V##"). Qed.

(* [comment removed for export] *)
Lemma fobj_off_block : forall s LB m LF m1 O n p A k,
  as_RHEAP H s LB m -> as_RFS H LF m1 -> aobj [] LF O n -> In (p, A, k) LB -> O + n <= A \/ A + k <= O.
Proof.
  intros s LB m LF m1 O n p A k RH RF AO IN. destruct AO as [(b & Hb & _)|(f & Hf & H1 & H2)]; [destruct Hb|].
  pose proof (ah_blocks H HH _ _ _ _ RH IN) as (_ & _ & K0 & _ & _ & KF & _). cbn [blk_addr blk_size fst snd] in K0, KF.
  pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (_ & F1 & F2 & _). pose proof (fsz_pos' (ff_class f) ltac:(pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & _); lia)).
  unfold AFS_HDR, AFS_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma sobj_scratch_off : forall LF m1 SP shi XS O n, as_RFS H LF m1 -> sobj SP shi O n -> Forall (fs_scratch H LF) XS ->
  Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) XS.
Proof. intros LF m1 SP shi XS O n RF SO FXS. unfold sobj in SO. eapply (scratch_off_hi H HH); [exact RF| exact FXS| lia]. Qed.
Lemma img_scratch_off : forall LF m1 XS A k, as_RFS H LF m1 -> Forall (fs_scratch H LF) XS -> A + k <= AIMG_TOP ->
  Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) XS.
Proof.
  intros LF m1 XS A k RF FXS HA. eapply Forall_impl; [| exact FXS]. intros iv FS. pose proof (scratch_facts H HH LF m1 [] iv RF FS) as (_ & K & _). left. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rs_at_putret (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z)
    (w : rsw) (cf : config) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5x s6x t3 t4 t5 t6 : word) (m : mem) (s : as_St H) (errv : word) (E2 : ecv) (tot : Z)
         (d2 : pst) (q : Z) (spa ff fp : Z) (mw80 : cell) (tmp gap : list cell) (hw : word) (optc : list cell) (j56 : list byte) (ectc : list cell) (j120 : list byte)
         (XS : list (Z * Z)),
    as_VIS H s (cfg_ms cf)
      = rs_ms RS_PUTRET (Z_to_bv 64 RS_PUTRET) sp spa (c_gp C) (c_tp C) t0 t1 t2 (c_E C) (wz (q - fb_in (w_FB w))) a1 a2 a3 a4 a5 a6 a7 tot (c_fb C) ff s5x s6x
              t3 t4 t5 t6 (c_F C) (c_fc C) m
    /\ as_AKREL H s cf /\ as_MPRES H (c_mo0 C) (cfg_model cf)
    /\ RWmF H C ((2, ff, fp) :: c_LF C) (mkW (pst_ret d2 (ps_LBn (w_d w)) (ps_g d2)) (ps_LBn d2 ++ w_PB w) (w_FBB w) (w_FB w) (w_fds w) (w_Fs w) (w_sds w) (w_nr w)) s errv E2 m
    /\ RWp H C MA (w_after_put w d2 true (q - fb_in (w_FB w)))
    /\ al_okR H s (ps_A d2) MA R
    /\ stk bsegs m (c_lo C) spa
    /\ rs_frames m sp spa ff fp (c_E C) (c_bs C) (c_P C) (c_fb C) mw80 tmp gap hw optc j56 ectc j120 248 s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra fr
    /\ fresh_frame H (c_LF C) 2 ff fp /\ (exists me, as_RFS H (c_LF C) me)
    /\ Forall (fs_scratch H (c_LF C)) XS
    /\ (forall a, (ff <= a < ff + 256 \/ Z.shiftr ff 3 + 2147450880 <= a < Z.shiftr ff 3 + 2147450880 + 32 \/ a = fp) -> rin_ivs XS a)
    /\ xpres H (c_LBin C) (c_SP C) (hread_X (c_P C) (c_E C) (c_fb C) (c_stb C) [] [] ++ XS) (c_m0 C) m
    /\ 0 <= tot /\ tot + zlength (w_fds w) + zlength (w_sds w) <= c_N C /\ w_nr w <= c_N C - zlength (w_sds w)
    /\ 1 <= fb_size (w_FB w) /\ fb_in (w_FB w) <= q <= fb_out (w_FB w)
    /\ (E2 = EC_clear \/ http_fail E2) /\ (E2 = EC_clear -> fb_in (w_FB w) < q \/ pc_state (ps_c d2) = 11) /\ (pc_state (ps_c d2) = 11 -> E2 = EC_clear)
    /\ wM (c_N C) w <= M0.

  Hypothesis BPUT : forall MX CX MA R, bput_stmtR H MX CX MA R.

(* [comment removed for export] *)
Lemma rs_put_call : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R ->
  rs_at_put H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (rs_at_putret C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w) cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 AT.
  pose proof STC as STC0.
  destruct C as [bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag].
  destruct cf as [msF mo]. unfold rs_at_put, rs_core, rs_frames in AT. unfold rs_at_putret, rs_frames. unfold rs_static in STC. unfold rs_placed in PLC.
  cbn_w_all. cbn [cfg_ms cfg_model] in AT |- *.
  destruct STC as (AOP & AOE & AOF & P8 & E8 & BS8 & FB8 & SEPPE & SEPPF & SEPEF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL & MB1).
  destruct PLC as (SOB & LOS & SP16 & SPHI & SPB & SPC & FRB128).
  destruct AT as (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s5x & s6x & t3 & t4 & t5 & t6 & m & s & errv & E1 & tot & spa & ff & fp & mw80 & tmp & gap & hw & optc & j56 & ectc & j120 & XS
                  & VIS & SZ1 & NS11 & KREL & MP & (RM & RP & ALK & ST & (FRM & SAVED & FR0 & SZFR & FAKE) & FF & (me & RF0) & FXS & FRX & XP0 & TOT0 & TOT & NRB) & WM0).
  pose proof RP as RP0. unfold RWmF in RM. unfold RWp in RP. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct RM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP & ERR & AUX & MI & RF' & AC & SK & ATH & ACP & ACE & SVE & ACB & ACF & SVA).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM_ & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof aceil_facts as (AF1 & AF2 & AF3). unfold HREAD_STACK in LOS. pose proof BPUT_STACK_val as BSV.
  destruct FRM as ((jl & LOW) & SLOTS & MW80 & MSZ & SH16 & (j96 & J96) & F120 & TMP & TSZ & GAP & GSZ & SPA).
  pose proof FAKE as (HDR & OPTC & OSZ & J56 & ECTC & ESZ & J120 & FPW & SHU & FL).
  assert (SPA64 : 0 <= spa < 2^64) by (clear - SPR LOS BSV CEIL AF1 SPA; lia).
  assert (SPACE : aceil <= spa) by (clear - LOS BSV CEIL SPA; lia).
  subst tp.
  pose proof SOB as SOB0. unfold sobj in SOB.
  set (LF' := (2, ff, fp) :: LF) in *.
  assert (SUBF : forall f, In f LF -> In f LF') by (intros f Hf; right; exact Hf).
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & SF1 & SA & M1 & M2 & LSH & SHH & SIDE & APFF & APP1 & APB).
  (* [comment removed for export] *)
  assert (NE : FB <> FB_empty) by (intros ->; cbn in SZ1; unfold fb_size in SZ1; cbn in SZ1; clear - SZ1; lia).
  destruct (fb_window _ _ LF' _ _ _ _ HP FBU NE) as (WIN & AOW & ACW & SVW & [pf INf] & BPOS & CPOS & BTOP & BCE & BAP & BIO & BOLE & FSZ).
  unfold fb_size, fb_cap in *.
  destruct (rw_cells_forget _ _ _ _ EC) as [ej ECb]. cbn [cells_size csize Nat.add ErrCodeCells length] in ECb.
  (* [comment removed for export] *)
  assert (SUB : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOP ltac:(intros b [])) as AOPn. pose proof (aobj_LB_mono _ LBin _ _ _ AOP ltac:(intros b [])) as AOPi.
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOE ltac:(intros b [])) as AOEn. pose proof (aobj_LB_mono _ LBin _ _ _ AOE ltac:(intros b [])) as AOEi.
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOF ltac:(intros b [])) as AOFn. pose proof (aobj_LB_mono _ LBin _ _ _ AOF ltac:(intros b [])) as AOFi.
  pose proof (aobj_LF_mono _ _ LF' _ _ AOPn SUBF) as AOPn'. pose proof (aobj_LF_mono _ _ LF' _ _ AOEn SUBF) as AOEn'. pose proof (aobj_LF_mono _ _ LF' _ _ AOFn SUBF) as AOFn'.
  pose proof (aobj_sub _ _ _ _ P PARSER_SIZE AOPn' ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear; lia)) as AOP344.
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOPn) as APP0. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOEn) as APE. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOFn) as APF.
  pose proof (aapp_sub _ _ P PARSER_SIZE APP0 ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear; lia)) as APP.
  pose proof (aapp_bounds _ _ APP ltac:(unfold PARSER_SIZE; clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (aapp_bounds _ _ APE ltac:(clear; lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (aapp_bounds _ _ APF ltac:(clear; lia)) as (T1 & T2 & T3 & T4 & T5).
  unfold PARSER_SIZE in Q2, Q3.
  pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOPn) as FOP. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOEn) as FOE. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOFn) as FOF.
  (* [comment removed for export] *)
  pose proof (aobj_range H HH _ _ _ _ _ _ _ HP RF0 AOPn) as [_ P352].
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOP FF ltac:(clear - Q4; lia) ltac:(clear; lia) ltac:(clear - P352 AF1; unfold AAPP_HI in *; lia)) as (DPF & DPS & DPP & _).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOE FF ltac:(clear - R4; lia) ltac:(clear; lia) ltac:(clear - R3 AF1; unfold AAPP_HI in *; lia)) as (DEF & DES & DEP & _).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOF FF ltac:(clear - T4; lia) ltac:(clear; lia) ltac:(clear - T3 AF1; unfold AAPP_HI in *; lia)) as (DFF & DFS & DFP & _).
  change (fsz 2) with 256 in DPF, DEF, DFF. change (fshn 2) with 32 in DPS, DES, DFS.
  (* [comment removed for export] *)
  pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOP INf) as WP. pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOE INf) as WE.
  pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOF INf) as WF.
  pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
  destruct UWc as (FC & _ & _ & MB & _).
  (* [comment removed for export] *)
  destruct (RWp_put_pre H HH _ MA _ (Z_to_bv 64 spa) s m STC0 RP0 HP UW NE ltac:(cbn_w; clear - BIO; lia) ltac:(cbn_w; clear - BOLE; lia) ltac:(cbn_w; exact FSZ)
              ltac:(cbn_w; rewrite unsigned_lit by exact SPA64; clear - SPC SPA; lia)) as (PL & PB_ & MXLE & CXLE).
  unfold pst_call in PL, PB_. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in PL, PB_.
  set (MX := put_MX _ _) in *. set (CX := put_CX _ _) in *. set (MA' := put_MA _ MA _) in *.
  assert (BRNN : 0 <= body_res es insz (zlength fds + zlength sds)) by (unfold body_res; unfold zlength in *; clear - CAP LES INZ; lia).
  pose proof PCOK as (_ & _ & _ & _ & _ & Hl & _). pose proof (pot_if_range (pc_state c)) as (PR34 & _).
  assert (FRNN : 0 <= fb_res N (fb_end FB - fb_begin FB)) by (apply fb_res_nonneg; [exact NR| unfold CAPMAX in *; clear - CPOS CPM; lia]).
  assert (MAR : Ag <= MA' <= MA) by (subst MA'; unfold put_MA; cbn_w; unfold fb_cap; clear - AL BRNN Hl PR34 FRNN AG0; lia).
  pose proof (al_okR_rebudget H HH _ _ _ _ MA' ALK MAR) as ALK'.
  (* [comment removed for export] *)
  pose proof (BPUT MX CX MA' (R + (as_Cm H MA - as_Cm H MA'))) as PS. unfold bput_stmtR in PS.
  unfold rs_ms in VIS |- *.
  replace (wz (fb_out FB - fb_in FB)) with (wz (Z.of_nat (length fds))) in VIS by (unfold wz; f_equal; unfold zlength in FSZ; clear - FSZ; lia).
  eapply (ah_seq H HH).
  { eapply (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s (LBn ++ LBin) LF' P E lo B shi pad7 pad2 ej (fb_in FB) (zlength fds + zlength sds) fds mb
               (mkPST c S L ns ls em h u es insz g rdi [] Ag) errv);
      [ exact VIS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact NS11
      | exact PC | exact ECb | exact RDI | exact HCT | exact FTS
      | exact (PutU_of _ _ _ _ _ _ UW WIN) | exact HOWN
      | exact PL | exact PB_
      | unfold put_static, put_pure; unfold wz; rewrite !unsigned_lit by exact SPA64;
        split; [ split; [unfold zlength in FSZ; clear - FSZ SZ1; lia|]; split; [clear - LOS BSV SPA; lia|]; split; [exact CEIL|]; split; [exact P8|]; split; [exact E8|];
                 split; [unfold PARSER_SIZE; clear - SEPPE; lia|];
                 split; [unfold PARSER_SIZE; unfold zlength in FSZ; clear - WP BIO BOLE FSZ; lia|];
                 split; [unfold zlength in FSZ; clear - WE BIO BOLE FSZ; lia|];
                 split; [clear - SP16 SPR SPA; Z.div_mod_to_equations; lia| clear - SPHI SPA; lia]
               | split; [clear; unfold zlength; lia|]; split; [clear - SPB SPA; lia|]; split; [reflexivity|]; split; [exact MXLE| exact CXLE] ]
      | exact HP | exact KREL | exact AUX
      | unfold wz; rewrite unsigned_lit by exact SPA64; exact ST | exact ERR | exact MI
      | unfold RS_PUTRET; rewrite unsigned_lit by (clear; lia); reflexivity
      | exact AOP344 | exact ACP
      | exact AOEn' | exact ACE | exact SVE
      | unfold zlength; exact AOW | unfold zlength; exact ACW | unfold zlength; exact SVW
      | exact RF' | subst LF'; cbn [length]; clear - LFL4; lia | subst LF'; cbn [length]; clear - LFL1; lia | exact AC | exact SK
      | exact ALK' | exact MB1 ]. }
  clear PS. intros [ms2 mo2] PO. unfold bput_postR in PO. cbn [cfg_ms cfg_model] in PO.
  destruct PO as (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & k3 & k4 & k5 & k6 & m2 & errv2 & s2 & d2 & q & E2 & XS2
                  & VIS2 & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & PC2 & EC2 & EOUT2 & RDI2 & HC2 & FTS2 & U2 & HOWN2 & PL2 & PB2 & FXS2 & XP2 & QR & PROG & ST11 & HDJ2 & BDJ2
                  & RF2 & AC2 & SK2 & AL2 & AMONO).
  unfold wz in ST2, XP2. rewrite unsigned_lit in ST2, XP2 by exact SPA64.
  replace (ret_pc (Z_to_bv 64 RS_PUTRET)) with (Z_to_bv 64 RS_PUTRET) in VIS2 by (symmetry; apply ret_pc_even; [unfold RS_PUTRET; clear; lia| reflexivity]).
  (* [comment removed for export] *)
  pose proof (RWp_put_post H HH _ MA _ (Z_to_bv 64 spa) d2 q true STC0 RP0 ltac:(cbn_w; intros _; unfold fb_cap; clear - BPOS CPOS; lia)
                ltac:(cbn_w; clear - BIO; lia) ltac:(cbn_w; clear - BOLE; lia) ltac:(cbn_w; exact FSZ)
                ltac:(cbn_w; rewrite unsigned_lit by exact SPA64; clear - SPC SPA; lia) PL2 PB2 ltac:(cbn_w; unfold zlength; exact QR)) as RP2.
  destruct d2 as [c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 A2]. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct (PutU_split _ _ _ _ _ _ U2) as [UW2 _].
  unfold PutL in PL2. unfold PutB in PB2. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A app] in PL2, PB2.
  pose proof PL2 as (PCOK2 & OWN2 & MOWN2 & _ & _ & OFFP2 & OFFE2 & _ & _ & _ & _ & _ & CAP2 & LES2 & INZ2 & _ & _ & _ & _ & _ & _ & _ & _ & A02).
  destruct PB2 as (_ & _ & _ & B24).
  assert (BRNN2 : 0 <= body_res es2 insz2 (zlength fds + zlength sds - (q - fb_in FB))) by (unfold body_res; unfold zlength in *; clear - CAP2 LES2 INZ2 QR; lia).
  pose proof PCOK2 as (_ & _ & _ & _ & _ & Hl2 & _). pose proof (pot_if_range (pc_state c2)) as (PR34b & _).
  pose proof (al_okR_unbudget H _ _ _ _ _ AL2 R0 ltac:(clear - B24 BRNN2 Hl2 PR34b A02 MAR; lia)) as ALK2.
  (* [comment removed for export] *)
  assert (XHI : forall A0 cs, rw_cells bsegs m A0 cs -> spa <= A0 -> rw_cells bsegs m2 A0 cs).
  { intros A0 cs K HA. eapply (xpres_rw_cells H); [exact XP2| exact K|]. split; [left; exact HA|]. apply Forall_app. split.
    - eapply put_X_hi; [exact FC| exact MB| exact APP| exact APE| clear - HA SPACE; lia].
    - eapply (scratch_off_hi H HH); [exact RF'| exact FXS2| clear - HA SPACE; lia]. }
  pose proof (XHI _ _ LOW ltac:(clear; lia)) as LOW'. pose proof (XHI _ _ SLOTS ltac:(clear; lia)) as SLOTS'. pose proof (XHI _ _ MW80 ltac:(clear; lia)) as MW80'.
  pose proof (XHI _ _ SH16 ltac:(clear; lia)) as SH16'. pose proof (XHI _ _ J96 ltac:(clear; lia)) as J96'. pose proof (XHI _ _ F120 ltac:(clear; lia)) as F120'.
  pose proof (XHI _ _ TMP ltac:(clear; lia)) as TMP'. pose proof (XHI _ _ GAP ltac:(clear; lia)) as GAP'.
  pose proof (XHI _ _ SAVED ltac:(clear - SPA; lia)) as SAVED'. pose proof (XHI _ _ FR0 ltac:(clear - SPA; lia)) as FR0'. pose proof (XHI _ _ BSC ltac:(clear - SOB SPA; lia)) as BSC'.
  clear LOW SLOTS MW80 SH16 J96 F120 TMP GAP SAVED FR0 BSC.
  (* [comment removed for export] *)
  assert (PXC : forall O n, aclient_range H LBin SP O n -> 0 < n -> (O + n <= P \/ P + 242 <= O) -> (O + n <= E \/ E + 24 <= O) -> AIMG_TOP <= O ->
                Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) (put_X P E L es)).
  { intros O n CR Hn DP DE OT. eapply put_X_Forall; [exact FC| exact MB| exact DP| exact DE| | | |]; cbn [fst snd].
    - right. unfold AG_HTTP_CAT, AIMG_TOP in *. clear - OT. lia.
    - right. unfold AG_FIELD_TABLE, AIMG_TOP in *. clear - OT. lia.
    - intros e dd Hd. pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
      exact (FRL e ltac:(apply (proj2 (DOM e)); rewrite Hd; eexists; reflexivity) O n CR Hn).
    - intros x s0 IN. destruct (FRB x s0 IN O n CR Hn); [left| right]; lia. }
  (* [comment removed for export] *)
  pose proof (fsobj_inframe H LF' (2, ff, fp) ff 256 ltac:(left; reflexivity) ltac:(cbn [ff_addr fst snd]; clear; lia) ltac:(cbn [ff_addr ff_class fst snd]; change (fsz 2) with 256; clear; lia)) as FOFF.
  assert (XFR : forall A0 cs, rw_cells bsegs m A0 cs -> ff <= A0 -> A0 + Z.of_nat (cells_size cs) <= ff + 256 -> 0 < Z.of_nat (cells_size cs) -> rw_cells bsegs m2 A0 cs).
  { intros A0 cs K HA HB POS. eapply (xpres_rw_cells H); [exact XP2| exact K|]. split.
    - right; right; right; right; left. clear - HA HB F7 F8. unfold AFS_SIZE, AFS_HDR in *. lia.
    - apply Forall_app. split.
      + apply PXC; [right; right; right; right; left; clear - HA HB F7 F8; unfold AFS_SIZE, AFS_HDR in *; lia| exact POS| clear - HA HB DPF; lia| clear - HA HB DEF; lia| clear - HA F1; unfold AFS_HDR in *; lia].
      + pose proof (Forall_scratch H HH LF' m XS2 ff 256 RF' FOFF ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - F2 AF1; lia) APFF FXS2) as K2.
        eapply Forall_impl; [| exact K2]. intros [u0 v0] KK. cbn [fst snd] in *. clear - KK HA HB. lia. }
  pose proof (XFR _ _ HDR ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as HDR'.
  pose proof (XFR _ _ OPTC ltac:(clear; lia) ltac:(rewrite OSZ; clear; lia) ltac:(rewrite OSZ; clear; lia)) as OPTC'.
  pose proof (XFR _ _ J56 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J56'.
  pose proof (XFR _ _ ECTC ltac:(clear; lia) ltac:(rewrite ESZ; clear; lia) ltac:(rewrite ESZ; clear; lia)) as ECTC'.
  pose proof (XFR _ _ J120 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J120'.
  pose proof (XFR _ _ FPW ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as FPW'.
  assert (SHU' : rw_cells bsegs m2 (Z.shiftr ff 3 + 2147450880) (rs_shcells 248 248)).
  { eapply (xpres_rw_cells H); [exact XP2| exact SHU|]. unfold rs_shcells. cbn [cells_size csize Nat.add length repeat]. split.
    - right; right; right; right; right; left. rewrite SHFF. clear - M1 M2. lia.
    - apply Forall_app. split.
      + pose proof (noshadow_avoid_sh _ ff 256 (put_X_noshadow _ _ _ _ _ _ _ _ _ _ E FC MB APP APE) ltac:(clear - F1; unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(clear; lia)
                      ltac:(unfold AAPP_HI; clear - F2 AF1; lia)) as K. rewrite SHFF. change (nsh 256) with 32 in K. exact K.
      + pose proof (Forall_scratch_sh H HH LF' m XS2 ff 256 RF' FOFF ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - F2 AF1; lia) APFF FXS2) as K.
        rewrite SHFF. change (nsh 256) with 32 in K. exact K. }
  assert (FL' : rw_cells bsegs m2 fp [C1 (b8 1)]).
  { eapply (xpres_rw_cells H); [exact XP2| exact FL|]. cbn [cells_size csize Nat.add]. split.
    - right; right; right; right; left. clear - F5 F6 F7 F8. unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *. lia.
    - apply Forall_app. split.
      + apply PXC; [right; right; right; right; left; clear - F5 F6 F7 F8; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; lia| clear; lia| clear - DPP; lia| clear - DEP; lia| clear - F4; unfold AFS_FLAGS in *; lia].
      + eapply Forall_impl; [| exact FXS2]. intros iv K. exact (scratch_flag H HH _ _ _ _ _ _ RF' K). }
  clear HDR OPTC J56 ECTC J120 FPW SHU FL.
  (* [comment removed for export] *)
  pose proof (Forall_scratch H HH LF' m XS2 P 352 RF' (aobj_fsobj H HH _ _ _ _ _ _ HP AOPn') ltac:(clear; lia) ltac:(clear - P352 AF1; unfold AAPP_HI; lia) APP0 FXS2) as FXP.
  pose proof (aobj_aclient_range H HH _ _ _ SP _ _ RF0 AOPi) as CRP.
  assert (XJ : forall O k (jj : list byte), rw_cells bsegs m O [CB k jj] -> P + 242 <= O -> 0 < Z.of_nat k -> O + Z.of_nat k <= P + 352 -> rw_cells bsegs m2 O [CB k jj]).
  { intros O k jj K HO HK HE. eapply (xpres_rw_cells H); [exact XP2| exact K|]. replace (Z.of_nat (cells_size [CB k jj])) with (Z.of_nat k) by (cbn; lia).
    pose proof (aclient_range_sub H _ _ _ _ O (Z.of_nat k) CRP ltac:(clear - HO; lia) ltac:(clear - HE; lia) ltac:(clear - HK; lia)) as CRO.
    split.
    - eapply aclient_range_LB_mono; [| exact SUB]. eapply aclient_range_SP_mono; [exact CRO| clear - SPC SPA; lia].
    - apply Forall_app. split.
      + apply PXC; [exact CRO| exact HK| right; exact HO| clear - SEPPE HO HE; lia| clear - Q1 HO; lia].
      + eapply Forall_impl; [| exact FXP]. intros [l hh] K1. cbn in K1 |- *. clear - K1 HO HE. lia. }
  pose proof (XJ _ _ _ J13 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as J13'. pose proof (XJ _ _ _ J32a ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as J32a'.
  pose proof (XJ _ _ _ J8a ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as J8a'. pose proof (XJ _ _ _ J32b ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as J32b'.
  pose proof (XJ _ _ _ J8b ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as J8b'.
  clear J13 J32a J8a J32b J8b XJ.
  (* [comment removed for export] *)
  assert (MV2 : AMiscVt48 m2).
  { unfold AMiscVt48 in MV |- *. eapply (ro_cells_xpres H); [exact XP2| exact MV|]. cbn [cells_size csize Nat.add]. unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR. split.
    - right; left. intros a Ha. unfold aimg_client. clear - Ha. lia.
    - apply Forall_app. split; [eapply put_X_img; [exact FC| exact MB| exact APP| exact APE| unfold AG_HTTP_CAT; clear; lia]|].
      eapply img_scratch_off; [exact RF'| exact FXS2| unfold AIMG_TOP; clear; lia]. }
  clear MV.
  (* [comment removed for export] *)
  assert (FBU2 : AFlatBuf (LBn ++ LBin) m2 fb FB fds).
  { eapply (AFlatBuf_xpres H); [exact FBU| exact XP2| | |].
    - eapply (xclient_range_aobj H HH); [exact HP| exact RF'| exact AOFn'| unfold SZ_FB; clear; lia| | exact FXS2].
      unfold SZ_FB. apply PXC; [exact (aobj_aclient_range H HH _ _ _ SP _ _ RF0 AOFi)| clear; lia| unfold PARSER_SIZE in *; clear - SEPPF; lia| clear - SEPEF; lia| exact T1].
    - intros _. apply Forall_app. split.
      + eapply put_X_fbblk; [exact FC| exact MB| unfold PARSER_SIZE; clear - WP; lia| clear - WE; lia| exact BTOP| exact (DJL NE)| exact (DJB NE)].
      + eapply Forall_impl; [| exact (Forall_scratch H HH LF' m XS2 (fb_begin FB) (fb_end FB - fb_begin FB) RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP INf) ltac:(clear - CPOS; lia)
                                       ltac:(clear - BCE AF2 AF1; unfold AAPP_HI; lia) BAP FXS2)].
        intros [l hh] K1. cbn in K1 |- *. clear - K1. lia.
    - intros _. apply Forall_app. split.
      + eapply noshadow_avoid_sh; [eapply put_X_noshadow; [exact FC| exact MB| exact APP| exact APE]| clear - BPOS; lia| unfold fb_cap; clear - CPOS; lia| unfold fb_cap; clear - BCE AF2 AF1; unfold AAPP_HI; lia].
      + unfold fb_cap. exact (Forall_scratch_sh H HH LF' m XS2 (fb_begin FB) (fb_end FB - fb_begin FB) RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP INf) ltac:(clear - CPOS; lia)
                 ltac:(clear - BCE AF2 AF1; unfold AAPP_HI; lia) BAP FXS2). }
  clear FBU.
  (* [comment removed for export] *)
  pose proof (rblock_bounds _ _ RBS) as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6).
  assert (CRS : aclient_range H LBin SP stb SZ_SPCI_STATE) by (right; right; left; exists (p7, stb, SZ_SPCI_STATE); split; [exact INS| cbn; clear; lia]).
  pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOP (SUB _ INS)) as PS1. pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOE (SUB _ INS)) as ES1.
  assert (SB2' : AStateBlock (LBn ++ LBin) m2 stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds).
  { eapply (AStateBlock_xpres H); [exact SB| exact XP2| | | |]; cbn [st_fb].
    - apply Forall_app. split.
      + apply PXC; [exact CRS| unfold SZ_SPCI_STATE; clear; lia| clear - PS1; lia| clear - ES1; lia| exact SB4].
      + exact (Forall_scratch H HH LF' m XS2 stb SZ_SPCI_STATE RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP (SUB _ INS)) SB2 SB3 (proj1 (proj2 (proj2 (proj2 RBS)))) FXS2).
    - apply Forall_app. split.
      + eapply noshadow_avoid_sh; [eapply put_X_noshadow; [exact FC| exact MB| exact APP| exact APE]| exact SB1| exact SB2| exact SB3].
      + exact (Forall_scratch_sh H HH LF' m XS2 stb SZ_SPCI_STATE RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP (SUB _ INS)) SB2 SB3 (proj1 (proj2 (proj2 (proj2 RBS)))) FXS2).
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. rewrite SA', SE. destruct (INA N1) as [p9 IN9].
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ IN9)) as (A1 & _ & A3 & A4 & A5 & _ & A7). cbn [blk_addr blk_size fst snd] in A1, A3, A4, A5, A7.
      replace (A + N) with (A + N) by reflexivity.
      apply Forall_app. split.
      + apply (PXC A N); [right; right; left; exists (p9, A, N); split; [exact IN9| cbn; clear; lia]| clear - N1; lia
          | pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOP (SUB _ IN9)); clear - H0; lia
          | pose proof (fobj_off_block _ _ _ _ _ _ _ _ _ _ HP RF0 AOE (SUB _ IN9)); clear - H0; lia | exact A4].
      + exact (Forall_scratch H HH LF' m XS2 A N RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP (SUB _ IN9)) A3 ltac:(clear - A5 AF1 AF2; unfold AAPP_HI; lia) A7 FXS2).
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. unfold fb_cap. rewrite SA', SE. destruct (INA N1) as [p9 IN9].
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ IN9)) as (A1 & _ & A3 & A4 & A5 & _ & A7). cbn [blk_addr blk_size fst snd] in A1, A3, A4, A5, A7.
      replace (A + N - A) with N by (clear; lia).
      apply Forall_app. split.
      + eapply noshadow_avoid_sh; [eapply put_X_noshadow; [exact FC| exact MB| exact APP| exact APE]| clear - A1; lia| exact A3| clear - A5 AF1 AF2; unfold AAPP_HI; lia].
      + exact (Forall_scratch_sh H HH LF' m XS2 A N RF' (fsobj_block H HH _ _ _ LF' _ _ _ HP (SUB _ IN9)) A3 ltac:(clear - A5 AF1 AF2; unfold AAPP_HI; lia) A7 FXS2). }
  clear SB.
  (* [comment removed for export] *)
  pose proof (put_X_noshadow _ _ _ _ _ _ _ _ _ _ E FC MB APP APE) as PNS.
  pose proof (aobj_xpres_accessible H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP RF' AOPn' ltac:(clear; lia) XP2 PNS FXS2 ACP ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear; lia)) as ACP2.
  pose proof (aobj_xpres_accessible H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP RF' AOEn' ltac:(clear; lia) XP2 PNS FXS2 ACE ltac:(clear; lia) ltac:(clear; lia)) as ACE2.
  pose proof (cobj_xpres_accessible H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP RF' (cobj_of_sobj (LBn ++ LBin) LF' _ _ _ _ SOB0) ltac:(clear; lia) XP2 PNS FXS2 ACB ltac:(clear; lia) ltac:(clear; lia)) as ACB2.
  pose proof (aobj_xpres_accessible H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP RF' AOFn' ltac:(clear; lia) XP2 PNS FXS2 ACF ltac:(clear; lia) ltac:(clear; lia)) as ACF2.
  assert (SUB2 : forall b, In b (LBn ++ LBin) -> In b (LBn2 ++ LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  pose proof (aobj_shvis H HH _ _ _ _ _ _ HP2 RF2 (aobj_LB_mono _ _ _ _ _ (aobj_LF_mono _ _ LF' _ _ AOE SUBF) ltac:(intros b [])) ltac:(clear; lia)) as SVE2.
  assert (SVA2 : 1 <= N -> shvis m2 A (A + N)).
  { intros N1. destruct (INA N1) as [p9 IN9]. exact (ah_blk_shvis H HH _ _ _ _ _ _ HP2 (SUB2 _ (SUB _ IN9))). }
  pose proof (ah_thr H HH _ _ _ HP2) as ATH2.
  (* [comment removed for export] *)
  assert (XP02 : xpres H LBin SP (hread_X P E fb stb [] [] ++ (XS ++ XS2)) m0 m2).
  { eapply xpres_trans.
    - eapply xpres_weaken; [exact XP0| clear; lia| intros b Hb; exact Hb| intros a K]. rewrite app_assoc. apply rin_ivs_app. left. exact K.
    - eapply xpres_weaken; [eapply xpres_put_hread; [exact XP2| exact FRL| exact FRB| clear - SPC SPA; lia]| clear; lia| intros b Hb; exact Hb| intros a K].
      apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K| right; apply rin_ivs_app; right; exact K]. }
  apply (ah_done H HH).
  exists k0, k1, k2, l1, l2, l3, l4, l5, l6, l7, s5x, s6x, k3, k4, k5, k6, m2, s2, errv2, E2, tot,
         (mkPST c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 A2), q, spa, ff, fp, mw80, tmp, gap, hw, optc, j56, ectc, j120, (XS ++ XS2).
  cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
  split; [exact VIS2|]. split; [exact KREL2|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP2)|].
  split.
  { (* [comment removed for export] *)
    unfold RWmF, pst_ret. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A]. rewrite <- !app_assoc.
    split; [exact PC2|]. split; [exact UW2|]. split; [exact HOWN2|]. split; [exact RDI2|].
    split; [exact J13'|]. split; [exact J32a'|]. split; [exact J8a'|]. split; [exact J32b'|]. split; [exact J8b'|].
    split; [exact HC2|]. split; [exact FTS2|]. split; [exact MV2|].
    split; [eapply AFlatBuf_mono; [exact SUB2| exact FBU2]|].
    split; [exact EC2|]. split; [exact BSC'|].
    split; [eapply AStateBlock_mono; [exact SUB2| exact SB2']|].
    split; [exact HP2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact MI2|].
    split; [exact RF2|]. split; [exact AC2|]. split; [exact SK2|]. split; [exact ATH2|].
    split; [exact ACP2|]. split; [exact ACE2|]. split; [exact SVE2|]. split; [exact ACB2|]. split; [exact ACF2| exact SVA2]. }
  split; [exact RP2|]. split; [exact ALK2|]. split; [exact ST2|].
  split.
  { split; [| split; [exact SAVED'| split; [exact FR0'| split; [exact SZFR|]]]].
    - split; [exists jl; exact LOW'|]. split; [exact SLOTS'|]. split; [exact MW80'|]. split; [exact MSZ|]. split; [exact SH16'|]. split; [exists j96; exact J96'|].
      split; [exact F120'|]. split; [exact TMP'|]. split; [exact TSZ|]. split; [exact GAP'|]. split; [exact GSZ| exact SPA].
    - split; [exact HDR'|]. split; [exact OPTC'|]. split; [exact OSZ|]. split; [exact J56'|]. split; [exact ECTC'|]. split; [exact ESZ|].
      split; [exact J120'|]. split; [exact FPW'|]. split; [exact SHU'| exact FL']. }
  split; [exact FF|]. split; [exists me; exact RF0|].
  split; [apply Forall_app; split; [exact FXS| eapply Forall_scratch_popC; exact FXS2]|].
  split; [intros a Ha; apply rin_ivs_app; left; exact (FRX a Ha)|]. split; [exact XP02|].
  split; [exact TOT0|]. split; [exact TOT|]. split; [exact NRB|].
  split; [exact SZ1|]. split; [unfold zlength in FSZ; clear - QR FSZ; lia|].
  split; [exact EOUT2|]. split; [exact PROG|]. split; [exact ST11|]. exact WM0.
Qed.
End HCW.

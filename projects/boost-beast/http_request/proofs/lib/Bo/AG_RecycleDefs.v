(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Frame Arr CellsX TacX Image SysStep SFModel.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR LazyNodes SReach.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepX AsDepotInv AW_DepotFrame SecLazy SecLazy2.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AG_MallocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AG_Malloc2 AG_RepQ AG_WriteSet.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition pendz (st : astate) (XB : list Z) (a : Z) : Prop :=
    exists x, In x XB /\ (x <= a < x + class_size (class_of_addr st x) \/ sh x <= a < sh x + class_size (class_of_addr st x) / 8).

  Lemma pendz_mono : forall st XB XB' a, (forall x, In x XB -> In x XB') -> pendz st XB a -> pendz st XB' a.
  Proof. intros st XB XB' a SUB (x & Hx & R). exists x. split; [exact (SUB x Hx)| exact R]. Qed.
  Lemma pendz_sb : forall st st' XB a, as_space_beg st' = as_space_beg st -> pendz st XB a <-> pendz st' XB a.
  Proof.
    intros st st' XB a E. unfold pendz, class_of_addr. rewrite E. tauto.
  Qed.

  (* [comment removed for export] *)
  Definition secgone (s s' : ast) (a : Z) : Prop :=
    exists sc, In sc (as_sec (a_st s)) /\ ~ In sc (as_sec (a_st s'))
               /\ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc \/ sh (sc_map_beg sc) <= a < sh (sc_map_beg sc + sc_map_size sc)).
  Definition avis (s s' : ast) (m m' : mem) : Prop :=
    forall x : word, wview bsegs m x <> None -> wview bsegs m' x <> None \/ secgone s s' (bv_unsigned x).

  Lemma avis_of_wmono : forall s s' m m', wmono bsegs m m' -> avis s s' m m'.
  Proof. intros s s' m m' WM x V. left. exact (WM x V). Qed.
  Lemma avis_of_wmono_out : forall s s' X m m',
    wmono_out X m m' -> (forall iv a, In iv X -> fst iv <= a < snd iv -> secgone s s' a) -> avis s s' m m'.
  Proof.
    intros s s' X m m' WM SUB x V.
    assert (D : outside X (bv_unsigned x) \/ secgone s s' (bv_unsigned x)).
    { clear WM V. induction X as [|[lo' hi'] X IH]; [left; exact I|]. cbn.
      destruct (Z.lt_ge_cases (bv_unsigned x) lo') as [L|G]; [| destruct (Z.lt_ge_cases (bv_unsigned x) hi') as [L2|G2]].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S].
      - right. apply (SUB (lo', hi') (bv_unsigned x)); [left; reflexivity| cbn; lia].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S]. }
    destruct D as [O|S]; [left; exact (WM x O V)| right; exact S].
  Qed.

  (* [comment removed for export] *)
  Definition alive (st : astate) (a : Z) : Prop :=
    exists ch, In ch (chunk_list st) /\ ch_state ch = CAllocated
               /\ (ch_user_beg ch <= a < ch_user_beg ch + ch_used ch \/ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch)).
  (* [comment removed for export] *)
  Definition alive_kept (st st' : astate) : Prop :=
    forall ch, In ch (chunk_list st) -> ch_state ch = CAllocated -> In ch (chunk_list st').
  Lemma alive_kept_refl : forall st, alive_kept st st.
  Proof. intros st ch H _. exact H. Qed.
  Lemma alive_kept_trans : forall a b c, alive_kept a b -> alive_kept b c -> alive_kept a c.
  Proof. intros a b c A B ch H E. exact (B ch (A ch H E) E). Qed.
  Lemma alive_mono : forall st st' a, alive_kept st st' -> alive st a -> alive st' a.
  Proof. intros st st' a K (ch & H & E & R). exists ch. split; [exact (K ch H E)|]. exact (conj E R). Qed.
  Lemma agree_alive_trans : forall st0 st1 m0 m1 m2, alive_kept st0 st1 ->
    agree_on (alive st0) m0 m1 -> agree_on (alive st1) m1 m2 -> agree_on (alive st0) m0 m2.
  Proof. intros st0 st1 m0 m1 m2 K A B a Ha Hr. rewrite (B a (alive_mono _ _ a K Ha) Hr). exact (A a Ha Hr). Qed.

  (* [comment removed for export] *)
  Section Compose.
    Variables (s0 s1 s2 : ast) (d : depot) (lo SP : Z) (m0 m1 m2 : mem) (mo0 mo1 mo2 : Model).
    Hypothesis E1 : a_thr s1 = a_thr s0 /\ a_sb s1 = a_sb s0 /\ a_pa s1 = a_pa s0.
    Hypothesis SUB1 : forall sc, In sc (as_sec (a_st s1)) -> In sc (as_sec (a_st s0)).
    Hypothesis SUB2 : forall sc, In sc (as_sec (a_st s2)) -> In sc (as_sec (a_st s1)).

    Lemma awrit_01_02 : forall a, awrit s0 s1 d lo SP a -> awrit s0 s2 d lo SP a.
    Proof. intros a W. apply (awrit_mono s0 s1 s2 d lo SP a); [| exact W]. intros sc Hsc. right. exact (SUB1 sc Hsc). Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.
    Lemma awrit_12_02 : forall a, awrit s1 s2 d lo SP a -> awrit s0 s2 d lo SP a.
    Proof.
      ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_WriteSet.awrit); constr:(s1); constr:(s2); constr:(d); constr:(lo); constr:(SP); constr:(E1); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.a_thr); constr:(s0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.a_sb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.a_pa); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPageSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kSpaceSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPtrArrayReserve); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.a_st); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_size); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_WriteSet.astatw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_nb); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_sb); constr:(@kc__2); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or_intror); constr:(@kc__3); constr:(@Corelib.Init.Logic.ex_intro); constr:(SUB1); constr:(@Corelib.Init.Logic.or_ind); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk))|] [|@sc; @z; @H4; @H; @H3; @H2; @H1; @H0; @I; @R; @x; @W; @Ep; @Es; @Et; @a0; @a|] "#1F#F#u#e###N#O#.#/#A#0#%#1#2#3#4#5#6#7#8#9#:#;#<#>#@#B#D#-#$#I#C#&#T#(#P#M#K#L#`#=#*#?#E#a#c#'#)#S#U#V#n#x#_#m#o#,#w#v#u#Q#Y#[#Z#t#d#\#l#q#^#f#b#r#s#p#]#i#j#k#J#R#h#g#X#W<#\%#]%#^%#_%#`&#a%#b%#c$#d(#e$#f&#g$#h&#i'#j)#k$#l$#m$#n%#o)#p&#q$#r$#s)#t(6S5S6S4EFDUS@S5US@S17S.$#USAS5USAS17S.$#USBS5USBS17S.$##&##*#6S1S6S4EFS0j##$#6S1S6S4EFS9j##'#&EG%GF#$#,SE,#,#,#,#,#2#)D#&#G)DS7%G##%#&=G)>S<)#S7%G##&#.B&#G.'%G##%#&s#$G)s#%S=%G##%#8S59#-CD#8S69#-CD#$&#3D&#H4D)%#%H##&#.(&#H2s#)5)#)&#%H##'#$*##1#j#$C#(C#*GUSFS4&#G2s#4,s#3,#,#,#,#,#,#,#,#,#2#VSC.#)1#%G##2#USGS4&#G,*,#2#VSCs###)(#%G##)#$,#$?#$A#$s#:#$s#?#$s#E#$s#K#$s#X#j#%S.#:S.s#k#SHs#jS2&ES,%S,F#$#)s#ns#W&#S,)s#pS7%S,##%#&s#qS,%S,s#U#$#&s#TS,%S,s#S#$#&s#tS,%S,s#R#$#&s#JG%Gs#H#$#&s#GG%Gs#D#$#$&##s#R#j#$C#(C#*S,&s#CS,%S,s#5#$#&s#4S,%S,s#/#$#$&#$*#$,#$7#$;#$?#$s###$s#)#&EH%HF#$#&s#,H%Hs#+#$#&DH)DS<)#S7%H##&#.D&#H.'%H##%#&s$DH%Hs#~#$#&s#vJ%Js#t#$#&s#sJ%Js#p#$#$&##s#~#j#$C#(C#*H&s#oH%Hs#a#$#&s#`H%Hs#[#$#$&#$*#$,#$7#$;#$A#$s#'#$s#+#j#%S.#:S.s$d#Ds$cK&s#WG%Gs#V#$#&s$gG)s$hS<)#S7%G##&#.s$l&#G.'%G##%#$#s#n$)#$/#$s$g#&EJ%JF#$#&s#kJ%Js#j#$#&s${J%J5#$#&4J%J3#$#&DJ)DS=%J##%#&s$VL%Ls$T#$#&s$SL%Ls$P#$#$&##s$^#j#$C#(C#*J&s$OJ%Js$A#$#&s$@J%Js$;#$#$&#$*#$,#$7#$<#$@#$s#$#$s#(#j#%S.#:S.s%A#Ds%@K&s%DH%Hs#:#$#&s#9H%Hs#8#$#&s%GH)s%HS=%H##%#$#s#P$(#$,#$s#t#$s#x#&s%PJ%J+#$#$#<$s#5#$s#9#$s#=#$s#A#&EL%LF#$#&s$QL%Ls$P#$#&s%aL%Ls#W#$#&s#VL%Ls#U#$#&s%dL%L?#$#8S19#-CD#$#s%@&s%?M%Ms%=#$#&s%<M%Ms%9#$#$&##*#j#$C#(C#*L&s%8L%Ls%*#$#&s%)L%Ls%$#$#$&#$*#$,#$;#$?#$s###$s#'#$s#+#j##s#/#&EM%MF#$#&s$~M%Ms$}#$#&s&2M%Ms$(#$#&s$'M%Ms$&#$#&s&5M%Ms#L#$#&s%hN%Ns%f#$#&s%eN%Ns%b#$#$&##s#3#j#$C#(C#*M&s%aM%Ms%S#$#&s%RM%Ms%M#$#$&#$*#$,#$7#$;#$?#$s###$s#'#&EO%OF#$#&s%JO%Os%I#$#&s&ZO%Os$P#$#&s$OO%Os$N#$#&s&]O%Os#t#$#&s&4P%Ps&2#$#&s&1P%Ps&.#$#$&##s#[#j#$C#(C#*O&s&-O%Os%{#$#&s%zO%Os%u#$#$&#$*#$,#$7#$;#$?#$s###$s#'#%PF&EQ%QF#$#&s%sQ%Qs%r#$#&s''Q%Qs$y#$#&s$xQ%Qs$w#$#&s'*Q%Qs$A#$#&s&]R%Rs&[#$#&s&ZR%Rs&W#$#$&##s$(#j#$C#(C#*Q&s&VQ%Qs&H#$#&s&GQ%Qs&B#$#$&#$*#$,#$7#$;#$?#$s###$s#'#&ES#%S#F#$#&s&?S#%S#s&>#$#&s'OS#%S#s%E#$#&s%DS#%S#s%C#$#&s'RS#%S#s$i#$#&s')S$%S$s''#$#&s'&S$%S$s'##$#$&##s$P#j#$C#(C#*S#&s&~S#%S#s&p#$#&s&oS#%S#s&j#$#$&#$*#$,#$7#$;#$?#$s###0s#)s#(S0K/s#($#j#&s'n#j#'s'r#+s'ss'ps#.#Kj#(s#W#j#)s$$#+s$%s$$s#Z#Kj#*s's#j#+s'{#+s'|s'us$)#S3j#'s$|#U#Dj##s%d##s'Ps$hj#$C#(C#$#s$_$s$w#$s${#$s%##$s%'##s'Xs$Gj#$C#(C#$#s$>$s$R#$s$V#$s$Z#$s$^#&EN%NF#$#&s'(N%Ns''#$#&s(8N%Ns&.#$#&s&-N%Ns&,#$#&s(;N%Ns%R#$#&s'nO%Os'l#$#&s'kO%Os'h#$#$&##s%9#j#$C#(C#*N&s'gN%Ns'Y#$#&s'XN%Ns'S#$#$&#$*#$,#$7#$;#$?#$s###$s#'#j##s#+#%Rs'L$s#os#K&ES%%S%F#$#&s'SS%%S%s'R#$#&s(cS%%S%s&Y#$#&s&XS%%S%s&W#$#&s(fS%%S%s%}#$#&s(=S&%S&s(;#$#&s(:S&%S&s(7#$#$&##s%d#j#$C#(C#*S%&s(6S%%S%s((#$#&s('S%%S%s'~#$#$&#$*#$,#$7#$;#$?#$s###0s#&s#%S0K/s#%%#'s#)%#j#&s)'#j#'s)+#+s),s))s#/#Kj#(s#1#j#)s$i#+s$js$is$F#Kj#*s),#j#+s)4#+s)5s).s$r#S3j#'s#[#U#Dj##s%c##s(es#Nj#$C#(C#$#s#E$s#Y#$s#]#$s#a##s(ls%3j#$C#(C#$#s%*$s%>#$s%B#$s%F#&EP##s%(&s(:P%Ps(9#$#&s)JP%Ps'@#$#&s'?P%Ps'>#$#&s)MP%Ps&d#$#&s)$Q%Qs(~#$#&s(}Q%Qs(z#$#$&##s&K#j#$C#(C#*P&s(yP%Ps(k#$#&s(jP%Ps(e#$#$&#$*#$,#$7#$;#$?#$s###$s#'#j##s#*#%S$s'b$s#ms#I&ES'%S'F#$#&s(eS'%S's(d#$#&s)uS'%S's'k#$#&s'jS'%S's'i#$#&s)xS'%S's'3#$#&s)OS8%S8s)M#$#&s)LS8%S8s)I#$#$&##s&v#j#$C#(C#*S'&s)HS'%S's):#$#&s)9S'%S's)4#$#$&#$*#$,#$7#$;#$?#$s###0s##BS0K/B&#'s#&&#'s#*&#j#&s*:#j#'s*>#+s*?s*<s#0#Kj#(s#2#j#)s%Q#+s%Rs%Qs$E#Kj#*s*?#j#+s*G#+s*Hs*As%\#S3j#'s#Y#U#Dj##s&K##s)xs#Oj#$C#(C#$#s#F$s#Z#$s#^##s)~s%xj#$C#(C#$#s%o$s&'#$s&+#&ER%RF#$#&s)LR##s$]&s*[R%Rs(Q#$#&s(PR%Rs(O#$#&s*^R%Rs'u#$#&s*5S#%S#s*3#$#&s*2S#%S#s*/#$#$&##s'\#j#$C#(C#*R&s*.R%Rs)|#$#&s){R%Rs)v#$#$&#$*#$,#$7#$;#$?#$s###$s#&#j##s#*#%S&s(n$s#ls#H&ES(%S(F#$#&s)vS(%S(s)u#$#&s+*S(%S(s(|#$#&s({S(%S(s(z#$#&s+-S(%S(s(D#$#&s*`S:%S:s*^#$#&s*]S:%S:s*Z#$#$&##s(+#j#$C#(C#*S(&s*YS(%S(s*K#$#&s*JS(%S(s*E#$#$&#$*#$,#$7#$;#$?#$s###0@?S0K/?'#'s##'#'s#''#'s#+'#j#&s+L#j#'s+P#+s+Qs+Ns#1#Kj#(s#3#j#)s%L#+s%Ms%Ls$E#Kj#*s+Q#j#+s+Y#+s+Zs+Ss%Z#S3j#'s#W#U#Dj##s'1##s+.s#Pj#$C#(C#$#s#G$s#[##s+3s&aj#$C#(C#$#s&X$s&l#&ES$%S$F#$#&s*\S$%S$s*[#$#&s+lS$##s$^&s)`S$%S$s)_#$#&s+nS$%S$s))#$#&s+ES%%S%s+C#$#&s+BS%%S%s+?#$#$&##s(l#j#$C#(C#*S$&s+>S$%S$s+0#$#&s+/S$%S$s+*#$#$&#$*#$,#$7#$;#$?#$B#$s#&#j##s#*#%S8s)E$s#ks#G&ES)%S)F#$#&s+*S)%S)s+)#$#&s,:S)%S)s*0#$#&s*/S)%S)s*.#$#&s,=S)%S)s)T#$#&s+pI%Is+n#$#&s+mI%Is+j#$#$&##s);#j#$C#(C#*S)&s+iS)%S)s+[#$#&s+ZS)%S)s+U#$#$&#$*#$,#$7#$;#$?#$s###0=<S0K/<(#'@(#'s#$(#'s#((#'s#,(#j#&s,]#j#'s,a#+s,bs,_s#2#Kj#(s#4#j#)s%H#+s%Is%Hs$E#Kj#*s,b#j#+s,j#+s,ks,ds%Y#S3j#'s#U#U#Dj##s's##s,?s#Qj#$C#(C#$#s#H#s,Cs&]j#$C#(C#$#s&T&ES&%S&F#$#&s+kS&%S&s+j#$#&s,{S&%S&s*q#$#&s*pS&##s$_&s,}S&%S&s*8#$#&s,TS'%S's,R#$#&s,QS'%S's,N#$#$&##s){#j#$C#(C#*S&&s,MS&%S&s,?#$#&s,>S&%S&s,9#$#$&#$*#$,#$7#$;#$>#$B#$s#&#j##s#*##s,o6j#$C#(C##s,rs%zj#$C#(C#&s,tS(%S(s,r#$#&s,qS(%S(s,n#$#$&##s*?#j#$C#(C#j##-##s-$'j#$C#U#D#s-'s$z-CS-s---CS-s-+$$#3S-&#S)4S-)%#%S)##&#.(&#S)5(s-*)%#%S)##&#$)##0#&s-8S*%S*s-6#$#&s-5S*%S*s-2#$#$&##s*_#j#$C#(C#j##-#3K&#I4K)%#%I##&#.(&#I5(s-C)%#%I##&#$)#-CS0s-V-CS0s-T$$#3S>&#S/4S>)%#%S/##&#.(&#S/5(s-S)%#%S/##&#$)#&s-`S;%S;s-^#$#&s-]S;%S;s-Z#$#$&##s++#j#$C#-CS2s+/-CS2s-m$$#3S2&#S+4S2)%#%S+##&#.(&#S+5(s-l)%#%S+##&#$)#-CS2s.#$#2-CS?s+A-CS?s.#$$#j##&#-CS?s.)-CS9s+F-CS9s.(VSIS9D/%$#j#,'#U#Dj##/#')(Dj#,.#U#Dj##B#14s##/'#S-0s##6#DXSJCs#'S2#j#-s#1#j#,s#?#V#S-Dj##s#D#j##s#k#;s#ls#_s#S#Dj#'s#p#j#$C#V#S-Dj##s#t#j#.C#YSKCs$)s#y#D/s'Ds';#'s'Os';#'s'Ss';#'s'Ws';#'s'[s';#'s'_s';#j#'s$2#U#Dj##s$`#$s%Bs$z&EI%IF#$#&s-mI%Is-l#$#&s.}I%Is,s#$#&s,rI%Is,q#$#&s/$I%Is,;#$#*I&s.FI%Is.8#$#&s.7I%Is.2#$#$&#$*#$s#}#$-#$1#$5#$9#/0)D's$')#'3)#'7)#';)#'?)#'s##)#j#*s%P#$s#%+&s.\S*%S*s.N&ES*%S*F#$#&s.9S*%S*s.8#$#&s/IS*%S*s-?#$#&s->S*%S*s-=#$#&s/LS*%S*s,c#$#&s/#S/%S/s.}#$#&s.|S/%S/s.y#$#$&##s,J#j#$C#(C#*S*#>=&s.gS*%S*s.b#$#$&#$(#$*#$5#$9#$=#$A#$s#%#%S/s.u&ES+%S+F#$#&s.`S+%S+s._#$#&s/pS+%S+s-f#$#&s-eS+%S+s-d#$#&s/sS+%S+s-.#$#(Cs$@*S+&s/:S+%S+s/,#$#&s/+S+%S+s/&#$#$&#$*#$,#$.#$2#$6#$:#0/.S-D/.+#'2+#'4+#'6+#':+#'>+#'B+#'s#&+#j#&s#*#j#*s#S#+s#Ts#Ss#-#Dj#'s#i#%S/s/<0:9S-D'<9#'@9#'B9#'s#$9#'s#(9#'s#,9#'s#09#'s#49#j#&,#j#*s#D#+s#Es#Ds#;#Dj#'s#t#ZSDs#xs#us#e1#Dj#*s&R#ZSDs&Zs&Ss$1s#h#S>j#(s0F#j#)s0J#+s0Ks0Hs&w#Dj#*s0H#j#+s0P#+s0Qs0Js(.#S3j#'s%u#U#Dj##s*2#1s&>s*3s%qs$<#Dj#+s&B#U#Dj##s'P#1s+^s'Qs'(s&I#Dj#+s'V#U#Dj##s(d#1s,1s(es(<s'^#Dj#+s(k#U#Dj##s)y#1s,as)zs)Qs(t#Dj#+s*%#U#Dj##s+4#1s-4s+5s*gs*/#Dj#+s+=#U#Dj##s-k#1s.Ns-ls->s+H#Dl#/s.'s-t#l#/s.ds.S#l#/s/as/7#6S1S6S4EFS,m#$#j#0s0i#j#1s0m#V#S-Dj##s0l#j##s0p#;s0qs0ns0h#Dj#'s0n#j#2s0v#V#S-Dj##s0q#j##s0y#;s0zs0ss0p#Dl#3S3s0s#j#/s1##j#4S.##"). Qed.
    Lemma acompl_trans : acompl s0 s1 d lo SP m0 m1 -> acompl s1 s2 d lo SP m1 m2 -> acompl s0 s2 d lo SP m0 m2.
    Proof.
      intros A B a Ha NW. rewrite (B a Ha) by (intros W; exact (NW (awrit_12_02 a W))). apply (A a Ha). intros W. exact (NW (awrit_01_02 a W)).
    Qed.
    Lemma secgone_01_02 : forall a, secgone s0 s1 a -> secgone s0 s2 a.
    Proof. intros a (sc & I & NI & R). exists sc. split; [exact I|]. split; [intros I2; exact (NI (SUB2 sc I2))| exact R]. Qed.
    Lemma secgone_12_02 : forall a, secgone s1 s2 a -> secgone s0 s2 a.
    Proof. intros a (sc & I & NI & R). exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R]. Qed.
    Lemma avis_trans : avis s0 s1 m0 m1 -> avis s1 s2 m1 m2 -> avis s0 s2 m0 m2.
    Proof.
      intros A B x V. destruct (A x V) as [V1|G]; [| right; exact (secgone_01_02 _ G)].
      destruct (B x V1) as [V2|G]; [left; exact V2| right; exact (secgone_12_02 _ G)].
    Qed.
    (* [comment removed for export] *)
    Lemma avmx_trans : avmx s0 s1 mo0 mo1 -> avmx s1 s2 mo1 mo2 -> avmx s0 s2 mo0 mo2.
    Proof.
      intros A B x Hx. destruct (A x Hx) as [A1 A2]. split.
      - destruct A1 as [H1|(sc & I & NI & R)].
        + destruct (proj1 (B x H1)) as [H2|(sc & I & NI & R)]; [left; exact H2| right]. exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R].
        + right. exists sc. split; [exact I|]. split; [| exact R]. intros I2. exact (NI (SUB2 sc I2)).
      - intros sc I2 NI. exact (False_ind _ (NI (SUB1 sc (SUB2 sc I2)))).
    Qed.
  End Compose.

  (* [comment removed for export] *)
  Definition rstep_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : ast) (d : depot) (lo : Z) (m : mem) (mo : Model) (XC' XB' PZ : list Z) (MODEL : astate -> Prop)
      (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ a_AL s' = a_AL s /\ a_sb s' = a_sb s /\ a_pa s' = a_pa s
    /\ (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s)))
    /\ as_cache_inited (a_st s') = true
    /\ (forall c0, 0 <= c0 -> rg_allocated_user (get_region (a_st s') c0) = rg_allocated_user (get_region (a_st s) c0))
    /\ lzok bsegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ AREPQ s' XC' XB' m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo'
    /\ nonvm_same mo mo' /\ avmx s s' mo mo' /\ depot_cov d mo'
    /\ DEPOT bsegs d m' /\ depot_placed s' d /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avis s s' m m' /\ agree_on (pendz (a_st s) PZ) m m'
    /\ alive_kept (a_st s) (a_st s') /\ agree_on (alive (a_st s)) m m'
    /\ MODEL (a_st s').
End HCW.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RMALLOC_SYM : Z := 0x68018.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x67ed8.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
Definition RATP : Z := 0x92650.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x925ac.        (* [comment removed for export] *)
Definition RLIBC : Z := 0xb28e0.         (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0xb28e8.    (* [comment removed for export] *)
Definition RCTX : Z := 0xb2958.          (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0xb2690.    (* [comment removed for export] *)
Definition RGOT_SSP : Z := 0x7f808.      (* [comment removed for export] *)
Definition RVMLOCK : Z := 0xb3978.       (* [comment removed for export] *)

Definition mem := word -> option byte.
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.
Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RVMLOCK <= a < RVMLOCK + 4).

(* [comment removed for export] *)
Section HC.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x7a000 <= a < 0xb4000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => hceil <= fst iv /\ snd iv <= SP) W ->
  (forall b, In b LB -> blk_addr b + blk_size b <= hceil) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM FW HB a Ha Hc.
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|].
    pose proof (HB b Hb). lia. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x7a000 <= A /\ A + n <= 0xb4000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A) /\ (A + n <= RVMLOCK \/ RVMLOCK + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.HC.rclient_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.blk_addr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.blk_size); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.in_block); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@kc__2); constr:(@kc__3); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.HC.rclient_addr); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block))|] [|@b; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__p1; @__arith; @H; @__x4; @__x5; @H2; @H1; @H0; @Hb; @x; @Ha; @HR; @a; @n; @A; @SP; @LB|] "#1Y#;$$#T#@#b#c#a#(#i#%#'#&###Z#?#*#)#h#$#.#5#2#,#+#v#-#6#/#3#K#0#1#>#Y#o#p#;#R#4#8#9#}#F#A#[#^#`#j#k#l#n#r#q#s#t#m#z#{#:$$#7$##~#|$%#S#C#B#I#G#D#V#J#E#f#e#U#d#H#M#W#x#N#X#O#y#P#Q#w#_#L#g#]#\#uA#b&#c%#d%#e$#f%#g%#h&#i$#j%#k'#l*#m%#n*#o$#p&#q%#r%#s$#t$#u$#v*#w$#x%#y&#z+#{%#|%#}%#~'$#&US1OXS<KLJS#$LS#+LJ(S##%%#$HK*S.*#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#&#0#*S.*#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#&#0#&S.*#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#0#&3*#&#*#&#&#&#*#*#*#&#&#&#&#&#0#*-&#*#&#*#*#&#&#&#0#&s#0*#&#&#*#&#&#*#&#*#*#&#*#&#*#*#&#&#0#&s#-*#*#&#*#&#&#*#&#&#&#&#0#*s#a*#*#*#&#&#&#&#&#&#&#*#&#&#&#0#*s#K*#&#&#*#&#*#*#*#*#&#&#&#0#$s#oK+KL&S.&#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#&#&#0#$7s#q&4*#&#*#&#*#*#&#&#&#&#&#&#&#&#0#$s#(s#r*,*#*#*#&#&#&#0#&s$g*#&#&#&#&#&#0#+s#y#$#K'5#&s#$*#*#*#*#&#&#&#&#*#&#&#0#$s#Is#v0s#H+s#x#$#K'&#&s#4&#*#&#*#*#&#&#&#&#0#$s#Ys#y&s#X0#+s#|#$#K''#*s%8*#*#*#&#&#*#*#&#*#&#*#&#&#&#0#$s#os$#+s$$7$#K'%#*s#\*#&#*#*#*#&#&#*#*#&#&#&#0#$s$%s$'+s$(s#:$#K'%#%5#%s#*#%s#<#%s#O#%s#t#%s$/#1OMP4M$#H+HK6M+&#$%#%'#%*#j#$O#<O#'.#'s%s#$QL$s%OL(Ls%<%$#$s%.L(Ls#f%$#$s$pL(Ls#W%$#$s$fL(Ls#I%$#$s$YL(Ls#8%$#$s$NL(Ls#)%$#'&#'*#'.#'2#8#%7#9PL'$#'=#j##?#$QH$PK(Ks%Y%s$]#$s%KK(Ks$'%$#$s%1K(Ks#t%$#$s%'K(Ks#f%$#$s$vK(Ks#U%$#$s$kK(Ks#F%$#'&#'*#'.#'2#8#%7#9S(K'$#5S25#2D#2D%2DS2)D$#)D&#.#NUS=C#C$#US1C>DJ>DL?D$S##US>DUS?D=Ds&_=Ds%(,D$R#-&GEEF#IZS@'GEEFH/(GEEF$#USAE=DS.,D#R*-,GEEF#I,D%R+-.GEEF#I;/GEEF%(#;0GEEF*)#VSB1FVSCS3S4VSDMJWSES3#S4m$%#WSFDSGS#XSHMJ$#l#%*)#l#&;:#l#'@?#j#(D#j#)D#j#*D#j#+S5#$JS#%#L$S#L$JLk##$#k##&#k#(D#k#)D#k#*D#k#+S5#+PQ(H#ZM#PHS(LS#l#,0&#WS6s#Vs#=#j#-s#X#U#Mj##s'1#$s&hH$s$'s&U$s$(s&F$s$~H'$#$s$+s&,$s$oH'$#$s$.s%~$s$aH'$#$s$1s%q$s$PH'$#$s$4s%f$s$AH'$#%&#%*#%.#%2#%6#%8#1OMS($s$@Q+QH$#s$>%%#%'#j#$O#<O#'+#$s',Q$*s&u$+s&f$s%BQ'$#$.s&L$s%3Q'$#$1s&B$s%%Q'$#$4s&5$s$pQ'$#$7s&*$s$aQ'$#%&#%*#%.#%2#%6#%8#1OMS'$s$`P$s#Cs$]%$#%&#j#$O#<O#'*#$S(H(Hs'8%s#C#$s'*H(Hs%b%$#$s&lH(Hs%S%$#$s&bH(Hs%E%$#$s&UH(Hs%4%$#$s&JH(Hs%%%$#'&#'*#'.#'2#8#%7#9S'H'$#'<#j##>#$s'gP$s#fs'T$s#gs'E$s%}P'$#$s#js'+$s%nP'$#$s#ms&}$s%`P'$#$s#ps&p$s%OP'$#$s#ss&e$s%@P'$#%&#%*#%.#%2#%6#%8#$S'Q(Qs'k%s#V#$s']Q(Qs&9%$#$s'CQ(Qs&*%$#$s'9Q(Qs%x%$#$s',Q(Qs%g%$#$s&}Q(Qs%X%$#'&#'*#'.#'2#8#%7#9S*Q'$#5s$o5#5#5#5#5#2D#)D#s$r.#N5&2D#2D+)D#s$x)D%#.#N5(2D#2D0)D#s$~)D%#.#N)Ds%'s%&)D.#.#N)Ds%*s%()D5#.#N2D=)D#s%.)D5#)D0#.#N)D's%0)D=#.#N2Ds#$)D#s%6)D=#)D8#.#N)D's%8)Ds#%#.#N)D<B)Ds#$#)D?#.#N)Ds#'1.#N)Ds#(s%B)Ds#*#.#N)Ds#+3)Ds#-#)Ds#(#.#N)Ds#0s%G.#N2Ds#8)D#s%K)Ds#4#.#N)Ds#%s%O)Ds#7#.#N)D@s%R)Ds#:#.#N)Ds#6s#:.#N)Ds#8@.#N)Ds#Ds#>.#N)Ds#;s%\)Ds#C#)Ds#>#.#N)Ds#@s#8.#N)Ds#As%a)Ds#I#.#N)Ds#Es#5.#N)Ds#Ls%g)Ds#N#)Ds#I#.#N)Ds#Us#I.#N#C#s%g#Cs#P##Cs#K##Cs#L##Cs#M##Cs#N##C4##Cs#\##Cs#W##Cs#R##Cs#S##Cs#T##Cs#U##Cs#S##Cs#Q##Cs#^##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#R##Cs#j##Cs#e##Cs#`##Cs#a##Cs#b##Cs#c##Cs#a##Cs#W##Cs#l##Cs#g##Cs#h##Cs#i##Cs#j##Cs#X##Cs#x##Cs#s##Cs#n##Cs#o##Cs#p##Cs#q##Cs#o##Cs#m##Cs#z##Cs#u##Cs#v##Cs#w##Cs#x##Cs#n##Cs$*##Cs$%##Cs#|##Cs#}##Cs#~##Cs$###Cs#}##Cs#k##Cs#]##Cs#?##Cs#I##Cs#A##Cs#K##Cs#h##Cs$8##Cs#m##Cs#k##Cs#h##Cs#i##Cs#j##Cs$/##Cs$-##Cs#k##Cs$*##Cs$+##Cs$,##Cs$-##Cs$.##Cs$F##Cs#n##Cs#y##Cs#z##Cs#k##Cs#[##Cs$=##Cs$3##Cs#y##Cs$0##Cs$1##Cs$2##Cs$3##Cs$4##Cs$T##Cs#|##Cs#z##Cs#{##Cs#|##Cs#}##Cs$K##Cs$I##Cs$+##Cs$F##Cs$G##Cs$H##Cs$I##Cs$J##Cs$b##Cs$;##Cs#v##Cs$(##Cs$'##Cs$(##Cs$Y##Cs$$##Cs$###Cs$&##Cs$%##Cs$(##Cs$=##Cs$.##Cs$a##Cs$2##Cs$:##Cs$;##Cs$<##Cs$M##Cs$v##Cs$`##Cs$a##Cs$b##Cs$c##Cs$d##Cs$K##Cs$k##Cs$o##Cs$B##Cs$E##Cs$D##Cs$G##Cs$N##Cs%(##Cs$f##Cs$g##Cs$h##Cs$i##Cs$j##Cs$Y##Cs$q##Cs$}##Cs$U##Cs$V##Cs$W##Cs$e##Cs$\##Cs%6##Cs$|##Cs$}##Cs$~##Cs%###Cs%$##Cs$g##Cs%+##Cs%/##Cs$l##Cs$m##Cs$n##Cs$s##Cs$w##Cs%D##Cs${##Cs%:##Cs%;##Cs%<##Cs%=##Cs%D##Cs%)##Cs%=##Cs%A##Cs%B##Cs%C##Cs%D##Cs%K##Cs%R##Cs%<##Cs%H##Cs%I##Cs%J##Cs%K##Cs%R##Cs%G##Cs%K##Cs%O##Cs%P##Cs%Q##Cs%R##Cs%Y##Cs%`##Cs%B##Cs%V##Cs%W##Cs%X##Cs%Y##Cs%`##Cs%M##Cs%Y##Cs%]##Cs%^##Cs%_##Cs%`##Cs%g##Cs%n##Cs%X##Cs%d##Cs%e##Cs%f##Cs%g##Cs%n##Cs%c##Cs%g##Cs%k##Cs%l##Cs%m##Cs%n##Cs%u##Cs%|#,Ds(*Rs($-s(-GEEF#I:Ds(,s(-,Ds('S)#-s(0GEEF#I/s(1GEEF&#3Ds+i,D#Rs(1-s(4GEEF#I3Ds+X,D*R#-s(7GEEF#I3Ds+K,D-R#-s(:GEEF#I3Ds+D3Ds*+:D$#,D#Rs(<-s(?GEEF#I7s(@GEEF(#3Ds+7,D6R#-s(CGEEF#I3Ds)}:D&#,D#Rs(D-s(GGEEF#I7s(HGEEF'#3Ds+2,D>R#-s(KGEEF#I3Ds)t:D&#,D#Rs(L-s(OGEEF#I7s(PGEEF'#3Ds+*,Ds#&R#-s(SGEEF#I:D%*,D#Rs(S-s(VGEEF#I7s(WGEEF&#3Ds+#,Ds#-R#-s(ZGEEF#I:D%9,D#Rs(Z-s(]GEEF#I7s(^GEEF&#/s(_GEEF*#/s(`GEEF2#/s(aGEEF;#/s(bGEEFs#$#/s(cGEEFs#.#/s(dGEEFs#2#,Ds#5Rs(]-s(fGEEF#I,Ds(_S)s#4-s(hGEEF#I/s(iGEEF%#,Ds#4Rs(b-s(kGEEF#I,Ds(dS)s#1-s(mGEEF#I/s(nGEEF%#,Ds#0Rs(g-s(pGEEF#I,Ds(iS)s#.-s(rGEEF#I/s(sGEEF%#,Ds#-Rs(l-s(uGEEF#I,Ds(nS)s#+-s(wGEEF#I/s(xGEEF%#,Ds#*Rs(q-s(zGEEF#I,Ds(sS)s#)-s(|GEEF#I/s(}GEEF%#,Ds#(Rs(v-s)#GEEF#I,Ds(xS)s#'-s)%GEEF#I/s)&GEEF%#7s)'GEEF(#7s)(GEEF.#7s))GEEF4#7s)*GEEF:#ZSIs)+GEEF#/s),GEEFA#;s)-GEEFs#'s)&#;s).GEEFs#[s)'#l#%#s(|s(vl#&s)2s)1#l#'s#ds)6#j#(D#j#)D#j#*D#$S#M+S#J(M#%%#$s,pJ+JL$#s,^$$s,O$s++J'$#$'s,5$s*xJ'$#$*s,+$s*jJ'$#$-s+z$s*YJ'$#$0s+o$s*JJ'$#%&#%*#%.#%2#%6#%9#(Js,t%;#$s,fJ(Js+B%$#$s,LJ(Js+3%$#$s,BJ(Js+%%$#$s,5J(Js*p%$#$s,*J(Js*a%$#'&#'*#'.#'2#k###SJ%7#k##:#k##s#3#k#(D#k#)D#k#*D#YMS(S'PHS#l#,s#<$#WS6s'os'n#@s(+s'n#j#-s(-#U#Mj##s(j#1OMS*$s*lS(+S(P$#s*j%%#%'#j#$O#<O#1OMS$$s*tS'+S'S($#s*r%%#%'#j#$O#<O#$S*P(Ps-L%s(X#$s->P(Ps+v%$#$s-$P(Ps+g%$#$s,vP(Ps+Y%$#$s,iP(Ps+H%$#$s,^P(Ps+9%$#'&#'*#'.#'2#8#%7#9S$P'$#'<#j##>#1OMS,$s+<S*+S*S'$#s+:%%#%'#j#$O#U#M1OMS/$s+DS$+S$S*$#s+B%%#%'#1OS#S04S#$#S,+S,S$6S#+&#$%#%'#%*#$S0S$$s.7S$(S$s.$%$#$s-rS$(S$s,N%$#$s-XS$(S$s,?%$#$s-NS$(S$s,1%$#$s-AS$(S$s+|%$#$s-6S$(S$s+m%$#'&#'*#'.#'2#8#%7#9S&S$'$#'=#j##?#4J$#S/+S/S,6J+&#$%#%'#1OLS-4K$#S&+S&S06K+&#$%#%'#4H$#S-+S-S&6H+&#$%#%'#$S%S&$s.jS&(S&s.W%$#$s.IS&(S&s-%%$#$s./S&(S&s,r%$#$s.%S&(S&s,d%$#$s-tS&(S&s,S%$#$s-iS&(S&s,D%$#'&#'*#'.#'2#8#%7#9S+S&'$#'=#j##?#+S7S-4Q6Q+$#$&#4P$#S%+S+S%4S(6S(+$#$&#$S8S%$s/7S%(S%s/$%$#$s.rS%(S%s-N%$#$s.XS%(S%s-?%$#$s.NS%(S%s-1%$#$s.AS%(S%s,|%$#$s.6S%(S%s,m%$#'&#'*#'.#'2#8#%7#9S9S%'$#1OMSK$s,nS+(S+s,k%$#%&#j#$O#1OS'S94S'$#S%6S'+%#(S%#%&#)Ds)es)h.#N)Ds)_s,3.#N#C#s,2#C&#>DKUSLD?D$J#>DH?D#L%?D%S##=Ds.V,D#Rs,2-s,5GEEF#I*s.Z=D#:D'#,Ds,7S)#-s,:GEEF#I/s,;GEEF(#:Ds,4s,;,D'R#-s,>GEEF#I,Ds,7R.-s,@GEEF#I,Ds,?S)'-s,BGEEF#I/s,CGEEFs,7#;s,DGEEF&s,=#;s,EGEEF)s,>#;s,FGEEF-s,?#l#%#s,8s,2l#&8s,I#l#'?s,N#j#(D#j#)D#j#*D#j#.D#j#/D#+LK(S##%s0V#+KH+S#L$$#$JH$LK+LH(K#%%#k##'#k##)#k##-#k#(D#k#)D#k#*D#k#.D#k#/D#6S*4S*\MSMS8$S+#S7S#Jl#,9&#XSNs#Hs#BH#XSOOs#JS'#@s#Ss#R#@s#ls#R#j#0s#n#j#1s#t#V#S#Mj##s#x#j##s$D#YS:s$Es$As$##Mj#2s$H#j#3s$P#V#S#Mj##s$S#j##s%$#YS:s%%s$zs$\#Mj#2s%'#j#$O#V#S#Mj##s%0#j#4O#YSPOs%Ws%:#Mj#2s%_#U#Mj##s+n#ZS;s+vs+os+Rs%j#Mj#2s,2#U#Mj##s-o#ZS;s1(s-ps-Rs,U#S#WSQQHJm#$#j#5s1,#j#6s11#j#7D#j#8D#j#9D#j#:D#j#;s17##"). Qed.

Lemma rclient_range_SP_mono : forall LB SP SP' A n, rclient_range LB SP A n -> SP' <= SP -> rclient_range LB SP' A n.
Proof. intros LB SP SP' A n [H|[H|H]] HS; [left; lia| right; left; exact H| right; right; exact H]. Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at rsegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at rsegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at rsegs m A n -> rclient_range LB SP A n -> wr_at rsegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells rsegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk rsegs m lo hi -> SP <= lo -> stk rsegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= hceil /\ (A + n <= 0x10000 \/ 0xb4000 <= A).

Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  hceil <= fst iv
  \/ (0x7a000 <= fst iv /\ snd iv <= 0xb4000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv) /\ (snd iv <= RVMLOCK \/ RVMLOCK + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context (RHEAP : PState -> list block -> mem -> Prop)
          (rauxv_ok : mem -> Z -> Prop)
          (raddr_exposed : PState -> Z -> Prop)
          (lb_remove : bptr -> list block -> list block).

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM rsegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.ret_pc); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RFREE_SYM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_evt_step); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@stdpp.bitvector.definitions.BV); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@LinuxProcessSemantics.Riscv.Instr.Jal); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.Riscv.DecodeC.decode_any); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_cong1); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@LinuxProcessSemantics.Riscv.Prelude.sext); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_btgt); constr:(@LinuxProcessSemantics.Riscv.Instr.Branch); constr:(@LinuxProcessSemantics.Riscv.Instr.BC_EQ); constr:(@LinuxProcessSemantics.Riscv.Prelude.TNode); constr:(@LinuxProcessSemantics.Riscv.Prelude.TEmpty); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@LinuxProcessSemantics.Riscv.Sem.w0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_branch_pc); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Init.Datatypes.true); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.v_addi); constr:(@stdpp.bitvector.definitions.bv_signed); constr:(@stdpp.bitvector.definitions.bv_and); constr:(@stdpp.bitvector.definitions.bv_not); constr:(@LinuxProcessSemantics.Riscv.Sem.w1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.ret_pc_fold); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.Z_to_bv_lit_self); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.add_0_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.w1_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.b_addsext); constr:(@LinuxProcessSemantics.Riscv.Instr.Jalr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_congT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.HC.Iface.rfree_null_stmt)|] [|@ms'; @a0; @y; @z; @H; @b; @t; @sfE; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra|] "#)+#I$2###F#&#i#'#n#X#Y#(#U#%#;#)#G#E#D#C#B#A#@#<#:#9#8#7#6#5#4#3#2#1#0#/#.#-#,#+#*#~#?#$#=#>#j#m#O#H#L#f#q#z$#$%$$$&$*$-#P#]#^#_#d#l#u#v#w#y#{#|#}$'$+$,$.$/$0$1$2$3#R$4#N#x#g#Q#S#a#Z#e#T#c#b$(#M#[#V#s#W#\#h#k#o#p#r#t$)#`=#t$#u'#v%#w$#x&#y$#z*#{%#|%#}%#~&$#&$$$$%B$&)$'&$(&$)$$*%$+$$,'$-$$.%$/&$0%$15#S@##########/#USB#&*/#VSL#%/)USB#+)L')N#0PDQRS#S$S%S&S:S;S<S'NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8O4PUSM,USNI)&K%G$E#'JC#j#$J#0DQRS#S$S%S&S:S=CS'NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8OK+3SO)$G#E)M(3I&#j#%5#0DQRS#S$S%S&S:S=0S'NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8OK4D)$G#E.M-'JC#j#$J#0QRS#S$S%S&S:S=S<5NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8OKG&S@##&#################&#&#&#&#&#####(#&S@####&#&#&#&#&#&###&#&###&#&#######(#&4##########&###&#&#&#&#&#&#####(#&/####&#&#######&#####(#&9################(#+s#js#*&s#n####&###############################&#&###&#&#&#&#(#,s$%#-s$&$#(-,s$*#-s$+L##s$-&#/#(@,$#-%$#VSP)#(s$;&s#r####&###&###########(#+s$Cs#N)s$*E#Ms$9S;s$8USCs$?%s$@=*$#5Is#<'&#%m$%#*FS>6s##'F#S>m$%#VSQS?HUSC#7S?H>=%%#*%#8s#+''#%m$%#)s$BGCEs$LMs$K9J#j#&s$X#:s#+s$Zs#(2s$[s#O#*Hs#gYSRs#ys#hs#.s#+#XSD'%=#&s$D##############&###&###########&#######&#&#######&#&#(#,s$v#-s$w$#(s#P(6,s$|#-s$}%#(>,s%##-s%$L#/s$g&s#&######(#,(#-)$#XSSST.+#USUs%0%s%1G$s%2$#$%s%3S+$s%4$#&%s%5S:%s%6S3$s%7)#)$s%8&%#%s%9S#%s%:S/$s%;-#-%s%<N%s%=S7$s%>0#0$s%?&%#$s%@*)#%s%AQ%s%BS-$s%C5#5%s%DS<%s%ES5$s%F8#8$s%G&%#%s%HS%%s%IS1$s%J<#<%s%KS)%s%LO$s%M?#?$s%N&%#$s%O*)#$s%P21#%s%QS,$s%Rs#$#s#$%s%SS=%s%TS4$s%Us#'#s#'$s%V&%#%s%WS$%s%XS0$s%Ys#+#s#+%s%ZS(%s%[S8$s%\s#.#s#.$s%]&%#$s%^*)#%s%_R%s%`S.$s%as#3#s#3%s%bs%\%s%cS6$s%ds#6#s#6$s%e&%#%s%fS&%s%gS2$s%hs#:#s#:%s%iS*%s%jK$s%ks#=#s#=$s%l&%#$s%m*)#$s%n21#$s%oAs%e#WSEs%qs%js%j&s$=####&#&###&#######(#+s%}s$|&s$B####(#+s&&s$wnF#$##s&&4#%#(##)6E#Ms%yS;s%x%s&#s#g*s$C#5Is$F's$E#%m$%#6s#l'F#S>m$s$C#7S?Hs#_s$Y%s$A#*s$A#8s#r's$C#%m$%#$s&6s#)s#+s#d$s&7#s#/s#-%s&8S'$s&9s#6#s#3$s&:%s#9#%s&;D$s&<$#s#<$s&=s#ks#hs#k$s&>#s#gs#e$s&?#s#ds#^$s&@s#[s#<s#X$s&A#s#Ws#Q$s&B%s#_#$s&C)s&9#)#GCEs&:Ms&99J#j#&s&F#WSEs&Hs&ASV:s$#s&Is#x2s&Js$e#+s&Ks$s2s&Ls$g#nF#$##s&L'#%#%##*Hs%M*Hs%D]SWs#=s%[s%Os%Es$xs$*s$#$#XSD,&s#,#*HLVSFs&Ss&L'HL#m$%#VSGCC'F#S9j#'H#*FS9ZSHHL$#)Cl#(()#VSG++'F#S9m#%#'Fs#LS9m#$#XSXFs#NS9#'FS9s#O0SAPDQRS#S$S%S&s&\S=S<S'NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S84SA)$O#Ks&ZGs&Y'JC#j#$J#$s&gs#xs#zs$9$s&h#s#~s#|$s&i#s$*s$$%s&jP$s&k$#s#.$s&ls$>s#as$>$s&m#s#es#c$s&n#s#ms#7$s&os#{s#ks#x$s&p#s#ws#q$s&q%s#8#$s&r)s&h#nF#$##s&sC#%#s#U#s#P)$K#Gs&jEs&i3I1#j#)F##s&\/#,#L-$L#VSY%#VSID#;s&~SJ.s'#C#'s'##s&vj#)s'$#(S@+s''#VSIP*;s')C.s'*$#'s'*#s&}j#)s'+#VSFs'-D+s'.C;s'/*.s'0$#'s'0#s''j#'H#.s'3C&'s'3#s'*j#)s'4#'s'5Cs',j#)s'6#*s'7s&~.s'9D,USZD1s':s'%&%$#+s'<1US[D1s'=D+%$#VSK4LUS\51H61%$#VSK7s#$+s'C#.s'D#7's'D#s'/m#'#.s'Gs#(:'s'G#s'2m#%#1s'Is#%@#SJS]:s#0s'Ks#.2s'LD#WS^Ds#2s#01s'Ms#/s#+&$#.s'O%s#/m#s':s'O's'P$##s'S##&#&#####&#&#&#(#,s'W#-s'X$#(-,s'\#-s']L#,s'^s#=-s'_s#>#WS_%#s#F)s#OKs'ZGs'YEs'X%s'_**s&##5Is$H's&%#%m$%#6/'F#S>m$s&##7S?H,s&9%s%}#*s%}#85's&##%m$%#$s'rs$ts$vs%D$s's#s$zs$x$s't#s$;s$|%s'uSA$s'v$#s#f$s'ws%Is%.s%I$s'x#s%2s%0$s'y#s%:s%4$s'zs$?s$vs%E$s'{#s%Ds%>$s'|%s#p#$s'})s's#)#OCKs'tGs's9J#j#*s($#2s(&Ps#9.s('#s#cYS`s('%#s'zC0PDQRS#S$S%S&S:s'~S<S'NS(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8O)#Ks'|Gs'{Es'z*J#XSaIs$#s#&#<Is$$s#tKs$jGs'~Es'}s#.s#(s&Us#'B?9'#l#+s#>s#;#'JC'j#$J#)s$KGs$nEs(&Ms(%3I$#m#'#ZSHFS9s#w#s$}Cl#(s$2s$1#<Is'ys'xEs&QMs(+S;s(*s%ts%ds&^s$ls$gs$ds$^s$C#<Is'zs'yEs'+Ms(,S;s(+s&js&`s&_s&Qs&Ks&Gs&?s&7#)s'zEs('Ms(-S;s(,3Is'|#m#%#1s(:s(4s('#S'Cj#(s(4#j#,Sb#j#-s(8#j#.s(;#j#/s(?#j#0s(@#j#1s(A#j#2s(B#j#3s(C#j#4s(D#j#5s(E#j#6s(F#j#7s(G#j#8s(H#j#9s(I#j#:s(J#j#;s(K#j#<s(L#j#=s(M#j#>s(N#j#?s(O#j#@s(P#j#As(Q#j#Bs(R#j#Cs(S#j#%s(T#j#Ds(U#j#Es(V#j#Fs(W#j#Gs(X#j#Hs(Y#j#Is(Z#j#Js([#j#Ks(\#j#Ls(]#m##Sc#"). Qed.

(* [comment removed for export] *)
Definition RHEAP_frame_stmt : Prop := forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Definition rauxv_ok_frame_stmt : Prop := forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W ->
  rauxv_ok m' B.
Definition RHEAP_block_range_stmt : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Definition RHEAP_blocks_disjoint_stmt : Prop := forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Definition RHEAP_blocks_nodup_stmt : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).

(* [comment removed for export] *)
Lemma fresh_block_disjoint_client :
  RHEAP_block_range_stmt -> RHEAP_blocks_disjoint_stmt -> RHEAP_blocks_nodup_stmt ->
  forall s' LB m' p A n SP a k,
  RHEAP s' ((p, A, n) :: LB) m' -> rclient_range LB SP a k -> hceil <= SP -> 0 <= k ->
  a + k <= A \/ A + n <= a.
Proof.
  intros HBR HBD HND s' LB m' p A n SP a k HP HR CE Hk.
  pose proof (HBR _ _ _ (p, A, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5). cbn in R1, R2, R3, R4, R5.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]].
  - right. lia.
  - destruct H as (Ha & Hn & _). hcb. lia.
  - pose proof (HND _ _ _ HP) as ND. cbn in ND. inversion ND; subst.
    assert (NE : blk_id (p, A, n) <> blk_id b).
    { cbn. intros E. apply H3. apply in_map_iff. exists b. split; [symmetry; exact E| exact Hb]. }
    destruct (HBD _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn in D; lia.
Qed.
End Iface.
End HC.

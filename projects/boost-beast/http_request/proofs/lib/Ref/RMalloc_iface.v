(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition RMALLOC_SYM : Z := 0x68018.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x67ed8.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8)
  \/ (RVMLOCK <= a < RVMLOCK + 4).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. try hcb. try hsb. intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof. try hcb. try hsb.
  intros s LB LB' m (st & LB0 & HP & H1 & H2 & H3) P. exists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x7a000 <= a < 0xb4000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. try hcb. try hsb. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof. try hcb. try hsb.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof. try hcb. try hsb.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x7a000 <= A /\ A + n <= 0xb4000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A)
      /\ (A + n <= RVMLOCK \/ RVMLOCK + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocBlocks.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface.HCW.rclient_range); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocBlocks.blk_addr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocBlocks.blk_size); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.Malloc_iface.in_block); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@kc__2); constr:(@kc__3); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface.HCW.rclient_addr); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocBlocks.block))|] [|@b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__p1; @__arith; @__sat1; @__sat0; @H; @__x4; @__x5; @__sat4; @__sat3; @H2; @H1; @H0; @Hb; @x; @HR; @a; @n; @A; @SP; @LB; @HCANB; @HSECB; @HCEILB|] "#3-#<$3#e#R#t#u#s#(#{#'#%#&#k###Q#)#*#z#$#.#5#2#+#,#J$*#-#/#0#I#3#6#F#1#9#@#P#_#a#j$$$%#<#]#:$1#U#?#G#H#K#M#N#O#S#^#`#c#b#l#n#p#r#|#}#~$'$&$($#$.$/#4#8#;#7$3$2$0$4#d#B#D#A#V#L#E#g#T#x#w#f#v#C#X#h$,#Y#i#Z#m$-#[#\$+#y#q#W#o$)A#q&#r%#s$#t%#u%#v%#w$#x&#y%#z'#{*#|%#}*#~$$#&$$%$%%$&$$'$$($$)'$**$+$$,%$-&$.%$/+$0%$1%$2&US@S4)S1)#)#)#)#)#)#)#)#)#)#)#)#)#%#)#)#)#)#)#)#)#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#USAS4$$#)s#&)#)#)#)#)#)#)#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#$s#%#&s#%#m#s#W#USBS.USCS.$S)#%S10#%$%#%#%#%#0#VSD)#(-#&-#m#0#USES.USFS.$S)#($)&$#m#'#US5OXSGJLKS#$LS#+LK(S##&%#$HJ%s#q)#%#%#%#%#%#%#%#%#%#%#%#%#%#0#)S1)#)#%#)#%#%#%#%#%#%#%#%#%#%#%#%#%#0#%S1)#)#%#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#%3)#%#)#%#%#%#)#)#)#%#%#%#%#%#0#)-%#)#%#)#)#%#%#%#0#%s#0)#%#%#)#%#%#)#%#)#)#%#)#%#)#)#%#%#0#%s#-)#)#%#)#%#%#)#%#%#%#%#0#)s#a)#)#)#%#%#%#%#%#%#%#)#%#%#%#0#)s#K)#%#%#)#%#)#)#)#)#%#%#%#0#$s#oJ+JL)s$N%#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#$5s#o%4)#%#)#%#)#)#%#%#%#%#%#%#%#%#0#$s#&s#p),)#)#)#%#%#%#0#%s%w)#%#%#%#%#%#0#+s#w#$#J'5#%s#$)#)#)#)#%#%#%#%#)#%#%#0#$s#Gs#t0s%7+s#v#$#J'&#%s#4%#)#%#)#)#%#%#%#%#0#$s#Ws#w0s%F+s#y#$#J'&#%s&C%#)#)#%#)#%#)#%#%#%#0#$s#hs#x+s#y3$#J'%#)s#W)#%#)#)#)#%#%#)#)#%#%#%#0#$s#zs#|+s#}s#5$#J'%#&5#&s#&#&s#7#&s#J#&s#o#&s$(#1ONQ4N$#H+HJ6N+&#$%#&'#&*#j#$O#>O#'.#'s%i#$PL$s%HL(Ls%5&$#$s%'L(Ls#a&$#$s$iL(Ls#R&$#$s$_L(Ls#E&$#$s$RL(Ls#8&$#$s$GL(Ls#)&$#'&#'*#'.#'2#9#&7#:QL'$#'=#j##?#$PH$QJ(Js%R&s$V#$s%DJ(Js#~&$#$s%*J(Js#o&$#$s$|J(Js#b&$#$s$oJ(Js#U&$#$s$dJ(Js#F&$#'&#'*#'.#'2#9#&7#:S'J'$#VSHs&]s&W(S)s&^$S)s&Y(S)s&Yk##$#k##&#$S)s&cWSIs&ds&^S#j##S6#j#%%#$S)s&`k##S6#k#%(#VSJS)s&jVS7SK#m##0US##5S85#2D#2D%2DS8*D$#*D&#.#MUSLC#C$#US5CUSMD?DL7D$K#7D#S#%USNDUSOD%s'|<D#<Ds'&,D$R#-'GEEF#IZSP(GEEFH/)GEEF$#USQE<DS1,D#R*--GEEF#I,D%R+-/GEEF#I=0GEEF%(#=1GEEF*)#VSR2FVS7S9S:VSSNKWSTS9#S:m$%#WSUDS)S#XSVNK$#l#&*)#l#'<;#l#(BA#j#)D#j#*D#j#+D#j#,S;#$KS#&#L$S#L$KLk##$#k##&#k#)D#k#*D#k#+D#k#,S;#+S+S((S'#ZN#S+S'S$PJl#-0&#l#.s#?s#K#l#/s#Gs#D#l#.s#Qs#L#WS<s#ls#S#j#0s#n#U#Nj##s'=#$s&wH$s$=s&d$s$>s&U$s%3H'$#$s$As&;$s%$H'$#$s$Ds&1$s$sH'$#$s$Gs&$$s$fH'$#$s$Js%u$s$WH'$#&&#&*#&.#&2#&6#&8#1ONS'$s$VP+PH$#s$T&%#&'#j#$O#>O#'+#$s';P$*s'($+s&u$s%SP'$#$.s&[$s%DP'$#$1s&Q$s%7P'$#$4s&D$s%*P'$#$7s&9$s$wP'$#&&#&*#&.#&2#&6#&8#1ONS($s$vQ+QP$#s$t&%#&'#j#$O#>O#'+#$S'H(Hs'H&s#D#$s':H(Hs%t&$#$s&|H(Hs%e&$#$s&rH(Hs%X&$#$s&eH(Hs%K&$#$s&ZH(Hs%<&$#'&#'*#'.#'2#9#&7#:S(H'$#'<#j##>#$s'wQ$s#&s'd$s#'s'U$s&3Q'$#$s#*s';$s&$Q'$#$s#-s'1$s%sQ'$#$s#0s'$$s%fQ'$#$s#3s&u$s%WQ'$#&&#&*#&.#&2#&6#&8#$S(P(Ps'{&s#W#$s'mP(Ps&K&$#$s'SP(Ps&<&$#$s'IP(Ps&/&$#$s'<P(Ps%~&$#$s'1P(Ps%o&$#'&#'*#'.#'2#9#&7#:S+P'$#5s$u5#5#5#5#5#2D#*D#s$x.#M5&2D#2D+*D#s$~*D%#.#M5(2D#2D0*D#s%(*D%#.#M*Ds%-s%,*D.#.#M*D4%*D1#.#M2D=*D#s%4*D5#*D0#.#M*D's%7*D=#*D:#.#M2Ds#%*D#s%=*D>#*D9#.#M*D@'*Ds#&#*Ds###.#M*Ds#$s%D*Ds#&#.#M*D.7*Ds#-#*Ds#*#.#M*Ds#,-*Ds#'#.#M*D5s%M*Ds#*#.#M2Ds#8*D#s%Q*Ds#4#.#M*Ds#6@.#M*Ds#8s%U.#M*D@s%Y*Ds#;#.#M*Ds#7s#;.#M*Ds#.s%]*Ds#@#.#M*Ds#F?*Ds#C#.#M*Ds#>s%e*Ds#F#*Ds#A#.#M*Ds%is%g*Ds#D#.#M*Ds#Es%k*Ds#M#.#M*Ds#I2.#M*Ds#Ps%q*Ds#R#*Ds#M#.#M*Ds#Ys#(.#M*Ds#[s#O.#M#C#s%s#Cs#V##Cs#Q##Cs#R##Cs#S##Cs#T##C6##Cs#b##Cs#]##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#Y##Cs#W##Cs#d##Cs#_##Cs#`##Cs#a##Cs#b##Cs#X##Cs#p##Cs#k##Cs#f##Cs#g##Cs#h##Cs#i##Cs#g##Cs#\##Cs#r##Cs#m##Cs#n##Cs#o##Cs#p##Cs#]##Cs#~##Cs#y##Cs#t##Cs#u##Cs#v##Cs#w##Cs#u##Cs#s##Cs$$##Cs#{##Cs#|##Cs#}##Cs#~##Cs#t##Cs$0##Cs$+##Cs$&##Cs$'##Cs$(##Cs$)##Cs$'##Cs#=##Cs#[##Cs#A##Cs#K##Cs#C##Cs#M##Cs#r##Cs$>##Cs#p##Cs#n##Cs#o##Cs#p##Cs#n##Cs$5##Cs$3##Cs$4##Cs$0##Cs$1##Cs$2##Cs$3##Cs$4##Cs$L##Cs#t##Cs$'##Cs$(##Cs#p##Cs#]##Cs$C##Cs$8##Cs#w##Cs$5##Cs$6##Cs$7##Cs$8##Cs$9##Cs$Z##Cs$&##Cs$%##Cs$&##Cs$'##Cs$(##Cs$Q##Cs$O##Cs$P##Cs$L##Cs$M##Cs$N##Cs$O##Cs$P##Cs$h##Cs$(##Cs#x##Cs$-##Cs$;##Cs$<##Cs$_##Cs$'##Cs$%##Cs$)##Cs$'##Cs$+##Cs$;##Cs$1##Cs$g##Cs$F##Cs$A##Cs$B##Cs$C##Cs$:##Cs$|##Cs$f##Cs$g##Cs$h##Cs$i##Cs$j##Cs$p##Cs$q##Cs$u##Cs$G##Cs$J##Cs$I##Cs$L##Cs$T##Cs%.##Cs$k##Cs$l##Cs$m##Cs$n##Cs$o##Cs$W##Cs$v##Cs%'##Cs$\##Cs$]##Cs$^##Cs$o##Cs$b##Cs%<##Cs%&##Cs%'##Cs%(##Cs%)##Cs%*##Cs%0##Cs%1##Cs%5##Cs$p##Cs$t##Cs$u##Cs$v##Cs$z##Cs%J##Cs%$##Cs%@##Cs%A##Cs%B##Cs%C##Cs%J##Cs%-##Cs%C##Cs%G##Cs%H##Cs%I##Cs%J##Cs%Q##Cs%X##Cs%B##Cs%N##Cs%O##Cs%P##Cs%Q##Cs%X##Cs%M##Cs%Q##Cs%U##Cs%V##Cs%W##Cs%X##Cs%_##Cs%f##Cs%G##Cs%\##Cs%]##Cs%^##Cs%_##Cs%f##Cs%R##Cs%_##Cs%c##Cs%d##Cs%e##Cs%f##Cs%m##Cs%t##Cs%^##Cs%j##Cs%k##Cs%l##Cs%m##Cs%t##Cs%i##Cs%m##Cs%q##Cs%r##Cs%s##Cs%t##Cs%{##Cs&&#7Ds(<Ls(;?DK7D#Ls(>7D%S##)s,\<D#,D#Rs(4-s(>GEEF#I;D%s(=,Ds(7S*#-s(AGEEF#I/s(BGEEF&#3Ds,),D#R*-s(EGEEF#I3Ds+t,D*R#-s(HGEEF#I3Ds+g,D-R#-s(KGEEF#I3Ds+`3Ds*I;D$#,D#R5-s(PGEEF#I8s(QGEEF(#3Ds+S,D6R#-s(TGEEF#I3Ds*?;D&#,D#R=-s(XGEEF#I8s(YGEEF'#3Ds+N,D>R#-s(\GEEF#I3Ds*7;D&#,D#Rs#%-s(`GEEF#I8s(aGEEF'#3Ds+F,Ds#&R#-s(dGEEF#I;D%*,D#Rs#,-s(gGEEF#I8s(hGEEF&#3Ds+?,Ds#-R#-s(kGEEF#I;D%9,D#Rs#3-s(nGEEF#I8s(oGEEF&#/s(pGEEF*#/s(qGEEF2#/s(rGEEF;#/s(sGEEFs#$#/s(tGEEFs#.#/s(uGEEFs#2#,Ds#5Rs(m-s(wGEEF#I,Ds(oS*s#4-s(yGEEF#I/s(zGEEF%#,Ds#4Rs(r-s(|GEEF#I,Ds(tS*s#1-s(~GEEF#I/s)#GEEF%#,Ds#0Rs(w-s)%GEEF#I,Ds(yS*s#.-s)'GEEF#I/s)(GEEF%#,Ds#-Rs(|-s)*GEEF#I,Ds(~S*s#+-s),GEEF#I/s)-GEEF%#,Ds#*Rs)%-s)/GEEF#I,Ds)'S*s#)-s)1GEEF#I/s)2GEEF%#,Ds#(Rs)*-s)4GEEF#I,Ds),S*s#'-s)6GEEF#I/s)7GEEF%#8s)8GEEF(#8s)9GEEF.#8s):GEEF4#8s);GEEF:#ZSWs)<GEEF#/s)=GEEFA#=s)>GEEFs#'s)6#=s)?GEEFs#[s)7#l#&#s)0s)*l#'s#es)B#l#(s#js)H#j#)D#j#*D#j#+D#$S#N+S#K(N#&%#$s-0K+KL$#s,z$$s,k$s+IK'$#$'s,Q$s+:K'$#$*s,G$s+-K'$#$-s,:$s*|K'$#$0s,/$s*mK'$#&&#&*#&.#&2#&6#&9#(Ks-4&;#$s-&K(Ks+`&$#$s,hK(Ks+Q&$#$s,^K(Ks+D&$#$s,QK(Ks+7&$#$s,FK(Ks+(&$#'&#'*#'.#'2#k###SX&7#k##:#k##s#3#k#)D#k#*D#k#+D#YNS$S,S+S'Jl#-s#<$#l#.s*5s*A#l#/s*=s*:#l#.s*Gs*B#WS<s'~s'}#@s(:s'}#j#0s(<#U#Nj##s(z#1ONS+$s+6S'+S'Q$#s+4&%#&'#j#$O#>O#1ONS$$s+>S(+S(S'$#s+<&%#&'#j#$O#>O#$S+Q(Qs-k&s(g#$s-]Q(Qs,;&$#$s-CQ(Qs,,&$#$s-9Q(Qs+{&$#$s-,Q(Qs+n&$#$s,}Q(Qs+_&$#'&#'*#'.#'2#9#&7#:S$Q'$#'<#j##>#1ONS,$s+bS+$s*2s+_&$#&&#j#$O#U#N1ONS-$s+iS$+S$S+$#s+g&%#&'#1OS#S24S#$#S,+S,S$6S#+&#$%#&'#&*#$S2S$$s.US$(S$s.B&$#$s.4S$(S$s,n&$#$s-vS$(S$s,_&$#$s-lS$(S$s,R&$#$s-_S$(S$s,E&$#$s-TS$(S$s,6&$#'&#'*#'.#'2#9#&7#:S&S$'$#'=#j##?#4K$#S-+S-S,6K+&#$%#&'#1OLS/4J$#S&+S&S26J+&#$%#&'#4H$#S/+S/S&6H+&#$%#&'#$S%S&$s/,S&(S&s.u&$#$s.gS&(S&s-E&$#$s.MS&(S&s-6&$#$s.CS&(S&s-)&$#$s.6S&(S&s,x&$#$s.+S&(S&s,i&$#'&#'*#'.#'2#9#&7#:S0S&'$#'=#j##?#+SYS/4P6P+$#$&#4Q$#S%+S0S%4S'6S'+$#$&#$SZS%$s/US%(S%s/B&$#$s/4S%(S%s-n&$#$s.vS%(S%s-_&$#$s.lS%(S%s-R&$#$s._S%(S%s-E&$#$s.TS%(S%s-6&$#'&#'*#'.#'2#9#&7#:S3S%'$#1ONS=$s-7S0(S0s-4&$#&&#j#$O#1OS(S34S($#S%6S(+%#(S%#&&#*Ds)ss)=.#M*Ds)ls,G.#M#C#s,F#C&#?DH7D#Hs,F7D#Ks,G?DJ7Ds,IL#7D%S##<Ds1b,D#Rs,D-s,HGEEF#I<Ds0g;D&#,Ds,HS*#-s,LGEEF#I/s,MGEEF'#<Ds1k;Ds,F#,D(R#-s,QGEEF#I,Ds,IR.-s,SGEEF#I,Ds,QS*'-s,UGEEF#I/s,VGEEFs,I#=s,WGEEF&s,O#=s,XGEEF)s,P#=s,YGEEF.s,Q#l#&#s,Js,Dl#'8s,\#l#(?s,b#j#)D#j#*D#j#+D#j#1D#j#2D#+LJ(S##&s0q#+JH+S#L$$#$KH$LJ+LH(J#&%#k##'#k##)#k##-#k#)D#k#*D#k#+D#k#1D#k#2D#6S-4S-\NS=S[$S3#S\JHl#-9&#l#3s-.s-:#l#4s-6s-3#l#3s-@s-;#XS]s#Ks#EH#XS^Os#MS(#@s#Vs#U#@s#os#U#j#5s#q#j#6s#w#V#S#Nj##s#{#j##s$G#YS>s$Hs$Ds$&#Nj#7s$K#j#8s$S#V#S#Nj##s$V#j##s%'#YS>s%(s$}s$_#Nj#7s%*#j#$O#V#S#Nj##s%3#j#9O#YS_Os%Ys%<#Nj#7s%a#U#Nj##s,##ZS?s,,s,$s+cs%l#Nj#7s,D#U#Nj##s.;#ZS?s1Fs.<s-zs,g#S#WS`PHKm#$#j#%s1J#j#:s1O#j#;D#j#<D#j#=D#j#>D#j#?s1U#l#@s1Ws1X#l#As1^s1_#l#Bs1ns1o##"). Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at rsegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at rsegs m' A bs.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocBlocks.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocTree.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface.HCW.rheap_pres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@kc__3); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mrd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Stdlib.Lists.List.nth_error); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface.HCW.rclient_range); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface.HCW.rclient_range_addr); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@Corelib.Init.Logic.eq_ind_r)|] [|@i; @o; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @__sat3; @__sat2; @cstr0; @cstr; @Hi0; @x; @b; @_H; @E; @a; @Hi; @HR; @HB; @H1; @H; @H0; @HP; @bs; @A; @m'; @m; @SP; @LB; @HCANB; @HSECB; @HCEILB|] "#(L#:$9#P$##V#$##$$#H#~#%#(#'#&#[$*#+#)#/#3#^#*#.#2#5#4$(#7#G#-#,#1#p$,#D#8#>#S#0#\#Y#J#i#k#u#q#v#o#z$'$+$/$2$3#6#c#Q#=#E#F#I#K#L#M#O#R#T#f#g#e#j#l#n#m#w#y#{#}$.$0$4$5$1$6$9#9$;#d#B#C#]#@#X#?#Z#`#_$&$%$8$7#a#|#h#s#A#t#r$)#N#U#b#x$-$:#WB#y$#z$#{&#|%#}%#I$#~%$#%$$$$%&$&'$'*#J%#H%$(&$)$$*&$++$,%$-%$.$$/$$0&$1%$2$$3'$4'$5'$6&$7%$8(USJS5$S3$#$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################7#USKS5&$#$s#&$#$#$#$#$#$#$#$###############################################7#&s#%#)s#%#m#s#W#USLS-USMS-&I##S37##$########7#VSN)#/-#)-#m#0#USOS-USPS-&I#/$))$#m#'#;SQUS62USR#;#XSSLMNK<EMKF&IN*'K(#'N#&#6*+N0G#US%-(F'L#+#,ES&#32MF%($#k##*#k#$O#).#)3#(/=QS&M#<ERLMk##$#j##'#'M'&#s#**?M0G#'R5+#,EQ#3s#$LF%:$#k##(#k#$O#),#&IL*s#*L(#'R#&#s#9*s#.R0G#'Qs#$+#,ES.#3s#3S&F%s#)$#k##(#k#$O#),#(,'S&#&#s#F*s#;S&0G#'S/s#1+#,ES'#3s#@QF%s#6$#k##(#k#$O#),#(,=S#S'Q#<ES.S/Qk##$#j##'#*s#JQ0G#'S.s#@+#,ES##3s#OS/F%s#E$#k##(#k#$O#(+'S/#&#s#a*s#VS.0G#'S#s#L+#,ES0#3s#[S'F%s#Q$#k##(#k#$O#(+=S(S0S'#&IS#*s#bS'(#'S##&#s#q*s#fS#0G#'S0s#\+#,ES(#3s#kS7F%s#a$#k##(#k#$O#),#,ES$)(K'S(#+#,ES$#%s#j#Gj#%s#k#*s#wS70F#($/s#n#5Cs#o5C%`STOCS8S9S:SUFs#q$(&#XSV(&#GUS;K&I1*s$%S(US;#($&I#VSWs$<s$6/Is$=&Is$8/Is$8k##$#k##&#&Is$BWSXs$Cs$=Fj##S<#j#&%#&Is$?k##S<#k#&(#VSYIs$I5SZ#m##0UF#8S=8#8#8#6C#6C'6CS=9C$#9C&#VS>#S?6C*6C,9C#(9C%#VS>#S?US[S1WS@S1$#WS@S1*#;S1US\CVSACN>C$K#>C#F%US]CUS^CVSBCI:Cs$h-C$S+#.&JDDH#PUSCD#s%h:C#-C(S2#.+JDDH#P:CS3?C#&VSBCs$qUS6s$mWS_C$#-C&S+#.2JDDH#P-C2S+).4JDDH#P?C+3-C5S+#.7JDDH#P-C%S2*.9JDDH#P[SD:JDDH%#4;JDDH)6#4<JDDH,7#4=JDDH48#4>JDDH:9#VS`?H5SESFVSaGK%SE#SFm$%#WSbCIFXScGK$#l#'*)#l#(s#)s#(#l#)s#/s#.#j#*C#j#+C#j#,C#&IF/KN'KM&#s%/'ML&I#/$s%2)$#k##s%$#k##(#k##+#k##-#k#*C#k#+C#k#,C#*s%/S,(#(Q[G$#S4LRS'S(l#-6'#l#.s#Ys#e#l#/s#as#^#l#.s#ks#f#l#0s#os#m#l#1s#ss#r#l#2s#us#y#VSACK>C#Fs#K:Cs&L-Cs#GS2#.s#JJDDH#P-Cs#AS+s#8.s#LJDDH#P?Cs#C'-Cs#;S2#.s#OJDDH#P[SDs#PJDDH&#4s#QJDDH)s#L#4s#RJDDHs#Ns#M#l#'#s#6s#0l#(/s#U#l#)s#^s#[#j#*C#j#+C#j#,C#'KN&K#/$s#/)$#k##s#2#k##s#4#k#*C#k#+C#k#,C#YGs#(s#'S4LRl#--$#l#.s#}s$-#l#/s$)s$&#l#.s$3s$.#l#0s$7s$5#l#1s$;s$:#l#2s$=s$A#[SdS)S*S0s$Cs$TK#WS#s$Us#(#US(s$UUS$s$V%s%W$#1ES$s$XUSCs%d%s%Z$#2#1ES$s$R%s%]#&2#k##&#)+#US$s$WUS*s$X%s%c$#1ES*s$Z%s%e#.2#(N'S$#+#1ES*#%s%k#42#k##)#)-#US*(VSes%{G@E*nS%$s%}$#3s%r%#%$#4$##US),nS%$s&#$#3s%t##%$#4&#%%s%u%#j##*#1ES)0%s%x#A2#(M'S*#+#1ES)#%s%~#s#'2#k##)#US)'USG(%s&'$#(L'S)#+#1ES,#%s&,#s#12#(R'SG#+#1ES,#%s&2#s#72#k##)#US4'(S&'S,#+#@E#nS%$s&E$#3s&:G#%$#4s#(##USf%nS%$s&G$#3s&<##%$#4s#*#%%s&=%#j#%s&>#@E1nS%$s&K$#3s&@-#%$#4s#.##5s&A#US,4ZSgs&C0'$#Fj#52#j#6@#V#FGj##s#%#j##s#C#As#Ds#:s#1#Gl#7s#Ts#H#%s&Ks%Js%Dm#$#VNFGZShs&Ns%Gs%A$s%L#j#8s%Q#j#$O#XSHs%Us%LK#XSHs%Zs%LR#j#9s%\#j#:s%_#j#;s%i#V#FGj##s%n#j##s&+#As&,s&#s%y#Gj#<s&0#j#=s&?#V#FGj##s&B#j##s&e#As&fs&Vs&P#Gj#<s&h#j#>s&j#j#?s&l#j#@C#j#ASI#j#BSI#j#CC#j#Ds&t#l#Es&vs&w#l#Fs&}s&~#l#Gs'1s'2##"). Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at rsegs m A n -> rclient_range LB SP A n -> wr_at rsegs m' A n.
Proof. try hcb. try hsb.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells rsegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells rsegs m' A cs.
Proof. try hcb. try hsb.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr rsegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr rsegs m' A xs.
Proof. try hcb. try hsb.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells rsegs m' A (length xs)).
  eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk rsegs m lo hi -> SP <= lo -> stk rsegs m' lo hi.
Proof. try hcb. try hsb.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= hceil /\ (A + n <= 0x10000 \/ 0xb4000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  hceil <= fst iv
  \/ (0x7a000 <= fst iv /\ snd iv <= 0xb4000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv)
      /\ (snd iv <= RVMLOCK \/ RVMLOCK + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ rsegs)).

Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof. try hcb. try hsb. intros; left; assumption. Qed.
Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init (reservedZ rsegs)) -> raddr_exposed s n.
Proof. try hcb. try hsb. intros; right; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
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
Proof. try hcb. try hsb.
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

End HCW.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

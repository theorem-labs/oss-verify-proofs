(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes LibWritev Frame RefMemcpyLib.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import LazyRestrict LazySR LazyFdNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import RefStdioDefs RefStdioWrite_run1 RefStdioWrite_run2 Bo_code_108fec_1092c8.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsLazyRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rz_emit_nil : forall c K, realizes RSEGS c K -> realizes RSEGS c (t_emit [] K).
Proof.
  intros c K H. eapply rz_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (realizes_nonempty _ _ _ H).
Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

(* [comment removed for export] *)
Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.not); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StepTac.u_Z2bv); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Hoare.at_)|] [|@s; @z; @E; @e; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat1; @__sat0; @NE; @n; @H; @Hle; @Hk; @k; @b|] "#%3#/#y#6#c#8#d###b#%#$#&#k#*#i#'#S#5#<#A#(#)#E#I#N#W#X#U#h#j#q#r#/#-#,#3#2#;#=#@#H#G#+#M#O#Q#P#T#Y#Z#R#[#]#^#\#_#a#l#e#m#n#o#s#t#p#.#w#v#u#x#y#L#K#D#z#B#:#9#7#4#g#f#?#>#F#J#`#C#V1#k&#l%#m%#n%#o$#p'#q*#r%#s%#t%#u%#v+#w$#x%'Q'#'#'#'#'#US3#US4#&EG$%I%#JUR-UR)VS5$#&&#US6K$,K&E#*$'+$#$0O%#KVS7#+#C$,/#VS#$#$6S$%#O#C#1/#VS#$#$;S%%#S$,=#$>##C#%#C$E#C':+$#VS&&#j#$,#$s#%M%#S%,s#'#$s#(##C#%#C$E#C's#$+$#,s#-G$s#.##C#Ej#%C#-CE,s#2s#+$s#3##C#Em$&#ZS'Cs#/(#2GXS8/.#GWS91.#j#&:#U#Gj#'s#%#/=$s#=S:%#M#CG#j#%C#-C=VS;s#=s#<*Es#>&Es#>*Es#>k##$#k##&#&Es#CWS<s#Ds#CJj##S(#j#(%#&Es#Ek##S(#k#((#VS=Es#J-S>#m##0UJ#US)S*US)#0C#0C%0CS*WS+C$#WS+C&#VS?#S@USAPWSBP$#USCPVSDCIUSECXSFC$J#USGCUSHCVS,CEVS-CQ(C$N#)&HDDF#LZSI'HDDFO[SJ(HDDF$#USKDVS-Cs#p(C*N#),HDDF#LWSLC+%(C-N#)/HDDF#L.0HDDF&)#.1HDDF+*#VSM2F-S.S/VSNGI#S.#S/m$%#WSOCEJXSPGI$#l#)*)#l#*<;#l#+A@#j#,C#j#-C#j#.S0#+s#}I&EI%IK&E#k##%#k##'#k#,C#k#-C#k#.S0#$s$,SQ*#s$&YG#S1$MS2l#//&#l#0s#<s#H#l#1s#Ds#A#l#0s#Ns#I#VS,Cs$.WSRC#s$4(Cs#&SS#)s#2HDDF#LZSTs#3HDDF#(Cs#)N&)s#5HDDF#L(Cs#+SU()s#7HDDF#L.s#8HDDF%s#1#.s#9HDDF(s#2#l#)#s#*s#$l#*s#=s#<#l#+s#Cs#A#j#,C#j#-C#%GJ#C#s$=k###SV%JI&#s$@*s#%s$Ak##$#k##'#k#,C#k#-C#$s$MS1XGS2#KMl#//%#l#1s#cs#`#l#0s#ms#h#WSWs$.B#ZS'Cs$/s#qs#ps$-#WSXs$-s$*#j#2s#w#U#Gj#3s$@#ZSYs$Bs$As$6s#{#Gl#$s$Is$F#l#4s$Qs$M#VSZKI$s$\#%s$SI#C$##C%E#C%s$Y+$#VS&&#m#+#j#5s$\#j#6s$c#j#7C#j#8s$f##"). Qed.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variables (L S Zr : list (word * word)) (msF0 : machine_state) (mo0 : Model).
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x123ef0 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0x1240d0)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds mo0) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  (* LPS 75d69e00: the channel-reader premise of LazyFdNodes' lazy writev lemmas,
     as one Section HYPOTHESIS beside [Hfd]; same port as
     As/AsStdioWrite.v, re-keyed to this image by this tree's own As/Bo pair (0x104f0c ->
     0x109248, 0x104e84 -> 0x1091c0, canary 0x67d4f0 -> 0x681830). *)
  Hypothesis Hrdr : m_channel_reader mo0 = true.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x681830) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  (* [comment removed for export] *)
  Hypothesis HK : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m ->
     forall msF' mo', lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo0 mo' -> hid_same L S msF0 msF' ->
     restrict L S msF' = mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K.

  (* [comment removed for export] *)
  Definition LZ (msF : machine_state) (mo : Model) : Prop :=
    lzok RSEGS L S Zr (mkCfg msF mo) /\ same_but_materialized mo0 mo /\ hid_same L S msF0 msF.

  Lemma LZ_fd : forall msF mo, LZ msF mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Proof. intros msF mo (_ & SB & _). rewrite (same_but_materialized_fds _ _ SB). exact Hfd. Qed.
  Lemma LZ_rdr : forall msF mo, LZ msF mo -> m_channel_reader mo = true.
  Proof. intros msF mo (_ & SB & _). rewrite (same_but_materialized_reader _ _ SB). exact Hrdr. Qed.

  Lemma LZ_next : forall msF mo msF' mo', LZ msF mo ->
    lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' -> LZ msF' mo'.
  Proof.
    intros msF mo msF' mo' (OK & SB & HS) OK' SB' HS'. split; [exact OK'|]. split.
    - eapply same_but_materialized_trans; eassumption.
    - eapply hid_same_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0x681830 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
           (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  Lemma LM_refl : LM mem1.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LM); constr:(@kc__2); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(su); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.eq); constr:(mem1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn_ext); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False)|] [|@x; @o; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @__sat73; @__sat74; @cstr; @Hx; @D; @Hnw; @H; @G; @E; @H0; @bs; @n; @a; @m|] "#%N#4#|#Z#k#$#l#j#%#&#J###'#V#)#M#r#,#.#(#+#*#-#\#q#:#D#8#7#;#=#X#a#]#b#[#f#s#m#x#w#h#}#~#>#@#Q#U#W#Y#c#e#g#i#t#u#v#y#z#|$#$$#{$%#2#3#T#S#?#<#B#9#G#I#P#O#C#H#o#n#A#L#_#F#E#`#^#p#K#N#R#d9#f%#g$#h%#i&#j$#k%#l%#m%#n'#o*#p%#q'#r%#s$#t$#u$#v&#w%#x%#y%#z%#{'$S)$#$#$#$#$#US+#US,#US+(US,#US-#k##&#US.%US<I0S)$#0#$#$#$#1#)S*#%2K#$#09$#$#$#1#)S*#**#-*#US=#UNEUJE&;$#k##&#k#$@#5JL-$#US->.OJLI6@H&%$#%s#(S#'L($#1s#11s#-VS>$##&#%s#/N'S#($###s###<&7$#.OS$S%N6s#0S#&5$#k##&#k##-#k##5#j##:#5JS#US$E&s#:#Bk##s#%#k#$s#?#5JS%.OJS%N&A#/%s#DS$'S%($###<%s#HQ'S$($###s#<#s#5&7$#.OJS&Q6s#IQ&s#.K#j#%s#/#.ORS&Q%s#SR##s#D'S&(%#*s#G#-&#US?R'R#M#VS@s#3s#2*Ms#4#Ms#4*Ms#4k##$#k##&##Ms#9WSAs#:s#9Ej##S/#j#&%##Ms#;k##S/#k#&(#2S02#2#/C#/C%/C'3C$#3C&#VS1#S22)/C#/CS03C*#3C%#VS1#S2USBS'WS3S'$#WS3S'+#US.S'USCCVS4CL8C$H#VS4CI8C#L&8C%E#USDCUSEC0s$.4C#4Cs$0+C$S(#,'GDDF#P4Cs$$WSFC'#+C'S5#,+GDDF#P[S6,GDDF'#USGD4CS)VS7Cs$&WS8C$#+C*S(#,2GDDF#PVS7Cs#~WS8C(#+C#S(3,6GDDF#P[SH7GDDF'#+C*S(5,9GDDF#P+C7S5(,;GDDF#P[S6<GDDF%#ZSI=GDDF#\S9>GDDF)3#\S9?GDDF54#VSJ@FVSKS:S;VSLKH&S:#S;m$%#WSMCMEXSNKH$#l#'*)#l#(s#*s#)#l#)s#2s#1#j#*C#j#+C#j#,C#j#-C##HE(HI*E#-%#(IL)Es$J#$#)Es$D##I7%#)Hs$O##I)Hs$I*I#-%#k###SOk##)#k##0#k#*C#k#+C#k#,C#k#-C#'SP%s$jSQZK$#s$ES*LNl#.<&#l#/s#fs#c#l#0s#ps#k#l#1s#ts#r#VNE#j#2s#w#j#$s$q#[SROQRJS&E#ZSSs$Rs$(s$%Hs$$#j#3s$*#j#4s$1#j#5s$6#j#6s$9#j#7s$;#V#EKj##s$A#j##s$]#YSTs$^s$]s$D#Kj#8s$w#j#9s$y#j#:SU#j#;s%$#j#<s$}##"). Qed.

  Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

  Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LM); constr:(@kc__2); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(su); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.eq); constr:(mem1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.wbytes_outside); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.not_morph); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StepTac.u_Z2bv); constr:(@Stdlib.micromega.VarMap.Empty); constr:(SUlo); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(SUhi); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.length_N_to_le_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.in_rng); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows_trans); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.wbytes_grows)|] [|@x; @o; @n; @z; @y; @m; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @Ha; @__sat74; @__sat73; @Hx; @Hhi; @Hlo; @G; @E; @H; @v; @a|] "#'T#2$1#:#l#m#k#$###%#v#-#u$$#'#G#&#.#R#A#,#_#)#8#(#J#*#S#I#E#c#w#?#6#5#;#N#X#g#f#o#n#y#|#}$%#T$+#9#+#[#\#]#Z#V#U#d#e#h#j#x#z#~$##{$'$($)$*$,$.$-$/#1$0$&$1$2$3#Q$5$4#O#<#7#q#p#i#B#@#>#M#Y#t#=#a#D#F#b#P#C#H#K#r#L#W#`#^#s@#t$#@%#u'#v*#<%#=%#w+#x$#y%#z%#{$#|%#}%#~$$#&$$%$%&$&%$')$($$)%$*%$+&$,%#;$$-$$.%$/&$0%#S'##########US1#US2#US1(US2#US@#k##&#US3I6S'##6#######*#+S##21H$$#68######*#+S##(*#,*#0#US(GUOG3:$#k##&#k#$?#7OP,$#$5P*s#('N#$#08s#'S(-S4-#-#-#-#-#-#-#:#NWS)S&,#US3#k##/#k##3#j##5#7ONUS*G3s#4#=k##@#k#$s#9#7OS&$s#.S&'S*;$#s#(8s#?K:3S$XS)Q$#G3s#>#s#'k##s#*#k#$s#C#8s#ESA:9S*WS)S$$#7O#UQGUOI3s#GH#j#%s#H#VS(GH8s#NQ2s#O#2s#PI$$#;H'&#(&#,&#0#j#&R#$H*;s#,'H#(-#,&#0#j#'C#2s#_G$K#'K*(%#,%#0#'Ks#C()#,)#0#<+j#$CH(GH<#j#(C#j#$C#.C2'GHXSBCCSC#.C#j#)C#j#&C#.CK.Cs#&j#$R#.Cs#V`SDRCCCS+S+11$s#Ls#W#fSECCCCCCS,222S,(KK's##s#X#`S5CCS-3S-/>>.<8#ZSF><>85#WSG<8#4Cs#U4Cs#W4CS41C$#1C&#=#S.4Cs#]4Cs#_1C$#1C+#=#S.USHS%>S%$#>S%*#USIS%VS6CIVS6CPXS7C$G#USJCUSKC?Cs$//Cs$*9C$#?Cs$?%C$L#&(FDDE#J/Cs$'9C)#%C'S/#&,FDDE#J[S8-FDDE'#ZS9.FDDE#USLD?CS'/Cs#~WS:C$#%C#L+&4FDDE#J%C2L'&6FDDE#J%C)L3&8FDDE#J%C5S/)&:FDDE#J[S8;FDDE%#ZS9<FDDE#)=FDDE)0#)>FDDE,1#)?FDDE32#VSM@E.S;S<VSNHI3S;#S<m$%#WSOCMGXSPHI$#l#**)#l#+s#*s#)#l#,s#/s#.#j#-C#j#.C#j#/C#+Is$S$#G+Is$M(G#,%#k###S='Gs$D+Ps$R$$#+Ns$\$#I$PN'Ps$J(N#,%#k###S=k##(#k##+#k##/#k#-C#k#.C#k#/C#ZHS#s$(QGPNl#0:$#XS>s#rs#ns#Y#m##s#s2s$zs$=1Cs#Ts#Y1Cs#V#=#S.>S%#s#SUSQCXS7Cs#QG#9Cs#Js#L%C#Ls#A&s#PFDDE#J#s%)##################################################*#/C#6s%=########*#/C#WS:C*#%C#Ls#q&s#vFDDE#J/CM%C#Ls#j&s#yFDDE#J)s#zFDDE&s#m#)s#{FDDEs#-s#n#l#*#s#^s#Xl#+s#2s#~#l#,s#5s$'#j#-C#j#.C#+Gs%K$#H':3$#I$MIk##$#k##'#k#-C#k#.C#XHS#QNSRl#0-$#*s%i*s%eVSS$#(M%$M%VST'&(M#k##%#k##'#$M+WSU,+Gj##S?#j#1%#$M*k##S?#k#1(#VSVM2.SW#m##1UG#9Cs$@s$=%Cs$5L#&s$FFDDE#J#s#;############################*#/C#%Cs$TL#&s$YFDDE#J/Cs#,WSXC#s&2%Cs$NS/#&s$]FDDE#J)s$^FDDE's$Q#)s$_FDDE;s$R#l#*#s$Bs$<l#+s#rs$b#l#,s#us$g#j#-C#j#.C#'Hs%v+Gs&($$#$I4(Is#6k##$#k##&#k#-C#k#.C#XHS#SYS&SZl#0-$#l#2s#/s#;#l#3s#7s#4#l#2s#Bs#<#WS[Ks#F#5CKs%Ks$0s$/#VS\s&Is%jVS]s%|S$5Rs%}s%U%$#;%WS^Gs%o#0#m#&#$s%^s#Ij#&R#$s%Ys#Kj#'C#$s%Ts#M$s%Qs#N$GH<#j#(C#j#$C#.Cs#S`S5CCS0s%RS0$s%[s%Ws%Bs#Ts#T#%Cs$xLs#/&s%-FDDE#J)s%.FDDEs#3s$}#)s%/FDDEs#Gs$~#l#*#s$ns$hl#+s$Bs%2#l#,s$Es%7#j#-C#j#.C#'Is&F$#s#_k##s#-#k##s#/#k#-C#k#.C#l#0)#s#+l#2s#Ws#c#l#3s#_s#\#l#2s#js#d#XS>=<6#m##>5CK@#s$Xs#,5Rs&Hs###s#+s#*ZS_s&8Qs&9Gs#&#5s&ss&0s&-s&,s&8#j#4s&_#j#$s&x#WS`s&6S$s&7YSaOS$s&6I#XSbs&:s&6%#j#5s&A#j#6s&D#j#7s&F#j#8s&H#V#GHj##s&N#j##s&e#YScs&fs&es&Q#Hj#9s'##j#:s')#j#;C#j#)s''##"). Qed.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.

  (* [comment removed for export] *)
  Lemma finish : forall regs m msF mo,
    RI regs -> LM m -> LZ msF mo -> restrict L S msF = mkst regs (0x1091cc : word) m (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) K.
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.RI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LZ); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.restrict); constr:(L); constr:(S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.mkst); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.seg_rom); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(su); constr:(@Corelib.Init.Logic.and); constr:(l); constr:(f); constr:(g3); constr:(g4); constr:(g23); constr:(g24); constr:(g25); constr:(g26); constr:(g27); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.realizes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_scfg); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(K); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioWrite_run2.sw_done); constr:(bufp); constr:(bufsz); constr:(can); constr:(ret); constr:(e8); constr:(e9); constr:(e18); constr:(e19); constr:(e20); constr:(e21); constr:(e22); constr:(SUlo); constr:(SUhi); constr:(Flo); constr:(Fhi); constr:(Hret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LM_rdn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(M8); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StepTac.u_Z2bv); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.Tauto.OR); constr:(M16); constr:(M24); constr:(M32); constr:(M40); constr:(M48); constr:(M56); constr:(M64); constr:(M72); constr:(Mcan); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.Tauto.X); constr:(Mbuf); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(Mbsz); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatSim.msteps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioWrite_run2.mem_sw2); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsLazyRun.rz_msteps_lazy_mkst); constr:(Zr); constr:(@Corelib.Init.Logic.proj1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.same_but_materialized); constr:(mo0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.hid_same); constr:(msF0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.Loop.LZ_next); constr:(HK); constr:(@kc__3 ((@LinuxProcessSemantics.Riscv.Prelude.bvmap) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xI) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))))|] [|@z; @x; @y; @m; @n; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat74; @__sat73; @__p1; @__x2; @regs'; @b; @HS2; @SB2; @H; @_H; @RS'; @HS'; @SB'; @OK'; @mo'; @msF'; @Q27; @Q26; @Q25; @Q24; @Q23; @Q4; @Q3; @Q22; @Q21; @Q20; @Q19; @Q18; @Q9; @Q8; @Q1; @Q2; @Q10; @RUN; @regs2; @e; @R27; @R26; @R25; @R24; @R23; @R4; @R3; @R21; @R9; @R8; @R2; @RS; @LZm; @LMm; @RIr; @mo; @msF; @regs|] "#O[$O&'%7%T##%U%S#$%[%Y%8$h$e%+%*$w${$v$y%)$u%(#%%9$t%'#'%$#(#)$s%&#,#M#Q%G$m$r#+#-#0%%#S$p#/#1#*$q#3#4$`$a#.#5#7#8#<$o#9#;#@#=#?#D%h#2#A#C#H#U#V#E#G$}$~#T#&#6#I#K#L#W#X#:#O#Z#[#^#_#b#c#d#f#g#h#j#k#n#o#r#v#w#z#{#|#~$$$&#>#P$O#\#`#l#p#s#t#x$#$'$($*&/$N#B#Y$+$,$.&-#F%,#R$/$0$2&)$V$Y#J%:%/#]$3$4$6$<$=#N%M#a$7$8$9$:$>$?$W$]%3%D%H%O%X%b%c%-%#%w%.%{&$#e#m$)$-$1$5$;$C$Z$R$X$[$\$_$g%;%A%B%C%E%I%K%J%L%N%P%R%\%_%`%d%e%a%5%l%m%n%o%p%q%r%s%u%v%t%z%}%y%~%x&#$|%0#i#q#u#y#}$%&*$A&0$B&1$M$I&(&'$j$^$n$U%W%V%Q%i$c$d$T$z$l%6$x$i%=%<%Z%@$f%]$k$b%F%>%?%f%g%j%k%1%4%^%2&&&.&,&%&+$S%|P%Y%%Z&%[%#+%%\$%]'%^*#8%%_+%`%%a&%b$%c$%d%%e%%f)%g'%h(%i/%j'%k%%l%%m%%n&%o%%p'%q%%r$%s5%t%%u&%v)%w*%x+%y%%z&%{$%|'%}'%~%&#&#%%&$(&%$&&%'T>/#N#'%'#'#'#'#N#UTR#VTj*#N)UTR#UTk#k##'#UTlS]UTmS]VTSS]S'WTnSCSDS+/0'#'#/#'#'#/#/#'#/#'#/#/#'#'#'#.#'T>'#'#'#/#'#'#/#'#'#'#/#/#/#'#'#/#/#'#'#.#/T>'#/#'#'#'#'#'#'#/#/#'#'#'#'#'#/#/#'#'#'#'#.#/s#-'#'#/#'#'#'#'#'#'#/#/#'#/#'#'#'#'#.#'3/#/#/#/#/#'#/#/#/#/#'#'#'#'#.#9s#ms#=m$M#-s#os#?#m##s#oUToL<S.$S-#$T?s#i#.s#|-s#{#M#S?#/T>/#'#'#'#'#.#1S5#;s$##$s$#,#.s$)-s$,#M#S?#$s$'#SJ/s$..#-s$1#M#S?#;s$-S<$s$-$#'s$6/#.#-s$8#M#S?#';'#/#/#'#'#'#'#/#/#'#/#'#'#/#/#/#'#'#'#'#.#;s$Js#_$s$J:#.s#3-s$S#M#S?#$s$N#S@.s$U-s$W#M#S?#$s$R#S6/s$[/#.#-s$]#M#S?#$s$X#S/'s#'.#-s$b#M#S?#$s$]#S).s#+-s$f#M#S?#$s$a#S%/s#1'#.#-s$l#M#S?#$s$g#R/(.#-s$q#M#S?#$s$l#P%(#%/#%4#%:#%A#%s#&#%s#+#%s#I#%s#P#%s#U#0S.S-3LS##Qj##%##S7s#W$s${#SJ#S7s#T$s$}#s#S#S7s#O$s%##s#8#S7s#6$s%%#S@#S7s#4$s%'#S6#S7s#0$s%)#S/#S7s#-$s%+#S)#S7s#+$s%-#S%#S7s#'$s%/#R#S7s#$$s%1#P%%#%(#%+#%.#%1#%4#%7#%:#%=##S1s$%$s%<#s#x#S8s#v$s%>#SJ#S8s#s$s%@#s#r#S8s#n$s%B#s#W#S8s#U$s%D#S@#S8s#S$s%F#S6#S8s#O$s%H#S/#S8s#L$s%J#S)#S8s#J$s%L#S%#S8s#F$s%N#R#S8s#C$s%P#P%%#%(#%+#%.#%1#%4#%7#%:#%=##SEs$7$s%[#SJ#SEs$4$s%]#s$3#SEs$/$s%_#s#t#SEs#r$s%a#S@#SEs#p$s%c#S6#SEs#l$s%e#S/#SEs#i$s%g#S)#SEs#g$s%i#S%#SEs#c$s%k#R#SEs#`$s%m#P%%#%(#%+#%.#%1#%4#%7#%:#%=#0S8S13LS##Qj##%##S=s$R$s%{#s$Q#S=s$M$s%}#s$6#S=s$4$s&##S@#S=s$2$s&%#S6#S=s$.$s&'#S/#S=s$+$s&)#S)#S=s$)$s&+#S%#S=s$%$s&-#R#S=s#~$s&/#P%%#%(#%+#%.#%1#%4#%7#%:##S9s$q$s&9#SJ#S>s$n$s&;#s$m#S>s$i$s&=#s$R#S>s$P$s&?#S@#S>s$N$s&A#S6#S>s$J$s&C#S/#S>s$G$s&E#S)#S>s$E$s&G#S%#S>s$A$s&I#R#S>s$>$s&K#P%%#%(#%+#%.#%1#%4#%7#%:##SRs%,$s&U#s%+#SRs%'$s&W#s$l#SRs$j$s&Y#S@#SRs$h$s&[#S6#SRs$d$s&]#S/#SRs$a$s&_#S)#SRs$_$s&a#S%#SRs$[$s&c#R#SRs$X$s&e#P%%#%(#%+#%.#%1#%4#%7#%:#0S>S93LS##Qj##%##SAs%B$s&r#s%+#SAs%)$s&t#S@#SAs%'$s&v#S6#SAs%#$s&x#S/#SAs$|$s&z#S)#SAs$z$s&|#S%#SAs$v$s&~#R#SAs$s$s'$#P%%#%(#%+#%.#%1#%4#%7##SBs%`$s'-#s%_#SFs%[$s'/#s%D#SFs%B$s'1#S@#SFs%@$s'3#S6#SFs%<$s'5#S/#SFs%9$s'7#S)#SFs%7$s'9#S%#SFs%3$s';#R#SFs%0$s'=#P%%#%(#%+#%.#%1#%4#%7##S^s%r$s'F#s%[#S^s%Y$s'H#S@#S^s%W$s'J#S6#S^s%S$s'L#S/#S^s%P$s'N#S)#S^s%N$s'P#S%#S^s%J$s'R#R#S^s%G$s'T#P%%#%(#%+#%.#%1#%4#%7#0SFSB3LS##Qj##%##SGs%q$s'`#S@#SGs%o$s'b#S6#SGs%k$s'd#S/#SGs%h$s'f#S)#SGs%f$s'h#S%#SGs%b$s'j#R#SGs%_$s'l#P%%#%(#%+#%.#%1#%4##SHs&D$s't#s&-#SKs&+$s'v#S@#SKs&)$s'x#S6#SKs&%$s'z#S/#SKs%~$s'|#S)#SKs%|$s'~#S%#SKs%x$s($#R#SKs%u$s(&#P%%#%(#%+#%.#%1#%4##Sds&?$s(.#S@#Sds&=$s(0#S6#Sds&9$s(2#S/#Sds&6$s(4#S)#Sds&4$s(6#S%#Sds&0$s(8#R#Sds&-$s(:#P%%#%(#%+#%.#%1#%4#0SKSH3LS##Qj##%##SLs&R$s(E#S6#SLs&N$s(G#S/#SLs&K$s(I#S)#SLs&I$s(K#S%#SLs&E$s(M#R#SLs&B$s(O#P%%#%(#%+#%.#%1##SIs&g$s(V#S@#SNs&e$s(X#S6#SNs&a$s(Z#S/#SNs&^$s(\#S)#SNs&\$s(^#S%#SNs&X$s(`#R#SNs&U$s(b#P%%#%(#%+#%.#%1##S}s&v$s(i#S6#S}s&r$s(k#S/#S}s&o$s(m#S)#S}s&m$s(o#S%#S}s&i$s(q#R#S}s&f$s(s#P%%#%(#%+#%.#%1#0SNSI3LS##Qj##%##SOs'($s(}#S/#SOs'%$s)##S)#SOs'#$s)%#S%#SOs&{$s)'#R#SOs&x$s))#P%%#%(#%+#%.##SMs'<$s)/#S6#SSs'8$s)1#S/#SSs'5$s)3#S)#SSs'3$s)5#S%#SSs'/$s)7#R#SSs',$s)9#P%%#%(#%+#%.##T1s'F$s)?#S/#T1s'C$s)A#S)#T1s'A$s)C#S%#T1s'=$s)E#R#T1s':$s)G#P%%#%(#%+#%.#0SSSM3LS##Qj##%##STs'R$s)P#S)#STs'P$s)R#S%#STs'L$s)T#R#STs'I$s)V#P%%#%(#%+##SPs'b$s)[#S/#SXs'_$s)]#S)#SXs']$s)_#S%#SXs'Y$s)a#R#SXs'V$s)c#P%%#%(#%+##T7s'j$s)h#S)#T7s'h$s)j#S%#T7s'd$s)l#R#T7s'a$s)n#P%%#%(#%+#0SXSP3LS##Qj##%##SYs't$s)v#S%#SYs'p$s)x#R#SYs'm$s)z#P%%#%(##SUs($$s)~#S)#S_s'~$s*$#S%#S_s'z$s*&#R#S_s'w$s*(#P%%#%(##T@s(*$s*,#S%#T@s(&$s*.#R#T@s(#$s*0#P%%#%(#0S_SU3LS##Qj##%##S`s(/$s*7#R#S`s(,$s*9#P%%##Sas(:$s*<#S%#S2s(6$s*>#R#S2s(3$s*@#P%%##TIs(;$s*C#R#TIs(8$s*E#P%%#0S2Sa3LS##Qj##%##Ses(>$s*K#P#S~s(E$s*M#R#S3s(B$s*O#P1S5s).;s*R#GTTG#G#G#G#G#G#G#E#S,UTA$*E#.s*_VTps)I#&%#j#$C#*3(&#&*5s)A&#(j#%CE&HE>#j#&C#j#%C#*HEXTqCCTr#8C#j#'C#j#(C#8CAUTAE8C#j#%TU#8Cs)Q`TsTUCCCTATA11$=s)R#?CCCCCCS(222S()s#'s#'(<s)S#8C:5CCK4K086$;;#VTts)c==S4s)d&S4?=S4?k##$#k##&#&S4s)iWTus)js#$Hj##TV#j#)%#&S4s#&k##TV#k#)(#VTvS4s)p8Tw#m##0UH#UTxTJUTyTJVTWCHUTzCUT{CVTXCT>'s+5'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#.#7C#(Cs#.J#)s#0GDDF#IUT|D7Cs*?FCs#2#:C#$7Cs*OWT}C#s+f(C%J#)s#8GDDF#I+s#9GDDF+*#VT~s#:F8TYTZVU#ES'$TY#TZm$%#WU$CS4HXU%ES'$#l#**)#l#+s#Ds#C#l#,s#Gs#F#j#-C#&E:1Hs*S*#s*T&#s#wk##&#k#-C#LS5T[l#.*$#l#/s#Rs#^#l#0s#Zs#W#l#/s#ds#_#6s#{s#ys#f#@s,%s$1.s#77C#7Cs*e:C$#(C#Js#U)s#WGDDF#I7CS4(C#Js#()s#ZGDDF#I+s#[GDDF&s#,#l#*#s#$>l#+s#_s#^#l#,s#bs#a#j#-C#*0s*q&#E&S4>k##$#k#-C#LS5T8l#.)$#(Cs#6SQs#3)s#hGDDF#I+s#iGDDFs#;s#:#l#*#s#2s#,l#+s#ms#l#l#,s#ps#o#j#-C#=s#*s$Ak##s#,#k#-C#l#.&#s#(l#/s#ws$'#l#0s$#s#|#l#/s$-s$(#As$V1#2Cs$Ws$Gs#(s#'#'s*E'#.#1S5#&s$P#'s+)'#'#.#1S5#&#E,)#j#$C#&s$T,&'s$f,$#&s$U/,#%8C15CCKs$VKs$Rs$Zs$Xs$F22#>(B*)')$#7C6FCs$1#(Cs#]J#)s$4GDDF#I7C4FCs$5#(C#Js#b)s$8GDDF#ICs$9GDDF'#l#*#s#^s#Xl#+s$=s$<#l#,s$@s$?#j#-C#1Es+K*#s+L1Es#%&$#1EA&#',%#k#-C#UES5l#.,$#6@>:#2Cs%*s#$#s#Vs#2DS3s%*s$~s$}S2U&s#2#.s,~1S5#;s,}#Es%&S:*%s%%&#s%#*'s+^&#s%%8C)?CCCCCCS(s$|s$|s$|S(s$s**#s%*s+as$m5CCKs$}Ks$y(&#s%(s%(s$l7C-FCs$V#:C#s$((C#Js$%)s$ZGDDF#I+s$[GDDFs$-s$,#l#*#s$$s#zl#+s$_s$^#l#,s$bs$a#j#-C#1H7*#s+n&#s%5k##s#|#k#-C#l#.(#s#xl#/s$ks$w#l#0s$ss$p#l#/s$}s$x#6;96#@s->?(Cs#qJ6)s$lGDDF#I+s$mGDDFs#ts$>#l#*#s$6s$0l#+s$qs$p#l#,s$ts$s#j#-C#&S44k##s#p#k#-C#l#.&#s#n(CASQs$B)s$wGDDF#I+s$xGDDFs$Js$I#l#*#s$As$;l#+s$|s${#l#,s%#s$~#j#-C#=?s%Pk##s$;#k#-C#l#.&#s$7l#/s%*s%6#l#0s%2s%/#l#/s%<s%7#As#:1#2Cs#;s%V>=#&s#9s#j&s#es#=,$#&s#:s#m,#%5CCKs%WKs%Ss#>s#<s#9s#os#os#`>'B)(&($#(Cs#8Js#^)s%3GDDF#I(Cs#\Js#;)s%5GDDF#ICs%6GDDF%#l#*#s$[s$Ul#+s%:s%9#l#,s%=s%<#j#-C#1Es#N*#s,I&#s#[&s#Z%,$#k#-C#l#.)#s#Y6863#2Cs#Us#z#s#7=DS3s#Us%xs#TS2U'=#1S5s+x;s-v#Es%{S0*%s%z&#s%x*'s,W&#s%z8C)?CCCCCCS(s%us%us%uS(s%l**#s&#s,Zs%f5CCKs%vKs%r(&#s%}s%}s%e7Cs,&FCs%O#:C#s$}(C#Js$z)s%SGDDF#I+s%TGDDFs%&s%%#l#*#s$ys$sl#+s%Xs%W#l#,s%[s%Z#j#-C#1Hs,0*#s,g&#s&.k##s$u#k#-C#l#.(#s$ql#/s%ds%p#l#0s%ls%i#l#/s%vs%q#6;96#@s.7?(Cs$jJ6)s%eGDDF#I+s%fGDDFs$ms%7#l#*#s%/s%)l#+s%js%i#l#,s%ms%l#j#-C#&S44k##s$i#k#-C#l#.&#s$g(CASQs%;)s%pGDDF#I+s%qGDDFs%Cs%B#l#*#s%:s%4l#+s%us%t#l#,s%xs%w#j#-C#=?s&Ik##s%4#k#-C#l#.&#s%0l#/s&#s&/#l#0s&+s&(#l#/s&5s&0#As#:1#2Cs#;s&O>=#&s#9s$c&s$^s#=,$#&s#:s$f,#%5CCKs&PKs&Ls#>s#<s#9s$hs$hs$Y>'B)(&($#(Cs#8Js$W)s&,GDDF#I(Cs$UJs#;)s&.GDDF#ICs&/GDDF%#l#*#s%Ts%Nl#+s&3s&2#l#,s&6s&5#j#-C#1Es,g*#s-B&#s$T&s$S%,$#k#-C#l#.)#s$R6863#2Cs#Us$s#s#7=DS3s#Us&qs#TS2U(=#.s.p1S5#;s.p#Es&uS**%s&t&#s&r*'s-Q&#s&t8C)?CCCCCCS(s&os&os&oS(s&f**#s&ys-Ts&`5CCKs&pKs&l(&#s&ws&ws&_7C-FCs&I#:C#s%w(C#Js%t)s&MGDDF#I+s&NGDDFs%|s%{#l#*#s%ss%ml#+s&Rs&Q#l#,s&Us&T#j#-C#1H7*#s-a&#s'(k##s%o#k#-C#l#.(#s%kl#/s&^s&j#l#0s&fs&c#l#/s&ps&k#6;96#@s/1?(Cs%dJ6)s&_GDDF#I+s&`GDDFs%gs&1#l#*#s&)s&#l#+s&ds&c#l#,s&gs&f#j#-C#&S44k##s%c#k#-C#l#.&#s%a(CASQs&5)s&jGDDF#I+s&kGDDFs&=s&<#l#*#s&4s&.l#+s&os&n#l#,s&rs&q#j#-C#=?s'Ck##s&.#k#-C#l#.&#s&*l#/s&ys')#l#0s'%s&~#l#/s'/s'*#As#:1#2Cs#;s'I>=#&s#9s%]&s%Xs#=,$#&s#:s%`,#%5CCKs'JKs'Fs#>s#<s#9s%bs%bs%S>'B)(&($#(Cs#8Js%Q)s'&GDDF#I(Cs%OJs#;)s'(GDDF#ICs')GDDF%#l#*#s&Ns&Hl#+s'-s',#l#,s'0s'/#j#-C#1Es#N*#s.<&#s%N&s%M%,$#k#-C#l#.)#s%L6863#2Cs#Us%m#s#7=DS3s#Us'ks#TS2U)=#'s.;'#.#1S5#;s/l#Es'qS&*%s'p&#s'n*'s.M&#s'p8C)?CCCCCCS(s'ks'ks'kS(s'b**#s'us.Ps'\5CCKs'lKs'h(&#s'ss'ss'[7C-FCs'E#:C#s&s(C#Js&p)s'IGDDF#I+s'JGDDFs&xs&w#l#*#s&os&il#+s'Ns'M#l#,s'Qs'P#j#-C#1H7*#s.]&#s($k##s&k#k#-C#l#.(#s&gl#/s'Zs'f#l#0s'bs'_#l#/s'ls'g#6;96#@s0-?(Cs&`J6)s'[GDDF#I+s'\GDDFs&cs'-#l#*#s'%s&{l#+s'`s'_#l#,s'cs'b#j#-C#&S44k##s&_#k#-C#l#.&#s&](CASQs'1)s'fGDDF#I+s'gGDDFs'9s'8#l#*#s'0s'*l#+s'ks'j#l#,s'ns'm#j#-C#=?s(?k##s'*#k#-C#l#.&#s'&l#/s'us(%#l#0s'}s'z#l#/s(+s(&#As#:1#2Cs#;s(E>=#&s#9s&Y&s&Ts#=,$#&s#:s&\,#%5CCKs(FKs(Bs#>s#<s#9s&^s&^s&O>'B)(&($#(Cs#8Js&M)s'~GDDF#I(Cs&KJs#;)s($GDDF#ICs(%GDDF%#l#*#s'Js'Dl#+s()s((#l#,s(,s(+#j#-C#1Es#N*#s/8&#s&J&s&I%,$#k#-C#l#.)#s&H6863#2Cs#Us&i#s#7=DS3s#Us(gs#TS2U*=#'s.h.#1S5#;s0g#Es(lS$*%s(k&#s(i*'s/H&#s(k8C)?CCCCCCS(s(fs(fs(fS(s(]**#s(ps/Ks(W5CCKs(gKs(c(&#s(ns(ns(V7C-FCs(@#:C#s'n(C#Js'k)s(DGDDF#I+s(EGDDFs'ss'r#l#*#s'js'dl#+s(Is(H#l#,s(Ls(K#j#-C#1H7*#s/X&#s({k##s'f#k#-C#l#.(#s'bl#/s(Us(a#l#0s(]s(Z#l#/s(gs(b#6;96#@s1(?(Cs'[J6)s(VGDDF#I+s(WGDDFs'^s((#l#*#s'|s'vl#+s([s(Z#l#,s(^s(]#j#-C#&S44k##s'Z#k#-C#l#.&#s'X(CASQs(,)s(aGDDF#I+s(bGDDFs(4s(3#l#*#s(+s(%l#+s(fs(e#l#,s(is(h#j#-C#=?s):k##s(%#k#-C#l#.&#s'}l#/s(ps(|#l#0s(xs(u#l#/s)&s(}#As#:1#2Cs#;s)@>=#&s#9s'T&s'Os#=,$#&s#:s'W,#%5CCKs)AKs)=s#>s#<s#9s'Ys'Ys'J>'B)(&($#(Cs#8Js'H)s(yGDDF#I(Cs'FJs#;)s({GDDF#ICs(|GDDF%#l#*#s(Es(?l#+s)$s)##l#,s)'s)&#j#-C#1Es#N*#s03&#s'E&s'D%,$#k#-C#l#.)#s'C6863#2Cs#Us'd#s#7=DS3s#Us)bs#TS2U+=#.s0B1S5#;s1a#Es)fO*%s)e&#s)c*'s0B&#s)e8C)?CCCCCCS(s)`s)`s)`S(s)W**#s)js0Es)Q5CCKs)aKs)](&#s)hs)hs)P7C-FCs):#:C#s(h(C#Js(e)s)>GDDF#I+s)?GDDFs(ms(l#l#*#s(ds(^l#+s)Cs)B#l#,s)Fs)E#j#-C#1H7*#s0R&#s)uk##s(`#k#-C#l#.(#s(\l#/s)Os)[#l#0s)Ws)T#l#/s)as)\#6;96#@s1~?(Cs(UJ6)s)PGDDF#I+s)QGDDFs(Xs(~#l#*#s(vs(pl#+s)Us)T#l#,s)Xs)W#j#-C#&S44k##s(T#k#-C#l#.&#s(R(CASQs)&)s)[GDDF#I+s)\GDDFs).s)-#l#*#s)%s({l#+s)`s)_#l#,s)cs)b#j#-C#=?s*4k##s({#k#-C#l#.&#s(wl#/s)js)v#l#0s)rs)o#l#/s)|s)w#As#:1#2Cs#;s*:>=#&s#9s(N&s(Is#=,$#&s#:s(Q,#%5CCKs*;Ks*7s#>s#<s#9s(Ss(Ss(D>'B)(&($#(Cs#8Js(B)s)sGDDF#I(Cs(@Js#;)s)uGDDF#ICs)vGDDF%#l#*#s)?s)9l#+s)zs)y#l#,s)}s)|#j#-C#1Es#N*#s1-&#s(?&s(>%,$#k#-C#l#.)#s(=6863#2Cs#Us(^#s#7=DS3s#Us*\s#TS2U,=#1S5s*Y;s2Z#Es*_N*%s*^&#s*\*'s1;&#s*^8C)?CCCCCCS(s*Ys*Ys*YS(s*P**#s*cs1>s*J5CCKs*ZKs*V(&#s*as*as*I7Cs*cFCs*3#:C#s)a(C#Js)^)s*7GDDF#I+s*8GDDFs)fs)e#l#*#s)]s)Wl#+s*<s*;#l#,s*?s*>#j#-C#1Hs*m*#s1K&#s*nk##s)Y#k#-C#l#.(#s)Ul#/s*Hs*T#l#0s*Ps*M#l#/s*Zs*U#6;96#@s2w?(Cs)NJ6)s*IGDDF#I+s*JGDDFs)Qs)w#l#*#s)os)il#+s*Ns*M#l#,s*Qs*P#j#-C#&S44k##s)M#k#-C#l#.&#s)K(CASQs){)s*TGDDF#I+s*UGDDFs*'s*&#l#*#s)zs)tl#+s*Ys*X#l#,s*\s*[#j#-C#=?s+-k##s)t#k#-C#l#.&#s)pl#/s*cs*o#l#0s*ks*h#l#/s*us*p#As#:1#2Cs#;s+3>=#&s#9s)G&s)Bs#=,$#&s#:s)J,#%5CCKs+4Ks+0s#>s#<s#9s)Ls)Ls)=>'B)(&($#(Cs#8Js);)s*lGDDF#I(Cs)9Js#;)s*nGDDF#ICs*oGDDF%#l#*#s*8s*2l#+s*ss*r#l#,s*vs*u#j#-C#1Es+H*#s2&&#s)8&s)7%,$#k#-C#l#.)#s)66863#2Cs#Us)W#s#7=DS3s#Us+Us#TS2U-=#;s3Rs)\Es+WT\*s)^s+V&#s+T*s)`s23&#s+V8Cs)b?CCCCCCS(s+Qs+Qs+QS(s+Hs)cs)c#s+[s26s+B5CCKs+RKs+N(&#s+Ys+Ys+A:Cs)Ss*W(C#Js*T)s+-GDDF#I+s+.GDDFs*\s*[#l#*#s*Ss*Ml#+s+2s+1#l#,s+5s+4#j#-C#1Hs)n*#s2A&#s+dk##s*O#k#-C#l#.(#s*Kl#/s+>s+J#l#0s+Fs+C#l#/s+Ps+K#6974#@s3m=(Cs*DJs)f)s+?GDDF#I+s+@GDDFs*Gs*m#l#*#s*es*_l#+s+Ds+C#l#,s+Gs+F#j#-C#&S44k##s*C#k#-C#l#.&#s*A(Cs)qSQs*q)s+JGDDF#I+s+KGDDFs*ys*x#l#*#s*ps*jl#+s+Os+N#l#,s+Rs+Q#j#-C#=?s,#k##s*j#k#-C#l#.&#s*fl#/s+Ys+e#l#0s+as+^#l#/s+ks+f#As*51#2Cs*6s,)>=#&s#7s*=&s*8s*8,$#&s#8s*@,#%5CCKs,*Ks,&s#<s#:s#7s*Bs*Bs*3>'B)(&($#(Cs#8Js*1)s+bGDDF#I(Cs*/Js*/)s+dGDDF#ICs+eGDDF%#l#*#s+.s+(l#+s+is+h#l#,s+ls+k#j#-C#*s**s2w&#s*-&s*,s*,,$#k#-C#l#.(#s*+6752#2Cs*Os*L#s#6<DS3s#Rs,Js#QS2U.<#*s3\s,I&#s,G*s3^s3&&#s,I8Cs3`?CCCCCCS(s,Ds,Ds,DS(s,;s3as3a#s,Ns3)s,55CCKs,EKs,A(&#s,Ls,Ls,4UU/C7Cs3d:C#s+L(C#Js+I)s+~GDDF#Il#*#s+Gs+Al#+(s,%#l#,s,)s,(#l#.#.El#/s,,s,8#l#0s,4s,1#l#/s,>s,9#642/#@s4[s2o(Cs+2J/)s,-GDDF#Il#*#s+Rs+Ll#+3s,0#l#,s,4s,3#&S4s3vl#.$#E(C6SQs+[)s,4GDDF#Il#*#s+Ys+Sl#+:s,7#l#,s,;s,:#=s3}s,gl#.$#El#/s,?s,K#l#0s,Gs,D#l#/s,Qs,L#As4&-#2Cs4's,k65#&s#*s+#&s*zs4),$#&s#+s+&,#%5CCKs,lKs,hs#/s#-s#*s+(s+(s*u8T#'WU0((#B*)')%#(Cs#*Js*t)s,IGDDF#IZT]s,JGDDFS]Cs,KGDDF$#+s,LGDDFs+Ss+y#l#*#s+qs+kl#+s,Ps,O#l#,s,Ss,R#j#-C#j#1T##1Hs+7&s#<#,#S'k##s+R#k#-C#k#1T##WE:S5T8l#.*$#6;95#2Cs4Ds+6#s#2@DS3s3Ds-4s$;S2U1@#'s3;'#'#.#*S<#;s56#Es-;SZ*%s-:&#s-8*'s3s&#s-:8C)?CCCCCCS(s-5s-5s-5S(s-,**#s-?s3vs-&5CCKs-6Ks-2(&#s-=s-=s-%/s4$'#'#'#.#7C#:Cs,p#/s+S'#'#'#'#/#'#'#/#/#/#'#'#'#'#.#7Cs4X(C4J#)s-(GDDF#I7Cs#':Cs-)#:C#s,W(C#Js,T)s--GDDF#I+s-.GDDF(s,[#l#*#s,Ss,Ml#+s-2s-1#l#,s-5s-4#j#-C#*EB&#s4f*Hs#3*#s4C&#s-fk##&#k#-C#LS<TBl#.+$#l#/s-As-M#l#0s-Is-F#l#/s-Ss-N#6s#8s#6s#3#@s5ps#<'s#)'#/#'#'#/#'#'#'#'#.#7Cs4n(C#Js-L)s-NGDDF#I(Cs,UJs#')s-PGDDF#I+s-QGDDF%s,~#l#*#s,vs,pl#+s-Us-T#l#,s-Xs-W#j#-C#&s4xE&S4s#$k##$#k#-C#LS<T^l#.($#(Cs#4SQs-()s-]GDDF#I+s-^GDDFs#8s-/#l#*#s-'s,}l#+s-bs-a#l#,s-es-d#j#-C#=s#0s.6k##s#2#k#-C#l#.&#s#.l#/s-ls-x#l#0s-ts-q#l#/s-~s-y#As#g1#2Cs#hs.<s#.s#-#&s#fs,P&s,Ks#j,$#&s#gs,S,#%5CCKs.=Ks.9s#ks#is#fs,Us,Us,F>'B)(&($#OCs.ROCs.TOCTTWT_C$#WT_C&#VU2#U3WU4TJ#s-~VTWCS'XU5C#Hs$`VTXCs6Y(Cs-+J#)s.#GDDF#IFC%s,Q(Cs#XJ#)s.&GDDF#IZT]s.'GDDFS+Cs.(GDDF$#+s.)GDDF(s-V#+s.*GDDFs#`s-W#l#*#s-Os-Il#+.s.-#l#,1s.0#j#-C#j#2C#j#1T##&s-/S'*S's$0*#s5@1S]s,u&$#,#S+k##(#k##s#b#k#-C#k#2C#k#1T##YEs#-S5S<TBT8l#./$#6s#.s#,s#)#2Cs$<s,v#s#]s#3DS3s$<s.ts$;S2U6s#3#'s(k.#*S<#;s6t#Es.yS[*%s.x&#s.v*'s5U&#s.x8C)?CCCCCCS(s.ss.ss.sS(s.j**#s.}s5Xs.d5CCKs.tKs.p(&#s.{s.{s.c7C-:Cs.M#:C#s-{(C#Js-x)s.QGDDF#I+s.RGDDFs$,s.##l#*#s-ws-ql#+s.Vs.U#l#,s.Ys.X#j#-C#*H7*#s5e&#s/,k##s$(#k#-C#l#.(#s$$l#/s.bs.n#l#0s.js.g#l#/s.ts.o#6;96#@s75?(Cs-hJ6)s.cGDDF#I+s.dGDDFs#ts.5#l#*#s.-s.'l#+s.hs.g#l#,s.ks.j#j#-C#&S44k##s#r#k#-C#l#.&#s#p(CASQs.9)s.nGDDF#I+s.oGDDFs$Is.@#l#*#s.8s.2l#+s.ss.r#l#,s.vs.u#j#-C#=?s/Gk##s$C#k#-C#l#.&#s$?l#/s.}s/-#l#0s/)s/&#l#/s/3s/.#As#:1#2Cs#;s/M>=#&s#9s-a&s-\s#=,$#&s#:s-d,#%5CCKs/NKs/Js#>s#<s#9s-fs-fs-W>'B)(&($#(Cs#8Js#c)s/*GDDF#ICs/+GDDF#s#b+s/,GDDFs#gs.Y#+s/-GDDFs$cs.Z#l#*#s.Rs.Ll#+s#ms/0#l#,s#ps/3#j#-C#j#2C#j#1T##*S's#P*#s6B&#s#`,#S+k##s#e#k##s$c#k#-C#k#2C#k#1T##YE=S5S<TBT8l#.-$#6><9#2Cs#[s-w#s#=s##DS3s#[s/us#ZS2U7s###i#IU8T9S3s6_S5S<SJSZS[T\S,S:S0S*S&S$ONSUSPSMSIT8T[T^TBU9s-Vs,\s+cs*is)ms(rs'xs'#s&.s%Ds#`#<S;s6aT9s6`HT9S<SZS[<ES,#s6bKL%#.s6J9s7~#m$M#-s8$%##E#$s7{#SJ9s8's6gm$M#-s8)s6i##E#;s8%S5$s8%$#.T>9s8.#m$M#-s80%##E#$s8+#S,9s83s6fm$M#-s85s6h##E#$s80#S:9s88s6fm$M#-s8:s6h##E#$s85#S0.s.E9s8>#m$M#-s8@%##E#$s8;#S*/s6r.#9s8E#m$M#-s8G%##E#$s8B#S&.s+:9s8K#m$M#-s8M%##E#$s8H#S$9s8Ps6wm$M#-s8Rs6y##E#$s8M#O.s%|9s8V#m$M#-s8X%##E#$s8S#N9s8[s6gm$M#-s8]s6i##E##S;$$s8Y$#9s8as6im$M#-s8cs6k##E##S;$$s8_$#9s8gs6im$M#-s8is6k##E##S;$$s8e$#9s8ms6jm$M#-s8os6l##E##S;$$s8k$#9s8ss6lm$M#-s8us6n##E##S;$$s8q$#9s8ys6lm$M#-s8{s6n##E##S;$$s8w$#9s9#s6mm$M#-s9%s6o##E##S;$$s8}$#%)#%0#%7#%>#%s#%#%s#,#%s#3#%s#:#%s#@#%s#G#%s#O#%s#V#%s#\#%s#b#%s#i#%s#p#%s#w#j#3s92#VT`s93#-s96s8bM<S\#S;s8$HS;S<SZS[<ES,#s8&KL%#-s9As#~M#E#$s9<#SJ#Es8'$s9>#s#x-s9Fs#wM#E#$s9A#S,#Es7{$s9C#S:#Es7x$s9E#S0-s9Ms#nM#E#$s9H#S*-s9Ps#jM#E#$s9K#S&-s9Ss#gM#E#$s9N#S$#Es7|$s9P#O-s9Xs#aM#E#$s9S#N#Es7f#S\s7g$s9V$##Es7e#S\s7f$s9Y$##Es7b#S\s7c$s9\$##Es7`#S\s7a$s9_$##Es7_#S\s7`$s9b$##Es7\#S\s7]$s9e$##Es7Z#S\s7[$s9h$#%&#%*#%.#%2#%6#%:#%>#%B#%s#%#%s#)#%s#-#%s#1#%s#4#%s#7#%s#;#%s#>#%s#B#j#3s9y#VT`s9z#0T9S33LS##Qj##%#<SVs#LS\s8mHS\S<SZS[<ES,#s8oKL%##SVs89$s:(s#2##SVs87$s:*s#1##SVs83$s:,s#0##SVs80$s:.s#/##SVs8.$s:0s#.##SVs8*$s:2s#-##SVs8'$s:4s#,#%%#%(#%+#%.#%1#%4#%s#F#%s#J#%s#M#%s#Q#%s#U#%s#Y#%s#\#%s#_#%s#c#%s#f#%A#j#3s:E#U#E<SWs#qSVs96HSVS<SZS[<ES,#s98KL%##SWs8^$s:Ms#W##SWs8\$s:Os#V##SWs8X$s:Qs#U##SWs8U$s:Ss#T##SWs8S$s:Us#S##SWs8O$s:Ws#R##SWs8L$s:Ys#Q#%%#%(#%+#%.#%1#%4#%s#k#%s#o#%s#r#%s#v#%s#z#%s#~#%s$%#%s$(#%s$,#%s$/#%A#<Sbs$8SWs9YHSWS<SZS[<HS,#s9[KL%##Hs$7$s:p#SJ#Hs9[$s:r#s%P#Hs$6$s:t#S,#Hs9R$s:v#S:#Hs9O$s:x#S0#Hs$5$s:z#S*#Hs$4$s:|#S&#Hs$3$s:~#S$#Hs9P$s;$#O#Hs$2$s;&#N#Hs99#Sbs9:$s;)$##Hs98#Sbs99$s;,$##Hs95#Sbs96$s;/$##Hs93#Sbs94$s;2$##Hs92#Sbs93$s;5$##Hs9/#Sbs90$s;8$##Hs9-#Sbs9.$s;;$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6#%s#9#%s#<#0SWSV3LS##Qj##%##S's$t$s;Q#SJ#S's:<$s;S#s&1#S's$s$s;U#S,#S's:3$s;W#S:#S's:0$s;Y#S0#S's$r$s;[#S*#S's$q$s;]#S&#S's$p$s;_#S$#S's:1$s;a#O#S's$o$s;c#N#S's9v#Scs9w$s;f$##S's9u#Scs9v$s;i$##S's9r#Scs9s$s;l$##S's9p#Scs9q$s;o$##S's9o#Scs9p$s;r$##S's9l#Scs9m$s;u$##S's9j#Scs9k$s;x$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6#%s#9#<T2s%VScs:wHScS<SZS[<S]S,#s:yKL%##S+s%U$s<2#SJ#S+s:y$s<4#s&n#S+s%T$s<6#S,#S+s:p$s<8#S:#S+s:m$s<:#S0#S+s%S$s<<#S*#S+s%R$s<>#S&#S+s%Q$s<@#S$#S+s:n$s<B#O#S+s%P$s<D#N#S+s:W#Sfs:X$s<G$##S+s:V#Sfs:W$s<J$##S+s:S#Sfs:T$s<M$##S+s:Q#Sfs:R$s<P$##S+s:P#Sfs:Q$s<S$##S+s:M#Sfs:N$s<V$##S+s:K#Sfs:L$s<Y$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6#%s#9##S-s&2$s<k#SJ#S-s;V$s<m#s'K#S-s&1$s<o#S,#S-s;M$s<q#S:#S-s;J$s<s#S0#S-s&0$s<u#S*#S-s&/$s<w#S&#S-s&.$s<y#S$#S-s;K$s<{#O#S-s&-$s<}#N#S-s;4#Sgs;5$s=$$##S-s;3#Sgs;4$s='$##S-s;0#Sgs;1$s=*$##S-s;.#Sgs;/$s=-$##S-s;-#Sgs;.$s=0$##S-s;*#Sgs;+$s=3$##S-s;(#Sgs;)$s=6$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6#%s#9#0SfT23LS##Qj##%##S.s<4$s=K#s()#S.s&k$s=M#S,#S.s<+$s=O#S:#S.s<($s=Q#S0#S.s&j$s=S#S*#S.s&i$s=U#S&#S.s&h$s=W#S$#S.s<)$s=Y#O#S.s&g$s=[#N#S.s;n#T$s;o$s=^$##S.s;m#T$s;n$s=a$##S.s;j#T$s;k$s=d$##S.s;h#T$s;i$s=g$##S.s;g#T$s;h$s=j$##S.s;d#T$s;e$s=m$##S.s;b#T$s;c$s=p$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6##S?s'H$s>%#SJ#S7s<l$s>'#s(a#S7s'G$s>)#S,$s>*s;jS:$s>+s;iS0#S7s'D$s>-#S*#S7s'C$s>/#S&#S7s'B$s>1#S$$s>2s;nO#S7s'@$s>4#N#Shs<G$s>6s;p##Shs<E$s>8s;p##Shs<A$s>:s;p##Shs<>$s><s;p##Shs<<$s>>s;p##Shs<8$s>@s;p##Shs<5$s>Bs;p#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%#%s#'#%s#)#%s#,#$s>Rs;us)0#S1s'r$s>T#S,#S1s=2$s>V#S:#S1s=/$s>X#S0#S1s'q$s>Z#S*#S1s'p$s>\#S&#S1s'o$s>^#S$#S1s=0$s>`#O#S1s'n$s>b#N#S1s<u#Sis<v$s>e$##S1s<t#Sis<u$s>h$##S1s<q#Sis<r$s>k$##S1s<o#Sis<p$s>n$##S1s<n#Sis<o$s>q$##S1s<k#Sis<l$s>t$##S1s<i#Sis<j$s>w$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#3#%s#6#0ShTC3LS##Qj##%##S8s(M$s?/#S,$s?0s<QS:$s?1s<PS0#S8s(J$s?3#S*#S8s(I$s?5#S&#S8s(H$s?7#S$$s?8s<UO#S8s(F$s?:#N#T%s=M$s?<s<W##T%s=K$s?>s<W##T%s=G$s?@s<W##T%s=D$s?Bs<W##T%s=B$s?Ds<W##T%s=>$s?Fs<W##T%s=;$s?Hs<W#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%#%s#'#%s#)##SEs>A$s?X#s*6#S=s(x$s?Z#S,#S=s>8$s?\#S:$s?]s<AS0#S=s(v$s?_#S*#S=s(u$s?a#S&#S=s(t$s?c#S$$s?ds<FO#S=s(r$s?f#N#Sjs=y$s?hs<H##Sjs=w$s?js<H##Sjs=s$s?ls<H##Sjs=p$s?ns<H##Sjs=n$s?ps<H##Sjs=j$s?rs<H##Sjs=g$s?ts<H#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%#%s#'#%s#*##S9s)F$s@(#S,$s@)s<OS:#S9s>^$s@+#S0#S9s)D$s@-#S*#S9s)C$s@/#S&#S9s)B$s@1#S$#S9s>_$s@3#O#S9s)A$s@5#N#S9s>H#Sks>I$s@8$##S9s>G#Sks>H$s@;$##S9s>D#Sks>E$s@>$##S9s>B#Sks>C$s@A$##S9s>A#Sks>B$s@D$##S9s>>#Sks>?$s@G$##S9s><#Sks>=$s@J$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#0#%s#2#0SjTK3LS##Qj##%##S>s?9$s@]#S:$s@^s=&S0#S>s)w$s@`#S*#S>s)v$s@b#S&#S>s)u$s@d#S$$s@es=+O#S>s)s$s@g#N#Sls>z$s@is=-##Sls>x$s@ks=-##Sls>t$s@ms=-##Sls>q$s@os=-##Sls>o$s@qs=-##Sls>k$s@ss=-##Sls>h$s@us=-#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%#%s#'##SRs*F$sA(#S,#SAs?b$sA*#S:#SAs?_$sA,#S0#SAs*E$sA.#S*#SAs*D$sA0#S&#SAs*C$sA2#S$$sA3s<|O#SAs*A$sA5#N#Sms?H$sA7s<~##Sms?F$sA9s<~##Sms?B$sA;s<~##Sms??$sA=s<~##Sms?=$sA?s<~##Sms?9$sAAs<~##Sms?6$sACs<~#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%#%s#(##SBs@.$sAR#S:$sASs=)S0#SBs*l$sAU#S*#SBs*k$sAW#S&#SBs*j$sAY#S$#SBs@+$sA[#O#SBs*i$sA]#N#SBs?p#Sns?q$sA`$##SBs?o#Sns?p$sAc$##SBs?l#Sns?m$sAf$##SBs?j#Sns?k$sAi$##SBs?i#Sns?j$sAl$##SBs?f#Sns?g$sAo$##SBs?d#Sns?e$sAr$#%&#%*#%.#%2#%6#%:#%>#%A#%s#$#%s#'#%s#*#%s#-#%s#/#0SmTa3LS##Qj##%##SFs@[$sB(#S0#SFs+A$sB*#S*#SFs+@$sB,#S&#SFs+?$sB.#S$$sB/s=_O#SFs+=$sB1#N#Sos@D$sB3s=a##Sos@B$sB5s=a##Sos@>$sB7s=a##Sos@;$sB9s=a##Sos@9$sB;s=a##Sos@5$sB=s=a##Sos@2$sB?s=a#%%#%(#%+#%.#%1#%4#%7#%:#%<#%?#%B#%s#%##S^sA)$sBM#S:#SGsA&$sBO#S0#SGs+h$sBQ#S*#SGs+g$sBS#S&#SGs+f$sBU#S$#SGsA'$sBW#O#SGs+e$sBY#N#Sps@l$sB[s=Z##Sps@j$sB]s=Z##Sps@f$sB_s=Z##Sps@c$sBas=Z##Sps@a$sBcs=Z##Sps@]$sBes=Z##Sps@Z$sBgs=Z#%%#%(#%+#%.#%1#%4#%7#%:#%=#%@#%s###%s#&##SHsAL$sBu#S0#SHs,2$sBw#S*#SHs,1$sBy#S&#SHs,0$sB{#S$$sB|s=gO#SHs,.$sB~#N#SHsA5#SqsA6$sC%$##SHsA4#SqsA5$sC($##SHsA1#SqsA2$sC+$##SHsA/#SqsA0$sC.$##SHsA.#SqsA/$sC1$##SHsA+#SqsA,$sC4$##SHsA)#SqsA*$sC7$#%&#%*#%.#%2#%6#%:#%>#%A#%s###%s#&#%s#)#%s#,#0SpU:3LS##Qj##%##SKs,_$sCH#S*#SKs,^$sCJ#S&#SKs,]$sCL#S$#SKsAz$sCN#O#SKs,\$sCP#N#T&sAc$sCRs>;##T&sAa$sCTs>;##T&sA]$sCVs>;##T&sAZ$sCXs>;##T&sAX$sCZs>;##T&sAT$sC\s>;##T&sAQ$sC^s>;#%%#%(#%+#%.#%1#%4#%7#%:#%=#%@#%s####SdsBB$sCk#S0#SLs-($sCm#S*#SLs-'$sCo#S&#SLs-&$sCq#S$#SLsBC$sCs#O#SLs-%$sCu#N#SLsB,#SrsB-$sCx$##SrsB+$sCzs>8##SrsB'$sC|s>8##SrsB$$sC~s>8##SrsA~$sD$s>8##SrsAz$sD&s>8##SrsAw$sD(s>8#%%#%(#%+#%.#%1#%4#%8#%;#%>#%A#%s#$##SIs-L$sD5#S*#SIs-K$sD7#S&#SIs-J$sD9#S$#SIsBg$sD;#O#SIs-I$sD=#N#SssBP$sD?s>H##SIsBN#SssBO$sDB$##SIsBK#SssBL$sDE$##SIsBI#SssBJ$sDH$##SIsBH#SssBI$sDK$##SIsBE#SssBF$sDN$##SIsBC#SssBD$sDQ$#%&#%*#%.#%2#%6#%:#%=#%@#%s###%s#&#%s#)#0SrTb3LS##Qj##%##SNs-u$sDa#S&#SNs-t$sDc#S$#SNsC5$sDe#O#SNs-s$sDg#N#SNsBz#T'sB{$sDj$##T'sBy$sDls>s##T'sBu$sDns>s##T'sBr$sDps>s##T'sBp$sDrs>s##T'sBl$sDts>s##T'sBi$sDvs>s#%%#%(#%+#%.#%1#%4#%8#%;#%>#%A##S}s.=$sE&#S*#SOs.<$sE(#S&#SOs.;$sE*#S$#SOsCX$sE,#O#SOs.:$sE.#N#SOsCA#StsCB$sE1$##SOsC@#StsCA$sE4$##StsC=$sE6s>t##StsC:$sE8s>t##StsC8$sE:s>t##StsC4$sE<s>t##StsC1$sE>s>t#%%#%(#%+#%.#%1#%5#%9#%<#%?#%B##SMs.^$sEJ#S&#SMs.]$sEL#S$#SMsCz$sEN#O#SMs.\$sEP#N#SMsCc#T(sCd$sES$##T(sCb$sEUs?)##SMsC^#T(sC_$sEX$##SMsC\#T(sC]$sE[$##SMsC[#T(sC\$sE^$##SMsCX#T(sCY$sEa$##SMsCV#T(sCW$sEd$#%&#%*#%.#%2#%6#%9#%=#%@#%s###%s#&#0StU;3LS##Qj##%##SSs/($sEs#S$#SSsDE$sEu#O#SSs/'$sEw#N#SSsD.#T)sD/$sEz$##SSsD-#T)sD.$sE}$##T)sD*$sF#s?Q##T)sD'$sF%s?Q##T)sD%$sF's?Q##T)sC}$sF)s?Q##T)sCz$sF+s?Q#%%#%(#%+#%.#%1#%5#%9#%<#%?##T1s/J$sF6#S&#STs/I$sF8#S$#STsDf$sF:#O#STs/H$sF<#N#STsDO#SusDP$sF?$##STsDN#SusDO$sFB$##STsDK#SusDL$sFE$##SusDI$sFGs?V##SusDG$sFIs?V##SusDC$sFKs?V##SusD@$sFMs?V#%%#%(#%+#%.#%2#%6#%:#%=#%@##SPs/i$sFX#S$#SPsE*$sFZ#O#SPs/h$sF\#N#SPsDo#SvsDp$sF_$##SPsDn#SvsDo$sFb$##SvsDk$sFds?h##SPsDh#SvsDi$sFg$##SPsDg#SvsDh$sFj$##SPsDd#SvsDe$sFm$##SPsDb#SvsDc$sFp$#%&#%*#%.#%2#%5#%9#%=#%@#%s###0SuU<3LS##Qj##%##SXsEN$sF~#O#SXs00$sG$#N#SXsE7#T*sE8$sG'$##SXsE6#T*sE7$sG*$##SXsE3#T*sE4$sG-$##T*sE1$sG/s@1##T*sE/$sG1s@1##T*sE+$sG3s@1##T*sE($sG5s@1#%%#%(#%+#%.#%2#%6#%:#%=##T7s0P$sG?#S$#SYsEm$sGA#O#SYs0O$sGC#N#SYsEV#SwsEW$sGF$##SYsEU#SwsEV$sGI$##SYsER#SwsES$sGL$##SYsEP#SwsEQ$sGO$##SwsEO$sGQs@:##SwsEK$sGSs@:##SwsEH$sGUs@:#%%#%(#%+#%/#%3#%7#%;#%>##SUsF/$sG_#O#SUs0m$sGa#N#SUsEt#SxsEu$sGd$##SUsEs#SxsEt$sGg$##SUsEp#SxsEq$sGj$##SxsEn$sGls@M##SUsEl#SxsEm$sGo$##SUsEi#SxsEj$sGr$##SUsEg#SxsEh$sGu$#%&#%*#%.#%1#%5#%9#%=#%@#0SwU=3LS##Qj##%##S_s12$sH&#N#S_sF9#SysF:$sH)$##S_sF8#SysF9$sH,$##S_sF5#SysF6$sH/$##S_sF3#SysF4$sH2$##SysF2$sH4s@o##SysF.$sH6s@o##SysF+$sH8s@o#%%#%(#%+#%/#%3#%7#%;##T@sFm$sHA#O#S`s1O$sHC#N#S`sFV#SzsFW$sHF$##S`sFU#SzsFV$sHI$##S`sFR#SzsFS$sHL$##S`sFP#SzsFQ$sHO$##S`sFO#SzsFP$sHR$##SzsFL$sHTs@|##SzsFI$sHVs@|#%%#%(#%,#%0#%4#%8#%<##Sas1k$sH_#N#SasFr#T+sFs$sHb$##SasFq#T+sFr$sHe$##SasFn#T+sFo$sHh$##SasFl#T+sFm$sHk$##T+sFk$sHmsA4##SasFg#T+sFh$sHp$##SasFe#T+sFf$sHs$#%&#%*#%-#%1#%5#%9#%=#0SzU>3LS##Qj##%##S2sG4#S{sG5$sI$$##S2sG3#S{sG4$sI'$##S2sG0#S{sG1$sI*$##S2sG.#S{sG/$sI-$##S2sG-#S{sG.$sI0$##S{sG*$sI2sAS##S{sG'$sI4sAS#%%#%(#%,#%0#%4#%8##TIs2H$sI<#N#SesGO#S|sGP$sI?$##SesGN#S|sGO$sIB$##SesGK#S|sGL$sIE$##SesGI#S|sGJ$sIH$##SesGH#S|sGI$sIK$##SesGE#S|sGF$sIN$##S|sGC$sIPsAd#%%#%)#%-#%1#%5#%9##S~sGi#T,sGj$sIY$##S~sGh#T,sGi$sI\$##S~sGe#T,sGf$sI_$##S~sGc#T,sGd$sIb$##S~sGb#T,sGc$sIe$##T,sG_$sIgsAy##S~sG\#T,sG]$sIj$#%&#%)#%-#%1#%5#%9#0S|U?3LS##Qj##%##S3sH&#T-sH'$sIv$##S3sH##T-sH$$sIy$##S3sG}#T-sG~$sI|$##S3sG|#T-sG}$sJ#$##S3sGy#T-sGz$sJ&$##T-sGw$sJ(sB8#%%#%)#%-#%1#%5##T9sH@#TcsHA$sJ0$##S;sH?#T.sH@$sJ3$##S;sH<#T.sH=$sJ6$##S;sH:#T.sH;$sJ9$##S;sH9#T.sH:$sJ<$##S;sH6#T.sH7$sJ?$##S;sH4#T.sH5$sJB$#%&#%*#%.#%2#%6##T3sHV$sJIs3O##T3sHR$sJKs3N##T3sHO$sJMs3M##T3sHM$sJOs3L##T3sHI$sJQs3K##T3sHF$sJSs3J#%%#%(#%+#%.#%1#0T.Tc3LS##Qj##%##T4sHd$sJ]s34##T4sHa$sJ_s34##T4sH_$sJas34##T4sH[$sJcs34##T4sHX$sJes34#%%#%(#%+#%.##TdsHx$sJks2{##T5sHt$sJms2A##T5sHq$sJos2@##T5sHo$sJqs2?##T5sHk$sJss2>##T5sHh$sJus2=#%%#%(#%+#%.##T:sI&$sJ{s1n##T:sI#$sJ}s1m##T:sH}$sK#s1l##T:sHy$sK%s1k##T:sHv$sK's1j#%%#%(#%+#%.#0T5Td3LS##Qj##%##T2sI2#T;sI3$sK1$##T2sI1#T;sI2$sK4$##T2sI.#T;sI/$sK7$##T2sI,#T;sI-$sK:$#%&#%*#%.##TesIF$sK?s1Q##T<sIC$sKAs0s##T<sIA$sKCs0r##T<sI=$sKEs0q##T<sI:$sKGs0p#%%#%(#%+##TDsIN$sKLs0D##TDsIL$sKNs0C##TDsIH$sKPs0B##TDsIE$sKRs0A#%%#%(#%+#0T<Te3LS##Qj##%##TCsIX#TEsIY$sK[$##TCsIU#TEsIV$sK^$##TCsIS#TEsIT$sKa$#%&#%*##TfsIg$sKes0,##TFsIe$sKgs/U##TFsIa$sKis/T##TFsI^$sKks/S#%%#%(##TLsIm$sKos/.##TLsIi$sKqs/.##TLsIf$sKss/.#%%#%(#0TFTf3LS##Qj##%##TKsIr#TMsIs$sK{$##TKsIp#TMsIq$sK~$#%&##TNsJ#$sL%s.p##TOsI{$sL's.?##TOsIx$sL)s.>#%%##TgsJ$$sL,s-t##TgsI}$sL.s-t#%%#0TOTN3LS##Qj##%##TasJ'#TGsJ($sL5$##THsJ/$sL7s-U##TPsJ,$sL9s-&#HTPS<SZS[0THTGMLSCSDT=#JT6TGISCSDT/TH%$#WU@&#TN0HEMLSCSDT=#JTQHISCSDUAS]HThS<SZS[<TbS,#sK4$T?sL>#\UBThUCS-S+TQS]S'HVTSS-S+MLSCSDT=sJ1JT6S-ISCSDT/S.%$#%&#0S?S.3LS##Qj##%#JT6S.ISCSDT/S?%$#0S7S?MLSCSDT=#JT6S7ISCSDT/S1%$#JT6S1ISCSDT/S8%$#0SES83LS##Qj##%#ISCSDT/SEJT6SEISCSDT/S9#T0sJk$sLdES/j#4sLe#2sLf%#T4s(aSO#T0sJj$sLhES)j#4sLi#2sLj%#T-s(bSL#T0sJj$sLlES%j#4sLm#2sLn%#S{s(cSG#T0sJh$sLpERj#4sLq#2sLr%#Sys(dSA#T0sJg$sLtEPj#4sLu#2sLv%#Sxs(eSR#T0sK-$sLxES@j#4sLy#2sLz%#TEs(zSY#T0sK-$sL|ES6j#4sL}#2sL~%#T;s({STi#=UDSvUESsSqSnSkSiSgSbS;SeS`;73/+'#UFS>S9S=HES1j#5@#j#6B#V#HEj##s#%#j##s#,#4s#-s#,s#(#Ej#7s#/#j#8s#3#V#HEj##s#7#j##s#B#4s#Cs#@s#<#El#7s#Fs#E#j#9s#H#j#:s#L#j#;s#N#j#<s#P#j#=Ti#j#>T?#fUGLSCSDT=THTQsL'TPsL%SoS,s#[TGQs#UTMSl#j#?s#]#j#@s#`#V#HEj##s#d#j##s#n#4s#os#ms#i#Ej#7s#r#j#As#x#V#HEj##s#|#j##s$1#4s$2s$-s$)#Ej#7s$5#j#Bs$>#V#HEj##s$B#j##s$Z#4s$[s$Ss$O#Ej#7s$^#j#Cs$j#V#HEj##s$n#j##s%1#4s%2s%'s%##Ej#7s%5#j#Ds%D#V#HEj##s%H#j##s%i#4s%js%\s%X#Ej#7s%m#j#Es&)#V#HEj##s&.#j##s&_#4s&`s&Js&F#Ej#7s&d#j#Fs'##V#HEj##s''#j##s'_#4s'`s'Fs'B#Ej#7s'c#j#Gs($#V#HEj##s((#j##s(e#4s(fs(Is(E#Ej#7s(i#j#Hs),#V#HEj##s)0#j##s)r#4s)ss)Ss)O#Ej#7s)v#j#Is*;#V#HEj##s*?#j##s+*#4s++s*ds*`#Ej#7s+.#j#Js+Q#V#HEj##s+U#j##s,E#4s,Fs+|s+x#Ej#7s,I#j#Ks,n#V#HEj##s,r#j##s-g#4s-hs-?s-;#Ej#7s-k#j#Ls.6#V#HEj##s.:#j##s/4#4s/5s.es.a#Ej#7s/8#j#Ms/a#V#HEj##s/e#j##s0d#4s0es06s02#Ej#7s0h#j#Ns17#V#HEj##s1;#j##s2@#4s2As1js1f#Ej#7s2C#j#Os2p#V#HEj##s2t#j##s4-#4s4.s3Ts3P#Ej#7s41#j#Ps4k#V#HEj##s4q#j##s60#4s61s5Ts5P#Ej#7s66#j#QsNB#V#HEj##s6\#j#%sNE#YUHsNFs7+s7'#El#Rs95s7r#j#SsFX#j#TsF[#V#HEj##sF_#j##sFh#4sFisFgsFc#Ej#7sFl#j#UsFr#V#HEj##sFv#j##sG)#4sG*sG%sF}#Ej#7sG-#j#VsG6#V#HEj##sG:#j##sGO#4sGPsGHsGD#Ej#7sGS#j#WsG_#V#HEj##sGc#j##sG~#4sH#sGtsGp#Ej#7sH&#j#XsH5#V#HEj##sH9#j##sHZ#4sH[sHMsHI#Ej#7sH^#j#YsHp#V#HEj##sHt#j##sI?#4sI@sI/sI+#Ej#7sIC#j#ZsIX#V#HEj##sI\#j##sJ-#4sJ.sIvsIr#Ej#7sJ1#j#[sJI#V#HEj##sJM#j##sK$#4sK%sJjsJf#Ej#7sK(#j#\sKC#V#HEj##sKG#j##sL$#4sL%sKgsKc#Ej#7sL(#j#]sLF#V#HEj##sLJ#j##sMb#4sMcsLmsLi#S]j#^sMq#j#_sN~#j#`sO$#j#asO&#j#bTi#j#cT?#j#'sO*#j#dsO/##"). Qed.

  Lemma finish_nil : forall regs m msF mo,
    RI regs -> LM m -> LZ msF mo -> restrict L S msF = mkst regs (0x1091cc : word) m (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit [] K).
  (* [Proof using All]: see As/AsStdioWrite.v's finish_nil. *)
  Proof using All. intros. apply rz_emit_nil. eapply finish; eassumption. Qed.


  (* [comment removed for export] *)
  Lemma pc_10924c : v_addi (0x109248 : word) 4 = (0x10924c : word).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma loop1 : forall n regs m msF mo (k : nat) (b : word) (bs : list byte),
    (length bs <= n)%nat ->
    RI regs -> LM m -> LZ msF mo -> restrict L S msF = mkst regs (0x109258 : word) m (seg_rom RSEGS) ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
    (Z.of_nat (length bs) <= 2 ^ 30)%Z ->
    realizes RSEGS (mkCfg msF mo)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  (* loop1, loop2 and as_stdio_write: plain text, as in As/AsStdioWrite.v. *)
  Proof using All.
    induction n as [|n IH]; intros regs m msF mo k b bs LEN RIr LMm LZm RS Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZm) | exact RS | exact RUN |]. clear RUN.
    intros msFa moa OKa SBa HSa RSa. pose proof (LZ_next _ _ _ _ LZm OKa SBa HSa) as LZa.
    replace (su - 88 + 8)%Z with (su - 80)%Z in RSa by lia.
    set (m' := wbytes (wbytes m _ _) _ _) in RSa.
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (rz_writev1_wall_lazy RSEGS L S Zr msFa regs1 (0x109248 : word) m' moa W_109248 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_109248 | exact E_109248 | exact (proj1 LZa) | subst m'; exact RSa | exact (LZ_fd _ _ LZa) | exact (LZ_rdr _ _ LZa) | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - unfold TASK_SIZE. u_norm. lia.
    - unfold TASK_SIZE. u_norm. lia.
    - u_norm. lia.
    - u_norm. lia.
    - (* [comment removed for export] *)
      intros k' msFb mob K1 K2 OKb SBb RSb HSb. pose proof (LZ_next _ _ _ _ LZa OKb SBb HSb) as LZb. rewrite pc_10924c in RSb. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply (finish_nil regs2 m' msFc moc); [| exact LMm' | exact LZc | exact RSc].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
        apply (IH regs2 m' msFc moc k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact LZc.
        * exact RSc.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.


  (* [comment removed for export] *)
  Lemma loop2 : forall n regs m msF mo (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m -> LZ msF mo -> restrict L S msF = mkst regs (0x109258 : word) m (seg_rom RSEGS) ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    realizes RSEGS (mkCfg msF mo)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof using All.
    induction n as [|n IH]; intros regs m msF mo k b0 bs0 b1 bs1 LEN RIr LMm LZm RS Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZm) | exact RS | exact RUN |]. clear RUN.
      intros msFa moa OKa SBa HSa RSa. pose proof (LZ_next _ _ _ _ LZm OKa SBa HSa) as LZa.
      replace (su - 104 + 8)%Z with (su - 96)%Z in RSa by lia.
      set (m' := wbytes (wbytes m _ _) _ _) in RSa.
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rz_writev2_wall_lazy RSEGS L S Zr msFa regs1 (0x109248 : word) m' moa W_109248 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_109248 | exact E_109248 | exact (proj1 LZa) | subst m'; exact RSa | exact (LZ_fd _ _ LZa) | exact (LZ_rdr _ _ LZa) | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' msFb mob K1 K2 OKb SBb RSb HSb. pose proof (LZ_next _ _ _ _ LZa OKb SBb HSb) as LZb. rewrite pc_10924c in RSb. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply (finish_nil regs2 m' msFc moc); [| exact LMm' | exact LZc | exact RSc].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
          apply (IH regs2 m' msFc moc k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact LZc.
          -- exact RSc.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZm) | exact RS | exact RUN |]. clear RUN.
      intros msFa moa OKa SBa HSa RSa. pose proof (LZ_next _ _ _ _ LZm OKa SBa HSa) as LZa.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z in RSa by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) in * by lia.
      set (m' := wbytes (wbytes m _ _) _ _) in RSa.
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rz_writev1_wall_lazy RSEGS L S Zr msFa regs1 (0x109248 : word) m' moa W_109248 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_109248 | exact E_109248 | exact (proj1 LZa) | subst m'; exact RSa | exact (LZ_fd _ _ LZa) | exact (LZ_rdr _ _ LZa) | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' msFb mob K1 K2 OKb SBb RSb HSb. pose proof (LZ_next _ _ _ _ LZa OKb SBb HSb) as LZb. rewrite pc_10924c in RSb. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply (finish_nil regs2 m' msFc moc); [| exact LMm' | exact LZc | exact RSc].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next _ _ _ _ LZb OKc SBc HSc) as LZc.
          apply (loop1 (length bs1) regs2 m' msFc moc k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact LZc.
          -- exact RSc.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].

Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x123ef0 <= f)%Z -> (f + 232 <= 0x1240d0)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioWrite.LM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioWrite_run1.mem_sw1); constr:(@kc__2); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioDefs.sw_post); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioWrite_run2.mem_sw2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioDefs.Build_sw_post); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_add); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.wbytes_outside); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.not_morph); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StepTac.u_Z2bv); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.length_N_to_le_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.in_rng); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows_trans); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.mem_grows_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.wbytes_grows); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SeqExec.rdn_wbytes_hit8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SumWalkTac.rdn_wbytes_out_Z); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.Tauto.OR)|] [|@x; @o; @n; @z; @y; @m; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat7; @__sat8; @Hx; @Hx3; @Hx2; @Hx1; @G; @E; @H; @Fhi; @Flo; @SUhi; @SUlo; @bufsz; @bufp; @l; @s; @wb; @can; @s6; @s5; @s4; @s3; @s2; @s1; @s0; @ra; @f; @su; @mem|] "#Bc#F$N#N$($)$'$2#l$1#'#O#%#P#$$3#a#Z#>###<$<#B#A#=#-#;$H#4#3#9#2#5#1#8#7#.#,#:#6#0#/#C#*#)#?#@#D#L#+#^#(#m#F$M$N$O$K#J#I#M#&#x#{#|#~$/$8$9#E#d#T#S#]#`#b#h#t#u#v#w#y#z$##}$$$&$4$6$:$;$7$?$>$@$E#_#U#W$-$,#K#c#V$%#X#e#Y#r$+#n#j#p#f$5$0#Q$*#s$=#q$D#o$A$B$C#k$F#R$.$L#[#g$G#\$I#i$JU#+%$&%#-%#1%$''$(*$)$$*)$+$$,+$-%$.%$/%$0/$1*$2'#f&$3%$4)$5%$6&$7%$8$$9)$:5$;&$<$#T$$=(#f'$>&$?%$@%$A&$B)$C&$D$$E&$F%$G&$H$$I'#3%#g2$J%#3&$K%#g3$L%$M()S@)#)#)#)#)#USJ#USK#USJ(USK#USL#k##&#)))#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#9#GS@G#)#)#)#)#9#%*###S-)-)#)#)#)#)#)#)#)#)#)#)#)#)#)#9##S,#Gs#B)#)#G#)#)#)#)#)#)#G#)#)#G#)#)#)#)#9#)S@)#G#)#)#)#G#G#G#G#G#)#G#G#G#G#)#)#)#)#9#G3)#)#)#)#)#)#G#G#)#G#)#)#)#)#9##3S,Gs#S)#)#)#9#%S0#Gs#:)#)#G#G#G#)#)#)#)#9##.5NS.S3S0S,S-S/S1S8S9S4S)S5SAS;S<WSXS3#S2)s#iG#)#)#)#9#-S.#/s$5S##$#)s#V9#-S.#&'#$'#+#US*NRS$S6S2S3S7S0S,S-S/S1S8S9S4S)S5NJs$;$#k##&#k#$s$@#NS6S2S7S0S,S-S/S1S8S9S4S)S5SAS;O#S.$%#XSBS6S2S;S<ZSYS*S.S2S;S<#j##%#NS*S.S3S7S0S,S-S/S1S8S9S4S)S5SAO#S6-S*9##8-S*6&:#$%#+#US(NRRS$S6S.S2S3S7S0S,S-S/S1S8S9S4NJs$N$#k##&#k#$s$S#NS(S*S.S2S3S7S0S,S-S/S1S8S9S4S)O#S$XSBS(S*S)S5-S(s$1##s#&&s#'S($$#+#9s$_%S(#/s$_N#$#)s#5)#)#9#%S(#&)#$)#+#9s$D%R#/s$kL#$#9s$n%R#&&#$&#+#USZSM/s$sSM#P#9s${VS[#+&&#$&#%S>>.s$z#KS\K#K#K#K#K#K#K#SS/S16$#3S&-#Gs%0)#)#)#9#%S>#.s%0#6-S/@+$#JUS?SCJs%0S##j#%s%1#@S&:0JUS&JRS:S'S=RS(S$S*S6S.S2S3S7S0S,S-J9s%=-S'#.s%;#68S=3S:$#9s%A-S'#.s%@#6=R3'$#9s#?-S'#.s%E#6BS(3'$#-S's#I.s%I#6s#&S$3&$#-S'@.s%M#6s#*S*3&$#-S's#J.s%Q#6s#.S63&$#-S's#I.s%U#6s#2S.3&$#-S's#I.s%Y#6s#6S23&$#-S's$&.s%]#6s#:S33&$#-S's$/.s%a#.s%bS76s#?#3'%#)s#`9#-S'#.s%h#.s%iS06s#F#3)%#Gs#D)#)#)#9#-S'#.s%r#6s#OS,@+$#J@3/-J@975J@><;J@s##A@J@s#(s#&s#%J@s#-s#+s#*J@s#2s#0s#/J@s#7s#5s#4J@s#=s#:s#9J@s#Cs#@s#?J@S:s#Fs#EJUS:J4s%}#-S&s#K.s&'#/s&(#/s&)SC#$#>S#%&#&&#$&#+#j#&H##S#*>s#j%S##&-#$&#+#j#'C#/s&8J#s#]#%s#^*&%#$%#+#%s#bs#c&)#$)#+#=+j#$CS#&NS#=#j#(C#j#$C#4C2%NS#XS]CCS^#4C#j#)C#j#&C#4Cs#r4Cs#&j#$H#4Cs#v`S_HCCCSDSD11$s$.s#w#;CCCCCCM222M(s#ws#w's##s#x#0CCQ3Q/>>.<8#5><>85#A<8#VS`s$@s$H&Ps$A#Ps$J&Ps$Bk##$#k##&##Ps$FWSas$Gs$ONj##SN#j#*%##Ps$Ik##SN#k#*(#USbSOUSPSOVSQCLUScCXSdC$N#USeCUSfCVSRCS@8Cs&EHC$#VSRCs&t'C$I#((FDDE#G'C%O((*FDDE#G1+FDDE%#:,FDDE#USgD8Cs$?HC.#'C#I,(1FDDE#G7C%&'C/O#(4FDDE#G15FDDE&#:6FDDE#,7FDDE-,#VSh8E4SSSTVSiS#LJSS#STm$%#WSjCPNXSkS#L$#l#+*)#l#,BA#l#-s#'s#&#j#.C#j#/C#-S#s&e##N$#s#Lk###S%-Ns$Y##L%$s$[&L#$%#k###S%k##)#k#.C#k#/C#/s'=S;P#S?S<l#02%#l#1s#>s#;#l#2s#Hs#C#2s#cs#_s#J#/s'Cs$fVSlPs%-4Sm#m##s#LUN#VSQCN8Cs')7C#s#<'C#Is#>(s#@FDDE#G8CP'C#Is#5(s#CFDDE#G,s#DFDDE&s#9#l#+#s#/s#)l#,,s#G#l#-s#Ms#L#j#.C##s'-S##Ps#$k##$#k#.C#MSUS,l#0($#l#26s#^#l#1s#Zs#W#l#2s#ds#_#8Cs'%'Cs#RI#(s#TFDDE#G8Cs%JWSnC#s'b'Cs#JO#(s#XFDDE#G,s#YFDDE's#N#l#+#s#Ds#>l#,As#\#l#-s#bs#a#j#.C##S#s'1&s#9s%Sk##$#k#.C#MSUS-l#0($#l#2s#+s#s#l#1s#os#l#l#2s#ys#t#<s%;8#*Cs%<s$?s#4s#3##s#4s$?%s#5s$F&s$A#$%#+#m#(#Bs'xs%ACs%XS=*Hs%Ys$O%$#>%DJs%F#+#m#&##s$Xs%jj#&H##s$Ss%lj#'C##s$Ns%n#s$Ks%o#NS#=#j#(C#j#$C#4Cs%t0CCKs$LK$s$Us$Qs$<s%us%u#'Cs#rIs#.(s$'FDDE#G,s$(FDDEs#2s#y#l#+#s#os#il#,s#Ls$+#l#-s$1s$0#j#.C##s#as%}k##s#.#k#.C#l#0&#s#,l#2s#Ts$@#l#1s$<s$9#l#2s$Fs$A#2871#*Cs%e:#s#\s#,#s#*s&*m#$#*Hs%|?#s#'s#&Es%gS:s%hJB#*s(Bs%$s%os%#s%%#-S&s%g.s(H#/s(I###s%#%$s$~&s%%#$%#+#j#&H##s%os$v%s%ps$}&s$x#$%#+#%s%ts%z&s$|#$)#+#=+4Cs%y;CCCCCCMs$vs$vs$vMs$ls%zs%z#s%+s&$s$g0CCQs$wQs$ss%&s%&s$r-)#5/-/)&#A-)#8Cs&#HCs$S#'C#Is$Q(s$VFDDE#G7C%s$K'Cs$TO#(s$YFDDE#G1s$ZFDDE&#:s$[FDDE#,s$\FDDEs$Rs$Q#l#+#s$Gs$Al#,s$`s$_#l#-s$es$d#j#.C#j#/C#-Ns&2##L%$s&9&L#$%#k###S%k##s$C#k#.C#k#/C#l#0,#s$;l#1s$vs$s#l#2s%$s${#2s#(s#$>#/s({s&='Cs$1I>(s$qFDDE#G,s$rFDDEs$4s$g#l#+#s$]s$Wl#,s$:s$u#l#-s${s$z#j#.C##P7k##s$1#k#.C#l#0&#s$/l#2s$Bs%.#l#1s%*s%'#l#2s%4s%/#'Cs#,Os$*(s%#FDDE#G,s%$FDDEs$.s$u#l#+#s$ks$el#,s$Hs%'#l#-s%-s%,#j#.C#&s#%s&yk##s$*#k#.C#l#0&#s$(l#2s$Ps%<#l#1s%8s%5#l#2s%Bs%=#<s&[1#*Cs&\s%dA@##As%d%Bs%k&s%f#$%#+#m#(#Bs)As&aCs&}R*Hs&~s#U%$#>%DJs&f#+#m#&##s#^s'3j#&H##s#Zs'5#s#Ws'60CCKs%jKs#~s#\s#Xs#Rs'7s'7s#}'Cs#KIs$L(s%EFDDE#G,s%FFDDEs$Ps%;#l#+#s%1s%+l#,s$js%I#l#-s%Os%N#j#.C##s#Es'?k##s$L#k#.C#l#0&#s$Jl#2s$rs%^#l#1s%Zs%W#l#2s%ds%_#2321#*Cs&~s$8#s#Bs#%#s##s'Hm#$#*Hs'>8#@?Es'$s'(s'%J;#*s)`s&Cs'1s#|s&D#-S&s'$.s)f#/s)g###s&A%$s&@&s&C#$%#+#j#&H##s',s&8%s'-s&?&s&:#$%#+#%s'1s'<&s&>#$)#+#=+4Cs'6;CCCCCCMs&8s&8s&8Ms&.s'7s'7#s&Is'Bs&)0CCQs&9Qs&5s&Ds&Ds&4-)#5/-/)&#A-)#8Cs'<HCs%q#'C#Is%o(s%tFDDE#G7C%s%i'Cs%rO#(s%wFDDE#G1s%xFDDE&#:s%yFDDE#,s%zFDDEs%ps%o#l#+#s%es%_l#,s%~s%}#l#-s&'s&&#j#.C#j#/C#-Ns'K##L%$s'W&L#$%#k###S%k##s%a#k#.C#k#/C#l#0,#s%Yl#1s&8s&5#l#2s&Bs&=#2s#(s#$>#/s*=s'V'Cs%OI>(s&3FDDE#G,s&4FDDEs%Rs&)#l#+#s%{s%ul#,s%Xs&7#l#-s&=s&<#j#.C##P7k##s%O#k#.C#l#0&#s%Ml#2s%`s&L#l#1s&Hs&E#l#2s&Rs&M#'Cs#,Os%H(s&AFDDE#G,s&BFDDEs%Ls&7#l#+#s&-s&'l#,s%fs&E#l#-s&Ks&J#j#.C#&s#%s(;k##s%H#k#.C#l#0&#s%Fl#2s%ns&Z#l#1s&Vs&S#l#2s&`s&[#<s't1#*Cs'us'&A@##As'&%Bs'-&s'(#$%#+#m#(#Bs*_s'zCs(?S(*Hs(@s#U%$#>%DJs(##+#m#&##s#^s(Qj#&H##s#Zs(S#s#Ws(T0CCKs',Ks%@s#\s#Xs#Rs(Us(Us%?'Cs#KIs%j(s&cFDDE#G,s&dFDDEs%ns&Y#l#+#s&Os&Il#,s&,s&g#l#-s&ms&l#j#.C##s#Es(]k##s%j#k#.C#l#0&#s%hl#2s&4s&|#l#1s&xs&u#l#2s'&s&}#2321#*Cs(;s%V#s#Bs#%#s##s(fm#$#*Hs(\8#@?Es(=s(As(>J;#*s*~s'bs(Os#|s'c#-S&s)(.s+(#/s+)###s'_%$s'^&s'a#$%#+#j#&H##s(Fs'V%s(Gs']&s'X#$%#+#%s(Ks(Z&s'\#$)#+#=+4Cs(P;CCCCCCMs'Vs'Vs'VMs'Ls(Qs(Q#s'gs(`s'G0CCQs'WQs'Ss'bs'bs'R-)#5/-/)&#A-)#8Cs)@HCs'3#'C#Is'1(s'6FDDE#G7C%s'+'Cs'4O#(s'9FDDE#G1s':FDDE&#:s';FDDE#,s'<FDDEs'2s'1#l#+#s''s&}l#,s'@s'?#l#-s'Es'D#j#.C#j#/C#-Ns)O##L%$s(u&L#$%#k###S%k##s'##k#.C#k#/C#l#0,#s&wl#1s'Vs'S#l#2s'`s'[#2s#(s#$>#/s+[s(p'Cs&mI>(s'QFDDE#G,s'RFDDEs&ps'G#l#+#s'=s'7l#,s&vs'U#l#-s'[s'Z#j#.C##P7k##s&m#k#.C#l#0&#s&kl#2s&~s'j#l#1s'fs'c#l#2s'ps'k#'Cs#,Os&f(s'_FDDE#G,s'`FDDEs&js'U#l#+#s'Ks'El#,s'(s'c#l#-s'is'h#j#.C#&s#%s)Yk##s&f#k#.C#l#0&#s&dl#2s'0s'x#l#1s'ts'q#l#2s'~s'y#<s)21#*Cs)3s(DA@##As(D%Bs(K&s(F#$%#+#m#(#Bs+}s)8Cs)]S$*Hs)^s#U%$#>%DJs)=#+#m#&##s#^s)oj#&H##s#Zs)q#s#Ws)r0CCKs(JKs&^s#\s#Xs#Rs)ss)ss&]'Cs#KIs',(s(%FDDE#G,s(&FDDEs'0s'w#l#+#s'ms'gl#,s'Js()#l#-s(/s(.#j#.C##s#Es){k##s',#k#.C#l#0&#s'*l#2s'Rs(>#l#1s(:s(7#l#2s(Ds(?#2321#*Cs)Us&t#s#Bs#%#s##s*(m#$#*Hs)z8#@?Es)Ws)Zs)XJ;#*s,@s)%s)ms#|s)&#-S&s)u.s,F#/s,G###s(}%$s(|&s)##$%#+#j#&H##s)`s(t%s)as({&s(v#$%#+#%s)es)x&s(z#$)#+#=+4Cs)j;CCCCCCMs(ts(ts(tMs(js)ks)k#s))s)~s(e0CCQs(uQs(qs)$s)$s(p-)#5/-/)&#A-)#8Cs*1HCs(Q#'C#Is(O(s(TFDDE#G7C%s(I'Cs(RO#(s(WFDDE#G1s(XFDDE&#:s(YFDDE#,s(ZFDDEs(Ps(O#l#+#s(Es(?l#,s(^s(]#l#-s(cs(b#j#.C#j#/C#-Ns*@##L%$s*7&L#$%#k###S%k##s(A#k#.C#k#/C#l#0,#s(9l#1s(ts(q#l#2s(~s(y#2s#(s#$>#/s,ys*.'Cs(/I>(s(oFDDE#G,s(pFDDEs(2s(e#l#+#s([s(Ul#,s(8s(s#l#-s(ys(x#j#.C##P7k##s(/#k#.C#l#0&#s(-l#2s(@s),#l#1s)(s)%#l#2s)2s)-#'Cs#,Os(((s(}FDDE#G,s(~FDDEs(,s(s#l#+#s(is(cl#,s(Fs)%#l#-s)+s)*#j#.C#&s#%s*wk##s((#k#.C#l#0&#s(&l#2s(Ns):#l#1s)6s)3#l#2s)@s);#<s*L1#*Cs*Ms)bA@##As)b%Bs)i&s)d#$%#+#m#(#Bs-?s*RCs*{S**Hs*|s#U%$#>%DJs*W#+#m#&##s#^s+1j#&H##s#Zs+3#s#Ws+40CCKs)hKs'|s#\s#Xs#Rs+5s+5s'{'Cs#KIs(J(s)CFDDE#G,s)DFDDEs(Ns)9#l#+#s)/s))l#,s(hs)G#l#-s)Ms)L#j#.C##s#Es+=k##s(J#k#.C#l#0&#s(Hl#2s(ps)\#l#1s)Xs)U#l#2s)bs)]#2321#*Cs*os(6#s#Bs#%#s##s+Fm#$#*Hs+<8#@?Es*qs*ts*rJ;#*s-^s*Ds+/s#|s*E#-S&s+].s-d#/s-e###s*?%$s*>&s*A#$%#+#j#&H##s*zs*6%s*{s*=&s*8#$%#+#%s+#s+:&s*<#$)#+#=+4Cs+(;CCCCCCMs*6s*6s*6Ms*,s+)s+)#s*Gs+@s*'0CCQs*7Qs*3s*Bs*Bs*2-)#5/-/)&#A-)#8Cs+uHCs)o#'C#Is)m(s)rFDDE#G7C%s)g'Cs)pO#(s)uFDDE#G1s)vFDDE&#:s)wFDDE#,s)xFDDEs)ns)m#l#+#s)cs)]l#,s)|s){#l#-s*%s*$#j#.C#j#/C#-Ns,(##L%$s+U&L#$%#k###S%k##s)_#k#.C#k#/C#l#0,#s)Wl#1s*6s*3#l#2s*@s*;#2s#(s#$>#/s.;s+H'Cs)MI>(s*1FDDE#G,s*2FDDEs)Ps*'#l#+#s)ys)sl#,s)Vs*5#l#-s*;s*:#j#.C##P7k##s)M#k#.C#l#0&#s)Kl#2s)^s*J#l#1s*Fs*C#l#2s*Ps*K#'Cs#,Os)F(s*?FDDE#G,s*@FDDEs)Js*5#l#+#s*+s*%l#,s)ds*C#l#-s*Is*H#j#.C#&s#%s,9k##s)F#k#.C#l#0&#s)Dl#2s)ls*X#l#1s*Ts*Q#l#2s*^s*Y#<s+f1#*Cs+gs+$A@##As+$%Bs++&s+&#$%#+#m#(#Bs.]s+lCs,=S6*Hs,>s#U%$#>%DJs+q#+#m#&##s#^s,Oj#&H##s#Zs,Q#s#Ws,R0CCKs+*Ks)>s#\s#Xs#Rs,Ss,Ss)='Cs#KIs)h(s*aFDDE#G,s*bFDDEs)ls*W#l#+#s*Ms*Gl#,s**s*e#l#-s*ks*j#j#.C##s#Es,[k##s)h#k#.C#l#0&#s)fl#2s*2s*z#l#1s*vs*s#l#2s+$s*{#2321#*Cs,-s)T#s#Bs#%#s##s,dm#$#*Hs,Z8#@?Es,/s,2s,0J;#*s.|s+cs,Ms#|s+d#-S&s,v.s/&#/s/'###s+]%$s+\&s+_#$%#+#j#&H##s,8s+T%s,9s+[&s+V#$%#+#%s,=s,X&s+Z#$)#+#=+4Cs,B;CCCCCCMs+Ts+Ts+TMs+Js,Cs,C#s+es,^s+E0CCQs+UQs+Qs+`s+`s+P-)#5/-/)&#A-)#8Cs-2HCs+1#'C#Is+/(s+4FDDE#G7C%s+)'Cs+2O#(s+7FDDE#G1s+8FDDE&#:s+9FDDE#,s+:FDDEs+0s+/#l#+#s+%s*{l#,s+>s+=#l#-s+Cs+B#j#.C#j#/C#-Ns-A##L%$s,s&L#$%#k###S%k##s*}#k#.C#k#/C#l#0,#s*ul#1s+Ts+Q#l#2s+^s+Y#2s#(s#$>#/s/Ys,b'Cs*kI>(s+OFDDE#G,s+PFDDEs*ns+E#l#+#s+;s+5l#,s*ts+S#l#-s+Ys+X#j#.C##P7k##s*k#k#.C#l#0&#s*il#2s*|s+h#l#1s+ds+a#l#2s+ns+i#'Cs#,Os*d(s+]FDDE#G,s+^FDDEs*hs+S#l#+#s+Is+Cl#,s+&s+a#l#-s+gs+f#j#.C#&s#%s-Wk##s*d#k#.C#l#0&#s*bl#2s+.s+v#l#1s+rs+o#l#2s+|s+w#<s-$1#*Cs-%s,BA@##As,B%Bs,I&s,D#$%#+#m#(#Bs/{s-*Cs-[S.*Hs-\s#U%$#>%DJs-/#+#m#&##s#^s-mj#&H##s#Zs-o#s#Ws-p0CCKs,HKs*\s#\s#Xs#Rs-qs-qs*['Cs#KIs+*(s,#FDDE#G,s,$FDDEs+.s+u#l#+#s+ks+el#,s+Hs,'#l#-s,-s,,#j#.C##s#Es-yk##s+*#k#.C#l#0&#s+(l#2s+Ps,<#l#1s,8s,5#l#2s,Bs,=#2321#*Cs-Gs*r#s#Bs#%#s##s.&m#$#*Hs-x8#@?Es-Is-Ls-JJ;#*s0>s-&s-ks#|s-'#-S&s.4.s0D#/s0E###s,{%$s,z&s,}#$%#+#j#&H##s-Rs,r%s-Ss,y&s,t#$%#+#%s-Ws-v&s,x#$)#+#=+4Cs-\;CCCCCCMs,rs,rs,rMs,hs-]s-]#s-'s-|s,c0CCQs,sQs,os,~s,~s,n-)#5/-/)&#A-)#8Cs.LHCs,O#'C#Is,M(s,RFDDE#G7C%s,G'Cs,PO#(s,UFDDE#G1s,VFDDE&#:s,WFDDE#,s,XFDDEs,Ns,M#l#+#s,Cs,=l#,s,\s,[#l#-s,as,`#j#.C#j#/C#-Ns.[##L%$s.5&L#$%#k###S%k##s,?#k#.C#k#/C#l#0,#s,7l#1s,rs,o#l#2s,|s,w#2s#(s#$>#/s0ws-|'Cs,-I>(s,mFDDE#G,s,nFDDEs,0s,c#l#+#s,Ys,Sl#,s,6s,q#l#-s,ws,v#j#.C##P7k##s,-#k#.C#l#0&#s,+l#2s,>s-*#l#1s-&s-##l#2s-0s-+#'Cs#,Os,&(s,{FDDE#G,s,|FDDEs,*s,q#l#+#s,gs,al#,s,Ds-##l#-s-)s-(#j#.C#&s#%s.uk##s,&#k#.C#l#0&#s,$l#2s,Ls-8#l#1s-4s-1#l#2s->s-9#<s.>1#*Cs.?s-`A@##As-`%Bs-g&s-b#$%#+#m#(#Bs1=s.DCs.yS2*Hs.zs#U%$#>%DJs.I#+#m#&##s#^s//j#&H##s#Zs/1#s#Ws/20CCKs-fKs+zs#\s#Xs#Rs/3s/3s+y'Cs#KIs,H(s-AFDDE#G,s-BFDDEs,Ls-7#l#+#s--s-'l#,s,fs-E#l#-s-Ks-J#j#.C##s#Es/;k##s,H#k#.C#l#0&#s,Fl#2s,ns-Z#l#1s-Vs-S#l#2s-`s-[#2321#*Cs.as,4#s#Bs#%#s##s/Dm#$#*Hs/:8#@?Es.cs.fs.dJ;#*s1\s.Es/-s#|s.F#-S&s0+.s1b#/s1c###s.=%$s.<&s.?#$%#+#j#&H##s.ls.4%s.ms.;&s.6#$%#+#%s.qs/8&s.:#$)#+#=+4Cs.v;CCCCCCMs.4s.4s.4Ms.*s.ws.w#s.Es/>s.%0CCQs.5Qs.1s.@s.@s.0-)#5/-/)&#A-)#8Cs0CHCs-m#'C#Is-k(s-pFDDE#G7C%s-e'Cs-nO#(s-sFDDE#G1s-tFDDE&#:s-uFDDE#,s-vFDDEs-ls-k#l#+#s-as-[l#,s-zs-y#l#-s.#s-~#j#.C#j#/C#-Ns0R##L%$s/S&L#$%#k###S%k##s-]#k#.C#k#/C#l#0,#s-Ul#1s.4s.1#l#2s.>s.9#2s#(s#$>#/s29s/:'Cs-KI>(s./FDDE#G,s.0FDDEs-Ns.%#l#+#s-ws-ql#,s-Ts.3#l#-s.9s.8#j#.C##P7k##s-K#k#.C#l#0&#s-Il#2s-\s.H#l#1s.Ds.A#l#2s.Ns.I#'Cs#,Os-D(s.=FDDE#G,s.>FDDEs-Hs.3#l#+#s.)s.#l#,s-bs.A#l#-s.Gs.F#j#.C#&s#%s07k##s-D#k#.C#l#0&#s-Bl#2s-js.V#l#1s.Rs.O#l#2s.\s.W#<s/X1#*Cs/Ys.~A@##As.~%Bs/)&s/$#$%#+#m#(#Bs2[s/^Cs0;S3*Hs0<s#U%$#>%DJs/c#+#m#&##s#^s0Mj#&H##s#Zs0O#s#Ws0P0CCKs/(Ks-<s#\s#Xs#Rs0Qs0Qs-;'Cs#KIs-f(s._FDDE#G,s.`FDDEs-js.U#l#+#s.Ks.El#,s.(s.c#l#-s.is.h#j#.C##s#Es0Yk##s-f#k#.C#l#0&#s-dl#2s.0s.x#l#1s.ts.q#l#2s.~s.y#2321#*Cs/{s-R#s#Bs#%#s##s0bm#$#*Hs0X8#@?Es/}s0$s/~J;#*s2zs/ds0Ks#|s/e#-S&s1N.s3$#/s3%###s/[%$s/Z&s/]#$%#+#j#&H##s0*s/R%s0+s/Y&s/T#$%#+#%s0/s0V&s/X#$)#+#=+4Cs04;CCCCCCMs/Rs/Rs/RMs/Hs05s05#s/cs0\s/C0CCQs/SQs/Os/^s/^s/N-)#5/-/)&#A-)#8Cs1fHCs//#'C#Is/-(s/2FDDE#G7C%s/''Cs/0O#(s/5FDDE#G1s/6FDDE&#:s/7FDDE#,s/8FDDEs/.s/-#l#+#s/#s.yl#,s/<s/;#l#-s/As/@#j#.C#j#/C#-Ns1u##L%$s0q&L#$%#k###S%k##s.{#k#.C#k#/C#l#0,#s.sl#1s/Rs/O#l#2s/\s/W#2s#(s#$>#/s3Ws0T'Cs.iI>(s/MFDDE#G,s/NFDDEs.ls/C#l#+#s/9s/3l#,s.rs/Q#l#-s/Ws/V#j#.C##P7k##s.i#k#.C#l#0&#s.gl#2s.zs/f#l#1s/bs/_#l#2s/ls/g#'Cs#,Os.b(s/[FDDE#G,s/\FDDEs.fs/Q#l#+#s/Gs/Al#,s/$s/_#l#-s/es/d#j#.C#&s#%s1Uk##s.b#k#.C#l#0&#s.`l#2s/,s/t#l#1s/ps/m#l#2s/zs/u#<s0r1#*Cs0ss0@A@##As0@%Bs0G&s0B#$%#+#m#(#Bs3ys0wCs1Ys0y*Hs1Zs#U%$#>%DJs0}#+#m#&##s#^s1kj#&H##s#Zs1m#s#Ws1n0CCKs0FKs.Zs#\s#Xs#Rs1os1os.Y'Cs#KIs/((s/}FDDE#G,s/~FDDEs/,s/s#l#+#s/is/cl#,s/Fs0%#l#-s0+s0*#j#.C##s#Es1wk##s/(#k#.C#l#0&#s/&l#2s/Ns0:#l#1s06s03#l#2s0@s0;#2321#*Cs19s.p#s#Bs#%#s##s2$m#$#*Hs1v8#@?Es1:s1>s1<J;#*s4<s1's1is#|s1(#-S&s19.s4B#/s4C###s0y%$s0x&s0{#$%#+#j#&H##s1As0p%s1Bs0w&s0r#$%#+#%s1Fs1t&s0v#$)#+#=+4Cs1K;CCCCCCMs0ps0ps0pMs0fs1Ls1L#s1%s1zs0a0CCQs0qQs0ms0|s0|s0l-)#5/-/)&#A-)#8Cs1QHCs0M#'C#Is0K(s0PFDDE#G7C%s0E'Cs0NO#(s0SFDDE#G1s0TFDDE&#:s0UFDDE#,s0VFDDEs0Ls0K#l#+#s0As0;l#,s0Zs0Y#l#-s0_s0^#j#.C#j#/C#-Ns1`##L%$s23&L#$%#k###S%k##s0=#k#.C#k#/C#l#0,#s05l#1s0ps0m#l#2s0zs0u#2s#(s#$>#/s4us1k'Cs0+I>(s0kFDDE#G,s0lFDDEs0.s0a#l#+#s0Ws0Ql#,s04s0o#l#-s0us0t#j#.C##P7k##s0+#k#.C#l#0&#s0)l#2s0<s1(#l#1s1$s0}#l#2s1.s1)#'Cs#,Os0$(s0yFDDE#G,s0zFDDEs0(s0o#l#+#s0es0_l#,s0Bs0}#l#-s1's1&#j#.C#&s#%s2sk##s0$#k#.C#l#0&#s/~l#2s0Js16#l#1s12s1/#l#2s1<s17#<s2-1#*Cs2.s1^A@##As1^%Bs1e&s1`#$%#+#m#(#Bs5;s22Cs2ws24*Hs2xs#U%$#>%DJs28#+#m#&##s#^s3-j#&H##s#Zs3/#s#Ws300CCKs1dKs/xs#\s#Xs#Rs31s31s/w'Cs#KIs0F(s1?FDDE#G,s1@FDDEs0Js15#l#+#s1+s1%l#,s0ds1C#l#-s1Is1H#j#.C##s#Es39k##s0F#k#.C#l#0&#s0Dl#2s0ls1X#l#1s1Ts1Q#l#2s1^s1Y#2321#*Cs2Ps02#s#Bs#%#s##s3Bm#$#*Hs388#@?Es2Qs2Ws2SJ;#*s5Zs2Fs3+s#|s2G#-S&s2M.s5`#/s5a###s2;%$s2:&s2=#$%#+#j#&H##s2Us22%s2Vs29&s24#$%#+#%s2Zs36&s28#$)#+#=+4Cs2_;CCCCCCMs22s22s22Ms2(s2`s2`#s2Cs3<s2#0CCQs23Qs2/s2>s2>s2.-)#5/-/)&#A-)#8Cs2eHCs1k#'C#Is1i(s1nFDDE#G7C%s1c'Cs1lO#(s1qFDDE#G1s1rFDDE&#:s1sFDDE#,s1tFDDEs1js1i#l#+#s1_s1Yl#,s1xs1w#l#-s1}s1|#j#.C#j#/C#-Ns2t##L%$s3Q&L#$%#k###S%k##s1[#k#.C#k#/C#l#0,#s1Sl#1s22s2/#l#2s2<s27#2s#(s#$>#/s67s3#'Cs1II>(s2-FDDE#G,s2.FDDEs1Ls2##l#+#s1us1ol#,s1Rs21#l#-s27s26#j#.C##P7k##s1I#k#.C#l#0&#s1Gl#2s1Zs2F#l#1s2Bs2?#l#2s2Ls2G#'Cs#,Os1B(s2;FDDE#G,s2<FDDEs1Fs21#l#+#s2's1}l#,s1`s2?#l#-s2Es2D#j#.C#&s#%s45k##s1B#k#.C#l#0&#s1@l#2s1hs2T#l#1s2Ps2M#l#2s2Zs2U#<s3A1#*Cs3Bs2|A@##As2|%Bs3'&s2~#$%#+#m#(#Bs6Ys3GCs49S,*Hs4:s#U%$#>%DJs3L#+#m#&##s#^s4Kj#&H##s#Zs4M#s#Ws4N0CCKs3&Ks1:s#\s#Xs#Rs4Os4Os19'Cs#KIs1d(s2]FDDE#G,s2^FDDEs1hs2S#l#+#s2Is2Cl#,s2&s2a#l#-s2gs2f#j#.C##s#Es4Wk##s1d#k#.C#l#0&#s1bl#2s2.s2v#l#1s2rs2o#l#2s2|s2w#2321#*Cs3ds1P#s#Bs#%#s##s4`m#$#*Hs4V8#@?Es3fs3ns3gJ;#*s6xs3es4Is#|s3f#3s3ps3is3h)s4S9#-S'#.s7%#6s4^S-@($#J-S&'.s7)#/s7*###s3`%$s3_&s3b#$%#+#j#&H##/s3W%0s3^&s3Y#$%#+#%4s4[&s3]#$)#+#=+4C9;CCCCCCMs3Ws3Ws3WMs3M::#s3hs4as3H0CCQs3XQs3Ts3cs3cs3S-)#5/-/)&#A-)#8C?HCs34#'C#Is32(s37FDDE#G7C%s3,'Cs35O#(s3:FDDE#G1s3;FDDE&#:s3<FDDE#,s3=FDDEs33s32#l#+#s3(s2~l#,s3As3@#l#-s3Fs3E#j#.C#j#/C#-Ns#.##L%$s4v&L#$%#k###S%k##s3$#k#.C#k#/C#l#0,#s2xl#1s3Ws3T#l#2s3as3\#2s#(s#$>#/s7\s#9'Cs2nI>(s3RFDDE#G,s3SFDDEs2qs3H#l#+#s3>s38l#,s2ws3V#l#-s3\s3[#j#.C##P7k##s2n#k#.C#l#0&#s2ll#2s3#s3k#l#1s3gs3d#l#2s3qs3l#'Cs#,Os2g(s3`FDDE#G,s3aFDDEs2ks3V#l#+#s3Ls3Fl#,s3)s3d#l#-s3js3i#j#.C#&s#%s5Zk##s2g#k#.C#l#0&#s2el#2s31s3y#l#1s3us3r#l#2s4#s3z#<s#W1#*Cs#Xs4EA@##As4E%Bs4L&s4G#$%#+#m#(#Bs7~s#]Cs5^S-*Hs5_s#U%$#>%DJs#b#+#m#&##s#^s5pj#&H##s#Zs5r#s#Ws5s0CCKs4KKs2_s#\s#Xs#Rs5ts5ts2^'Cs#KIs3-(s4&FDDE#G,s4'FDDEs31s3x#l#+#s3ns3hl#,s3Ks4*#l#-s40s4/#j#.C##s#Es5|k##s3-#k#.C#l#0&#s3+l#2s3Ss4?#l#1s4;s48#l#2s4Es4@#2321#*Cs#zs2u#s#Bs#%#s##s6)m#$#*Hs5{8#@?Es#|s$%s#}J;#*s8As5/s5ns$'s#|#Js8Bs5ls5$m#$#'Cs48Os),(s4=FDDE#G1s4>FDDEs'j#:s4?FDDE#,s4@FDDEs46s45#l#+#s4+s4%l#,s4Ds4C#l#-s4Is4H#j#.C#j#/C#&Ls)($s'f#k###S%k##s4$#k#.C#k#/C#l#0)#s3xl#1s4Ws4T#l#2s4as4\#VS<J#*s8Xs6&s6)7s6'#%S's6^.s8^#/s8_###s59%$s58&s5;#$%#+#j#&H##s6Ks50%s6Ls57&s52#$%#+#%s6Ps64&s56#$)#+#=+4Cs6U;CCCCCCMs50s50s50Ms5&s6Vs6V#s5As6:s4}0CCQs51Qs5-s5<s5<s5,-)#5/-/)&#A-)#7Cs4hs08'C#Is4f(s4kFDDE#G7Cs4ks-['Cs4iO#(s4nFDDE#G1s4oFDDE&#:s4pFDDE#7C*s4e'Cs4nO#(s4sFDDE#G1s4tFDDE+#:s4uFDDE#,s4vFDDE(s4k#l#+#s4as4[l#,s4zs4y#l#-s5#s4~#j#.C#j#/C#%S#s7-##N%S#s7(&N#$%#k###S%%Ns73##L%$s6Y&L#$%#k###S%k##)#k#.C#k#/C#Ps4\S:SCl#03$#l#1s5;s58#l#2s5Es5@#2s#3s#/s#)#/s9@s7$8Cs8;'C#Is55(s57FDDE#G'Cs4UIs#-(s59FDDE#G,s5:FDDE%s5/#l#+#s5%s4{l#,s4^s5=#l#-s5Cs5B#j#.C##s8ES##P<k##$#k#.C#MS?S/l#0($#l#2s4hs5T#l#1s5Ps5M#l#2s5Zs5U#8Cs887Cs5H#8Cs8@'C$I#(s5LFDDE#G'Cs#BOs4U(s5NFDDE#G,s5OFDDE%s5D#l#+#s5:s54l#,s4ss5R#l#-s5Xs5W#j#.C#%S#s8D##s8K&s#2s7Jk##$#k#.C#MS?S1l#0)$#l#2s4~s5j#l#1s5fs5c#l#2s5ps5k#<s7O9#*Cs7Ps66s#.s#-##s#.s66%s#/s6=&s68#$%#+#m#(#Bs9os7LCs7Os7N*Hs7Ps#m%$#>%DJs7Z#+#m#&##s#vs7aj#&H##s#rs7c#s#os7d0CCKs6<Ks4Ps#ts#ps#js7es7es4O'Cs#_Is4z(s5sFDDE#G,s5tFDDEs#*s5i#l#+#s5_s5Yl#,s5<s5w#l#-s5}s5|#j#.C##s#Ss7mk##s#'#k#.C#l#0&#s#%l#2s5Ds60#l#1s6,s6)#l#2s66s61#2321#*Cs7rs4f#s#Os#%#s##s7vm#$#*Hs7l8#@?Es7kS&s7uJ;#*s:2s7]s7_s$8s7^#%S's7g.s:8#/s:9###s6o%$s6n&s6q#$%#+#j#&H##s7os6f%s7ps6m&s6h#$%#+#%s7ts7j&s6l#$)#+#=+4Cs7y;CCCCCCMs6fs6fs6fMs6\s7zs7z#s6ws7ps6W0CCQs6gQs6cs6rs6rs6b-)#5/-/)&#A-)#7Cs6Bs0P'C#Is6@(s6EFDDE#G7C%s6:'Cs6CO#(s6HFDDE#G1s6IFDDE&#:s6JFDDE#,s6KFDDEs$9s6@#l#+#s66s60l#,s6Os6N#l#-s6Ts6S#j#.C#j#/C#%Ns81##L%$s8(&L#$%#k###S%k##s$4#k#.C#k#/C#l#0,#s$-l#1s6es6b#l#2s6os6j#2s#'s##=#/s:js8<'Cs5|I>(s6`FDDE#G,s6aFDDEs$,s6V#l#+#s6Ls6Fl#,s6)s6d#l#-s6js6i#j#.C##P7k##s$*#k#.C#l#0&#s$(l#2s61s6y#l#1s6us6r#l#2s7#s6z#'Cs#,Os5u(s6nFDDE#G,s6oFDDEs$%s6d#l#+#s6Zs6Tl#,s67s6r#l#-s6xs6w#j#.C#&s#%s8hk##s#~#k#.C#l#0&#s#|l#2s6?s7+#l#1s7's7$#l#2s71s7,#<s8Z1#*Cs8[s7SA@##As7S%Bs7Z&s7U#$%#+#m#(#Bs;0s8`Cs8lS/*Hs8ms#T%$#>%DJs8e#+#m#&##s#]s8~j#&H##s#Ys9$#s#Vs9%0CCKs7YKs5ms#[s#Ws#Qs9&s9&s5l'Cs#KIs6;(s74FDDE#G,s75FDDEs$Gs7*#l#+#s6|s6vl#,s6Ys78#l#-s7>s7=#j#.C##s#Es9.k##s$D#k#.C#l#0&#s$Bl#2s6as7M#l#1s7Is7F#l#2s7Ss7N#2321#*Cs8}s6'#s#Bs#%#s##s97m#$#*Hs9-8#@?Es9#s9+s9$J;#*s;Os8{s8|s#{s9##3s9-s9&s9%%S>s9J.s;V#@%#s9(J%S's9M.s;Y#/s;Z###s84%$s83&s86#$%#+#j#&H##.s8+%/s82&s8-#$%#+#%3s9/&s81#$)#+#=+4C8;CCCCCCMs8+s8+s8+Ms7}99#s8<s95s7x0CCQs8,Qs8(s87s87s8'-)#5/-/)&#A-)#7Cs7cs/5'C#Is7a(s7fFDDE#G7Cs7fs-v'Cs7dO#(s7iFDDE#G1s7jFDDE&#:s7kFDDE#7C*s7`'Cs7iO#(s7nFDDE#G1s7oFDDE+#:s7pFDDE#,s7qFDDE(s7f#l#+#s7\s7Vl#,s7us7t#l#-s7zs7y#j#.C#j#/C#%S#s9x##N%S#s9v&N#$%#k###S%%Ns9~##L%$s9T&L#$%#k###S%k##)#k#.C#k#/C#Ps7WS:Jl#03$#l#1s86s83#l#2s8@s8;#2s#3s#/s#)#/s<;s#C'Cs7MIs#*(s81FDDE#G,s82FDDEs%Ys8'#l#+#s7ys7sl#,s7Vs85#l#-s8;s8:#j#.C##P8k##s%W#k#.C#l#0&#s%Ul#2s7^s8J#l#1s8Fs8C#l#2s8Ps8K#'Cs#8Os7F(s8?FDDE#G,s8@FDDEs%Rs85#l#+#s8+s8%l#,s7ds8C#l#-s8Is8H#j#.C#&s#&s:9k##s%O#k#.C#l#0&#s%Ml#2s7ls8X#l#1s8Ts8Q#l#2s8^s8Y#<s#a1#*Cs#bs9$A@##As9$%Bs9+&s9&#$%#+#m#(#*Hs:<s#^#s$/s$.DJs#is$-+#m#%##s#fs:Lj#&H##s#bs:N#s#_s:O0CCKs9'Ks7;s#ds#`s#Zs:Ps:Ps7:'Cs#OIs7e(s8^FDDE#G,s8_FDDEs%qs8T#l#+#s8Js8Dl#,s8's8b#l#-s8hs8g#j#.C##s#Cs:Xk##s%n#k#.C#l#0&#s%ll#2s8/s8w#l#1s8ss8p#l#2s8}s8x#2321#*Cs$%s7Q#s#?B#@s:am#$#*Hs:W8#s$Js$IEs:Ms$*s$(J;#*s<ys:Ms:Js$,s$(#YSBS&S>S/S1JJs<{#s9]m#%#l#3s:ms:g#j#4s:o#j#5s:y#j#6s;*#j#$s=(#%S*s;+.s=+#SS)S56s:e#3S(%#%S*s:_.s=0#6s:iS)3&$#%S*s;(.s=4#3%#&NRS$S6S.S2S3S7S0S,S-S/S1S8S9S4-S$s:\.s=8#3R#s:E-S$s:Z.s=;#3%#s:D-S$s:X.s=>#3%#s:C-S$s;A.s=A#3%#s:B-S$s:s.s=D#6s:}S73&$#-S$s;A.s=H#6s;%S03&$#-S$s;@.s=L#3%#s:8-S$s;?.s=O#3%#s),-S$s;w.s=R#3%#s;$-S$s<#.s=U#.s=VS16s;3#3'%#-S$s:Q.s=Z#.s=[S86s;8#3'%#-S$s:L.s=_#6s;<S93&$#-S$s)A.s=c#6s;@S43&$#USoRFs:sRs#1?RRs#1$#Fs:qs#2s#0?Rs#3s#0$#Fs:os#1s#/?Rs#2s#/$#Fs:ms#0s#.?Rs#1s#.$#Fs#,s#/s#-?Rs#0s#,$#Fs#*s#-s#+?Rs#.s#*$#Fs:^s#+s#)?Rs#,s#)$#Fs)Qs#*s#(?Rs#+s#($#Fs;Hs#)s#'?Rs#*s#'$#Fs#$s#(s#&?Rs#)s#$$#FAs#%s##?Rs#&A$#F?B@?Rs##?$#F=@>?RA=$#ORs#Mm#$#?Rs#OS(#S#Fs#YS(s#[?RS(s#Y$#Fs#Ws#Zs#X?Rs#[s#W$#Fs#Ys#Xs#V?Rs#Ys#V$#ORs<5m#$#USPs>-USL#LS+s#^s#es;jSS4S)6s;l#Q'#J'S##j#%(#LS+s#hs#ks;p%S#s;^##s;~j#'C#MS=S5l#0s&ss&p#l#2s9Us:A#l#1s:=s::#l#2s:Gs:B#/s>As#tMS$S;l#0s'Ws'S#l#0s'Cs'>*l#2s9\s:H#l#1s:Ds:A#l#2s:Ns:I#<s#|'#*Cs#}0+*#%+s;o##s<3m#%#TS+S(s$$s$##%S$s<O#P#&$s<8$$#%&s:~##s<;%S$s<(#P#&$s<>$$#%&s;/##s<A#*(#%/I$#$&#$)#$.#$1#j#&H##Ps$:&s$;s<K$$#%s$=s;5##s<N#Ps$:&s$;s<P$$#%s$=s;:##s<S#)s$?#%s$EI$#$&#$)#$-#$0#%s$Ks<<##s<\%s$Hs<>##s<^#&s$J#%s$PI$#$&#$4#$*#$;#4SE<WSF==#4Cs$X;CCCCCCMs;@s;@s;@Ms;6s$Ys$Y#s;Qs<Js;10CCKs;AKs9U?1#s<js<js9T4SE<WSF==#4Cs$X;CCCCCCMs;Es;Es;EMs;;s$Ys$Y#s;Vs<Os;60CCKs;FKs9Z?4#s<os<os9Y0CCKs;GKs9[s#%7)s$[s$[%0CCKs;HKs9\A6%s$as$a+ZSG@?54$#5B?74&#5s#%?s#%4*#5s#)?;4-#5s#,?s#,41#1s;'FDDEs(Ls(71s;(FDDEs'&s&t'Cs(rIs'D(s;*FDDE#G'Cs'CIs(|(s;,FDDE#G[SHs;-FDDE%#1s;.FDDEs&X#1s;/FDDE)#1s;0FDDEs'w#1s;1FDDE,#,s;2FDDEs(Ys;'#,s;3FDDEs(Es;(#l#+#s:zs:tl#,s:Ws;6#l#-s;<s;;#j#.C##s>>N%Ls=F#P#&$s=/$$#%&s<n##s=2%Ls<{#P#&$s=5$$#%&s<t##s=8#*(#%/I$#$&#$)#$.#$1#k##6#k##s(V#k#.C#PS=S5S)l#0;$#l#2s:ts;`#l#1s;\s;Y#l#2s;fs;a#2s#Ls#As#0#m##s#MBs?_s%3Cs=?S)*Hs=@s#a%$#[SIS+s%6s%9s%8s%=s=A#*s$7s$0s$1s#ws$6#LS+s%4s%>s=C%S$s=]#P#&$s=R$$#%&s<C##s=U#s#z(#%s$#I$#$&#$)#$s#~#$s$%#j#&H##Ps%E&s%Fs=_$$#%s%Hs<I##s=b#s#ts%J#%s%TI$#$&#$)#$s#x#$s#{#%s%Qs=K##s=k#s#os%S#%s%]I$#$&#$2#$s#s#$s$(#4SE5WSF66#4Cs%\;CCCCCCMs<Ms<Ms<MMs<Cs%]s%]#s<^s=Ws<>0CCKs<NKs:b8/#s=ws=ws:a0CCKs<OKs:cs$-s#{s#ms%_s%_%0CCKs<PKs:d:1%s%is%is#oZSG980/$#5;82/&#5>8>/*#5s$18s$#/s#q#5s$48s$4/s#u#1s</FDDEs&\s&N'Cs)yIs'*(s<1FDDE#G'Cs'$Is*'(s<3FDDE#G[SHs<4FDDE%#1s<5FDDEs&5#1s<6FDDE)#1s<7FDDEs(~#1s<8FDDEs#o#,s<9FDDEs)`s<.#,s<:FDDEs)Ls</#l#+#s<%s;{l#,s;^s<=#l#-s<Cs<B#j#.C#%Ls>@#P#&$s>5$$#%&s=t##s>8#s#f(#%s#kI$#$&#$)#$s#j#$s#m#k##s#r#k##s)V#k#.C#l#03#s#^l#2s;ss<_#l#1s<[s<X#l#2s<es<`#2s#<s#3s#'#m##s#=*Hs>=s#J#s#]s#\[SIS+s&3s&2s&1s&:s>>#*s%4s%3s%.s#[s#Z#LS+s>ks&;s>@Qs%7s&:Js%7$#m#&#LS+s&8s&:s>DQs%;s%cJs%;S##j#%s%<#l#0s()s(&s%2l#2s<(s<p#l#1s<ls<i#l#2s<vs<q#/s@ps&Bl#0s(^s([s%1l#0s(Qs(Ns%8l#2s<.s<v#l#1s<rs<o#l#2s<|s<w#<s&I'#*Cs&Js%>*)#%*s>A##s>am#%#TS+s&Os&MS)#LS+s&Is&Ns>X%s%+s=M##s>f#$s#u#s#rs%.I$#$s#s#$s#v#$(#$s%0#j#&H##s${s&V#s#ms&[I$#$s#n#$s#q#$s%##$s%&##s$ws&]#s#ks&bI$#$s#l#$s#x#$s${#$s%-#0CCKs=TKs;hs%-s$~s$ms&ds&ds#f0CCKs=UKs;is#{s#rs#fs&is&is$oZSG21+*$#5s#|1s#s*s#g#5s$#1s$#*s#k#5s%11s%&*s$q#5s%41s%4*s$u#'Cs)LIs(.(s=5FDDE#G'Cs((Is)Q(s=7FDDE#G[SHs=8FDDE%#1s=9FDDEs'9#1s=:FDDEs#i#1s=;FDDEs(e#1s=<FDDEs$r#,s==FDDEs*ds=2#,s=>FDDEs*Ps=3#l#+#s=)s=#l#,s<bs=A#l#-s=Gs=F#j#.C##s$^s#b#s#_s$cI$#$s#`#$s#c#$s$b#$s$e#k##s$p#k##s*T#k#.C#l#0-#s$\l#2s<qs=]#l#1s=Ys=V#l#2s=cs=^#2s#.s#'@#m##s#/*Hs?;s#7#s$[s$Z[SIS+s'1s'0s'/s'3s?<#*s&2s#Ws#Ts#Ds#C#LS+s?is'4s?>Qs&5s'4Js&5$#m#&#l#0s'Us'Rs&,l#2s<~s=j#l#1s=fs=c#l#2s=ps=k#/sAjs'8l#0s(+s((s&+l#0s'zs'ws&2l#2s=(s=p#l#1s=ls=i#l#2s=vs=q#<s'?'#*Cs'@s&8*)#%*s?;##s?[m#%#TS+s'Es'CS)#LS+s?}s'Ds?RJs&H#6m#%#_SpRS$S*S)S5s@$s'Rs&Ls#p6#j#7s@&#j#8s@)#V#NS#j##s@6#j##s@?#YSqs@@s@>s@:#S#j#9s@U#j#:s@X#j#;s@k#j#<sAI#j#=sA[#j#>sB(#j#?sB)#j#@sB*#j#AsB+#j#&C#j#BC#j#CsB.#j#DsB/#j#EsB0#j#FsB1#j#GsB2#j#HsB3#j#IsB4#j#JsB5#j#KsB6#j#LC#j#MC#j#)sB5#j#NsB6##"). Qed.

Lemma pc_1091c4 : v_addi (0x1091c0 : word) 4 = (0x1091c4 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Scheme kc__5 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioDefs.sw_file Sort Prop.
Scheme kc__6 := Elimination for Corelib.Init.Datatypes.list Sort Prop.

Theorem as_stdio_write :
  forall regs mem L S Zr msF mo (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x123ef0 <= f)%Z -> (f + 232 <= 0x1240d0)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* LPS 75d69e00: the reader premise, next to the fd_lookup one. *)
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (0x109138 : word) mem (seg_rom RSEGS) ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem' msF' mo',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst regs' ret mem' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros regs mem L S Zr msF mo su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr OK RS WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  assert (LZ0 : LZ L S Zr msF mo msF mo).
  { split; [exact OK|]. split; [apply same_but_materialized_refl | apply hid_same_refl]. }
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x681830) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     forall msF' mo', lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K).
  { intros. eapply HK. all: try eassumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 L S Zr msF mo K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as FIN.
  pose proof (loop1 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 L S Zr msF mo K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 L S Zr msF mo K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK | exact RS | exact RUN1 |]. clear RUN1.
    intros msFa moa OKa SBa HSa RSa. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZ0 OKa SBa HSa) as LZa.
    lazymatch type of RSa with _ = mkst _ _ ?M _ =>
      replace M with mem1 in RSa by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rz_writev1_zero_lazy RSEGS L S Zr msFa regs1 (0x1091c0 : word) mem1 moa W_1091c0 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_1091c0 | exact E_1091c0 | exact OKa | exact RSa | exact (LZ_fd fd L S Zr msF mo Hfd _ _ LZa) | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      intros msFb mob OKb SBb RSb HSb. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZa OKb SBb HSb) as LZb.
      rewrite pc_1091c4 in RSb.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZb OKc SBc HSc) as LZc.
      apply (FIN regs2 mem1 msFc moc); [| exact LM1 | exact LZc | exact RSc].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (rz_writev1_wall_lazy RSEGS L S Zr msFa regs1 (0x1091c0 : word) mem1 moa W_1091c0 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_1091c0 | exact E_1091c0 | exact OKa | exact RSa | exact (LZ_fd fd L S Zr msF mo Hfd _ _ LZa) | exact (LZ_rdr L S Zr msF mo Hrdr _ _ LZa) | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * unfold TASK_SIZE. u_norm. lia.
      * unfold TASK_SIZE. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k msFb mob K1 K2 OKb SBb RSb HSb. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZa OKb SBb HSb) as LZb.
        rewrite pc_1091c4 in RSb.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZb OKc SBc HSc) as LZc.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply (FIN regs2 mem1 msFc moc); [| exact LM1 | exact LZc | exact RSc].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZb OKc SBc HSc) as LZc.
           apply (L1 (length (x0 :: extra')) regs2 mem1 msFc moc k s (x0 :: extra')); try (first [clear - K1 K2 NK LENE DISJE SNW LENP M30; lia | lia]).
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact LZc.
           ++ exact RSc.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK | exact RS | exact RUN1 |]. clear RUN1.
    intros msFa moa OKa SBa HSa RSa. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZ0 OKa SBa HSa) as LZa. fold mem1 in RSa.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (rz_writev2_wall_lazy RSEGS L S Zr msFa regs1 (0x1091c0 : word) mem1 moa W_1091c0 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_1091c0 | exact E_1091c0 | exact OKa | exact RSa | exact (LZ_fd fd L S Zr msF mo Hfd _ _ LZa) | exact (LZ_rdr L S Zr msF mo Hrdr _ _ LZa) | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k msFb mob K1 K2 OKb SBb RSb HSb. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZa OKb SBb HSb) as LZb.
      rewrite pc_1091c4 in RSb. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZb OKc SBc HSc) as LZc.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply (FIN regs2 mem1 msFc moc); [| exact LM1 | exact LZc | exact RSc].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact (proj1 LZb) | exact RSb | exact RUN2 |]. clear RUN2.
        intros msFc moc OKc SBc HSc RSc. pose proof (LZ_next L S Zr msF mo _ _ _ _ LZb OKc SBc HSc) as LZc.
        apply (L2 (length pending + length extra)%nat regs2 mem1 msFc moc k (Z_to_bv 64 wb) pending s extra); try (first [clear - WBP NEQ K1 K2 NK LENE DISJE SNW M30; lia | lia]).
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact LZc.
        -- exact RSc.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

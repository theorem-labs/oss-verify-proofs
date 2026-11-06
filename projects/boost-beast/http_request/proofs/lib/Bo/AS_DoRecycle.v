(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit AllocBudget.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsDepotInv AW_DepotFrame AllocWalkKit SecLazy AG_Malloc AG_Malloc2.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AG_MallocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AG_RepQ AG_RepQFacts AW_MergeBatches AW_Recycle AW_DoRecycle AG_WriteSet SecLazy2 AG_RecycleDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac olia := Zify.zify; xlia zchecker.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wkeep (P : Z -> Prop) (m m' : mem) : Prop :=
  forall x : word, P (bv_unsigned x) -> wview bsegs m x <> None -> wview bsegs m' x <> None.

Lemma wkeep_of_wmono : forall P m m', wmono bsegs m m' -> wkeep P m m'.
Proof. intros P m m' WM x _ Hx. exact (WM x Hx). Qed.
Lemma wkeep_refl : forall P m, wkeep P m m.
Proof. intros P m x _ Hx. exact Hx. Qed.
Lemma wkeep_trans : forall P m1 m2 m3, wkeep P m1 m2 -> wkeep P m2 m3 -> wkeep P m1 m3.
Proof. intros P m1 m2 m3 A B x Hp Hx. exact (B x Hp (A x Hp Hx)). Qed.
Lemma wkeep_weaken : forall (P P' : Z -> Prop) m m', (forall a, P' a -> P a) -> wkeep P m m' -> wkeep P' m m'.
Proof. intros P P' m m' H A x Hp Hx. exact (A x (H _ Hp) Hx). Qed.
Lemma agree_on_weaken : forall (P P' : Z -> Prop) m m', (forall a, P' a -> P a) -> agree_on P m m' -> agree_on P' m m'.
Proof. intros P P' m m' H A x Hp Hr. exact (A x (H _ Hp) Hr). Qed.
Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m x _ _. reflexivity. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 A B x Hp Hr. rewrite (B x Hp Hr). exact (A x Hp Hr). Qed.

Section TransportPt2.
  Variable P : Z -> Prop.
  Variables m m' : mem.
  Hypothesis AG : agree_on P m m'.
  Let WK : wkeep P m m'.
  Proof.
    intros x Hp Hx. pose proof (bv_unsigned_in_range _ x) as R; change (bv_modulus 64) with (2^64) in R.
    pose proof (AG (bv_unsigned x) Hp R) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E.
    rewrite (wview_pointwise m m' x E). exact Hx.
  Qed.

  Lemma bytes_at_transport_pt2 : forall A bs,
    bytes_at bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at bsegs m' A bs.
  Proof.
    intros A bs (Ha & Hl & H) HR. split; [olia|]. split; [olia|].
    intros i Hi. unfold mrd. rewrite AG; [apply H; exact Hi| apply HR; olia| olia].
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
  Lemma stk_transport_pt2 : forall lo hi,
    stk bsegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk bsegs m' lo hi.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(m); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mrd); constr:(@Corelib.Init.Datatypes.Some); constr:(P); constr:(m'); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@kc__2); constr:(WK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(AG); constr:(@kc__2 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))|] [|@b; @a; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat4; @__sat3; @z; @__x2; @__x3; @x; @o; @Hb; @H0; @Hw; @a0; @HR; @H; @H2; @H1; @hi; @lo|] "#'+#>$'#A###j#C#$#k#i#G#D#Z#%#-#&#q#.#o#'#*#)#c#L#(#+#,#1$,#J#R#P#U#]#_#n#t#u#|$($$$)$##<#=#0#{#I#Q#/#\#^#a#`#b#d#f#h#r#v#w#s#2#x#}$*$-#4#8#~#z$/$0$.#y#F#H#O#M#W#T#V#m#l#S#N#K#g$&$'$%#B#X#Y#e#p$+#[#E;#k%#l%#m&#n%#o&#p$#q%#r'#s*#t&#u$#v$#w+#x%#y$#z&#{'#|%#}$#~%$#%$$*$%'$&(3FKGD#JM.S'US-#.$.#.#.#.#US-#VS?)##G##OD&DM$$#US.,US@#US/#(G,FK#US0&%&$#-#(M'FK#4+D%+$#j#$-#).#$)#k##2#k#%C#$7#$B##S#D&DO$$#5Gk##$#k#%C#3FLS#Ok##$#j##+##Ms##k##*1k#%C#$%##JS##S#s#(#S%D&DS($$#k###9k#%C#$(##S(s#/#S$D&DS%$$#k###@k#%C#$(##S)D&DS$$$#k###>k#%C#3FLS)S$k##$#j##*#k##(s#+k#%C##S$s#@#ND&DS*$$#k###s#1k#%C##QD&DN$$#k###s#.k#%C##JQ#Ns#L#SAD&DQ$$#,FLs#H%s#J#s#G-#'FLs#F%s#M#s#Ej#$s#O#)s#P#$'#k##+#k#%C#$0#VSBs#bs#\&Js#c#Js#^&Js#^k##$#k##&##Js#hWSCs#is#cGj##S1#j#&%##Js#ek##S1#k#&(#VSDJs#oVS2SE#m##0UG#USFS&USGS&6CGUSHCUSICVS3CJ7CS'*C$R#+&IEEH#PUS0E/(IEEH$#$VSJ)HVS2S4S5VSKDM%S4#S5m$%#WSLCJGXSMDM$#l#'*)#l#(32#l#)65#j#*C##JD#JGk##$#k#*C#VDSNNl#+($#l#,?s#+#l#-s#'s#$#l#,s#1s#,#VS3Cs$6US.s$2WSOC$#*C>R#+AIEEH#P/BIEEH#=#l#'#<6l#(s#&s#%#l#)s#)s#(#j#*C##Ds$9k###s$9k#*C#VDS+S%l#+'$#l#,s#1s#=#l#-s#9s#6#l#,s#Cs#>#VOGD,FKs$5%s$<#s$9-#(O'FK#%s$@#s$8j#$s$B#)s$C#$(#,FL(%s$E#s$B-#(S#'FL#%s$I#s$Aj#$s$K#)s$L#$(#j##,#'FK)%s$O#s$Gj#$s$Q#)s$R#,FK-%s$S#s$P-#(S%'FK#%s$W#s$Oj#$s$Y#)s$Z#(S$'FK#%s$\#s$Tj#$s$^#)s$_#,FL'%s$`#s$]-#(S)'FL#%s$d#s$\j#$s$f#)s$g#$(#j##,#'FK)%s$j#s$bj#$s$l#U#D(S*'FK#%s$o#s$g(N,FL#%s$r#s$o-#(Q'FL#%s$v#s$nj#$s$x#)s$y#5Dj#.C#VQNS*VSPs#UNVS6s#V#1S71#1#0C#0C%0CS72C$#2C&#VS8#S91)0C#0C-2C#)2C%#VS8#S9WS:S&#s$*WS:S&*#6CM6COXSQC$G#7Cs%E*C#Rs$*+s$-IEEH#PUSRS'7C#*Cs$.S,#+s$1IEEH#P8s$2IEEH'#*C&Rs#r+s$4IEEH#P*Cs$4R,+s$6IEEH#P*Cs$5S,s#v+s$8IEEH#P8s$9IEEHs$5#/s$:IEEH&s$5#/s$;IEEH)s$6#/s$<IEEH,s$7#l#'#s$6s$0l#(6s$?#l#):s$B#j#*C#j#/C#j#0C##GD$#s%S#Os%W#JO&Os%Y$$#k##%#k##'#k##)#k#*C#k#/C#k#0C#ZDS;S<S+S=SSSTl#+0$#l#,s$Vs$b#l#-s$^s$[#l#,s$hs$c#VSUN#ZS>CNs#Ds#Cs#A#VS6s$:s#O5#m#%#WSVs#R#S(UKs#SVSWFs#PnS/$s%h$#1s%gD#%$#$s%_##4s%iM%s%i$#j#2s%j#ULs#Y*Cs$_Rs#8+s$bIEEH#P*Cs#:S,s#6+s$dIEEH#P8s$eIEEH%#/s$fIEEH#s$a#l#'#s$`s$Zl#(s#@s$i#l#)s$ms$l#j#*C#j#/C#j#0C##DG&GM$$##GM&MO$$#k##&#k#*C#k#/C#k#0C#XDS;S+S<S=l#+.$#l#,s$~s%.#l#-s%*s%'#l#,s%4s%/#VQN#WSXN#s#,ZS>s&-s#&AD@#'FLs#x4s&0G%s&0$#m#&#XSYs&3s#uG#9s#zs#us#-#j#3s$##j#$s&6#V#GDj##s$)#j#1s&9#YSZs&:s$:s$/#Dj#4s$?#j#5s$E#V#GDj##s$J#j##s$_#:s$`s$[s$P#Dl#6s$ds&4#j#&s%W#j#%C#9s%\s%Os$h#9s%^s%Os${#j#7s%`#j#8s%f#j#9s%l#V#GDj##s%o#j##s&$#:s&%s%|s%s#Dj#4s&'#j#:s&/#V#GDj##s&2#j##s&`#:s&as&Bs&8#Dj#4s&c#j#;C#j#<C##"). Qed.
  Lemma junk_transport_pt2 : forall lo n,
    junk m lo n -> (forall a, lo <= a < lo + n -> P a) -> junk m' lo n.
  Proof. intros lo n J HR Hn. eapply stk_transport_pt2; [apply J; exact Hn| exact HR]. Qed.
  Lemma wr_at_transport_pt2 : forall A n,
    wr_at bsegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at bsegs m' A n.
  Proof.
    intros A n (H1 & H2 & H) HR. split; [exact H1|]. split; [exact H2|]. intros i Hi.
    apply WK; [| apply H; exact Hi]. unfold wa. rewrite unsigned_lit by olia. apply HR. olia.
  Qed.
  Lemma rw_cells_transport_pt2 : forall A cs,
    rw_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells bsegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
    eapply bytes_at_transport_pt2; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
  Qed.
  Lemma u64arr_transport_pt2 : forall A ws,
    u64arr bsegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr bsegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split.
    - eapply bytes_at_transport_pt2; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. olia.
    - eapply wr_at_transport_pt2; [exact Hw|]. exact HR.
  Qed.
  Lemma SHAD_transport_pt2 : forall A sbs,
    SHAD m A sbs -> (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> P a) -> SHAD m' A sbs.
  Proof.
    intros A sbs (A0 & HA & [Hb Hw]) HR. split; [exact A0|]. split; [exact HA|].
    split; [eapply bytes_at_transport_pt2; eauto| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
  Qed.
  Lemma poisoned_transport_pt2 : forall A k v,
    poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v H HR. eapply SHAD_transport_pt2; [exact H|]. unfold poison_bytes. rewrite repeat_length. exact HR.
  Qed.
  Lemma batch_rep_transport_pt2 : forall b nx,
    (forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    0 <= qb_count b -> 24 + 8 * qb_count b <= kBatchSize -> qb_count b = zlen (qb_chunks b) ->
    batch_rep m b nx -> batch_rep m' b nx.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qbatch); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qb_addr); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kBatchSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(P); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qb_count); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.zlen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qb_chunks); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.batch_rep); constr:(m); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qb_size); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.wlist); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.junk); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.poisoned); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kAsanHeapLeftRedzoneMagic); constr:(m'); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Lists.ListDef.map); constr:(@Stdlib.Lists.List.length_map); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.TransportPt2.rw_cells_transport_pt2); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.TransportPt2.u64arr_transport_pt2); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.TransportPt2.junk_transport_pt2); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.TransportPt2.poisoned_transport_pt2); constr:(@Corelib.Init.Logic.or_intror)|] [|@a; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @H0; @H4; @H3; @H2; @H1; @H; @__sat5; @cstr; @x; @y; @m; @Ha0; @Ha; @z; @__x3; @__x4; @LW; @B4; @B3; @B2; @B1; @K3; @K2; @K1; @HP; @nx; @b|] "#+/#D$^#H$8#$##$9$7#^#V#c#%$>#n#o#a#-#&#'#,#)#.#5#6#*$&$V$W#O#T#/#q#(#+#1#4$/$=#e#7#s#N#M#B#Q#X#g#m#0#2#3$.$B$C#?#=#p#8$O$^$`#I#U#[#u#v#w#x#y#z#{#|#~#}$%$$$+$*$)$0$3$4$6$?$@$D$E$A#:$G$F$H$I$R$S$T$Q$P$N$M#9#C#A$Z$K$\#>#@$[$_$]$b$a#G#J#K$-#L#W#b#S#Y#d#k#\$;$:#Z#l#i#j#r$5#h$#$($X#P#]#f$,$Y$U#R#`$1$<#t$'$2$L$J#_P#J%$7%$8%#K%$9$$:$$;$$<&$=$$>%#G$$?$$@%$A$$B'$C*$D&#I$$E'$F$$G&$H%$I+$J'$K%$L&$M&$N$$O&$P$$Q%$R%$S*$T$$U'$V'$W%#8%$X$$Y%$Z%#&&$[&$\'$]((L%#F#$S-&F#$%#>'%#F+S.+#+#D#VS=S-##)#&F#$*#VSN-#USOEk##$#k#$C#)L%J#US>S.+#+#+#D#)R,3##%#%#S-)S#0S#VSPC#3C%#?IS1S#(S%-S1.#@S%-#.#)S%-#.#US?K*K$#*K(#*K,#EPI/##0:0S%6#:PI%#,s#-.#'#/S-@/#%7I%#US@s#15I:#N$%#$+#$0#?OS)S%j##$#(S)##s#+0S)6#:PI%#)S),s#?##(#/4$7I$#5I,3N$$#$*#(S2-S).#@S2-#.#)S2-#.#*K#s#-*K'#*K+#EPI.#(S$##s#E0S$6#:PI%#)S$,s#Y##(#/s#.$7I$#5I,s#-N$$#$*#(Q##s#R0Q6#:PI%#)Q,s#f##(#/s#;$7I$#5I,s#:N$$#$*#?OS&Qj##$#(S&##s#a)S&,s#r##%#/s#G$7I$#5I)s#FN$$#(S/##s#j0S/6#:PI%#(SA##s#o)SA,s$$##%#/s#U$7I$#5I)s#TN$$#(S3##s#x)S3,s$-##%#/s#^$7I$#5I)s#]N$$#?OSBS3j##$#(SB5I#s#bN(SC##s$))SC,s$:##%#/s#k$7I$#(S45I#s#kN0S'8C#4F)S(3C$#j#%S0#I'4(%J#+s$J+#+#+#+#+#+#+#+#+#D#VSQ#s$T%J$%Js$VVS=&s$W%J#k##%#k##'#VSR*s$[3Cs$\JUSS#,s$^)VST.s$_#$#3C0#k##'#VSU2s$c&Js$d%J(&)s$f$$#k##&#VSV8s$i&s$jJ&s$k.%/J$$#k##&#VSW>s$o3C;Jk##7#VSXAs$r3C6Bk##:#VSYs#$s$um#SZ#VS[Js$w;S\#m##7US##US]S.VS^C#'SDAC#WS_C%#ACSD<C$#J#S5US?S**S*$#US`S*KCLUSaCFC$E#USbCUScCGCs%2GCS.1C$S6#2&HDDG#MUSdD1C&S6'2)HDDG#M9*HDDG&%#VSe+G;SESFVSfFL3SE#SFm$%#WSgCJEXShFL$#l#&*)#l#'54#l#(:9#j#)C#j#*C#3CEF3CELk##$#k#)C#k#*C#)SG0SG8C#4#L&#Sil#+-(#l#,s#2s#E#0SH8C#4#)SH3C$#m#(#l#-s#=s#>#l#.s#Bs#@#l#/s#Fs#D#l#0s#Ms#H#l#,s#Ts#O#l#1s#]s#V#l#2s#es#_#l#3s#ts#r#USjs#pUSk#XSlC#S7s#}8$#XSmC%S7s$#ZSIS0s$#s#{($#6s$%8(#4#)S'3C$#m#(#(S(-S'.#@S(-#.#-s$..#*K#s%O*K&#*K*#EPO-##.s%f0S(6#:PO%#,s%ys$8#'#/s$*s%l/#%7O%#US@s$)5O8#N$%#$+#(S8%#F's#e'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#4##<#&F#$=#(SJ%#E#$s$P&E#$%#>'%#E#$s$Q&E#$%##,0&E#$-##/s&A&E#$0#j#4CFU#s&E#4#&E#USK5&EFUSK#j#5C#j#4C#;CE#EFXSnCCSo#;C#j#6C#j#%C#;CA;Cs%#j#4S0#;Cs&V`SpS0CCCS9S955$s#*s&W#fSqCCCCCCS:666S:(s#&s#&'s#*5#`SrCCS;7S;/EE.=5#ZSss#'=s#'54#XSt=:#F0Su6#8s#m#I#4$%J#1Cs$CS+s$D2s$FHDDG#MBCs&d=Cs$F#1Cs$HS,#2s$JHDDG#MCs$KHDDG'#BCs%'=Cs$K#1Cs$MS,#2s$OHDDG#MCs$PHDDG,#9s$QHDDG(s$L#l#&#s$Is$Cl#'s$Us$T#l#(s$[s$Y#j#)C#j#*C#%FE#Fs&u&E#$%#%EL#Es%7&L#$%#k##'#k#)C#k#*C#(SvLS/#Ql#+0%#l#,s$us%,#(Sw%#Q#$s%C&Q#$%#m#(#l#-s%$s%%#l#.s%)s%'#l#/s%-s%+#l#0s%4s%/#l#,s%;s%6#l#1s%Ds%=#l#2s%Ls%F#l#3s#3s#1#l#7s#8s#P#Ms#\s#W#HE#j#8s#c#j#$C#-S(.#@S8-#.#)S8-#.#*K#s'/*K'#*K+#USx#4##s$2#&F#$s$3#k###s'Sk#$C#m#5#XSys$Qs$GQ#%s#kF,s'^E#s#m#&F#$&#k###s'\k#$C#j#9C##s$As'V%#F,s'g;#%#&F#$&#0SJ6#8s$m#I#4$%J#ACs$K<Cs%Rs%P<C$#J#S5*S*#s%PKCRFCs%OE#1Cs#bS+s%K2s%MHDDG#MBCs'zGCs'pWSzC$#=Cs#g#1Cs%QS,#2s%SHDDG#MCs%THDDG)#=Cs#l'1C#S+s#h2s%WHDDG#M9s%XHDDG#s%Ss#f9s%YHDDG's%T#l#&#s%Qs%Kl#'2s%\#l#(5s%a#j#)C#j#*C#j#:C#%s#fE,s(1L#s#h#&E#$&#,s(5R#s('#%#s&B%LR#Ls&D&R#$%#k##'#k##+#k#)C#k#*C#k#:C#)S<(S<YF$S&#QS{l#+7&#l#,s&)s&<#(S|%#S$#$s&S&S$#$%#m#(#l#-s&4s&5#l#.s&9s&7#l#/s&=s&;#l#0s&Ds&?#l#,s&Ks&F#l#1s&Ts&M#l#2s&\s&V#l#3s#Cs#A#Ms$ks$f#HE#j#8s#J#j#$C#8s%Xs%?4#ZSICs&us#T%#FXS}s%Ds%BS%#%s#RF/s%@s#T#s#T#&F#$&#VS~Cs(aACs%:WSLC$#ACs%=WSLC&s&E<C#s&D<C%#<C'#J#S5*S*#s&EKCS#FC#Rs&CFCs&EE#BCJUS>s(rGC#1C%S+#2s&FHDDG#M1Cs#TS+s&F2s&HHDDG#MWSMCs$[s$`WSMC#s#X=Cs#X#1Cs&KS,#2s&MHDDG#MCs&NHDDG(#1C-S6s#^2s&PHDDG#M9s&QHDDG#s&Ls$_9s&RHDDG&s&M#9s&SHDDG/s&N#l#&#s&Ks&El#'6s&V#l#(:s&[#j#)C#j#*C#j#:C#j#;C#%JR#Es(y##s#V%#L/s%ns#X#%#&L#$&#3CS1S#%RS##Rs'@&S##$%#k##'#k##)#k##1#k#)C#k#*C#k#:C#k#;C#0S<6#8s&A#4#[F#s#`S&s#_S$QS/l#+<(#l#,s')s'<#m##s#Zl#-s'/s'0#l#.s'4s'2#l#/s'8s'6#l#0s'?s':#l#,s'Fs'A#l#1s'Os'H#l#2s'Ws'Q#l#3s$>s$<#Ms%fs%a#HE#j#8s#O#j#$C#XT#s&7s&5L#>s&0%#F4s&6#%#&F#$&#Ds'iBC#=Cs'.#1Cs'0S,#2s'2HDDG#MCs'3HDDGs%K#9s'4HDDG#s'/#l#&#s',s'&l#'s'8s'7#l#(s'>s'<#j#)C#j#*C##F.&E#$s%C##E1&L#$s%B#k##&#k#)C#k#*C#>s$/LS&#Ql#+.%#l#,s'Vs'i#>s$/%#S$#$=&S$#$%#m#(#l#-s'as'b#l#.s'fs'd#l#/s'js'h#l#0s'qs'l#l#,s'xs's#l#1s(%s'z#l#2s(-s('#l#3s$ps$n#WT$s&<s&7#HE#j#8s#,#j#$C#YT%s&zs&eNE#Ns&gs&es#5#Ns&ms&es$.#Ns&rs&es%.#l#<s'#s'$#(S'-S4.#@S'-#.#-s',.#*K#s)p*K&#*K*#EPO-##.s*+:PO#s'6,s*<s'4#%#/s)m$7O$#5O4s)lN$$#$)#$,#m#9#?OS'S4m#$#j#=s(f#j#>s(i#V#EFj##s(r#j##s(y#Os(zs(ys(v#Fj#1s)&#j#?s)0#V#EFj##s)7#j##s)K#Os)Ls)Es)B#Fj#1s)R#j#@s)`#V#EFj##s)o#j##s*1#Os*2s*%s)~#Fj#1s*A#j#As*C#j#Bs*H#j#Cs*R#j#Ds*U#j#EC#j#FT&##"). Qed.
  Lemma bseg_transport_pt2 : forall l nx,
    (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    Forall bok l -> bseg m l nx -> bseg m' l nx.
  Proof.
    intros l nx HP OKl. induction l as [|b r IH]; [exact (fun x => x)|].
    cbn [bseg]. intros [HB HR]. apply Forall_cons_iff in OKl. destruct OKl as [OKb OKr].
    split; [| apply IH; [intros b0 a Hb0 Ha; apply (HP b0 a); [right; exact Hb0| exact Ha]| exact OKr| exact HR]].
    destruct OKb as (_ & _ & _ & K1 & K2 & _). unfold kBatchCount, kBatchSize in *.
    apply (batch_rep_transport_pt2 b _); [intros a Ha; apply (HP b a); [left; reflexivity| exact Ha]| clear - K1; olia| clear - K1; unfold kBatchSize; olia| exact K2| exact HB].
  Qed.
End TransportPt2.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma PROOM_of_NUM : forall st XC XB, WFQ st XC XB -> NUM st -> pusage st + 303104 <= B_PRIM.
Proof.
  intros st XC XB W NM. pose proof B0_val as BV.
  assert (PB : pusage st <= B0); [| clear - PB BV; olia].
  apply pusage_bound; [exact NM|]. intros c Hc. unfold kNumClasses in Hc.
  pose proof (WFQ_region st XC XB c W ltac:(unfold kNumClasses; olia)) as RO. pose proof (class_size_table_facts c ltac:(olia)) as (CS1 & _ & CS3 & _).
  cbv zeta. split; [olia|]. split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split.
  - pose proof (ro_tail_small _ _ RO ltac:(olia)) as T. destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; olia.
  - pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_bound _ _ RO). pose proof (ro_numfreed _ _ RO). pose proof (zlen_nonneg (rg_free_array (get_region st c))). olia.
Qed.

Lemma NUM_au : forall st st',
  (forall c0, 0 <= c0 -> rg_allocated_user (get_region st' c0) = rg_allocated_user (get_region st c0)) -> NUM st -> NUM st'.
Proof. intros st st' AU NM c Hc. unfold ncarved. rewrite (AU c ltac:(clear - Hc; olia)). exact (NM c Hc). Qed.

Lemma class_of_addr_sb : forall st st' a, as_space_beg st' = as_space_beg st -> class_of_addr st' a = class_of_addr st a.
Proof. intros st st' a E. unfold class_of_addr. rewrite E. reflexivity. Qed.
Lemma in_primary_sb : forall st st' a, as_space_beg st' = as_space_beg st -> in_primary st' a = in_primary st a.
Proof. intros st st' a E. unfold in_primary. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma xb24_facts : forall st XC XB B, WFQ st XC XB -> In B XB -> class_of_addr st B = kBatchClass ->
  exists off, 0 <= off < 2^32 /\ B = as_space_beg st + kBatchClass * 2^32 + off /\ in_primary st B = true.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.WFQ); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_of_addr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kBatchClass); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.WFQ_xb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.xb_ok); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.carved); constr:(@kc__1); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kNumClasses); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_size); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region_beg); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_allocated_user); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.get_region); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_space_beg); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.in_primary); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.WFQ_region); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.region_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.ro_alloc_le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_mapped_user); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.ro_mapped_bound); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kUserMapSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kFreeArrayOffset); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@Stdlib.ZArith.BinInt.Z.shiftl_mul_pow2); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.andb_true_intro); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt)|] [|@z; @off; @__ff; @__varmap; @__wit; @__arith; @H0; @H4; @H3; @H2; @H1; @H; @__sat6; @Ha; @__x1; @__x2; @__x3; @__x4; @__sat7; @__sat1; @__sat0; @m; @n; @__sat9; @__sat8; @C3; @C4; @C5; @A2; @A1; @RO; @C2; @C1; @CV; @CL; @HB; @W; @B; @XB; @XC; @st|] "#+6#J$T#O#T#\$)###$$*$(#n#p#%$0#&#'#>#?$.#(#<#=#*#+#-#.#2#6#9#;#B#)#/#5#7#:$#$A#k#,#1#0#3#4#8#A$1#N#S#X#h#t#@#}#|$&$@$B$H$D$I$C$S$R#E#F#I#P#Q#U#V#^#`#_#r#s#u#v#w#x#z#y#~$$$%$'$2$4$5$3#q$6$7$9$:$;$<$=$O$Q$T$X#C$Y$U$>#M#j#[#Z#d#R#a#b#c#f#e#]$,$+#l$L#i#o$-#g$E$M#Y$F#W$/$8$G$N$P$V$W#m#{$K$J$?H$0$$1%$2%$3%$4&$5%$6%$7%$8%$9$$:%$;'$<*$=$$>+$?$$@%$A%$B%$C&$D&$E($F%$G)$H$$I$$J$$K%$L&$M%$N%$O%$P%$Q%$R'#'&$S'US@CWSTOMHWSUCHMVSAS$M'C#DZSVS0S$POMHVSWS0OVSAS'PWSBS(GS$j#$C#:C%#GDHWSBS'DP$ED-DSX%$#USYD'C#EUSZ#)S(D(S$#$E#*$('C#E&&*+S(D,#$%#%'#%*#%.#%2#$EG#S72##$######2#VSC(#-G#%,#0S)BD&&$#&#G'CS'#3S)S''K#L%%#%+#j#%C#5C#j##9#)S8D(S0#$E#*$s#,'C#E&&s#.+S8D,#$%#%'#%*#%s#2#)S*D(S(#$E#*$s#8'C#E&&s#:+S*D,#$%#%'#%*#%s#>#)S1D(S8#$E#*$s#D'C#E&&s#F+S1D,#$%#%'#%*#%s#J#0S9&#s#2&#G'CS*#3S9S*'K#L%%#%s#:#j#%C#5C#j##-#)S:D(S)#$E#*$s#['C#E&&s#]+S:D,#$%#%'#%*#)S+D(S1#$E#*$s#f'C#E&&s#h+S+D,#$%#%'#%*#)S;D(S:#$E#*$s#q'C#E&&s#s+S;D,#$%#%'#%*#0S2&#s#^&#G'CS+#3S2S+'K#L%%#%s#f#j#%C#5C#j##-#)S<D(S9#*#s$*'C#E&%s$,+S<D,#$%#%'#)S2D(S+#$E#)S,D(S;#*#s$6'C#E&%s$8+S,D,#$%#%'#)S3D(S<#*#s$?'C#E&%s$A+S3D,#$%#%'#0S-&#s$+&#G'CS,#3S-S,'K#L%%#%s$3#j#%C#5C#j##-#)S=D(S2#&#s$S+S=D,#$%#)S-D(S,#*#s$Y'C#E)S4D(S3#&#s$]+S4D,#$%#)S.D(S=#WS[#s$cS$$Es$d)S%D(S-#*#s$g$E#k##'#VS\&s$j)S&D(S4#VSD#s$mBs$n#*%s$o&$#'C'#k##s$p#VS])s$s-Es$t)QD(S.#*#s$w$E#-$s$y%$#k##)#VS^(s$|-s$}E)RD(S%#*#s%$-s%%#$$E%$#k##)#VS_(s%))SED(S&#VSD#s%,'C#Ek##s%-#VS`&s%/)S>D(Q#*#s%2'C#$k##s%3#VSa&s%5m#Sb#VSFEs%7CSG#m##s##UP#)S/D(R#*#s%=$E#-$s%?%$#UScS5US@S5USdCUSeCUSfC4CE;S7######2#4C#.C)S##/+JFFI#N4Cs%8.C&S?#/.JFFI#N[SH/JFFI&#VSg0ICKLVShGM'K#Lm$%#WSiCEHXSjGM$#l#&*)#l#':9#l#(=<#$E4-5s%G%$#l#)&#Gl#*s#)s###m##%l#+s#/s#0#l#,s#7s#2#l#-s#>s#9#l#.s#Hs#@#l#*s#Rs#J#l#/s#\s#T#l#0s#ds#^#m##s%kZSkS.S4S-DS3#VSlS.DWSmS%DG+S%D,#<$$$#WSnS&DH+S&D<#&#So$#SpVSqDs%`0R&#G(S%#&#s%{+RD,#$%#j#$C#.Cs#<S#s#3/s#>JFFI#Nl#&#s#1s#+l#'s#Bs#A#l#(s#Es#D#$Es%nl#)$#GWSrDs%p#:C3+Os%l#0Q&#s%n(S.#&#s&0+QD,#$%#0SE&#G(S&#*#s&7'C#Ej#$C#:CA#S$s%z1&As%{(S%#*#s&='C#E0S>&#G(Q#$E#j#$C#:Cs#+#S)s&(;&3s&)(S&#$E#0S/Bs#\s&1&$#&#G'CR#3S/R'K#L%%#%s&6#j#%C#(Q5(#,$E#-$s&=%$#&:0&#''CQ#3S>Q'K#L%%#VSIs&Ks&F-Es&L-Es&Gk##s#9#k##%#$Es&PWSJs&Qs&LHj##S6#j#1%#$Es&Nk##S6#k#1(#VSFEs&WCSG#m##/UH#=SK=#=#=#9C#9C%9C'9CSK6C$#6C&#6C(#VSL#SMWSNS5#s$:DCPEC#Ms$:DCOEC$H#>Cs&k#s&i########################2#4C#7C2#;s$J##########################################################2#4C#.Cs##S##/s$mJFFI#NUSsF>Cs$m.C#S#s#7/s$qJFFI#N>CS7>Cs'I4Cs'IUSOs'FWSPC$#WStCs$p#7C'#?C)#2s#94C#7C%#.C#S#0/s$~JFFI#N.Cs$~S#(/s%$JFFI#N?C10?C#-.Cs%&S##/s%(JFFI#N.C%S?1/s%*JFFI#N[SHs%+JFFI%#1s%,JFFI*<#1s%-JFFI-=#1s%.JFFI;>#1s%/JFFI@?#l#&#s$~s$xl#'s#Us%2#l#(s#Zs%5#j#2C#j#3C#j#4C#j#5C#&Os#L$#s#,$OP&Os$6(M#&#@$#P&Ps$:(O#$E#(PS$(#s$>$E#-$s'o%$#k##(#k##,#k##1#k##3#k#2C#k#3C#k#4C#k#5C#+SQs%H<#,$0SQ\G%$#S/S'S(S0Pl#)?(#l#6s$-s$9#l#0s$5s$2#l#6s$>s$:#DCMEC#Hs%Z7Cs#?s#5.Cs#FSu#/s%[JFFI#Nl#&#s%Ns%Hl#''s%^#l#(s%bs%a#j#2C#j#3C#&Hs$](GH(#s$_&%#'CG#k#2C#k#3C#VG9S/l#)+$#l#7s$Cs$O#l#8s$Ks$H#l#7s$Ts$P#@s$sQ;s(B##;#2#VSCs(G#&s$y#AQ#'K*L'K$L@HG'K#L$MHk##$#$HG@MH'K#Lk##%#%'#@OM'K#Lk##+#j##&#j##$Gj##-#VSvHG8/+&$#j#9C#j#:C#k#9C.k#:C#7Cs#xs#s?Cs#x#.Cs&1S##/s&3JFFI#N.Cs#|S#s#{/s&5JFFI#N1s&6JFFI%s$&#l#&#s&)s&#l#'s#>s&9#l#(s&=s&<#j#2C#j#3C#&Gs%8(H#$E#$HMk##$#k#2C#k#3C#0SRFSw#S$l#),%#l#6s${s%+#l#0s%'s%$#l#6s%0s%,#Fs%FR#l#/?=#AHG'K#L-MHk##$#-HGAMH'K#Lk##%#%'#AOM'K#Lk##+#j##&#j##$Gj##-#VSxHG8/+&$#j#9C#j#:C#k#9C.k#:C#&s%]s#LVSIs)6s#N$Es#O-Es#Ok##$#k##s%L#WSJs);s#SHj##S6#j#1s%K#$Es#Uk##S6#k#1s%N#UPs%F9Cs%E6C#s%?6Cs%A#6Cs%C#VSL#SMWSNS5#s&vUSOs#aWSPCs$^#7Cs$`#.Cs$bS?#/s&wJFFI#N1s&xJFFIs$Xs$h#1s&yJFFIs$fs$i#1s&zJFFIs$ks$j#l#&#s&ms&gl#'s%Ds&}#l#(-s'$#j#2C#j#3C#j#4C#j#5C#&Ps#n-O#k##s$I#k##s$N#k##s$P#k#2C#k#3C#k#4C#k#5C#+SSs')<#,$0SS[G%$#SRS*S1S)l#)1(#l#;s#'s#/#l#6s%ks%w#l#0s%ss%p#l#6s%|s%x#l#<s#/s#,#l#;s#7s#3#FRs#9#l#/s#=s#;#Gs$&s$%s#Q#WSys$/s$(#m##s&)Gs&,s&*s$2#Gs&0s&*s$I#XSzCs&6s&4#&s&@s)j&#G'CR#%#s&=%s)p#j#%C#5C#m#*#l#=s&Ls&I#l#>s&Ws&S#l#?s&fs&_#&s&XG'CS%#3RS%'K#L%%#%s)|#j#%C#5C#m#+#l#@s'*s'&#l#As'0s',#l#Bs'3s'2#j#?s(?#j#>s(F#V#HGj##s(L#j##s(c#8s(ds(`s(T#Gj#/s(i#j#=s(s#V#HGj##s(x#j##s)9#8s):s)3s)'#Gj#/s)>#j#Cs*L#V#HGj##s)L#j##s*O#8s*Ps)es)Y#Gj#/s)q#j#Ds*U#V#HGj##s*$#j##s*X#8s*Ys*Js*2#Gl#Es*^s*]#l#Es*ds*c#j#Fs*f#j#Gs*i#j#Hs*k#j#IC#j#Js*n#j#Ks*o#j#LS{##"). Qed.

(* [comment removed for export] *)
Lemma xc_chunk : forall st XC XB mch, WFQ st XC XB -> In mch XC ->
  exists ch, In ch (chunk_list st) /\ ch_state ch = CQuarantine /\ ch_chunk_beg ch = mch.
Proof.
  intros st XC XB mch W Hin. destruct (WFQ_xc st XC XB mch W Hin) as (ch & Fd & Qu). exists ch.
  split; [exact (find_chunk_In st _ ch Fd)|]. split; [exact Qu|].
  unfold ch_chunk_beg. rewrite (find_chunk_key st _ ch (WFQ_keys st XC XB W) Fd). unfold kChunkHeaderSize. clear; olia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cell : forall m A (ls : list Z) (i : nat) x, u64arr bsegs m A (wlist ls) -> nth_error ls i = Some x ->
  rw_cells bsegs m (A + 8 * Z.of_nat i) [C8 (wz x)].
Proof.
  intros m A ls i x U NE. apply nth_error_split in NE. destruct NE as (l1 & l2 & -> & LEN).
  unfold wlist in U. rewrite map_app in U. cbn [map] in U. apply (proj1 (mb_u64arr_app _ _ _ _)) in U. destruct U as [_ U].
  apply (proj1 (mb_u64arr_cons _ _ _ _)) in U. destruct U as [U _]. rewrite length_map, LEN in U. exact U.
Qed.

(* [comment removed for export] *)
Lemma arepq_sb_cell : forall s XC XB m, AREPQ s XC XB m -> rw_cells bsegs m (AINST + OI_SPACEBEG) [C8 (wz (a_sb s))].
Proof.
  intros s XC XB m R. pose proof (AREPQ_mem _ _ _ _ R) as (I & _). destruct I as (I1 & _).
  apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in I1. exact (proj1 I1).
Qed.

(* [comment removed for export] *)
Lemma batch_junk : forall m b nx, bok b ->
  rw_cells bsegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))] ->
  u64arr bsegs m (qb_addr b + 24) (wlist (qb_chunks b)) ->
  stk bsegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize) ->
  junk m (qb_addr b) kBatchSize.
Proof.
  intros m b nx OK H1 H2 H3 _. destruct OK as (K0 & K0' & _ & K1 & K2 & _).
  pose proof (stk_of_rw_cells bsegs _ _ _ H1) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 24) with 24 in S1.
  pose proof (stk_of_u64arr _ _ _ H2) as S2. unfold wlist in S2. rewrite length_map in S2.
  replace (8 * Z.of_nat (length (qb_chunks b))) with (8 * qb_count b) in S2 by (unfold zlen in K2; clear - K2; olia).
  unfold kBatchSize, kBatchCount in *.
  eapply stk_merge; [exact S1| eapply stk_merge; [exact S2| exact H3| clear - K1; olia]| clear - K1; olia].
Qed.

Lemma bsum_cons_le : forall b T, bok b -> bsum T <= bsum (b :: T).
Proof. intros b T (_ & _ & _ & _ & _ & K & _). rewrite bsum_cons. unfold kBatchSize in K. clear - K; olia. Qed.

(* [comment removed for export] *)
Lemma acompl_SP_mono : forall s s' d lo SP SP' m m', SP <= SP' -> acompl s s' d lo SP m m' -> acompl s s' d lo SP' m m'.
Proof.
  intros s s' d lo SP SP' m m' LE A a Ha NW. apply (A a Ha). intros W. apply NW. unfold awrit in W |- *.
  destruct W as [H|H]; [left; clear - H LE; olia| right; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 cs : word).
  Variables (lo : Z) (d : depot) (l : list qbatch) (Q : config -> Prop).
  (* [comment removed for export] *)
  Variables (s0 : ast) (m0 : mem) (mo0 : Model) (T0L : list qbatch).

  Let spv := bv_unsigned sp.          (* [comment removed for export] *)
  Let T0 := spv + 112.                (* [comment removed for export] *)
  Let SP := spv + 144.                (* [comment removed for export] *)
  Let st0 := a_st s0.
  Let ca := wz (a_cache s0).          (* [comment removed for export] *)

  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 800 <= spv.
  Hypothesis SPT : spv + 112 + 96 <= 2^47.
  Hypothesis SPA : spv mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.
  Hypothesis OKL : Forall bok l.
  Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 262144 <= lo.
  (* [comment removed for export] *)
  Hypothesis ALB : forall a, alive st0 a -> a < aceil.

  (* [comment removed for export] *)
  Definition REL (s : ast) (m : mem) (mo : Model) : Prop :=
       a_thr s = a_thr s0 /\ a_ctx s = a_ctx s0 /\ a_fsb s = a_fsb s0 /\ a_Zr s = a_Zr s0 /\ a_top s = a_top s0 /\ a_bot s = a_bot s0
    /\ a_AL s = a_AL s0 /\ a_sb s = a_sb s0 /\ a_pa s = a_pa s0
    /\ (forall sc, In sc (as_sec (a_st s)) -> In sc (as_sec st0))
    /\ (forall c0, 0 <= c0 -> rg_allocated_user (get_region (a_st s) c0) = rg_allocated_user (get_region st0 c0))
    /\ nonvm_same mo0 mo /\ avmx s0 s mo0 mo
    /\ acompl s0 s d lo SP m0 m /\ avis s0 s m0 m
    /\ agree_on (fun a => SP <= a) m0 m
    /\ alive_kept st0 (a_st s) /\ agree_on (alive st0) m0 m.

  (* [comment removed for export] *)
  Definition CUR (s : ast) (m : mem) (mo : Model) (XC XB : list Z) : Prop :=
       AREPQ s XC XB m /\ as_cache_inited (a_st s) = true /\ NUM (a_st s)
    /\ awin_vis s m /\ flagsx_rep m /\ AMODELX s mo /\ DEPOT bsegs d m /\ depot_placed s d /\ depot_cov d mo
    /\ mem_inv bsegs m.

  (* [comment removed for export] *)
  Definition dr_mid (B : Z) (T' : list qbatch) (st : astate) (ms : list Z) (racc : list effect) : option (astate * list effect) :=
    match cb_recycle_list st ms racc with
    | None => None
    | Some (st1, racc1) =>
        if negb (in_primary st1 B) then None else
        match cache_dealloc st1 (class_of_addr st1 B) B with
        | None => None
        | Some (st2, ev2) => do_recycle st2 T' (rev_append ev2 racc1)
        end
    end.
  Lemma do_recycle_cons : forall st b T' racc, do_recycle st (b :: T') racc = dr_mid (qb_addr b) T' st (qb_chunks b) racc.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition MSF (R : astate -> list effect -> option (astate * list effect)) (st : astate) : Prop :=
    forall stA racc, same_but_shadow stA st0 ->
      exists stB raccB, do_recycle stA T0L racc = R stB raccB /\ same_but_shadow stB st.

  (* [comment removed for export] *)
  Definition dr_post (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       REL s' m' mo' /\ CUR s' m' mo' [] []
    /\ lzok bsegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR (wz 0x5209c) (Z_to_bv 64 T0) gp tp t0 t1 t2 rs0 rs1 a0 a1 a2 a3 a4 a5 a6 a7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5209c) fc None m' (seg_rom bsegs)
    /\ stk bsegs m' lo T0
    /\ rw_cells bsegs m' T0 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]     (* [comment removed for export] *)
    /\ (forall stA racc, same_but_shadow stA st0 -> exists stA' racc', do_recycle stA T0L racc = Some (stA', racc') /\ same_but_shadow stA' (a_st s')).

  (* [comment removed for export] *)
  Hypothesis STEP_CHUNK : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 : word)
      (m : mem) (msF : machine_state) (mo : Model) (s : ast) (XC XB : list Z) (ch : chunk),
      AREPQ s (ch_chunk_beg ch :: XC) XB m -> In ch (chunk_list (a_st s)) -> ch_state ch = CQuarantine ->
      as_cache_inited (a_st s) = true -> awin_vis s m /\ flagsx_rep m -> AMODELX s mo ->
      DEPOT bsegs d m -> depot_placed s d -> depot_cov d mo -> mem_inv bsegs m ->
      aceil <= lo -> lo + 800 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      stk bsegs m lo (bv_unsigned sp) -> bv_unsigned tp = ATP -> pusage (a_st s) + 303104 <= B_PRIM ->
      bv_unsigned sp <= bv_unsigned sp + 8 /\ bv_unsigned sp + 8 + 8 <= 2^63 ->
      rw_cells bsegs m (bv_unsigned sp + 8) [C8 (wz (a_cache s))] ->
      lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (bv_unsigned sp + 8)) (wz (ch_chunk_beg ch)) a2 a3 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x523cc) fc None m (seg_rom bsegs) ->
      (forall msF' mo',
         rstep_post ra sp gp tp (Z_to_bv 64 T0) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 F fc s d lo m mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st s) ->
                         exists stA' ev, cb_recycle stA (ch_chunk_beg ch) = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).

  Hypothesis STEP_BATCH : forall (ra t0 t1 t2 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 : word)
      (m : mem) (msF : machine_state) (mo : Model) (s : ast) (XC XB : list Z) (p : Z),
      AREPQ s XC (p :: XB) m -> class_of_addr (a_st s) p = kBatchClass ->
      as_cache_inited (a_st s) = true -> awin_vis s m /\ flagsx_rep m -> AMODELX s mo ->
      DEPOT bsegs d m -> depot_placed s d -> depot_cov d mo -> mem_inv bsegs m ->
      aceil <= lo -> lo + 688 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      stk bsegs m lo (bv_unsigned sp) -> bv_unsigned tp = ATP ->
      junk m p (class_size kBatchClass) -> poisoned m p (Z.to_nat (class_size kBatchClass / 8)) kAsanHeapLeftRedzoneMagic ->
      pusage (a_st s) + 303104 <= B_PRIM ->
      lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (a_cache s)) (wz AINST) (wz kBatchClass) (wz p) a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x527d0) fc None m (seg_rom bsegs) ->
      (forall msF' mo',
         rstep_post ra sp gp tp (Z_to_bv 64 T0) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 F fc s d lo m mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st s) ->
                         exists stA' ev, cache_dealloc stA kBatchClass p = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TOK (T : list qbatch) : Prop :=
       Forall bok T /\ List.NoDup (map qb_addr T) /\ (forall x, In x T -> In (qb_addr x) (map qb_addr l))
    /\ bsum T < 2^62 /\ Forall (fun b => class_of_addr st0 (qb_addr b) = kBatchClass) T.

  (* [comment removed for export] *)
  Definition memB (m : mem) (b : qbatch) (T' : list qbatch) (j0 : list byte) : Prop :=
       rw_cells bsegs m T0 [C8 (wz (zlen T')); C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (last (map qb_addr T') 0)); C8 (wz (bsum T'))]
    /\ bseg m T' 0
    /\ dr_frame m spv j0 ca cs rs9 rs8 rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 (wz 0x5209c)
    /\ rw_cells bsegs m (qb_addr b) [C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
    /\ u64arr bsegs m (qb_addr b + 24) (wlist (qb_chunks b))
    /\ stk bsegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize)
    /\ poisoned m (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.

  (* [comment removed for export] *)
  Definition HEADINV (T : list qbatch) (s : ast) (m : mem) (mo : Model) (msF : machine_state) (XC XB : list Z) (j0 : list byte)
      (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word) : Prop :=
       REL s m mo /\ CUR s m mo XC XB /\ stk bsegs m lo spv
    /\ Permutation XC (flat_map qb_chunks T) /\ Permutation XB (map qb_addr T)
    /\ TOK T /\ dr_head_mem sp rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 ca cs m T j0
    /\ MSF (fun stB raccB => do_recycle stB T raccB) (a_st s)
    /\ lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo)
    /\ restrict (a_L s) (a_S s) msF = dr_head_ms sp gp tp F fc s10 s11 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 T 0x5230c m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma REL_refl : avmx s0 s0 mo0 mo0 -> REL s0 m0 mo0.
  Proof.
    intros AV. unfold REL. repeat (split; [reflexivity|]). split; [intros sc Hsc; exact Hsc|]. split; [intros c0 _; reflexivity|].
    split; [apply nonvm_same_refl|]. split; [exact AV|]. split; [apply acompl_refl|]. split; [apply avis_of_wmono; apply wmono_refl|]. split; [apply agree_on_refl|].
    split; [apply alive_kept_refl| apply agree_on_refl].
  Qed.

  (* [comment removed for export] *)
  Lemma agree_of_acompl : forall (P : Z -> Prop) s s' SPx m m',
    acompl s s' d lo SPx m m' -> (forall a, P a -> ~ awrit s s' d lo SPx a) -> agree_on P m m'.
  Proof. intros P s s' SPx m m' A NW x Hx Hr. exact (A x Hr (NW x Hx)). Qed.

  (* [comment removed for export] *)
  Lemma above_not_awrit : forall s s' SPx a,
    placed_ok s -> (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s))) ->
    aceil <= SPx -> lo <= SPx -> SPx <= a -> ~ awrit s s' d lo SPx a.
  Proof.
    intros s s' SPx a PL SUB AC LS Ha W. pose proof aceil_range as ACR. pose proof DLO as [D1 D2].
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _ & _ & _ & _ & _ & F1 & F2 & _ & _ & _ & _ & SEC & SEC2 & TCX).
    unfold awrit, astatw in W. unfold a_sb, kSpaceSize, kPageSize, kPtrArrayReserve, AINST, AIAINIT, AIAINST, sh, ASHADOW_BASE in *.
    destruct W as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - clear - H Ha. olia.
    - clear - H Ha T3 AC. olia.
    - clear - H Ha S3 AC. olia.
    - clear - H Ha S3 AC ACR. olia.
    - clear - H Ha P3 AC. olia.
    - destruct H as (sc & I & R). assert (I' : In sc (as_sec (a_st s))) by (destruct I as [I|I]; [exact I| exact (SUB sc I)]).
      pose proof (SEC sc I') as (_ & _ & G & _). clear - R Ha G AC ACR. olia.
    - clear - H Ha AC ACR. olia.
    - clear - H Ha D1 D2 LS. olia.
  Qed.

  (* [comment removed for export] *)
  Lemma batch_in_pendz : forall st PZ x a, In x PZ -> class_of_addr st x = kBatchClass ->
    (x <= a < x + kBatchSize \/ sh x <= a < sh x + kBatchSize / 8) -> pendz st PZ a.
  Proof.
    intros st PZ x a Hx CL R. exists x. split; [exact Hx|]. rewrite CL. change (class_size kBatchClass) with kBatchSize. exact R.
  Qed.

  Lemma TOK_tail : forall b T, TOK (b :: T) -> TOK T.
  Proof.
    intros b T (K1 & K2 & K3 & K4 & K5). apply Forall_cons_iff in K1. apply Forall_cons_iff in K5. cbn [map] in K2. apply List.NoDup_cons_iff in K2.
    split; [exact (proj2 K1)|]. split; [exact (proj2 K2)|]. split; [intros x Hx; apply K3; right; exact Hx|].
    split; [pose proof (bsum_cons_le b T (proj1 K1)); clear - H K4; olia| exact (proj2 K5)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wlocal (W : list ivl) : Prop := Forall (fun iv : ivl => spv <= fst iv /\ snd iv <= SP) W.

  Lemma outside_below : forall W a, wlocal W -> a < spv -> outside W a.
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.
  Lemma outside_above : forall W a, wlocal W -> SP <= a -> outside W a.
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.

  Lemma flagsx_local : forall W m m', flagsx_rep m -> wlocal W -> munch W m m' -> wmono bsegs m m' -> flagsx_rep m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.flagsx_rep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.Loop.wlocal); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepFacts2.munch_agree); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.agree_on); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.outside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.Loop.outside_below); constr:(@Corelib.Init.Logic.eq_refl); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(sp); constr:(@Corelib.Init.Logic.eq); constr:(spv); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(lo); constr:(HI); constr:(LO); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.ALIBCPGSZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.AGOT_SSP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.ASSPGUARD); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.ACFLAGS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@kc__2); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.rw_cells_transport_pt); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Corelib.Init.Logic.ex_intro); constr:(@kc__2 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__p1; @__arith; @heq_spv; @Ha; @a; @g; @b; @x; @y; @m; @n; @Ha0; @FXe; @bb; @H; @FXd; @FXc; @FXb; @FXa; @ZT; @ACR; @AG; @WM; @MU; @FW; @FX; @m'; @W|] "#-?#G$N#a#$#V#z###{#y#G#&$=#B$9$2#b$%#C#=#'#($##-#%#)$<#,#/$E#>#P#Y#+#3#4#k$($8#.#0#1#7#8#;$O#J#N#M#[#i#p#r#s$)$-$.$?#?$N$Q$B#K#Q#S#T#U#W#X#Z#`#c#f#g#l#q#u#v#x$&$+$/$0$1$,$3$4$5#d$A#2#5#6#9#:#<#@#A#D$J$L$M#F#L#O#_#\$7$>#]#e#^#j$$#}#|#h#w#R#o$*$'$:#n$H$K$I$G$F$P$D#m#~$@$C$6#t$;J$,$$-$$.%$/'#0%$0%#/%$1%$2%$3$$4&$5%$6'$7*$8&$9+$:$$;$$<&#=$$=*$>$$?%$@&$A5$B/$C)$D'#'&#3%$E$$F,$G&$H%$I$$J'$K($L%$M$US>SN#S/##########US?#US@#US?(US@#USO#k##&#3DUSPKWSQS$KS(WSRES$KXSSS)S%S$DUS0S)WST#S%S$USUSA$S/$#$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################,#USVSA*$#$s#&$#$#$#$#$#$#$#$###############################################,#*s#%#%s#%#'GSWVSXs#eSY+C#1CSB$m#$#4SC4#4#4#9C#9C%9C'9C)9CSCCC$#CC&#CC(#CC*#VSZ#S[USDS4-S4$#US>S4HCS$US\CXSEC$S(#HCKXSEC$D#US]CUS^CDCS/#s#t##$#$#####$#############################,#$S/##$#########$#############################,##3##$#$###$###$###$#$#########,##.######$#$#########,##S/##$###############$#$#$#$#$#$#########,#$s#G$#$#$#$#####$###$#$#$###$#######,#.Cs#E/Cs#sS&#0s#uIFFH#QUS_F.Cs$]DCs%0/C$S5#0s#zIFFH#QZSFs#{IFFHS)7s#|IFFH$#DCs%H#s#z########,#.C#5C*#DCs%R/C$S5#0s$,IFFH#Q/C3S5.0s$.IFFH#Q/Cs$.S&'0s$0IFFH#Q2s$1IFFH%9#2s$2IFFH(:#2s$3IFFH5;#2s$4IFFH=<#VS`s$5H+SGSHVSaGS(1SG#SHm$%#WSbCScDXSdGS($#l#$*)#l#%s$?s$>#l#&s$Fs$E#j#'C#j#(C#j#)C#j#*C#j#+J#'Gs#r*s%+K%#S%)S%B*#K*S%S)'S$S%k##$#k##&#k##)#k##,#k#'C#k#(C#k#)C#k#*C#k#+J#]Gs$rSes%9s$oKS(S$SfSgl#,4$#l#-s$ns$o#'DSBm#$#XShS'DS)#j#.s$v#j#/C#VS0S'Dk##s$y#k#/C##s&&##########,#I#8#USDN-N$#&ES1S6#IL8#-N#'&ES1S*#8G-N#*&ES+L#j#0s&7#(s&8#$s$r$###$#$#,#)SI#,S/USi#E#-N#8&ES1'##s&6$#####,#)SI#EG-N#A&ES+%#j#1s&L#(s&M#%.#%;#%A#%s#&#3S1j##$#&ES+S*s#&&ES'Ls#$j#0s&X#(s&Y#&ES+=9&ES'31j#1s&Z#(s&[#%&#%(#%,#&ES'S6s#5&ES7S*s#2&ES,Ls#0j#0s&d#(s&e#&ES7s#)s#%&ES,?=j#1s&f#(s&g#%&#%(#%,#&ES,S*s#=&ES8Ls#;j#0s&o#(s&p#&ES,s#4s#0&ES8s#*s#(j#1s&q#(s&r#%&#%(#%,#3S,j##$#&ES9Ls#Gj#0s&{#(s&|#&ES8s#@s#<&ES9s#6s#4j#1s&}#(s&~#%&#%(#&ES9S*s#S&ES2Ls#Qj#0s')#(s'*#&ESjs#Js#F&ES2s#@s#>j#1s'+#(s',#%&#%(#&ES3Ls#Zj#0s'2#(s'3#&ES2s#Ss#O&ES3s#Is#Gj#1s'4#(s'5#%&#%(#3S2j##$#&ES3s#[s#W&ESks#Qs#Oj#1s'<#(s'=#%&#&ESlLs#jj#0s'B#(s'C#&ES:Ls#mj#0s'E#(s'F#&ES:s#fs#b&ES;s#\s#Zj#1s'G#(s'H#%&#3S:k##$#j##*#&ES;Ls#xj#0s'P#U#G&ESmLs#{&ESns#rs#n&ES<s#hs#fj#1s'S#(s'T#%&#&ES<s#ws#s&ESos#ms#kj#1s'X#(s'Y#%&#3S<j##$#&ES#s#ss#qj#1s'^#(s'_#&ES#s$%s#}&ESJs#ws#uj#1s'b#(s'c#&ESps#zs#xj#1s'e#(s'f#3SJj##$#&ESqs$#s#}j#1s'j#U#G&EMs$&s$$#s&G##$#$#$#####$#$#$#$#########,#&EMs%|s$S$s(*############$###$#$#####$#########,##s##$#####$#$#$#########,#Is&58#-N#s$v&EMs&##&ERs&9s$pj#0s(H#(s(I#$s$n$#$#$###$#####$###$###$#######,#)s&&s${&EM#s$w)s&(s$r&ER#s$pj#1s(]#(s(^#%'#%;#%?#US0Sr*s&bG4s'Y4#4#4#6#)s&h#'G#%*#*s&kD'D&%$#,s(v)s&o#'D#%(#j#2CGU#')s&t#'D#+J-1J..m#$#:00#'DGUSs#j#3C#j#2C#+CD)DGXStCCSu#+C#j#4C#j#5C#+Cs'(6G+C#j#2S=#+C<`SKS=CCCS-S-99$s#%=#;CCCCCCO:::O)s'.s'.(s#%9#<CCP;P0DD/s#%9#=s##Bs##95#>B>#GHCDZSFs'qIFFHK.Cs'4.Cs#%5C$#/Cs'tS&#0s'vIFFH#Q7s'wIFFH(#2s'xIFFH#s&`s&al#$#s&Fs&@l#%,s'{#l#&s((s(&#j#'C#j#+J#'Gs#/%D#'Ds'Rk##$#k#'C#k#+J#*s'FK?#KDl#,+%#l#6:s#6#@D#j#.s#?#j#/C#As&$6#)s'O#'G#%s#M#VS0SvDk##$#k#/C#m#+#Bs#SRMS#S.s'Vs&-S;#*s'7G)s'8s#O'G#%%#*s';D'D&%$#)s'>s#N'D#%'#)s'As#L'D#+J*1J++m#$#:--#+Cs'G;CCCCCCOs#Ts#Ts#TOs#Cs'Hs'H#s#_s#Ss#=<CCPs#UPs#JDDs#I3*#=101*&#>0-#G.Cs'L5C#s#:/Cs(OS&#0s(QIFFH#Q7s(RIFFHs#?#2s(SIFFH#s';s'<l#$#s&}s&wl#%s#Cs(V#l#&s(_s(]#j#'C#j#+J#'G;%D#k###s#9k#'C#k#+J#*s'\K?#KDl#,*%#l#66A#@D#j#.s#)#j#/C#As$C6#)s'e#'G#%s#2#k###s#8k#/C#m#*#Bs$,RMS#S.s'ks$KS3#8S'-N#s&e*s('G)s((s$*'G#%%#*s(+D'D&%$#)s(.s$)'D#%'#)s(1s$''D#+J*1J++m#$#:--#+Cs(7;CCCCCCOs$/s$/s$/Os#zs(8s(8#s$:s$.s#t<CCPs$0Ps$%DDs$$3*#=101*&#>0-#G.Cs(<5C#s#q/Cs)*S&#0s),IFFH#Q7s)-IFFHs#v#2s).IFFH#s'rs'sl#$#s'Xs'Rl#%s#zs)1#l#&s):s)8#j#'C#j#+J#'G;%D#k###s#pk#'C#k#+J#*s(LK?#KDl#,*%#l#66A#@D#j#.s#)#j#/C#8S7-N#s'7A#6#)s(W#'G#%s#4#k###s#qk#/C#m#,#Bs$eRMS#S.s(]s#9S+#XSLs*ls%&S'#*s$pG6s)d)s$r#'G#%&#*s$uD'D&%$#)s$xs'7'D#%'#Us$as':)s$|#'D#+J+1J,,m#$#:..#+Cs%&1Cs%'s%'m#$#+Cs'D`SKS=CCCS-S-s$ls$ls$Ws)ys'E#;CCCCCCOs$ms$ms$mOs$\s%+s%+%8.#<CCPs$nPs$cDDs$b8.#=656.*#>52#G.Cs(S.Cs'M5C$#.Cs'M5C$#/Cs)kS&#0s)mIFFH#Q7s)nIFFHs$[#2s)oIFFH#s(Ws(Xl#$#s(=s(7l#%s$_s)r#l#&s){s)y#j#'C#j#+J#'Gs##%D#k###s$Uk#'C#k#+J#*s%BK?#KDl#,*%#l#69s#)#@D#j#.s#1#j#/C#As'a6#)s%K#'G#%s#;#k###s$Tk#/C#m#*#Bs%HRMS#S.s%Qs'iS%#ED-N#s(%*s%RG)s%Ss#B'G#%%#*s%VD'D&%$#)s%Ys'v'D#%'#)s%\s#A'D#+J*1J++m#$#:--#+Cs%b1Cs%cs%cm#$#;CCCCCCOs%Ms%Ms%MOs%<s%es%e#s#Ts#Js#?<CCPs%NPs%CDDs%B5,#=323,(#>2/#G.Cs'}5Cs#?#5C#s#=/Cs*IS&#0s*KIFFH#Q7s*LIFFHs%9#2s*MIFFH#s)5s)6l#$#s(ws(ql#%s%=s*P#l#&s*Ys*W#j#'C#j#+J#'G>%D#k###s%3k#'C#k#+J#*s%zK?#KDl#,*%#l#67s#$#@D#j#.s#,#j#/C#ES(-N#s(VA#6#)s&)#'G#%s#7#k###s%4k#/C#m#,#Bs&(RMS#S.s&/s#<G#XSLs,-s&.D#Fs&2s&.s#@#Fs&Fs&.s$##Fs&Js&.s$^#Fs&ns&.s%8#&EMS6s(d&EMS*s(a&ERLs(_j#0s,7#(s,8#&EMs(Xs(T&ERs(Ns(Lj#1s,9#(s,:#%&#%(#%,#%.#m#0#3Mm#$#j#7s'4#j#8s,C#V#DGj##s'8#j#2s,F#YSMs,Gs'@s'=#Gj#9s'C#j#:s'G#V#DGj##s'J#j##s'T#Gs'Us'Rs'O#Gj#9s'W#j#;s']#j#0s,R#V#DGj##s'a#j#2s,U#YSMs,Vs'os'f#Gj#9s'r#V#DGj##s'w#j##s()#Gs(*s(%s'~#Gj#9s(.#j#<s(8#V#DGj##s(;#j##s(Q#Gs(Rs(Is(F#Gj#9s(T#j#=s(`#V#DGj##s(c#j##s)9#Gs):s(ss(p#S)l#>s)Js)G#l#?s,]s+e#l#@s,as,_#j#As,c#j#Bs,e#j#Cs,g#j#Ds,i#j#Es,k#j#4Sw#j#Fs,y##"). Qed.

  Lemma stk_local : forall W m m' x, stk bsegs m lo x -> wlocal W -> x <= spv -> munch W m m' -> wmono bsegs m m' -> stk bsegs m' lo x.
  Proof.
    intros W m m' x ST FW LE MU WM. eapply (stk_transport_pt _ m m' (munch_agree _ _ _ MU) WM); [exact ST|]. intros a Ha. apply (outside_below W a FW). clear - Ha LE; olia.
  Qed.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.

  Lemma CUR_local : forall s m mo XC XB W m' mo',
    CUR s m mo XC XB -> wlocal W -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> same_but_materialized mo mo' ->
    CUR s m' mo' XC XB.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.ast); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.Loop.CUR); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.AREPQ); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache_inited); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.a_st); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocCons.NUM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.awin_vis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.flagsx_rep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.AMODELX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.DEPOT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(d); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_Malloc2.depot_placed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.depot_cov); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.Loop.wlocal); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.same_but_materialized); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil_range); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.AREPQ_frame); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Stdlib.Lists.List.In); constr:(@Stdlib.Lists.List.Forall_forall); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.afoot); constr:(@kc__3); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQFacts.stack_not_afootQ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.placed_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.WFQ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.AREPQ_placed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AG_RepQ.AREPQ_WFQ); constr:(@Corelib.Init.Logic.proj1); constr:(spv); constr:(SP); constr:(@Corelib.Init.Logic.eq_refl); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(sp); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(lo); constr:(HI); constr:(LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.awin_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.awin_vis_wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_DoRecycle.HCW.Loop.flagsx_local); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.AMODELX_mat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_DepotFrame.DEPOT_transport); constr:(DLO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_nb); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_sb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_DepotFrame.depot_avoid); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.depot_cov_mat); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@x; @l; @P; @A; @a; @iv; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__arith; @heq_spv; @F2; @F1; @H; @Ha; @Hin; @y; @z; @x0; @__p2; @D2; @D1; @ACR; @SBM; @MI'; @WM; @MU; @FW; @MI; @DCOV; @DPL; @DEP; @AMX; @FXR; @AWV; @NM; @INIT; @RQ; @mo'; @m'; @W; @XB; @XC; @mo; @m; @s|] "#1Y#_$w#f$W#}###|#p#$$X$V#&#'#g#*#+#%#,$\$]#)#.#2#6#_#U#(#1#-#/#5#3#:#9#O#0#4#7#>#s#v#8#=#<#A#?#B#;#F#I#J#[$i#E#D#N#^#Z$C#@#C#G#Q#K#P#S#V$B$j#H#M#]$H#T#k#L#R#Y$k#i#h$0$8$7$A$D$M$I$N$G$`$_$s$u#\$x#d#l$)$-$:$=$>$?$@$E$F$O$R$S$U$^$c$e$f$g$d$<$l$/$m$n$o$r$t#X$q$p$y#c#b#q#j$*$,$$$##~$v#{#z$T#n$Z$Y#y$.#x#u$+$1#m$%$&$'$($2#w$6$b$h#r$;$P$4$a#t$[$K$9#e$5$L$J$w#o$3$QT$H%$I$$J%$K$$L%$M%$N&$O%$P&$Q&$R+$S($T'$U*$V$$W'$X%$Y$$Z$$[&$\($]$$^&$_&$`%$a&$b$$c&$d%$e%$f&$g'$h'$i&$j&$k$$l%$m%$n(#&'$o$$p%$q$$r&$s*$t($u&$v%#&-KCKN$S[$#$#$#$#$#US`#USa#US`(USa#USr#k##&#7OS%S+MLPHPS+MO4PF#AS8#S9=%3PO1O,HPS%+GEO)HPE(ES%'GO#$##&##(##*##,##.##0##2##6#8M9S+RM:GS-S+'GS%;S&S%7S,POS&S-k##$#k##&#k##(#k##*#k##,#j##.#4RF#AS8#S9=%3RP1P,HRO+GEP)HRE(EO'GP#$##&##(##*##,##.##0##2#PHS-OS%R4S&F#AS8#S9=%3S&S-1S-,HS&R+GES-)HS&E(ER'GS-#$##&##(##*##,##.##0##2#4S.F#AS8#S9=%3S.S&1S&,HS.S-+GES&)HS.E(ES-'GS&#$##&##(##*##,##.##0##2#8P9RS4P:GS,R;S'S-7S/S.S&S'S,k##$#k##s#$#k##'#k##)#k##+#j##-#4S4=#3S4S.1S.,HS4S&+GES.)HS4E(ES&'GS.#$##&##(##*##,##.##0#4S,F#AS8#S94S'=#3S'S,1S,,HS'S4+GES,)HS'E(ES4'GS,#$##&##(##*##,##.##0#4S0=#3S0S'1S',HS0S,+GES')HS0E(ES,'GS'#$##&##(##*##,##.##0#8S.9S4S5S.:GS/S4;S(S,7S2S0S'S(S/k##$#k##@#k##'#k##)#k##+#j##-#3S5S01S0,HS5S'+GES0)HS5E(ES''GS0#$##&##(##*##,##.#4S/=#3S(S/1S/,HS(S5+GES/)HS(E(ES5'GS/#$##&##(##*##,##.#3S6S(1S(,HS6S/+GES()HS6E(ES/'GS(#$##&##(##*##,##.#8S09S5S:S0:GS2S5;S1S/7S;S6S(S1S2k##$#k##<#k##'#k##)#k##+#j##-#1S6,HS:S(+GES6)HS:E(ES('GS6#$##&##(##*##,#3S2S:1S2,HS1S:+GES2)HS1E(ES:'GS2#$##&##(##*##,#1S1,HS@S2+GES1)HS@E(ES2'GS1#$##&##(##*##,#8S69S:S<S6:GS;S:;S7S27S=S@S1S7S;k##$#k##9#k##'#k##)#k##+#j##-#,HS<S1+GES@)HS<E(ES1'GS@#$##&##(##*#1S<,HS7S<+GES;)HS7E(ES<'GS;#$##&##(##*#,HS>S;+GES7)HS>E(ES;'GS7#$##&##(##*#8S@9S<SLS@:GS=S<;S?S;7SFS>S7S?S=k##$#k##6#k##'#k##)#k##+#j##-#+GES>)HSLE(ES7'GS>#$##&##(#,HS=S>+GES=)HS?E(ESL'GS=#$##&##(#+GES?)HSME(ES='GS?#$##&##(#8S>9SLSGS>:GSFSL;SAS=7SBSMS?SASFk##$#k##3#k##'#k##)#k##+#j##-#)HSGE(ES?'GSM#$##&#+GESG)HSAE(ESG'GSF#$##&#)HSNE(ESF'GSA#$##&#8SM9SGSVSM:GSBSG;SCSF7SWSNSASCSBk##$#k##0#k##'#k##)#k##+#j##-#(ESA'GSN#$#)HSBE(ESV'GSB#$#(ESB'GSC#$#8SN9SVS\SN:GSWSV;SHSB7SOSPSCSHSWk##$#k##-#k##'#k##)#k##+#j##-#'GSP(ESP'GSW8SC9SPS3SC:GSQSP'GS\;SOS\USsH&S[&#&#&#&#&#&#&#&#&#&#&#&#&#$#&#&#&#&#&#&#&#&#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#5#UStH%$#&s#&&#&#&#&#&#&#&#&#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#5#%s#%##s#%#PHS*S]SOS34S*F#AS8#S9=%3S*S31S3,HS*SH+GES3)HS*E(ESH'GS3#$##&##(##*##,##.##0##2#k##FS)KI6QIF<MFQUMIk##$#k#$L#k##'#<LFIULIk##$#k#$Q#6LQIk##$##)#6MLQk##,#j##%#j##$Fj##.#QQIF.0*&$#j#%7#j#&9#j#'Sb#k#%:.k#&<#k#'Sb#DCCI%#F>CCILF##%#VScS^IUSd#k##%#k#(C#j#)N#VSuCC<NFSRDCCQ%#F>CCQLF##%#VScSDIUSd#k##%#k#(C#k##,#j#*.#BCCIF<N#SSBCCLQDCC#%#F>CC%LF##%#VSvHSI4SIWSw#SDSJZSxHSISDSJSXSRZSyHSISDSJSXSR2'%$#DCCF%ST#>CCF%#SK#%#j#)N#6N#S^<NFSDU%Ik##$#k#$N#k##'#<NFSJk###'k#$N#6N,SJk##$#QN.S^BCCMLZSe*%$S,#QU1$BCCS+MDCC#%ST#>CC%%#SK#%#%s$;Lj##$#BCCS%S+>CC#%#SKBCCOS%DCC#%ST#BCCPO>CC#%#SKVSzs)6S{VSfC#ACST$m#$#MSgM#M#M#HC#HC%HC'HC)HCSgNC$#NC&#NC(#NC*#VSh#SiUS|SYWSjSY$#KSYRCMUS}CCC$Q#RCS+CC#L%CC%I#US~CUT#CGCs)X&s)ZGC#/C%S##0'KDDJ#S$UT$DGCs)_/C'S##0+KDDJ#S$ZSk,KDDJO[Sl-KDDJ$#GCs%A$s%B$#&#$#$#$#$#$#5#?C#EC-#/C#S#90;KDDJ#S$GCS[/C#S#10>KDDJ#S$/C%S#80@KDDJ#S$-AKDDJ%;#-BKDDJ)<#-s##KDDJ8=#-s#$KDDJ?>#VT%s#%JVSfS8S9VT&FQAS8#S9m$%#WT'CT(IXT)FQ$#l#+*)#l#,s#/s#.#l#-s#7s#6#j#.C#j#/C#j#0C#j#1C#j#2C#j#3S)#%LM%S+Q##S%@Ms##%#S+%LS+%MS+k##$#k##&#k##)#k##,#k#.C#k#/C#k#0C#k#1C#k#2C#k#3S)#LPS-S#S&s#cSEPs%KLOSUS_l#46%#l#5s#bs#c#%s%NS%m#$#j#6s#i#j#7s#m#V#IFj##s#r#j##s#{#.s#|s#zs#w#Fl#8s$%s$$#[T*HSISDSJs$:I#j#9s$A#j#(C#j#:s$I#j#;C#j#$C#V#IFj#<C#j#<C#ICCs$Q#Fj#=N#JNs$`SO#l#8s$ns$k#VT+S*SQm#$#_T,HS*S]SOSQSZS3SCML#YT-S*SZS3S7L[T.SQSZS3S1S+MLZT/HS*SRSHS(IUT0E5s*^$s*]$#$#$#$#$#$#$#$#$#5#$S[$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#5#&/&#&#&#$#&#&#$#&#$#$#&#&#$#$#$#5#&S[$#$#$#$#$#&#&#&#&#$#&#&#$#&#$#&#$#&#$#$#$#5#&9&#&#&#&#&#&#$#&#&#$#&#$#$#$#&#$#$#$#5#VSms#[s#?@s#]#%#SEUT1E5s+`$s#V$#5#VSm&#@(#%#SE#+#VSnS]Ej##$#&s+h&#&#&#&#$#$#$#$#&#$#&#&#$#$#$#5#%s%gs#M$s$v$#$#&#&#&#&#&#$#$#$#$#&#&#$#&#$#$#$#5#@s#Ks#2%#s&#*9#j#)s&@#6s&A#S*$s'l$#$#$#&#$#$#&#$#$#$#5#%s&1s#H$s($$#5#@s#L#%#s&8*(#j#)s&U#6s&V#S*%s&:s$N%s#Ps&=*$#j#)s&Z#6s&[#S*%s&?s#R%s#Ms&B*$#j#)s&_#6s&`#S*#(##.#<s&cFT2%s&ls$-%s#*s&o*$#k##&#j#*s&h#<s&is&\SD6Ns&JSo<NFSIk###s&Ik#$N#k##&#<NFSXk###s&Mk#$N#6Ns&RSXk##$#QNs&TSoBCCQIZSe*%$S5#FUs&W$%STs&h%s&gSK#$#>CCs&N%#s$EDCCs&P%s#C#*%#j##(#%(SKRCLCC#Is&,CC#Ms&,?Cs(-/C#S#s%y0s&*KDDJ#S$ZSks&+KDDJS%[Sls&,KDDJ$#ECs&,s%s/C#S#s&+0s&/KDDJ#S$/Cs&$S#s&/0s&1KDDJ#S$?Cs$A?Cs$)EC$#/C#S#s&.0s&6KDDJ#S$Os&7KDDJs&-#-s&8KDDJ)s&2#-s&9KDDJ,s&3#-s&:KDDJ0s&4#-s&;KDDJs&2s&5#l#+#s%us%ol#,8s&>#l#-s&Gs&F#j#.C#j#/C#j#0C#j#1C#j#3S)#j#>S)#%LF%s(KQ##S+%s#jM*R#k##s%m#k##s%p#k##'#k##*#k#.C#k#/C#k#0C#k#1C#k#3S)#k#>S)#%Ps$zS#s(6s&qSEs(YRLS(SUS_l#44%#l#5s&ps&q#%S%s$~%s#{O*$#m#&#>CCs&~%#s%'%s$$s'#*$#m#'#j#6s'(#j#7s'1#V#IFj##s#B#j##s#L#.s#Ms#Ls#E#Fl#8s#Ps#O#j#:s#^#j#;C#j#$C#V#IFj#<C#j#<C#ICCs#e#Fj#=s'p#Js'qs$3SS#l#8s($s'}#%s'{s$m%s$$s'~*$#k##s#q#j#*s'w#%s#[s$r%s$)s#Z*$#j##s#_#?Cs$v?Cs$.EC$#/C#S#s&w0s'#KDDJ#S$Os'$KDDJs&v#-s'%KDDJs#Rs&{#-s'&KDDJs#Us&|#-s''KDDJs#Ys&}#-s'(KDDJs&{s&~#l#+#s&bs&\l#,s#as'+#l#-s'4s'3#j#.C#j#/C#j#0C#j#1C#j#3S)#j#>S)#%s$?M*R#k##s&W#k##s&Z#k##s#M#k##s#P#k#.C#k#/C#k#0C#k#1C#k#3S)#k#>S)#%Ps%9S#s(|s'[SEs)CRLS(SUS_l#41%#l#5s'Zs'[#%S%s%=%s$PO*$#m#&#%s#Hs%A%s$Ts'h*$#m#&#j#6s'm#j#7s'v#V#IFj##s$+#j##s$5#.s$6s$5s#3#Fl#8s$9s$8#j#:s$G#j#;C#j#$C#V#IFj#<C#j#<C#ICCs#?#Fj#=s(Y#Js(Zs$cSS#l#8s(is(f#%s(ds&S%s%Us(g*$#k##s$Z#j#*s(`#%s$Ds&X%s%Zs$C*$#j##s$H#VShs'qSiWSjSY#s'oCCs'lIs'mCCs$DQs'mCC$M#GCs'\/C#S#s'^0s'kKDDJ#S$?Cs&c?Cs&HWSpC$#ECs'h#/C#S#s'm0s'qKDDJ#S$ECs'os'\/C#S#,0s'tKDDJ#S$/C(S#s'i0s'vKDDJ#S$Os'wKDDJs$N#-s'xKDDJ&s'r#-s'yKDDJ*s's#-s'zKDDJ1s't#l#+#s'Xs'Rl#,6s'}#l#-:s()#j#.C#j#/C#j#0C#j#1C#j#3S)#%LI@Is%~%#L@Ls&$%#M*O#k##s'R#k##'#k##*#k#.C#k#/C#k#0C#k#1C#k#3S)#%Ps'-\F#s(RSERs'.LS'SUl#43%#l#5s(Qs(R#%S%s'1%s&3O*$#m#&#%s$?s'5%s&7s(_*$#m#&#j#6s(d#j#7s(m#V#IFj##s$~#j##s%,#.s%-s%,s#A#Fl#8s%0s%/#j#:s%>#j#;C#j#$C#V#IFj#<C#j#<C#ICCs#M#Fj#=s)P#Js)Qs%USS#l#8s)`s)]#%s)[s&I%s&Ds)^*$#k##s%Q#j#*s)W#%s%;s&N%s&Is%:*$#j##s%?#?Cs&NWSpCs%+#ECs(V#/C#S#s([0s(_KDDJ#S$/C%S#s(T0s(aKDDJ#S$Os(bKDDJs%9#-s(cKDDJs#Ms(]#-s(dKDDJ's(^#-s(eKDDJs#Xs(_#l#+#s(Cs(=l#,s#]s(h#l#-s#as(p#j#.C#j#/C#j#0C#j#1C#j#3S)#@Is&`%#L@Ls&b%#M*O#k##s(<#k##'#k##s#P#k#.C#k#/C#k#0C#k#1C#k#3S)#%Ps&r\F#s)<SERs&sLS,SUl#42%#l#5s);s)<#%S%s&v%s&qO*$#m#&#%s%)s&z%s&us)I*$#m#&#j#6s)N#j#7s)W#V#IFj##s%h#j##s%r#.s%ss%rs#4#Fl#8s%vs%u#j#:s&(#j#;C#j#$C#V#IFj#<C#j#<C#ICCs#@#Fj#=s*:#Js*;s&:SS#l#8s*Js*G#2s&@s&;s#I#2s&Fs&;s$A#2s&\s&;s%+#VSnS*Em#$#j#?s'1#j#@s':#V#IFj##s'4#j##s'=#.s'>s'6s'3#Fl#8T3s'6#]T4GESZS3SQS'ML#YT5ESRSHOI2s*{s*z#Q2s*}s*zS&#2s+#s*z&#2s+%s*zs(F#2s+'s*zs(H#2s+)s*zs(J#2s++s*zS?#2s+-s*zSA#2s+1s*zs(N#l#As,+s+3#j#Bs,-#j#Cs,/#j#Ds,1#j#Es,3#j#Fs,5#j#Gs,7#j#Hs,9#V#IFj##s,<#j##s,K#.s,Ls,Ks,?#Fj#8s,N#j#Is,R#V#IFj##s,U#j##s,h#.s,is,fs,Z#Fj#8s,k#j#Js,q#V#IFj##s,t#j##s-/#.s-0s-+s,{#Fj#8s-2#j#Ks-:#V#IFj##s-=#j##s-X#.s-Ys-Rs-F#Fj#8s-[#j#Ls-e#V#IFj##s-h#j##s.+#.s.,s.#s-s#Fj#8s..#j#Ms.:#V#IFj##s.=#j##s.`#.s.as.Vs.J#Fj#8s.c#j#Ns.q#V#IFj##s.u#j##s/@#.s/As/4s/(#Fj#8s/D#j#Os/U#V#IFj##s/Z#j##s0*#.s0+s/xs/l#Fj#8s0/#j#Ps0C#V#IFj##s0F#j##s0z#.s0{s0hs0[#Fj#8s0}#j#QSq#j#Rs1$#j#Ss11#j#Ts13#j#Us14#j#VSq#j#WT6#j#XT7##"). Qed.

  Lemma REL_local : forall s m mo W m' mo',
    REL s m mo -> wlocal W -> munch W m m' -> wmono bsegs m m' -> same_but_materialized mo mo' -> REL s m' mo'.
  Proof.
    intros s m mo W m' mo' RL FW MU WM SBM.
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    unfold REL. split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
    split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|]. split; [exact SUBS|]. split; [exact AU|].
    split; [eapply nonvm_same_trans; [exact NVS| apply nonvm_same_mat; exact SBM]|].
    split; [eapply avmx_mat_r; [exact AVM| exact SBM]|].
    split.
    { apply (acompl_trans s0 s s d lo SP m0 m m' (conj Et (conj Esb Epa)) SUBS ACM).
      apply (acompl_of_munchF s s d lo SP W m m' MU). apply Forall_forall. intros [x y] Hin a Ha.
      pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]. cbn [fst snd] in F1, F2, Ha. unfold awrit. left. clear - F1 F2 Ha LO HI; unfold spv, SP in *; olia. }
    split; [apply (avis_trans s0 s s m0 m m' SUBS (fun sc H => H) AVS); apply avis_of_wmono; exact WM|].
    split; [eapply agree_on_trans; [exact AGS|]; intros a Ha Hr; apply (munch_agree _ _ _ MU a); [| exact Hr]; apply (outside_above W a FW); exact Ha|].
    split; [exact ALK|].
    eapply agree_on_trans; [exact AGA|]. intros a Ha Hr. apply (munch_agree _ _ _ MU a); [| exact Hr]. apply (outside_below W a FW).
    pose proof (ALB a Ha) as B. clear - B LO HI. unfold spv. olia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma batch_phase : forall (b : qbatch) (T' : list qbatch) (XC XB : list Z) (s : ast) (m : mem) (mo : Model) (msF : machine_state)
      (j0 : list byte) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
      REL s m mo -> CUR s m mo XC XB -> stk bsegs m lo spv ->
      Permutation XC (flat_map qb_chunks T') -> Permutation XB (qb_addr b :: map qb_addr T') ->
      TOK (b :: T') -> memB m b T' j0 ->
      MSF (fun stB raccB => dr_mid (qb_addr b) T' stB [] raccB) (a_st s) ->
      lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688))
                  (wz (qb_addr b)) (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x52364) fc None m (seg_rom bsegs) ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach bsegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).
  Proof.
    intros b T' XC XB s m mo msF j0 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6.
    intros RL CU ST PXC PXB TK MB MF OK VIS HK K.
    destruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    destruct TK as (OKT & NDT & SUBT & BST & CLT).
    destruct MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    assert (CLb : class_of_addr (a_st s) (qb_addr b) = kBatchClass).
    { rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (Forall_inv CLT). }
    assert (INb : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    destruct (xb24_facts _ _ _ _ WQ INb CLb) as (off & OFF & EB & PRIM).
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    pose proof PL as (S1 & S2 & S3 & PLrest).
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_batch sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs (qb_addr b) (a_sb s) kBatchClass off).
      - exact MI.
      - exact S2.
      - exact S3.
      - unfold kBatchClass; clear; olia.
      - exact OFF.
      - exact EB.
      - exact (arepq_sb_cell _ _ _ _ RQ).
      - exact FR. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    apply (STEP_BATCH (wz 0x52390) t0 t1 t2 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6 x7 x8 x9 t3 t4 t5 t6
             m msF1 mo1 s XC (map qb_addr T') (qb_addr b)).
    - eapply AREPQ_perm; [apply Permutation_refl| exact PXB| exact RQ].
    - exact CLb.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - clear - HI; unfold spv in *; olia.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - change (class_size kBatchClass) with kBatchSize. exact (batch_junk m b _ OKb HB ARR STB).
    - change (class_size kBatchClass / 8) with (kBatchSize / 8). exact POI.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - exact OK1.
    - rewrite VIS1. unfold ca. rewrite ECA. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    destruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x52390)) with (ret_pc (Z_to_bv 64 0x52390)) in VIS2. rewrite (ret_pc_even 0x52390) in VIS2 by (clear; olia).
    (* [comment removed for export] *)
    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    pose proof (TOK_tail b T' (conj OKT (conj NDT (conj SUBT (conj BST CLT))))) as (OKT' & NDT' & SUBT' & BST' & CLT').
    assert (HM2 : dr_head_mem sp rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 ca cs m2 T' j0).
    { split; [| split].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) (map qb_addr T') (qb_addr b0) a); [apply in_map; exact Hb0| | exact Ha].
        rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_loop_test sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo); [| exact MI2| exact OKT'| exact BST'| exact HM2| exact ST2].
      clear - HI; unfold spv in *; olia. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.
    (* [comment removed for export] *)
    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (MF2 : MSF (fun stB raccB => do_recycle stB T' raccB) (a_st s2)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      pose proof SB as SB'. destruct SB' as (Esbeg & _).
      destruct (MOD2 stB SB) as (stC & ev & CD & SC).
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite (in_primary_sb (a_st s) stB) by exact Esbeg. rewrite PRIM. cbn [negb].
      rewrite (class_of_addr_sb (a_st s) stB) by exact Esbeg. rewrite CLb. rewrite CD. reflexivity. }
    assert (XCP : Permutation XC (flat_map qb_chunks T')) by exact PXC.
    destruct T' as [|b' T''].
    + (* [comment removed for export] *)
      destruct VIS3 as [VIS3 ST3].
      apply K. unfold dr_post. exists s2, t0', t1', t2', (wz 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
      split; [exact RL2|].
      split. { split; [| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]].
               cbn [flat_map] in XCP. apply Permutation_sym, Permutation_nil in XCP. subst XC. exact RQ2. }
      split; [exact OK3|]. split; [exact VIS3|]. split; [exact ST3|]. split; [exact (proj1 HM2)|].
      intros stA racc SA. destruct (MF2 stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [exact EQ| exact SB].
    + (* [comment removed for export] *)
      eapply (HK ltac:(discriminate)). unfold HEADINV.
      split; [exact RL2|].
      split; [split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]|].
      split; [exact ST2|]. split; [exact XCP|]. split; [apply Permutation_refl|].
      split; [exact (conj OKT' (conj NDT' (conj SUBT' (conj BST' CLT'))))|].
      split; [exact HM2|]. split; [exact MF2|]. split; [exact OK3| exact VIS3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma chunk_phase : forall (rest : list Z) (b : qbatch) (T' : list qbatch) (XC XB : list Z) (s : ast) (m : mem) (mo : Model) (msF : machine_state)
      (j0 : list byte) (i : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6 : word),
      rest <> [] -> 0 <= i -> rest = skipn (Z.to_nat i) (qb_chunks b) ->
      REL s m mo -> CUR s m mo XC XB -> stk bsegs m lo spv ->
      Permutation XC (rest ++ flat_map qb_chunks T') -> Permutation XB (qb_addr b :: map qb_addr T') ->
      TOK (b :: T') -> memB m b T' j0 ->
      MSF (fun stB raccB => dr_mid (qb_addr b) T' stB rest raccB) (a_st s) ->
      lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688))
                  (wz (qb_addr b)) (wz kSpaceSize) x6 (wz (qb_addr b + 152 + 8 * i)) (wz (qb_count b + 16)) (wz (16 + i)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5234c) fc None m (seg_rom bsegs) ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach bsegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).
  Proof.
    induction rest as [|mi rest' IH]; intros b T' XC XB s m mo msF j0 i rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6;
      intros NE I0 EQR RL CU ST PXC PXB TK MB MF OK VIS HK K; [exfalso; exact (NE eq_refl)|]. clear NE.
    destruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    pose proof (Forall_inv CLT) as CLb0.
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).
    (* [comment removed for export] *)
    assert (NTH : nth_error (qb_chunks b) (Z.to_nat i) = Some mi) by (rewrite <- hd_error_skipn, <- EQR; reflexivity).
    assert (IR : 0 <= i < qb_count b).
    { split; [exact I0|]. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
    assert (MIR : 0 <= mi < 2^64) by exact (proj1 (Forall_forall _ _) Kb7 mi (nth_error_In _ _ NTH)).
    assert (CELL : rw_cells bsegs m (qb_addr b + 24 + 8 * i) [C8 (wz mi)]).
    { pose proof (u64arr_cell m _ _ _ _ ARR NTH) as C. rewrite Z2Nat.id in C by exact I0. exact C. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b) mi); [exact MI| exact Kb1| exact Kb2| exact IR| clear - Kb4; olia| exact MIR| exact CELL]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    assert (INmi : In mi XC) by (eapply Permutation_in; [apply Permutation_sym; exact PXC| left; reflexivity]).
    destruct (xc_chunk _ _ _ _ WQ INmi) as (ch & CHIN & QUAR & Ebeg).
    (* [comment removed for export] *)
    assert (CBC : rw_cells bsegs m (spv + 8) [C8 (wz (a_cache s))]).
    { unfold dr_frame in FR. apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [_ FR2].
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR2. destruct FR2 as [FR2 _]. cbn [cells_size csize Nat.add] in FR2.
      rewrite ECA. unfold ca in FR2. replace (spv + 8) with (spv + Z.of_nat 8) by (clear; olia). exact FR2. }
    (* [comment removed for export] *)
    apply (STEP_CHUNK (wz 0x52358) t0 t1 t2 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6
             (wz (qb_addr b + 152 + 8 * i)) (wz (qb_count b + 16)) (wz (16 + i)) t3 t4 t5 t6
             m msF1 mo1 s (rest' ++ flat_map qb_chunks T') XB ch).
    - rewrite Ebeg. eapply AREPQ_perm; [exact PXC| apply Permutation_refl| exact RQ].
    - exact CHIN.
    - exact QUAR.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - exact HI.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - clear - SPT SPR; unfold spv in *; olia.
    - exact CBC.
    - exact OK1.
    - rewrite VIS1, Ebeg. unfold wz, T0, spv. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    destruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x52358)) with (ret_pc (Z_to_bv 64 0x52358)) in VIS2. rewrite (ret_pc_even 0x52358) in VIS2 by (clear; olia).
    (* [comment removed for export] *)
    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    assert (INB : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    assert (PZb : forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> pendz (a_st s) XB a).
    { intros a Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b) a INB); [| exact Ha]. rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact CLb0. }
    assert (MB2 : memB m2 b T' j0).
    { pose proof (TOK_tail b T' TK) as (OKT' & _ & _ & _ & CLT').
      assert (LW : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in Kb5; clear - Kb5; olia).
      unfold memB. unfold kBatchSize, kBatchCount in *.
      split; [| split; [| split; [| split; [| split; [| split]]]]].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b0) a); [| | exact Ha].
        + eapply Permutation_in; [apply Permutation_sym; exact PXB| right; apply in_map; exact Hb0].
        + rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia.
      - eapply (rw_cells_transport_pt2 _ m m2 AGP2); [exact HB|]. cbn [cells_size csize Nat.add]. intros a Ha. apply PZb. left. clear - Ha; olia.
      - eapply (u64arr_transport_pt2 _ m m2 AGP2); [exact ARR|]. rewrite LW. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (stk_transport_pt2 _ m m2 AGP2); [exact STB|]. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (poisoned_transport_pt2 _ m m2 AGP2); [exact POI|]. intros a Ha. apply PZb. right.
        change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. clear - Ha; olia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_next_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b)); [exact IR| clear - Kb4; olia| clear - Kb1; unfold AHI_LO in Kb1; olia| clear - Kb2 ACR; olia]. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.
    (* [comment removed for export] *)
    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (CU2 : CUR s2 m2 mo3 (rest' ++ flat_map qb_chunks T') XB).
    { split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]. }
    assert (MF2 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB rest' raccB) (a_st s2)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      destruct (MOD2 stB SB) as (stC & ev & CR & SC). rewrite Ebeg in CR.
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite CR. reflexivity. }
    destruct rest' as [|mi' rest''].
    + (* [comment removed for export] *)
      replace (i + 1 =? qb_count b) with true in VIS3.
      2: { symmetry. apply Z.eqb_eq. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      eapply (batch_phase b T' _ XB s2 m2 mo3 msF3 j0); [exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
    + (* [comment removed for export] *)
      assert (NEQ : i + 1 <> qb_count b).
      { pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      replace (i + 1 =? qb_count b) with false in VIS3 by (symmetry; apply Z.eqb_neq; exact NEQ).
      eapply (IH b T' _ XB s2 m2 mo3 msF3 j0 (i + 1)); [discriminate| clear - I0; olia| | exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
      rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, <- EQR by (clear - I0; olia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma head_body : forall (T' : list qbatch) (b : qbatch) s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6,
      HEADINV (b :: T') s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach bsegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).
  Proof.
    intros T' b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV HK K.
    destruct HINV as (RL & CU & ST & PXC & PXB & TK & HM & MF & OK & VIS).
    pose proof CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_deq sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO HI SPT OKL PW); [exact MI| exact OKT| exact SUBT| exact NDT| exact BST| exact HM]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    destruct VIS1 as (m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & FR1 & HB1 & ARR1 & STB1 & POI1).
    assert (WL : wlocal [(T0, T0 + 32)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s m mo XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s m mo _ m1 mo1 RL WL MU1 WM1 SBM1) as RL1.
    pose proof (stk_local _ m m1 spv ST WL ltac:(clear; olia) MU1 WM1) as ST1.
    assert (MB1 : memB m1 b T' j0) by (exact (conj HT1 (conj BSG1 (conj FR1 (conj HB1 (conj ARR1 (conj STB1 POI1))))))).
    assert (MF1 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB (qb_chunks b) raccB) (a_st s)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [| exact SB]. rewrite EQ. apply do_recycle_cons. }
    destruct (Z.eqb_spec (qb_count b) 0) as [C0|C0].
    - (* [comment removed for export] *)
      assert (CH0 : qb_chunks b = []) by (clear - Kb5 C0; unfold zlen in Kb5; destruct (qb_chunks b); [reflexivity| cbn [length] in Kb5; exfalso; olia]).
      rewrite CH0 in MF1.
      eapply (batch_phase b T' XC XB s m1 mo1 msF1 j0); [exact RL1| exact CU1| exact ST1| | exact PXB| exact TK| exact MB1| exact MF1| exact OK1| exact VIS1| exact HK| exact K].
      cbn [flat_map] in PXC. rewrite CH0 in PXC. exact PXC.
    - (* [comment removed for export] *)
      eapply (chunk_phase (qb_chunks b) b T' XC XB s m1 mo1 msF1 j0 0); [ | clear; olia| reflexivity| exact RL1| exact CU1| exact ST1| exact PXC| exact PXB| exact TK| exact MB1| exact MF1| exact OK1| | exact HK| exact K].
      + intros E. apply C0. rewrite Kb5, E. reflexivity.
      + rewrite VIS1. replace (qb_addr b + 152 + 8 * 0) with (qb_addr b + 152) by (clear; olia). replace (16 + 0) with 16 by (clear; olia). reflexivity.
  Qed.

  Lemma head_phase : forall (T' : list qbatch) (b : qbatch) s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6,
      HEADINV (b :: T') s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 ->
      (forall msF' mo', dr_post msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo).
  Proof.
    induction T' as [|b' T'' IH]; intros b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV K;
      (eapply head_body; [exact HINV| | exact K]).
    - intros NE. exfalso. exact (NE eq_refl).
    - intros _ s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' HINV'.
      eapply IH; [exact HINV'| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem do_recycle_arepq : forall (msF : machine_state) (XC XB : list Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      CUR s0 m0 mo0 XC XB -> stk bsegs m0 lo T0 ->
      Permutation XC (flat_map qb_chunks T0L) -> Permutation XB (map qb_addr T0L) -> TOK T0L ->
      rw_cells bsegs m0 T0 [C8 (wz (zlen T0L)); C8 (wz (hd 0 (map qb_addr T0L))); C8 (wz (last (map qb_addr T0L) 0)); C8 (wz (bsum T0L))] ->
      batches_rep m0 T0L ->
      lzok bsegs (a_L s0) (a_S s0) (a_Zr s0) (mkCfg msF mo0) ->
      restrict (a_L s0) (a_S s0) msF
        = MS (mkR (wz 0x5209c) (Z_to_bv 64 T0) gp tp t0 t1 t2 rs0 rs1 (wz (AINST + OI_Q)) (Z_to_bv 64 T0) ca cs a4 a5 a6 a7
                  rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x52294) fc None m0 (seg_rom bsegs) ->
      (forall msF' mo', dr_post msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) ->
      sreach bsegs Q (mkCfg msF mo0).
  Proof.
    intros msF XC XB t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 CU ST PXC PXB TK HT BR OK VIS K.
    pose proof CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    assert (RL0 : REL s0 m0 mo0) by (apply REL_refl; apply avmx_same; reflexivity).
    apply (proj2 (bseg_batches m0 T0L)) in BR.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s0) (a_S s0) (a_Zr s0) _ msF _ mo0 Q OK VIS).
    { eapply (dr_entry sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO HI SPT OKL PW T0L); [exact MI| exact ST| exact OKT| exact SUBT| exact BST| exact HT| exact BR]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    destruct VIS1 as (a1' & j0 & m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & REST1).
    assert (WL : wlocal [(spv, T0)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s0 m0 mo0 XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s0 m0 mo0 _ m1 mo1 RL0 WL MU1 WM1 SBM1) as RL1.
    destruct T0L as [|b T'] eqn:ET.
    - (* [comment removed for export] *)
      apply K. unfold dr_post. exists s0, t0, t1, t2, (wz 0), a1', ca, cs, a4, a5, a6, a7, t3, t4, t5, t6, m1.
      split; [exact RL1|].
      split. { cbn [flat_map map] in PXC, PXB. apply Permutation_sym, Permutation_nil in PXC. apply Permutation_sym, Permutation_nil in PXB. subst XC XB. exact CU1. }
      split; [exact OK1|]. split; [exact VIS1|]. split; [exact REST1|]. split; [exact HT1|].
      intros stA racc SA. exists stA, racc. rewrite ET. split; [reflexivity| exact SA].
    - destruct REST1 as [ST1 FR1].
      eapply (head_phase T' b s0 m1 mo1 msF1 XC XB j0); [| exact K]. unfold HEADINV.
      split; [exact RL1|]. split; [exact CU1|]. split; [exact ST1|]. split; [exact PXC|]. split; [exact PXB|]. split; [exact TK|].
      split; [exact (conj HT1 (conj BSG1 FR1))|].
      split; [intros stA racc SA; exists stA, racc; rewrite ET; split; [reflexivity| exact SA]|].
      split; [exact OK1| exact VIS1].
  Qed.

End Loop.
End HCW.

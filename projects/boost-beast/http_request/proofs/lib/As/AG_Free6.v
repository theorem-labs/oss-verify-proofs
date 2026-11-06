(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocRep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint inb (W : list ivl) (a : Z) : bool :=
  match W with
  | [] => false
  | (lo, hi) :: W' => ((lo <=? a) && (a <? hi)) || inb W' a
  end.
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma inb_false_outside : forall W a, inb W a = false <-> outside W a.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_Free6.inb); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.outside); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.orb_false_iff); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.Bool.Bool.andb_false_iff); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Stdlib.ZArith.BinInt.Z.leb_gt); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@kc__2); constr:(@kc__3); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@a; @W; @H; @l; @p; @lemma; @B; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @H2; @H0; @__x3; @H1; @IH; @hi; @lo; @z|] "#&B#0#|#6###f#$#0#g#%#e#9#;#&#7#'#)#(#n#*#+#4#K#,#m#r#>#-#.#l#z#3#@#A#D#G#H#F#E#W#Y#Q#I#R#^#v#/#\#?#C#O#P#T#U#V#X#Z#[#a#b#d#k#o#s#t#w#x#y#u#{#]#|#}#B#5#8#M#N#<#i#h#:#L#=#J#S#`#_#j#q#p#c9#J%#k&#l%#m%#n%#I%#.%#o'#p*#q%#r$#s'#t,#u'#K)#v%#w'#x%#y*#z)#{+#$'US/S%,FD$K#L'FD)$#k#$C#j#%(#$KLLk###S*k##S*$j#&%S@VS0KLj#&S*#.'&%#US1S%,#D$K#L'%D)$#m#(#j#$C#VSACCWS2S%MI,#D$K#L'%D)$#k#$C#k##9#k#'?#j#(+#VS3ODVS4DMVS5$#,IDVS6$#$K#L$K&L$K&L#$#)&#VS3QFVS4FOVS5$#,MFVS6$#$K#L$K&L$K&L#$#%QF&FO#$#-#'MF#$#VSBG#/GNS&-*D$$#j#)4#VSC<;$K?L$K?L($#)<#$K9L$K9L($###5WSDGNSE0GN#719&D88#/GNS&8&#221j#)+#VSFs#,s#+&DO)1#&FQ(#.##@0GN-0ZS72&D11#11&#s##s##./GNS&1&#==<j#)*#VSGOD%MD);#%OF(.###s#+k#*GGXSHGGNN0GN:2_S8G%N$S9S73#>(D13(#s#0s#0;/GNS&3(#s#*s#*s#)j#),#VSIDM'ID)s#?##.s#00GNs##/_S8G.N-S:S;0#s#8s#2D/GNS&0%#s#2s#2s#1j#)'#UFD(B7##+k###s#7%OD&DM#$#-###1k###0%PI&IQ#$#-#'OI#$#j##7#&MS#%PM($#&OS$%S#O($#'S#Q%S+P&PS'#$#-#'S$P#$#k##)#j##+#&QS'%S,S#&S#S+#$#-#'S'S#US1S<US/S<2CIUSJC3C$F#USKCUSLCUSMS-4C#4CS-*C$S(#+'JEEH#RUSNE*C&S)'+*JEEH#RZSO+JEEHO5,JEEH$#6-JEEH#7.JEEH)(#VSP/HVS0KS=VSQDI$K#S=m$%#WSRCSSFXSTDI$#l#+*)#l#,98#l#->=#j#.C#j#/C#j#0G#&FD%FI##Mk###S.k##&#k#.C#k#/C#k#0G#&S$S,8#S$S>Il#1-%#.s#/s#.#Dj#2s#8#j#&s#5#U#Dj##s#C#%S$Q2CF3C#Is#2USUS-4C#*C#S)s#/+s#2JEEH#R*Cs#1S(%+s#4JEEH#R5s#5JEEHs#,#6s#6JEEH#7s#7JEEH's#1#l#+#s#+s#%l#,-s#:#l#-s#@s#?#j#.C#j#/C#j#0G#%FD&FI#M#k###S.k##&#k#.C#k#/C#k#0G#%S>S$8#S,S$Il#1-%#.s#Qs#P#Dj#2s#Z#j#&A#U#Dj##s#d#ZSVs#fs#es#[s#%#Dj#3s#h#V#FDj##s#o#j##s$3#YS?s$4s$Vs#o#Dj#3s#~#&IP%QI($###s#vj##s$[#%S#M&MP#$#-#'PO(s#ks#52CM3Cs#eF#*Cs#`S)s#_+s#cJEEH#R*Cs#aS(s#6+s#eJEEH#R5s#fJEEH%#6s#gJEEH#*Cs#eS(s#f+s#iJEEH#R*Cs#<S)s#g+s#kJEEH#R[SWs#lJEEH%#7s#mJEEH(s#g#l#+#s#as#[l#,0s#p#l#-s#vs#u#j#.C#j#/C#j#4C#&DI#s#9#k###S.%MF(s#;#k##%#k#.C#k#/C#k#4C#8S'S+PIl#1-$#.Bs$8#Dj#2s#$#j#5s#&#V#FDj##s$E#j##s%,#YS?s%-s%,s#.#Dj#&s$N#.s$Ts$Ns#5#Vs$Ys$X#Vs$bs$a#Vs$ps$o#Vs$|s${#Vs%/s%.#XSXCCOMWS2S%#I,#D$K#L'%D)$#m#)#j#$C#j#6s%m#j#%s%s#j#7C#j#8C#V#FDj#9C#j#9C#YSYCCs%[#Dj#$S%#YSZS%s%us%g#Dj#%s%|##"). Qed.
Lemma inb_true_not_outside : forall W a, inb W a = true <-> ~ outside W a.
Proof.
  intros W a. rewrite <- inb_false_outside. destruct (inb W a); split; congruence || (intros H; exfalso; apply H; reflexivity) || auto.
Qed.

Definition chim (W : list ivl) (m m2 : mem) : mem := fun x => if inb W (bv_unsigned x) then m x else m2 x.

(* [comment removed for export] *)
Lemma wview_pt : forall ma mb x, ma x = mb x -> wview asegs ma x = wview asegs mb x.
Proof. intros ma mb x E. unfold wview. rewrite E. reflexivity. Qed.
Lemma mrd_pt : forall ma mb x, ma x = mb x -> mrd asegs ma x = mrd asegs mb x.
Proof. intros ma mb x E. unfold mrd. rewrite E. reflexivity. Qed.

Section Chim.
  Variables (W : list ivl) (m m2 : mem).

  Lemma chim_in : forall x, inb W (bv_unsigned x) = true -> chim W m m2 x = m x.
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.
  Lemma chim_out : forall x, inb W (bv_unsigned x) = false -> chim W m m2 x = m2 x.
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.

  Lemma chim_mem_inv : mem_inv asegs m -> mem_inv asegs m2 -> mem_inv asegs (chim W m m2).
  Proof. intros M1 M2 a b E. unfold chim in E. destruct (inb W (bv_unsigned a)); [exact (M1 a b E)| exact (M2 a b E)]. Qed.

  (* [comment removed for export] *)
  Lemma chim_wmono_in : wmono asegs m m2 -> wmono asegs m (chim W m m2).
  Proof.
    intros WM x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)). exact Hx.
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)). exact (WM x Hx).
  Qed.
  Lemma chim_wmono_out : forall m3, wmono asegs m m3 -> wmono asegs m2 m3 -> wmono asegs (chim W m m2) m3.
  Proof.
    intros m3 W1 W2 x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)) in Hx. exact (W1 x Hx).
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)) in Hx. exact (W2 x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma chim_agree_in : agree_on (fun a => inb W a = true) m (chim W m m2).
  Proof. intros a Ha Hr. apply chim_in. rewrite wa_unsigned by exact Hr. exact Ha. Qed.
  Lemma chim_agree_out : agree_on (outside W) m2 (chim W m m2).
  Proof. intros a Ha Hr. apply chim_out. rewrite wa_unsigned by exact Hr. apply inb_false_outside. exact Ha. Qed.
  (* [comment removed for export] *)
  Lemma chim_agree_trans : forall (P : Z -> Prop) m3, (forall a, P a -> outside W a) -> agree_on P m2 m3 -> agree_on P (chim W m m2) m3.
  Proof.
    intros P m3 SUB AG a Ha Hr. rewrite (AG a Ha Hr). symmetry. exact (chim_agree_out a (SUB a Ha) Hr).
  Qed.
End Chim.

(* [comment removed for export] *)
Section PtEq.
  Context {HCEIL : HeapCeil}.
  Variables (P : Z -> Prop) (m m' : mem).
  Hypothesis AG : agree_on P m m'.

  Lemma bytes_at_pteq : forall A bs, bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (mrd_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma wr_at_pteq : forall A n, wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
  Proof.
    intros A n (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (wview_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma rw_cells_pteq : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HP. split; [split; [exact Hwf|]|].
    - apply bytes_at_pteq; [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact HP.
    - apply wr_at_pteq; [exact Hw| exact HP].
  Qed.
  Lemma stk_pteq : forall lo hi, stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hw [b Hb]].
    assert (E : m' (wa a) = m (wa a)) by (apply AG; [apply HP; exact Ha| lia]).
    split; [rewrite (wview_pt m' m _ E); exact Hw| exists b; rewrite (mrd_pt m' m _ E); exact Hb].
  Qed.
  Lemma u8arr_pteq : forall A bs, u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
  Proof. intros A bs [Hb Hw] HP. split; [apply bytes_at_pteq; [exact Hb| exact HP]| apply wr_at_pteq; [exact Hw| exact HP]]. Qed.
  Lemma u32arr_pteq : forall A ws, u32arr asegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HP. split; [| apply wr_at_pteq; [exact Hw| exact HP]].
    apply bytes_at_pteq; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HP. lia.
  Qed.
  Lemma u64arr_pteq : forall A ws, u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HP. split; [| apply wr_at_pteq; [exact Hw| exact HP]].
    apply bytes_at_pteq; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HP. lia.
  Qed.
  Lemma poisoned_pteq : forall A k v, poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v (H0 & H8 & U8) HP. split; [exact H0|]. split; [exact H8|]. apply u8arr_pteq; [exact U8|].
    unfold poison_bytes. rewrite repeat_length. exact HP.
  Qed.
  Lemma junk_pteq : forall lo n, junk m lo n -> (forall a, lo <= a < lo + n -> P a) -> junk m' lo n.
  Proof. intros lo n J HP POS. apply stk_pteq; [exact (J POS)| exact HP]. Qed.
End PtEq.

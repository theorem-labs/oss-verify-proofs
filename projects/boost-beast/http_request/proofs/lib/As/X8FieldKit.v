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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP N8Kit N8Kit2 N8Kit3 X8Kit X8Call X8LeafKit X8StateKit X8StateKit2 X8StateKit3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BW.
  Context {HCEIL : HeapCeil}.

  Lemma bytes_le_to_Z_range8 : forall bs : list byte, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
  Proof.
    intros bs L. rewrite Bytes.bytes_le_to_Z_le_val. pose proof (Bytes.le_val_range (map bv_unsigned bs) (Bytes.bytes_ok_map bs)) as R.
    rewrite length_map, L in R. change (256 ^ Z.of_nat 8) with (2^64) in R. exact R.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes); constr:(@Corelib.Init.Datatypes.length); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.lor_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Numbers.BinNums.N); constr:(@Stdlib.ZArith.BinInt.Z.shiftl_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@stdpp.tactics.f_equal_help); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.False); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.shiftr_div_pow2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Bytes.lor_shiftl8_add); constr:(@Stdlib.micromega.Tauto.X)|] [|@bs; @__ff; @__varmap; @__wit; @__arith; @b; @a; @n; @H; @IHc; @cs; @c; @z; @b2; @b1; @__x1; @__x2; @__x3; @__x4; @H0; @r; @q; @H3; @H2; @H1; @__p1; @NN; @Hb; @IH|] "#)$#2$7#J#O#D###P#N#%#$#&#'#T#(#H#S#9#a#c#+$%$+$.#2#-#.#5#@#A#W#X#`#:#h#)#l#p#*#q#r#,#s#}#x$&#0#i#7#I#K#M#U#Y#Z#V#]#b#j#k#m#u#t#z#y$$$#$,$-$1$2#1$3$4#/$5$6$8$7#C#;#E#B#>#F#Q#L#f#e#w$(#8#n#o#{#6#<#|$)#=#^#?#\#[#~$*$0$/#G#R#_#g#v$'#dI#o%#p&#q%#r%#s$#t%#u'#v*#w%#x%#y&#z+#{$#3&#|%#}%#~%$#$$$%$%$$&*$'%$(%$)%$*%$+(#&&$,%$-%$.&$/&$0$$1%$2$$3%$4%$5%$6)/Q/#/#US@#4#US+#8$F'F5$#$&#Fj#$'#US,):)#VS-,I%-I#E#B/(%#&%##E.j#$1#US,OUS+OUSACUSBCUSCCCCE)C#P#*%HDDG#MVSD&G:S.S/VSEFI$S.#S/m$%#WSFCEJXSGFI$#l#%*)#l#&0/#l#'32##EEl#($#Fm##$'A#E#m#%#;JF#E##EI#EJ&$#k##&##EF&&#;IJ#E#k##%#&(#;KI#E#k##,#j##&#j##$Fj##.#VSHJF<0+&$#j#)C#j#*C#k#)C.k#*C#%s#DK'IDs#G9$##E&#E$4F%JF#E#BJ(%#&%#%IJ#E#j##%#BI(&#j###Jj##,#VS-JF<.,($#j#)1#j#+R#k#)31k#+R#VFs#]Ll#,&$#9JF#E#k###s#59IJ#E#k##s#7#&&#9KI#E#k##s#<#j##&#j##$Fj##,#VSIJF<.+&$#j#+C#j#*C#k#+C.k#*C#'K=#s#/Il#,'%#XS0s#/s#.9#=s#4s#1#l#,s#8s#6#0s#wIJ'##E#m#&#j#-s#l#j#.s#{#j#/s#}#YS1s#~s#ns#V#I#Es#=%s$%L/s$'/#/#/#/#D#+#8,*#Es$.F8s$.LVS2Fs#H5$#0s$1&#0s$2NL$s$2$#j#0C#Es$6+VS#s$6#VS#s$7L8s$8KVS2/s#R5$#k##s$:s$:US#s$<k##s$=$:#$4J4I$#JF%KI%KJ$C$#k##&#%IF$Cs#V#4K$#IJk##%#&(#4L$#KIk##,#j##&#j##$Fj##.#WSJIJF<0+&$#j#17#j#2s#j#j#+R#k#1:/k#2s#m#k#+R#%s$[N'L+s#4#,%#Es$_#VSKs$`$%s$aS3$CF#j#0C#VS4(s#;$Cs#<EUSL#'N+s#?#,*#1#s#A+s#B#2%s#C,$#$C'#k##+#VS5)s#G(Es#H%s$rS6'S3+s#K#,%#2#s#M#E#($s#O&$#k##+#VS7(s#R(s#SE%s$}S$'S6+s#V#,%#2#s#X(s#Y##$E&$#k##+#VS8(s#]%s%+S9'S$+s#`#,%#1#s#b$C#Ek##s#*#VS:&s#e%s%3S)'S9+s#h#,%#2#s#j$C#$k##s#2#1&s#m%s%;S*'S)+s#p#,%#2#s#rVSMEs#s:SN#m##s#/UN#(Fs#w&s$q#USOQVSPC#6S;6#6#3C#WS<C'#3CS;-C$#VSQCs$&WSRC#%6)6#3C#3C%-C#,-C%#-C)#>#S%F-#-C1/6+3C#WS<C8+3C7-C$#-C&#-C3#>#S%F+#0O#s%R0O.#GCLXS=C#Is%SGCKXS=C$J#?CQ)Cs%TP#*s%VHDDG#MCCs$D)C&S&#*s%YHDDG#M7s%ZHDDG&#USSD)C'S's%[*s%]HDDG#MZSTs%^HDDG#?Cs%xUSUQ?C#@C-#AC&#?Cs%|@C0#AC#4)C&S'#*s%hHDDG#M.s%iHDDG-0#)Cs%iP-*s%kHDDG#M)C/S&7*s%mHDDG#M7s%nHDDG%#)C=S'2*s%pHDDG#M.s%qHDDG%8#.s%rHDDG+9#.s%sHDDG;:#l#%#s%ps%jl#&s#$s%v#l#'s#)s%y#j#3C#j#4C#j#5C#j#6C#k##s$.SV+s$iL,K#+s$kN,#I$C%#k##(##EK(Ks$p&$#$CKLk##$#k##(#k##s#[#k#3C#k#4C#k#5C#k#6C#'S>%s&HSW[FK$#IJS$S*l#(8&#%s&KS>$CJ#m#%#l#7s#is#g#l#8s#nC#l#9s#tC#l#:s#}s#v#l#;s$*s$##l#<s$6s$,#l#7s$Bs$8#l#,s$Os$D#%s&Vs$UVSXs&Ws$WHCs$Vs$S%$#XFs&Ys$XN#l#,s$as$^#\S?s&Zs$}s$|s$|s%'Ls$z#Ds&_VSY#s%u1s%3#5s%2F$s&^#Lj#0C#VS4s%7s%91s$cs%:+s%;#2s$es%<,$#$Cs$g#k##s$`#VS5s$is%@#Es$\(s$]s%B&$#k##s$Z#VS7s$cs%E(s%Fs$W#s$XE&$#k##s$T#VS8s$\s%J1s$Rs%K$C#Ek##s$o#VS:s$Us%N2s$Ls%O$C#s$Mk##s$s#-Cs#{s$--Cs$3#-Cs$+#>#S%3Cs$9-Cs$6#-Cs$0#-Cs$7%>#S%F%#0O#s&s0O*#)Cs&pPs#k*s&rHDDG#M)Cs#mS&s#z*s&tHDDG#M7s&uHDDG%#@Cs#}s$$ACs#t#@Cs$#s#wAC#s#s)C%S'#*s&{HDDG#M.s&|HDDGs#|s$##)Cs&|Ps#z*s&~HDDG#M)Cs#|S&s$**s'$HDDG#M7s'%HDDG%#.s'&HDDG#s$)s#p.s''HDDG)s$*#.s'(HDDG1s$+#l#%#s'%s&{l#&s$5s'+#l#'9s'.#j#3C#j#4C#j#5C#j#6C#+s%yI,L#+s%{K,#N$C%#k##s#t##EL(Ls&$&$#k###s#nk##'#k##s#q#k#3C#k#4C#k#5C#k#6C#'SZ[FIs#jK#JS$S)l#(5%#'S*$C#Im#%#l#7s$ws$u#l#8s%(C#l#9s%1C#l#:s#Fs#C#l#;s#Ks#H#l#<s#Qs#M#l#7s#Ws#S#l#,s#_s#Y#1s&9s&;$Cs&Q#8s'eN5#F$s'f#Nj#0C#ZS[Cs%l#Ks#eFl#,*(#CCs'()Cs'VP#*s'XHDDG#Ml#%#s'Us'Ol#&s'\s'[#l#'s'_s'^##Es'.l#($#Fm##$WS\s&Js'1#HCs#vs#s-s&>#\S?s'us'us&Bs&As&>Ks#z#9s&ds'4;s&V##Es&W(s&Xs&RGCJZS]s'gHDDGK7s'hHDDGs$p#.s'iHDDG#s$ls$ql#%#s'fs'`l#&'s'l#l#'s'ps'o#j#3C#j#=S(#&s'UJk###s'Yk#3C#k#=S(#(s&0s&`=#s&1Il#()%#m##47s'wHDDG2s$|.s'xHDDG#s${s$}l#%#s'us'ol#&6s'{#l#'s(#s'~#j#3C#j#=S(#&Js%R(Js&lk##$#k#3C#k#=S(##Es&@=#s&AIl#(*%#m##s##XS0s#%s#$3#&s#&s#%m#$#.s(.HDDGs%6s%1s%6l#%#s(+s(%l#&s#(s(1#l#'s(5s(4#j#3C#k##s'us'xk#3C#VFs&MJl#(&$##Es'9m#$#XS^s',s';.#HCs'%s&ys#7s#5#l#>s'0s'/#l#?s(Hs(C#8s(Rs'95#s'9$s(S#s';m#&#j#@s(Q#j#$s(V#j#)s(X#YS1s(Ys(Ss(Q#Fj#$s(Y##"). Qed.

  Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
  Proof.
    intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
    rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_range8 bs L).
    change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_CB8_C8 : forall m A bs cs, rw_cells asegs m A (CB 8 bs :: cs) -> exists w, rw_cells asegs m A (C8 w :: cs).
  Proof.
    intros m A bs cs R. assert (L : length bs = 8%nat) by (destruct R as [[[L _] _] _]; exact L).
    destruct (le8_surj bs L) as [w Hw]. exists w. destruct R as [[[_ W] B] R']. refine (conj (conj (conj I W) _) R').
    cbn [cells_bytes cbytes] in *. rewrite Hw. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma cells16_words : forall m A cs, rw_cells asegs m A cs -> cells_size cs = 16%nat ->
    exists w1 w2, rw_cells asegs m A [C8 w1; C8 w2].
  Proof.
    intros m A cs R SZ.
    destruct (rw_cells_forget _ _ _ _ R) as [j R16]. rewrite SZ in R16.
    destruct (rw_cells_CB_split asegs _ A 16 8 j R16 ltac:(lia)) as [R1 R2]. change (16 - 8)%nat with 8%nat in R2.
    destruct (rw_cells_CB8_C8 _ _ _ _ R1) as [w1 W1]. destruct (rw_cells_CB8_C8 _ _ _ _ R2) as [w2 W2].
    exists w1, w2. apply (proj2 (rw_cells_app asegs m A [C8 w1] [C8 w2])). split; [exact W1|].
    cbn [cells_size csize Nat.add]. exact W2.
  Qed.

End BW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section IMG.
  Context {HCEIL : HeapCeil}.
  Lemma img_tlit_ok : forall m, ACONST m -> accessible m AL_TAB_IS_TOKEN_LIT 256.
  Proof. intros m AC. apply (ACONST_gbody_accessible m AL_TAB_IS_TOKEN_LIT 256 AC). vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition pf_side (m : mem) (B E p0 n lo shi : Z) : Prop :=
    pside2 m lo shi [(p0, n); (E, 24); (B, 4104)] [(p0, n); (E, 24); (B, 4104)].

  Lemma pf_side_intro : forall m B E p0 n lo shi,
    ACONST m -> stack0 m lo shi -> AXStatics2 m -> accessible m p0 n -> accessible m E 24 -> accessible m B 4104 ->
    shvis m p0 (p0 + n) -> shvis m E (E + 24) -> shvis m B (B + 4104) -> aapp p0 n -> aapp E 24 -> aapp B 4104 -> 0 <= n ->
    pf_side m B E p0 n lo shi.
  Proof.
    intros m B E p0 n lo shi AC SK XS AW AE AB SVW SVE SVB APW APE APB N0. apply pside2_intro; [exact AC| exact SK| exact XS| |].
    - apply Forall_cons; [exact AW| apply Forall_cons; [exact AE| apply Forall_cons; [exact AB| apply Forall_nil]]].
    - apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd]; apply shv_entry; try assumption; lia.
  Qed.
End IMG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac acc_chkw AW a BT PRE :=
  lazymatch type of AW with accessible ?mc ?O ?n =>
    let v := fresh "v" in let V1 := fresh "V1" in let V2 := fresh "V2" in let RD := fresh "RD" in
    let B1 := fresh "B1" in let B2 := fresh "B2" in
    assert (B1 : O <= a) by BT; assert (B2 : a + 1 <= O + n) by BT;
    destruct (accessible_readw_sr mc a 1 (accessible_sub _ _ _ a 1 AW B1 B2 ltac:(clear; lia))
                ltac:(clear; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as (v & V1 & V2 & RD);
    clear B1 B2;
    PRE; clear RD;
    first [ rewrite (sxb_b8_small v) by (clear - V1; lia) | rewrite (zxb_b8_small v) by (clear - V1; lia) ];
    shchk_join V1 V2; clear V1 V2
  end.

Ltac acc_chkw_ge AW a BT PRE :=
  lazymatch type of AW with accessible ?mc ?O ?n =>
    let v := fresh "v" in let V1 := fresh "V1" in let V2 := fresh "V2" in let RD := fresh "RD" in
    let B1 := fresh "B1" in let B2 := fresh "B2" in
    assert (B1 : O <= a) by BT; assert (B2 : a + 1 <= O + n) by BT;
    destruct (accessible_readw_sr mc a 1 (accessible_sub _ _ _ a 1 AW B1 B2 ltac:(clear; lia))
                ltac:(clear; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as (v & V1 & V2 & RD);
    clear B1 B2;
    PRE; clear RD;
    first [ rewrite (sxb_b8_small v) by (clear - V1; lia) | rewrite (zxb_b8_small v) by (clear - V1; lia) ];
    shchk_join_ge V1 V2; clear V1 V2
  end.

(* [comment removed for export] *)
Ltac acc_chktl AC x PRE :=
  lazymatch type of AC with ACONST ?mc =>
    let RD := fresh "RD" in
    pose proof (accessible_read0_in mc AL_TAB_IS_TOKEN_LIT 256 x (img_tlit_ok mc AC)
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold AL_TAB_IS_TOKEN_LIT; lia)) as RD;
    unfold AL_TAB_IS_TOKEN_LIT in RD;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

Ltac ps_chktl SD MU WM FW x PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let ACc := fresh "ACc" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (pside2_aconst _ _ _ _ _ SDc) as ACc; clear SDc;
    acc_chktl ACc x PRE; clear ACc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Ltac unpark H := unfold parked in H.

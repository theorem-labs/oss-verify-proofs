(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import STRW_merge.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

(* [comment removed for export] *)
Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

(* [comment removed for export] *)
Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)
Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
  (0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
  eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
  rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Lists.ListDef.skipn); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.STRW_tac.ld_facts); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Corelib.Init.Logic.ex); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Nat.min); constr:(@Stdlib.Lists.List.length_firstn); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.Lists.List.length_skipn); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.Arith.PeanoNat.Nat.min); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_min); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.min_spec); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_read); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.window_sub)|] [|@w; @a; @n; @x; @y; @m; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__p4; @__arith; @z5; @H5; @z4; @H4; @z3; @H3; @cstr2; @cstr1; @cstr0; @cstr; @HW0; @HL0; @Hc0; @HW; @L0; @__x7; @__x8; @__x9; @z6; @H6; @L; @H; @Hi; @Hc; @Hb; @HL; @SRC; @i; @c; @xsw; @base; @kw; @src; @S; @segs|] "#.C#I$X#S$?$@$>#`#T###e$H$/#$#,$6#)#(#*#-#8$J#I$N#%#+#9#6#:#'#2#7#0#5#&#/#.#;#4#<#?#3#>#B#d#b#_#1#Y#v#w#t#Q#y$F#V$##C#O#N#R#]#i#Z#n#p$'$($%$&#@#D$-#E$L$M$R$S#G#=#A$W#^#M#U#[#k#|#~#}$5$4$7$:$;$=$K$P$T$U$Q#H$X$Y#F$V$1#a$D$C$.$<#r$0#z$+$B$,$8$2#\#c$$$E$O#X#m#u#s#P#W$)$9$A$*#f#{$I#h#o$3#x$G#L#g#l#q#jU#W&$.&$/%#N%$0'$1*#*$$2&#L%#_%$3+$4%$5%$6%$7%$8*$9%$:'$;%$<$$=%#M%$>%$?%$@&$A&$B%$C5$D/$E$#P$$F&$G$$H%$I*#X%$J%$K$$L'$M)$N'$O%$P&$Q/$R$$S$$T%$U)$V'$W)PSc@SD@#@#@#@#@#USJ#USK#USJ(USK#USL#k##&#P%XSdNS)RPAQ<(#RB)P##'#S-,+Q#H#R6SM6#6#6#YSeRQ#S)S-&GS)7P%8#N)P+S)##CQ#%&#%)#+S3PH##>Q#USL:KS9S.R0VSN<I#%$#<ANS#BB4##@I#,s#$I#H#7%%#%)#j#$s#%#Qs#&#k##0#j##4#7R>8#S#)R+N##CP#%&#&GS#7Ns#%8#S3)N+S4##CS)#%&#7S#s#+8#S0)S#+S3##CN#%&#+S9S#H##s#CN#KS/S+S4s#4#s#(#s#&<s#DS0S?Bs#Es#7##s#CI#%#s#$%'#j#$s#F#Qs#G#k##,#j##0#)S4+S0##CS##7S3s#B8#S.)S0+S.##CS3#+S+S0H##s#YS3#+S/S?H#KS5S,Ms#L#s#@#s#><s#\S6S1Bs#]s#O##s#[I#%#s#<%'#j#$s#^#Qs#_#j#%s#e#USOs#dAS6<s#f#S+Bs#gS1#ZSfs#eH&#S9S4,s#i$,s#jS9#H$#AS1<s#m#S/Bs#nS+#,s#o#,s#pS1#HI#j#&H#,s#s(=S+#WSPs#uS+*RH)&I$#,s#wS6#H&#AS+<s#z#S$,s#{#=S$I,s#}S+#H$#j#&H#,s$$S$L#*WSQs$&+S$RH*&I$#=S/%#H#7,s$*S,AS$L$#=S*##H#Ij#&H#RH1#IS$S0,s$1S*AS/L$#=S$##H#S$7-S*8#/.GS$)S*+$#)3&$#j#'CI.GIj#'C#0CS$NCHCCS@&J$SES$S$#0C+>HHHCCCSAJJJS<SB:-$S*,#0C+?HCS=JS>SC1-$=,#7S+s$88#S*)S+USgs$Q+$#&#40C&0C&>HHHCCCSAJJJS<SBS+($s$@'#?HCS=JS>SC+'#S*8/I+'#P#Hs#/S,)s#0)S,#C$#USGHUSGC)M)I#C$##HMIVShMIWSi%$#j#(H#j#'H#0C/0C/?HC.J-%s#?1$S,0#I30#S.,s$cS7AS,L$#=S5##H#S5)S5)(.GS,9$#.G#F'##C#(9MI.G#j#)C#j#&C#Us#6S,V$-#F/#0C00C00CS,NCHCCS@s#>Js#<SES,S,#>HHHCCCSRJJJ*SS93%8)#>HHHCCCSTJJJSHSUS55'8)#?HCs#)Js#(@8)#S56(I81#S(Cs#V&Gs#F,s%$S:C#)$&G#CS5&G?CS8)S8&G#GGS83GS8.GS8#C#S8%%#&S8G#C&G%$#1&#.GSV,s%7SI)#9#IGG#3G$.G%#C#&%%#&(G#C&G%$#1&#,s%CSW)#9#M.G#)SWVSX#I3$IF%I#C#&%%#&I(#C&I%$#1&#)SYF#M6s%E5C#5Cs%G5Cs%IUSjSDVSkC#5Cs%MMC$#5Cs%P$C$#$C)#$C+#$C-#/#O5CSM$C*#$C0#$C2#/#O$C3'$C5#/#O$C50$C7#$C9#/#OUSlL*L$#*L)#*L-#*L3#PLDCQUSmC4C$P#DCS-4C$S(#DCP4C#P'4C#S2(4C&M#USnCUSoC:Cs&+Os&+:C#'C%SF#('FDDE#KJ(FDDES)2)FDDE$#J*FDDEN:Cs&1'C#S%)(-FDDE#K2.FDDE&#E/FDDE(#USpDJ1FDDES#OSD:C#:CSDWSZC$#'C3S%#(7FDDE#K28FDDE)#J9FDDES4VS[CG'C8S%#(<FDDE#K2=FDDE&#E>FDDE(#@/:C#'C)S'#(BFDDE#K'C:S%B(s#$FDDE#KVS[Cs$Y;C(#'C#S's#&(s#(FDDE#K;C7s#('C#S'9(s#+FDDE#K-s#,FDDE&>#-s#-FDDE+?#-s#.FDDE.@#-s#/FDDE3A#-s#0FDDEs##B#VSqs#1E0S\S]VSrIS(#S\#S]m$%#WSsCGMXStIS($#l#**)#l#+s#;s#:#l#,s#Fs#E#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#3S&#j#4S&#j#5S&#j#6S&#3MQ%#P#CS-Q%R#1%#9S2M#CP#%N##CPG%S##1%#&GQ#CRS-+Rs%*&#Q+QP&#Rk##%#k##(#k##*#k##,#k##3#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#3S&#k#4S&#k#5S&#k#6S&#,s'(Su)#9#Q&#G3G$)S^&S2##CM$cI'&$#S2Ms$G)%QS(S-S)S4S0l#7s#,,#l#8s$>C#l#9s$Is$A#l#:s$LC#l#;s$Ys$Q#l#<s$^C#l#=s$hs$`#l#>s$ls$j#l#?s$os$n#l#@s$ss$q#l#As$ws$v#l#Bs$ys%,#l#Cs%9s%G#l#Ds%Ls%Q#Ss%fs%as%X#l#Es%ns%i#l#Es%xs%v#l#Es&*s&(#l#Es&9s&6#7s&=S18#s&&+S*S9H#KS5S,#s':#s'.#s',%#s&Ij#$s'H#AS.<s'M#S/Bs'Ns'@#+S$S.H#KS,S*#s'CVSNs'O&#s'8$#<s'TS9S6Bs'Us'G##s'S*#,s'W+#H#s'J%%#7s&LS+,s'[S/8$#.GS1+#s%t)&&$#Us&$S1+#s%x0CS1NCHCCS@s&)Js&'SES1S1#>HHHCCCSAJJJS<SBs&W&#S+s%{s%w0C)?HCS=JS>SC/'$.*#I.*#I7S6s'[8#S/)S6+#s&%)S/&$#0C&>HHHCCCSAJJJS<SBS6'#s'bs&)s&%0C&?HCS=JS>SC+($S/'#I+'#S-#Hs&US$)s&V)S$#C$#0C%0C%?HCs&'Js&&s%zs&['$S$&#I)&#S0Cs##&G@,s'~S5C#)$&G#CS$&G/CS7)S7&G#GGS73GS7.GS7#C#S7%%#&S7G#C&G%$#1&#.GS_$Cs%8s%2$Cs%:#$Cs%?#/#O*L#s%*DCS(DCS24C$M#'Cs$bS's$i(s${FDDE#K;Cs${s$k'Cs$kS%#(s$~FDDE#K'Cs$gS's$~(s%$FDDE#K'Cs$iS's$o(s%&FDDE#K-s%'FDDE%s$u#-s%(FDDE(s$v#-s%)FDDE,s$w#l#*#s$Ws$Ql#+0s%,#l#,4s%7#j#-C#j#.C#j#/C#&GS(+S(S2#CM#&GS2k####k##%#k##(#k#-C#k#.C#k#/C#)S_ZI#S8S7S-S3S6l#7/%#l#<s#*C#l#=s#4s#,#l#>s#8s#6#l#?s#;s#:#l#@s#?s#=#l#As#Cs#B#l#Cs#Es#I#l#Ds#Ns#S#l#Fs#Zs#b#7s#ws(W8#s#i.GS.+#s&}&#s#h0CS.NCHCCS@s'0Js'.SES.S.#>HHHCCCSAJJJS<SBs#~'#s(^s'%s&}?HCS=JS>SC*'#s#ps#ls#eGGS*3GS*.GS*#C#S*%%#&S*G#C&G%$#1&#GGS:3GS:.GS:#C#S:%%#&S:G#C&G%$#1&#6s&/5C#MCs&,#$Cs&,s&$$Cs&0#$Cs&2#$Cs&4#$C'#/#O6+5C#$Cs&4s#X$Cs&8#$Cs&;#$C.#$C'#/#O/%O$C*-/#O*L#s&)*L&#*L(#*L1#4Cs&$S(s%~DCR4Cs&)S2#4C%M#'Cs%eSFs%l(s%~FDDE#K'Cs%aS%s%n(s&$FDDE#K2s&%FDDE%#'Cs%qS's%j(s&'FDDE#K'Cs%fS%s%l(s&)FDDE#K2s&*FDDE%#Es&+FDDE(#:Cs)S'Cs%wS%#(s&.FDDE#K2s&/FDDEs&'#'Cs%zS%s%t(s&1FDDE#K2s&2FDDEs&##Es&3FDDE&#Os)\:C#'Cs%zS'#(s&7FDDE#K;C%s%qOs&):C#'C%S'#(s&<FDDE#K;Cs%{%'C#S's&=(s&?FDDE#K;Cs&/-'C7S%#(s&BFDDE#K;Cs&1s%|'C#S's&C(s&EFDDE#K-s&FFDDE&s&8#-s&GFDDE*s&9#-s&HFDDE.s&:#-s&IFDDE4s&;#-s&JFDDE9s&<#-s&KFDDEBs&=#l#*#s%ys%sl#+s#/s&N#l#,s#4s&Y#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#GC#j#3S&#j#4S&#3GS(#CQS(%$#&S(G#CQG%$#1&##CMS-%S)##CMG%N#1%#&GP&s%qN+NS#&#Q+RN#CS)#+Ps(B&#Rk##%#k##(#k##+#k##-#k##/#k##5#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#GC#k#3S&#k#4S&#)S;cIs#}s$%#Ms'rS:S`s'eS2S(S-PS#S4S?l#7s#(%#l#:s'pC#l#;s$)s#}#l#<s(7C#l#=s$4s$,#l#>s${s$y#l#?s$~s$}#l#@s%&s%$#l#As%*s%)#l#Cs%,s%0#l#Ds%5s%:#l#Fs%As%I#Ss$Ds$As$=#]SvS,S*S$S/S.s*?S0s$G#_SwS/S6S1S+S9s*@S.S3RS2S(,s*Os%`=s*B##HIs*Cj#&H#Ls%Vs%e=s*FI#H#s*Gj#&H#=s*I&#H#s*J9s%Xs$P.G#Fs(p##C#s(q>HHHCCCSRJJJs(ISSs%`s%\s%Us%os$Ts$P>HHHCCCSTJJJSHSUs*Ps(ss(o-&#?HCs(hJs(gs(_*&#s*Qs(ts(p,s*`SV)#9#IGG#3G$.G%#C#&%%#&(G#C&G%$#1&#,s*lS`)#9#M.G#VSXs))I3s)*IFs)+I#C#s),%%#&Is).#C&I%$#1&#Fs)2MGGS;3GS;.GS;#C#S;%%#&S;G#C&G%$#1&#.GSI6s$Y6#6#5C#MCs(2#$Cs(5s(2$Cs(7#$Cs(9#$Cs$`#$C'#/#O5C-$Cs$ms(1$C$#/#O6/5C#$Cs(>s(<$Cs(B#$Cs(E#$Cs$l#$C3#$C(#/#O5C9MCs(G#MCs(Hs$r$C#s$o$C%#$C<#/#O$Cs$ws(D$C7#/#O$C*s$}$C,#/#O$C-s(J/#O$Cs#&&/#O//O/7O$C=s#$/#O*L#s(F*LB#*Ls###*L(#*L*#*L3#*L4#*L.#*L1#*L2#*L3#*L4#*L7#*L;#*L<#*L@#*Ls#(#*Ls#2#*Ls#3#*Ls#8#DCN4C#Ps(T4Cs(SS(#DCS)4C#Qs(W4C#S2s%34C&M#'Cs(9SFs(P(s(RFDDE#K'Cs$|S%s(R(s(TFDDE#K2s(UFDDE%#'Cs(US's(>(s(WFDDE#K'Cs%%S%s(@(s(YFDDE#K2s(ZFDDE%#Es([FDDE(#@s%*:C#'Cs(;SF#(s(_FDDE#K'Cs(NS%s(=(s(aFDDE#K2s(bFDDE%#'C(S's(@(s(dFDDE#K'Cs(SS%*(s(fFDDE#K2s(gFDDE%#Es(hFDDE(#WSZCs%1s(f'C/S%#(s(kFDDE#K2s(lFDDEs(U#'C&S's(U(s(nFDDE#K'C4S%s(W(s(pFDDE#K2s(qFDDE%#Es(rFDDE(#Js(sFDDES3'Cs(qS%s(c(s(uFDDE#K2s(vFDDE%#Js(wFDDES02s(xFDDE#s(^Es(yFDDE%#'Cs(bS's%P(s({FDDE#K;Cs%Rs(Y'C#S's(_(s(~FDDE#K;Cs%Ls(a'C#S's%H(s)%FDDE#K;Cs)%s%X'Cs(rS%#(s)(FDDE#K-s))FDDE#s(ws#&-s)*FDDE's(x#-s)+FDDE+s(y#-s),FDDE/s(z#-s)-FDDE2s({#-s).FDDE:s(|#-s)/FDDEs#%s(}#-s)0FDDEs#3s(~#l#*#s(^s(Xl#+s#@s)3#l#,s#Hs)>#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#GC#j#HC#j#IC#j#3S&#j#4S&#j#5S&#3GM#CS-M%$#&MG#CS-G%$#1&#3s*{N#CMs*|%$#&Ns*~#CMN%$#1&#9S)N#CS##%S4#&%G#CS#G%$#1&##CS#Q%S0#%S?'1$#&GR+S)s+2&#S#+S#S4&#S3+S)S##CN##CS)s+8k##$#k##'#k##*#k##-#k##/#k##4#k##<#k##s#$#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#GC#k#HC#k#IC#k#3S&#k#4S&#k#5S&#,s-8S^)#9#R3G#)Sx)SIhIs$ys$}%QR'$M#S;SYS2S(S-PS)S#S?S.S1l#7s#?*#l#Js$wC#l#Ks%%s$y#l#8s%'C#l#9s%1s%)#l#:s%3C#l#;s%@s%8#l#<s+:C#l#=s'7s'/#l#>s'~s'|#l#?s(%s($#l#@s()s('#l#As(-s(,#l#Cs(/s(3#l#Ds(8s(=#l#Fs(Ds(L#Ss%Us%Qs%N#WSQs-Ps(bS/THs%\s%Y$s%`#WSPs-Rs-Ds(cTHs%as%_$s(Z#XSas(\s(Zs%d#XSas(`s(Zs%f#XSys-Ss(is(f#l#Ls(rs(p#Ts-Zs,]s,S#S0Ij#Ms,`#j#Ns,d#j#Os,h#V#MIj##s,l#j##s-&#YSbs-'s-$s,q#Ij#Ms-*#j#Ps-1#V#MIj##s-4#j##s-T#YSbs-Us-Os-<#Ij#Ms-W#j#Qs-]#j#Es-`#j#Rs-e#j#%s-l#j#SC#j#TH#j#Us-j#j#VC#j#WH#j#Xs-m#j#YC#j#)s-p#j#Zs-}##"). Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
  intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u8arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.copied); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Lists.ListDef.skipn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.STRW_tac.st_facts); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.upd_bytes); constr:(@Corelib.Init.Logic.proj1); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.STRW_tac.mc_store_ok); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_write_other); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.u8arr_write_bytes); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.copied_updZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.window_sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv_store); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch_write); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.inside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono_write)|] [|@n; @SOK; @a; @y; @x; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @__sat7; @__sat6; @z5; @H5; @cstr4; @cstr3; @cstr2; @cstr1; @cstr0; @cstr; @LEN0; @Hc0; @Hl0; @Lbs0; @__x5; @m; @__x6; @__x7; @__p1; @__p2; @__p3; @__sat8; @z6; @H6; @k; @xs; @Lbs; @Hl; @Hxs; @Dn; @D0; @H; @SEP; @Hk; @HP; @HPb; @Hc; @Hb; @HW; @LEN; @WM; @MU; @MI; @CP; @DST; @SRC; @bs; @P; @c; @xsw; @base; @kw; @src; @D; @S; @m1; @m0; @segs|] "#28#k%)#u$c$.$d$b#v##$j#$#O$h#?#G#[#C#B#F#Q#7#J#:#;#>#X$2#2#6#K#S#R#]#3#(#Z#%#&#'#=#M#P#W#)#9#I$U#1#A#E#H#L#N#5#4#8$l#0#<#@#D#T#V$[#Y#*#k#/#U#\#,$;$=#^#b#a#+$$$-#c#s#z#i#h#.$'$G$0$L#_$|#j#q#p$%$5$H$I$F$N$Q$Z$g$t$:#o#t#~$+$4$9$>$D$C$P$R$T$S$^$_$a$k$o$q$r$p#e$s$v$w$x$y$u$@%$%#$~#-#d$}%'%&%%%(%*%+%,%)%-$/$f$e$3$`#}$($W$E$\$)$?$m#y$*#w#x#{$##|$&$6$V$1$7$8$i$J$X#r$O$Y${$,$B$M$]$z$<$A$K$n#nU#o%$Z%#n%#v&#;$$['$\*$]%#r$$^+$_&$`%$a&$b%$c'$d&$e'$f&$g&$h&$i'$j'$k%$l'$m&$n&$o$$p%$q%#x%$r&$s&$t%$u%$v%$w$$x%$y$$z*${($-)$|/$}$$~%%#*%$'%%'%&/%'$%($TSzFSaF#F#F#F#F#USm#USn#USm(USn#US{#k##&#T%7S,SJSTSW8S2S@STS6+S35SeS7#9SFS2VS|CC%S,S@:CCS,#USo%-&$#;#SFSG<S%S-SF.2S,+S2&H$#+S@66#S227S,#&5#SJ\S}S%S-SFS,SJSTS2Se#ES2?S@SJ@#SG'S@%S2#&CST##EST'SJ%ST###S-%SHS-##S%%S%S-##SH*%##ES%USps#3USps#/VS~$##)#$'#$)#$/#$3#$5#$9#$<#6s#5S,S22s#6S@#&s#4Se#.s#8ST&H#S,%S'S,=#&s#>ST#AS8SJS@7N#SKS=BS,s#.S@8N%S(#'SG%S2#+#5S='#9N*%S(S':CCS(#-s#?#s#<;#S).<NS)/$$#$)#$+#$0#$3#k##6#k##:#k##=#j##A#?S,S@@#SF'S,%SG#&CSJ##ESJ%SJs#?##S%%S=S%##SH%SHS%##S=*%##ESH#&s#8$$#$&#$,#$/#$1#$5##ESF?SGS2@#S%%S-s#-&CS,##ES,'S2%S,###S=%S(S=##S'%S'S=##S(*%##ES'#&s#N$$#$&#$,#$0#$2#$5#?SFSG@#SH'SF%S%#&CS2##s#DS'%SKS'##S(#s#CSK*$##ES(#s#Fs#`$$#$&#$+#$s#v#$.#$2#6s$5S-S%2s$6SF#&s$4S,#.s$8S2&H#S-%S)S-=#&s$>S2#ASASGSF7Q#SLS8+S%BS-#SF8Q&N#'SH%S%#+#5S8'#9Q+%NS):CCN#-s$@#s$=;#R/<QR0$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B#'S-%SH#&CSG##ESG%SGs#6##S(%S8S(##SK%SKS(##S8*%##ESK#&s$7$$#$&#$,#$/#$1#?S%S-@#S'%S's#)&CS-##ES-'S%%S-###S8%NS8##S)%S)S8##N*%##ES)#&s$K$$#$&#$,#$0#$2#'S=%S(#&CS%##s#=S)%SLS)##N#s#<SL*$##EN#s#?s$Z$$#$&#$+#$s$a#$.#6s%.S'S(2s%/S=#&s%-S-#.s%1S%&H#S'%RS'=#&s%7S%#ASBSHS=7O#SMSA+S(BS'#S=8O&Q#'SK%S(#+#5SA'#9O+%QR:CCQ#-s%9#s%6;#S#/<OS#0$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B#%SHs#1##N%SAN##SL%SLN##SA*%##ESL#&s%,$$#$&#$,#$s$W#'S(%S8#&CS=#%S'%##SA%QSA##R%RSA##Q*%##ER#&s%<$$#$&#$,#$s$Q##s#1R%SMR##Q#s#0SM*$##EQ#s#3s%G$$#$&#$+#$s$J#6s%vS)N2s%wS8#&s%uS'#.s%yS(&H#S)%S#S)=#&s&#S(#AS>SKS87S.#SCSB+NBS)#S88S.&O#'SL%N#+#5SB'#9S.+%OS#:CCO#-s&%#s%~;#S&/<S.S&0$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B#'S8%SK###Q%SBQ##SM%SMQ##SB*%##ESM#&s%u$$#$&#$,##ES8'N%S)###SB%OSB##S#%S#SB##O*%##ES##&s&'$$#$&#$,##s#/S#%SCS###O#s#.SC*$##EO#s#1s&1$$#$&#$+#6s&_RQ2s&`SA#&s&^S)#.s&bN&H#R%S&R=#&s&hN#AS9SLSA7L#SDS>+QBR#SA8L&S.#'SM%Q#+#5S>'#9L+%S.S&:CCS.#-s&j#s&g;#SE/<LSE0$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B#%S>O##SC%SCO##S>*%##ESC#&s&[$$#$&#'R%SA###SC%S.S>##S&%S&S>##S.*%##ES&#&s&g$$#$&#%SDS&##S.#s#'SD*$##ES.#s#*s&o$$#$&#6s'@S#O2s'ASB#&s'?R#.s'CQ&H#S#%SES#=#&s'IQ#AS$SMSB7S/#S:S9+OBS##SB8S/&L#'SC%O#+#5S9'#9S/+%LSE:CCL#-s'K#s'H;#S0/<S/S00$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B##ESD%SDS.##s'8$%#%SESD##S9%S9SD##SE*%##ESE%SES9##s'A$%##EL#>s'D$$#6s'pS&S.2s'qS>#&s'oS##.s'sO&H#S&%S0S&=#&s'yO#ASUSCS>7S;#SNS$+S.BS&#S>8S;&S/#'SD%S.#+#5S$'#9S;+%S/S0:CCS/#-s'{#s'x;#SO/<S;SO0$$#$)#$+#$0#$4#k##7#k##;#k##>#j##B#%S:L##s'g#ES$%S0S$##s'j6s(9S9SE2s(:SD#&s(8S>#.s(<S&&H#S9%SUS9=#&s(BS&#.s(AS9.s(BSN&H$#+SE2s(E#S92s(F$SN&s(D$#WT#'#SCPSVS4S9I&SX#SYj#$H##ES/?S$S:@#SN'S$%S/#&CL#'S:%L###SO%S*SO##S;%S;SO##S**%##ES;#&s(1$$#$&#$,#$s#P#$1#$5#3*)S3S73,)SW#32)SJ#3s#V)SG#37)SH#3;)SK#3>)SL#hT$PSQS*S;SOSUSNS/S0S$S:LSESDS&S>SBSM#KKHS:A#s#+S5PPSQSDs#,&SX#SY%S*S:=#.s(oLPS1PI#&SX#SYASVKS:7SZ#PS*+S0BS$#S:8SZ&S4#'S/%S0#+#5S*'#9SZ+%S4SQ:CCS4#-s(u#s(r;#S1/<SZS10$$#$)#$+#$0#$4#k#%7#j#&s)-#.s),SEPSVS4=#&SX#SY%SQS$=#AP#L7S1#S4S;+S$BS:#L8S1&SQ#'S0%S$#+#5S;'#9S1+%SQS*:CCSQ#-s)4#s)1;#SV/<S1SV0$$#$)#$+#$0#.s)DS:.s)ES;&H$#'%'%&C$#USfHUSfC'K'I&C$#&HKIVT%KIWT&%$#j#'H#j#(H#0C/0C/LHC.S+-%41$30#Q30#S5&H6S/&C4s#@0Cs#ALHC3S+2*96)S/s#B#Q&%#S3?SUSN@#S*'SU'SN%$#'S*#$#0C'0C'fSgHHHCCCSqS+S+S+S^SrSU)$SN(#0C'LHCShS+S_Ss-)$S*(#Q-(#SL.s)jS4+P&H$#'%DEP&C$#0C%DEIj#(C#U#Pj#(CI0CPRCHCCSb$S+&SiPP#LHCs#/S+s#.s#&/,).&#Q.+#S&MSO'SO#E#Ms$<'s$=#E#.s*#SOM#'$#E#.s*'SZM#'$#E#MP'P#E#MSj'Sj#E#VStES[GES[DES[&C#S[$%##S[E&C&E$$#*&#DES`VT's)os)nGEs)p#Es)pGEs)pk##$#k##&##Es)uWT(s)vs)uKj##Su#j#)%##Es)wk##Su#k#)(#VT)Es)|0T*#m##0UK#HSvH#H#H#EC#EC%ECSv/C$#/C&#>#SPUSoS?-S?$#TS?NCS7UT+C1C$S5#NCS61C$K#UT,CUT-CVSwCECCs*i(C$M#)&GDDF#JUT.DCCSa(C(M#)*GDDF#JCCs*q(C+M#)-GDDF#JSSaCC#4C#.(C(SI#)2GDDF#J(C2M&)4GDDF#J4C/,(C5M#)7GDDF#J,8GDDF&3#,9GDDF)4#,:GDDF/5#,;GDDF36#,<GDDF87#VT/=F0SXSYVT0IS5&SX#SYm$%#WT1CEKXT2IS5$#l#**)#l#+s#'s#&#l#,s#.s#-#j#-C#j#.C#j#/C#j#0C##ES6#EK%S3S<&CS7##ES<#E%k##$#k##&#k##*#k##*#k##,#k#-C#k#.C#k#/C#k#0C#'S`]I#T3S\ScSRS'S#S&S0l#14%#l#2s#Qs#]#l#3s#Ys#V#l#2s#cs#^#l#4s#eC#l#5s#os#g#l#6s#ss#q#l#7s#ws#u#l#8s#{s#y#l#9s$$s#~#l#:s$)s$'#l#;s$-s$+#l#<s$/s$8#l#=s$?s$E#l#>s$Ms$P#l#?s$Ss$a#ECs#^ECs#`/C#s#[/C%#/Cs#^#>#SP-S?#s#[1Cs#XS5s#YNCS31Cs#ZS6#1C%K#Fs#KCC#(Cs#LSI#)s#ZGDDF#JSs#OCC#4Cs#W#VSwCs+7WT4C#s+c(C%M#)s#aGDDF#J4Cs#Y,(C#M))s#dGDDF#J4Cs#Rs#X(C#M))s#gGDDF#J,s#hGDDF&s#c#,s#iGDDF*s#d#,s#jGDDF2s#e#l#*#s#Ps#Jl#+8s#m#l#,=s#t#j#-C#j#.C#j#/C#j#0C#j#@C#&CS5S6%KS3##s+L%S6S3##S<%S6S7%#S3##s+Qk##&#k##)#k##,#k#-C#k#.C#k#/C#k#0C#k#@C#'S[.s,)Sj'#\ISd%#S\ScS@S=Rl#17'#l#2s$@s$L#l#3s$Hs$E#l#2s$Rs$M#l#4s$TC#l#5s$^s$V#l#6s$bs$`#l#7s$fs$d#l#8s$js$h#l#9s$os$m#l#:s$ts$r#l#;s$xs$v#l#<s$zs%'#l#=s%.s%4#l#>s%<s%?#l#?s%Bs%P#+S*%Ps%N%S4S0#$#%$s%W##P*%#j#$H#'*%S4###s%u's&6%s%w###S4*&#DES*%S4###s%|*#'#KIUT5#j#'C#j#(C#%KIXT6CCT7#0C#j#AC#j#$C#0CS40Cs%jj#(H#0CS*RCHCCSbs%FS+s%HSiS*S*#RHCCCS+S+s%Gs%G%s##4#fSgCCCCCCS^s%Hs%Hs%HS^)S4S4(<5#0Cs&2LCCS_s%JS_0=6$s&3s&3#0SS:WT8;;#ZT9?<8<%#Hs$sH#H#EC#EC%EC'/C#s#w/C%#/C'#>#SP/C's$x>#SP/Cs$%s$$/Cs%##/C,#>#SP-S?#s$|-S?(#-S?+#-S?,#NCS<1C#S7s$}1C#S5s$~NCSR1C#S3s%$1C#S6s%%1C&K#ZSks$~GDDFSWSs-,CC#(Cs$xSI#)s%&GDDF#JIs%'GDDF'#(C&Ms%')s%)GDDF#J(Cs$}SIs%))s%+GDDF#JIs%,GDDF%#Os%-GDDF(#Ss-8CC#CCs-8(C$SI#)s%2GDDF#J4Cs%-1(C#Ms%')s%5GDDF#J4Cs%)4(C#Ms%1)s%8GDDF#JOs%9GDDF&#4Cs%8,(C#M9)s%<GDDF#J(Cs%*Ms%/)s%>GDDF#J4Cs%12(C#Ms%:)s%AGDDF#JOs%BGDDF&#,s%CGDDFs%?s%>#,s%DGDDF*s%?#,s%EGDDF.s%@#,s%FGDDF6s%A#,s%GGDDF<s%B#l#*#s%-s%'l#+s#*s%J#l#,s#2s%Q#j#-C#j#.C#j#/C#j#0C#j#@C#j#BC#j#CC#j#DSS#&CKS<$SR##S<E&CKE$$#*&#&CS3S<%S5S]##S7%S7S]##S5*%#%S<S]##SW#ESR%SRS]#s%8#%$SW##S3*%#k##(#k##*#k##-#k##3#k##5#k#-C#k#.C#k#/C#k#0C#k#@C#k#BC#k#CC#k#DSS#GESdaI#Sds$Ps$NS\ScS7SlS3S@S)RS#l#1s#&%#l#2s&/s&;#l#3s&7s&4#l#2s&As&<#l#4s&CC#l#5s&Ms&E#l#6s&Qs&O#l#7s&Us&S#l#8s&Ys&W#l#9s&^s&\#l#:s&cs&a#l#;s&gs&e#l#<s&is&r#l#=s&ys'##l#>s'+s'.#l#?s'1s'?#XSxs$?s$;s$&#KHs$Ns$G#s'EO^T:S1Ps'\LS4S;S9s%?s$P#NCK,s&.GDDFs&&s&)s&&l#*#s%ps%jl#+%s&1#l#,s&:s&8#j#-C##EIk###s%fk#-C#VIS\S#l#1'$#l#2s&Ls&X#l#3s&Ts&Q#l#2s&^s&Y#l#4s&`C#l#5s&js&b#l#6s&ns&l#l#7s&rs&p#l#8s&vs&t#l#9s&{s&y#l#:s'$s&~#l#;s'(s'&#l#<s'*s'3#l#=s':s'@#l#>s'Hs'K#l#?s'Ns'\#?s(2s'b@#Ij#$H#?s'vs(:@#s$nDES$%#s$e##s$b0CS$RCHCCSbs';S+s'=SiS$S$#0Cs$ifSgHHHCCCSqS+S+S+S^Srs'~($s(Bs$j#LHCShS+S_Ss+(#s$vs$gs$VVStES1GES1DES1&C#S1$%##S1E&C&E$$#*&#DESZUT;SaVT<C#WT=C#s&o/C#s%o/Cs$X#/Cs$Z#>#SP>%SP/Cs%xs&s/Cs&u#/C*#/Cs$_#>#SP/Cs$b$>#SP-S?#s&v-S?&#-S?,#-S?.#1Cs$XS<s&v1C#S5s&w1Cs&yS6s%}1C$K#ZSks&uGDDFS](Cs&pSIs$I)s&wGDDF#JIs&xGDDF%#(Cs&sSIs&x)s&zGDDF#JIs&{GDDFs$[#Os&|GDDF&#ZSks&}GDDFT>(Cs&qSIs$P)s'#GDDF#JIs'$GDDF%#(Cs$SMs'$)s'&GDDF#J(Cs&vSIs'&)s'(GDDF#JIs')GDDF%#Os'*GDDF(#(Cs&~SIs&-)s',GDDF#J4Cs$\s&/(C#Ms$\)s'/GDDF#J(Cs'/Ms$_)s'1GDDF#J(Cs&{Ms'%)s'3GDDF#J,s'4GDDF%s'/#,s'5GDDF(s'0#,s'6GDDF,s'1#,s'7GDDF/s'2#,s'8GDDF:s'3#l#*#s&zs&tl#+s#$s';#l#,s#)s'B#j#-C#j#.C#j#/C#j#0C#j#@C#j#BC#j#DSS#j#ESS#j#FSS#&CIS6$S<#&CIE$SR#*%#&CS6S<$SW#&CS6E$s$V#*%#%S<SR##S]#s'&SRk##s$O#k##%#k##,#k##)#k##/#k#-C#k#.C#k#/C#k#0C#k#@C#k#BC#k#DSS#k#ESS#k#FSS#GESl#S`EGES`'T?.s/eS\'#bI('&Sl%S`S<#S7S3SRS2SMSCl#1s#%*#l#Gs'|s(,#l#2s((s(%#l#Gs(2s(-#l#Hs#lC#l#Is#vs#n#l#4s(6C#l#5s(@s(8#l#6s(Ds(B#l#7s(Hs(F#l#8s(Ls(J#l#9s(Qs(O#l#:s(Vs(T#l#;s(Zs(X#l#<s(\s(e#l#=s(ls(r#l#>s(zs(}#l#?s)$s)2#XSxs$0s$-s$(#KHs&As$3#s)8OKHs)9s$4#s):S5]T@S1PSQS:S$LSDs$8#%S0s)3+#5S*s)i#j#JH#6s0&s)lS*2s0'I#&s0%#S:j#$H#6s0*S/SN2s0+S0#2s0,S/(&s0*#Ij#Ks0+#_TAS;SNSUSOS/S0S$S#RS)S'Ks0-'$#LS3KHS0*#s)|S7\TBS;S:S$LS.s$I#5ZTCHs)~0#S0S7ZTDS1Ps)bLS&I#SQs)d#s&Ls)Y$$#>s$.SP-S?#s(A1Cs(=Ks'B(Cs(-SIs'<)s(;GDDF#J4Cs(3s'>(C#Ms(;)s(>GDDF#J(Cs(9Ms(,)s(@GDDF#J4Cs(;s(?(Cs';M#)s(CGDDF#JIs(DGDDF&#,s(EGDDFs(:s(@#,s(FGDDF*s(A#,s(GGDDF.s(B#l#*#s(-s('l#+2s(J#l#,4s(Q#j#-C#j#.C#j#/C#j#0C#j#@C#&CS5S7%S5S3##S7#S6s'9%S6S<#s':#$%#k##s(.#k##(#k##+#k#-C#k#.C#k#/C#k#0C#k#@C#\Is':Sds'8S\ScS@RS#l#13$#l#2s(us)%#l#3s(}s(z#l#2s)+s)&#l#4s)-C#l#5s)7s)/#l#6s);s)9#l#7s)?s)=#l#8s)Cs)A#l#9s)Hs)F#l#:s)Ms)K#l#;s)Qs)O#l#<s)Ss)\#l#=s)cs)i#l#>s)qs)t#l#?s)ws*)#WTEs#<TF#WTGs*7s*Es'-m#$#]THs*9SVPs*GLS>s(*s';#ZTIS1SVPs*GLSC3s*:s*9$#3s*?s*9s#E#3s*As*9s#G#3s*Fs*9s#Z#3s*Js*9s%O#j#%s*O#[Sys0~s*ls*S#S9S5Il#%s*qs*o#l#Ls+8s+=#j#)s+A#j#Ms+E#j#Ns+H#j#Os+L#j#Ps+O#V#KIj##s+R#j##s+w#Js+xs+ws+V#Ij#Qs+z#j#Rs,##V#KIj##s,*#j##s,S#Js,Ts,Qs,0#Ij#Qs,Y#j#Ss,c#V#KIj##s,h#j##s-?#Js-@s-8s,s#Ij#Qs-B#j#Ts-P#V#KIj##s-S#j##s/m#Js/ns.'s-b#Ij#Qs.2#j#Us.@#V#KIj##s.E#j##s/##Js/$s.us.T#Ij#Qs/(#j#Vs/;#V#KIj##s/?#j##s0&#Js0's/ts/S#Ij#Qs0*#j#Ws0@#V#KIj##s0C#j##s16#Js17s0zs0Z#Ij#Qs19#j#Xs1;#j#Ys1@#j#Zs1D#j#[s1F#j#\s1M#j#]s1O#j#^s1R#j#_s1T#j#&s1[#j#Ks1W#j#`s1X#j#aC#j#JH#j#bH#j#cs1\#j#dC#j#eH#j#fs1_#j#$C#j#gC#j#hC#j#is1d#j#js1e#j#ks1r##"). Qed.

(* [comment removed for export] *)
Ltac ld1 HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
                  ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
    zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
  end end.

(* [comment removed for export] *)
Ltac ld4 HW c w :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
    destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
      as [w [RD [Ew Lw]]];
    cbn [firstn skipn] in Ew;
    zstep; try clear RD
  end end.

(* [comment removed for export] *)
Ltac zify_bytes :=
  repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch type of b with
      | byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
      end
  end.
Ltac solve_le K :=
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
  cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
  zify_bytes;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
  lazymatch K with
  | 0%Z => idtac
  | _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
               | rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
  end;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)
Ltac by_le K :=
  symmetry;
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first
    [ lazymatch goal with
      | |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
          lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
      | |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
          lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
      | |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
          lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
      | |- le1 (sext _ _) = _ => apply lwb0
      end
    | solve_le K ].

(* [comment removed for export] *)
Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

(* [comment removed for export] *)
Ltac cst HW c k bytes_tac :=
  lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

(* [comment removed for export] *)
Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

(* [comment removed for export] *)
Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

(* [comment removed for export] *)
Ltac cp_norm P' :=
  lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

(* [comment removed for export] *)
Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
    (m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
  bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
  mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

(* [comment removed for export] *)
Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

(* [comment removed for export] *)
Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

(* [comment removed for export] *)
Ltac finish2 :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac mc_fin :=
  lazymatch goal with
  | DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
      let E := fresh "E" in
      pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
      apply rw_cells_of_u8arr in DST; rewrite L in DST
  end;
  finish2.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := zstep; fix_lit_store.

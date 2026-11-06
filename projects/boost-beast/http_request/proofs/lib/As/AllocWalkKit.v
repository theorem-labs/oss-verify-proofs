(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocRep.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma zx32_wz : forall x, 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros x Hx. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma shl32_shr30 : forall x, 0 <= x < 2^32 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2^32) with ((4 * x) * 2^30) by lia. apply Z.div_mul. lia.
Qed.

Lemma shl32_val : forall x, 0 <= x < 2^32 -> bv_unsigned (Z_to_bv 64 (Z.shiftl x 32)) = x * 2^32.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma shl4_val : forall x, 0 <= x < 2^60 -> bv_unsigned (Z_to_bv 64 (Z.shiftl x 4)) = x * 16.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Section WithSegs.
  Variable segs : list Segment.
  Lemma u32arr_snoc : forall m A ws w,
    u32arr segs m A (ws ++ [w]) <-> u32arr segs m A ws /\ rw_cells segs m (A + 4 * Z.of_nat (length ws)) [C4 w].
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u32s); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(segs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wr_at); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le4); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_app); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Nat.mul); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.mul); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_mul); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.CellsX.wr_at_app); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.I); constr:(@Stdlib.Lists.List.length_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u32s_length); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u32s_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u32arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells)|] [|@l; @lemma; @n; @x; @y; @__ff; @__varmap; @__wit; @__x1; @__arith; @cstr; @z; @m; @B; @H3; @H0; @H2; @H; @H1; @H5; @H4; @w; @ws; @A|] "#(]#4$>#<#F#&###'#%#$#(#_#s#)#4#J#C#*#S#l#+#-#t#,#/#r#.#1#z#0#H#3#:#M#V#m$4#2#8#7#I#N#L#P#Q#Z#Y#]#W#X#`#b#f#c#v#y#}#~#a#O$*#D$/$9$%$>#;#[#\#^#d#h#i#n#o#q#x#{$#$$#|$&$'$($)$,$+$1$0$2$.$5$3$6$-$:$;$<$=$?#E#G#K#R#@#e$7$8#?#9#k#A#u#p#B#U#T#>#=#g#j#w?#]%$('$)'#/$#[%#>%$*%$+$$,$#0%$-%$.'#S&$/($0&$1$$2%$3&$4'$5*$6$$7$$8%$9)$:$$;5$<$$=%2S02#2#2#2#2#US6#US7#US6(US7#USR#k##&#;';&+I7*4+F#+#1+&#$DGEFUS8540I(11H#)2#&#('#%DGE##*#+H$DGE#)9H&#(.#%DGE##'#US9I7S14S1$#US:#'E)US;%$DG$##&#US<(&#%DG(##&##/#,7#j#$s#&#*F1s#,9F$DGE###=#RR$DG2F#$#8S28#8#8#9#S2&#%DG:##*##A#,/#j#$s#8#1s#=s#84$DEH#$DEHs#:)s#@s#;&#'H#$DE#:#'#,)#*I1s#Gs#4#$DGE###s#8)s#Js#7&#'E#$DG#)#s#:###s#>WSSNPSTXS=NP#s#@ZS>,&Fs#As#A#$DGs#5/#s#'###?#s#=#VS?N#]S@NPSA1+($$#j#%6#YSUDEHs#Us#1)s#]IVSBs#)#&F'E#$DG#;#s#L###s#P,#.j#&K#)s#fs#]9,#VSBs#3s#Q&#'E#$DG#s#%#s#V#(s#`0%DGE##%#,#:j#&K#&7(s#f#&8/C$#/C%%USCCj#'CF/CIFUSV#j#(C#j#'C#-C,-CAj#'K#-Cs#s-C1<KKKCCCSWOOOS.SXs#Ms#u$s#'2#`SDKCCCOO--&s#'2#`SECC/./*33)23#=s#*3S#67S3;S3VSYCIUSZCUS[C>Cs$#VS\CS0WSFC$#5C#SG#6'S)LLS&#S,VS](S&-SHSIVS^FH/SH#SIm$%#WS_CS#IXS`FH$#l#)*)#l#*21#l#+54#j#,C#(s$3F/C##k#,C#)s$CE&#UF#l#-)&#l#.@?#XSJs#1s#0B#+E$DJG#'GF*H$DJ$##&#9.s#y&#(s$D#%DJG##'#(s$G2%DJG##.#'G%$DJ#.#s$*#%DJ%s$##$##(#,,#j#/C#'s$Fs$R9s$Is$.&#(s$U#/C&#US8S0's$M#(s$Y#/C*#-C+(IFXSaCCSb#-C#j#0C#j#&C#-Cs$V-C-<KKKCCCScOOOSKSds$Ys$X$s$>.#`SDKCCCOOs#Ws#Ws#P3.#<CCCCCCS.s#Xs#Xs#XS.'s$es$es#P3/#`SECCs#Zs#Ys#Zs#U66-3/#=s$]3S#s$]WSLCs#Fs#H>C5WSLCs#I#WSFCs#K#5C&SG#6s#NS)LLS&#S,l#)#s#Is#Cl#*s#Rs#Q#l#+s#Us#T#j#,C#'s#Bs$s'F?(s$u#/C%#k#,C#)s%)G&#UF#l#-+&#l#.76#XSJs#)s#%9#'s#9s$~+G$DMJ#(s%%*'J#*E$DM$##'#%DMJF#$#%DMJ)#+##s$h(%DM+s$a#$##&#,)#j#/C#%DJG4%DJs#Is%5#s#L#,%#'5s%8%DMJ##3#%DM7s%;#2##6#k#1NNXSeNNPPXS=NPs$Y9_SfN%P$SMS>:#*'FVS?N3]S@NPSA+($44#j#%/#=s#m3S#s#mVSNCS2VSNCs$~WSgC$#VSh#SiVSj&#4S3#s$0>CS#5C#S4s$,6s$/S)LLS&#S,USkL5C&S4s$.6s$2S)LLS&#S,\Sls$3S)LLS&&%#l#)#s$.s$(l#*s$7s$6#l#+,s$9#j#,C#3S#F(s%YI3S##k##%#k#,C#)s%jJ&#VF#Il#-+&#l#.>=#USmC5C8S4s$B6s$DS)LLS&#S,l#)#s$?s$9l#*&s$G#l#+s$Ks$J#3S#s%hl#-$#F[SnDJGs$%s%j+##s$0s#~##s#8#s#As#4#s#C#k##%##s$&s#=#s$*#k###s#7(s%s7%DQM#'M$%DQ#s%v#%#+M$DS$Q#)s&+M&#(s%|#'Q#*J$DS$$#%DS$Q&#*##s%`%%DS$(s&'#$##&#)s&7Q&#(s&,#'S$#*M$DS'$#)s&=S$&#(s&2#%DS%S'#'S'$%DS%#s&5+S$$DS%S'###'*Q$DS%(##s%u###)#'#)s&KS'&#(s&@#'S%#%DS*#s&B+S%$DS(S*#)s&RS%&#(s&G#%DS(S*##'#'S*%*S'$DS($##s&+#%DS(&s&N#$#..*EI.RRSOSO.s&0(#H.('#F.-'&#j#25#j#3s#%#0s#&s#$<#Hj#4s#+#j#5s#>#0s#?s#9s#3#Ij#6s#B#j#3s$5#0s$6s$#s#M#Fj#5s#P#*G$DQs#I##s&?###s#J#s#Hs#B#s#Bs#?#$#%DS'S$s#<#s#2s#/#s#7s#5#$##s#(@#s#%?#$#)s&zS*&#(s&o#'S(#*S%$DS-$#+S($DS+S-#)s'&S(&#(s&w#'S-#*S*$DS+$##)#%DS+S-'%DS+'s&}#$##&#+S+$DS/S5#)s'3S+&#(s'(#'S5#*S-$DS/$##)#%DS/S5'%DS/'s'.#$#.-'QH.&%MG.(%$#j#7R#j#3R#0RR4#Ij#8B#j#6s&q#0s&rs#Js#*#Ij#2s#U#j#3s#]#0s#^s#ds#0#Hj#4s#4#j#5s#~#0s$#s#xs#7#Ij#6s#;#j#3s$q#0s$rs$2s$b#Fj#5s$/#.s$2s$/s#C#Vs$^s$8#ZSPCs%%s$p#s%_Fl#5s%'s%N#ZSPCs';s%T#s&IFl#5s%ks&>#'Hs&@$DE#s',#s&u#&s&P(s'M#%DEH##&#%DEHs&H#s&{#'Hs&J$DE#s'5#s'2#%DE%s'+#$##(#,+#m#3#1s'gIs'^)s'h#WSos'iIs'`:Ks&as&W&$#USpI:Ks&ls&e$s',#Vs&ps&o#7s'l1s'ms'D#VSqs'ns'E:s'ks'Fs'5&$#$DEHs'g&-(s'g#%DEH##&#US9F4S1#s'[US:#US;$$DE>##%#US<'&#%DEB##&##s#%#,.#m#4#+?VSrIs'|:s($s'{s'\%$#XSQDEHBXSQDEHIXSsDEs#,3#$#,&#m#(#j#9s(1#j#:s(-#j#;C#j#0s(0##"). Qed.
  Lemma u64arr_snoc : forall m A ws w,
    u64arr segs m A (ws ++ [w]) <-> u64arr segs m A ws /\ rw_cells segs m (A + 8 * Z.of_nat (length ws)) [C8 w].
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(segs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wr_at); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le8); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_app); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Nat.mul); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.mul); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_mul); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.CellsX.wr_at_app); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.I); constr:(@Stdlib.Lists.List.length_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s_length); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells)|] [|@l; @lemma; @n; @x; @y; @__ff; @__varmap; @__wit; @__x1; @__arith; @cstr; @z; @m; @B; @H3; @H0; @H2; @H; @H1; @H5; @H4; @w; @ws; @A|] "#(a#4$>#<#F#&###'#%#$#(#_#s#)#4#J#C#*#S#l#+#-#t#,#/#r#.#1#z#0#H#3#:#M#V#m$4#2#8#7#I#N#L#P#Q#Z#Y#]#W#X#`#b#f#c#v#y#}#~#a#O$*#D$/$9$%$>#;#[#\#^#d#h#i#n#o#q#x#{$#$$#|$&$'$($)$,$+$1$0$2$.$5$3$6$-$:$;$<$=$?#E#G#K#R#@#e$7#U$8#?#9#k#A#u#p#B#T#>#=#g#j#w?#]%$('$)'#/$#[%#>%$*%$+$$,$#0%$-%$.'$/$#S&$0($1&$2$$3%$4&$5'$6*$7$$8%$9)$:$$;5$<$$=%3S03#3#3#3#3#US6#US7#US6(US7#USR#k##&#;';&+I8*5+F#+#2+&#$DGEFUS8450I(21H#)2#&#('#%DGE##*#+H$DGE#)9H&#(.#%DGE##'#US9I8S15S1$#US:#'E)US;%$DG$##&#US<(&#%DG(##&##/#,7#j#$s#&#*F2s#,9F$DGE###=#RR$DG2F#$#/S2/#/#/#/#/#/#/#9#S2&#%DG>##.##s#%#,3#j#$s#<#2s#As#<8$DEH#$DEHs#>)s#Ds#?&#'H#$DE#>#'#,)#*I2s#Ks#8#$DGE###s#<)s#Ns#;&#'E#$DG#)#s#>###s#BWSSNPSTXS=NP#s#DZS>,&Fs#Es#E#$DGs#9/#s#+###?#s#A#VS?N#]S@NPSA1+($$#j#%6#YSUDEHs#Ys#5)s#aIVSBs#)#&F'E#$DG#;#s#P###s#T,#.j#&K#)s#js#a9,#VSBs#3s#U&#'E#$DG#s#%#s#Z#(s#d0%DGE##%#,#:j#&K#&7(s#j#&80C$#0C%%USCCj#'CF0CIFUSV#j#(C#j#'C#-C,-CAj#'K#-Cs#w-C1<KKKCCCSWOOOS.SXs#Ms#y$s#'2#`SDKCCCOO--&s#'2#`SECC/./*33)23#=s#*4S#68S3;S3VSYCIUSZCUS[C>Cs$'VS\CS0WSFC$#6C#SG#7'S)LLS&#S,VS](S&-SHSIVS^FH0SH#SIm$%#WS_CS#IXS`FH$#l#)*)#l#*21#l#+54#j#,C#(s$7F0C##k#,C#)s$GE&#UF#l#-)&#l#.@?#XSJs#1s#0B#+E$DJG#'GF*H$DJ$##&#9.s#}&#(s$H#%DJG##'#(s$K2%DJG##.#'G%$DJ#.#s$.#%DJ%s$##$##(#,,#j#/C#'s$Js$V9s$Ms$2&#(s$Y#0C&#US8S0's$Q#(s$]#0C*#-C+(IFXSaCCSb#-C#j#0C#j#&C#-Cs$Z-C-<KKKCCCScOOOSKSds$]s$\$s$B.#`SDKCCCOOs#Ws#Ws#P3.#<CCCCCCS.s#Xs#Xs#XS.'s$is$is#P3/#`SECCs#Zs#Ys#Zs#U66-3/#=s$a4S#s$aWSLCs#Fs#H>C5WSLCs#I#WSFCs#K#6C&SG#7s#NS)LLS&#S,l#)#s#Is#Cl#*s#Rs#Q#l#+s#Us#T#j#,C#'s#Bs$w'F?(s$y#0C%#k#,C#)s%-G&#UF#l#-+&#l#.76#XSJs#)s#%9#'s#9s%&+G$DMJ#(s%)*'J#*E$DM$##'#%DMJF#$#%DMJ)#+##s$l(%DM+s$a#$##&#,)#j#/C#%DJG4%DJs#Is%9#s#L#,%#'5s%<%DMJ##3#%DM7s%?#2##6#k#1NNXSeNNPPXS=NPs$Y9_SfN%P$SMS>:#*'FVS?N3]S@NPSA+($44#j#%/#=s#m4S#s#mVSNCS2VSNCs%&WSgC$#VSh#SiVSj&#5S3#s$0>CS#6C#S4s$,7s$/S)LLS&#S,USkL6C&S4s$.7s$2S)LLS&#S,\Sls$3S)LLS&&%#l#)#s$.s$(l#*s$7s$6#l#+,s$9#j#,C#4S#F(s%]I4S##k##%#k#,C#)s%nJ&#VF#Il#-+&#l#.>=#USmC6C8S4s$B7s$DS)LLS&#S,l#)#s$?s$9l#*&s$G#l#+s$Ks$J#4S#s%ll#-$#F[SnDJGs$%s%n+##s$0s#~##s#8#s#As#4#s#C#k##%##s$&s#=#s$*#k###s#7(s%w7%DQM#'M$%DQ#s%z#%#+M$DS$Q#)s&/M&#(s&$#'Q#*J$DS$$#%DS$Q&#*##s%d%%DS$(s&+#$##&#)s&;Q&#(s&0#'S$#*M$DS'$#)s&AS$&#(s&6#%DS%S'#'S'$%DS%#s&9+S$$DS%S'###'*Q$DS%(##s%y###)#'#)s&OS'&#(s&D#'S%#%DS*#s&F+S%$DS(S*#)s&VS%&#(s&K#%DS(S*##'#'S*%*S'$DS($##s&/#%DS(&s&R#$#..*EI.RRSOSO.s&4(#H.('#F.-'&#j#25#j#3s#%#1s#&s#$<#Hj#4s#+#j#5s#>#1s#?s#9s#3#Ij#6s#B#j#3s$5#1s$6s$#s#M#Fj#5s#P#*G$DQs#I##s&C###s#J#s#Hs#B#s#Bs#?#$#%DS'S$s#<#s#2s#/#s#7s#5#$##s#(@#s#%?#$#)s&~S*&#(s&s#'S(#*S%$DS-$#+S($DS+S-#)s'*S(&#(s&{#'S-#*S*$DS+$##)#%DS+S-'%DS+'s'%#$##&#+S+$DS/S5#)s'7S+&#(s',#'S5#*S-$DS/$##)#%DS/S5'%DS/'s'2#$#.-'QH.&%MG.(%$#j#7R#j#3R#1RR4#Ij#8B#j#6s&u#1s&vs#Js#*#Ij#2s#U#j#3s#]#1s#^s#ds#0#Hj#4s#4#j#5s#~#1s$#s#xs#7#Ij#6s#;#j#3s$q#1s$rs$2s$b#Fj#5s$/#.s$2s$/s#C#Vs$^s$8#ZSPCs%%s$p#s%_Fl#5s%'s%N#ZSPCs'?s%T#s&IFl#5s%ks&>#'Hs&@$DE#s'0#s&u#&s&P(s'Q#%DEH##&#%DEHs&H#s&{#'Hs&J$DE#s'9#s'6#%DE%s'+#$##(#,+#m#3#2s'kIs'b)s'l#WSos'mIs'd:Ks&as&W&$#USpI:Ks&ls&e$s',#Vs&ps&o#8s'p2s'qs'H#VSqs'rs'I:s'os'Js'5&$#$DEHs'k&-(s'k#%DEH##&#US9F5S1#s'_US:#US;$$DE>##%#US<'&#%DEB##&##s#%#,.#m#4#+?VSrIs($:s((s(#s'`%$#XSQDEHBXSQDEHIXSsDEs#,3#$#,&#m#(#j#9s(5#j#:s(1#j#;C#j#0s(4##"). Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma junk_of_rw_cells : forall m A cs, rw_cells asegs m A cs -> junk m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs H Hn. eapply stk_of_rw_cells. exact H. Qed.
Lemma junk_merge : forall m lo n k, junk m lo n -> junk m (lo + n) k -> 0 <= n -> 0 <= k -> junk m lo (n + k).
Proof.
  intros m lo n k J1 J2 Hn Hk Hp. destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.add_0_r in J2. cbn. replace (lo + (0 + k)) with (lo + k) by lia. apply J2. lia.
  - destruct (Z.eq_dec k 0) as [->|KZ].
    + replace (lo + (n + 0)) with (lo + n) by lia. apply J1. lia.
    + eapply stk_merge; [apply J1; lia| replace (lo + (n + k)) with (lo + n + k) by lia; apply J2; lia| lia].
Qed.
Lemma junk_split : forall m lo n k, junk m lo (n + k) -> 0 <= n -> 0 <= k -> junk m lo n /\ junk m (lo + n) k.
Proof.
  intros m lo n k J Hn Hk. split; intros Hp.
  - destruct (stk_split asegs m lo (lo + n) (lo + (n + k))) as [A _]; [apply J; lia| lia| exact A].
  - destruct (stk_split asegs m lo (lo + n) (lo + (n + k))) as [_ B]; [apply J; lia| lia|].
    replace (lo + n + k) with (lo + (n + k)) by lia. exact B.
Qed.
Lemma junk_transport : forall W m m' lo n, junk m lo n -> munch W m m' -> wmono asegs m m' ->
  (forall x, lo <= x < lo + n -> outside W x) -> junk m' lo n.
Proof. intros W m m' lo n J MU WM OUT Hp. eapply stk_transport; [apply J; exact Hp| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia. Qed.

End HCW.



(* [comment removed for export] *)
Ltac addr_diff_near E A :=
  let k := addr_diff E A in
  let b := eval vm_compute in (Z.ltb (Z.abs k) 2048)%Z in
  lazymatch b with true => k end.

Ltac solve_load_near :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_load ::= first [ solve_load_near | solve_load_image ].

(* [comment removed for export] *)
Ltac solve_store_near :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    end
  end.

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callN segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callN" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callN segs m ]
  end.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma stk_cells : forall m lo hi, stk asegs m lo hi -> lo <= hi ->
  exists junk, rw_cells asegs m lo [CB (Z.to_nat (hi - lo)) junk].
Proof.
  intros m lo hi ST LE. destruct (stk_carve asegs m lo hi (Z.to_nat (hi - lo)) ST) as [_ [junk R]]; [lia|].
  rewrite Z2Nat.id in R by lia. replace (hi - (hi - lo)) with lo in R by lia. exists junk. exact R.
Qed.

(* [comment removed for export] *)
Inductive hidden (P : Prop) : Prop := Hide (p : P).

End HCW2.

Ltac hide_hyp H := apply Hide in H.
Ltac unhide_hyp H := destruct H as [H].
Lemma hidden_out : forall P : Prop, hidden P -> P.
Proof. intros P [p]. exact p. Qed.

(* [comment removed for export] *)
Ltac nb_from pf T :=
  lazymatch T with
  | ?A /\ ?B => nb_from constr:(@proj1 A B pf) A; nb_from constr:(@proj2 A B pf) B
  | akobj ?X 4096 => first [ lazymatch goal with _ : akobj X 4096 |- _ => idtac end | pose proof (pf : akobj X 4096) as THB | idtac ]
  | aapp ?X 160 => first [ lazymatch goal with _ : aapp X 160 |- _ => idtac end | pose proof (pf : aapp X 160) as CTB | idtac ]
  | _ => idtac
  end.
Ltac name_bands :=
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [akobj _ 4096] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [aapp _ 160] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [akobj _ 4096] => nb_from H P end end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [aapp _ 160] => nb_from H P end end
       end).
(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition hide (P : Prop) : Prop := hidden P.

End HCW3.


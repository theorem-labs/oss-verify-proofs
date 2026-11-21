(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach HeapCeil Frame FileSim RefNodes SymDriveX
  SymExec2 SymExec2Sound RegsEquivM MainEqv MemSplit MainMem LazyRestrict LazySR LazyFdNodes StreamSim StoreOk.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsDrvHeap AsDrvRun AsDrvOpen AsDrvMem N9_read.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma AECALL : fetch_word bsegs (Z_to_bv 64 AREAD_ECALL) = Some ECALLW.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N9_read.AREAD_ECALL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDriveX.ECALLW)|] Array.empty "##=###4#+#)#,#(#'#.#0#-#&#4#5#2#3#6#1#*#/%#2$#3$#C########UD#UF#UG#$C$#####$#$#UH#VI,#WJ-$#VE-#VK-##1UD#VL#MVNO#VE3PWQ3$#m$)##"). Qed.
Scheme kc__1 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

(* [comment removed for export] *)
Lemma amem_inv_wbytes_data : forall m (A : Z) bs,
  mem_inv bsegs m -> 0x119000 <= A -> A < 2 ^ 64 -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  mem_inv bsegs (wbytes m (Z_to_bv 64 A) bs).
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.ZArith_dec.Z_lt_le_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.ro_addr); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes_below); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.u_small); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDrvMem.aro_addr_false); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes_above)|] [|@s; @o; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat65; @__sat66; @cstr; @Hab; @Hlt; @l; @__p1; @Hin; @__x3; @Hout; @Hge; @b; @a; @Hl; @HA64; @HA; @Hinv; @bs; @A; @m|] "#'2#7$*#?#i###j#h#%#$#Q#,#'#)#r#3#.#/#0#o#&#*#2#1#B#+#-#(#V#=#a#6#;#:#@#A#P#S#W#X#\#^#b#w#{#z#Y$&$'$$#7#U#L#>#G#O#]#_#`#d#e#g#m#p#s#t#v#x#y#u#|#Z$#$(#~$*$)$+#}#5$,#<#C#F#R#H#K#l#k#J#I#f#N#E#D#M#T#c#n#q#[$%:#q$#r%#s%#t%#u%#v&#w'#x*#y%#z$#{+#|%#}$#~$$#%$$%#%&#T'$%%$&%$'%$()$)%#S-##########US0#US1#US0(US1#USE#k##&#US2%VS3S(H/./#####/#########################0##S-####/#/#####/#########################0##5########################0#$1H0s#F0s#BVSF$#%S$#+s#AS$,#'L#$#'1s#HS%4S)#MI.s#GE(s#G$#USGH&s#MH$J#%$/VS4$#&s#QS$VS5#K%$K$K%2$#&s#VL%#S*$S*$2$#VS6S(S+(S,#S7j#$%#&s#]S+%#P1s#_Q4R#PM.s#^M(s#^E#j#%s#_#URM+s#bQ,#'E#$#s#(j#&C#+s#gPUS8#,$$J#VSHs#0s#/%Js#1$Js#1%Js#1k##$#k##&#$Js#6WSIs#7s#6Ij##S9#j#'%#$Js#8k##S9#k#'(#USJS.US2S.5CHUSKCXS:C$I#USLCUSMC6CS-6Cs$-WSNC$#7Cs#GWSOC#s$*)C%S##*)GDDF#NUSPD-+GDDF$#$VSQ,FVSRS,S;VSSEH(S,#S;m$%#WSTCJIXSUEH$#l#(*)#l#)65#l#*;:#j#+C#j#,C#'EI$#s#X'IH$#s#Zk##%#k#+C#k#,C#+s$?S&,#3#OPl#--&#l#.s#-s#*#l#/s#7s#2#l#0s#;s#9#&s$Is#H5CI)Cs#'S<s##*s#)GDDF#N7Cs#{)C#S#s#**s#,GDDF#N7CJ)C#S#s#-*s#/GDDF#N[SVs#0GDDF#)-s#1GDDF's#)#-s#2GDDF+s#*#l#(#s#)s##l#)/s#5#l#*s#;s#:#j#+C#%Es#v$s$-I$JH%Hs#yVS4$#k##&#k##(#k#+C#3OQRl#-,$#l#.s#Ks#H#l#/s#Us#P#l#0s#Ys#W#VS=Q#8CQs#]BA#&s$iS%%#Ej#&C#)Cs#HS<s#G*s#JGDDF#N-s#KGDDF#s#C#l#(#s#Bs#<l#)s#Os#N#l#*s#Ts#S#j#+C#j#,C#%EI%IHk##$#k#+C#k#,C#&s$yS*3O#Ll#-*%#l#.s#cs#`#l#/s#ms#h#l#0s#qs#o#8CQ6#s#8:ZSWPRs$#M:#ZS>s$}s$#s#|Ls#{#.s%#S+(s%#s#}#WPS%MEl#1&$#j#2s$*#U#Ej#3s$3#$Ps$.&s%.M'Qs#}VS5$#%%$$%&2$#'Rs$,%s#*#$$s#+2$#VS6S(S)(S,#S7j#$%#&s%;S)+s%9R,#'S'#%&#+s%=S'US8#,$$J#US?S@US?#9C#9C%9CS@WSAC$#WSAC&#VSX#SYWSZS.#s$/)Cs$(S#s$)*s$+GDDF#N)Cs#`S#s$**s$-GDDF#NZS[s$.GDDFL[S\s$/GDDF#s#a-s$0GDDF%s$(#-s$1GDDF(s$)#l#(#s$(s#~l#)s$5s$4#l#*-s$9#j#+C#j#,C#j#4SB#$IEVS]Ls${k##s$|#k##%#k#+C#k#,C#k#4SB#&s%bR#s%d##################0#%.s%2YE#S//S%Ol#-81#l#.s$Xs$U#l#/s$bs$]#l#0s#4s#2#VS^K#j#5s#8#U#Ej#3s#D#$s#<s#?1s%yS&4O#S'K.s%xK(s%xE#j#%s%y#UOK'Es$>$#s#ej#&C#5CS$XS:Cs$dI#/S-6C#)Cs$`S##*s$dGDDF#N-s$eGDDF#s$]#l#(#s$\s$Vl#))s$h#l#*s$ns$m#j#+C#j#,C#j#6C#$s$VH$s$US$k##$#k#+C#k#,C#k#6C#+s&6S_,#XEs#7#S/Ll#-,&#l#.s%$s$}#l#/s%.s%)#l#0s#\s#Z#&s&@s#%3S/S&Ol#-s$Gs$?#l#.s%*s%'#l#/s%4s%/#l#0s#bs#`#VS=S&#8CS&s#$*)#YS`S'Os#-K#ZS>s&Es#-s#*S%s#)#.s&GS)(s&Gs#+#WS'S*KEl#1&$#j#7s#4#U#Ej#3s#x#ZSCs#zs#ys#us#8#El#$s$$s#}#j#8s$(#U#Ej#3s%[#ZSCs%]s%\s%Xs$,#El#$s%cs%`#l#'s%js%f#j#1s%l#j#9s&W#j#:s&Z#1s&\S+WSDM#LVS3S(#m#&#j#;s%w#j#<s%|#j#=s&%#j#>s&\#j#?s&^#j#@C#j#As&a##"). Qed.

Section DrvRead.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom bsegs.

  (* [comment removed for export] *)
  Lemma awseg_stage : wseg_ok RSEGS (0x64fe10 : word) 65536%nat = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma store_ok_stage : forall m (a : word) n,
    0x64fe10 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 0x65fe10 -> store_ok RSEGS m a n = true.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StoreOk.store_ok_window); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Nat.of_num_uint); constr:(@Corelib.Init.Number.UIntDecimal); constr:(@Corelib.Init.Decimal.D6); constr:(@Corelib.Init.Decimal.D5); constr:(@Corelib.Init.Decimal.D3); constr:(@Corelib.Init.Decimal.Nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDrvRead.DrvRead.awseg_stage)|] [|@Ha; @__ff; @__varmap; @__wit; @__arith; @__sat0; @__sat1; @Hhi; @Hlo; @n; @a; @m|] "#$c#(#]#B#E#$#%###.#,#+#4#=#>#D#G#J#T#Q#R#Z#[#/#6#5#9#:#@#?#<#;#C#F#H#I#K#L#M#O#V#S#U#N#P#W#X#]#\#^#Y#7#8#'#&#_#0#3#-#1#2#A(#X$#Y$#Z%#[$#\%$H$#$#$#$#$#UI#UJ#UI(UJ#US&#k##&##H$#$###$#$#####################$###$#$#$#$#&#VK?E#H$#$###$#$###############$#$#$#$###$#$#$#$#&##5##############$#$#$#$###$#$#$#$#&#%5s#,VKs#JFUS'EVS($##s#C####################$###$#$#$#$#&#%59WS)s#`s#,S*ULS+US,#UM#UM#UL#US-#US.#'Cs#4'Cs##&s#p&s#lVS/$#VND%%D%VS0'&VND#k##%#k##'#%D+WS1,+Ej##O#j#$%#%D*k##O#k#$(#US2PUS3PUS4CUS5CUS6CVQCs#9VQC8WS7C#s$%XS8C%S9#[S:'S;RRS##S<VS=(S#'S$S%VS>GFWS?S$#S%m$%#WS@CDEXSAGF$#l#%*)#l#&21#l#'54#%s#HAl#($#Gl#)<9#l#*s#'A#bSBSCSDs#4SEs#-Fs#^s#Ls#,s#+#SFEGj#+s#6#j#,s#M#j#-SG#j#.s$9#j#/s$6##"). Qed.

  Lemma mkR_of_upd10 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
    mkR_of (regupd (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) 10 v)
    = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.regupd); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Lists.ListDef.nth); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MainEqv.getr_mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr_other); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr_same); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RegsEquivM.mkR_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MainEqv.mkR_of_getr)|] [|@b; @p; @z; @e; @H0; @E; @v; @x31; @x30; @x29; @x28; @x27; @x26; @x25; @x24; @x23; @x22; @x21; @x20; @x19; @x18; @x17; @x16; @x15; @x14; @x13; @x12; @x11; @x10; @x9; @x8; @x7; @x6; @x5; @x4; @x3; @x2; @x1|] "#.^#D#h###`#$#b#S#B#A#@#?#>#=#<#;#8#7#6#5#4#3#2#1#0#/#.#-#,#+#*#)#(#'#&#%#:#9#D#d#c#J#C#H#G#P#Z#W#L#Y#[#\#e#g#h#i#T#O#N#X#K#U#Q#R#_#a#f#V#]#^#I#M4#X&#Y%#ZB#[&#\)#]'#^&#O%#_$#`)#a)#b$#c$#dC#e(#f$#g$2S92#2#2#2#2#US;#US<#3*US;#VS@#%%HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3E2&+#)'#GWS=&#C+S9)*#G$%#+5)-#G$(#3S9+#)1#G$,#+;)4#G$/#+7)7#G$2#2,+#);#G$6#30+#)?#G$:#+s#()B#G$=#3s#,+#)s#&#G$A#$Bs##3s#*+#)s#+#G$s#&#26+#)s#/#G$s#*#3:+#)s#3#G$s#.#2:+#)s#7#G$s#2#3>+#)s#;#G$s#6#+s#C)s#>#G$s#9#3s#G+#)s#B#G$s#=#2B+#)s#F#G$s#A#3s#&+#)s#J#G$s#E#2s#I+#)s#N#G$s#I#3s#M+#)s#R#G$s#M#2s#-+#)s#V#G$s#Q#3s#1+#)s#Z#G$s#U#2s#1+#)s#^#G$s#Y#3s#5+#)s#b#G$s#]#2s#5+#)s#f#G$s#a#3s#9+#)s#j#G$s#e#2s#9+#)s#n#G$s#i#3s#=+#)s#r#G$s#m#2s#=+#)s#v#G$s#q#3s#A+#)s#z#G$s#u#%s#ss#ps#ls#is#fs#bs#^s#[s#Ws#Vs#Rs#Ns#Js#Fs#Bs#?s#;s#7s#3s#/s#+s#'s##?;73/+'#%S:HIJKLMNOES5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3#s#}C#j#$s#~#%S:HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3WS=#s#|E$#s#z$$s#x$%s#u$&s#s$'s#q$(s#n$)s#k$*s#i$+s#f$,s#b$-s#_$.s#\$/s#Y$0s#V$1s#T$2s#Q$3s#N$4s#K$5s#H$6s#E$7s#B$8s#?$9s#<$:s#9$;s#6$<s#3$=s#0$>s#-$?s#*$@s#'%@?>=<;:98C76543210/.-,+*)('&%$##s$D#s#&j#$s$H#$s$Es$?%Cs##BA@?>=<E;:9876543210/.-,+*)('#s$H#s#*j#$s$L#$s$Is$@$s#*s$D%#Cs#'s#&s#%s#$s##BAE@?>=<;:9876543210/.-,#s$M#s#/j#$s$Q#$s$Ns$A$s#/s$F%(#Cs#+s#*s#)s#(s#'s#&Es#%s#$s##BA@?>=<;:987654321#s$R#s#4j#$s$V#$s$Ss$C$s#4s$G%-(#Cs#/s#.s#-s#,s#+Es#*s#)s#(s#'s#&s#%s#$s##BA@?>=<;:9876#s$W#s#9j#$s$[#$s$Xs$E$s#9s$I%2-(#Cs#3s#2s#1s#0Es#/s#.s#-s#,s#+s#*s#)s#(s#'s#&s#%s#$s##BA@?>=<;#s$\#s#>j#$s$`#$s$]s$F$s#>s$K%72-(#Cs#7s#6s#5Es#4s#3s#2s#1s#0s#/s#.s#-s#,s#+s#*s#)s#(s#'s#&s#%s#$s##BA@#s$a#s#Cj#$s$e#$s$bs$G$s#Cs$L%<72-(#Cs#;s#:Es#9s#8s#7s#6s#5s#4s#3s#2s#1s#0s#/s#.s#-s#,s#+s#*s#)s#(s#'s#&s#%#s$f#s#Hj#$s$j#$s$gs$I$s#Hs$M%A<72-(#Cs#?Es#>s#=s#<s#;s#:s#9s#8s#7s#6s#5s#4s#3s#2s#1s#0s#/s#.s#-s#,s#+s#*#s$k#s#Mj#$s$o#$s$ls$J$s#Ms$O%s#&A<72-(#CEs#Cs#Bs#As#@s#?s#>s#=s#<s#;s#:s#9s#8s#7s#6s#5s#4s#3s#2s#1s#0s#/#s$p#s#Rj#$s$t#$s$qs$J$s#Rs$P%s#+s#&A<72-(#ECs#Gs#Fs#Es#Ds#Cs#Bs#As#@s#?s#>s#=s#<s#;s#:s#9s#8s#7s#6s#5s#4#s$u#s#Wj#$s$y#$s$vs$K$s#Ws$P%s#0s#+s#&A<72-(E#Cs#Ks#Js#Is#Hs#Gs#Fs#Es#Ds#Cs#Bs#As#@s#?s#>s#=s#<s#;s#:s#9#s$z#s#\j#$s$~#$s${s$L$s#\s$Q%s#5s#0s#+s#&A<72-E(#Cs#Os#Ns#Ms#Ls#Ks#Js#Is#Hs#Gs#Fs#Es#Ds#Cs#Bs#As#@s#?s#>#s%##s#aj#$s%'#$s%$s$M$s#as$R%s#:s#5s#0s#+s#&A<72E-(#Cs#Ss#Rs#Qs#Ps#Os#Ns#Ms#Ls#Ks#Js#Is#Hs#Gs#Fs#Es#Ds#C#s%(#s#fj#$s%,#$s%)s$N$s#fs$S%s#?s#:s#5s#0s#+s#&A<7E2-(#Cs#Ws#Vs#Us#Ts#Ss#Rs#Qs#Ps#Os#Ns#Ms#Ls#Ks#Js#Is#H#s%-#s#kj#$s%1#$s%.s$P$s#ks$T%s#Ds#?s#:s#5s#0s#+s#&A<E72-(#Cs#[s#Zs#Ys#Xs#Ws#Vs#Us#Ts#Ss#Rs#Qs#Ps#Os#Ns#M#s%2#s#pj#$s%6#$s%3s$Q$s#ps$V%s#Is#Ds#?s#:s#5s#0s#+s#&AE<72-(#Cs#_s#^s#]s#\s#[s#Zs#Ys#Xs#Ws#Vs#Us#Ts#Ss#R#s%7#s#uj#$s%;#$s%8s$R$s#us$W%s#Ns#Is#Ds#?s#:s#5s#0s#+s#&EA<72-(#Cs#cs#bs#as#`s#_s#^s#]s#\s#[s#Zs#Ys#Xs#W#s%<#s#zj#$s%@#$s%=s$S$s#zs$X%s#Ss#Ns#Is#Ds#?s#:s#5s#0s#+Es#&A<72-(#Cs#gs#fs#es#ds#cs#bs#as#`s#_s#^s#]s#\#s%A#s$#j#$s%E#$s%Bs$T$s$#s$Y%s#Xs#Ss#Ns#Is#Ds#?s#:s#5s#0Es#+s#&A<72-(#Cs#ks#js#is#hs#gs#fs#es#ds#cs#bs#a#s%F#s$(j#$s%J#$s%Gs$U$s$(s$Z%s#]s#Xs#Ss#Ns#Is#Ds#?s#:s#5Es#0s#+s#&A<72-(#Cs#os#ns#ms#ls#ks#js#is#hs#gs#f#s%K#s$-j#$s%O#$s%Ls$V$s$-s$[%s#bs#]s#Xs#Ss#Ns#Is#Ds#?s#:Es#5s#0s#+s#&A<72-(#Cs#ss#rs#qs#ps#os#ns#ms#ls#k#s%P#s$2j#$s%T#$s%Qs$W$s$2s$\%s#gs#bs#]s#Xs#Ss#Ns#Is#Ds#?Es#:s#5s#0s#+s#&A<72-(#Cs#ws#vs#us#ts#ss#rs#qs#p#s%U#s$7j#$s%Y#$s%Vs$X$s$7s$]%s#ls#gs#bs#]s#Xs#Ss#Ns#Is#DEs#?s#:s#5s#0s#+s#&A<72-(#Cs#{s#zs#ys#xs#ws#vs#u#s%Z#s$<j#$s%^#$s%[s$Y$s$<s$^%s#qs#ls#gs#bs#]s#Xs#Ss#Ns#IEs#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$#s#~s#}s#|s#{s#z#s%_#s$Aj#$s%c#$s%`s$Z$s$As$_%s#vs#qs#ls#gs#bs#]s#Xs#Ss#NEs#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$'s$&s$%s$$s$##s%d#s$Fj#$s%h#$s%es$[$s$Fs$`%s#{s#vs#qs#ls#gs#bs#]s#Xs#SEs#Ns#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$+s$*s$)s$(#s%i#s$Kj#$s%m#$s%js$\$s$Ks$a%s$$s#{s#vs#qs#ls#gs#bs#]s#XEs#Ss#Ns#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$/s$.s$-#s%n#s$Pj#$s%r#$s%os$]$s$Ps$b%s$)s$$s#{s#vs#qs#ls#gs#bs#]Es#Xs#Ss#Ns#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$3s$2#s%s#s$Uj#$s%w#$s%ts$^$s$Us$c%s$.s$)s$$s#{s#vs#qs#ls#gs#bEs#]s#Xs#Ss#Ns#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#Cs$7#s%x#s$Zj#$s%|#$s%ys$_$s$Zs$d%s$3s$.s$)s$$s#{s#vs#qs#ls#gEs#bs#]s#Xs#Ss#Ns#Is#Ds#?s#:s#5s#0s#+s#&A<72-(#C#s%}#s$_j#$s&%#*s&$s%x/#VSAs&)S>USBs&)&s&*E#&s&+S3#&s&,S2#&s&-S1#&s&.S0#&s&/S/#&s&0S.#&s&1S-#&s&2S,#&s&3S+#&s&4S*#&s&5S)#&s&6S(#&s&7S'#&s&8S&#&s&9S%#&s&:S$#&s&;S##&s&<R#&s&=Q#&s&>P#&s&?S5#&s&@S4#&s&AO#&s&BN#&s&CM#&s&DL#&s&EK#&s&FJ#&s&GI#&s&HH#&s&Is###(s&Js#%#s#$$s%'s%-%Cs$Ws$Rs$Ms$Hs$Cs$>s$9s$4Es$/s$*s$%s#|s#ws#rs#ms#hs#cs#^s#Ys#Ts#Os#Js#Es#@s#;s#6s#1s#,##s&J#s%,j#$s&N#*s&Ms&B/#(s&Q#*s#+&s&RS3s#+&s&SS2#&s&TS1#&s&US0#&s&VS/#&s&WS.#&s&XS-#&s&YS,#&s&ZS+#&s&[S*#&s&\S)#&s&]S(#&s&^S'#&s&_S&#&s&`S%#&s&aS$#&s&bS##&s&cR#&s&dQ#&s&eP#&s&fS5#&s&gS4#&s&hO#&s&iN#&s&jM#&s&kL#&s&lK#&s&mJ#&s&nI#&s&oH#&s&pS:#&s&qs#K#(s&rs#M#s#L%#Cs$ys$ts$os$js$es$`s$[Es$Vs$Qs$Ls$Gs$Bs$=s$8s$3s$.s$)s$$s#{s#vs#qs#ls#gs#bs#]s#Xs#Ss#*#s&q#s%Sj#$s&u#*s&ts&e/#(s&x#s#1s#R(s&ys#+*s#S%*#Cs${s$vs$qs$ls$gs$bEs$]s$Xs$Ss$Ns$Is$Ds$?s$:s$5s$0s$+s$&s#}s#xs#ss#ns#is#ds#_s#Zs#1#s&x#s%Zj#$s&|#*s&{s&i/#(s'##s#8s#Y(s'$+1s#Z%1*#Cs$}s$xs$ss$ns$iEs$ds$_s$Zs$Us$Ps$Ks$Fs$As$<s$7s$2s$-s$(s$#s#zs#us#ps#ks#fs#as#8#s'##s%aj#$s''#*s'&s&m/#(s'*#s#?s#`(s'++8s#a%81*#Cs%#s$zs$us$pEs$ks$fs$as$\s$Ws$Rs$Ms$Hs$Cs$>s$9s$4s$/s$*s$%s#|s#ws#rs#ms#hs#?#s'*#s%hj#$s'.#*s'-s&p/#(s'1#s#Fs#g(s'2+?s#h%?81*#Cs%%s$|s$wEs$rs$ms$hs$cs$^s$Ys$Ts$Os$Js$Es$@s$;s$6s$1s$,s$'s#~s#ys#ts#os#F#s'1#s%oj#$s'5#*s'4s&s/#(s'8#s#Ms#n(s'9+s#&s#o%s#&?81*#Cs%'s$~Es$ys$ts$os$js$es$`s$[s$Vs$Qs$Ls$Gs$Bs$=s$8s$3s$.s$)s$$s#{s#vs#M#s'8#s%vj#$s'<#*s';s&w/#(s'?#s#Ts#u(s'@+s#-s#v%s#-s#&?81*#Cs%)Es%$s${s$vs$qs$ls$gs$bs$]s$Xs$Ss$Ns$Is$Ds$?s$:s$5s$0s$+s$&s#}s#T#s'?#s%}j#$s'C#*s'Bs&z/#(s'F#s#[s#|(s'G+s#4s#}%s#4s#-s#&?81*#CEs%+s%&s$}s$xs$ss$ns$is$ds$_s$Zs$Us$Ps$Ks$Fs$As$<s$7s$2s$-s$(s#[#s'F#s&(j#$s'J#*s'Is&|/#(s'M#s#bs$'(s'N+s#;s$(%s#;s#4s#-s#&?81*#ECs%-s%(s%#s$zs$us$ps$ks$fs$as$\s$Ws$Rs$Ms$Hs$Cs$>s$9s$4s$/s#b#s'M#s&/j#$s'Q#*s'Ps'#/#(s'T#s#is$.(s'U+s#Bs$/%s#Bs#;s#4s#-s#&?81*E#Cs%/s%*s%%s$|s$ws$rs$ms$hs$cs$^s$Ys$Ts$Os$Js$Es$@s$;s$6s#i#s'T#s&6j#$s'X#*s'Ws'&/#(s'[#s#ps$5(s'\+s#Is$6%s#Is#Bs#;s#4s#-s#&?81E*#Cs%1s%,s%'s$~s$ys$ts$os$js$es$`s$[s$Vs$Qs$Ls$Gs$Bs$=s#p#s'[#s&=j#$s'_#*s'^s')/#(s'b#s#ws$<(s'c+s#Ps$=%s#Ps#Is#Bs#;s#4s#-s#&?8E1*#Cs%3s%.s%)s%$s${s$vs$qs$ls$gs$bs$]s$Xs$Ss$Ns$Is$Ds#w#s'b#s&Dj#$s'f#*s'es',/#(s'i#s#~s$C(s'j+s#Ws$D%s#Ws#Ps#Is#Bs#;s#4s#-s#&?E81*#Cs%5s%0s%+s%&s$}s$xs$ss$ns$is$ds$_s$Zs$Us$Ps$Ks#~#s'i#s&Kj#$s'm#*s'ls'0/#(s'p#s$)s$J(s'q+s#^s$K%s#^s#Ws#Ps#Is#Bs#;s#4s#-s#&E?81*#Cs%7s%2s%-s%(s%#s$zs$us$ps$ks$fs$as$\s$Ws$Rs$)#s'p#s&Rj#$s't#*s'ss'3/#(s'w#s$0s$Q(s'x+s#es$R%s#es#^s#Ws#Ps#Is#Bs#;s#4s#-Es#&?81*#Cs%9s%4s%/s%*s%%s$|s$ws$rs$ms$hs$cs$^s$Ys$0#s'w#s&Yj#$s'{#*s'zs'6/#(s'~#s$7s$X(s(#+s#ls$Y%s#ls#es#^s#Ws#Ps#Is#Bs#;s#4Es#-s#&?81*#Cs%;s%6s%1s%,s%'s$~s$ys$ts$os$js$es$`s$7#s'~#s&`j#$s(&#*s(%s'9/#(s()#s$>s$_(s(*+s#ss$`%s#ss#ls#es#^s#Ws#Ps#Is#Bs#;Es#4s#-s#&?81*#Cs%=s%8s%3s%.s%)s%$s${s$vs$qs$ls$gs$>#s()#s&gj#$s(-#*s(,s'</#(s(0#s$Es$f(s(1+s#zs$g%s#zs#ss#ls#es#^s#Ws#Ps#Is#BEs#;s#4s#-s#&?81*#Cs%?s%:s%5s%0s%+s%&s$}s$xs$ss$ns$E#s(0#s&nj#$s(4#*s(3s'?/#(s(7#s$Ls$m(s(8+s$%s$n%s$%s#zs#ss#ls#es#^s#Ws#Ps#IEs#Bs#;s#4s#-s#&?81*#Cs%As%<s%7s%2s%-s%(s%#s$zs$us$L#s(7#s&uj#$s(;#*s(:s'B/#(s(>#s$Ss$t(s(?+s$,s$u%s$,s$%s#zs#ss#ls#es#^s#Ws#PEs#Is#Bs#;s#4s#-s#&?81*#Cs%Cs%>s%9s%4s%/s%*s%%s$|s$S#s(>#s&|j#$s(B#*s(As'E/#(s(E#s$Zs${(s(F+s$3s$|%s$3s$,s$%s#zs#ss#ls#es#^s#WEs#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Es%@s%;s%6s%1s%,s%'s$Z#s(E#s''j#$s(I#*s(Hs'H/#(s(L#s$as%&(s(M+s$:s%'%s$:s$3s$,s$%s#zs#ss#ls#es#^Es#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Gs%Bs%=s%8s%3s%.s$a#s(L#s'.j#$s(P#*s(Os'K/#(s(S#s$hs%-(s(T+s$As%.%s$As$:s$3s$,s$%s#zs#ss#ls#eEs#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Is%Ds%?s%:s%5s$h#s(S#s'5j#$s(W#*s(Vs'N/#(s(Z#s$os%4(s([+s$Hs%5%s$Hs$As$:s$3s$,s$%s#zs#ss#lEs#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Ks%Fs%As%<s$o#s(Z#s'<j#$s(^#*s(]s'Q/#(s(a#s$vs%;(s(b+s$Os%<%s$Os$Hs$As$:s$3s$,s$%s#zs#sEs#ls#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Ms%Hs%Cs$v#s(a#s'Cj#$s(e#*s(ds'T/#(s(h#s$}s%B(s(i+s$Vs%C%s$Vs$Os$Hs$As$:s$3s$,s$%s#zEs#ss#ls#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Os%Js$}#s(h#s'Jj#$s(l#*s(ks'W/#(s(o#s%(s%I(s(p+s$]s%J%s$]s$Vs$Os$Hs$As$:s$3s$,s$%Es#zs#ss#ls#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%Qs%(#s(o#s'Qj#$s(s#*s(rs'Z/#(s(v#s%/s%P(s(w+s$ds%Q%s$ds$]s$Vs$Os$Hs$As$:s$3s$,Es$%s#zs#ss#ls#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#Cs%/#s(v#s'Xj#$s(z#*s(ys']/#(s(}#s%6s%W(s(~+s$ks%X%s$ks$ds$]s$Vs$Os$Hs$As$:s$3Es$,s$%s#zs#ss#ls#es#^s#Ws#Ps#Is#Bs#;s#4s#-s#&?81*#C#s(}#s'_j#$s)%#%HIJKLMNOS4CPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3EVSCs)$#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es'f's))*&$s%f#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es'l's)+3/$s%m#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es'r's)-<8$s%t#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es'x's)/s#%A$s%{#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es'~'s)1s#.s#*$s&&#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(('s)3s#7s#3$s&-#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(.'s)5s#@s#<$s&4#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(4's)7s#Is#E$s&;#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(:'s)9s#Rs#N$s&B#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(@'s);s#[s#W$s&I#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(F's)=s#ds#`$s&P#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(L's)?s#ms#i$s&W#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(R's)As#vs#r$s&^#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(X's)Cs$#s#{$s&e#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(^'s)Es$,s$($s&l#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(d's)Gs$5s$1$s&s#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(i's)Is$>s$:$s&z#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(o's)Ks$Gs$C$s'%#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es(u's)Ms$Ps$L$s',#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es({'s)Os$Ys$U$s'3#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)%'s)Qs$bs$^$s':#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es),'s)Ss$ks$g$s'A#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)2's)Us$ts$p$s'H#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)7's)Ws$}s$y$s'O#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)='s)Ys%*s%&$s'V#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)C's)[s%3s%/$s']#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)H's)]s%<s%8$s'd#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)M's)_s%Es%A$s'k#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)S's)as%ns%J$s'r#0HIJKLMNOS4S5PQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3Es)X's)cs%ws%s$s'x#US<s)b##s(Gs)^US?s)d,%D#s(Is)`C*s)fs)a#Ds#L#nS7#$#%S6C#&$##S8$##F#FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds#P#G'CVSDFCl#($F#l#)+)#j#).#./m#$#1s)ps)mCs(V#'s)us&Vs&R4s(V##4s(\s)o,5D3s(]s)pC#Ds#b2nS7#$#%S6C#&$#%1$#%F#FnS7#$#%S6C#&$#%F$#%##FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds#g#G7Cl#(#F2l#)*)#j#),#.-m#$#1s*#s)|Cs(i#'s*(s&js&f1s(i##s##s(os)~,s#$DBs(ps*#C#Ds#xA-Ds#y>GBCl#(#F=l#)&%#j#)(#.)m#$#1s*.s*+Cs(x#'s*3s&zs&v-s(x##s#.s(~s*-,s#/Ds#-s)#s*.C#Ds$.s#,nS7#$#%S6C#&$##F$##S8#FnS7#$#%S6C#&$#%F$#%##FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds$3#Gs#1Cl#(#Fs#,l#)*)#j#),#.-m#$#1s*=s*:Cs)/#'s*Bs'2s'.1s)/##s#=s)5s*<,s#>Ds#<s)6s*=C#Ds$Ds#;-Ds$Es#8Gs#<Cl#(#Fs#7l#)&%#j#)(#.)m#$#1s*Hs*ECs)>#'s*Ms'Bs'>-s)>##s#Hs)Ds*G,s#IDs#Gs)Es*HC#Ds$Vs#FnS7#$#%S6C#&$#%F$#%s#E#FnS7#$#%S6C#&$#%#$#%F#FnS7#$#%S6C#&$#%F$#%##FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds$\#Gs#LCl#(#Fs#Gl#)+*#j#)-#..m#$#1s*Xs*UCs)R#'s*]s'Ws'S2s)R##s#Xs)Xs*W,s#YDs#Ws)Ys*XC#Ds$ms#V-Ds$ns#SGs#WCl#(#Fs#Rl#)&%#j#)(#.)m#$#1s*cs*`Cs)a#'s*hs'gs'c-s)a##s#cs)gs*b,s#dDs#bs)hs*cC#Ds%#s#a-Ds%$s#4Gs#bCl#(#Fs#]l#)&%#j#)(#.)m#$#1s*ns*kCs)p#'s*ss'ws's-s)p##s#ns)vs*m,s#oDs#ms)ws*nC#Ds%5s#l-Ds%6s#iGs#mCl#(#Fs#hl#)&%#j#)(#.)m#$#1s*ys*vCs*##'s*~s(+s('-s*###s#ys*)s*x,s#zDs#xs**s*yC#Ds%Gs#w-Ds%Hs#dGs#xCl#(#Fs#sl#)&%#j#)(#.)m#$#1s+(s+%Cs*2#'s+-s(;s(7-s*2##s$(s*8s+',s$)Ds$'s*9s+(C#Ds%Ys$&-Ds%Zs$#Gs$'Cl#(#Fs#~l#)&%#j#)(#.)m#$#1s+3s+0Cs*A#'s+8s(Ks(G-s*A##s$3s*Gs+2,s$4Ds$2s*Hs+3C#Ds%ks$1-Ds%ls#`Gs$2Cl#(#Fs$-l#)&%#j#)(#.)m#$#1s+>s+;Cs*P#'s+Cs([s(W-s*P##s$>s*Vs+=,s$?Ds$=s*Ws+>C#Ds%}s$<-Ds%~s$9Gs$=Cl#(#Fs$8l#)&%#j#)(#.)m#$#1s+Is+FCs*_#'s+Ns(ks(g-s*_##s$Is*es+H,s$JDs$Hs*fs+IC#Ds&3s$GnS7#$#%S6C#&$#%s#x$#%F#FnS7#$#%S6C#&$#%F$#%##FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds&8#Gs$LCl#(#Fs$Gl#)*)#j#),#.-m#$#1s+Xs+UCs*r#'s+]s)#s({1s*r##s$Xs*xs+W,s$YDs$Ws*ys+XC#Ds&Is$V-Ds&Js$SGs$WCl#(#Fs$Rl#)&%#j#)(#.)m#$#1s+cs+`Cs+%#'s+hs)3s)/-s+%##s$cs++s+b,s$dDs$bs+,s+cC#Ds&[s$a-Ds&\s$4Gs$bCl#(#Fs$]l#)&%#j#)(#.)m#$#1s+ns+kCs+4#'s+ss)Cs)?-s+4##s$ns+9s+m,s$oDs$ms+:s+nC#Ds&ms$l-Ds&ns$iGs$mCl#(#Fs$hl#)&%#j#)(#.)m#$#1s+ys+vCs+B#'s+~s)Ss)O-s+B##s$ys+Hs+x,s$zDs$xs+Is+yC#Ds'#s$w-Ds'$s$dGs$xCl#(#Fs$sl#)&%#j#)(#.)m#$#1s,(s,%Cs+Q#'s,-s)cs)_-s+Q##s%(s+Ws,',s%)Ds%'s+Xs,(C#Ds'5s%&-Ds'6s%#Gs%'Cl#(#Fs$~l#)&%#j#)(#.)m#$#1s,3s,0Cs+`#'s,8s)ss)o-s+`##s%3s+fs,2,s%4Ds%2s+gs,3C#Ds'Gs%1-Ds'Hs$`Gs%2Cl#(#Fs%-l#)&%#j#)(#.)m#$#1s,>s,;Cs+o#'s,Cs*'s*#-s+o##s%>s+us,=,s%?Ds%=s+vs,>C#Ds'Ys%<-Ds'Zs%9Gs%=Cl#(#Fs%8l#)&%#j#)(#.)m#$#1s,Is,FCs+~#'s,Ns*7s*3-s+~##s%Is,)s,H,s%JDs%Hs,*s,IC#Ds'ks%G-Ds'ls%DGs%HCl#(#Fs%Cl#)&%#j#)(#.)m#$#1s,Ts,QCs,2#'s,Ys*Gs*C-s,2##s%Ts,8s,S,s%UDs%Ss,9s,TC#Ds'}s%R-Ds'~s%%Gs%SCl#(#Fs%Nl#)&%#j#)(#.)m#$#1s,_s,\Cs,A#'s,ds*Ws*S-s,A##s%_s,Fs,^,s%`Ds%^s,Gs,_C#Ds(3s%]-Ds(4s%ZGs%^Cl#(#Fs%Yl#)&%#j#)(#.)m#$#1s,js,gCs,O#'s,os*gs*c-s,O##s%js,Us,i,s%kDs%is,Vs,jC#Ds(Es%hnS7#$#%S6C#&$##F$##F#S8nS7#$#%S6C#&$#%#$#%F#FnS7#$#%S6C#&$#%F$#%##FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds(K#Gs%nCl#(#Fs%il#)+*#j#)-#..m#$#1s,zs,wCs,c#'s-#s*|s*x2s,c##s%zs,is,y,s%{Ds%ys,js,zC#Ds(\s%x-Ds(]s%uGs%yCl#(#Fs%tl#)&%#j#)(#.)m#$#1s-)s-&Cs,r#'s-.s+0s+,-s,r##s&)s,ws-(,s&*Ds&(s,xs-)C#Ds(ns&'-Ds(os%VGs&(Cl#(#Fs&#l#)&%#j#)(#.)m#$#1s-4s-1Cs-$#'s-9s+@s+<-s-$##s&4s-)s-3,s&5Ds&3s-*s-4C#Ds)$s&2-Ds)%s&/Gs&3Cl#(#Fs&.l#)&%#j#)(#.)m#$#1s-?s-<Cs-2#'s-Ds+Ps+L-s-2##s&?s-8s->,s&@Ds&>s-9s-?C#Ds)Vs&=nS7#$#%S6C#&$#%F$#%s#3#FnD#$#&S6C#&#F$#%#$#%Fj#'D#-Ds)Z#Gs&ACl#(#Fs&<l#))(#j#)+#.,m#$#1s-Ms-JCs-D#'s-Rs+cs+_0s-D##s&Ms-Is-L,s&NDs&Ls-Js-MC#Ds*1s&KnD#$#&S6C#&#F$#%s#A$#%Fj#'D#-Ds*4#Gs&NCl#(#Fs&Il#)('#j#)*#.+m#$#1s-Zs-WCs-T#'s-_s+ts+q/s-T#)s-^S>G#s&[s-Z#,s&\Ds&Zs-[$C*s-a%#Ds&Z#nD#$#&S6C#&#F$##S8$##Fj#'D#-Ds&]#G&Cl#(#Fs&Xl#))'#j#)+#.,m#$#XSEs-is-fC#'s-nCs,(1s-F#USFs-gUSGs-h's-ns,Qs,N%$#j#*s-r#j#+s-s#j#,s-t#j#-s-u#j#.s-v#j#/s-w#j#0s-x#j#1s-y#j#2s-z#j#3s-{#j#4s-|#j#5s-}#j#6s-~#j#7s.##j#8s.$#j#9s.%#j#:s.&#j#;s.'#j#<s.(#j#=s.)#j#>s.*#j#?s.+#j#@s.,#j#As.-#j#Bs..#j#Cs./#j#Ds.0#j#Es.1#j#Fs.2#j#Gs.3#j#Hs.4#j#Is.5##"). Qed.

  Lemma aconst_ok_stage : aconst_ok (AREAD_STAGE, (AREAD_STAGE + 65536)%Z).
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.aconst_ok_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAD_STAGE); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHBASE_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMEMCPYP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AINITED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AHIEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ADYING_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.APGSZ_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACANPOISON_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AVERBOSITY_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_TLSGA_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ATSD_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREGISTERED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACOVFLAG_CELL); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.Tauto.X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ASHADOW_BASE_val); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP)|] [|@__ff; @__varmap; @__wit; @__arith; @z; @__x1; @__p1; @__sat0; @__sat1|] "#.[#'#d#9#4#:#8#@#A###+#J#%#/#$#1#E#F#M#N#O#P#Q#R#S#T#U#V#W#X#Z#[#'#c#0#2#3#5#7#B#D#H#G#I#C#\#^#_#`#&#Y#a#b#d#e#*#.#?#L#<#;#K#-#>#,#6#=#]/#X$#Y$#Z%#['#\*#]%#^$#_%#`%#a*#b&#c+#M##############################)##M##############################)#$M####$#####$#$#$#$#$#$#$#########$#########)#$s#($#####$#########################)#$s#;########$###$#$#########$#########)#$4$###$###$#$#$#$###$#$#$#######)##:########)#$8####$#####$#####$#$#######)#$*##########)#$s#j$#$#$#$#$#####$###$#$###$#$#$#####)##2$#####$#####$#$###########)##s#M##########$#$#$#####)#$s#%##$#######)#$s#1##########$###$#####)##s#p$###$#$#$#$#$###$#$#$#######)#$1##########$#$#$#$#######)##s#G$#$#######)##s$E$#####$###$#######)#$s#M##########)#$s%(########$###$#$#$#$#####$#$#######)#$0##########$###$#######)##s#W####$#################)#$s#r####$#$###########)##s$V######$#############################)#+Js%xUS2OUS3OUS4DUS5DUS6D$M####$#####$#$#$#$#$#$#$#$#$#$###$#########)#*Ds%~*Ds&:-D$#$s&[$#####$#########################)#*Ds&%&D6G#'s#1FCCE#H$s&q########$###$#$#$#$###$#$#########)#*Ds&(&D#Gs#.'s#GFCCE#H,s#HFCCE9#VS7s#IEVS8PQVS9ILWS:P#Qm$%#WS;DKNXS<IL$#l#$*)#l#%s#Ss#R#l#&s#Vs#U#+s&[s&r%#s&J%s&8s&]($#l#''#I%s#]s&N%s&<J($#m#&#$s#+$###$#$#####$###$#$#$#$#######)#*Ds&?&Ds#TG#'s#oFCCE#H)s#m*D#-D'#&D#Gs#['s#tFCCE#H,s#uFCCE(#l#$#s#/s#)l#%s#ys#x#l#&s#|s#{#%s#(s&K+s&L,%#s''(%#l#''#I%s$'R+R1%#J(%#m#'##s#G########)#*Ds&U&Ds#pG#'s$/FCCE#H)s'm*D#-D'#&D#Gs#w's$4FCCE#H,s$5FCCE(#l#$#s#Ks#El#%s$9s$8#l#&s$<s$;#%s#Ds&a+s&b,%#s'C(%#l#''#I%s$CS#+S#1%#J(%#m#'#$s#D####$#$#####$###$#$#######)#*Ds&k&Ds$9G#'s$TFCCE#H)s(9*D#-D'#&D#Gs$@'s$YFCCE#H,s$ZFCCE(#l#$#s#ps#jl#%s$^s$]#l#&s$as$`#%s#is&w+s&x,%#s'h(%#l#''#I%s$hS$+S$1%#J(%#m#'#$@##########)#*Ds'%&Ds$VG#'s$qFCCE#H#s$o)#*D#-D(#&D#Gs$^'s$wFCCE#H,s$xFCCE)#l#$#s$2s$,l#%s$|s${#l#&s%#s$~#%s$+s'2+s'3,%#s(*(%#l#''#I%s%*S%+S%1%#J(%#m#'#$s%($#$#$#$#$###$#####$#####$#$#$#####)#*Ds'<&Ds%$G#'s%?FCCE#H)s)#*D#-D'#&D#Gs%+'s%DFCCE#H,s%EFCCE(#l#$#s$[s$Ul#%s%Is%H#l#&s%Ls%K#%s$Ts'H+s'I,%#s(S(%#l#''#I%s%SS&+S&1%#J(%#m#'##s#($###$#########$###########)#*Ds'R&Ds%IG#'s%dFCCE#H)s)G*D#-D'#&D#Gs%P's%iFCCE#H,s%jFCCE(#l#$#s%$s$zl#%s%ns%m#l#&s%qs%p#%s$ys'^+s'_,%#s(x(%#l#''#I%s%xS'+S'1%#J(%#m#'##s$w####$#$#$###$#$#$#####)#*Ds'i&Ds%lG#'s&+FCCE#H)M*D#-D'#&D#Gs%s's&0FCCE#H,s&1FCCE(#l#$#s%Gs%Al#%s&5s&4#l#&s&8s&7#%s%@s'u+s'v,%#s)?(%#l#''#I%s&?S(+S(1%#J(%#m#'#$s#h##$#######)#*Ds(#&Ds&-G#'s&HFCCE#H$s#u$#$###$###$#####)#*Ds($&D#Gs&<'s&UFCCE#H,s&VFCCE0#l#$#s%ls%fl#%s&Zs&Y#l#&s&]s&\#%s%es(7%s(,s)c($#l#'&#I%s&cs(;%s(0J($#m#&##s%d$#$#######$###$#$#$#$#######)#*Ds(3&Ds&YG#'s&tFCCE#H$1######$#$#$#######)#*Ds(3&D#Gs&i's'&FCCE#H,s''FCCE1#l#$#s&=s&7l#%s'+s'*#l#&s'.s'-#%s&6s(H%s(;s*4($#l#'&#I%s'4s(L%s(?J($#m#&##s$7$#$#######)#*Ds(B&Ds&}G#'s'<FCCE#H-D%s$Z&D#Gs'&'s'?FCCE#H,s'@FCCE&#l#$#s&Vs&Pl#%s'Ds'C#l#&s'Gs'F#%s&Os(L+s(Ms$c%#s*N(%#l#''#I%s'NS)+S)s$h%#J(%#m#'##s&r$#$#####$#######)#*Ds(U&Ds'?G#'s'ZFCCE#H-D%s$S&D#Gs'D's']FCCE#H,s'^FCCE&#l#$#s&ts&nl#%s'bs'a#l#&s'es'd#%s&ms(_+s(`s$\%#s*l(%#l#''#I%s'lS*+S*s$a%#J(%#m#'#$s$M##########)#*Ds(i&Ds'ZG#'s'uFCCE#H-D%s$n&D#Gs'_'s'xFCCE#H,s'yFCCE&#l#$#s'3s'-l#%s'}s'|#l#&s($s(##%s',s(s+s(ts$w%#s++(%#l#''#I%s(+S++S+s$|%#J(%#m#'#$s('########$#$#####$#$#####$#########)#*Ds(}&Ds(%G#'s(@FCCE#H$1######$###########)#*Ds(~&D#Gs(5's(NFCCE#H,s(OFCCE1#l#$#s'es'_l#%s(Ss(R#l#&s(Vs(U#%s'^s)6%s)*s+\($#l#'&#I%s(\s):%s).J($#m#&##s$V####$###$#$#############)#*Ds)2&Ds(PG#'s(kFCCE#H-D%s%d&D#Gs(U's(nFCCE#H,s(oFCCE&#l#$#s()s(#l#%s(ss(r#l#&s(vs(u#%s'~s)<+s)=s%m%#s+}(%#l#''#I%s(}S,+S,s%r%#J(%#m#'#$s&P##########$###########)#*Ds)H&Ds(qG#'s)0FCCE#H-D%s%b&D#Gs(v's)3FCCE#H,s)4FCCE&#l#$#s(Js(Dl#%s)8s)7#l#&s);s):#%s(Cs)R+s)Ss%k%#s,B(%#l#''#I%s)BS-+S-s%p%#J(%#m#'#$s)A$#$#$#$#$#$#$#$#$#$#$#$#$###############################)#VS.s-#s&Y+I#%s(m#$s$8############################)#VS.s)ys&l+I#%#s,}(6#j#(D#VS/s-;s&q%Ks-<%Ks&s%K=k##$#k##&#VS/s*(s&w%Ks*)%K/k##)#k##%#VS=DN*DK&D#Gs)l's**FCCE#HUS>C&D&Gs'$'s*-FCCE#HVS?DM&D)G#'s*0FCCE#H.s*1FCCE&(#.s*2FCCE*)#*Ds#2-D#(&Ds)wG#'s*6FCCE#HZS@s*7FCCESA,s*8FCCE$#.s*9FCCE)0#l#$#s)Os)Il#%6s*<#l#&s*@s*?#j#)D#j#*S0#%KLk##s#$#k##s#&#+s#AN%s)N#(#Lk##&#k#)D#k#*S0#+s#Gs#3%#s-QWI#s#HLl#'/&#l#+s#,s#(#l#,s#3s#.#ZSBDs#Ms#5#SCSDUS1SE%s*U#US1SF%#J(%#m#(#gSGJs*Zs)Xs)1s(qs(Ls(.s'as'<s&us&Rs&%s%fs%Hs%-s$Ys$7s#r##"). Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.False Sort Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aread_stage_file : forall s msF mo regs mem (fd cnt lo : Z) (p : list byte) (off : word) (data : list byte) (ra : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 AREAD_STAGE -> getr regs 12 = Z_to_bv 64 cnt ->
    0 <= fd < 2 ^ 32 -> 1 <= cnt <= 65536 ->
    stk bsegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AREAD_STACK ->
    mem_inv bsegs mem -> ACONST mem ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
    let bs := file_read data off (Z_to_bv 64 cnt) in
    (forall regs' mem' msF' mo',
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> getr regs' 10 = len_word bs ->
       munch [(AREAD_STAGE, AREAD_STAGE + 65536); (bv_unsigned (getr regs 2) - AREAD_STACK, bv_unsigned (getr regs 2))] mem mem' ->
       wmono bsegs mem mem' -> mem_inv bsegs mem' -> stk bsegs mem' lo (bv_unsigned (getr regs 2)) -> ACONST mem' ->
       rdn RSEGS mem' (Z_to_bv 64 AREAD_STAGE) (length bs) = Some bs ->
       m_fs mo' = m_fs mo -> m_fds mo' = fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
       m_channel_reader mo' = m_channel_reader mo ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) K.
  Proof using HCEIL H HH DL.
    (* Text proof on the shape of openssl/echconfiglist_parser's Both/As/AsDrvRead.v [aread_stage_file]; each lemma
       is one the former recorded proof named, and the frame cells are this unit's (Bo/N9_read.v:50-51,65-66).
       The new last premise of the continuation: [same_but_materialized_reader] (As/LazyRestrict.v:852) across
       the read, and [adl_rdr] (Bo/AsDriverLaws.v:45) across the two [aevt_call]s. *)
    intros s msF mo regs mem fd cnt lo p off data ra K HV HA Hra Hra64 Hra2 Htp H10 H11 H12 Hfd Hcnt HSTK HCL HLO HINV HAC Hlk Hfs bs HK.
    pose proof (u64_range (getr regs 2)) as Hsp. acb. pose proof HLO as HLO'. unfold AREAD_STACK in HLO'.
    eapply (aevt_call H HH DL _ s msF mo regs _ mem K HV HA).
    { rewrite mkR_of_getr, Hra, Htp, H10, H11, H12.
      eapply aread_pre with (lo := lo) (fd := fd) (buf := AREAD_STAGE) (cnt := cnt);
        [ exact HCL | exact HLO | lia | reflexivity | reflexivity | reflexivity | exact HSTK | exact HINV | exact HAC
        | exact (proj1 (proj2 (ACONST_drv_reals mem HAC))) ]. }
    intros msF1 mo1 HA1 MP1 HP1.
    destruct HP1 as (m1 & fj & fj2 & HV1 & MU1 & WM1 & INV1 & STK1 & FR1 & FRJ1 & FRM1 & AC1 & RRD1).
    (* [comment removed for export] *)
    unfold read_at in HV1. change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV1.
    set (R1 := mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HV1.
    assert (G10 : getr R1 10 = Z_to_bv 64 fd) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G11 : getr R1 11 = Z_to_bv 64 AREAD_STAGE) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G12 : getr R1 12 = Z_to_bv 64 cnt) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G17 : getr R1 17 = Z_to_bv 64 63) by (subst R1; rewrite getr_mkR; reflexivity).
    eapply (drv_read_file H DL s msF1 R1 (Z_to_bv 64 AREAD_ECALL) m1 mo1 ECALLW (Z_to_bv 64 fd) p off data cnt K AECALL is_ecall_ECALLW HV1 HA1 G17 G10);
      [ rewrite u_small by lia; lia
      | destruct (adl_mpres H DL _ _ MP1) as (_ & E & _); rewrite E; exact Hlk
      | rewrite (proj1 (adl_mpres H DL _ _ MP1)); exact Hfs
      | exact G12
      | lia | unfold MAX_RW_COUNT; lia | lia
      | rewrite G11, u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE, TASK_SIZE; lia
      | | ].
    { rewrite G11. apply store_ok_stage; rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia. }
    cbv zeta. rewrite G11, G12. fold bs. intros msF2 mo2 HV2 HA2 SB2.
    (* [comment removed for export] *)
    set (m2 := wbytes m1 (Z_to_bv 64 AREAD_STAGE) bs) in HV2.
    assert (Lbs : Z.of_nat (length bs) <= cnt).
    { subst bs. pose proof (proj1 (file_read_length_le data off (Z_to_bv 64 cnt))) as FL. unfold word_to_nat in FL. rewrite u_small in FL by lia. lia. }
    assert (MU2 : munch [(AREAD_STAGE, AREAD_STAGE + 65536)]%Z m1 m2).
    { subst m2. rewrite MainMem.wbytes_eq. replace (Z_to_bv 64 AREAD_STAGE) with (wa AREAD_STAGE) by reflexivity.
      apply munch_write; [apply munch_refl | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia | cbn; left; unfold AREAD_STAGE; lia]. }
    assert (WM2 : wmono bsegs m1 m2) by (subst m2; rewrite MainMem.wbytes_eq; apply wmono_write; apply wmono_refl).
    assert (INV2 : mem_inv bsegs m2) by (subst m2; apply amem_inv_wbytes_data; [exact INV1 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia]).
    assert (STK2 : stk bsegs m2 lo (bv_unsigned (getr regs 2) + -2144)).
    { subst m2. rewrite MainMem.wbytes_eq. replace (Z_to_bv 64 AREAD_STAGE) with (wa AREAD_STAGE) by reflexivity.
      apply stk_write; [exact STK1 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia]. }
    assert (AC2 : ACONST m2).
    { eapply ACONST_frame; [exact AC1 | exact MU2 | exact WM2 |]. constructor; [apply aconst_ok_stage | constructor]. }
    assert (DJ : forall a n, aceil <= a -> disjoint_from [(AREAD_STAGE, AREAD_STAGE + 65536)]%Z a n).
    { intros a n Ha. cbn. unfold AREAD_STAGE. lia. }
    assert (FR2' : rw_cells bsegs m2 (bv_unsigned (getr regs 2) + -48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (Z_to_bv 64 ra)]).
    { eapply rw_cells_transport; [exact FR1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (FRJ2 : rw_cells bsegs m2 (bv_unsigned (getr regs 2) + -2128) [CB 2080 fj]).
    { eapply rw_cells_transport; [exact FRJ1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (FRM2 : rw_cells bsegs m2 (bv_unsigned (getr regs 2) + -2144) [CB 8 fj2; C8 (Z_to_bv 64 0x63040)]).
    { eapply rw_cells_transport; [exact FRM1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (RD2 : rdn RSEGS m2 (Z_to_bv 64 AREAD_STAGE) (length bs) = Some bs).
    { subst m2. apply rdn_wbytes_hit. rewrite u_small by (unfold AREAD_STAGE; lia). unfold AREAD_STAGE; lia. }
    (* [comment removed for export] *)
    assert (FS2 : m_fs mo2 = m_fs mo).
    { rewrite (same_but_materialized_fs _ _ SB2). cbn. exact (proj1 (adl_mpres H DL _ _ MP1)). }
    assert (FDS2 : m_fds mo2 = fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)).
    { rewrite (same_but_materialized_fds _ _ SB2), with_fds_fds. destruct (adl_mpres H DL _ _ MP1) as (_ & E & _). rewrite E. reflexivity. }
    assert (RDR2 : m_channel_reader mo2 = m_channel_reader mo).
    { rewrite (same_but_materialized_reader _ _ SB2). exact (adl_rdr H DL _ _ MP1). }
    (* [comment removed for export] *)
    assert (TAIL : forall msF3 mo3 (x10 : word),
      as_AKREL H s (mkCfg msF3 mo3) -> as_MPRES H mo2 mo3 ->
      aread_ret_post (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
        (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
        (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) lo x10 m2 (as_VIS H s msF3) ->
      x10 = len_word bs ->
      realizes bsegs (mkCfg msF3 mo3) K).
    { intros msF3 mo3 x10 HA3 MP3 HP3 Ex10. unfold aread_ret_post in HP3.
      destruct HP3 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & HV3 & MU3 & WM3 & INV3 & STK3 & AC3).
      rewrite (ret_pc_even ra Hra64 Hra2) in HV3.
      change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV3.
      apply (HK _ m3 msF3 mo3 HV3 HA3).
      - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
          rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
      - rewrite (getr_mkR (Z_to_bv 64 ra)). cbn. exact Ex10.
      - intros x Hx. cbn in Hx. unfold AREAD_STACK, AREAD_STAGE in *.
        rewrite (MU3 x) by (cbn; lia). rewrite (MU2 x) by (cbn; lia). apply MU1. cbn. lia.
      - eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]].
      - exact INV3.
      - exact STK3.
      - exact AC3.
      - rewrite (rdn_ext RSEGS (length bs) m3 m2); [exact RD2 | rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia |].
        intros x Hx. rewrite u_small in Hx by (unfold AREAD_STAGE; lia). apply MU3. cbn. unfold AREAD_STAGE in Hx. lia.
      - rewrite (proj1 (adl_mpres H DL _ _ MP3)). exact FS2.
      - destruct (adl_mpres H DL _ _ MP3) as (_ & E' & _). rewrite E'. exact FDS2.
      - rewrite (adl_rdr H DL _ _ MP3). exact RDR2. }
    (* [comment removed for export] *)
    rewrite AgentLib.v_addi_lit in HV2 by (unfold AREAD_ECALL; lia).
    destruct (Nat.eq_dec (length bs) 0) as [L0|Lp].
    - eapply (aevt_call H HH DL _ s msF2 mo2 _ _ m2 K HV2 HA2).
      { subst R1. rewrite mkR_of_upd10, len_word_of_nat, L0. change (Z.of_nat 0) with 0.
        eapply aread_post_zero;
          [ exact HLO | lia | exact INV2 | exact STK2 | exact FR2' | exact FRJ2 | exact FRM2 | exact AC2 ]. }
      intros msF3 mo3 HA3 MP3 HP3. eapply (TAIL msF3 mo3 _ HA3 MP3 HP3). rewrite len_word_of_nat, L0. reflexivity.
    - eapply (aevt_call H HH DL _ s msF2 mo2 _ _ m2 K HV2 HA2).
      { subst R1. rewrite mkR_of_upd10, len_word_of_nat.
        eapply aread_post_pos;
          [ exact HCL | exact HLO | lia | unfold AREAD_STAGE; lia | unfold AREAD_STAGE, AAPP_HI; lia
          | exact INV2 | exact STK2 | exact FR2' | exact FRJ2 | exact FRM2 | exact AC2
          | lia | lia
          | eapply addressable_accessible; [apply ACONST_read_stage; exact AC2 | lia | lia | unfold AREAD_STAGE, AAPP_HI; lia]
          | apply ACONST_shvis; [exact AC2 | unfold AREAD_STAGE, AIMG_LO; lia | lia | unfold AREAD_STAGE, AIMG_TOP; lia]
          | left; unfold AREAD_STAGE; rewrite ASHADOW_BASE_val; lia ]. }
      intros msF3 mo3 HA3 MP3 HP3. eapply (TAIL msF3 mo3 _ HA3 MP3 HP3). rewrite len_word_of_nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aread_stage_dir : forall s msF mo regs mem (fd cnt lo : Z) (errv : word) (ra : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 AREAD_STAGE -> getr regs 12 = Z_to_bv 64 cnt ->
    0 <= fd < 2 ^ 32 -> 1 <= cnt <= 65536 ->
    stk bsegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AREAD_STACK ->
    mem_inv bsegs mem -> ACONST mem -> rw_cells bsegs mem AERRNO [C4 errv] ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
    (forall regs' mem' msF' mo',
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> bv_unsigned (getr regs' 10) = 2 ^ 64 - 1 ->
       munch [(AERRNO, AERRNO + 4); (bv_unsigned (getr regs 2) - AREAD_STACK, bv_unsigned (getr regs 2))] mem mem' ->
       wmono bsegs mem mem' -> mem_inv bsegs mem' -> stk bsegs mem' lo (bv_unsigned (getr regs 2)) -> ACONST mem' ->
       rw_cells bsegs mem' AERRNO [C4 (Z_to_bv 64 EISDIR)] ->
       m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
       m_channel_reader mo' = m_channel_reader mo ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) K.
  Proof using HCEIL H HH DL.
    (* Text proof on the shape of openssl/echconfiglist_parser's Both/As/AsDrvRead.v [aread_stage_dir]; each lemma
       is one the former recorded proof named.  The new last premise of the continuation is [adl_rdr]
       (Bo/AsDriverLaws.v:45) across the two [aevt_call]s; [drv_read_dir] keeps the model. *)
    intros s msF mo regs mem fd cnt lo errv ra K HV HA Hra Hra64 Hra2 Htp H10 H11 H12 Hfd Hcnt HSTK HCL HLO HINV HAC HERR Hlk HK.
    pose proof (u64_range (getr regs 2)) as Hsp. acb. pose proof HLO as HLO'. unfold AREAD_STACK in HLO'.
    (* [comment removed for export] *)
    eapply (aevt_call H HH DL _ s msF mo regs _ mem K HV HA).
    { rewrite mkR_of_getr, Hra, Htp, H10, H11, H12.
      eapply aread_pre with (lo := lo) (fd := fd) (buf := AREAD_STAGE) (cnt := cnt);
        [ exact HCL | exact HLO | lia | reflexivity | reflexivity | reflexivity | exact HSTK | exact HINV | exact HAC
        | exact (proj1 (proj2 (ACONST_drv_reals mem HAC))) ]. }
    intros msF1 mo1 HA1 MP1 HP1.
    destruct HP1 as (m1 & fj & fj2 & HV1 & MU1 & WM1 & INV1 & STK1 & FR1 & FRJ1 & FRM1 & AC1 & RRD1).
    (* [comment removed for export] *)
    unfold read_at in HV1. change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV1.
    set (R1 := mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HV1.
    assert (G10 : getr R1 10 = Z_to_bv 64 fd) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G11 : getr R1 11 = Z_to_bv 64 AREAD_STAGE) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G12 : getr R1 12 = Z_to_bv 64 cnt) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G17 : getr R1 17 = Z_to_bv 64 63) by (subst R1; rewrite getr_mkR; reflexivity).
    eapply (drv_read_dir H DL s msF1 R1 (Z_to_bv 64 AREAD_ECALL) m1 mo1 ECALLW (Z_to_bv 64 fd) cnt K AECALL is_ecall_ECALLW HV1 HA1 G17 G10);
      [ rewrite u_small by lia; lia
      | destruct (adl_mpres H DL _ _ MP1) as (_ & E & _); rewrite E; exact Hlk
      | exact G12
      | lia | lia
      | rewrite G11, u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE, TASK_SIZE; lia
      | rewrite G11; apply store_ok_stage; rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia
      | ].
    intros msF2 HV2 HA2.
    rewrite AgentLib.v_addi_lit in HV2 by (unfold AREAD_ECALL; lia).
    replace (errno_ret EISDIR) with (Z_to_bv 64 (2 ^ 64 - 21)) in HV2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (ERR1 : rw_cells bsegs m1 AERRNO [C4 errv]).
    { eapply rw_cells_transport; [exact HERR | exact MU1 | exact WM1 |]. cbn. unfold AERRNO, ATP. lia. }
    (* [comment removed for export] *)
    eapply (aevt_call H HH DL _ s msF2 mo1 _ _ m1 K HV2 HA2).
    { subst R1. rewrite mkR_of_upd10.
      eapply aread_post_err;
        [ exact HCL | exact HLO | lia | exact INV1 | exact STK1 | exact FR1 | exact FRJ1 | exact FRM1 | exact AC1
        | reflexivity | exact ERR1 | lia ]. }
    intros msF3 mo3 HA3 MP3 HP3. unfold aread_err_post in HP3.
    destruct HP3 as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3
                     & HV3 & U10 & MU3 & WM3 & INV3 & STK3 & AC3 & ERR3).
    rewrite (ret_pc_even ra Hra64 Hra2) in HV3.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV3.
    apply (HK _ m3 msF3 mo3 HV3 HA3).
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). cbn. exact U10.
    - intros x Hx. cbn in Hx. unfold AREAD_STACK, AERRNO, ATP in *.
      rewrite (MU3 x) by (cbn; lia). apply MU1. cbn. lia.
    - eapply wmono_trans; [exact WM1 | exact WM3].
    - exact INV3.
    - exact STK3.
    - exact AC3.
    - exact ERR3.
    - rewrite (proj1 (adl_mpres H DL _ _ MP3)). exact (proj1 (adl_mpres H DL _ _ MP1)).
    - destruct (adl_mpres H DL _ _ MP3) as (_ & E3 & _). rewrite E3. destruct (adl_mpres H DL _ _ MP1) as (_ & E1 & _). exact E1.
    - rewrite (adl_rdr H DL _ _ MP3). exact (adl_rdr H DL _ _ MP1).
  Qed.
End DrvRead.

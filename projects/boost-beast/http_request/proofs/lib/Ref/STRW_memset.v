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
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
  u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof.
  intros segs m A n bs i k a ARR LEN (Hi & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
  u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
  mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
  ms_facts A n i k -> a = wa (A + i) ->
  u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
  filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
  length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
  mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
  wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u8arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.filled); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.length); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.STRW_memset.ms_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.STRW_memset.ms_store_ok); constr:(@Corelib.Lists.ListDef.repeat); constr:(@Stdlib.Lists.List.repeat_length); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.upd_bytes); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.u8arr_write_bytes); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.StrFun.filled_updZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.upd_bytes_length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv_store); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch_write); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.inside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono_write)|] [|@n; @j; @SOK; @a; @y; @x; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat3; @__sat2; @z1; @H1; @cstr0; @cstr; @LEN0; @__x2; @__x3; @__x4; @__x5; @__p1; @__p2; @__p3; @__sat4; @z2; @H2; @An; @A0; @H; @Hk; @Hi; @MF; @WM; @MU; @MI; @LEN; @FIL; @ARR; @k; @i; @Q; @cb; @bs; @A; @m; @m0; @segs|] "#*L#K$^#U$3#o##$4$2#V#;#$#:$:#6#@#?#A$8#(#>#C#B#0#5#8#=#<#%#2#1#4#3#7#&#.#/#q#K#+#*#,#D$-#-#)#'#g#i#9$O#S$U#Y#[#F#I#Q#P#b#l#s$$$%#|$&$'$)$7#a$@#n$K$R$V#J#H#f#O#T#_#d#j#r#~#}#z$($*$,$+$/$1$;$<$>$?$=$D$E$F$C$N$M$L$Q#E$B#y$X$Y$Z$\$]$^$_$[$`#p$6$5#Z#^#w$0#v$H#k#{#R#W#X#\#`#]#c$#$I#t#u$.$9$J$G$P$S$W#x#h#N#e$A$T#mN#g%$:%#e%#U&#E$$;'$<*$=%$>&$?%$@+$A%$B&#V$$C&$D%$E$$F'$G&$H%$I'$J&$K&#m)$L%$M%$N&$O&$P%$Q%$R$$S%$T'$U*$V&$W'$X'$Y$$Z$$[%#f%$\)$](HS^3SC3#3#3#3#3#USI#USJ#USI(USJ#US_#k##&#H%k##CS64S<S7S8S#5S#S=S>*)S80S7&I$#6S'S3VS`CC%S3S<7CCS3#USK%+&$#8#S'S49S-S.S'XSaS'S4S7S8%S.S9I#&9S8#GNS/S9F&S?#S@j#$I#`SbS(S0S-S.S'S<S9S7S8S#KF1<S4S9*=#WSL>S4S9:IS9'&$#GS(S0S7%&S?#S@#ES3'S<%S3###S-#ES0%S0S-USMs#1USMs#-VSc$##&#$(#$*#$.#1s#/S.S3=S(S<#0S4>S-#%4S1%S/#US.F#S'F'S4%S'#,F#$&#.(#j#%C#5S.,#*s#=-0S0&I$#6S12%S/S07CCS/#+s#8#s#58#N69S1N7$$#$)#$+#$/#$9#j##?#'S3%S4###S0#ES/#1s#($$#$&##ES''S'%S.###S(#EN%NS(##s#1$%#$'#'S.%S-###N#ES1%S1N##s#9$%#$'#1s#dS(S-=SAS.#>Ns#*$4J$S)#US(F#S/F'S0%S/#,F#$&#.(#j#%C#5S(,#*s#q-0S1&I$#6J1%S)S17CCS)#+s#l#s#i8#L59JL6$$#$)#$+#$/#$9#j##>##ES)#.s#Y$$##:S)#EL%LSA##s#^$%##EJ%JL##s#b$%#1s$0SAN=S*S(#>L>$4P$S+#USAF#S)F'S1%S)#,F#$&#.(#j#%C#5SA,#*s$=-0J&I$#6P1%S+J7CCS+#+s$8#s$58#S$59PS$6$$#$)#$+#$/#$9#j##>##-s$$#ES*%S$S*##s$'%PLI#1s$RS*L*s$S#GS%QF#&S?#S@1s$VS$J=S&K#0S+>P#%4S:%Q#US$F#S*F'S+%S*#,F#$&#.(#j#%C#5S$,#*s$d-0O&I$#6S:2%QO7CCQ#+s$_#s$\8#S%69S:S%7$$#$)#$+#$/#$9#k#&?#j#'s$u#1s$tS+SA*s$u#GS&Os#'#&S?#S@%OJI#=Q#s#*>S$s#?s#+4S%$O#US*F#S+F'J%S+#,F#$&#.(#j#%C#5S*,#*s%*-0P&I$#6S%1%OP7CCO#+s%%#s$~8#S&59S%S&6$$#$)#$+#$/#*s%7S$&I#/'$2EP&C$#USEIUSEC'K'F&C$#&IKFVSdKFWSe%$#j#(I#j#)I#;C/2EFj#)C#U#Pj#)CF;CP`SNCICCSF$S5&SOPP#`SPIC3S52*86)s#$&#XSf85#NUSQJ#Es#/*s%QOUSQ#'$#E#VSRES&,ES&2ES&&C#S&$%##S&E&C&E$$#.&#2ES%VSgs%9s%8,Es%:#Es%:,Es%:k##$#k##&##Es%?WShs%@s%?Kj##SS#j#*%##Es%Ak##SS#k#*(#VSiEs%F;Sj#m##0UK#USKS;HS;?CKUSkCUSlCVSTCE@CSC(C$R#)&HDDG#MUSmD-(HDDG$#$VSn)G;S?S@VSoFS,&S?#S@m$%#WSpCEKXSqFS,$#l#+*)#l#,32#l#-65#j#.C##EF#EKk##$#k#.C#VFS:Nl#/($#l#0?s#+#l#1s#'s#$#l#0s#1s#,#l#2s#3C#l#3s#=s#5#l#4s#As#?#l#5s#Es#D#l#6s#Gs#Z#Js$>F*s&9PK$#j#$I#Js$BJK#Fj#$I#Js$_LK#s#s2EJ'L%$###s#h;CJ`SNCICCSFs#ZS5s#\SOJJ#;C'fSrIIICCCSsS5S5S5SUSts$h)$L(#`SPICSVS5SWSu,(#s#|s#ms#[VSREO,EO2EO&C#O$%##OE&C&E$$#.&#2EQASXA#A#A#A#<C#<C%USvSCVSwC#<C)WSxC$#<C,<C.<CSX/C$#/C&#/C(#/C-#/C/#B#SBB%SB/C,*/C.#/C3#B#SB/C6$B#SB+S;#s#]+S;&#+S;+#+S;-#?CS>USyCCC$S,#?CS#CC#S2%CC%K#Ls#cHDDGS8@Cs'&(Cs#cSD#)s#fHDDG#MDs#gHDDG&#Ls#hHDDGS7(Cs#gSDs#h)s#jHDDG#MDs#kHDDG%#[SYs#lHDDG'#Ls#mHDDGS9USZSC@C#USZs'3@C#(C%SD#)s#sHDDG#MDs#tHDDG)#(C&Rs#t)s#vHDDG#M(C*SDs#v)s#xHDDG#MDs#yHDDG%#[SYs#zHDDG(#@Cs'>EC:#(C#R.)s#~HDDG#M(Cs#~R=)s$$HDDG#MECs$#((C#R5)s$'HDDG#M-s$(HDDG&s$##-s$)HDDG)s$$#-s$*HDDG.s$%#-s$+HDDG=s$&#l#+#s$%s#{l#,s#)s$.#l#-s#0s$1#j#.C#j#7C#j#8C#j#9C#j#:C#j#;S6#j#<S6#j#=S6#&CFS2$S##&CFE$S=#.%#&CS2S#$S7##S#E&CS2E$$#.&#%S#S2##S=#ES=%S>S###S=k##%#k##'#k##*#k##1#k#.C#k#7C#k#8C#k#9C#k#:C#k#;S6#k#<S6#k#=S6#,ES[#SGE,ESG'Sz`F&%$S[SGS=#S>S#S8S/S)l#/s#$(#l#>s$^s$j#l#0s$fs$c#l#>s$ps$k#l#?s#}C#l#@s$+s$##l#2s$tC#l#3s$~s$v#l#4s%&s%$#l#5s%*s%)#l#6s%,s%?#XS{s$;s$7s$2#:Is%Qs$>#s%ENWSLs'{S*L:ILs$C$s&+#]S|S%QOS$Js&-S)s$H#\S}S*S$S+JLS1s$I&&IFs%xj#$I#XS~S$s&Es&1':Is%M$Ns%Z#ZT#S%Qs%hs&3S(FBs$#SB+S;#s$s?CS,CC#Ks#q(Cs$qRs#U)s$sHDDG#M(Cs$sRs#Q)s$uHDDG#M-s$vHDDG%s$q#-s$wHDDGs$ss$r#l#+#s$qs$kl#,*s$z#l#--s$}#j#.C#j#7C##ES,%S,S2#E#k##%#k##s$o#k#.C#k#7C#XFS:SHS3Nl#/+$#l#0s%/s%;#l#1s%7s%4#l#0s%As%<#l#2s%CC#l#3s%Ms%E#l#4s%Qs%O#l#5s%Us%T#l#6s%Ws%j#%QS+%#s%h##s'~j#$I#?CS2CCs$6K#ECs%6s$2VSTCs()WT$C#s(S(C%R#)s%<HDDG#MECs#|s$,(C#Rs$8)s%?HDDG#MECs#ys$/(C#R))s%BHDDG#M-s%CHDDG&s%>#-s%DHDDG*s%?#l#+#s%>s%8l#,1s%G#l#-s#6s%J#j#.C#j#7C#j#8C#j#9C#%FS2##s(;#s#.S>%s#/S>##s(>k##%#k##'#k#.C#k#7C#k#8C#k#9C#'S%ZFS\#S:SHS<S-l#/0%#l#0s%_s%k#l#1s%gs%d#l#0s%qs%l#l#2s%sC#l#3s%}s%u#l#4s&%s&##l#5s&)s&(#l#6s&+s&>#:ILs#/#s''s#[#Os&_'s')%s&a###s&P$&##Qs#8#s#8s&u$$#j#$I#(Cs%jRs$I)s%mHDDG#M(Cs#0Rs#8)s%oHDDG#MDs%pHDDG%#-s%qHDDGs#\s%l#-s%rHDDGs#5s%m#l#+#s%ls%fl#,s#?s%u#l#-s%ys%x#j#.C#j#7C#j#8C#j#9C#%KS,##S2#S,s#\%S,S##s#1#$%#k##s#a#k##(#k#.C#k#7C#k#8C#k#9C#ZFS\s#1S:SHS-Nl#/0$#l#0s&1s&=#l#1s&9s&6#l#0s&Cs&>#l#2s&EC#l#3s&Os&G#l#4s&Ss&Q#l#5s&Ws&V#l#6s&Ys&l#:ILs#'#s'Us$-WT%s#,T&#WT's&zs'2s#0m#$#]T(s&|S&Qs'4s'ZS/s#es#4#ZT)S%S&Qs'4s'[S0Fs&}s&|$#Fs'&s&|s$,#Fs'(s&|s$.#Fs',s&|s$3#Fs'6s&|s$5#j#&s'<#[S]s)Xs'cs'A#S)S'S4j#As'f#j#Bs'i#V#KFj##s'l#j##s(1#Ms(2s(0s'o#Fj#Cs(4#j#Ds(9#V#KFj##s(<#j##s(a#Ms(bs(^s(A#Fj#Cs(f#j#Es(o#V#KFj##s(r#j##s)G#Ms)Hs)=s({#S,l#&s)Ls)J#j#*s)U#j#Fs)Y#j#Gs)[#j#Hs)]#j#Is)d#j#Js)f#j#Ks)j#j#Ls)l#j#'s)t#j#MI#j#NC#j#Os)q#j#Ps)v#j#Qs)t#j#$C#j#RC#j#Ss)x#j#Ts)y#j#Us**##"). Qed.

(* [comment removed for export] *)
Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.


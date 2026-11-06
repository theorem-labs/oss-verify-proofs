(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsAtomics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsDepotInv F_memset AllocWalkKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells bsegs m 1177192 (map (fun v => C8 (wz v)) AGOT_VALS);                       (* [comment removed for export] *)
  re_shb  : rw_cells bsegs m 1234872 [C8 (wz 2147450880)];                                      (* [comment removed for export] *)
  re_hme  : rw_cells bsegs m 1238176 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];           (* [comment removed for export] *)
  re_thresh : rw_cells bsegs m 1831776 [C8 (wz 0xffffffffffffffff)];                                       (* [comment removed for export] *)
  re_mlim : rw_cells bsegs m 1831800 [C8 (wz 0)];                                               (* [comment removed for export] *)
  re_dd   : rw_cells bsegs m 1831875 [C1 (b8 1)];                                               (* [comment removed for export] *)
  re_madv : rw_cells bsegs m 1831900 [C1 b244];                                                 (* [comment removed for export] *)
  re_rms  : rw_cells bsegs m 1185288 [C8 (wz 1121976)];                                         (* [comment removed for export] *)
  re_psc  : rw_cells bsegs m 1823328 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_lpg  : rw_cells bsegs m 6822576 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_ssp  : rw_cells bsegs m 1180656 [C8 (wz 6821936)];                                         (* [comment removed for export] *)
  re_grd  : rw_cells bsegs m 6821936 [C8 g]                                                     (* [comment removed for export] *)
}.

End HCW.

Ltac open_renv E :=
  destruct E as [Rgot Rshb Rhme Rthresh Rmlim Rdd Rmadv Rrms Rpsc Rlpg Rssp Rgrd]; unfold AGOT_VALS in Rgot; cbn [map] in Rgot.

(* [comment removed for export] *)
Ltac split_frame FR sizes :=
  lazymatch type of FR with rw_cells _ _ _ [CB ?n ?j] =>
    let J := fresh "J" in remember j as J in FR;
    match goal with E : J = j |- _ => clear E end;
    apply (rw_cells_split_CB bsegs _ _ [] n J [] sizes) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    repeat match type of FR with context [CB _ (take ?k ?l)] => let K := fresh "jk" in remember (take k l) as K in FR end;
    repeat match type of FR with context [CB _ (drop ?k ?l)] => let K := fresh "jk" in remember (drop k l) as K in FR end;
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.RENV Sort Prop.

Lemma renv_transport : forall g b m m' W,
  RENV g b m -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W 1177192 120 -> disjoint_from W 1234872 8 -> disjoint_from W 1238176 24 -> disjoint_from W 1831776 8 ->
  disjoint_from W 1831800 8 -> disjoint_from W 1831875 1 -> disjoint_from W 1831900 1 -> disjoint_from W 1185288 8 ->
  disjoint_from W 1823328 8 -> disjoint_from W 6822576 8 -> disjoint_from W 1180656 8 -> disjoint_from W 6821936 8 ->
  RENV g b m'.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.RENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.AGOT_VALS); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.mkRENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size)|] [|@v; @re_grd0; @re_ssp0; @re_lpg0; @re_psc0; @re_rms0; @re_madv0; @re_dd0; @re_mlim0; @re_thresh0; @re_hme0; @re_shb0; @re_got0; @re_grd; @re_ssp; @re_lpg; @re_psc; @re_rms; @re_madv; @re_dd; @re_mlim; @re_thresh; @re_hme; @re_shb; @re_got; @WM; @MU; @E; @W; @m'; @m; @b; @g|] "#,G#O#m#]#J#d#e#G#K#H#L#&#'#%#6#4#U#$#(#)#*#+#,#-#.#5###;#A#M#S#R#1#7#c#j#<#=#>#?#@#B#C#D#E#F#N#W#X#Y#[#\#/#0#h#k#8#m#9#:#I#n#a#V#T#`#_#i#^#b#q#p#o#f#g#l#Z0#`$#a$#b$#c&#d&#e'#f$#g$#h-#i$#j$#k$#l&#P##########US.#US/#US.(US/#US?#k##&#US@SA/LKMWSBQKMWSCCLK$0$#$#$#$#$###############$#######%#$P$#$#######%##P####$#$#$#$#$###$#$#####$#$###$#######%#$6##$#$###$###$#$#$#$###$#$#$#######%#$2####$#####$###$###########%#$P##$#$#$#$#$#$#####$#$###$#$###########%#$)$#######%#$2$#########$#$#%#$)$#$#####%##s#M####$###$#$###########$#######%##s#8$#####$#####$#$###########%##s#J##########$#$###$###$###$#$#########%##s#4####$#$#$#$#$#$#########%##<######$#$#########%##s$Q####$#$#$#$###$###$#$#$#######%##s#H$#$#######%##s$+$#$###$#$#$#####%#$s#i##$#########%#$s#p$#$#######%##s#u######%#$s$Z########%#$s$_######%##s$~$###$#$#$#$#$###$#$#$#######%#$s#9##$#######%##s#7########%#'Ks%Bs%W$s&###$#$###$#$#####$###$#$#$#$#######%#%s&5'Ls%D#$4####$#$#####$#$###########%##s&&####%#'Rs%I#$'$#$#$#$#$###$###$#####$###########%#'S#s%Hs#+$*$#######%#'S$s%Is#2$4##########$#$#%#%P'S%s%K#$+$#$#####%#'S&s%L*#s#W####$###$#$#$#$###$###$#######%#'S's%Ms#V#s#>$###$#########$###########%#'S(s%Ns#f$s#U$#########$#$#$#####$#$#$#$#########%#'SDs%Os#{#s#7##$###$#$#####$#########%#'SEs%Ps$.#?$#####$#$#$#########%#'S0s%Rs$;/NS)O/S1NOj##$#-S*,#j#$E#XS2EF#SF(COs';#$s'U$#$#$#$#$#$#$#$#$#$#$###############################%#-#,#US3F&F$#(CS)s'I#$8$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#-SG,#&F#s#)&F$#&F'#(CNs'b#$,$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#&F#s#A(CS1s'c#(CSHs'^<USIs$j.#&F#s#F(CSJs'Y#.S+&F#s#I(CSKs'V##s(t##$#############$#######$#####%#-s&f,#&F#s#^(CS+s'Z##s)8##########%#-#,#&F#s#i(CS4s'V#(CS5s'C$-s'+,#&F#s#n(CS6s'9#,S,&F#s#q(CS7s'1#(CS8s(os$7(CS,s(]s#s(CS9s(Os#L(CS:s(;s#7(CS;s(6s#P(CS<s(.s#4.G&F#s#z(CS=s(+#(CGs'w@(CIs'i6(CSLs'V7(CDs'I3,S-&F#s$%(CHs'A#$s%<$###########%##s%q$###$###$#######%##s&N$#$#######$###$#$#$#$#######%#$s&B######%#$s&H########%##s%f######%##s#4$#$#######%#$s#:########%##s#7$#$#$#####%##s%q$#$#######%#US3E&Es'x#&Es'o#&Es&A#&Es'i#&Es'c#&Es'_#&Es(v#&Es)V#&Es'\#&Es'X#&Es)h#&Es'J#&Es'D#&Es'?#&Es(o#XS2EFs%I#)#*#'Ds*'#m#S=#)s%M*#'Ds*+#m#&#+CDJHs*-s%QS(IG#)s%1*#'Ds)y#m#S<#m##$+CDJHs)|s%6S'IG#)s$k*#'Ds)p#m#S;#m##$+CDJHs)ss$pS&IG#)s$[*#'Ds)a#m#S:#m##$+CDJHs)ds$`S%IG#)s$y*#'Ds)a#m#S9#m##$+CDJHs)ds$~S$IG#)s$b*#'Ds)^#m#S,#m##$+CDJHs)as$gS#IG#.S-&F#s%Q)#*#'Ds)`#m#S8#m##$+CDJHs)c(RIG#)s$X*#'Ds)U#m#S7#m##$+CDJHs)Xs$]LIG#)s$S*#'Ds)L#m#S6#m##$+CDJHs)Os$XKIG#'Ds)<'m#S5#m##$+CDJHs)?s$\MIG#)s$X*#'Ds)4#m#S4#m##$+CDJHs)7s$]QIG#,S>&F#s%o)#*#'Ds)1#m#S+#m##$+CDJHs)4(S*IG#cSMS>S-Hs#Gs#As#;s#5s#/s#)A;51+#j#%s$S#j#&s$W#j#'s$Y#j#(s$[#j#)s$]#j#*s$_#j#+s$c#j#,s$e#j#-s$g#j#.s$i#j#/s$k#j#0s$m#`#S(S'S&S%S$S#RLKMQS*j#1s$p#j#2s$t#j#3s$y#j#4s${#j#5s%+#j#6s%A#j#7s%E#j#8s%J#j#9s%L#j#:s%c#j#;s&0#j#<s&R#ZSNNS)Os&X#S0j##s&\#j##s&j#j##s&z#j##s'4#j##s'E#j##s'X#j##s'`#j##s'l#j##s't#j##s(-#j##s(B#j##s(X#j#=s+k#j#>s+m#j#?s+o#j#@s+q#j#As+s#j#BSO#j#Cs+w#j#Ds+z##"). Qed.

End HCW2.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?g ?b m =>
      region_table; region_hull_memo W;   (* [comment removed for export] *)
      assert (E' : RENV g b m');
      [ apply (renv_transport g b m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma bsegs_below_top : forall seg, In seg bsegs -> Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 6832128.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.AsanUbsan_segment_000); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.AsanUbsan_segment_001); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.AsanUbsan_segment_002); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.AsanUbsan_segment_003); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Corelib.Init.Datatypes.Lt); constr:(@Corelib.Init.Datatypes.Gt); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Datatypes.Eq); constr:(@kc__3)|] [|@seg; @c; @e; @H; @x|] "#%4#.#L#1###;#:#9#F#8#%#6#'#$#H#&#)#(#+#G#.#I#J#*#L#-#2#3#D#A#K#,#M#5#>#B#7#?#@#=#<#E#C#4.#A&#B$#C$#D%#E$#F$#G%#H%#I)#J$#K)WS*CDS+#CKM#CIM#CGM#CFM&#E&%#&'#&)#'J$#(J$#)%#,S,%#%#,#,#%#%#,#%#%#%#%#%#%#%#%#%#%#%#%#%#%#US-#,S,%#,#%#%#%#%#,#%#%#%#%#%#%#%#%#%#%#%#%#%#%#US-#*s#1#j##s#7##CKJ'D$#(D$#)%#*#+j#$C##HS#NnH#$#%S$D#&#E#S%#Ej#&H#+HS##S&NDVS.EDl#'$E#j#((#'K$#(K$#)%#*#9m$)#+CK1#ODj#'9#U#Dj##s#X##CIJ#CGJ#CFJ&#E&%#&'##CIO#CGO#CFO&#E&%#&'#'L$#(L$#)%#*#s#0j##)##CIL'I$#(I$#)%#*#s#8m$s#(#+CIs#0#QDj#'+#U#Dj##:##CGL#CFL&#E&%##CGQ#CFQ&#E&%#'P$#(P$#)%#*#s#Kj##)##CGP'G$#(G$#)%#*#s#Sm$s#C#+CGs#K#S'Dj#'+#U#Dj##8##CFP&#E#CFS'&#E'R$#(R$#)%#*#s#bj##)##CFR#HS(NnH#$#%S$D#&#S%#E#Ej#&H#+HS(#S&NDl#'#Es#Zj#('#'F$#(F$#)%#*#s#pm$)#+CFs#h#S/Dj#'1#U#Dj##<#'S)$#(S)$#)%#*#s#{j##E#VS0#Dj#'E#U#Dj##E#-s#(E@.#Dj#'s#*#U#Dj##s#B#-s#Es#Cs#;s#/#Dj#'s#G#U#Dj##s#a#-s#fs#bs#Zs#N#Dj#'s#h#U#Dj##s$d#-s$ks$es$/s#q#Dj#'s$m#j#$C##"). Qed.

(* [comment removed for export] *)
Definition prm_pb (addr : Z) : Z := round_up (sh addr) 4096.
Definition prm_pe (addr size : Z) : Z := round_down (sh addr + size / 8) 4096.

End HCW3.

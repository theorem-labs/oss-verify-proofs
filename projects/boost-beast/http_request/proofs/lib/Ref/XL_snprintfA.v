(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX
  RefMemcpyLib AgentLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma alu_add_Z : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. rewrite alu_add. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma alu_add_wZ : forall (a : word) b, alu64 ALU_ADD a (Z_to_bv 64 b) = Z_to_bv 64 (bv_unsigned a + b).
Proof. ltac2:(KReplay.runc [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.eq_Transitive); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms.reflexive_proper); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive); constr:(@Corelib.Classes.RelationClasses.eq_Reflexive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Corelib.Classes.RelationClasses.symmetry); constr:(@Corelib.Classes.RelationClasses.eq_Symmetric); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.Z_to_bv_bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.alu_add_Z)|] [|@lemma; @b; @a|] "##Q#&#?#6#$#3#4#%#.#0###,#*#)#2#;#9#8#>#=#5#?#1#@#A#-#+#/#7#:#<(#:$#;%#<'#='#>%#K##########UL#UM#VI$D$%#WH%#DUH&UN'$)DWEFG#VI+G$,#WEF#&k##--k##.#UHC%00,,%1&-#k##C&%C'&$UO4&551#&6+(#&C+(#WP('#XQ)(#E'CFUR;ZS#<8#3GJ'=7bS$C21/E'F&G5$88#VS%7D$A#'A#]S&B>=;8&$$#j#$@#VS's#%DVS(s#$JV%$#j#%S)#j#&s#(##"). Qed.

(* [comment removed for export] *)
Definition SN_FR : Z := 1360.
Definition SN_ENTRY : Z := 0x6af38.
Definition SN_RET : Z := 0x6af90.     (* [comment removed for export] *)
Definition SN_FMT : Z := 0x13289.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record snH (mem : word -> option byte) (sp bufb : word) (can : Z) : Prop := SNH {
  Ssp16  : bv_unsigned sp mod 16 = 0;
  SspLo  : 0x200000 <= bv_unsigned sp;
  SspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Sbb16  : bv_unsigned bufb mod 16 = 0;
  SbbLo  : 0x200000 <= bv_unsigned bufb;
  SbbHi  : bv_unsigned bufb <= 0x7fffffffffff;
  Sstk   : stk_ok RSEGS mem sp SN_FR;
  Sbuf   : forall d m, 0 <= d -> d + Z.of_nat m <= 22 -> store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned bufb + 2 + d)) m = true;
  Sdisj  : bv_unsigned sp <= bv_unsigned bufb + 2 \/ bv_unsigned bufb + 24 <= bv_unsigned sp - SN_FR;
  Simg   : forall i, 0x10000 <= i < 0x7a000 -> mem (Z_to_bv 64 i) = None;   (* [comment removed for export] *)
  Sgot   : rdn RSEGS mem (Z_to_bv 64 0x7f808) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2690)); (* [comment removed for export] *)
  Scan   : rdn RSEGS mem (Z_to_bv 64 0xb2690) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Scan64 : 0 <= can < 2 ^ 64 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sn_vals (regs : bvmap 5 word) (sp bufb : word) (can : Z) : list word :=
  [sp; bufb; Z_to_bv 64 can] ++ junk_vals regs.

Definition snE (regs : bvmap 5 word) (sp bufb : word) (can : Z) : env :=
  Env (vals_ev (sn_vals regs sp bufb can)) (blobs_ev []).

Definition sn_sr : list expr :=
  Eval cbv in (map (fun i => match i with
     | 0 => ELit 0 | 2 => EVar 0 | 10 => EAlu ALU_ADD (EVar 1) (ELit 2) | 11 => ELit 22 | 12 => ELit SN_FMT
     | 13 => ELit 18446744073709551615
     | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition sn_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x200000 0x7fffffffffff;
   KAlign (EVar 1) 16; KRange (EVar 1) 0x200000 0x7fffffffffff;
   KWr (SA (EVar 0) (-1360)) 1360;
   KWr (SA (EVar 1) 2) 22;
   KDisj (SA (EVar 0) (-1360)) 1360 (SA (EVar 1) 2) 22;
   KImg 0x10000 0x7a000;
   KWord (SA (ELit 0) 0x7f808) 8 (ELit 0xb2690);
   KWord (SA (ELit 0) 0xb2690) 8 (EVar 2)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allregs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_idx : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i allregs32 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section Entry.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp bufb : word) (can : Z).
  Hypothesis SH : snH mem sp bufb can.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 (bv_unsigned bufb + 2).
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 22.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 SN_FMT.
  Hypothesis R13 : getr regs 13 = Z_to_bv 64 18446744073709551615.

  Let E := snE regs sp bufb can.

  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, snE, sn_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; bufb; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = bufb. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = Z_to_bv 64 can. Proof. reflexivity. Qed.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.snH Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

  Lemma sn_regs_ok : regs_ok E sn_sr regs.
  Proof.
    ltac2:(KReplay.runc [|constr:(SH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.snH); constr:(mem); constr:(sp); constr:(bufb); constr:(can); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2SoundX.SX2S.regs_ok); constr:(E); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_sr); constr:(regs); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRunX.stk_ok); constr:(@OSSVerify.boost_beast.http_request.images.Plain.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.SN_FR); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.regs_ok_by_idx); constr:(@Corelib.Init.Peano.lt); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@Corelib.Lists.ListDef.nth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.allregs32); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.edenot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SeqExec.getr_zero); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Nat.sub); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.Entry.ev_junk); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(R2); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.alu_add_wZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.Entry.ev1); constr:(R10); constr:(R11); constr:(R12); constr:(R13); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.X)|] [|@m; @d; @i; @Hi; @n; @b; @__ff; @__varmap; @__wit; @__arith; @x; @Ha; @__x1; @__p1; @__sat66; @__sat67; @__sat68; @__sat69; @cstr; @Hi0; @Hb; @Scan65; @Scan0; @Sgot0; @Simg0; @Sdisj0; @Sbuf0; @Sstk0; @SbbHi0; @SbbLo0; @Sbb17; @SspHi0; @SspLo0; @Ssp17; @Scan64; @Scan; @Sgot; @Simg; @Sdisj; @Sbuf; @Sstk; @SbbHi; @SbbLo; @Sbb16; @SspHi; @SspLo; @Ssp16; @s|] "#;K#0$E#?#L$$###=#N#;$%$##<#g#k$*#\$;#i#c#V#t#G#x$)$+#w#F#$#5#7#%#8#6#J#&#]#D#O#R$2#+#A#@#K#W#Y#Z#[#_#^#z$=$?$A$C#0#(#)#4#:#I#P#T#S#`#a#l#m#y#{#|#~$,$.$/$-$0$3$4$5$6$7$8$9$<$>$@$B$D$F#b#/#.#-#,#*#'#9#3#f#e#>#H#M#j#C#p#U$'$&#v#E#Q$:$E#d$(#n#h#q#o#u#}#s#r#B#X$1F#0$$('$)%$*&#3%$+$$,%$-%$.$$/%$0%$1'$2*$3/#6%$4$$5%#4%$6/$7&$8'$9%#($$:)$;&$<%$=%#5%$>)$?*$@'$A%$B$$C$$D&XSKS-S1S.S0WSLILGj##$#+S5+#+#+#+#+#C#VS:#S12'VS;$#&C#S++(+#+#+#+#+#+#+#+#+#+#+#+#+#+#2#1#6(S5(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#2#1s#F#VS:s#HS.VS;#s#G&C#S+1s#7%1&(XSMS2S-S1S<1S+S,9S,)S/#(s#W(#+#2#1'#2s#\)1#)#S33s#Y#XSNS2S-#S/&S6#S7k##)#k##1#k#$D#k#%C#1s#_++s#K+#+#2#)?#VSOs#eS<1$#VSP*#2s#[+S5+#+#+#+#+#+#+#+#+#+#+#+#+#+#+#2#(S5(#(#+#(#+#+#+#+#+#+#+#+#+#+#+#+#+#2#(3(#(#(#+#+#+#+#+#+#+#(#+#+#+#2#(s#6(#+#+#(#+#+#(#(#+#(#+#+#(#+#+#+#+#2#1s#9F+s$>(#+#+#+#+#+#+#+#+#+#+#+#+#+#2#4Fs#7-4#Cs$lD#US=#3s$kS,US-#US>&&&$#k##*#k#&C#US?*US=#+s$W+#(#(#+#(#+#(#+#+#+#2#3s%#s#@#S4##############XS@S2S-+#(s%2+#+#(#+#(#+#+#+#(#+#(#(#+#+#+#+#2#3s%?s#IVSA7#VSBs#.#&s#.8#XS@S2S-&:3s%DS0VSA<#VSBs#3#&s#3&#1S+S02s%JVSQs$R#4S0#-&#USRS.1S+s$d4s$e'-$##s#(##############################################'F#Ds%jCs$xD#;$S+R$$S,M#%G#USSS+$NS,L#*I#&+&#k#'-#j#(D#'S40USTG$.S4M-%G#$NS4L,*I#&4%#m#(#j#'*##F'#:#S,$8#M7%G#$N%L6*I#&>%#k#')#j#(D#'s#gs##=s#es#f9#3s###%G#2S5;s#&#R%G#&s#)#Fj#)s#*#,s#+(<Is#o>s#qs#p#s#0####'s#t#-'#2s&)2s&E1$#(s&F(#2#4'#-'#,C*,C*0DCS%HS&S*s$%,$s$$+#,C(0DCS#HS$S's$&-%1)#?51-)%#USUSCUS?SCUSVCUSWCUSXC8C58C5.C$S(#/&KEEJ#O8C4.C&S)#/)KEEJ#O@*KEEJ&#VSY+J,S6S7VSZFS/&S6#S7m$%#WS[CS+S,XS\FS/$#l#**)#l#+54#l#,87#l#-#@FAs#)A;#Bs$A#:s#[s#8s#3s#2s#1#$s#Zs$FMs#Y%G#$Ns$HLs#X*I#&s#`%#m#(#j#'s#C##s#N'#s#f#s#N$s#d#Ms#c%G#$N%Ls#b*I#&s#j%#k#')#j#(D#'s$Vs#o$s#ls$WMs#k%G#$Ns$YLs#j*I#&s#r%#m#S]#j#')##4'#s#x#4$s#v#Ms#u%G#$N%Ls#t*I#&s#|%#k#')#j#(D#'s$gs$%=s$es$h9#3s$%#%G#;s$'s#SR%G#&s$*#Fj#)s$+#,s$,'<Is$n>s$rs$o's$ps#]-$#2s&:1s#]#4$s#Y-$#,C&0DCS%HS&S*s$zs#as#Ys$w'#0DCS#HS$S's$x($s#es#]s#W?,+('$#8C*.Cs#RS(#/s#TKEEJ#O.C%S)s#P/s#VKEEJ#O@s#WKEEJ%#l#*#s#Os#Il#+s#[s#Z#l#,s#^s#]#l#-#0FA51-#Bs%)#:s$E@<;:#$s$Ds%.Ms$C%G#$Ns%0Ls$B*I#&s$J%#m#(#j#'s#+##s#6'#s$P#s#6$s$N#Ms$M%G#$N%Ls$L*I#&s$T%#k#')#j#(D#'s%>s$Y=s%<s%@9#3s$Y#%G#;s$[s$*R%G#&s$^#Fj#)s$_#,s$`'<Is%E>s%Js%F's%Gs$5-$#2s'Z1s$5#4$s$1-$#,C&0DCS%HS&S*s%Rs$9s$1s%N'#0DCS#HS$S's%O($s$=s$5s$/?,+('$#8C*.Cs$*S(#/s$,KEEJ#O.C%S)s$(/s$.KEEJ#O@s$/KEEJ%#l#*#s$'s#}l#+s$3s$2#l#,s$6s$5#l#-#0FA51-#Bs%\#:s$y@<;:#$s$xs%aMs$w%G#$Ns%cLs$v*I#&s$~%#m#(#j#'s#+##s#6'#s%(#s#6$s%&#Ms%%%G#$N%Ls%$*I#&s%,%#k#')#j#(D#'s%qs%1=s%os%t9#3s%1#%G#2s'M;s%4#R%G#&s%7#Fj#)s%8#,s%9(<Is%y>s&#s%z's%{s$j-$#2s(N1s$j#4$s$f-$#,C&0DCS%HS&S*s&+s$ns$fs&&'#0DCS#HS$S's&'($s$rs$js$d?,+('$#8C*.Cs$_S(#/s$aKEEJ#O.C%S)s$]/s$cKEEJ#O@s$dKEEJ%#l#*#s$\s$Vl#+s$hs$g#l#,s$ks$j#l#-#0FA51-#Bs&4#:s%RA<;:#$s%Qs&9Ms%P%G#$Ns&;Ls%O*I#&s%W%#m#(#j#'s#,##s#7'#s%]#s#7$s%[#Ms%Z%G#$N%Ls%Y*I#&s%a%#k#')#j#(D#'s&Is%f=s%~s&M9#3s%f#%G#;s%hs$:R%G#&s%k#Fj#)s%l#,s%m'<Is&+>s&Ws&,'s&-s%B-$#2s&S1s%B#4$s%>-$#,C&0DCS%HS&S*s&_s%Fs%>s&4'#0DCS#HS$S's&5($s%Js%Bs%<?,+('$#8C*.Cs%7S(#/s%9KEEJ#O.C%S)s%5/s%;KEEJ#O@s%<KEEJ%#l#*#s%4s%.l#+s%@s%?#l#,s%Cs%B#l#-#0FA51-#Bs&B#:s&*@<;:#$s&)s&lMs&(%G#$Ns&nLs&'*I#&s&/%#m#(#j#'s#+##s#6'#s&5#s#6$s&3#Ms&2%G#$N%Ls&1*I#&s&9%#k#')#j#(D#'s&|s&>=s&Us'%9#3s&>#%G#;s&@s$:R%G#&s&C#Fj#)s&D#,s&E'<Is&^>s'/s&_'s&`s%v-$#+s(c2#1s%w#4$s%s-$#,C&0DCS%HS&S*s'8s%{s%ss&h'#0DCS#HS$S's&i($s&#s%ws%q?-,('$#8C*.Cs%lS(#/s%nKEEJ#O.C%S)s%j/s%pKEEJ#O@s%qKEEJ%#l#*#s%is%cl#+s%us%t#l#,s%xs%w#l#-#0FA61-#Bs&v#:s&_A=<;#$s&^s'DMs&]%G#$Ns'FLs&\*I#&s&d%#m#(#j#'s#,##s#7'#s&j#s#7$s&h#Ms&g%G#$N%Ls&f*I#&s&n%#k#')#j#(D#'s'Ts&s=s'-s'Z9#3s&s#%G#;s&us$:R%G#&s&x#Fj#)s&y#,s&z'<Is'6>s'ds'7's'8s&O-$#2s);1s&O#4$s&K-$#,C&0DCS%HS&S*s'ls&Ss&Ks'?'#0DCS#HS$S's'@($s&Ws&Os&I?,+('$#8C*.Cs&DS(#/s&FKEEJ#O.C%S)s&B/s&HKEEJ#O@s&IKEEJ%#l#*#s&As&;l#+s&Ms&L#l#,s&Ps&O#l#-#0FA51-#Bs'M#:s'7@<;:#$s'6s'wMs'5%G#$Ns'yLs'4*I#&s'<%#m#(#j#'s#+##s#6'#s'B#s#6$s'@#Ms'?%G#$N%Ls'>*I#&s'F%#k#')#j#(D#'s'bs'K=s'`s(29#3s'K#%G#;s'Ms$:R%G#&s'P#Fj#)s'Q#,s'R'<Is'i>s(<s'j's'ks''-$#2s)_1s''#4$s'#-$#,C&0DCS%HS&S*s(Ds'+s'#s'r'#0DCS#HS$S's's($s'/s''s&}?,+('$#8C*.Cs&xS(#/s&zKEEJ#O.C%S)s&v/s&|KEEJ#O@s&}KEEJ%#l#*#s&us&ol#+s'%s'$#l#,s'(s''#l#-#0FA51-#Bs($#:s'k@<;:#$s'js()Ms'i%G#$Ns(+Ls'h*I#&s'p%#m#(#j#'s#+##s#6'#s'v#s#6$s't#Ms's%G#$N%Ls'r*I#&s'z%#k#')#j#(D#'s(9s(#3s+.s*5<Is(i3s+0s*8ES8$#&s(&F#j#)s('#ES8F&&s())#j#)s(*#&s(++Fj#)s(,#,s(--ES8S.,VS^S.s*C:s(00&%$#:s(1S.)#0S_;s(1s$ER%G#:s(44/%#S`$s(3s(MMs(2%G#$Ns(OLs(1*I#&s(9%#m#(#j#'<##s#''#s(?#s#'$s(=#Ms(<%G#$N%Ls(;*I#&s(C%#k#')#j#(D#'s(]s(H$s(Es(^Ms(D%G#$Ns(`Ls(C*I#&s(K%#m#Sa#j#')##4'#s(Q#4$s(O#Ms(N%G#$N%Ls(M*I#&s(U%#k#')#j#(D#'s(ns(Z$s(Ws(oMs(V%G#$Ns(qLs(U*I#&s(]%#m#Sb#j#')##4'#s(c#4$s(a#Ms(`%G#$N%Ls(_*I#&s(g%#k#')#j#(D#'s)#s(l$s(is)$Ms(h%G#$Ns)&Ls(g*I#&s(o%#m#Sc#j#')##4'#s(u#4$s(s#Ms(r%G#$N%Ls(q*I#&s(y%#k#')#j#(D#'s)4s(~=s)2s)e9#3s(~#%G#+s+v2#;s)&#R%G#&s))#Fj#)s)*#,s)+)<Is)=>s)qs)>'s)?s(\-$#2s(X1s(\#4$s(X-$#,C&0DCS%HS&S*s)ys(`s(Xs)F'#0DCS#HS$S's)G($s(ds(\s(V?,+('$#8C*.Cs(QS(#/s(SKEEJ#O.C%S)s(O/s(UKEEJ#O@s(VKEEJ%#l#*#s(Ns(Hl#+s(Zs(Y#l#,s(]s(\#l#-#0FA51-#Bs)T#:s)DB<;:#$s)Cs)YMs)B%G#$Ns)[Ls)A*I#&s)I%#m#(#j#'s#-##s#8'#s)O#s#8$s)M#Ms)L%G#$N%Ls)K*I#&s)S%#k#')#j#(D#'s)is)X=s)gs*?9#3s)X#%G#2s,O;s)[#R%G#&s)^#Fj#)s)_#,s)`(<Is)q>s*Js)r's)ss)5-$#2s*E1s)5#4$s)1-$#,C&0DCS%HS&S*s*Rs)9s)1s)z'#0DCS#HS$S's){($s)=s)5s)/?,+('$#8C*.Cs)*S(#/s),KEEJ#O.C%S)s)(/s).KEEJ#O@s)/KEEJ%#l#*#s)'s(}l#+s)3s)2#l#,s)6s)5#l#-#0FA51-#Bs*,#:s)yA<;:#$s)xs*1Ms)w%G#$Ns*3Ls)v*I#&s)~%#m#(#j#'s#,##s#7'#s*(#s#7$s*&#Ms*%%G#$N%Ls*$*I#&s*,%#k#')#j#(D#'s*As*1=s*?s*t9#3s*1#%G#;s*3s->R%G#&s*6#Fj#)s*7#,s*8'<Is*H>s*~s*I's*Js)i-$#(s*z2#1s)j#4$s)f-$#,C&0DCS%HS&S*s++s)ns)fs*R'#0DCS#HS$S's*S($s)rs)js)d?-,('$#8C*.Cs)_S(#/s)aKEEJ#O.C%S)s)]/s)cKEEJ#O@s)dKEEJ%#l#*#s)\s)Vl#+s)hs)g#l#,s)ks)j#l#-#0FA61-#Bs*`#:s*RA=<;#$s*Qs*eMs*P%G#$Ns*gLs*O*I#&s*W%#m#(#j#'s#,##s#7'#s*]#s#7$s*[#Ms*Z%G#$N%Ls*Y*I#&s*a%#k#')#j#(D#'s*us*f=s*ss+M9#3s*f#%G#;s*hs$;R%G#&s*k#Fj#)s*l#,s*m'<Is*|>s+Ws*}'s*~s*B-$#+s'*2#1s*C#4$s*?-$#,C&0DCS%HS&S*s+`s*Gs*?s+*'#0DCS#HS$S's++($s*Ks*Cs*=?-,('$#8C*.Cs*8S(#/s*:KEEJ#O.C%S)s*6/s*<KEEJ#O@s*=KEEJ%#l#*#s*5s*/l#+s*As*@#l#,s*Ds*C#l#-#0FA61-#Bs+8#:s++A=<;#$s+*s+=Ms+)%G#$Ns+?Ls+(*I#&s+0%#m#(#j#'s#,##s#7'#s+6#s#7$s+4#Ms+3%G#$N%Ls+2*I#&s+:%#k#')#j#(D#'s+Ms+?=s+Ks,&9#3s+?#%G#;s+As$;R%G#&s+D#Fj#)s+E#,s+F'<Is+T>s,0s+U's+Vs*w-$#(s'_2#1s*x#4$s*t-$#,C&0DCS%HS&S*s,9s*|s*ts+^'#0DCS#HS$S's+_($s+$s*xs*r?-,('$#8C*.Cs*mS(#/s*oKEEJ#O.C%S)s*k/s*qKEEJ#O@s*rKEEJ%#l#*#s*js*dl#+s*vs*u#l#,s*ys*x#l#-#0FA61-#Bs+l#:s+`A=<;#$s+_s+qMs+^%G#$Ns+sLs+]*I#&s+e%#m#(#j#'s#,##s#7'#s+k#s#7$s+i#Ms+h%G#$N%Ls+g*I#&s+o%#k#')#j#(D#'s,%s+t=s,#s,[9#3s+t#%G#;s+vs$;R%G#&s+y#Fj#)s+z#,s+{'<Is,,>s,es,-'s,.s+P-$#1s+Os.:4s.;s+K-$#,Cs.=0DCS%HS&S*s,ls+Ss+Ks,4s.>#0DCS#HS$S's,5s.?$s+Ws+Os+I?+*('$#8Cs.A.Cs+DS(#/s+FKEEJ#O.C%S)s+B/s+HKEEJ#O@s+IKEEJ%#l#*#s+As+;l#+s+Ms+L#l#,s+Ps+O#l#-#0FA41-#Bs,B#:s,7?;:9#$s,6s,GMs,5%G#$Ns,ILs,4*I#&s,<%#m#(#j#'s#*##s#5'#s,B#s#5$s,@#Ms,?%G#$N%Ls,>*I#&s,F%#k#')#j#(D#'s,Ws,K=s,Us-29#3s,K#%G#;s,Ms$9R%G#&s,P#Fj#)s,Q#,s,R'<Is,^>s-<s,_'s,`s,'-$#(s.o2#1s,(#4$s,$-$#,C&0DCS%HS&S*s-Es,,s,$s,h'#0DCS#HS$S's,i($s,0s,(s+~?-,('$#8C*.Cs+yS(#/s+{KEEJ#O.C%S)s+w/s+}KEEJ#O@s+~KEEJ%#l#*#s+vs+pl#+s,&s,%#l#,s,)s,(#l#-#0FA61-#Bs,v#:s,lA=<;#$s,ks,{Ms,j%G#$Ns,}Ls,i*I#&s,q%#m#(#j#'s#,##s#7'#s,w#s#7$s,u#Ms,t%G#$N%Ls,s*I#&s,{%#k#')#j#(D#'s-/s-$=s--s-g9#3s-$#%G#;s-&s$9R%G#&s-)#Fj#)s-*#,s-+'<Is-6>s-qs-7's-8s,\-$#1s,[s/64s/7s,W-$#,Cs/90DCS%HS&S*s-xs,_s,Ws->s/:#0DCS#HS$S's-?s/;$s,cs,[s,U?+*('$#8Cs/=.Cs,PS(#/s,RKEEJ#O.C%S)s,N/s,TKEEJ#O@s,UKEEJ%#l#*#s,Ms,Gl#+s,Ys,X#l#,s,\s,[#l#-#0FA41-#Bs-L#:s-C?;:9#$s-Bs-QMs-A%G#$Ns-SLs-@*I#&s-H%#m#(#j#'s#*##s#5'#s-N#s#5$s-L#Ms-K%G#$N%Ls-J*I#&s-R%#k#')#j#(D#'s-as-W=s-_s.>9#3s-W#%G#;s-Ys/pR%G#&s-\#Fj#)s-]#,s-^'<Is-h>s.Hs-i's-js-3-$#(s/k2#1s-4#4$s-0-$#,C&0DCS%HS&S*s.Qs-8s-0s-r'#0DCS#HS$S's-s($s-<s-4s-.?-,('$#8C*.Cs-)S(#/s-+KEEJ#O.C%S)s-'/s--KEEJ#O@s-.KEEJ%#l#*#s-&s,|l#+s-2s-1#l#,s-5s-4#l#-#0FA61-#Bs.$#:s-xA=<;#$s-ws.)Ms-v%G#$Ns.+Ls-u*I#&s-}%#m#(#j#'s#,##s#7'#s.'#s#7$s.%#Ms.$%G#$N%Ls.#*I#&s.+%#k#')#j#(D#'s.9s.0=s.7s.s9#3s.0#%G#;s.2s$9R%G#&s.5#Fj#)s.6#,s.7'<Is.@>s.}s.A's.Bs-h-$#(s0E+#2#1s-j#4$s-f-$#,C&0DCS%HS&S*s/+s-ns-fs.K'#0DCS#HS$S's.L($s-rs-js-d?.-('$#8C*.Cs-_S(#/s-aKEEJ#O.C%S)s-]/s-cKEEJ#O@s-dKEEJ%#l#*#s-\s-Vl#+s-hs-g#l#,s-ks-j#l#-#0FA71-#Bs.Y#:s.RB>=<#$s.Qs.^Ms.P%G#$Ns.`Ls.O*I#&s.W%#m#(#j#'s#-##s#8'#s.]#s#8$s.[#Ms.Z%G#$N%Ls.Y*I#&s.a%#k#')#j#(D#'s.ns.f=s.ls/M9#3s.f#%G#;s.hs0oR%G#&s.k#Fj#)s.l#,s.m'<Is.u>s/Ws.v's.ws.B-$#(s#82#1s.C#4$s.?-$#,C&0DCS%HS&S*s/`s.Gs.?s/#'#0DCS#HS$S's/$($s.Ks.Cs.=?-,('$#8C*.Cs.8S(#/s.:KEEJ#O.C%S)s.6/s.<KEEJ#O@s.=KEEJ%#l#*#s.5s./l#+s.As.@#l#,s.Ds.C#l#-#0FA61-#Bs/1#:s/+A=<;#$s/*s/6Ms/)%G#$Ns/8Ls/(*I#&s/0%#m#(#j#'s#,##s#7'#s/6#s#7$s/4#Ms/3%G#$N%Ls/2*I#&s/:%#k#')#j#(D#'s/Fs/?=s/Ds0&9#3s/?#%G#;s/As$<R%G#&s/D#Fj#)s/E#,s/F'<Is/M>s00s/N's/Os.w-$#+s)(2#1s.x#4$s.t-$#,C&0DCS%HS&S*s09s.|s.ts/W'#0DCS#HS$S's/X($s/$s.xs.r?-,('$#8C*.Cs.mS(#/s.oKEEJ#O.C%S)s.k/s.qKEEJ#O@s.rKEEJ%#l#*#s.js.dl#+s.vs.u#l#,s.ys.x#l#-#0FA61-#Bs/e#:s/`A=<;#$s/_s/jMs/^%G#$Ns/lLs/]*I#&s/e%#m#(#j#'s#,##s#7'#s/k#s#7$s/i#Ms/h%G#$N%Ls/g*I#&s/o%#k#')#j#(D#'s/zs/t=s/xs0[9#3s/t#%G#;s/vs$;R%G#&s/y#Fj#)s/z#,s/{'<Is0%>s0es0&'s0's/P-$#(s)]2#1s/Q#4$s/M-$#,C&0DCS%HS&S*s0ns/Us/Ms0/'#0DCS#HS$S's00($s/Ys/Qs/K?-,('$#8C*.Cs/FS(#/s/HKEEJ#O.C%S)s/D/s/JKEEJ#O@s/KKEEJ%#l#*#s/Cs/=l#+s/Os/N#l#,s/Rs/Q#l#-#0FA61-#Bs0=#:s09A=<;#$s08s0BMs07%G#$Ns0DLs06*I#&s0>%#m#(#j#'s#,##s#7'#s0D#s#7$s0B#Ms0A%G#$N%Ls0@*I#&s0H%#k#')#j#(D#'s0Rs0M=s0Ps149#3s0M#%G#;s0Os$;R%G#&s0R#Fj#)s0S#,s0T'<Is0Y>s1>s0Z's0[s0)-$#2s1m1s0)#4$s0%-$#,C&0DCS%HS&S*s1Fs0-s0%s0b'#0DCS#HS$S's0c($s01s0)s0#?,+('$#8C*.Cs/zS(#/s/|KEEJ#O.C%S)s/x/s/~KEEJ#O@s0#KEEJ%#l#*#s/ws/ql#+s0's0&#l#,s0*s0)#l#-#0FA51-#Bs0p#:s0m@<;:#$s0ls0uMs0k%G#$Ns0wLs0j*I#&s0r%#m#(#j#'s#+##s#6'#s0x#s#6$s0v#Ms0u%G#$N%Ls0t*I#&s0|%#k#')#j#(D#'s1)s1%=s1's1h9#3s1%#%G#;s1's$:R%G#&s1*#Fj#)s1+#,s1,'<Is10>s1rs11's12s0]-$#2s4$1s0]#4$s0Y-$#,C&0DCS%HS&S*s1zs0as0Ys19'#0DCS#HS$S's1:($s0es0]s0W?,+('$#8C*.Cs0RS(#/s0TKEEJ#O.C%S)s0P/s0VKEEJ#O@s0WKEEJ%#l#*#s0Os0Il#+s0[s0Z#l#,s0^s0]#l#-#0FA51-#Bs1G#:s1E@<;:#$s1Ds1LMs1C%G#$Ns1NLs1B*I#&s1J%#m#(#j#'s#+##s#6'#s1P#s#6$s1N#Ms1M%G#$N%Ls1L*I#&s1T%#k#')#j#(D#'s1\s1Y=s1Zs2@9#3s1Y#%G#;s1[s$9R%G#&s1^#Fj#)s1_#,s1`'<Is1c>s2Js1d's1es15-$#2s4s1s15#4$s11-$#,C&0DCS%HS&S*s2Rs19s11s1l'#0DCS#HS$S's1m($s1=s15s1/?,+('$#8C*.Cs1*S(#/s1,KEEJ#O.C%S)s1(/s1.KEEJ#O@s1/KEEJ%#l#*#s1's0}l#+s13s12#l#,s16s15#l#-#0FA51-#Bs1z#:s1y@<;:#$s1xs2#Ms1w%G#$Ns2%Ls1v*I#&s1~%#m#(#j#'s#+##s#6'#s2(#s#6$s2&#Ms2%%G#$N%Ls2$*I#&s2,%#k#')#j#(D#'s23s21=s1`s2t9#3s21#%G#;s23s$9R%G#&s26#Fj#)s27#,s28'<Is1i>s2~s1j's1ks1i-$#(s5L2#1s1j#4$s1f-$#,C&0DCS%HS&S*s3+s1ns1fs1s'#0DCS#HS$S's1t($s1rs1js1d?-,('$#8C*.Cs1_S(#/s1aKEEJ#O.C%S)s1]/s1cKEEJ#O@s1dKEEJ%#l#*#s1\s1Vl#+s1hs1g#l#,s1ks1j#l#-#0FA61-#Bs2%#:s2RA=<;#$s2Qs2WMs2P%G#$Ns2YLs2O*I#&s2W%#m#(#j#'s#,##s#7'#s2]#s#7$s2[#Ms2Z%G#$N%Ls2Y*I#&s2a%#k#')#j#(D#'s2gs2f=s28s3M9#3s2f#%G#;s2hs$:R%G#&s2k#Fj#)s2l#,s2m'<Is2A>s3Ws2B's2Cs2B-$#+s2>2#1s2C#4$s2?-$#,C&0DCS%HS&S*s3`s2Gs2?s2K'#0DCS#HS$S's2L($s2Ks2Cs2=?-,('$#8C*.Cs28S(#/s2:KEEJ#O.C%S)s26/s2<KEEJ#O@s2=KEEJ%#l#*#s25s2/l#+s2As2@#l#,s2Ds2C#l#-#0FA61-#Bs2Y#:s3+A=<;#$s3*s3/Ms3)%G#$Ns31Ls3(*I#&s30%#m#(#j#'s#,##s#7'#s36#s#7'#s38)s5Rs2o)#s2p)#s2q)#s2r)#s2s)#s2t)#s2u)#s2v)#s2w)#s2x)#s2y)#s2z)#s2{)#s2|)#s2})#s2~)#s3#)#s3$)#s3%)#s3&)#s3')#s3()#s3))#s3*)#s3+)#s3,)#s3-)#s3.)#s3/)#s30)#s31)#s324#s$P)Fs34j#.C#U#s5uU$#U%#U&#U'#U(#U)#U*#U+#U,#U-#U.#U/#U0#U1#U2#U3#U4#U5#U6#U7#U8#U9#U:#U;#U<#U=#U>#U?#U@#UA#UB#,Cs695DDCCPHHs#$QS,s6:#5DDCCPHHs#%Qs3es#$#5DDCCPHHs#&Qs2vs#$#5DDCCPHHs#'Qs2es#$#5DDCCPHHs#(Qs22s#$#5DDCCPHHs#)Qs1[s#$#5DDCCPHHs#*Qs1's#$#5DDCCPHHs#+Qs0Ps#$#5DDCCPHHs#,Qs/xs#$#5DDCCPHHs#-Qs/Es#$#5DDCCPHHs#.Qs.ns#$#5DDCCPHHs#/Qs.Js#$#5DDCCPHHs#0Qs.9s#$#5DDCCPHHs#1Qs.(s#$#5DDCCPHHs#2Qs-ss#$#5DDCCPHHs#3Qs->s#$#5DDCCPHHs#4Qs,fs#$#5DDCCPHHs#5Qs,2s#$#5DDCCPHHs#6Qs+Zs#$#5DDCCPHHs#7Qs+&s#$#5DDCCPHHs#8Qs*Ps#$#5DDCCPHHs#9Qs)xs#$#5DDCCPHHs#:Qs)Fs#$#5DDCCPHHs#;Qs(ns#$#5DDCCPHHs#<Qs(9s#$#5DDCCPHHs#=Qs'as#$#5DDCCPHHs#>Qs'-s#$#5DDCCPHHs#?Qs&Us#$#5DDCCPHHs#@Qs%~s#$#5DDCCPHHs#AQs%Ks#$#5DDCCPHHs#BQs$ts#$#5DDCCPHHs#CQs$@s#$#0DCS#HS$S's#hs#$#s4As%8s%4XSds#hs#G#FUSeS/9S/1S+#VSDs7Os7N1S+s7P1S+s7P1S+s7Pk##$#k##&#VSDs6ls7T1S+s6lk##(#k##s4i#VSfs6bs4o4S+s6c1S+s4q4S+s4qk##$#k##&#1S+s6hWSgs6is4vS,j##SE#j#/%#1S+s4xk##SE#k#/(#VShCS,XSFCs3wS,#XSFCs3xS,#8CS+VSiCs7T.C$S(#/s3zKEEJ#OUS>E8Cs4?6C'#6C#$6C#%6C#&6C#'6C#(6C#)6C#*6C#+6C#,6C#-6C#.6C#/6C#06C#16C#26C#36C#46C#56C#66C#76C#86C#96C#:6C#;6C#<6C#=6C#>6C#?6C#@6C#A6C#B.C#S)s%u/s4BKEEJ#OZSjs4CKEEJS3\SGs4DKEEJ$s#'#\SGs4EKEEJs#)s#(#l#*#s4=s47l#+s#/s4H#l#,s4Ls4K#j#0C#j#1SH#1S+F)S,s4k)#s4l)#s4m)#s4n)#s4o)#s4p)#s4q)#s4r)#s4s)#s4t)#s4u)#s4v)#s4w)#s4x)#s4y)#s4z)#s4{)#s4|)#s4})#s4~)#s5#)#s5$)#s5%)#s5&)#s5')#s5()#s5))#s5*)#s5+)#s5,)#s5-)#s5.4#s&Lk###S3k##s#%#k#0C#k#1SH##S9##############################################################$s5v#Ms5u%G#$N%Ls5t*I#&s5|%#9S9XF$#SISJl#-s#Ps#*#l#2s$+s$(#l#3s$5s$0#l#4s$:s$7#l#5s$As$<#l#6s$Es$C#l#7s$Gs%0#j#'s%T#j#&D#U#Fj#(D#7s&)s%Z#Fj#(D#U#Fj#(D#7s&bs&7#Fj#(D#U#Fj#(D#7s'>s&p#Fj#(D#U#Fj#(D#7s'vs'L#Fj#(D#U#Fj#(D#7s(Rs((#Fj#(D#U#Fj#(D#7s)/s(`#Fj#(D#U#Fj#(D#7s)hs)=#Fj#(D#U#Fj#(D#7s*Es)v#Fj#(D#U#Fj#(D#7s+#s*S#Fj#(D#U#Fj#(D#7s+\s+1#Fj#(D#U#Fj#(D#7s,7s+j#Fj#(D#U#Fj#(D#7s,ps,E#Fj#(D#U#Fj#(D#7s-Ks,~#Fj#(D#U#Fj#(D#7s.(s-Y#Fj#(D#U#Fj#(D#7s.as.6#Fj#(D#U#Fj#(D#7s/>s.o#Fj#(D#U#Fj#(D#7s/ws/L#Fj#(D#U#Fj#(D#7s0Us0)#Fj#(D#U#Fj#(D#7s0ks0c#Fj#(D#U#Fj#(D#7s1%s0y#Fj#(D#U#Fj#(D#7s1;s13#Fj#(D#U#Fj#(D#7s1ds1I#Fj#(D#U#Fj#(D#7s2@s1r#Fj#(D#U#Fj#(D#7s2xs2N#Fj#(D#U#Fj#(D#7s3Us3*#Fj#(D#U#Fj#(D#7s41s3c#Fj#(D#U#Fj#(D#7s4js4?#Fj#(D#U#Fj#(D#7s5Fs4x#Fj#(D#U#Fj#(D#7s5~s5T#Fj#(D#U#Fj#(D#7s68s60#Fj#(D#U#Fj#(D#7s7,s6F#Fj#(D#U#Fj#(D#7s7Cs7:#S,U#Fj#'s7Q#j#&D#XSkILG#l#8s7ps7m#j#9s7r#j#:s7x#j#;s7~#j#<s8Q#j#=s9Z#j#>s9d#j#?s9w#j#@s9y#j#As9{#j#Bs9}#j#Cs:%#j#Ds:V#j#Es:h#a#SlSmSnSoS9SpSJSISqS3S/S,Fj#Fs8$#j#Gs8*#j#Hs80#j#Is8_#j#Js9h#j#Ks9r#j#Ls:)#j#Ms:+#j#Ns:-#j#Os:/#j#Ps:3#j#Qs:d#j#Rs:v#[SrS-S1S.S0s;&#Fl#SSss;)##"). Qed.

  Lemma sn_know_ok : know_ok RSEGS E mem sn_kn.
  Proof.
    destruct SH. pose proof (u64_range sp) as Hsp. pose proof (u64_range bufb) as Hb.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold sn_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev1. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev1. lia.
    - apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1360); [apply ev0 | exact Sstk0 | unfold SN_FR; lia].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1.
      split; [lia|]. intros d m Hd Hm. replace (bv_unsigned bufb + 2 + d) with (bv_unsigned bufb + 2 + d) by lia.
      first [ apply Sbuf0; lia | replace (bv_unsigned bufb + 2 + d)%Z with (bv_unsigned bufb + 2 + d)%Z by lia; apply (Sbuf0 d m); lia
            | match goal with |- store_ok _ _ (Z_to_bv 64 ?x) _ = true => replace x with (bv_unsigned bufb + 2 + d) by lia; apply Sbuf0; lia end ].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite ev0, ev1. unfold SN_FR in Sdisj0. lia.
    - apply kimg_intro; [lia | lia | exact Simg0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Sgot0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Scan0].
  Qed.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sn_run := sym_exec RSEGS 3000 true [SN_RET] (SCR [] [] []) (SS SN_ENTRY sn_sr [] sn_kn 35) [].
Definition sn_res := Eval vm_compute in sn_run.
Definition sn_car := Eval vm_compute in (carry (s_log (fst (fst sn_res))) sn_kn []).

(* [comment removed for export] *)
Definition sn_regions : list sregion := [(SA (EVar 0) (-1360), 1360); (SA (EVar 1) 2, 3)].

(* [comment removed for export] *)
Lemma sn_res_pc : s_pc (fst (fst sn_res)) = SN_RET. Proof. vm_compute. reflexivity. Qed.
Lemma sn_res_scs : snd (fst sn_res) = []. Proof. vm_compute. reflexivity. Qed.
Lemma sn_car_scs : snd (fst sn_car) = [] /\ snd sn_car = []. Proof. vm_compute. split; reflexivity. Qed.
Lemma sn_covered : log_covered sn_regions (s_log (fst (fst sn_res))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_same : same_regs sn_sr (s_regs (fst (fst sn_res))) callee_saved = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  (* [comment removed for export] *)
  Variable rsh : bvmap 5 word -> Prop.
  Hypothesis rsh_upd : forall (R : bvmap 5 word) (rd : reg) (v : word), bv_eqb rd 0 = false -> rsh R -> rsh (regupd R rd v).
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp bufb : word) (can : Z).
  Hypothesis SH : snH mem sp bufb can.
  Hypothesis RSH : rsh regs.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 (bv_unsigned bufb + 2).
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 22.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 SN_FMT.
  Hypothesis R13 : getr regs 13 = Z_to_bv 64 18446744073709551615.

  Let E := snE regs sp bufb can.

  Lemma sn_adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (bv_unsigned bufb + k).
  Proof. intros k. unfold adenot. cbn [a_base a_off edenot]. change (ev E 1) with bufb. unfold v_addi. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma sn_byte : forall log kn' k v,
    know_ok RSEGS E (mem_denot E mem log) kn' ->
    kread RSEGS kn' (EVar 1) k 1 = Some (ELit v) -> 0 <= k -> bv_unsigned bufb + k + 1 <= 2 ^ 64 ->
    rdn RSEGS (mem_denot E mem log) (Z_to_bv 64 (bv_unsigned bufb + k)) 1
    = Some (word_to_le_bytes 1 (Z_to_bv 64 v)).
  Proof.
    intros log kn' k v HK Hr Hk Hnw. pose proof (u64_range bufb).
    pose proof (kread_rdn RSEGS E _ kn' (EVar 1) k 1 _ HK Hr ltac:(lia) ltac:(lia)) as B.
    rewrite sn_adenot_var1 in B. cbn [edenot] in B. apply B.
    unfold flat, estart. cbn [a_base a_off edenot]. change (ev E 1) with bufb. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_3 : forall segs m (a : Z) b0 b1 b2,
    0 <= a -> a + 3 <= 2 ^ 64 ->
    rdn segs m (Z_to_bv 64 a) 1 = Some [b0] -> rdn segs m (Z_to_bv 64 (a + 1)) 1 = Some [b1] ->
    rdn segs m (Z_to_bv 64 (a + 2)) 1 = Some [b2] ->
    rdn segs m (Z_to_bv 64 a) 3 = Some [b0; b1; b2].
  Proof.
    intros segs m a b0 b1 b2 Ha Hnw H0 H1 H2.
    change 3%nat with (1 + (1 + 1))%nat. change [b0; b1; b2] with ([b0] ++ ([b1] ++ [b2])).
    apply rdn_app; [exact H0|].
    replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned. unfold nat_to_word. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite <- Zplus_mod. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
    apply rdn_app; [exact H1|].
    replace (Z_to_bv 64 (a + 1) + nat_to_word 1)%bv with (Z_to_bv 64 (a + 2)); [exact H2|].
    apply bv_eq. rewrite bv_add_unsigned. unfold nat_to_word. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- Zplus_mod. f_equal. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Definition sn_post (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
      msteps RSEGS (mkst regs (Z_to_bv 64 SN_ENTRY) mem rom) (mkst regs' (Z_to_bv 64 SN_RET) mem' rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 2
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1360), 1360); (Z_to_bv 64 (bv_unsigned bufb + 2), 3)]
      /\ rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned bufb + 2)) 3 = Some [Z_to_bv 8 45; Z_to_bv 8 49; Z_to_bv 8 0]
      /\ rsh regs'.

  (* [comment removed for export] *)
  Lemma sn_pack : forall ss' scr' kn' hs',
    sym_exec RSEGS 3000 true [SN_RET] (SCR [] [] []) (SS SN_ENTRY sn_sr [] sn_kn 35) [] = (ss', [], scr') ->
    s_pc ss' = SN_RET ->
    log_covered sn_regions (s_log ss') = true ->
    same_regs sn_sr (s_regs ss') callee_saved = true ->
    nth 10 (s_regs ss') (ELit 0)
      = EAlu ALU_ADD (EAluw ALU_ADD (EAlu ALU_SLTU (ELit 0) (EAlu ALU_ADD (EVar 0) (ELit (-736)))) (ELit (-1))) (ELit 2) ->
    carry (s_log ss') sn_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (EVar 1) 2 1 = Some (ELit 45) ->
    kread RSEGS kn' (EVar 1) 3 1 = Some (ELit 49) ->
    kread RSEGS kn' (EVar 1) 4 1 = Some (ELit 0) ->
    exists regs' mem', sn_post regs' mem'.
  Proof.
    intros ss' scr' kn' hs' Hrun Hpc Hcov Hsame H10 Hcarry K0 K1 K2.
    pose proof (sn_regs_ok regs mem sp bufb can SH R2 R10 R11 R12 R13) as HR.
    pose proof (sn_know_ok regs mem sp bufb can SH) as HK.
    fold E in HR, HK.
    destruct (run_sound RSEGS rsh rsh_upd 3000 [SN_RET] (SCR [] [] []) SN_ENTRY sn_sr sn_kn 35 ss' [] scr' E mem rom regs
                Hrun HR HK ltac:(constructor) RSH) as (R' & HR' & Hlf & Hms & HSH').
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct SH. pose proof (u64_range sp) as Hsp. pose proof (u64_range bufb) as Hb.
    exists R', (mem_denot E mem (s_log ss')). unfold sn_post.
    split; [exact Hms|]. split; [|split; [|split; [|split; [|exact HSH']]]].
    - (* [comment removed for export] *) eapply (keeps_cs_of_same E); [exact Hsame | exact HR | exact HR'].
    - (* [comment removed for export] *)
      rewrite (reg_val E _ _ 10 HR').
      replace (sr_get (s_regs ss') 10) with (nth 10 (s_regs ss') (ELit 0)) by reflexivity.
      rewrite H10. cbn [edenot]. change (ev E 0) with sp.
      rewrite (alu_add_wZ sp (-736)).
      rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_small by lia.
      destruct (Z.ltb_spec 0 (bv_unsigned sp + -736)); [|lia].
      apply bv_eq. vm_compute. reflexivity.
    - (* [comment removed for export] *)
      replace [(Z_to_bv 64 (bv_unsigned sp - 1360), 1360); (Z_to_bv 64 (bv_unsigned bufb + 2), 3)]
        with (map (rdenot E) sn_regions).
      2:{ unfold sn_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. change (ev E 1) with bufb. repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold sn_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd a_base a_off edenot]; [change (ev E 0) with sp | change (ev E 1) with bufb]; lia.
    - (* [comment removed for export] *)
      apply rdn_3; [lia | lia | | |].
      + exact (sn_byte _ kn' 2 45 HK' K0 ltac:(lia) ltac:(lia)).
      + replace (bv_unsigned bufb + 2 + 1) with (bv_unsigned bufb + 3) by lia. exact (sn_byte _ kn' 3 49 HK' K1 ltac:(lia) ltac:(lia)).
      + replace (bv_unsigned bufb + 2 + 2) with (bv_unsigned bufb + 4) by lia. exact (sn_byte _ kn' 4 0 HK' K2 ltac:(lia) ltac:(lia)).
  Qed.

  Lemma sn_case : exists regs' mem', sn_post regs' mem'.
  Proof.
    ltac2:(KReplay.runc [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.Package.sn_pack); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.sym_state); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.sidecond); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_res); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.kentry); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_car); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.SS); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.EVar); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.EAluw); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLTU); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.sentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.SE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KImg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.SCR); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.sym_exec); constr:(@OSSVerify.boost_beast.http_request.images.Plain.M.loaded_segments); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.SN_RET); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.SN_ENTRY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_sr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_kn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.s_pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymPackX.log_covered); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XL_snprintfA.sn_regions); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.s_log); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymPackX.same_regs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.s_regs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefMemcpyLib.callee_saved); constr:(@Corelib.Lists.ListDef.nth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.carry); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymPackX.kread)|] Array.empty "#Wm###b#F#/#:#A#,#0#(#8#T#R#S#*#-#.#1#?#I#J#K#4#U#W#X#<#C#B#L#M#O#V#Q#Y#\#Z#[#^#]#_#`#a#b#&#>#6#9#7#G#H#D#N#;#5#=#@#P#3#2#E#+#'#)#c#d8#M$#N$#O&#P$#Q&#R%#S$#T&#U$#V$#W$#X&#Y&#Z'#[%#\$#]%#^&#_$#`%#a(5N3I#4#GO4I%#WP%GO5D3#(5H4$#Q4&+#WP&%Q3,G&J$#&#$#&#&#$#$#$#&#$#$#&#&#$#&#$#$#,#+S*#R######-#-R#%##-##$-##$##-##$-##$-##$-#$J&#&#&#$#$#$#$#$#)#+#.F<#.S+s###)J+#WS,F%#,2+#.F%#-s#(-s#*$7,#+#.F&#$9&#,#+#$s#F$#&#,#+##s#&################-##$-##$-##$-##$-##$-##$-##$-##$-##$-##$-##$-##$-##$-#2E%E$#%E'#%E*#%E-#%E0#%E3#%E6#%E9#%E<#%E?#%EB#%Es#%#%Es#(#%Es#+#%Es#6#%Es#@#%Es#8#%Es#>#%Es#C#%Es#I#%Es#J#%Es#L#%Es#`#%Es#c#%Es#f#%Es#i#%Es#x#%Es#n#%Es#q#%Es#u#%Es#w#%Es#}#$s#K$#$#$#)#(s#}#'#s$$s$(&s#[$#$#$#$#$#)#(s$*#'#s$%s$1&*$#$#$#)#(s$1#$s#j$#$#$#&#)#+#.Fs$9#'+s$4#$s$+$#&#$#$#$#)#(s$B#'#s$=s$I&+&#$#$#$#)#(s$J#'#s$Es$Q$s$$$#$#$#)#(s$Q#'#s$Ls$X'3s$Ms$9',s$Ns$:(s$2s$0'#s$[s$\)s#2(s$X#&s#8,#+#'&s$V#$&$#$#)#(s$a#'#s$\s$;,s$|(s$A#'#s$js$5(s$Cs$G'#s$ls$<&s$<$#&#$#$#$#)#(s$o#'#s$js$v$*$#$#$#)#(s$v#'#s$qs#@&s$J$#$#$#)#(s$}#,J+#'%s$z#$s$S$#$#$#)#(s%*#&s#d$#&#$#$#$#&#$#&#&#$#$#$#$#,#$J&#&#$#$#&#$#$#&#&#$#&#$#$#&#$#$#$#$#,#&J$#&#$#&#&#$#$#&#&#&#$#$#$#&#$#$#$#,#$s#)&#&#$#$#&#$#&#$#$#$#&#$#&#&#,#&@&#&#&#$#&#&#&#&#$#$#$#,#$-$#&#$#&#$#$#$#$#,#$s#)$#$#&#&#$#&#$#$#$#$#$#$#$#,#$s#,&#,#&s#H$#&#$#&#$#&#&#$#$#$#,#$s#Q&#&#$#&#$#$#$#,#$s#[&#&#$#$#&#$#$#$#,#&s#k&#&#&#&#$#&#$#$#&#&#&#$#$#$#,#&+&#$#$#&#$#$#,#$s$%&#&#&#&#$#&#&#&#&#$#$#$#,#$s#W$#$#$#$#$#$#$#$#$#$#,#&s$C&#$#&#$#$#$#$#$#$#$#$#$#$#$#$#$#,#&3&#&#&#$#$#$#$#$#$#$#&#$#$#$#,#&s#:$#$#&#$#$#$#$#,#+s$o's%7s'Y#&s&F$#$#$#)#(s'e#'#s'`s'F$s&J)#(s'i#+s&L.Fs'k#'%s'f#&s'[&#$#$#$#)#(s's#&s(+$#&#$#$#&#$#&#&#$#$#,#+s$~'0s'{#&s'Y&#&#$#)#+#.Fs(,#'s&As('#&()#(s(0#'#s(6s']$s&L$#&#$#$#$#)#(s(9#&s&;$#$#$#$#&#$#&#&#$#&#,#+s%4'0s(A#$7$#$#$#)#(s(M#'#s(Hs#A&s&p&#$#$#$#)#(s(U#'#s(Ps(\$*$#$#$#)#(s(\#'#s(Ws(c&s&~$#$#$#)#(s(c#&s(}&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#,#+#'Bs(}#$s'F$#)#(s)+#,s'^+#'%s)(#$s'Q&#&#$#$#$#)#(s)6#&s)N$#$#$#$#$#&#$#$#$#&#&#&#$#$#,#+s&('4s)B#+s#x.Fs)J#'s'_s)E#(s)Ls)4'#s)Rs(~&s)b&#&#&#&#&#&#&#$#&#$#$#,#+s&2's#(s)V#$s#0&#$#$#$#)#(s)c#'#s)^s)j&s'j&#$#$#$#$#)#(s)l#'#s)gs)M$3$#$#$#)#(s)s#'#s)ns'S&s(E&#$#$#$#$#&#)#(s)}#'#s*'s)N$s#Q$#$#$#)#(s*(#&s(S$#&#&#$#$#&#$#&#&#$#,#+s&Y'0s*0#$s(f$#)#(s*:#'#s*5s'v&s#4$#$#$#)#(s*A#'#s*<s'}&s#}&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#,#+#'s#.s*`#$s%X$#$#$#)#(s*l#)s);+#.Fs*o#'&s*j#$s%2&#&#,#+s':'s%?s*p#'s$ys*qs$S&s%b$#&#&#&#&#&#&#$#$#,#+s'<'s$Ps*~#$s#~&#$#$#$#)#(s+/#$s#I$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#&#,#+#'s##s+J#$s#*$#$#$#)#(s+V#$s#c&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#,#+#'6s+d#&s*@$#$#$#)#(s+p#&s)g$#$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#$#&#&#$#$#,#+#'<s,(#$s*.$#$#)#(s,3#&s*c$#$#$#&#$#$#&#,#+#'-s,8#)s%a(s,@#'#s,;s+{&s*t$#$#$#$#)#(s,H#'#s,Cs'I&*$#$#$#)#(s,O#'#s,Js,V&s*Q$#$#$#)#(s,V#+s$J.Fs,X#'%s,S#&s&~$#$#$#)#(s,_#)s&:+#.Fs,b#'&s,]#)s'((s,e#$s&_&#$#$#$#)#+#.Fs,m#'+s,h#)s-$(s,p#'#s,ks,%$s-+$#$#$#)#(s,w#'#s,rs,.$s-3&#$#$#$#)#(s-##'#s,zs,8$*$#$#$#)#(s-*#'#s-%s,A&s#u$#$#$#)#(s-1#'#s-,s,J$s#z$#)#(s-6#'#s-1s,Q's(1s-2s$}$s'{$#&#&#$#$#,#+s)L's(,s-;#'s+Os-<s#>)s--(s-D#'#s-?s-K)s%;(s-G#'#s-Bs-N$s'A$#$#)#(s-M#'#s-Ps%G,s&P+#'s,)s-K#'s,#s-Ls-8's+Bs-Ms,o's+<s-Ns,r.Fs-2s-5's+7s-P#$s(@$#&#&#$#&#&#$#$#,#+s)c's(Ms-\#)s'6+#.Fs-e#'s%Xs-`#$s'a&#$#$#$#$#)#(s-n#'#s-is-u&*$#$#$#)#(s-u#'#s-ps-|$s#o$#$#$#)#(s-|#'#s-ws.'(s-~s#q'#s-ys.)$;&#$#$#$#)#(s.*#'#s.%s.1&s-u$#$#$#)#(s.1#'#s.,s#+$1$#$#$#)#(s.8#'#s.3s-s&s'a$#$#$#)#(s.?#'#s.:s-\)s'd(s.B#'#s.=s-a)s$.(s.E#'#s.@s#O)s#~(s.H#'#s.Cs)I)s#u(s.K#'#s.Fs&5)s,8(s.N#'#s.Is#H)s,+(s.Q#&:&#&#&#$#&#&#$#&#&#&#$#$#,#+s*R'2s.[#'s,Zs.gs.h)s#V(s.d#+s,c.Fs.f#'%s.a#)s#M(s.i#'#s.ls&c)s$`(s.l#'#s.os&f)s%z(s.o#&=$#$#$#$#&#$#$#$#,#+s*d'.s.u#)s-0(s.}#'#s.xs/()s.j(s/$#'#s.{s/+)s-f(s/'#'#s.~s/.)s,q(s/*#'#s/%s/1)s$d(s/-#'#s/(s/4)s(S(s/0#'#s/+s/7)s#[(s/3#'#s/.s/:'s#/s//s/;'s#+s/0s/<'s$Hs/1s/=$s-a$#)#(s/;#'#s/6s/B&s-h$#$#$#)#(s/B#'#s/=s/I$s(-$#$#$#)#(s/I#'#s/Ds/P)s(0(s/L#'#s/Gs/S's-{s/Hs/T)s%~(s/P#'#s/Ks/W's#As/Ls/X)s(B(s/T#'#s/Os/[)s)k(s/W#'#s/Rs/^$s/0$#$#)#(s/]#'#s/Xs/d)s)u(s/`#'#s/cs/g)s-y(s/c#'#s/fs/j's#Fs/gs/k).(s/g#'#s/js/n'.s/ks/o$s*F$#)#(s/m#'#s/ps/t's%-s/qs/u)s$D(s/q#'#s/ts/x)s(c(s/t#'#s/ws/{)s.9(s/w#'#s/zs/~'s%4s/{s0#)s*h(s/{#'#s/~s0&)s'.(s/~#'#s0%s0)'$s0)s0*&s*p)#(s0'#'#s0-s0.)s*L(s0*#'#s00s01)s&0(s0-#'#s03s04&s*{$#)#(s02#'#s08s09&')#(s06#'#s0<s0=)s&E(s09#'#s0?s0@'s.xs0@s0A,s.V+#'s.Ds08#'s.<s09s%H)s#f(s0A#'#s0<s/|)s%)(s0D#'#s0?s/e)s$p(s0G#'#s0Bs/j)s&&(s0J#'#s0Es0=)s/1(s0M#'#s0Hs+N)s.`(s0P#$s0_&#&#&#$#$#,#+s,4'+s0S#)s)[(s0[#'#s0Vs%U)s/9(s0^#'#s0Ys0=)s//(s0a#-s0+'$s0]#)s07(s0e#-s00'$s0a#(s0hs(Y-s04'$s0d#(s0ks%f'#s0fs(e)s/=(s0n#-s07'$s0j#)s/>(s0r#'#s0ms0g)s%C(s0u#'#s0ps0w2C%C$#%C(#%C,#%C1#%C4#%C8#%C=#%CB#%Cs#&#%Cs#*#%Cs#6#%Cs#:#%Cs#>#%Cs#B#%Cs#F#%Cs#J#%Cs#L#%Cs#P#%Cs#R#%Cs#V#%Cs#[#%Cs#a#%Cs#e#%Cs#i#%Cs#n#%Cs/q#%Cs#q#%Cs#u#%Cs#y#%Cs#{#%Cs$##%Cs$'#%Cs$+#%Cs$-#%Cs$3#%Cs$5#%Cs$9#%Cs$;#%Cs$?#%Cs$C#%Cs/P#%Cs/X#%Cs$L#%Cs/b#%Cs$Q#%Cs$U#%Cs$W#%Cs$[#%Cs0##%Cs$^#%Cs$b#%Cs$j#%Cs$r#%Cs$x#%Cs$z#%Cs$|#%Cs$~#%Cs%&#%Cs%*#%Cs%.#%Cs%2#%Cs%6#%Cs%:#%Cs%>#%Cs0$#%Cs%N#%Cs%R#%Cs%V#%Cs%\#%Cs%^#%Cs%q#%Cs%u#%Cs%y#%Cs%}#%Cs&%#%Cs&)#%Cs&1#%Cs&9#%Cs&A#%Cs&J#%Cs&M#%Cs&U#%Cs&]#%Cs&g#%Cs&l#%Cs,c#%Cs'<#%Cs,r#%Cs&|#%Cs'##%Cs'%#%Cs'B#%Cs'H#%Cs'P#%Cs'X#%Cs'a#%Cs'i#%Cs'm#%Cs'y#%Cs((#%Cs(2#%Cs(:#%Cs(C#%Cs(G#%Cs(X#%Cs(y#%Cs)8#%Cs0g#%Cs08#%Cs0@#%Cs0I#%Cs';#%Cs'=#%Cs'A#%Cs0=#%Cs'I#%Cs'M#%Cs'Q#%Cs0@#%Cs'T#%Cs-*#%Cs'_#%Cs-9#%Cs/u#%Cs0##%Cs0+#%Cs'e#%Cs'k#%Cs's#%Cs'{#%Cs((#%Cs(0#%Cs(4#%Cs(@#%Cs(K#%Cs(U#%Cs(]#%Cs(f#%Cs(j#%Cs({#%Cs)@#%Cs)[#%Cs*(#%Cs,##%Cs,+#%Cs*8#%Cs,Z#%Cs,c#%Cs*<#%Cs0_#%Cs*D#%Cs*O#%Cs*t#%Cs*|#%Cs+&#%Cs+;#%Cs+F#%Cs+N#%Cs+X#%Cs+a#%Cs,4#%Cs,<#%Cs,c#%Cs,k#%Cs,t#%Cs,|#%Cs+w#%Cs+z#%Cs+~#%Cs,=#%Cs,E#%Cs,l#%Cs,t#%Cs,}#%Cs-)#%Cs-@#%Cs-E#%Cs-N#%Cs-d#%Cs-k#%Cs-s#%Cs0S#%Cs0]#%Cs0e#%Cs0o#%Cs0r#%Cs0v#%Cs0}#%Cs1(#%Cs1+#%Cs1-#%Cs1/#%Cs17#%Cs1@#%Cs1J#%Cs1Z#%Cs1d#,s1TVS#s3*#$s&P$#$#$#$#$#$#$#$#$#$#$#$#,#,s+EWS$s3:$#VS#s2t4WS$s2u&%&s-i$#$#$#$#)#(s3C#,%VS%$#,s2zVS%s1?#XS-'&s1@$,9$s)>$#$#$#$#$#$#$#$#$#,#VS.s/%s.o$s-K$#&#&#$#&#$#&#$#$#$#,#(s3hs.l*#s3]s.c(s3js0u*#s3_s3C2D%D$#%D'#%D6#%Ds#$#%Ds#&#%Ds#)#%Ds#3#%Ds#5#%Ds#7#%Ds#H##s2zYS&s.ss2Ys#L$#2N0Is4=$#2HWS/#s2}#0s4?G%#1s46##*########################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################2K%KS'#YS&S0S(sEwS)sB}[S1L&M$sBy#sB|0IsT[sTXsB}0sT[G#sTX/sTR%#m$sB{#1KsO;US2sT]/K#S'm$%#1HMUS3sTaVS4S5#/H#Mm$&#US6sTeWS7S(#S8/H#Mm$*#1EsT&XS9EsT?'sTN/E#sT(m$%#3sTjsTi*sS-sTNsTR*sS%sTGsTS*sR{sTHsRs*sRksTIsTU*sRdsTJsTV*sR^sTKsTW*sR[sTWsTX*sRYsTMsRV*sRQsTNsT-*sROsTZsT%*sRNsT[sT+*sRFsTQsT]*sR@sTRsR}*sR:sTSsR8*sR2sTTsOZ*sOTsTUsT;*sOQsTVsOO*sOHsTWsO;*sO0sTcsT.*sO(sTYsNw*sNqsTZsOS*sNjsT[sTg*sNdsT\sTh*sN^sT]sN?*sN;sT^sN9*sN1sT_sM|*sMxsTksT;*sMbsTasTm*sMZsTbsTH*sMTsTcsRH*sMKsTosT:*sMEsTesM8*sM4sTfsRK*sM.sTgsRL*sL`sThsL]*sLBsTisK~*sKxsTjsKe*sK_sTksKF*sKAsTlsK7*sK5sTmsTQ*sK.sTnsOt*sK(sTosT{*sJ~sTpsJ|*sJvsTqsJs*sJqsTrsJi*sJgsTssT-*sJasTtsT0*sJZsTusT3*sJTsTvsT6*sJNsTwsT9*sJJsTxsT<*sJ=sTysU)*sJ;sTzsU**sJ6sU'sLz*sIrsT|sU,*sIlsT}sU-*sIfsT~sU.*sIesU#sU/*sI^sU$sU0*sIXsU%sJ$*sIRsU&sTf*sILsU'sTI*sIJsU(sTL*sIHsU)sJ8*sIFsU*sP0*sIDsU+sLv*sIBsU,sJ+*sI@sU-sI1*sI.sU.sI,*sI*sU7sM.*sI(sU8sM/*sI&sU1sHw*sHusU2sU>*sHssU3sU?*sHqsU4sU@*sHosU5sUA*sHmsU6sUB*sHksU7sUC*sHisU8sUD*sHbsU9sUE*sH\sU:sUF*sHVsU;sUG*sHTsU<sUH*sHQsU=sUI*sHNsU>sUJ*sHLsU?sUK*sHGsU@sUL*sHEsUIsUM*sH2sUJsUN*sH0sUKsUO*sH-sULsUP*sH+sUMsUQ*sGisUFsU**sGgsUGsTm*sGesUHsTp*sGcsUIsUA*sGasUJsPP*sG_sUKsGW*sGUsULsJK*sGSsUMsU1*sGQsUNsGP*sGNsUOsGM*sGLsUPsGK*sGJsUQsMP*sGHsURsGG*sGEsUSsUM*sGCsUTsU[%D#sDI%D%#%D'#%D)#%D+#%D-#%D/#%D1#%D3#%D5#%D7#%D9#%D;#%D=#%D?#%DA#%Ds###%Ds#%#%Ds#'#%Ds#)#%Ds#+#%Ds#-#%Ds#/#%Ds#1#%Ds#3#%Ds#5#%Ds#7#%Ds#9#%Ds#;#%Ds#=#%Ds#?#%Ds#A#%Ds#C#%Ds#E#%Ds#G#%Ds#I#%Ds#K#%Ds#M#%Ds#O#%Ds#Q#%Ds#S#%Ds#U#%Ds#W#%Ds#Y#%Ds#[#%Ds#]#%Ds#_#%Ds#a#%Ds#c#%Ds#e#%Ds#g#%Ds#i#%Ds#k#%Ds#m#%Ds#o#%Ds#q#%Ds#s#%Ds#u#%Ds#w#%Ds#y#%Ds#{#%Ds#}#%Ds$##%Ds$%#%Ds$'#%Ds$)#%Ds$+#%Ds$-#%Ds$/#%Ds$1#%Ds$3#%Ds$5#%Ds$7#%Ds$9#%Ds$;#%Ds$=#%Ds$?#%Ds$A#%Ds$C#%Ds$E#%Ds$G#%Ds$I#%Ds$K#%Ds$M#%Ds$O#%Ds$Q#%Ds$S#%Ds$U#%Ds$W#%Ds$Y#%Ds$[#%Ds$]#%Ds$_#%Ds$a#%Ds$c#%Ds$e#%Ds$g#%Ds$i#%Ds$k#%Ds$m#%Ds$o#%Ds$q#%Ds$s#%Ds$u#%Ds$w#%Ds$y#%Ds${#0sW.sW3#sEU0sW.sW-#sET1s%##WS:s%0S)sEV0sW2sW7sW.sEY0sW2sW1#sW./s%'%#m$'#US;E6EsVH1$#7LsW5sVRsVVsVz/&#%m$%#6EsVH1)#7LsW:sVWsTusW#/+#%m$%#6EsW'1.#7LsW?sV\sVZsW(/0#%m$%#aS<sWHsWGsWBsWAs%Ks%Gs%Bs%>s%:3-(##"). Qed.
End Package.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

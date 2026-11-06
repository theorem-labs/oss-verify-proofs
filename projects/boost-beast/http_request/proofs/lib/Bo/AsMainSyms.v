(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record pm_syms : Type := PMS {
  ps_tid : Z;                 (* [comment removed for export] *)
  ps_granted : bool;          (* [comment removed for export] *)
  ps_b04 : Z; ps_b05 : Z; ps_b06 : Z; ps_b08 : Z; ps_b09 : Z; ps_b10 : Z; ps_b11 : Z; ps_b12 : Z;
  ps_b13 : Z;                 (* [comment removed for export] *)
  ps_b16 : Z; ps_b20 : Z; ps_b21 : Z; ps_b22 : Z; ps_b23 : Z;
  ps_b19r : Z
}.

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.          (* [comment removed for export] *)
Definition AIMG_TOP : Z := 0x684000.
Definition ALOWSH_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition AHI_LO : Z := 0x10007fff8000.

(* [comment removed for export] *)
Definition page_up (z : Z) : Z := ((z + 4095) / 4096) * 4096.
Definition page_down (z : Z) : Z := (z / 4096) * 4096.
(* [comment removed for export] *)
Definition pm_sh (a : Z) : Z := 0x7fff8000 + a / 8.
(* [comment removed for export] *)
Definition pm_top (sp0z : Z) : Z := sp0z - 0x800000.
(* [comment removed for export] *)
Definition pm_stack_top (sp0z : Z) : Z := page_up (sp0z - 0xa0).
Definition pm_stack_bottom (sp0z : Z) : Z := pm_stack_top sp0z - 0x800000.
(* [comment removed for export] *)
Definition pm_space_beg (X : pm_syms) : Z := ((ps_b06 X) / 0x10000) * 0x10000 + 0x10000.
Definition pm_region_info (X : pm_syms) : Z := pm_space_beg X + 2^37.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_A15 (sp0z : Z) : Z := page_up (pm_sh (pm_stack_bottom sp0z)).
Definition pm_E15 (sp0z : Z) : Z := page_down (pm_sh (pm_stack_top sp0z)).
Definition pm_r (sp0z : Z) : Z := (pm_sh (pm_stack_top sp0z)) mod 4096.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_short (sp0z : Z) : bool := (0x60 <=? sp0z mod 4096) && (sp0z mod 4096 <=? 0xa0).
(* [comment removed for export] *)
Definition pm_meta_map (brk0z : Z) (X : pm_syms) : Z := if (ps_granted X) then brk0z else (ps_b19r X).
(* [comment removed for export] *)
Definition pm_envp (sp0z argc : Z) : Z := sp0z + 16 + 8 * argc.
Definition pm_auxv (sp0z argc envc : Z) : Z := pm_envp sp0z argc + 8 * (envc + 1).
Definition pm_argv0 (sp0z argc envc : Z) : Z := pm_auxv sp0z argc envc + 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pm_kernel_placed (X : pm_syms) : list (Z * Z) :=   (* [comment removed for export] *)
  [((ps_b04 X), 0x10000); ((ps_b05 X), 0x38e000); ((ps_b06 X), 0x2000011000); ((ps_b08 X), 0x800000);
   ((ps_b09 X), 0x1000); ((ps_b10 X), 0x10000); ((ps_b11 X), 0x1000); ((ps_b12 X), 0x1000); ((ps_b16 X), 0xb09000);
   ((ps_b20 X), 0x1000); ((ps_b21 X), 0x100000); ((ps_b22 X), 0x800000); ((ps_b23 X), 0x1000)]
  ++ (if (ps_granted X) then [] else [((ps_b19r X), 0x2000)]).

Fixpoint pairwise_apart (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => Forall (fun q => a + n <= fst q \/ fst q + snd q <= a) r /\ pairwise_apart r
  end.

(* [comment removed for export] *)
Definition pm_placed (sp0z : Z) (p : Z * Z) : Prop :=
  fst p mod 4096 = 0 /\ 4096 <= fst p /\ fst p + snd p <= pm_top sp0z
  /\ (fst p + snd p <= AIMG_LO \/ AIMG_TOP <= fst p)
  /\ (fst p + snd p <= ALOWSH_LO \/ AHI_LO <= fst p).

(* [comment removed for export] *)
Definition pm_band3 (sp0z : Z) (X0 n : Z) : Prop :=
  (4096 <= X0 /\ X0 + n <= AIMG_LO) \/ (AIMG_TOP <= X0 /\ X0 + n <= ALOWSH_LO) \/ (AHI_LO <= X0 /\ X0 + n <= pm_top sp0z).
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma pm_placed_band3 : forall sp0z p, pm_placed sp0z p -> 0 <= snd p -> pm_band3 sp0z (fst p) (snd p).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_placed); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_band3); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_top); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.AIMG_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.AHI_LO); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @Hn; @H5; @H4; @H; @H3; @H2; @H1; @n; @a; @z; @sp0z|] "#(1#<#o#?#`#a###_#$#U#V#%#S#T#D#'#&#g#j#(#)#*#.#3#N#+#,#-#/#0#1#B#K#2#7#4#5#X#[#p#q#6#:#@#W#Y#Z#\#^#e#k#m#o#r#s#n#;#A#C#M#i#R#O#E#H#P#G#Q#F#d#c#L#h#b#]#I#J#f#l8#Z%#[$#\$#]%#^%#_&#`'#a%#b&#c$#d&#e'#f*#g$#h%#i*#j+#k(#l&#m%#n*VS;CCVS/KF(CCH#N#+CCK(CCK-O$#k##&#k##)#j#$+#)CCHFVS/S##)CCKH+CC#$S($#$#$#$#$#$#$#$#$#$#$#0#VS00#5C#N#%2(CC4*4#,S$#$##%L#M8&$##(I#J;&$#'&#'*#'/#'1#)CCPK(CC##N#)CCOP+CC#(CC$-S)$#k##'#j##+#+CC+#>#*$,,S%#$##%L#M(&$##(I#J+&$#'&#'*#'.#VS05s#+5C#N)CCS#O+CC##s#/#(CC%*%#,S*#$##%L#M)&$##(I#J,&$#'&#'*#'/#)CCS$S#+CC##s#?#(CC%*%#,S+#$##%L#M)&$##(I#J,&$#'&#'*#'/#)CCS%S$(CC##N#)CCS)S%+CC#(CC$-S,$#k##'#j##+#+CC+*#+,S&#$##%L#M'&$##(I#J*&$#'&#'*##s#b3)CCS*S)+CC#(CC$*$#,S-#$##%L#M(&$##(I#J+&$#'&#'*#)CCS+S*+CC#(CC$*$#,S.#$##%L#M(&$##(I#J+&$#'&#'*#)CCS&S+(CC##N#)CCS,S&+CC#(CC$-S'$#k##'#j##+#+CC+*#+##L#M%&$##&I#J(&$#'&#*0/,S'#$#)CCS-S,+CC#(CC$*$###L#M&&$##&I#J)&$#'&#)CCS.S-+CC#(CC$*$###L#M&&$##&I#J)&$#'&#)CCS1S.(CC##N#)CCS'S1+CC#(CC$-S2$#k##'#j##+#+CC+*#+##I#J%&$#*,+##L#M.&$#)CCS3S'+CC#(CC$*$###I#J&&$#)CCS4S3(CC##N#US<S5US=S5VS6CKVS6CPXS>C$H#US?CUS@C6CS(6Cs$~WSAC$#%S(%#%#%#%#%#%#%#%#%#%#%#%#%#$#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#0#1C#.Cs##Q#/s#'GDDE#R$s%;%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#0#1C#.C#Qs#I/s#KGDDE#R2s#LGDDEs#'#USBD$s#($#$#0#1C#.Cs#PQ#/s#TGDDE#R$s#Q$#%#%#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#0#%S($#%#$#$#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#0#1C#.C#Qs$&/s$(GDDE#R2s$)GDDEs#3#6Cs$&.Cs$(Q#/s$,GDDE#R1Cs&?.C#Qs$-/s$/GDDE#R7s$0GDDE#s#:7s$1GDDE+s#h7s$2GDDEs#E(2s$3GDDE$#2s$4GDDE&#3s$5GDDE(s#F#3s$6GDDE,s#G#3s$7GDDE0s#H#3s$8GDDEs#Js#I#VSCs$9EVSDS7S8VSEFK5S7#S8m$%#WSFCNHXSGFK$#l#%*)#l#&s$Cs$B#l#'s$Hs$G#j#(C#j#)C#j#*C#*FH##s$%#s#^F&$#*HK##s#X#s#)H&$#*KP##O#s&bP#s&cO*OS###s#`'%##s#2O#&s$4'$##s#nO#)S$'$#&&#&*#k##/#k##1#k##4#k##9#k#(C#k#)C#k#*C#,SH[F#S9S2KPS%S&l#+s##%#)CCS9S4+CC##s&{#(CC%*%###s#y'&##s#K(#&s$M'$##s$++,S:#*#'%#&'#&+#m#3#-S:20m#$#j#,s%%#j#-s%)#j#.s%1#V#HFj##s%7#j##s%J#4s%Ks%Hs%>#Fj#/s%S#j#0s%_#V#HFj##s%d#j##s&##4s&$s%ys%o#Fj#/s&+#j#1s&:#V#HFj##s&=#j##s&`#4s&as&Us&K#Fj#/s&e#j#2s&v#V#HFj##s&z#j##s'E#4s'Fs'8s'.#Fj#/s'X#j#3C#j#4C#V#HFj#5C#j#5C#YSICCs'`#Fj#$s'j#j#6C##"). Qed.

Record pm_syms_ok (sp0z brk0z mbasez : Z) (X : pm_syms) : Prop := PMSOK {
  pso_tid    : 0 < (ps_tid X) < 2^22;                       (* [comment removed for export] *)
  pso_placed : Forall (pm_placed sp0z) (pm_kernel_placed X);
  pso_apart  : pairwise_apart (pm_kernel_placed X);                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pso_spacebeg : (ps_b06 X) < pm_space_beg X <= (ps_b06 X) + 0x10000 /\ pm_space_beg X mod 0x10000 = 0;
  pso_brk    : (ps_granted X) = true ->
               brk0z + 0x3000 <= ALOWSH_LO                                               (* [comment removed for export] *)
               /\ Forall (fun q => brk0z + 0x2000 <= fst q \/ fst q + snd q <= brk0z) (pm_kernel_placed X)
}.

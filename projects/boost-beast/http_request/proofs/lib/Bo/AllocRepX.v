(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import GapGrid.
From OSSVerify.Proofs.boost_beast.http_request.lib Require LazyNodes.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR Gap04.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AsDepotInv SecGap.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ALIBCPGSZ : Z := 0x681ab0.   (* [comment removed for export] *)
Definition AGOT_SSP  : Z := 0x1203f0.   (* [comment removed for export] *)
Definition ASSPGUARD : Z := 0x681830.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOWSH_SZ : Z := 0x10000000.

(* [comment removed for export] *)
Definition AHSB : Z := 0x2008fff7000.
Lemma AHSB_eq : AHSB = sh AHI_LO.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sh_ceiling_range : 0x10006fef8000 <= sh aceil <= 0x10007fef8000.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil_facts); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__arith; @H0; @H5; @r0; @q0; @H8; @H7; @H6; @H4; @r; @q; @H3; @H2; @H1; @H; @ACEILB|] "#'e#5#}#B#j#k#i#D#q#'###p#w#?#(#T#%#&#9#+#$#C#H#I#K#L#M#N#O#R#Q#\#^#]#`#S#e#l#u#|#}#5$$#8#@#E#0#Y#X#_#U#a#b#d#f#h#r#x#y#*#z#~$##{#)#-#.#,#3#4$%#=#>#;#:#A#F#n#m#V#[#Z#o#<#G#g#s#v#J#P#W#c#t9#g$#h$#i%#j%#k&#l%#m'#n*#o&#p$#q%#r%#s$#t%#u+#v%#w*#x%#y%#z&#{'#|&US;R$M$#$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################/#US<R%$#$s#&$#$#$#$#$#$#$#$###############################################/#%s#%#&s#%##M######################/#VS%s#4#'C#GUS=R%s#7#0s#8'(%#&%#&(#&8#m#s#m#/7VS&s#?#'C$GUS'#VS(s#B&4'#VS%s#D(0$#'Cs#F#k##(#VS)s#H,(G-%G(()/&$#k##&#VS*s#N2(3G(4.%/G&$#k##&#VS+s#T8'C5Gk##8#VS,s#W;'C6s#Xk##;#VS&s#Zs#)'Cs#*GUS'#VS(s#]s#,4s#-#0#s#-'Cs#`#k##'#VS)s#bs#1(Gs#2%Gs#2(s#3s#4&$#k##&#VS*s#hs#7(s#8G(s#9s#8%s#9G&$#k##&#VS+s#ns#='C4Gk##7#VS,s#qs#@'Cs#@s#rk##:#VS-Gs#C5S.#m##5UN#%GJ(Js#H&$#VS-Gs#?5S.#m##s#6US>#%GS#(S#s#D&$#US?MVS@C#,S/,#,#,#,#,#,#-C#6C+#-C'-C)-C-6C/#+C%#+C'#+C)#VSACs#X-CS/WS0C$#,/-C#-C6WS0C(-+C$#+C0#+C'#+C*#VS1#S2VSB/#-C:6CA6+C,/+C$#+C&#VS1#S2USCOWS3O$#WS3O+#USDOUSECVS4CN7C$P#VS4CI7C#Q&7C%S$#USFCUSGC.Cs$&.CG)C$K#*&FDDE#HZS5'FDDE#USHD2Cs$8#s%12C#WS6C+#2Cs%48C$#)C(K#*0FDDE#H11FDDE,+#$s$A2C#)C2L#*5FDDE#H.Cs$.)C&SI#*8FDDE#H39FDDE&#)C&K8*;FDDE#HZS5<FDDE#2CMWS6C*#8C#.)C9K#*AFDDE#H1BFDDE(<#.Cs$x)C#L=*s#%FDDE#H.Cs$X)C@L#*s#(FDDE#H3s#)FDDE&#)C?Ks#(*s#+FDDE#HZSJs#,FDDESK3s#-FDDE$#3s#.FDDE'##s$S$#$###$#$#$#$#$#$#$###$#$#$#$#$###############################/#.C##s%G############################/#.C#8C#s#G)C5L#*s#dFDDE#H$s#6$#$#$#$#$#$#$###$#$#$#$#$###############################/#.C#)Cs#$L#*s$)FDDE#H3s$*FDDEs#$#1s$+FDDEs#[s$%#1s$,FDDEs#hs$&#1s$-FDDEs#rs$'#1s$.FDDEs#{s$(#VSLs$/E5S7S8VSMJP'S7#S8m$%#WSNCGS$XSOJP$#l#$*)#l#%s$9s$8#l#&s$As$@#j#'C#j#(C#j#)C#j#*C#j#+C#j#,S9#k##s%:S:4s%cN0#Q'CP#k##&#%GI(Is%]&$#k##s%]S:4s%`Q0#SP'CI#k##&#%s&EI%Is&#&$#'CNG&#S#&%#0s#PI%s#b#%$s#0&$#k##'#k##.#k##4#k##8#k#'C#k#(C#k#)C#k#*C#k#+C#k#,S9#^Js%|ISQQs&XSRSSS$STSUl#-s#%$#l#.s%:s%7#l#/s%Bs%?#l#0s&*C#l#1s%^C#l#2s%Ks%I#l#3s%Os%M#l#4s%Vs%Q#l#/s%]s%X#l#5s%fs%_#l#6s%}C#l#7s&$C#l#8s%ls%j#l#9s%ps%n#l#:s%ws%r#l#.s%~s%y#l#;s&,s&$#USVs&j%s$&#%$s#P&$#m#'#l#<s&4s&5##"). Qed.
Lemma sh_ceiling_lt_AHI_LO : sh aceil < AHI_LO.
Proof. pose proof sh_ceiling_range. unfold AHI_LO. lia. Qed.

(* #38 RESERVED-CEILING-CLASS: the floor for the launch's extra reserved bases,
   the same constant as [As/AsanPlanSound.v RESX_LO] in this file's vocabulary.
   [Run.v:3154 valid_mmap_base] - the va-INDEPENDENT predicate, assumed at
   [As/AsanInit.v:105], NOT [valid_mmap_base_va], so Sv39's zero floor is not
   reachable here - gives [State.v:321 mmap_base_min] = 0x154555557000, and
   [As/AsanInit.v:482 vtop_range] with [State.vdso_len_bounds] puts every extra
   base at or above 0x154555542001.  This is that rounded DOWN; margin 0x542001.
   It sits far above [AHI_LO] = [AsanPlanCore.v:34 KHI] = 0x10007fff8000, where
   every window this unit maps ends ([AHIGHSH], [sh_ceiling_lt_AHI_LO]). *)
Definition ARESX_LO : Z := 0x154555000000.

(* [comment removed for export] *)
Definition ehigh (e : word * word) : bool := AHI_LO <? KInv.ehi e.      (* [comment removed for export] *)
Definition hcnt (E : list (word * word)) : Z := zlen (List.filter ehigh E).
Definition hlen (E : list (word * word)) : Z := zsum (map (fun e => bv_unsigned (snd e)) (List.filter ehigh E)).
Definition schigh (sc : schunk) : bool := AHI_LO <? sc_map_beg sc + sc_map_size sc.
Definition hsec (st : astate) : list schunk := List.filter schigh (as_sec st).
Definition AHC0 : Z := 32.            (* [comment removed for export] *)
Definition AHL0 : Z := 2 ^ 38.        (* [comment removed for export] *)
Definition ASECMAX : Z := 2 ^ 32 + 2 ^ 14.   (* [comment removed for export] *)

Lemma hcnt_nil : hcnt [] = 0. Proof. reflexivity. Qed.
Lemma hlen_nil : hlen [] = 0. Proof. reflexivity. Qed.
Lemma hcnt_cons : forall e E, hcnt (e :: E) = (if ehigh e then 1 else 0) + hcnt E.
Proof. intros e E. unfold hcnt, zlen. cbn [List.filter]. destruct (ehigh e); cbn [length]; lia. Qed.
Lemma hlen_cons : forall e E, hlen (e :: E) = (if ehigh e then bv_unsigned (snd e) else 0) + hlen E.
Proof. intros e E. unfold hlen. cbn [List.filter]. destruct (ehigh e); cbn [map zsum]; lia. Qed.
Lemma hcnt_nonneg : forall E, 0 <= hcnt E. Proof. intros E. unfold hcnt, zlen. lia. Qed.
Lemma hlen_nonneg : forall E, 0 <= hlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hlen_nil; lia|]. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_cons_le : forall e E, hcnt (e :: E) <= 1 + hcnt E.
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_le : forall e E, hlen (e :: E) <= bv_unsigned (snd e) + hlen E.
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_cons_ge : forall e E, hcnt E <= hcnt (e :: E).
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_ge : forall e E, hlen E <= hlen (e :: E).
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_app : forall E1 E2, hcnt (E1 ++ E2) = hcnt E1 + hcnt E2.
Proof. intros E1 E2. unfold hcnt, zlen. rewrite filter_app, length_app. lia. Qed.
Lemma hlen_app : forall E1 E2, hlen (E1 ++ E2) = hlen E1 + hlen E2.
Proof. intros E1 E2. unfold hlen. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma hcnt_low_cons : forall e E, KInv.ehi e <= AHI_LO -> hcnt (e :: E) = hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_low_cons : forall e E, KInv.ehi e <= AHI_LO -> hlen (e :: E) = hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_high_cons : forall e E, AHI_LO < KInv.ehi e -> hcnt (e :: E) = 1 + hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_high_cons : forall e E, AHI_LO < KInv.ehi e -> hlen (e :: E) = bv_unsigned (snd e) + hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_low : forall E, Forall (fun e => KInv.ehi e <= AHI_LO) E -> hcnt E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hcnt_low_cons by exact He. exact IH. Qed.
Lemma hlen_low : forall E, Forall (fun e => KInv.ehi e <= AHI_LO) E -> hlen E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hlen_low_cons by exact He. exact IH. Qed.
Lemma hcnt_le_len : forall E, hcnt E <= zlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hcnt_nil; unfold zlen; cbn; lia|]. rewrite hcnt_cons. unfold zlen in *. cbn [length]. destruct (ehigh e); lia. Qed.
Lemma hlen_le_total : forall E, hlen E <= zsum (map (fun e => bv_unsigned (snd e)) E).
Proof.
  intros E. induction E as [|e E IH]; [rewrite hlen_nil; cbn; lia|]. rewrite hlen_cons. cbn [map zsum].
  pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia.
Qed.
(* [comment removed for export] *)
Lemma hcnt_map_remove_le : forall E lo, hcnt (map_remove E lo) <= hcnt E.
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hcnt_cons; destruct (ehigh e); lia| pose proof (hcnt_cons_ge e E); lia].
Qed.
Lemma hlen_map_remove_le : forall E lo, hlen (map_remove E lo) <= hlen E.
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hlen_cons; destruct (ehigh e); lia| pose proof (hlen_cons_ge e E); lia].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.False Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Lemma hcnt_map_remove_in : forall E e, In e E -> AHI_LO < KInv.ehi e -> hcnt (map_remove E (fst e)) <= hcnt E - 1.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.KInv.ehi); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.hcnt); constr:(@Stdlib.Lists.List.filter); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.cons); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.hcnt_map_remove_le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_remove); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.hcnt_high_cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.bv_eqb_refl); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.ehigh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.hcnt_cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.hcnt_cons_ge); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Numbers.BinNums.xI)|] [|@p; @IN; @E; @e0; @b; @z; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @L; @H0; @__x3; @IH; @H; @e|] "#&f#1#x#Q###]#$#N#&#^#%#\#'#*#+#)#b#c#m#(#,#P#9#U#4#G#T#W#g#q#p#r#w#x#u#7#6#5#=#;#<#F#I#H#M#-#S#X#Y#[#d#h#j#k#l#i#.#n#o#/#0#s#t#y#z#K#>#@#?#E#J#B#D#C#A#R#:#`#_#8#Z#O#f#e#L#V#a#v8#c$#d%#e%#f&#g$#h&#i&#j&#k%#l&#m'#n*#o$#p+#q)#r&#s&#t&#u'#v%#w%/S&/#/#/#/#/#US3#US4#VS5##US(#,$DFUS6FVS7S8#,'HD())D(**S#),$#'#j#$,#*-#F###FUS9S&%$#$&#k#%.#j#&3#US)5,6J#*7-$###&%#,$%#j##S:#VS;#Dj#%*#,?LD(AAO)s##;#'#j#$s###*s#$#F##$#7k#%*#&s#(JF,s#)S##4s#*HO,s#+OJVS<$#(s#.s#.L(s#/s#/M)s#1$#'#(s#2s#2N)s#4s#,#'#j#$s#4#*s#5#H&s#6L#nG#$##s#6)#%###$##&s#9LH##%#s#-$&#j##3#4s#>LM(s#@s#@S$)s#Bs#:#'#(s#Cs#CS=)s#Es#=#'#j#$s#E#*s#F#S#&s#GD#nG#$##s#G)#%###$##&s#JDS###%#s#>$&#j#'s#N#'D&s#PS$,nG#$##s#P$#%###-##&s#SS$S###%#s#G$&#j#(G##L+s#K##6%Ds#M$$#j#)C#VS>Ls#/VS*Ls#0##$#+US)S'US(S'VS+CJUS?C5C$F#US@CUSAC6CS&6Cs#r-C$P#.&KEEI#QUSBEVS,Cs#`2C#'3C#$-C*P#.,KEEI#Q0-KEEI)(#VSC.IVSDGS%VSEDJ4G#S%m$%#WSFCRFXSGDJ$#l#**)#l#+87#l#,=<#j#-C#j#.C#$DF+s#sJ%#s#t$F#k##&#k#-C#k#.C##O(s$-s$-SH)s$/s$'#'#j#$s$/#*s$0#O##WD)#Fl#/2+#l#0s#4s#1#&s$5NL##WSINLO1Cs#=s#9&$#'S%j#$s$:s#W*s$;#L&s$<N#nG#$##s$<&#%###$##%+s$1$$#m#+#)s$Ds#os#oVSJs$Es#p1GS%s#K%$#1s$ENs#U#S#Dj#1s#f#U#Dj##s#|#,s$IMHUHD#2%s#Rs$>$$#)s$Ps$0s#m'#(s$Qs$QSK)s$Ss$K#'#j#$s$S#*s$T#M&s$UN#nG#$##s$UD#%###$##&s$XNM##%#s$L$&#j#(G#US-MnG#$##C##%#s$P#R+#s#0$D(j#)C#+&s#9US-NnG#$##C##%#s$V#R#3+$#$#s#jj#)C#nG#$##CD#%#s$[#R(s$ks$kSL)s$ms$e#'#j#$s$m#*s$n#N##+)##N++#%#s$e$&#j#(G#3Cs#js#f-Cs#lP#.s#nKEEI#Q2Cs#is#n-C#Ps#h.s#qKEEI#Q0s#rKEEI&s#m#l#*#s#gs#al#+s#vs#u#l#,s#{s#z#j#-C#j#.C#%Fs$t$D#+s$vF$#s#ak##%#k#-C#k#.C#WD:<Hl#/+$#VS,CR2C#s$%2C$s$%3C#s#~-C%P#.s$*KEEI#Q0s$+KEEI;s$&#l#*#s#|s#vl#+s$/s$.#l#,s$4s$3#j#-C#j#.C#+RF+RJ%#s%/$%#k##:#k#-C#k#.C#l#/*#7XS.s#,7#Dl#(s#EG#&s%EMO##VS/MO1Cs#Ds#>&$#&s%IMs#w##VS/Ms#y1Cs#Ks#I&$#VSMMO$s$%*US0S1US0#7C#7C%7CS1WS2C$#WS2C&#VSN#SO&S'#s$SVS+CH5C#Hs$R5Cs$TF#USPs%c6C#-C#Ps$Q.s$TKEEI#Q3C%s$O-Cs$UP#.s$WKEEI#Q0s$XKEEI#s$Ss#H0s$YKEEI's$T#l#*#s$Ns$Hl#+-s$\#l#,1s$a#j#-C#j#.C#j#2C#$JF%Hs%]$F#$J$k##$#k##'#k#-C#k#.C#k#2C#&s%sS$N##YDs#b#s#dFHl#//&#l#1s#,s#+#XS.s#zs#.#Dl#(s$,G#l#3s$2s$/#j#%s$4#U#Dj##s%T#ZSQs%Vs%Us%Cs$8#D)s&%s%ys%S'#j#$s&%#&s&&HJ*s&'$####%%#s%x$%#m#,#j#%s%b#j#3s%e#j#&s&.#j#'s&0#ZSRs&1s%{s%q#HF(s&3s&3JVS*H####H%#s&($%#m#)#j#4s&5#j#%s&8#j#5s&;#j#&s&;##"). Qed.
Lemma hlen_map_remove_in : forall E e, In e E -> AHI_LO < KInv.ehi e -> hlen (map_remove E (fst e)) <= hlen E - bv_unsigned (snd e).
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hlen_high_cons e E H). pose proof (hlen_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hlen_cons; destruct (ehigh e0); lia| pose proof (hlen_cons_ge e0 E); lia].
Qed.
(* [comment removed for export] *)
Lemma hsec_nil_st : forall st, as_sec st = [] -> hsec st = [].
Proof. intros st E. unfold hsec. rewrite E. reflexivity. Qed.
Lemma zlen_filter_app {A} : forall (f : A -> bool) l1 l2, zlen (List.filter f (l1 ++ l2)) = zlen (List.filter f l1) + zlen (List.filter f l2).
Proof. intros f l1 l2. unfold zlen. rewrite filter_app, length_app. lia. Qed.
Lemma zlen_filter_cons {A} : forall (f : A -> bool) x l, zlen (List.filter f (x :: l)) = (if f x then 1 else 0) + zlen (List.filter f l).
Proof. intros f x l. unfold zlen. cbn [List.filter]. destruct (f x); cbn [length]; lia. Qed.
Lemma zlen_filter_nil {A} : forall (f : A -> bool), zlen (List.filter f (@nil A)) = 0. Proof. reflexivity. Qed.
Lemma zsum_size_filter_app : forall (f : schunk -> bool) l1 l2,
  zsum (map sc_map_size (List.filter f (l1 ++ l2))) = zsum (map sc_map_size (List.filter f l1)) + zsum (map sc_map_size (List.filter f l2)).
Proof. intros f l1 l2. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma zsum_size_filter_cons : forall (f : schunk -> bool) x l,
  zsum (map sc_map_size (List.filter f (x :: l))) = (if f x then sc_map_size x else 0) + zsum (map sc_map_size (List.filter f l)).
Proof. intros f x l. cbn [List.filter]. destruct (f x); cbn [map zsum]; lia. Qed.
Lemma schigh_iff : forall sc, schigh sc = true <-> AHI_LO < sc_map_beg sc + sc_map_size sc.
Proof. intros sc. unfold schigh. rewrite Z.ltb_lt. tauto. Qed.
Lemma ehigh_wz : forall a n, 0 <= a < 2^64 -> 0 <= n < 2^64 -> ehigh (wz a, wz n) = schigh (mkSC a n 0).
Proof. intros a n Ha Hn. unfold ehigh, schigh, KInv.ehi, wz. cbn [fst snd sc_map_beg sc_map_size]. rewrite !unsigned_lit by lia. reflexivity. Qed.

Section X.
  Variable s : ast.
  Let st := a_st s.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition awin_vis (m : mem) : Prop :=
    forall x : word, in_rangesb x (a_S s) = true -> wview bsegs m x <> None.

  (* [comment removed for export] *)
  Definition flagsx_rep (m : mem) : Prop :=
       rw_cells bsegs m ALIBCPGSZ [C8 (wz 4096)]
    /\ rw_cells bsegs m AGOT_SSP [C8 (wz ASSPGUARD)]
    /\ (exists g : word, rw_cells bsegs m ASSPGUARD [C8 g])
    /\ rw_cells bsegs m (ACFLAGS + 219) [C1 (b8 1)]
    /\ (exists b : byte, rw_cells bsegs m (ACFLAGS + 244) [C1 b]).

  Definition AREPX (m : mem) : Prop := AREP s m /\ awin_vis m /\ flagsx_rep m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* #38 RESERVED-CEILING-CLASS: [akernel] is now [akernel_pre /\ akernel_resx].
     The eighteen conjuncts of [akernel_pre] are the pre-#38 list, in order, with
     only the first one's LIST changed; [akernel_resx] is the split that carries
     the launch's extra reserved intervals.  Factoring rather than appending keeps
     the recorded body of [AS_InstMainK.akernel_main] usable for [akernel_pre]
     verbatim: it proves exactly that conjunction and nothing else. *)
  (* #38: an ABBREVIATION, not a Definition.  A KReplay body that binds the
     hypothesis by name (ak_hsm_full, constr:(AK)) needs the conjunction
     visible SYNTACTICALLY; with a Definition wrapper the replay sees
     "akernel_pre mo" and refuses it against the spelled-out type, even
     though the two are convertible.  Measured on the farm,
     both mirrors, "The term proj1 AKfull has type akernel_pre mo while it is
     expected to have type (forall e, ...) /\ ...". *)
  #[local] Notation akernel_pre mo :=
    ((let h := m_vmmaps mo in
       (* #38 RESERVED-CEILING-CLASS.  This bound was stated over [vm_reserved h]
          and is FALSE there: at 75d69e00 [init_reserved] appends [vdso_reserved]
          (State.v:6540-6545), and this tree's own [As/AsanPlanSound.v:340 co_vdso]
          witnesses that the pair really is in [vm_reserved].  The pair hangs off
          [mm->mmap_base], not off the image.  SPLIT, not weakened: the bound keeps
          its text over the IMAGE's reservations, and the launch's extra intervals
          are carried by [akernel_resx]. *)
       (forall e, In e (segments_reserved bsegs) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= AIMG_TOP)
    /\ (* [comment removed for export] *)
       (vm_limit h = target_alloc_limit /\ alloc_top h = hceil)
    /\ (* [comment removed for export] *)
       (forall x : word,
          (a_thr s <= bv_unsigned x < a_thr s + kPageSize \/ a_ctx s <= bv_unsigned x < a_ctx s + 160
           \/ a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize \/ a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve
           \/ a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE
           \/ sh AHI_LO <= bv_unsigned x < AHI_LO) ->               (* [comment removed for export] *)
          in_rangesb x (vm_maps h) = true)
    /\ (* [comment removed for export] *)
       (forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
          map_contains (vm_maps h) a n = true)
    /\ (* [comment removed for export] *)
       (forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (* [comment removed for export] *)
       (forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true)
    /\ (forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
          in_rangesb x (vm_noaccess h) = false)
    /\ (* [comment removed for export] *)
       (forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h))
    /\ (* [comment removed for export] *)
       (forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true)
    /\ (forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
          map_contains (vm_maps h) a n = true)
    /\ (forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (* [comment removed for export] *)
       (forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true)
    /\ (* [comment removed for export] *)
       (hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
        /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX))
    /\ (* [comment removed for export] *)
       (forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil)
                           \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
          region_free (vm_noaccess h) a n = true))) (only parsing).

  (* #38 RESERVED-CEILING-CLASS, the split.  This is the shape the producer already
     builds: [As/AsanPlanSound.v:333-337 co_res] and [Bo/BoMainFacts.v pm_reserved]
     give exactly this [rx], and the entry facts are [As/AsanPlanSound.v:126-139
     resx_entry_ok] transcribed into this file's own vocabulary ([img_hi BOTH_H] is
     [AIMG_TOP]; [AsanPlanCore.v:34 KHI] is [AHI_LO], both 0x10007fff8000).  NOT a
     claim that the pair is above the allocator's ceiling: [vdso_top =
     page_round_down (mmap_top)] and [mmap_top = min (vm_mmap_base)
     (page_round_down alloc_top)] (State.v:3466, :3483), so the pair is BELOW
     [alloc_top] by construction.  What separates it from every window this unit
     maps is [AHI_LO] - the app region ends there, the high shadow [AHIGHSH]
     ([BSegs.v:44]) ends exactly there, and [sh aceil < AHI_LO]
     ([sh_ceiling_lt_AHI_LO]) - with a 4096-byte margin. *)
  Definition akernel_resx (mo : Model) : Prop :=
    let h := m_vmmaps mo in
    exists rx : list (word * word),
      vm_reserved h = segments_reserved bsegs ++ rx
      /\ (forall e, In e rx ->
            0 < bv_unsigned (snd e)
            /\ bv_unsigned (fst e) mod 4096 = 0
            /\ bv_unsigned (snd e) mod 4096 = 0
            /\ AIMG_TOP <= bv_unsigned (fst e)
            /\ AHI_LO + 4096 <= bv_unsigned (fst e)
            /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 47
            (* the seventh component, [As/AsanPlanSound.v RESX_LO <= fst iv].
               This is the one that makes [ak_resf] usable: [AHI_LO + 4096]
               above is where the allocator's own windows END, so a consumer
               placing ABOVE it gets nothing from the fifth component. *)
            /\ ARESX_LO <= bv_unsigned (fst e))
      (* #38: the pair's COUNT and TOTAL SIZE.  [cost] needs both and the
         per-entry facts give neither.  Straight from [ak_reserved]:
         [length rx <= n_resx BOTH_H] = 2 and [sum_sizes rx <= resx_bytes
         BOTH_H] = 20 * 4096. *)
      /\ (length rx <= 2)%nat
      /\ zsum (map (fun e => bv_unsigned (snd e)) rx) <= 81920
      (* #38 RESERVED-CEILING-CLASS, the MAPS-vs-RESERVED DISJOINTNESS conjunct.
         WHY IT IS HERE AND NOT DERIVED.  [ak_resf] bounds a range away from the
         reserved ledger by ARITHMETIC: every [rx] entry starts at or above
         [ARESX_LO], so a range ending below [ARESX_LO] misses the pair.  That
         route is EXHAUSTED for a consumer that cannot bound its range above.
         [aapp_lit] ({As,Bo}/AllocRep.v:148) splits [aapp] into
         [X + k <= ALOWSH_LO \/ AHI_LO <= X]; the low arm closes arithmetically,
         but the HIGH arm gives only a LOWER bound on [X] and the layout permits
         [X] to run to [2 ^ 47] = 140,737,488,355,328, SIX TIMES
         [ARESX_LO] = 23,387,522,990,080.  So the residual is not merely unfound,
         it is UNPROVABLE from the hypotheses the caller has, and no stronger
         per-entry bound rescues it: the existing fifth component
         [AHI_LO + 4096] = 17,594,333,499,392 lies BELOW [ARESX_LO], so a lemma
         keyed on it is strictly WEAKER than [ak_resf], not stronger.
         The sound carrier for a range that is MAPPED rather than bounded is the
         disjointness of the live mappings from the reserved ledger - the model's
         own [co_mres] ([As/AsanPlanSound.v:420]), whose conclusion is exactly
         this [Forall]/[Forall] pair spelled here as two [In] quantifiers so this
         file needs no new import and no [iv_disjoint] name.
         IT IS INIT-ONLY, like every other conjunct of [akernel_resx]: proved once
         at the concrete construction site ([AS_InstMainK.akernel_main]) straight
         from [co_mres], and transported unchanged thereafter.
         NOTHING EXISTING IS WEAKENED.  [ak_resf], the seven per-entry components,
         the count and size bounds and [ARESX_LO] are all untouched; this is an
         ADDED conjunct, so [akernel_resx] is strictly STRONGER than before and
         every existing consumer keeps the fact it already used. *)
      /\ (forall iv, In iv (vm_maps h) ->
            forall e, In e (vm_reserved h) ->
              bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
              \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)).

  Definition akernel (mo : Model) : Prop := akernel_pre mo /\ akernel_resx mo.

  Definition AMODELX (mo : Model) : Prop := AMODEL s mo /\ akernel mo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Derived.
    Variable mo : Model.
    Hypothesis AKfull : akernel mo.
    (* #38 RESERVED-CEILING-CLASS: [akernel] is now [akernel_pre /\ akernel_resx].
       [AK] keeps naming the pre-#38 conjunction, so every projection chain below
       and the recorded body of [ak_hsm_full] (which binds [AK] by name) are
       unchanged; only the two lemmas that need the split mention [AKfull]. *)
    #[local] Notation AK := (proj1 AKfull) (only parsing).
    Let h := m_vmmaps mo.

    (* #38 RESERVED-CEILING-CLASS: the split half of [akernel], re-exported so
       consumers can take [region_free_app] over the two halves and stay
       single-bound on each. *)
    Lemma ak_resx : exists rx : list (word * word),
      vm_reserved h = segments_reserved bsegs ++ rx
      /\ (forall e, In e rx ->
            0 < bv_unsigned (snd e)
            /\ bv_unsigned (fst e) mod 4096 = 0
            /\ bv_unsigned (snd e) mod 4096 = 0
            /\ AIMG_TOP <= bv_unsigned (fst e)
            /\ AHI_LO + 4096 <= bv_unsigned (fst e)
            /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 47
            /\ ARESX_LO <= bv_unsigned (fst e))
      (* #38: the pair's COUNT and TOTAL SIZE.  [cost] needs both and the
         per-entry facts give neither.  Straight from [ak_reserved]:
         [length rx <= n_resx BOTH_H] = 2 and [sum_sizes rx <= resx_bytes
         BOTH_H] = 20 * 4096. *)
      /\ (length rx <= 2)%nat
      /\ zsum (map (fun e => bv_unsigned (snd e)) rx) <= 81920
      (* #38: the maps-vs-reserved disjointness conjunct, re-exported with the rest. *)
      /\ (forall iv, In iv (vm_maps h) ->
            forall e, In e (vm_reserved h) ->
              bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
              \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)).
    Proof. exact (proj2 AKfull). Qed.



    (* #38: the whole ledger.  The upper premise is what the vDSO pair costs, and
       [ARESX_LO] rather than [AHI_LO + 4096] is what makes it payable: every
       caller whose range lies anywhere in this unit's address space - including
       the large and secondary groups ABOVE [AHI_LO] - discharges it. *)
    Lemma ak_resf : forall a k : word, AIMG_TOP <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned k <= ARESX_LO -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha Hk. destruct ak_resx as [rx [Hr [Hok _]]]. destruct AK as (K1 & _).
      rewrite Hr. apply region_free_introZ. intros e sz He.
      apply in_app_or in He as [He|He].
      - specialize (K1 (e, sz) He). cbn [fst snd] in K1. pose proof (bv_unsigned_in_range _ k). right. lia.
      - pose proof (Hok (e, sz) He) as (_ & _ & _ & _ & _ & _ & HK). cbn [fst] in HK. left. lia.
    Qed.
    (* #38 RESERVED-CEILING-CLASS: the ledger lemma for a range that is MAPPED
       rather than arithmetically bounded.  Keyed on [map_contains] and NOT on
       [In iv] plus containment bounds, because [map_contains] is what the caller
       already holds: [ak_pamc] proves exactly [map_contains (vm_maps h) a n = true]
       for the ptr-array window, on the bullet IMMEDIATELY PRECEDING the one that
       needs this.  So the consumer passes the same term twice and derives no new
       geometry.
       Proof body transcribed from this unit's own [As/AsanNodesMmLib.v:1501-1514
       reserved_free_inside], with [co_mres] replaced by the [akernel_resx]
       conjunct that carries it and the [In iv] premise replaced by the
       [existsb_exists] elimination of [map_contains] ([State.v:8279-8286]), which
       yields the same containment bounds.  No upper bound on [a] is needed or
       used - that is the whole point of this lemma. *)
    Lemma ak_resf_inside : forall a k : word,
      map_contains (vm_maps h) a k = true -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Hmc. destruct ak_resx as [rx [_ [_ [_ [_ HD]]]]].
      unfold map_contains in Hmc. apply existsb_exists in Hmc as [iv [Hiv Hb]].
      cbv beta in Hb. apply andb_true_iff in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      apply region_free_introZ. intros e sz He.
      specialize (HD iv Hiv (e, sz) He). cbn [fst snd] in HD.
      destruct HD as [HD|HD]; [left | right]; lia.
    Qed.
    (* #38 RESERVED-CEILING-CLASS: the term the allocator's [RESF] slots
       ({As,Bo}/AS_Refill2.v, AS_Refill3.v, AS_Refill4.v, AS_Rta.v,
       AS_LcDealloc.v, AS_RecyclePrim.v) are fed.  Keyed on [map_contains] and
       proved from [ak_resf_inside]: those slots name windows inside the primary
       region, whose [sb] is bounded only by [AHI_LO] and [aceil], so the former
       upper premise [a + k <= ARESX_LO] could not be paid there.  The [AHI_LO]
       premise is unused but kept: the recorded bodies of the AG_* callers
       (AG_Free8, AG_FreeMid, AG_MallocCold, AG_CacheDealloc3, AG_RecyclePrim)
       pass this lemma through a lambda that binds exactly that premise
       ([fun a kk (Ha : AHI_LO <= bv_unsigned a) => ak_resf_hi .. a kk Ha]), so
       the slots keep it and those bodies stay valid unchanged. *)
    Lemma ak_resf_hi : forall a k : word, AHI_LO <= bv_unsigned a ->
      map_contains (vm_maps h) a k = true -> region_free (vm_reserved h) a k = true.
    Proof. intros a k _ Hmc. exact (ak_resf_inside a k Hmc). Qed.
    Lemma ak_resf_sh : forall a k : word, sh AHI_LO <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned k <= ARESX_LO -> region_free (vm_reserved h) a k = true.
    Proof. intros a k Ha Hk. apply ak_resf; [unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *; lia | exact Hk]. Qed.
    (* [comment removed for export] *)
    Lemma ak_hcov : hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
                    /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). exact K10. Qed.

    Lemma ak_limit : vm_limit h = target_alloc_limit.
    Proof. destruct AK as (_ & (K2 & _) & _). exact K2. Qed.
    (* [comment removed for export] *)
    Lemma ak_atop : alloc_top h = hceil.
    Proof. destruct AK as (_ & (_ & K2) & _). exact K2. Qed.
    Lemma ak_atop_ge_aceil : aceil <= alloc_top h.
    Proof. rewrite ak_atop. exact aceil_le_hceil. Qed.
    (* [comment removed for export] *)
    Lemma ak_grant_below_aceil : forall a len, a mod 4096 = 0 -> len mod 4096 = 0 -> a + len <= alloc_top h -> a + len <= aceil.
    Proof. intros a len Ha Hl Hb. rewrite ak_atop in Hb. exact (grant_below_aceil a len Ha Hl Hb). Qed.

    Lemma ak_tmaps : forall x : word, a_thr s <= bv_unsigned x < a_thr s + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_cmaps : forall x : word, a_ctx s <= bv_unsigned x < a_ctx s + 160 -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_sbmaps : forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_pmaps : forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_fsmaps : forall x : word, a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
Scheme kc__4 := Elimination for Corelib.Init.Logic.and Sort Prop.
    Lemma ak_hsm_full : forall x : word, sh AHI_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    (* #38 RESERVED-CEILING-CLASS: was a KReplay body, which bound [AK] by name
       and TRANSPORTED its first conjunct, so the split retyped it out from under
       the replay (both mirrors, span 6310-6314:
       "In e (segments_reserved bsegs)" against "In e (vm_reserved (m_vmmaps mo))").
       It needs only the SIXTH disjunct of conjunct 3 - exactly what the five
       lemmas above prove in one line each - so the recorded body is replaced by
       theirs rather than re-authored.  A recorded body that transports a changed
       fact is ~150 lines; this one was never worth encoding. *)
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_hsm : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. apply ak_hsm_full. pose proof sh_ceiling_lt_AHI_LO. lia. Qed.

    Lemma ak_prim : forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize -> map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_pamc : forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_hsmc : forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & K4 & _). exact K4. Qed.

    Lemma ak_zr_sb : forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zr_pa : forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zrsh : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj1 (K5 x Hx)). Qed.
    Lemma ak_lsh : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_L s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj2 (K5 x Hx)). Qed.
    Lemma ak_noacc_maps : forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K6a & _). exact K6a. Qed.
    (* [comment removed for export] *)
    Lemma ak_sec_noacc : forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
      in_rangesb x (vm_noaccess h) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K6b & _). exact K6b. Qed.
    (* [comment removed for export] *)
    Lemma ak_free_noacc : forall (a n x : word), region_free (vm_maps h) a n = true ->
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x (vm_noaccess h) = false.
    Proof.
      intros a n x FR Hx. destruct (in_rangesb x (vm_noaccess h)) eqn:E; [| reflexivity]. exfalso.
      pose proof (ak_noacc_maps x E) as M. rewrite (LazyNodes.region_free_not_in _ a n x FR Hx) in M. discriminate M.
    Qed.
    Lemma ak_secmaps : forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K7 & _). exact K7. Qed.

    (* [comment removed for export] *)
    Lemma ak_shland : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8a & _). exact K8a. Qed.
    Lemma ak_lsm : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. apply ak_shland. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia. Qed.
    Lemma ak_lsmc : forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8b & _). exact K8b. Qed.
    Lemma ak_zrsl : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj1 (K8c x Hx)). Qed.
    Lemma ak_lsl : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_L s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj2 (K8c x Hx)). Qed.
    Lemma ak_imgr : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K9 & _). exact K9. Qed.
    Lemma ak_zrsh2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (a_Zr s) = true.
    Proof. intros x [Hx|Hx]; [apply ak_zrsh; exact Hx| apply ak_zrsl; exact Hx]. Qed.
    Lemma ak_lsh2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (a_L s) = true.
    Proof. intros x [Hx|Hx]; [apply ak_lsh; exact Hx| apply ak_lsl; exact Hx]. Qed.
    Lemma ak_shm2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (vm_maps h) = true.
    Proof. intros x [Hx|Hx]; [apply ak_hsm; exact Hx| apply ak_lsm; exact Hx]. Qed.
    Lemma ak_shmc2 : forall a n : word, 0 < bv_unsigned n ->
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      map_contains (vm_maps h) a n = true.
    Proof. intros a n Hn [[H1 H2]|[H1 H2]]; [apply ak_hsmc| apply ak_lsmc]; assumption. Qed.
    Lemma ak_shrf2 : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_reserved h) a n = true.
    (* #38: [ak_resf] now carries the upper premise the vDSO pair costs.  Both
       disjuncts discharge it from the band they already bound: [sh_ceiling_range]
       puts [sh aceil] at most 0x10007fef8000 and [sh ALOWSH_LO] is smaller again,
       both far below [ARESX_LO] = 0x154555000000.  The Bo twin was a KReplay body
       transporting the old one-premise shape; it is replaced by this text, which
       is the As mirror's own proof. *)
    Proof.
      intros a n [[H1 H2]|[H1 H2]]; pose proof sh_ceiling_range;
        apply ak_resf;
        unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP, ARESX_LO, ALOWSH_LO in *; lia.
    Qed.
    (* [comment removed for export] *)
    Lemma ak_shna : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_noaccess h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11). exact K11. Qed.

    (* [comment removed for export] *)
    Lemma grant_aapp : forall (a : word) (n : Z),
      bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= alloc_top h -> n mod 4096 = 0 -> 0xF000 < n ->
      region_free (vm_reserved h ++ vm_maps h) a (wz n) = true -> aapp (bv_unsigned a) n.
    Proof.
      ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(h); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.X.Derived.ak_grant_below_aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil_facts); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.region_free_not_in); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb_app); constr:(@kc__4); constr:(@Stdlib.Bool.Bool.orb_false_iff); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.ZArith.BinInt.Z.lt_ge_cases); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@Corelib.Init.Logic.or); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp); constr:(@Corelib.Init.Logic.False_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_LO); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.X.Derived.ak_imgr); constr:(@Stdlib.ZArith.BinInt.Z.le_gt_cases); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ALOWSH_LO); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_hi); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.HCW.X.Derived.ak_shland); constr:(@Corelib.Init.Logic.or_intror)|] [|@Ha; @a; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__arith; @__sat2; @__sat1; @zh; @H0; @H6; @H12; @H16; @H15; @H14; @H13; @H11; @H10; @H9; @H8; @H7; @H5; @H4; @H3; @H2; @H1; @H; @__sat0; @__sat3; @__sat4; @z; @b; @b2; @b1; @NI; @Hx; @x; @r1; @q1; @r0; @q0; @r; @q; @__x7; @__x8; @__p4; @__sat4097; @__sat4098; @__sat4099; @e; @R; @_H; @a0; @BELOW; @INIMG; @o; @LOWIMG; @LO2; @M; @B; @INLAND; @HI; @NOTLO; @ABOVE; @A4096; @NOTIN; @NW; @AF; @CE; @FREE; @BIG; @NAL; @TOP; @POS; @AL; @n|] "#8?#Z$v#a$G#f$H$F#e###n$N#$$`$s#%$m#&$P#+#Z#5#*#0$4$L$h$x#'#-$.#<$V$\#(#)#A#x#/#1#;#B#u#7#8#6#3#.#4#D#=#>#@#2#9#:#,$=#G#?#E#C#M#`$$#I#H#k$1$f#K$l#F#S$'$9#N#L$p$q#P#O$u$v$w#Q$y#V#^#]#j#q#r#s#p#o#v#w#y#{#~$#$%$<$;$>$?$A$C$E$O$W$X$Z$[$Y#J$]$c$e$o$n$r$t#T#Y#U$z#h#_#g#b#z#c#m#d$J$I$D#i$)$_$6$($Q$@$&$*$+$,$-$8$7#}$/$3#l$M$i$K$B$T$R$a#t$:$5$^$d$k$j$0$b$g$2$S$U#|U$D%$E$$F%$G&$H%$I%$J$$K%$L'$M*$N+$O%$P%$Q%$R&$S%$T*$U'$V%$W%$X%$Y%$Z%$[$$\%$]%$^%$_&$`$$a%$b%$c%$d%$e&$f)$g)$h$$i&$j%$k)$l($m&$n)$o%$p%$q%$r%$s)$t&$u%$SO$#$#$#$#$#USh#USi#*$L(#H&C#E*'O%E#*)Q.#OUSjSS#$#$.$#$#$#$#$#?#(Q#&C#E)SO)#)#$#$#$#$#$#$#$#$#$#$#$#$#?#%#S,VSks#&s#&USlSSUSmSSWSn%$#GS2WSo$S3#&J#S:*s#.S&YSp#S3S2OQ.$S3USqS5#$#USrS5)>)#)#)#)#)#)#)#)#)#)#$#)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?###s#1)s#%)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?##s#S#'s#%#(s#Us#s&C#EUSsS5#s#X#.s#Ys#w%%#'%#'(#'+#<s#^s#|#Es#_#Es#~#E.k##$#k##&#*s$7S-<#H#E$#EH*s$;S6(#H#E#k##&#k##(#?s$F?s$BVSt$#%E%#E%VSu'&%E#k##%#k##'##E+WSv,+Lj##SP#j#$%##E*k##SP#k#$(#<S6s$?#ES6(S7s$A#E#k##s###k##&#5S's$E&Cs$FEUSZ#/S7s$H2s$I#.#+&CS7#k##'#6S7s$M%Es$N(SEs$O#E#%$s$Q'$#k##'#7SEs$T%s$UE(S>s$V%s$W##$E'$#k##'#8S>s$[/S@s$\&C#Ek##:#9S@s$_(S%s$`&C#S%k##>#=S%s$cm#S.#*s$vS;5#H&CHEUSZ#*s$zS</#H2H#(%H.$#&C'#k##)#6)H%EH*s%'SF(#H#E#%$H'$#k##(#7(H%HE*s%/SG(#H%H##$E'$#k##(#8(H*s%6S8/#H&C#Ek##?#9&H*s%;S/(#H&C#$k##s#$#=&Hm#S.#5s$ns%0/s$os%12s%2#.#s#z&Cs$r#k##s#L#6s$ts%6%s#~s%7's#s#k##s#I#7s$xs%:%s%;s$&#s$'E'$#k##s#G#8s$}s%?&C1Ek##s#Y#9s%$s%B&Cs$.s%%k##s#\#=s%'s%Em#S.#QEs%GNST#m##s#YUS,#QEHNST#m##s#:US?#*s%`SA(#H#E#%$H'$#US%-(SAs%U#E#%$s%W'$#VS8ILj#%s$$#k#%s$%s#}QEs$/NST#m##s$.US/#:S[:#:#:#:#:#:#:#:#:#:#;C#;C*;C,USwSOVSxC#;C2HC$#;CS[1C$#1C)#1C+#1C-#I#SI;C91C#)1C/#1C1#I#SIUSyS(>S($#>S(%#>S(+#>S(,#>S(-#USzS(US{CCCS,4C$O#CCS24C#S3&CCS34C#S3(4C%Q#4C(L#US|CUS}C)s&IBC#@CE+C$S)#,'GDDF#KUS~DBCs&PBCs&7+C$S)#,,GDDF#K--GDDF('#)s&U)#BC#+C#S).,2GDDF#K-3GDDF.-#+C2R1,5GDDF#K+C4R/,7GDDF#KE8GDDFS#39GDDF$#-:GDDF'4#E;GDDFSH+C5R:,=GDDF#K3>GDDF%#R?GDDF:SC>2DC#:+C:S)#,s##GDDF#K-s#$GDDF'>#@Cs%e$s&SBC#+C%S0#,s#)GDDF#K@Cs%H+C&S0#,s#,GDDF#K3s#-GDDF&#Es#.GDDFS-3s#/GDDF$#BCSODCs#)#+C#S0-,s#3GDDF#K@Cs&R+C#R',s#6GDDF#K+Cs#4Rs#/,s#8GDDF#K+Cs#2S)s#6,s#:GDDF#K+Cs#8S0-,s#<GDDF#K@Cs%@WT#C#s'#+C1R#,s#@GDDF#K3s#AGDDF'#-s#BGDDF*s#<#-s#CGDDF-s#=#-s#DGDDF0s#>#-s#EGDDF4s#?#-s#FGDDF9s#@#-s#GGDDFs#%s#A#-s#HGDDFs#,s#B#-s#IGDDFs#1s#C#-s#JGDDFs#9s#D#-s#KGDDFs#@s#E#VT$s#LFNJS:VT%IO&J#S:m$%#WT&CELXT'IO$#l#&*)#l#'s#Vs#U#l#(s#as#`#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#/S$#j#0S$#j#1S$#&CS,E&COQk##$#&CS2E&CS&Ek##$#%S3E%S&S,'#SHk##%#%S,S&'S-#&CS#Ek###S12SHS-.#S3&CS&#k##&##s&US##S#s&4'$#'#S'.S#S3##SH%s'9S&%ES-&CS-E#ES-%S-s%y'$#k##&#k##(#k##*#k##,#k##/#k##4#k##;#k##>#k##s###k##s#'#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#/S$#k#0S$#k#1S$#*s'uT((#H#E##$E/&HgIs&M%$#Hs'K'&SQS7SES>S2S%S4S9SASJSRl#2s#:)#l#3s$js&7#l#4s$ps$o#l#5QSP#l#6s$xs$t#l#7s%#s$z#l#8s%(s%:##ES9%S9s&@'$#m#&#l#9s%1s%2#l#:s%6s%4#l#;s%:s%8#l#<s%@s%<#l#8s%Es%B#l#=s%Ls%G#l#>s%Ns%O#l#?s%Us%Q#l#@s%[s%W#l#As%ds%]#l#7s%ms%f#l#Bs%xs%o#l#Cs%{s%|#l#Ds&%s%~#l#Es&*s&'#l#Fs&2s&,#l#6s&:s&4#l#Gs&Cs&<#l#Hs&Js&E#l#4s&Os&L#l#3s&Zs&T#l#Is&es&^#l#Js&ms&h#TS##GS#*s(C#&C#S#m#&#*s(FS?*s(GI#$#.%S-%%#'%#GS?*s(MS'##s(I.$I%s(K#'%#j#KC#*s(S)JCS?$I#OZT)s(-S6+LS2#0Ls(.&J#M0Os(0&JIMj#LJ#0Os(50Os(5O$#WT*Os(8s(7FJ)'I$#&J%MOLI&J#M&JOM&JLM'$#k##&#'%0OOL&J#Mk##%#''#&JQM'#,k##'#j##&#OQO&J#Mk##/#j###Lj##0#VT+LIK2.)$#j#MJ#j#NJ#k#MJ5k#NJ#0S,s(U0S,s(UWI$#L&J%M&J%M'$#l#O&#Il#G,*#l#Os#&s#%#l#Os#1s#/#j#Ps#<#j#Qs))#0Ls(a&J#M0Ls(b&J#M'%#k##s#C#k#Qs)0#5S@s(}/S%s(~2s)##.#s&~&CS%#k##s'=#6S%s)'(S=s)(#E#%$s)*'$#k##s'<#7S=s)-(S;s).%s)/##$E'$#k##s';#8S;s)3/S<s)4&C#Ek##s'N#9S<s)7(SFs)8&C#SFk##s'R#/SFs);(SGs)<5s&qs)=*s)OSB/#s)?2s)@#(%s)A.$#&C'#k##s'[#6)s)E*s)WSC(#s)G#E#%$s)I'$#k##s'[#7(s)L*s)^SK(#s)N%s)O##$E'$#k##s'[#8(s)S*s)eSD/#s)U&C#Ek##s'o#9&s)X*s)jS4(#s)Z&C#$k##s't#/&s)]*s)oS9(#s)_US2s&u#EI%Is)b'$#US's&y#ES#%S#s)f'$#US<s&}#ES>%S>s)j'$#;Cs&hHCs&\#1C#s&Y1C%s&U1Cs&a#1Cs&_s&]I#SIVSU%#VSU(#>S(#s&VCCQ4Cs&QQ#4C#Os&R4C#Ls&S@Cs)z+C#S)s&H,s&LGDDF#KRs&MGDDF#$s&*BC#SC(#DC#s&J+Cs&$S)#,s&SGDDF#K-s&TGDDF)s&N#+Cs&RRs&',s&VGDDF#K+C/S0s&),s&XGDDF#K-s&YGDDFs%}s&S#-s&ZGDDF&s&T#-s&[GDDF)s&U#l#&#s%ns%hl#'6s&^#l#(;s&i#j#)C#j#*C#j#+C#k##s(NS12s*7Q.#O&CL#k##&#%EL&CQE#s*=Qk##$#k##&#k##(#k#)C#k#*C#k#+C#*s*USJZIS2S,#S-SASLl#23%#l#6s#=s#:#l#Bs#Bs#?#l#>s#Gs#D#l#Rs#IC#l#Ss#LC#l#<s#Rs#N#l#8s#Xs#T#l#=s#`s#Z#l#>s#hs#b#l#?s#qs#j#l#Ts#sC#l#Us#uC#l#@s#zs#w#l#As$#s#|#l#7s$*s$%#l#Bs$1s$,#l#Cs$8s$3#l#Vs)CC#l#Ws(*C#l#Ds'vs't#l#Es'zs'x#l#Fs($s'|#l#6s()s(&#l#Gs(0s(+##s*_s%,Ps)8S*%s)9S*#S*s):A$#%s%*S*#S*s%+A$#*s*xS7LS5#S'j##%#%%S**s*|SELS5#S7P$P%%P#P&A$#*s+&S>%#P#P$A$#j###S1*s++S@%#PGP*s+.S=##I.$S%%I#'%#j#KC#<(H#E)#Es(sk##s)[#k##%#<S=s+(#ES=(S<s+*#E#k##s)h#k##&#5S;s+.2s+/s$Y.#(&CS<#k##s)I#6S<s+3#Es$Z%s$[s+5'$#k##s)G#7SFs+8%s+9s$[#s$\E'$#k##s)E#8SGs+=/S8s+>&C#Ek##s)X#9S8s+A(S/s+B&C#S/k##s)\#=S/s+Em#S.#5s$_H/s$YH2H#(s$[H.$#&Cs$]#k##s)C#6s$_H(s$YH#E#%$H'$#k##s)@#7s$^H(s$ZH%H##$E'$#k##s)>#8s$_H/s$[H&C#Ek##s)T#9s$^H*s+pSM(#H&C#$k##s)Y#=&Hm#S.#*s+vSV(#H#E#%$H'$#(SVs+j#E#%$s+l'$#:s(b:#;C#HCs(`#;Cs(k1C#s(a1C%#I#SI;Cs(m1Cs(hs$i1C$#VT,Cs+yWT-C#s(f;Cs(qHCs(k#;Cs(uHCs(ms(o1C#s(m1C%#1C'#1C*#I#SIVSU.#>S(#s(f>S($#>S(4#>S(5#>S(6#CCS&4Cs(eS##4C#Os(cCCS#4Cs(hS,#4Cs(dS#s(i4C$Q#4C'L#+Cs(ZS)s(4,s(cGDDF#K-s(dGDDFs(Ts(^#)s(ABC#+C#S)s(d,s(hGDDF#K-s(iGDDFs(Ys(c#+Cs(\Rs(g,s(kGDDF#K+Cs(^Rs(d,s(mGDDF#K3s(nGDDF#s(B-s(oGDDF&s(i#Es(pGDDFS?+Cs(iRs(c,s(rGDDF#K3s(sGDDF%#Rs(tGDDFs(dSCs(g1DC#s(n+Cs(IS)#,s(xGDDF#K-s(yGDDF's(s#BCs(nDCs%-#+Cs(uS)#,s(}GDDF#K-s(~GDDFs%3s(x#$s,T$#$#$#?#$SO$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#)SO$#)#$#$#$#$#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#@C:+Cs)#R#,s)RGDDF#KEs)SGDDFS63s)TGDDFs)-#Es)UGDDFS'3s)VGDDF$#+Cs)%Rs)P,s)XGDDF#K+Cs#=S)s)V,s)ZGDDF#K+Cs)SS)s)X,s)\GDDF#K+Cs)/S0/,s)^GDDF#KDCs)1s)X+C2R#,s)aGDDF#K3s)bGDDF&#-s)cGDDF)s)]#-s)dGDDFs%ls)^#-s)eGDDF-s)_#-s)fGDDF0s)`#-s)gGDDF3s)a#-s)hGDDFs%ns)b#-s)iGDDF9s)c#-s)jGDDFs#Js)d#-s)kGDDFs#Ps)e#-s)lGDDFs#Ws)f#-s)mGDDFs#\s)g#-s)nGDDFs#cs)h#-s)oGDDFs#is)i#l#&#s)&s(|l#'s#ns)r#l#(s#ws)}#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#XC#j#YC#j#/S$#j#0S$#j#1S$#j#ZS$#&CQLk##s(|#&CS3E&CSHEk##$#%S&E%S#S2'#S?k##%#%S2S#'S6#k##*S12S-S6.#S&&CS2#k##&#2s-cS6.#SH&CS&#k##s&2#%S3s#]#s-hS&#s,yS6'#S%'#S=%s-ZS-&CS'E%ES?&CS7E#S's#f.S'S7%s#h#'%#k##'#k##)#k##+#k##-#k##/#k##3#k##5#k##7#k##<#k##B#k##s#%#k##s#*#k##s#.#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#XC#k#YC#k#/S$#k#0S$#k#1S$#k#ZS$#*s.BS\(#H#E##$E/&H/SNs.6(SNs.7i#<Is,xs-%'&%$Hs-v#(SN)S?S6S'OSES<S/S9SLSRSQSVS]l#2s#E+#l#6s+Ds%+#l#7s+Ks%0#l#8s+Ps+b##s)7s$3.s)8SQ%s$5#'%#m#'#l#9s+Zs+[#l#:s+_s+]#l#;s+cs+a#l#<s+is+e#l#8s+ns+k#l#=s+us+p#l#>s%Bs%C#l#?s%Is%E#l#@s%Ns%K#l#As%Us%P#l#7s%\s%W#l#Bs%ds%^#l#Cs%fs%g#l#Ds%ls%i#l#Es%qs%n#l#Fs%ws%s#l#6s%}s%y#l#Gs&'s&##l#[s&.s&)#l#\s&4s&0#l#]s-8s-3#*s.hS%##P.$S@%P#'%#m#(#VS^s.nP*s.o#ULs+_+Cs+-S0s$>,s+1GDDF#K+Cs$@Rs*R,s+3GDDF#K3s+4GDDF%#l#&#s*Gs*Al#'s+@s+7#l#(s+Hs+B##Es$^%s$_s-7'$#l#2&#Il#4/s-8#l#Hs-4s-1#l#4s-?s-9##EP%Ps->'$#m#&#TP#JCPs&T:8#*s/*s&[#A#%$@'$#m#'#VS&s&`#0s&as.f&J#M0s&cs.g&J#M'%#j###S1#PI%IS*'$#j#KC#+Cs$cS0s$c,s+VGDDF#K)s'g)#$#$#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#@Cs$z+Cs$zR#,s+mGDDF#K3s+nGDDF:#l#&#s+%s*{l#'s+zs+q#l#(s,&s+|##s%<s%<%s%=s%&'$#l#2&#I#PP%PS*'$#m#&#JCPs#(#s#Ns#9#Ps#8%s#9S*'$#m#&#VS_s'9#FJs#7s)iLS:#&JS:MnJ#$#LS$I#%#SP#S1j#^J#FJS:#S.MIVSWS1Il#G$S1#l#_)(#j#`s#<#j#_s#?#V#LIj##s#?#j##s#B#Ks#Cs#As#?#Il#as#Fs#A#j#bs'J#U#Ij##s'Q##Ps'NCCO4C#Ls,B+Cs+gS0s+g,s,:GDDF#K+Cs+iRs%:,s,<GDDF#K3s,=GDDF%#-s,>GDDFs%Ds,8#l#&#s+Qs+Kl#'*s,A#l#(s,Rs,L#j#)C#j#*C#%s/bL#LL.LO%L#'%#k##'#k#)C#k#*C#WISNs$MSRl#2,$#l#6s-,s&o#l#7s-3s&t#l#8s-8s-J##s*{s*{%s*|s$F'$#m#&#l#9s-As-B#l#:s-Fs-D#l#;s-Js-H#l#<s-Ps-L#l#8s-Us-R#l#=s-\s-W#l#>s')s'*#l#?s'0s',#l#@s'5s'2#l#As'<s'7#l#7s'Cs'>#l#Bs'Ks'E#l#Cs'Ms'N#l#Ds'Ss'P#l#Es'Xs'U#l#Fs'^s'Z#l#6s'ds'`#l#Gs'js'f#l#[s'qs'l#l#\s'ws's#l#]s.{s.v#VS&S%#0S%s0*&J#M0S%s0+&J#M'%#0S=s0/&J#M0S=s00&J#M'%#j###S10S;s04&J#M0S<s07&J#M0SFs08&J#M0SGs0;<s..H#Es./(s)sH#E#k##s/.#k##&#<S8s0W#ES8(SBs0Y#E#k##s/;#k##&#5S/s0]/SBs0^2s0_#.#)&CSB#k##s.y#6SBs0c(SCs0d#E#%$s0f'$#k##s.x#7SCs0i(SKs0j%s0k##$E'$#k##s.w#8SKs0o/SDs0p&C#Ek##s/.#9SDs0s(S4s0t&C#S4k##s/2#=S4s0wm#S.#5s'xH/s.-H2H#.#s..&Cs.0#k##s.t#6s.2H*s15SL(#H#E#%$H'$#k##s.r#7(H*s1<SX(#H%H##$E'$#k##s.q#8(H/s)LH&C#Ek##s/+#9s)OH*s1GSR(#H&C#$k##s/0#=&Hm#S.#*s1MS`(#H#E#%$H'$#(S`s1A#E#%$s1C'$#4Cs$<Ls*-+Cs-DS0s-k,s-sGDDF#K+Cs-mRs-l,s-uGDDF#K3s-vGDDF%#-s-wGDDF$s-q#-s-xGDDF's-r#l#&#s-/s-)l#'+s-{#l#(s.0s.*#j#)C#j#*C#j#+C##IL%OQ#OQ%QS,'$#k##&#k##(#k#)C#k#*C#k#+C#*s1nSYYIS*#PS4SAl#2/%#l#6s.j>#l#7s.qs###l#8s.vs/,#*s1tSa#P#%$S*'$#m#'#l#9s/$s/%#l#:s/)s/'#l#;s/-s/+#l#<s/3s//#l#8s/8s/5#l#=s/?s/:#l#>s#5s#6#l#?s#<s#8#l#@s#As#>#l#As#Is#C#l#7s#Qs#K#l#Bs#Xs#S#l#Cs#Zs#[#l#Ds#`s#]#l#Es#es#b#l#Fs#ls#g#l#6s#ss#n#l#Gs#zs#u#l#[s$%s#|#l#\s$,s$'#l#]s0^s0Y#VS_SG#FJs$0s,7LS:#l#_#s%,s%'j#`s$3#j#_s$6#V#LIj##s$:#j##s$A#Ks$Bs$@s$>#Il#as$Js$E#j#cs%##U#Ij##s)t#Ms)vs)us)ss%'#Il#ds)|s)y#VSWs)~#j#es*%#U#Ij##s*-##S*s*+.s*(S7VT.#N#$N%N%A$#.s*'SE##N%N$A$#LS5s*&S>j##$#.s*(S>##NVSbs&IS@WScS5s&JS@#S*s&K#s&JNXSd$#QIWT/'&#j#f)#U#Ij##1#%N-Ps&SS+%s&TS+#S+s&UA$#%s*5S+#S+s*6A$#LS5s0LS=j##$#%s0NS+LS5s0KS;Ps0LN%s0MN#Ns0NA$#%s0GN#Ns0HA$#j###S1%s0CNGN#s09I.s0:S8%I#'%#j#KC#<s0>H#Es0?(s,$H#E#k##s1C#k##&#<S/s2l#ES/k##s1Ns$gk##$#5SBs2p/SCs2q2s2r#.#s$m&CSC#k##s10#6SCs2v#Es$k%s$ls2x'$#k##s1.#7SKs2{(SDs2|%s2}##$E'$#k##s1-#8SDs3%/S4s3&&C#Ek##s1@#9S4s3)(S9s3*&C#S9k##s1D#=S9s3-m#S.#5s0>H/s$jH2H#.#s$k&Cs$m#k##s1*#6s$oH#Es$h%s$iH'$#k##s1&#7s$mH(s+UH%H##$E'$#k##s1$#8s+ZH/s$iH&C#Ek##s1:#9s$lH*s3VSQ(#H&C#$k##s1?#=&Hm#S.#*s3\Se(#H#E#%$H'$#(Ses3P#E#%$s3R'$#+Cs/RRs/y,s0%GDDF#KDCs/Ts/z+Cs/|R#,s0(GDDF#K3s0)GDDFs$p#-s0*GDDF$s0$#-s0+GDDF(s0%#l#&#s/>s/8l#'s$vs0.#l#(s0?s09#j#)C#j#*C#j#+C#%IL.LQ%O#.OS,%Q#'s$p#k##&#k##)#k#)C#k#*C#k#+C#*s3~T0YISYN#S/S9l#20%#l#6s0z?#l#7s1%s#$#l#8s1*s1<##s%9N.s%:Sa%N#'%#m#'#l#9s14s15#l#:s19s17#l#;s1=s1;#l#<s1Cs1?#l#8s1Hs1E#l#=s1Os1J#l#>s#6s#7#l#?s#=s#9#l#@s#Bs#?#l#As#Is#D#l#7s#Os#K#l#Bs#Vs#Q#l#Cs#Xs#Y#l#Ds#^s#[#l#Es#cs#`#l#Fs#js#e#l#6s#ps#l#l#Gs#ws#r#l#[s#|s#y#l#\s$'s#~#l#]s2ns2i#VS^s4BN*s4C#$s3`$#$#$#$#$#$#$#$#$#$#$#?#@C#+Cs0jS0#,s0nGDDF#K+C%Rs03,s0pGDDF#K3s0qGDDF%#l#&#s0(s/~l#'s0}s0t#l#(s1)s1###E,%-s2t'$#l#2&#Il#4s(Ls2u#l#Hs2qs2n#l#4s2|s2v##EN%Ns2{'$#m#&#TN#JCNs$Ns#'s#%#*s4gs$T#s24#.s25SG%%#'%#m#(#VS's$Z#0s$[s4H&J#M0s$]s4I&J#M'%#j###S1#NI%IS+'$#j#KC#+Cs#)S0s#),s18GDDF#K)s*t)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#@C#+Cs#LR#,s1[GDDF#K3s1\GDDFs#&#l#&#s0os0il#'s1hs1_#l#(s1ps1j##s#Ss#S%s#T+'$#l#2&#I#NN%NS+'$#m#&#JCNs#4#s#hs#F#Ns#E%s#FS+'$#m#&#VSfs%?#FJs#As/WIS:#l#g#s(Ls(Gj#gs#B#j#`s#E#V#LIj##s#E#j##s#H#Ks#Is#Gs#E#Il#as#Ls#G#j#hs%J#U#Ij##s%P##Ns32WISYs$@S\l#2s(;s(3#l#6s2[s$\#l#7s2bs$a#l#8s2gs2y##s&vs&v%s&ws$?'$#m#&#l#9s2ps2q#l#:s2us2s#l#;s2ys2w#l#<s3#s2{#l#8s3(s3%#l#=s3/s3*#l#>s$rs$s#l#?s$ys$u#l#@s$~s${#l#As%)s%$#l#7s%/s%+#l#Bs%6s%1#l#Cs%8s%9#l#Ds%>s%;#l#Es%Cs%@#l#Fs%Js%E#l#6s%Ps%L#l#Gs%Ws%R#l#[s%\s%Y#l#\s%cs%^#l#]s4Ns4I#VS'S8#0S8s5Y&J#M0S8s5Z&J#M'%#0S/s5^&J#M0S/s5_&J#M'%#j###S10SBs5c&J#M0SCs5f&J#M0SKs5g&J#M0SDs5i<s/)H#Es/*#Es-$k##s4\#k##%#<S4s6)#ES4(SMs6+#E#k##s4i#k##&#5S9s6//SMs602s61#.#)&CSM#k##s4K#6SMs65k##s4Fs3<7SAs67(SLs68%s69##$E'$#k##s4E#8SLs6=/SXs6>&C#Ek##s4X#9SXs6A(SJs6B&C#SJk##s4\#=SJs6Em#S.#5s%`H2Hs1>.#s1B&Cs1D#k##s4A#6s1FHk##s4:s-B7s-GH*s6`S](#H%H##$E'$#k##s49#8(H*s6gSN/#H&C#Ek##s4P#9&H&Cs++s+,k##s4S#=s+.Hm#S.#*s6pSg(#H#E#%$H'$#(Sgs6d#E#%$s6f'$#*s6yT1YIS+#NS4SAl#2s'vs'l#l#6s3u&#l#7s3|+#l#8s4%s47#*s7#T2#N#%$S+'$#m#'#l#9s4/s40#l#:s44s42#l#;s48s46#l#<s4>s4:#l#8s4Cs4@#l#=s4Js4E#l#>=>#l#?B@#l#@s#(s#$#l#As#0s#*#l#7s#3s#2#l#Bs#9s#5#l#Cs#;s#<#l#Ds#As#>#l#Es#Fs#C#l#Fs#Ms#H#l#6s#Ps#O#l#Gs#Ws#R#l#[s#^s#Y#l#\s#ds#`#l#]s5is5d#VSfSD#FJs#hs1BIS:#l#g#s*7s*2j#gs#k#j#`s#n#V#LIj##s#r#j##s#y#Ks#zs#xs#v#Il#as$&s#}#j#hs$F#U#Ij##s':#Ms'<s';s'9s$J#Il#ds'As'>#VSWs'C#j#is'E#U#Ij##s'L##S+s58VSbs55S;WScS5s56S;#S+s57.s58S;##s7&XSd%#IS'WT3('#j#j*#U#Ij##s'V#Ms'Xs'Ws'T.#Il#ds']s'Z#j#ks'_#U#Ij##s'p#Ms'rs'qs'ns'c#Il#ds'xs'u#j#ls'{#U#Ij##s/L#Ms/Ns/Ms/Is(##Il#ds/Ss/P#l#ms/Vs/U#l#ns1@s19#l#os2&s2'#l#ps79s6<#l#qs7>s7;#j#rs7A#j#ss7I#j#ts7[#j#us7e#j#vs7j#j#ws7m#j#xC#j#%s7r##"). Qed.
  End Derived.

  (* [comment removed for export] *)
  Lemma akernel_mat : forall mo mo', akernel mo -> same_but_materialized mo mo' -> akernel mo'.
  Proof. intros mo mo' AK SB. unfold akernel, akernel_resx in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact AK. Qed.
  Lemma AMODELX_mat : forall mo mo', AMODELX mo -> same_but_materialized mo mo' -> AMODELX mo'.
  Proof. intros mo mo' [A K] SB. split; [eapply AMODEL_mat; eassumption| eapply akernel_mat; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma awin_vis_wmono : forall m m', awin_vis m -> wmono bsegs m m' -> awin_vis m'.
  Proof. intros m m' V W x Hx. apply W. apply V. exact Hx. Qed.
End X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_cov (d : depot) (mo : Model) : Prop :=
  forall x : word, (d_nb d <= bv_unsigned x < d_nb d + 16 * 65536 \/ d_sb d <= bv_unsigned x < d_sb d + 8 * 262144) ->
                   in_rangesb x (vm_maps (m_vmmaps mo)) = true.
Lemma depot_cov_mat : forall d mo mo', depot_cov d mo -> same_but_materialized mo mo' -> depot_cov d mo'.
Proof. intros d mo mo' C SB. unfold depot_cov in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact C. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGAP (n : Z) (mo : Model) : Prop :=
  let h := m_vmmaps mo in let E := vm_reserved h ++ vm_maps h in
     AHI_LO + cost n AHI_LO E + n <= alloc_top h.
(* [comment removed for export] *)

Lemma AGAP_mat : forall n mo mo', AGAP n mo -> same_but_materialized mo mo' -> AGAP n mo'.
Proof. intros n mo mo' G SB. unfold AGAP in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact G. Qed.
Lemma AGAP_mono : forall n n' mo, n <= n' -> 0 < n -> AGAP n' mo -> AGAP n mo.
Proof.
  intros n n' mo LE POS G2. unfold AGAP in *.
  pose proof (cost_mono_n n n' AHI_LO (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) LE). lia.
Qed.

(* [comment removed for export] *)
Lemma cost_high_bound : forall n E, 0 < n -> cost n AHI_LO E <= hlen E + hcnt E * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil, hlen_nil, hcnt_nil; lia|].
  rewrite cost_cons, hlen_cons, hcnt_cons. unfold ecost, ehigh.
  destruct (Z.ltb_spec AHI_LO (KInv.ehi e)) as [H|H].
  - unfold KInv.ehi, KInv.elo in *. pose proof (bv_unsigned_in_range _ (fst e)). lia.
  - lia.
Qed.
(* #38 RESERVED-CEILING-CLASS: the extra reserved intervals are ABOVE the gate,
   so they do not vanish from the ledger - they charge.  [ecost_le] bounds each
   entry by its own size plus [n + 4096], so a list of them costs at most its
   total size plus its length times that.  Stated for any [E]; applied to the
   [rx] half, where [akernel_resx] bounds both. *)
Lemma cost_le_sizes : forall n E, 0 < n ->
  cost n AHI_LO E <= zsum (map (fun e => bv_unsigned (snd e)) E) + Z.of_nat (length E) * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil; cbn; lia|].
  rewrite cost_cons. cbn [map length zsum]. unfold ecost.
  pose proof (bv_unsigned_in_range 64 (snd e)). unfold KInv.ehi, KInv.elo.
  rewrite Nat2Z.inj_succ.
  destruct (AHI_LO <? bv_unsigned (fst e) + bv_unsigned (snd e)); lia.
Qed.

(* #38 RESERVED-CEILING-CLASS: ROOM grows by exactly what the launch's extra
   reserved intervals cost the ledger - at most two entries ([akernel_resx]'s
   count bound) of at most 81920 bytes together (its size bound), each
   charging [n + 4096].  This is the (b) obligation of the akernel split and
   it is discharged by the caller. *)
Theorem AGAP_of_akernel : forall s mo n, akernel s mo -> 0 < n ->
  AHI_LO + (AHL0 + zsum (map sc_map_size (hsec (a_st s)))) + (AHC0 + zlen (hsec (a_st s))) * (n + 4096) + n
    + (81920 + 2 * (n + 4096)) <= hceil ->
  AGAP n mo.
Proof.
  intros s mo n AK Hn ROOM. unfold AGAP.
  (* #38: akernel is now akernel_pre /\ akernel_resx, so the pre-chain sits one
     level in.  K1 is the SEGMENT half only; see R0 below. *)
  pose proof AK as ((K1 & (_ & K2) & _) & RX). pose proof (ak_hcov s mo AK) as (C1 & C2 & _).
  rewrite K2, cost_app.
  destruct RX as [rx [Hrx [Hok [Hcnt Hsz]]]].
  (* the IMAGE's reservations still cost nothing: K1 puts every one of them at or
     below AIMG_TOP, hence below the AHI_LO gate. *)
  assert (R0seg : cost n AHI_LO (segments_reserved bsegs) = 0).
  { assert (L : Forall (fun e => KInv.ehi e <= AHI_LO) (segments_reserved bsegs)).
    { apply Forall_forall. intros e He. specialize (K1 e He). unfold KInv.ehi, AHI_LO, AIMG_TOP in *. lia. }
    clear - L Hn. induction L as [|e E He L IH]; [apply cost_nil|]. rewrite cost_cons, IH, (ecost_below n AHI_LO e He). reflexivity. }
  (* the LAUNCH's extra intervals do charge, and this is the whole repair: the old
     `= 0` was true of the image's list and false of the list the model builds. *)
  assert (R0 : cost n AHI_LO (vm_reserved (m_vmmaps mo)) <= 81920 + 2 * (n + 4096)).
  { rewrite Hrx, cost_app, R0seg. pose proof (cost_le_sizes n rx Hn) as CLS.
    (* the count bound enters as a PRODUCT with (n + 4096), which is nonlinear in
       two variables and beyond lia; discharge it the same way the hcnt bound is
       discharged below, with Z.mul_le_mono_nonneg_r. *)
    assert (ML : Z.of_nat (length rx) * (n + 4096) <= 2 * (n + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  pose proof (cost_high_bound n (vm_maps (m_vmmaps mo)) Hn) as CB.
  pose proof (hcnt_nonneg (vm_maps (m_vmmaps mo))). pose proof (hlen_nonneg (vm_maps (m_vmmaps mo))).
  assert (M : hcnt (vm_maps (m_vmmaps mo)) * (n + 4096) <= (AHC0 + zlen (hsec (a_st s))) * (n + 4096)) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

End HCW.

(* [comment removed for export] *)
Ltac acb ::=
  let K := fresh "ACEILB" in
  pose proof (conj aceil_facts sh_ceiling_range
              : (0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096)
                /\ (0x10006fef8000 <= sh aceil <= 0x10007fef8000)) as K.

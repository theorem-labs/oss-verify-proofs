(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
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
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import GapGrid.
From OSSVerify.Proofs.boost_beast.http_request.lib Require LazyNodes.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR Gap04.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsDepotInv SecGap.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ALIBCPGSZ : Z := 0x67d770.   (* [comment removed for export] *)
Definition AGOT_SSP  : Z := 0x11c130.   (* [comment removed for export] *)
Definition ASSPGUARD : Z := 0x67d4f0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOWSH_SZ : Z := 0x10000000.

(* [comment removed for export] *)
Definition AHSB : Z := 0x2008fff7000.
Lemma AHSB_eq : AHSB = sh AHI_LO.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sh_ceiling_range : 0x10006fef8000 <= sh aceil <= 0x10007fef8000.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil_facts); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__arith; @H0; @H5; @r0; @q0; @H8; @H7; @H6; @H4; @r; @q; @H3; @H2; @H1; @H; @ACEILB|] "#'e#5#}#B#j#k#i#D#q#'###p#w#?#(#T#%#&#9#+#$#C#H#I#K#L#M#N#O#R#Q#\#^#]#`#S#e#l#u#|#}#5$$#8#@#E#0#Y#X#_#U#a#b#d#f#h#r#x#y#*#z#~$##{#)#-#.#,#3#4$%#=#>#;#:#A#F#n#m#V#[#Z#o#<#G#g#s#v#J#P#W#c#t9#g$#h$#i%#j%#k&#l%#m'#n*#o&#p$#q%#r%#s$#t%#u+#v%#w*#x%#y%#z&#{'#|&US;R$M$#$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################/#US<R%$#$s#&$#$#$#$#$#$#$#$###############################################/#%s#%#&s#%##M######################/#VS%s#4#'C#GUS=R%s#7#0s#8'(%#&%#&(#&8#m#s#m#/7VS&s#?#'C$GUS'#VS(s#B&4'#VS%s#D(0$#'Cs#F#k##(#VS)s#H,(G-%G(()/&$#k##&#VS*s#N2(3G(4.%/G&$#k##&#VS+s#T8'C5Gk##8#VS,s#W;'C6s#Xk##;#VS&s#Zs#)'Cs#*GUS'#VS(s#]s#,4s#-#0#s#-'Cs#`#k##'#VS)s#bs#1(Gs#2%Gs#2(s#3s#4&$#k##&#VS*s#hs#7(s#8G(s#9s#8%s#9G&$#k##&#VS+s#ns#='C4Gk##7#VS,s#qs#@'Cs#@s#rk##:#VS-Gs#C5S.#m##5UN#%GJ(Js#H&$#VS-Gs#?5S.#m##s#6US>#%GS#(S#s#D&$#US?MVS@C#,S/,#,#,#,#,#,#-C#6C+#-C'-C)-C-6C/#+C%#+C'#+C)#VSACs#X-CS/WS0C$#,/-C#-C6WS0C(-+C$#+C0#+C'#+C*#VS1#S2VSB/#-C:6CA6+C,/+C$#+C&#VS1#S2USCOWS3O$#WS3O+#USDOUSECVS4CN7C$P#VS4CI7C#Q&7C%S$#USFCUSGC.Cs$&.CG)C$K#*&FDDE#HZS5'FDDE#USHD2Cs$8#s%12C#WS6C+#2Cs%48C$#)C(K#*0FDDE#H11FDDE,+#$s$A2C#)C2L#*5FDDE#H.Cs$.)C&SI#*8FDDE#H39FDDE&#)C&K8*;FDDE#HZS5<FDDE#2CMWS6C*#8C#.)C9K#*AFDDE#H1BFDDE(<#.Cs$x)C#L=*s#%FDDE#H.Cs$X)C@L#*s#(FDDE#H3s#)FDDE&#)C?Ks#(*s#+FDDE#HZSJs#,FDDESK3s#-FDDE$#3s#.FDDE'##s$S$#$###$#$#$#$#$#$#$###$#$#$#$#$###############################/#.C##s%G############################/#.C#8C#s#G)C5L#*s#dFDDE#H$s#6$#$#$#$#$#$#$###$#$#$#$#$###############################/#.C#)Cs#$L#*s$)FDDE#H3s$*FDDEs#$#1s$+FDDEs#[s$%#1s$,FDDEs#hs$&#1s$-FDDEs#rs$'#1s$.FDDEs#{s$(#VSLs$/E5S7S8VSMJP'S7#S8m$%#WSNCGS$XSOJP$#l#$*)#l#%s$9s$8#l#&s$As$@#j#'C#j#(C#j#)C#j#*C#j#+C#j#,S9#k##s%:S:4s%cN0#Q'CP#k##&#%GI(Is%]&$#k##s%]S:4s%`Q0#SP'CI#k##&#%s&EI%Is&#&$#'CNG&#S#&%#0s#PI%s#b#%$s#0&$#k##'#k##.#k##4#k##8#k#'C#k#(C#k#)C#k#*C#k#+C#k#,S9#^Js%|ISQQs&XSRSSS$STSUl#-s#%$#l#.s%:s%7#l#/s%Bs%?#l#0s&*C#l#1s%^C#l#2s%Ks%I#l#3s%Os%M#l#4s%Vs%Q#l#/s%]s%X#l#5s%fs%_#l#6s%}C#l#7s&$C#l#8s%ls%j#l#9s%ps%n#l#:s%ws%r#l#.s%~s%y#l#;s&,s&$#USVs&j%s$&#%$s#P&$#m#'#l#<s&4s&5##"). Qed.
Lemma sh_ceiling_lt_AHI_LO : sh aceil < AHI_LO.
Proof. pose proof sh_ceiling_range. unfold AHI_LO. lia. Qed.

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
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.KInv.ehi); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt); constr:(@Stdlib.Lists.List.filter); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.cons); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt_map_remove_le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_remove); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt_high_cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.bv_eqb_refl); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.ehigh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt_cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt_cons_ge); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Numbers.BinNums.xI)|] [|@p; @IN; @E; @e0; @b; @z; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @L; @H0; @__x3; @IH; @H; @e|] "#&f#1#x#Q###]#$#N#&#^#%#\#'#*#+#)#b#c#m#(#,#P#9#U#4#G#T#W#g#q#p#r#w#x#u#7#6#5#=#;#<#F#I#H#M#-#S#X#Y#[#d#h#j#k#l#i#.#n#o#/#0#s#t#y#z#K#>#@#?#E#J#B#D#C#A#R#:#`#_#8#Z#O#f#e#L#V#a#v8#c$#d%#e%#f&#g$#h&#i&#j&#k%#l&#m'#n*#o$#p+#q)#r&#s&#t&#u'#v%#w%/S&/#/#/#/#/#US3#US4#VS5##US(#,$DFUS6FVS7S8#,'HD())D(**S#),$#'#j#$,#*-#F###FUS9S&%$#$&#k#%.#j#&3#US)5,6J#*7-$###&%#,$%#j##S:#VS;#Dj#%*#,?LD(AAO)s##;#'#j#$s###*s#$#F##$#7k#%*#&s#(JF,s#)S##4s#*HO,s#+OJVS<$#(s#.s#.L(s#/s#/M)s#1$#'#(s#2s#2N)s#4s#,#'#j#$s#4#*s#5#H&s#6L#nG#$##s#6)#%###$##&s#9LH##%#s#-$&#j##3#4s#>LM(s#@s#@S$)s#Bs#:#'#(s#Cs#CS=)s#Es#=#'#j#$s#E#*s#F#S#&s#GD#nG#$##s#G)#%###$##&s#JDS###%#s#>$&#j#'s#N#'D&s#PS$,nG#$##s#P$#%###-##&s#SS$S###%#s#G$&#j#(G##L+s#K##6%Ds#M$$#j#)C#VS>Ls#/VS*Ls#0##$#+US)S'US(S'VS+CJUS?C5C$F#US@CUSAC6CS&6Cs#r-C$P#.&KEEI#QUSBEVS,Cs#`2C#'3C#$-C*P#.,KEEI#Q0-KEEI)(#VSC.IVSDGS%VSEDJ4G#S%m$%#WSFCRFXSGDJ$#l#**)#l#+87#l#,=<#j#-C#j#.C#$DF+s#sJ%#s#t$F#k##&#k#-C#k#.C##O(s$-s$-SH)s$/s$'#'#j#$s$/#*s$0#O##WD)#Fl#/2+#l#0s#4s#1#&s$5NL##WSINLO1Cs#=s#9&$#'S%j#$s$:s#W*s$;#L&s$<N#nG#$##s$<&#%###$##%+s$1$$#m#+#)s$Ds#os#oVSJs$Es#p1GS%s#K%$#1s$ENs#U#S#Dj#1s#f#U#Dj##s#|#,s$IMHUHD#2%s#Rs$>$$#)s$Ps$0s#m'#(s$Qs$QSK)s$Ss$K#'#j#$s$S#*s$T#M&s$UN#nG#$##s$UD#%###$##&s$XNM##%#s$L$&#j#(G#US-MnG#$##C##%#s$P#R+#s#0$D(j#)C#+&s#9US-NnG#$##C##%#s$V#R#3+$#$#s#jj#)C#nG#$##CD#%#s$[#R(s$ks$kSL)s$ms$e#'#j#$s$m#*s$n#N##+)##N++#%#s$e$&#j#(G#3Cs#js#f-Cs#lP#.s#nKEEI#Q2Cs#is#n-C#Ps#h.s#qKEEI#Q0s#rKEEI&s#m#l#*#s#gs#al#+s#vs#u#l#,s#{s#z#j#-C#j#.C#%Fs$t$D#+s$vF$#s#ak##%#k#-C#k#.C#WD:<Hl#/+$#VS,CR2C#s$%2C$s$%3C#s#~-C%P#.s$*KEEI#Q0s$+KEEI;s$&#l#*#s#|s#vl#+s$/s$.#l#,s$4s$3#j#-C#j#.C#+RF+RJ%#s%/$%#k##:#k#-C#k#.C#l#/*#7XS.s#,7#Dl#(s#EG#&s%EMO##VS/MO1Cs#Ds#>&$#&s%IMs#w##VS/Ms#y1Cs#Ks#I&$#VSMMO$s$%*US0S1US0#7C#7C%7CS1WS2C$#WS2C&#VSN#SO&S'#s$SVS+CH5C#Hs$R5Cs$TF#USPs%c6C#-C#Ps$Q.s$TKEEI#Q3C%s$O-Cs$UP#.s$WKEEI#Q0s$XKEEI#s$Ss#H0s$YKEEI's$T#l#*#s$Ns$Hl#+-s$\#l#,1s$a#j#-C#j#.C#j#2C#$JF%Hs%]$F#$J$k##$#k##'#k#-C#k#.C#k#2C#&s%sS$N##YDs#b#s#dFHl#//&#l#1s#,s#+#XS.s#zs#.#Dl#(s$,G#l#3s$2s$/#j#%s$4#U#Dj##s%T#ZSQs%Vs%Us%Cs$8#D)s&%s%ys%S'#j#$s&%#&s&&HJ*s&'$####%%#s%x$%#m#,#j#%s%b#j#3s%e#j#&s&.#j#'s&0#ZSRs&1s%{s%q#HF(s&3s&3JVS*H####H%#s&($%#m#)#j#4s&5#j#%s&8#j#5s&;#j#&s&;##"). Qed.
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
    forall x : word, in_rangesb x (a_S s) = true -> wview asegs m x <> None.

  (* [comment removed for export] *)
  Definition flagsx_rep (m : mem) : Prop :=
       rw_cells asegs m ALIBCPGSZ [C8 (wz 4096)]
    /\ rw_cells asegs m AGOT_SSP [C8 (wz ASSPGUARD)]
    /\ (exists g : word, rw_cells asegs m ASSPGUARD [C8 g])
    /\ rw_cells asegs m (ACFLAGS + 219) [C1 (b8 1)]
    /\ (exists b : byte, rw_cells asegs m (ACFLAGS + 244) [C1 b]).

  Definition AREPX (m : mem) : Prop := AREP s m /\ awin_vis m /\ flagsx_rep m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition akernel (mo : Model) : Prop :=
    let h := m_vmmaps mo in
       (* [comment removed for export] *)
       (forall e, In e (vm_reserved h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= AIMG_TOP)
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
          region_free (vm_noaccess h) a n = true).

  Definition AMODELX (mo : Model) : Prop := AMODEL s mo /\ akernel mo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Derived.
    Variable mo : Model.
    Hypothesis AK : akernel mo.
    Let h := m_vmmaps mo.

    Lemma ak_resf : forall a k : word, AIMG_TOP <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha. destruct AK as (K1 & _). apply region_free_introZ. intros e sz He.
      specialize (K1 (e, sz) He). cbn [fst snd] in K1. pose proof (bv_unsigned_in_range _ k). right. lia.
    Qed.
    Lemma ak_resf_hi : forall a k : word, AHI_LO <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof. intros a k Ha. apply ak_resf. unfold AHI_LO, AIMG_TOP in *. lia. Qed.
    Lemma ak_resf_sh : forall a k : word, sh AHI_LO <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof. intros a k Ha. apply ak_resf. unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *. lia. Qed.
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
    Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(AK); constr:(@Corelib.Init.Datatypes.prod); constr:(@Stdlib.Lists.List.In); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(mo); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_TOP); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(HCEIL); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_thr); constr:(s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPageSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_ctx); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_sb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kSpaceSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_pa); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPtrArrayReserve); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_fsb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.AFS_SIZE); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kNumClasses); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.RB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kRegionSize); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_Zr); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.a_L); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(st); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_size); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hcnt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.AHC0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.zlen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hsec); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.hlen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.AHL0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecGap.zsum); constr:(@Corelib.Lists.ListDef.map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.ASECMAX); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@kc__4); constr:(h); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.conj)|] [|@e; @x; @c; @n; @a; @sc; @H0; @H; @_H1; @K3; @_H0; @_H; @Hx|] "#&P#4#}#$#_###b#T#%#m#>#L#&#J#c#'#q#Q#U#a#e#j#o#p#s#t#1#:#8#7#B#E#F#D#H#I#M#N#O#P#S#V#X#W#Y#Z#[#\#]#^#d#f#(#h#i#k#l#n#r#u#v#y#x#w#z#}#|#{#~$#$%#*#.#2#3$($&#0#A#;#<#@#K#G#R#9#?#`$'#=#C#g$$1#o%#p%#q%#r&#s%#t%#u$#v%#w%#x&#y$#z&#{&#|()S+)#)#)#)#)#US,#US-#-J*%E$$#%$J#$#VS.((US/S0US1#.%E#WS2,,C*.#WS3..C*0#'%#$#Mk##)#k#$-#US4-&K#S5US6/US7Q&K$##&#US8G$#9'$R%;##%#US9G$#>US:s#()#)#)#)#)#US;#'+#%s#'##,#US<G$#s#*'$S='#R%s#-##&#US>G$#s#0'$S?%s#2##%#US@G$#s#5'$SA%s#7##%#(#s#6()#(/#(6#(s###US#s#9+C#&D#Fk##&#k#%s#D#$NE%ESB#$#VS$GC*s#JL$$#*s#LO'#%VS$GH'#SC$%#/2SDO&D#Fk##%#k##+#k##/#k#&K#k#'s#V#k#(s#W#*s#YC$s#*#*s#[H'#%$#s#+/?LH&D#Fk##%#k##)#k#'s#a#k#(s#b#$s#b-%N.'>-USEQ-#$%#/s#+OL&D#Fk##%#k##*#k##,#k#'s#n#k#(s#o#USFG+C#&D#S%k##s#E#k#%s#t#k##s#B%k#%s#v#%s#u2#s#u#&D*FUSGG+C#&D#F#&#k##(#k#%s$##USHs#y+E#&D#Fk###s#Ck#%s$(#USIS&.IC#US'H$#s#2UPH'%#%s#5##&#+H/&D#S%k##%#k##,#k#%s$5#k#)I#.IE0US'CUS(#UPCUS(#XSJs$<s$<%#.s$7#s#[k##)#k#)I#$S)s$>##s$=k###s#^k#%s$C#-M$#s#K-S)$s#@#k###s#<k##s#C#k##'#k#'s$K#k#(s$L#$+s$K%s$L*#$#k###s#1k#%s$Q#$SKs$P%s$QM#$#+Cs$M&D#Fk##%#k#%s$X#USLs#wUSMS&VSNI#'SO#$&#USPs#|XSQIKP'USR#'SS#$&#$Ns#+$s#,ST#$#k##s#1#k#)I##(##.#'s#ps$h$#s#b#s#g#$%s#)#s#+#(%#WSUs#NHC&D#Fk##%#k#'s$s#k#(s$t##.##@##s#(##s#.##s#8##s#=##s#G##s#V##s#\##s#f##s#i##s#o##s#}##s$-##s$A##s$m##s$t#US#SV+L#&D#Fj##&#+SW&&D#Fj##*#+SX)&D#Fj##.#*s%5S*$s%4#%$J$s${%%&s$z#$#$s$y(%)s$q#$#$s$p+%,s$n#$#$s$m.%/s$l#$#$s$k1%2s$j#$##32($#((#(,#(0#(4#*s%MSY%#J*s%OSZ$s%7#%$s%6#$#$s%5&%'s%-#$#$s%,)%*s%*#$#$s%),%-s%(#$#$s%'/%0s%&#$#$s%]2%3J#$#(&#(*#(.#(2#XS[)(CE,+(#,/(#,3(#,7(#,;(#j#*@#j#+s#9#YS\s#:s#9s#$#S]VCS*#j#,s#K#j#-s%.#V#CEj##s#N#j##s%1#0s%2s#Ps#C#Ej#+s#P#j#.s%_#V#CEj##s#S#j##s%b#0s%cs#Us#L#Ej#+s#U#j#/s%k#V#CEj##s#X#j##s%n#0s%os#Zs#U#El#(S^s#Z#j#0s%}#j#%s&'##"). Qed.
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
    Proof. intros a n [[H1 H2]|[H1 H2]]; apply ak_resf; unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *; lia. Qed.
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
      ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(h); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.X.Derived.ak_grant_below_aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil_facts); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.region_free_not_in); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb_app); constr:(@kc__4); constr:(@Stdlib.Bool.Bool.orb_false_iff); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.ZArith.BinInt.Z.lt_ge_cases); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_TOP); constr:(@Corelib.Init.Logic.or); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp); constr:(@Corelib.Init.Logic.False_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_LO); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.X.Derived.ak_imgr); constr:(@Stdlib.ZArith.BinInt.Z.le_gt_cases); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ALOWSH_LO); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp_hi); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRepX.HCW.X.Derived.ak_shland); constr:(@Corelib.Init.Logic.or_intror)|] [|@Ha; @a; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__arith; @__sat3; @__sat2; @zh; @H0; @H6; @H12; @H16; @H15; @H14; @H13; @H11; @H10; @H9; @H8; @H7; @H5; @H4; @H3; @H2; @H1; @H; @__sat0; @__sat1; @__sat4; @z; @b; @b2; @b1; @NI; @Hx; @x; @r1; @q1; @r0; @q0; @r; @q; @__x7; @__x8; @__p4; @__sat4097; @__sat4098; @__sat4099; @e; @R; @_H; @a0; @BELOW; @INIMG; @o; @LOWIMG; @LO2; @M; @B; @INLAND; @HI; @NOTLO; @ABOVE; @A4096; @NOTIN; @NW; @AF; @CE; @FREE; @BIG; @NAL; @TOP; @POS; @AL; @n|] "#8I#Z$v#a$G#f$H$F#e###n$N#$$`$s#%$m#&$P#+#Z#*$L#)#5$4$h$x#'#(#0$.$V#-$\#7#x#;#B#D#u#,#.#:#6#I#/#H#8#@#<#G#M#9#>#A#C#E#=$=#4#3#1#F#`$$#?#K#L#k$1#J$f#2$l#O#S$'$9#N$p$q$u$v$w#P$y#U#^#]#j#q#r#s#p#o#v#w#y#{#~$#$%$<$;$>$?$A$C$E$O$W$X$Z$[$Y$]$c$e$o$n$r$t#T#Q#R#Y$z#h#_#g#b#z#c#m#d$J$I$D#i$)$_$6$($Q$@$&$*$+$,$-$8$7#}$/$3#l$K$M$i$B$T$R$a#t$:$5$^$d$k$j$0$U$b$g$2$S#|U$D%$E$$F%$G&$H%$I%$J$$K%$L'$M*$N+$O%$P%$Q%$R&$S%$T*$U'$V%$W%$X%$Y%$Z%$[$$\%$]%$^%$_&$`$$a%$b%$c%$d%$e&$f)$g)$h$$i&$j%$k)$l($m&$n)$o%$p&$q%$r%$s%$t)$u%$SP$#$#$#$#$#USh#USi#*$L(#H&C#E*'O%E#*)Q.#OUSjSU#$#$.$#$#$#$#$#?#(Q#&C#E)SP)#)#$#$#$#$#$#$#$#$#$#$#$#$#?#%#S,VSks#&s#&USlSUUSmSUWSn%$#GS-WSo$S'#&J#S8*s#.S%YSp#S'S-OQ.$S'USqS4#$#USrS4)>)#)#)#)#)#)#)#)#)#)#$#)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?###s#1)s#%)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?##s#S#'s#%#(s#Us#s&C#EUSsS4#s#X#.s#Ys#w%%#'%#'(#'+#*s$1S9<#H#E$#EH*s$5S:(#H#E#k##&#k##(#?s$@?s$<VSt$#%E%#E%VSu'&%E#k##%#k##'##E+WSv,+Lj##SQ#j#$%##E*k##SQ#k#$(#<S:s$9#ES:#Es$;(S.s$<#E#k##%#k##'#<s#~s$@#Es$##Es#-k##*#k##%#5s$'s$E&Cs$FEUS]#/s$*s$H2s$I#.#s#5&Cs$-#k##'#6s$/s$M%Es$N%s#:s$O'0#k##%#7s$4s$R%s$SE%s$Ts#?#s#@E'$#k##&#8s$:s$X&C3Ek##6#9s$=s$[&Cs#Gs$>k##9#=s$@s$^m#S/#5S<s$`/S3s$a2s$b#(S3s$c.$#&CS3#k##A#6S3s$g(S@s$h#E#%$s$j'$#k##@#7S@s$m(SEs$n%s$o##$E'$#k##A#8SEs$s/S;s$t&C#Ek##s#2#9S;s$w(S5s$x&C#S5k##s#6#=S5s${m#S/#*s%2SJ5#H&CHEUS]#*s%6SF/#H2H#(%H.$#&C'#k##)#6)H%EH*s%?SR(#H#E#%$H'$#k##(#7(H%HE*s%GSA(#H%H##$E'$#k##(#8(H*s%NSG/#H&C#Ek##?#9&H*s%SS6(#H&C#$k##s#$#=&Hm#S/#REHNSV#m##?US,#*s%]SH(#H#E#%$H'$#REs%QNSV#m##s#cUS:#(SHs%U#E#%$s%W'$#US((VSBILj#%s$+#k#%s$,s$(REs$6NSV#m##s$5USJ#:S^:#:#:#:#:#:#:#:#:#:#;C#;C*;C,USwSPVSxC#;C2HC$#;CS^1C$#1C)#1C+#1C-#I#SK;C91C#)1C/#1C1#I#SKUSyS)>S)$#>S)%#>S)+#>S),#>S)-#USzS)US{CCCS'4C$S'#CCS,4C$O#CCS-4C#S'(4C#Q)4C&L#US|CUS}C)s&J@C#ACE+C$S&#,'GDDF#KUS~D@Cs&Q@Cs&8+C$S&#,,GDDF#K--GDDF('#$s&<$#@C#+C#S&.,2GDDF#K-3GDDF.-#+C2R1,5GDDF#K+C4R/,7GDDF#KE8GDDFS#39GDDF$#-:GDDF'4#E;GDDFS9+C5R:,=GDDF#K3>GDDF%#S?GDDF:OC>2DC#:+C:S&#,s##GDDF#K-s#$GDDF'>#ACs%f@C:+C$S0#,s#(GDDF#KACs%H+C&S0#,s#+GDDF#K3s#,GDDF&#Es#-GDDFS13s#.GDDF$#@CSPDCs#(#+C#S0-,s#2GDDF#KACs&R+C#R',s#5GDDF#K+Cs#3Rs#.,s#7GDDF#K+Cs#1S&s#5,s#9GDDF#K+Cs#7S0-,s#;GDDF#KACs%FWT#C#s'#+C1R#,s#?GDDF#K3s#@GDDF'#-s#AGDDF*s#;#-s#BGDDF-s#<#-s#CGDDF0s#=#-s#DGDDF4s#>#-s#EGDDF9s#?#-s#FGDDFs#$s#@#-s#GGDDFs#+s#A#-s#HGDDFs#0s#B#-s#IGDDFs#8s#C#-s#JGDDFs#?s#D#VT$s#KFNJS8VT%IO&J#S8m$%#WT&CELXT'IO$#l#&*)#l#'s#Us#T#l#(s#`s#_#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#/S$#j#0S$#j#1S$#&CS,E&COQk##$#&CS-E&CS%Ek##$#%S'E%S%S,'#S9k##%#%S,S%'S1#&CS#Ek###S22S9S1.#S'&CS%#k##&##s&US##S#s&4'$#'#S..S#S'##S9%s'9S%%ES1&CS1E#ES1%S1s&#'$#k##&#k##(#k##*#k##,#k##/#k##4#k##;#k##>#k##s###k##s#'#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#/S$#k#0S$#k#1S$#*s'uSW(#H#E##$E/&HgIs&M%$#Hs'K'&S=S#S9S1S'S>SGS6S7SCS?l#2s#:)#l#3s$is&=#l#4s$os$n#l#5QSQ#l#6s$ss%|#l#7s$ys$u#l#8s%'s$~##ES6%S6s&F'$#m#&#l#9s%0s%1#l#:s%7s%3#l#;s%=s%9#l#<s%Fs%?#l#8s%Os%H#l#=s%Zs%Q#l#>s%]s%^#l#?s%cs%`#l#@s%hs%e#l#As%os%j#l#7s%vs%q#l#Bs%~s%x#l#Cs&$s&%#l#Ds&)s&'#l#Es&-s&+#l#Fs&4s&/#l#6s&:s&6#l#Gs&Cs&<#l#Hs&Is&E#l#Is&Qs&K#l#4s&Vs&S#l#3s&as&[#l#Js&ls&e#TS##GS#*s(C#&C#S#m#&#*s(FI#s&p#.s&qS1%%#'%#GS:*s(LS.##s(H.$I%s(J#'%#j#KC#*s(R)JCS:$I#OZT(s(,S>+LS-#0Ls(-&J#M0Os(/&JIMj#LJ#0Os(40Os(4P$#WT)Os(7s(6FJ)'I$#&J%MPLI&J#M&JOM&JLM'$#k##&#'%0POL&J#Mk##%#''#&JQM'#,k##'#j##&#PQO&J#Mk##/#j###Lj##0#VT*LIK2.)$#j#MJ#j#NJ#k#MJ5k#NJ#0S,s(T0S,s(TWI$#L&J%M&J%M'$#l#O&#Il#G,*#l#Os#&s#%#l#Os#1s#/#j#Ps#<#j#Qs)(#0Ls(`&J#M0Ls(a&J#M'%#k##s#C#k#Qs)/#5SLs(|/S(s(}2s(~#(S(s)#.$#&CS(#k##s'=#6S(s)'(S<s)(#E#%$s)*'$#k##s'<#7S<s)-%s).s')#s'*E'$#k##s'<#8S3s)2/S@s)3&C#Ek##s'M#9S@s)6&Cs''SEk##s'P#/SEs)9(S;s):*s)LSB5#s)</s&zs)=2s)>#(s&|s)?.$#&Cs&~#k##s'Y#6s'$s)C(s&}s)D#E#%$s)F'$#k##s'X#7s'&s)I(s&zs)J%s)K##$E'$#k##s'Y#8s'#s)O/s&xs)P&C#Ek##s'j#9s&{s)S(s&us)T&C#s&vk##s'n#/s&xs)W(s&ts)XUS-s&d#EI%Is)['$#US.s&h#ES#%S#s)_'$#US@s&l#ESM%SMs)c'$#;Cs&`HCs&T#1C#s&Q1C%s&M1Cs&Y#1Cs&Ws&UI#SKVSX%#VSX(#>S)#s&NCCQ4Cs&IQ#4C#Os&J4C#Ls&KACs)s+C#S&s&@,s&DGDDF#KSs&EGDDF#OC&s&8DC#s&@+Cs%wS&#,s&IGDDF#K-s&JGDDF's&D#+Cs&HRs%z,s&LGDDF#K+C-S0s%|,s&NGDDF#K-s&OGDDFs%ts&I#-s&PGDDF&s&J#-s&QGDDF)s&K#l#&#s%es%_l#'4s&T#l#(9s&_#j#)C#j#*C#j#+C#k##s(ES22s*.Q.#O&CL#k##&#%EL&CQE#s*4Qk##$#k##&#k##(#k#)C#k#*C#k#+C#*s*LSCZIS-S,#S1S7SIl#23%#l#6s#;s#8#l#Bs#@s#=#l#>s#Es#B#l#Rs#GC#l#Ss#IC#l#<s#Ns#K#l#8s#Ss#P#l#=s#Zs#U#l#>s#as#\#l#?s#is#c#l#Ts#lC#l#Us#nC#l#@s#rs#p#l#As#ws#t#l#7s#}s#y#l#Bs$(s$##l#Cs$0s$*#l#Vs):C#l#Ws(fC#l#Ds(Ts(R#l#Es(Xs(V#l#Fs(_s(Z#l#6s(es(a#l#Gs(ns(g##s*Vs)4*s*hS>Q#S*%$S*#S*%B$#%s%#S*#S*s%$B$#*s*pSNLS4#S.j##%#%%S**s*tSYLS4#SNQ$P%%P#P&B$#*s*zSM%#P#P$B$#j###S2*s+#SL%#PGP*s+&S<##I.$S(%I#'%#j#KC#*s+,S(<#H#E$*s+/S3(#H#E#k##s)\#k##'#<S(s+##ES(#Es(|k##s)I#k##%#5SJs+(/SFs+)2s+*#(SFs++.$#&CSF#k##s)E#6SFs+/(SRs+0#E#%$s+2'$#k##s)D#7SRs+5(SAs+6%s+7##$E'$#k##s)E#8SAs+;/SGs+<&C#Ek##s)V#9SGs+?(S6s+@&C#S6k##s)Z#=S6s+Cm#S/#*s+VS75#H*s+XSI/#H2H#(%H.$#&C'#k##s)+#6)H*s+`SO(#H#E#%$H'$#k##s))#7(H(s#yH%H##$E'$#k##s)'#8s#~H*s+mS?/#H&C#Ek##s)>#9&H*s+rS=(#H&C#$k##s)C#=&Hm#S/#%s&`H's&`#(SWs+i#E#%$s+k'$#:s(`:#;C#HCs(^#;Cs(i1C#s(_1C%#I#SK;Cs(k1Cs(fs$o1C$#VT+Cs+xWT,C#s(d;Cs(oHCs(i#;Cs(sHCs(ks(m1C#s(k1C%#1C'#1C*#I#SKVSX.#>S)#s(d>S)$#>S)4#>S)5#>S)6#CCS#4Cs(cS-#4Cs(dO#CCS%4Cs(fS,#4Cs(fS#s(g4C$Q#4C'L#)s,L)#@C#+C#S&s(`,s(dGDDF#K+Cs(]S&s(8,s(fGDDF#K-s(gGDDF%s(a#$s,9@C#+C#S&s(g,s(kGDDF#K-s(lGDDF*s(f#+C-Rs(j,s(nGDDF#K+C/Rs(g,s(pGDDF#K3s(qGDDF#s(F-s(rGDDF&s(l#Es(sGDDFS:+Cs(lR4,s(uGDDF#K3s(vGDDF%#Ss(wGDDF5OC81DC#s(q+Cs(MS&#,s({GDDF#K-s(|GDDF's(v#)s(q@C#OCs%?#@CBDC$#+Cs({S&#,s)'GDDF#K-s)(GDDFs%As(~#$s,[$#$#$#?#$SP$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#)SP$#$#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#?#AC:+Cs)*R#,s)XGDDF#KEs)YGDDFS>3s)ZGDDFs)4#Es)[GDDFS.3s)\GDDF$#+Cs),Rs)V,s)^GDDF#K+Cs#=S&s)\,s)`GDDF#K+Cs)YS&s)^,s)bGDDF#K+Cs)6S0/,s)dGDDF#KDCs)8s)^+C2R#,s)gGDDF#K3s)hGDDF&#-s)iGDDF)s)c#-s)jGDDFs%|s)d#-s)kGDDF-s)e#-s)lGDDF0s)f#-s)mGDDF3s)g#-s)nGDDFs%~s)h#-s)oGDDF9s)i#-s)pGDDFs#Js)j#-s)qGDDFs#Ss)k#-s)rGDDFs#Zs)l#-s)sGDDFs#_s)m#-s)tGDDFs#fs)n#-s)uGDDFs#ls)o#l#&#s)-s)'l#'s#vs)x#l#(s$#s*'#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#XC#j#YC#j#/S$#j#0S$#j#1S$#j#ZS$#&CQLk##s)'#&CS'E&CS9Ek##$#%S%E%S#S-'#S:k##%#%S-S#'S>#k##*S22S1S>.#S%&CS-#k##&#2s-jS>.#S9&CS%#k##s&B#%S's#]#s-oS%#s-$S>'#S('#S<%s-aS1&CS.E%ES:&CSNE#S.s#f.S.SN%s#h#'%#k##'#k##)#k##+#k##-#k##/#k##3#k##5#k##7#k##<#k##B#k##s#%#k##s#*#k##s#.#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#XC#k#YC#k#/S$#k#0S$#k#1S$#k#ZS$#*s.IS_(#H#E##$E/&H/SDs.=(SDs.>i#<Is-#s-,'&%$Hs-}#(SD)S-S'S%QS9SYSBS6SIS?S=SSSTl#2s#E+#l#6s+Fs,O#l#7s+Ls%4#l#8s+Vs%9##s)>s$3.s)?S=%s$5#'%#m#'#l#9s%As%B#l#:s%Hs%D#l#;s%Ns%J#l#<s%Us%P#l#8s%]s%W#l#=s%fs%_#l#>s%is%j#l#?s%os%l#l#@s%ts%q#l#As%{s%v#l#7s&&s%}#l#Bs&.s&(#l#Cs,Ts,U#l#Ds,Ys,W#l#Es,]s,[#l#Fs,ds,_#l#6s,js,f#l#Gs,ss,l#l#[s,ys,u#l#\s&;s&7#l#]s&Cs&=##s&EP.s&FSL%P#'%#m#'#VS`s.tP*s.u#ULs+d+Cs+2S0s$=,s+6GDDF#K+Cs$?Rs*X,s+8GDDF#K3s+9GDDF%#l#&#s*Ms*Gl#'s+Es+<#l#(s+Ms+G##Es$]%s$^s-C'$#l#2&#Il#I/s-D#l#Hs-@s-=#l#Is-Ks-E##EP%Ps-J'$#m#&#TP#JCPs&b:8#*s/0s&i#s&c#%$@'$#m#'#VS%s&n#0s&os.l&J#M0s&qs.m&J#M'%#j###S2#PI%IS*'$#j#KC#+Cs$bS0s$b,s+[GDDF#K)s+O$#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#?#ACs$y+Cs$yR#,s+rGDDF#K3s+sGDDF:#l#&#s++s+%l#'s,#s+v#l#(s,+s,%##s%;s%;%s%<s%%'$#l#2&#I#PP%PS*'$#m#&#JCPs#(#s#Ns#9#Ps#8%s#9S*'$#m#&#VSas'G#FJs#7s)pLS8#&JS8MnJ#$#LS$I#%#SQ#S2j#^J#FJS8#S/MIVSZS2Il#G$S2#l#_)(#j#`s#<#j#_s#?#V#LIj##s#?#j##s#B#Ks#Cs#As#?#Il#as#Fs#A#j#bs'X#U#Ij##s'_##Ps'\CCO4C#Ls,G+Cs+mS0s+m,s,?GDDF#K+Cs+oRs%9,s,AGDDF#K3s,BGDDF%#-s,CGDDFs%Cs,=#l#&#s+Ws+Ql#'*s,F#l#(s,Ws,Q#j#)C#j#*C#%s/hL#LL.LO%L#'%#k##'#k#)C#k#*C#WISDs$LS?l#2,$#l#6s--s.6#l#7s-3s&w#l#8s-=s&|##s+%s+%%s+&s$E'$#m#&#l#9s''s'(#l#:s'.s'*#l#;s'4s'0#l#<s';s'6#l#8s'Cs'=#l#=s'Ls'E#l#>s'Os'P#l#?s'Us'R#l#@s'Zs'W#l#As'as'\#l#7s'hs'c#l#Bs'ps'j#l#Cs.:s.;#l#Ds.?s.=#l#Es.Cs.A#l#Fs.Js.E#l#6s.Ps.L#l#Gs.Ys.R#l#[s._s.[#l#\s'}s'y#l#]s()s(##VS%S(#0S(s00&J#M0S(s01&J#M'%#0S<s05&J#M0S<s06&J#M'%#j###S20S3s0:&J#M0S@s0=&J#M0SEs0>&J#M0S;s0A*s0hS;<#H#E$(s)}H#E#k##s/;#k##&#<S;s0^#ES;(SBs0`#E#k##s/)#k##&#5S6s0d/SHs0e2s0f#.#s-p&CSH#k##s/$#6SHs0j(S7s0k#E#%$s0m'$#k##s/##7S7s0p(SIs0q%s0r##$E'$#k##s/$#8SIs0v/SOs0w&C#Ek##s/5#9SOs0z(SCs0{&C#SCk##s/9#=SCs0~m#S/#5s'}H2Hs+w.#s+{&Cs+}#k##s.b#6s,#H*s1;SS(#H#E#%$H'$#k##s.`#7(H*s1BST(#H%H##$E'$#k##s._#8(H*s1ISD/#H&C#Ek##s.v#9&H&Cs%bs%ck##s.y#=s%eHm#S/#*s1RS[(#H#E#%$H'$#(S[s1F#E#%$s1H'$#4Cs$;Ls*9+Cs-IS0s-o,s-wGDDF#K+Cs-qRs-p,s-yGDDF#K3s-zGDDF%#-s-{GDDF$s-u#-s-|GDDF's-v#l#&#s-4s-.l#'+s.##l#(s.4s..#j#)C#j#*C#j#+C##IL%OQ#OQ%QS,'$#k##&#k##(#k#)C#k#*C#k#+C#*s1sS\YIS*#PSGS7l#2/%#l#6s.js/s#l#7s.p?#l#8s.zs#$##Ps#)%s#*S*'$#m#&#l#9s#.s#/#l#:s#3s#1#l#;s#9s#5#l#<s#As#;#l#8s#Is#C#l#=s#Os#K#l#>s#Qs#R#l#?s#Ws#T#l#@s#\s#Y#l#As#cs#^#l#7s#js#e#l#Bs#qs#l#l#Cs/ws/x#l#Ds/|s/z#l#Es0$s/~#l#Fs0+s0&#l#6s01s0-#l#Gs0:s03#l#[s0@s0<#l#\s$#s#z#l#]s$*s$%#VSaS;#FJs$.s,<LS8#l#_#s%*s%%j#`s$1#j#_s$4#V#LIj##s$8#j##s$?#Ks$@s$>s$<#Il#as$Hs$C#j#cs$}#U#Ij##s*$#Ms*&s*%s*#s%%#Il#ds*,s*)#VSZs*.#j#es*1#U#Ij##s*9##S*s*7.s*4SNVT-#N#$N%N%B$#.s*3SY##N%N$B$#LS4s*2SMj##$#.s*4SM##NVSbs*-SLWScS4s*.SL#S*s*/#s&HNXSd$#QIWT.'&#j#f)#U#Ij##1#%N-Qs*7S+%s*8S+#S+s*9B$#%s*AS+#S+s*BB$#LS4s*;S<j##$#%s*=S+*s2kS@LS4#S3Q$N%%N#N&B$#*s2qSE%#N#N$B$#j###S2%s$lNGN#s,.I.s,/S5%I#'%#j#KC#*s2}S5<#H#E$(s0PH#E#k##s1P#k##&#<S5s2s#ES5(SJs2u#E#k##s1>#k##&#5SHs2y/S7s2z2s2{#.#s$o&CS7#k##s19#6S7s3##Es$m%s$ns3%'$#k##s17#7SIs3((SOs3)%s3*##$E'$#k##s18#8SOs3./SCs3/&C#Ek##s1I#9SCs32(S?s33&C#S?k##s1M#=S?s36m#S/#5s.2H/s$mH2H#.#s$n&Cs$p#k##s0w#6s$rH#Es$k%s$lH'$#k##s0s#7s$pH(s$jH%H##$E'$#k##s0q#8s$oH&Cs'lEk##s1*#9s'rH&Cs$is$jk##s1-#=s$lHm#S/#*s3bSe(#H#E#%$H'$#(Ses3V#E#%$s3X'$#+Cs/XRs/~,s0*GDDF#KDCs/Zs0#+Cs0%R#,s0-GDDF#K3s0.GDDFs$q#-s0/GDDF$s0)#-s00GDDF(s0*#l#&#s/Ds/>l#'s$ws03#l#(s0Ds0>#j#)C#j#*C#j#+C#%IL.LQ%O#.OS,%Q#'s$q#k##&#k##)#k#)C#k#*C#k#+C#*s4(T/YIS\N#SBS6l#20%#l#6s0{s2(#l#7s1%@#l#8s1/s#%##s#*N.s#+S[%N#'%#m#'#l#9s#0s#1#l#:s#5s#3#l#;s#9s#7#l#<s#@s#;#l#8s#Fs#B#l#=s#Ms#H#l#>s#Os#P#l#?s#Us#R#l#@s#Zs#W#l#As#as#\#l#7s#gs#c#l#Bs#ns#i#l#Cs2-s2.#l#Ds22s20#l#Es26s24#l#Fs2=s28#l#6s2Cs2?#l#Gs2Ls2E#l#[s2Rs2N#l#\s#|s#w#l#]s$'s#~#VS`s4HN*s4I#$s3f$#$#$#$#$#$#$#$#$#$#$#?#AC#+Cs0oS0#,s0sGDDF#K+C%Rs09,s0uGDDF#K3s0vGDDF%#l#&#s0.s0(l#'s1&s0y#l#(s1.s1(##E,%-s3$'$#l#2&#Il#Is(Ls3%#l#Hs2}s2z#l#Is3,s3&##EN%Ns3+'$#m#&#TN#JCNs$Ns#'s#%#*s4ms$T#s$O#.s$PS;%%#'%#m#(#VS.s$Z#0s$[s4N&J#M0s$]s4O&J#M'%#j###S2#NI%IS+'$#j#KC#+Cs#)S0s#),s1=GDDF#K)s*s)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#?#AC#+Cs#LR#,s1`GDDF#K3s1aGDDFs#&#l#&#s0us0ol#'s1ms1d#l#(s1us1o##s#Ss#S%s#T+'$#l#2&#I#NN%NS+'$#m#&#JCNs#4#s#hs#F#Ns#E%s#FS+'$#m#&#VSfs%?#FJs#As/^IS8#l#g#s(Ls(Gj#gs#B#j#`s#E#V#LIj##s#E#j##s#H#Ks#Is#Gs#E#Il#as#Ls#G#j#hs%J#U#Ij##s%P##Ns'[WIS\s$@S_l#2s(;s(3#l#6s2\s3e#l#7s2bs$]#l#8s2ls$b##s$gs$g%s$hs$?'$#m#&#l#9s$ls$m#l#:s$qs$o#l#;s$us$s#l#<s$|s$w#l#8s%&s$~#l#=s%-s%(#l#>s%/s%0#l#?s%5s%2#l#@s%:s%7#l#As%As%<#l#7s%Gs%C#l#Bs%Ns%I#l#Cs3is3j#l#Ds3ns3l#l#Es3rs3p#l#Fs3ys3t#l#6s4#s3{#l#Gs4,s4%#l#[s42s4.#l#\s%\s%W#l#]s%cs%^#VS.S5#0S5s5_&J#M0S5s5`&J#M'%#0SBs5d&J#M0SBs5e&J#M'%#j###S20SJs5i&J#M0SFs5l&J#M0SRs5m&J#M0SAs5o<s3RH#Es3S#Es3Gk##s4h#k##%#<SAs6/#ESA#Es-Ok##s4U#k##%#5S?s64/S=s652s66#(S=s67.$#&CS=#k##s4Q#6S=s6;k##s4Ls-.7SWs6=(SSs6>%s6?##$E'$#k##s4M#8SSs6C/STs6D&C#Ek##s4^#9STs6G&Cs*hSDk##s4a#=SDs6Jm#S/#5s'iH/s%ZH2H#.#s%[&Cs%]#k##s4/#6s%_H*s6dT0(#H#E#%$H'$#k##s4-#7(H*s6kT1(#H%H##$E'$#k##s4,#8(H/s']H&C#Ek##s4B#9s'`H(s%PH&C#s%Qk##s4F#=s%SHm#S/#*s6{Sg(#H#E#%$H'$#(Sgs6o#E#%$s6q'$#*s7(T2YIS+#NSGS7l#2s'|s'r#l#6s3{s5(#l#7s4%'#l#8s4/,##N1%2S+'$#m#&#l#967#l#:<9#l#;A>#l#<s#)s###l#8s#1s#+#l#=s#8s#3#l#>s#:s#;#l#?s#?s#=#l#@s#Ds#A#l#As#Ks#F#l#7s#Ns#M#l#Bs#Vs#P#l#Cs5,s5-#l#Ds51s5/#l#Es55s53#l#Fs5<s57#l#6s5Bs5>#l#Gs5Ks5D#l#[s5Qs5M#l#\s#cs#_#l#]s#is#e#VSfSA#FJs#ls1MIS8#l#g#s*;s*6j#gs#o#j#`s#r#V#LIj##s#v#j##s#}#Ks#~s#|s#z#Il#as$*s$%#j#hs$J#U#Ij##s'>#Ms'@s'?s'=s$N#Il#ds'Fs'C#VSZs'H#j#is'K#U#Ij##s'R##S+s/-VSbs'NS3WScS4s'OS3#S+s'P.s'QS3##s70XSd%#IS.WT3('#j#j*#U#Ij##s'\#Ms'^s']s'Z.#Il#ds'cs'`#j#ks'e#U#Ij##s'v#Ms'xs'ws'ts'i#Il#ds'~s'{#j#ls(%#U#Ij##s/^#Ms/`s/_s/[s()#Il#ds/es/b#l#ms/is/h#l#ns1Ks1D#l#os20s21#l#ps7Cs6F#l#qs7Hs7E#j#rs7K#j#ss7S#j#ts7e#j#us7o#j#vs7t#j#ws7w#j#xC#j#%s7|##"). Qed.
  End Derived.

  (* [comment removed for export] *)
  Lemma akernel_mat : forall mo mo', akernel mo -> same_but_materialized mo mo' -> akernel mo'.
  Proof. intros mo mo' AK SB. unfold akernel in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact AK. Qed.
  Lemma AMODELX_mat : forall mo mo', AMODELX mo -> same_but_materialized mo mo' -> AMODELX mo'.
  Proof. intros mo mo' [A K] SB. split; [eapply AMODEL_mat; eassumption| eapply akernel_mat; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma awin_vis_wmono : forall m m', awin_vis m -> wmono asegs m m' -> awin_vis m'.
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
Theorem AGAP_of_akernel : forall s mo n, akernel s mo -> 0 < n ->
  AHI_LO + (AHL0 + zsum (map sc_map_size (hsec (a_st s)))) + (AHC0 + zlen (hsec (a_st s))) * (n + 4096) + n <= hceil ->
  AGAP n mo.
Proof.
  intros s mo n AK Hn ROOM. unfold AGAP.
  pose proof AK as (K1 & (_ & K2) & _). pose proof (ak_hcov s mo AK) as (C1 & C2 & _).
  rewrite K2, cost_app.
  assert (R0 : cost n AHI_LO (vm_reserved (m_vmmaps mo)) = 0).
  { assert (L : Forall (fun e => KInv.ehi e <= AHI_LO) (vm_reserved (m_vmmaps mo))).
    { apply Forall_forall. intros e He. specialize (K1 e He). unfold KInv.ehi, AHI_LO, AIMG_TOP in *. lia. }
    clear - L Hn. induction L as [|e E He L IH]; [apply cost_nil|]. rewrite cost_cons, IH, (ecost_below n AHI_LO e He). reflexivity. }
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

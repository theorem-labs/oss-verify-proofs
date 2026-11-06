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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP AXImg_leafP N8Kit N8Kit2 N8Kit3 X8Kit X8Call X8LeafKit X8StateKit X8StateKit2 X8StateKit3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TABB_PCHAR : list byte := map (fun z => Z_to_bv 8 z) TAB_IS_PATHCHAR.
Lemma len_PCHAR : length TAB_IS_PATHCHAR = 256%nat. Proof. reflexivity. Qed.

Section TAB.
  Context {HCEIL : HeapCeil}.

  Lemma tab_pchar_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 0x29c00 TABB_PCHAR.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.SysStep.ro_cells_bytes_at); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8StateKit4.TABB_PCHAR); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Image.ro_cells_image); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Image.ro_bytes_b); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.length)|] [|@__ff; @__varmap; @__wit; @__arith; @x; @y; @m; @n; @Ha; @__sat1; @__sat0; @MI|] "#'F#&#e#C###L#$#/#8#H#<#=#I#V#U#S#*#)#9#4#>#@#J#M#E#G#N#%#^#`#a#,#-#.#7#5#3#?#A#B#D#F#O#Q#R#P#W#Y#[#\#]#Z#X#_#b#d#c#e#f#T#g#:#0#6#+#2#;#1#K,#_$#`$#/%#a$#b%#c$#d%#.%#-$$S/$#$#$#$#$#UP#UQ#UP(UQ#US0#k##&#VS1GD&/$#$#&#&#&#$#&#&#$#&#$#$#$#$#$#(##S2##############################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################VS3#HURS#WS4S#$#'JK$S/&#$#$#&#&#&#$#$#$#$#$#$#$#$#$#$#(#WS5G#HWS$J#Km$7#URS%US6S%US7CUS8CUS9C)CE)C,XS&C$S'#[S(&S)IIL#S*VS:'LVS;DS+WS$J#Km$s#$#WS<CEFXS=DS+$#l#$)(#l#%0/#l#&32#%E8l#'$#Dm##$+s#1*<#(s&<(s&8VS>$#%&#$s&;$#(#*s#$#%#(j#(CD%FDUS?#j#)C#j#(C#*FDXS@CCSA#'C#j#*C#j#+C#'Cs#0+D'C#j#(S,#'C3`SBS,CCCMM11$s#K4#fSCCCCCCCN222N)s#6s#6(=5#'C:`SDCCO4O0>6$;;#VSE>=VS-E?%E?VS-E?k##$#k##&#%Es#$WSFs#%s#$Fj##S.#j#,%#%Es#&k##S.#k#,(#VSGEs#+'SH#m##0UF#)Cs#)WSICs#A#)Cs#1WSJC#s&fXS&C%S'#[S(s#GS)IIL#S*l#$#s#Cs#>l#%s#Ks#J#l#&s#Ns#M#l#'#s#0Dl#--9#l#.52#l#-?:#XSKs#9s#4A#m##s#:VSLs&oH+#*s#[#%#s#?m#'#\SMGFs#^HDs#[s#F#YSNGFs#_s#r#j#/s&s#j#*s&u##"). Qed.

  Lemma pchar01 : forall c, 0 <= nth (Z.to_nat c) TAB_IS_PATHCHAR 0 <= 1.
  Proof. intros c. apply tab01. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pchar_load : forall c, 0 <= c < 256 ->
    zxb (Z_to_bv 8 (nth (Z.to_nat c) TAB_IS_PATHCHAR 0)) = wz (if is_pathchar c then 1 else 0).
  Proof.
    intros c Hc. unfold is_pathchar. pose proof (pchar01 c) as H.
    remember (nth (Z.to_nat c) TAB_IS_PATHCHAR 0) as v eqn:EV. clear EV.
    assert (E : v = 0 \/ v = 1) by lia. destruct E as [-> | ->]; reflexivity.
  Qed.

  Lemma img_pchar_ok : forall m, ACONST m -> accessible m AL_TAB_IS_PATHCHAR 256.
  Proof. intros m AC. apply (ACONST_gbody_accessible m AL_TAB_IS_PATHCHAR 256 AC). vm_compute. reflexivity. Qed.

  Lemma img_tchar_ok' : forall m, ACONST m -> accessible m AL_TAB_IS_TOKEN_CHAR 256.
  Proof. exact img_tchar_ok. Qed.
End TAB.

Ltac tab_pchar c := tab_load tab_pchar_bytes TABB_PCHAR TAB_IS_PATHCHAR len_PCHAR c 0x29c00.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ps_chkimg SD MU WM FW IMG TAB x PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (accessible_read0_in mc TAB 256 x (IMG mc (pside2_aconst _ _ _ _ _ SDc))
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold TAB; lia)) as RD;
    unfold TAB in RD; clear SDc;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

(* [comment removed for export] *)
Definition kpick (k j : nat) (v d : word) : word := if Nat.eqb k j then v else d.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land1_loc : forall loc, Z.even loc = true -> Z.land (loc + 1) 1 = 1.
Proof.
  intros loc EV. change 1 with (Z.ones 1) at 2. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Z.even_spec in EV. destruct EV as [k ->].
  replace (2 * k + 1) with (1 + k * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac isl_cat_now HC MUh WMh FACTS :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch type of HC with AHttpCat _ ?g =>
    let HCc := fresh "HCc" in
    assert (HCc : AHttpCat mc g)
      by (eapply AHttpCat_transport; [exact HC| exact MUh| exact WMh| |];
          cbn [disjoint_from fst snd]; unfold AG_HTTP_CAT, AG_HTTP_CAT_GUARD; FACTS; repeat split; lia);
    clear HC MUh WMh; rename HCc into HC
  end end.

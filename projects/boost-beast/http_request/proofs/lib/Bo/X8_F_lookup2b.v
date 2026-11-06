(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXRep_fields AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8LeafKit X8Call X8SRKit X8_F_kit X8_F_trim X8_F_rbread X8_F_rbread2 X8_F_rbins X8_svcopy X8_F_insert X8_F_insert2 X8_F_insert4.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8_P_ftab_rep X8_P_ftab2 X8_P_tok_stmt X8_P_tok3_stmt X8_F_lookup X8BoKit X8_F_lookup2 X8_F_lookup2a.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe RBOrder RBKey RBInsert RBBalance DList RBElement.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
(* [comment removed for export] *)
Ltac2 rec fit_arith_orneg (t : constr) : bool :=
  lazy_match! t with
  | ?a \/ ?b => Bool.and (fit_arith_orneg a) (fit_arith_orneg b)
  | ?a /\ ?b => Bool.and (fit_arith_orneg a) (fit_arith_orneg b)
  | not ?a => fit_arith_orneg a
  | _ => LiaTuning.zt_plain_arith t
  end.
(* [comment removed for export] *)
Ltac2 fit_orneg_hyps () : ident list :=
  List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if LiaTuning.zt_plain_arith ty then None
                else if Bool.and (LiaTuning.zt_is_local id) (Bool.and (LiaTuning.zt_is_prop ty) (fit_arith_orneg ty))
                then Some id else None
      end) (Control.hyps ()).
(* [comment removed for export] *)
Ltac2 fit_prune_but (keep : ident -> constr -> bool) : unit :=
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if LiaTuning.zt_plain_arith ty then None
                else if keep id ty then None
                else if Bool.and (LiaTuning.zt_is_local id) (LiaTuning.zt_is_prop ty) then Some id else None
      end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac2 rec fit_first_of (ids : ident list) (k : ident -> unit) : unit :=
  match ids with
  | [] => Control.zero (Tactic_failure None)
  | i :: rest => Control.plus (fun () => k i) (fun _ => fit_first_of rest k)
  end.
Ltac fit_xlia1 := zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac2 fit_lia_one () : unit :=
  let ids := List.rev (fit_orneg_hyps ()) in
  Control.once (fun () => fit_first_of ids (fun i => fit_prune_but (fun id _ => Ident.equal id i); ltac1:(fit_xlia1))).
Ltac fit_prune_orneg := ltac2:(Control.enter (fun () => fit_prune_but (fun _ ty => fit_arith_orneg ty))).
Ltac fit_lia_1 := zify_prune; fit_xlia1.
Ltac fit_lia_1a := ltac2:(Control.enter fit_lia_one).
Local Ltac lia ::=
  first [ fit_lia_1
        | fit_lia_1a
        | fit_prune_orneg; fit_xlia1
        | zify_prune; Zify.zify; xlia zchecker
        | fit_prune_orneg; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac fit_slia_atom := first [ exact I | assumption | dj_lia ].
Ltac fit_slia_conj := first [ exact I | lazymatch goal with |- _ /\ _ => split; [fit_slia_atom | fit_slia_conj] end | fit_slia_atom ].
Local Ltac slia ::= fit_slia_conj.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac fast_eassumption :=
  first [ lazymatch goal with
          | |- rw_cells _ ?M ?A _ => assert_fails (is_evar M); match goal with H : rw_cells _ M A _ |- _ => exact H end
          | |- ro_cells _ _ ?A _ => match goal with H : ro_cells _ _ A _ |- _ => exact H end
          | |- bytes_at _ ?M ?A _ => assert_fails (is_evar M); match goal with H : bytes_at _ M A _ |- _ => exact H end
          | |- u8arr _ ?M ?A _ => assert_fails (is_evar M); match goal with H : u8arr _ M A _ |- _ => exact H end
          end
        | eassumption ].
(* [comment removed for export] *)
Local Ltac fit_zsizes :=
  repeat match goal with
  | |- context [Z.of_nat (cells_size ?cs)] =>
      let v := eval cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat (cells_size cs)) in
      lazymatch v with Z0 => idtac | Zpos _ => idtac end;     (* [comment removed for export] *)
      change (Z.of_nat (cells_size cs)) with v
  end.
(* [comment removed for export] *)
Local Ltac dj_lia ::=
  first [ let a := dj_subject in progress (dj_reveal_for a); lia
        | lia
        | match goal with K : hideL _ |- _ => unfold hideL in K; lia end ].
Ltac2 Set StepFast.sf_check := true.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition OTF_STACK : Z := 176 + INS_STACK.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AFT_xpres : forall (H : asr) LB SP X m m',
  FT m -> xpres H LB SP X m m' ->
  Forall (fun iv : Z * Z => AG_FIELD_TABLE + 3456 <= fst iv \/ snd iv <= AG_FIELD_TABLE) X -> FT m'.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.asr); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_P_ftab_rep.FT); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_FIELD_TABLE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_P_ftab_rep.FTCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_FIELD_TABLE_GUARD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_P_ftab_rep.FTGuardCells); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.xpres); constr:(HCEIL); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.xpres_rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8SRKit.xclient_range_img); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.aimg_client); constr:(@Stdlib.Lists.List.Forall_impl); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@kc__2 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @x; @y; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @Ha0; @Ha; @a; @p; @__x2; @K; @h; @l; @z; @FX; @XP; @T2; @T1; @H0; @m'; @X; @SP; @LB; @H|] "#P1#0$(#6#i#$#j###h#%#q#=#?#0#o#G#&#<#,#@#C#*#>#-#Q#S#r#F#(#+#/#.#'#K#a#9#B#)#D#R#\#`#W#T#c#d#p#y#z$%$'$&$$$##P#O#8#5#7#V#^#_#b#e#g#t#v#w#{#|#}#x#~$)$(#N#:#3#U#I#J#E#m#l#A#H#Y#n#;#u#k#L#M#X#]#[#f#4#Z#s=#n$#o$#p$#;%#q%#9%#r'#s*#t%#u$#/%#v%#w%#x'#y*#8$#z*#{&#|&#}&#~5$#/$$+$%$$&&$'&:SIVSJCC:#US3E0QIKS&0QILS#+$#[S4S$S%S5S,S0PI%S1$#%#%#$#$#$#$#$#$#$#,#-K#4CCG&$#5CCG&#K'%#j#$;#WS6<#S,US3S0k##$#k##9#j##;#0QPLS#0QS0KS&0QS,LS#[S4S$S'RS-S%S5S,WS6s#%,S-0QS%KS&0QS%LS#US7S&2#&KG-K$(G#+%#$s#&%#%#$#$#$#$#$#$#$#$#$#%#%#$#%#$#$#$#$#,#%S1$#$#%#$#%#%#%#%#%#%#%#%#%#$#$#$#%#$#$#$#$#,#$S1$#%#$#$#$#%#%#%#%#$#%#$#$#$#%#$#$#$#$#,#%4$#%#$#$#$#$#%#$#$#$#$#$#$#$#$#,#%($#$#$#,#%0$#%#%#$#$#$#,#$s#H%#%#%#%#%#%#%#$#$#$#$#%#$#$#$#$#,#%s#]$#$#$#$#$#%#%#$#$#$#$#%#%#$#%#$#$#$#$#,#$s#[%#%#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#,#$s#j%#$#%#$#$#$#%#%#$#%#$#$#$#,#%s$6$#$#$#$#$#%#%#$#$#%#$#$#$#%#$#$#$#,#&s$6E#SK##############################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################2#-sId#(E#+sH2#$sJY%#%#%#%#$#$#$#,#-sIp#(E#+sH>#j#%CGU#'-sIu#(E#.MsHC;MsHDsHDm#$#6sHFsHF#(EGUS8#j#&C#j#%C#.CE-EGXSLCCSM#.C#j#'C#j#(C#.CsJ)2G.C#j#%S2#.C<`S9S2CCCS(S(99$s#*=#7CCCCCCO:::O)sJ/sJ/(s#*9#8CCS);S)0EE/s#*9#ZS:sHYs#*sHY95#XS;s#*>#GUSNS<:S<VS=CEUSOCUSPC/CsJ8VS>CS1)C$N#*&HDDF#J/Cs#+<C'#)C'S*#**HDDF#J3+HDDF'#USQDZSR-HDDFP$S1$#%#$#$#$#%#%#%#%#%#$#%#$#%#%#$#$#$#$#,#/CsJC)C#NB*s#%HDDF#J%7$#%#$#$#$#%#$#%#%#$#$#$#$#$#$#,#/CsJF)Cs#6S*#*s#9HDDF#J3s#:HDDF7#%,$#$#$#,#/CsJJ)C#Ns#?*s#BHDDF#J%9$#$#$#%#%#$#$#$#,#/CsJO)Cs#LS*#*s#OHDDF#J3s#PHDDF0#$sKT$#%#%#%#%#%#%#%#%#%#%#$#%#$#$#$#$#,#/CsJT)C#Ns#c*s#fHDDF#J%sKf%#$#$#%#%#$#$#$#%#$#$#$#$#,#/CsJQ)Cs#uS*#*s#xHDDF#J3s#yHDDF5#1s#zHDDFs#,#1s#{HDDFs#C#1s#|HDDFs#q#9s#}HDDFs#ts#s#VSSs#~F.S?S@VSTGI;S?#S@m$%#WSUCSVEXSWGI$#l#)*)#l#*s$,s$+#l#+s$/s$.#j#,C#j#-M#&sKcG(Gs$R+$#&sKQE(EsKA+$#&sK>E(EsK7+$#&sK'E(EsJo+$#'&#'*#'I#k##/#k#,C#k#-M#$s$3%#%#$#$#%#$#$#$#$#$#$#$#$#$#$#$#$#,#&sJwP$s$C%#$#%#%#$#$#$#$#$#%#$#$#$#,#(PsJx+3#WG#PEl#.s#;s#)#l#/s$ls%,#USXEm#$#j#0sLo#j#1C#&sLssM,'#sM*j#$sMB#4CCE&sLw#5CCE&#K'%#k##sM0#j#2sMI#XSACCEG4CC#&sM9#5CC%&#K'%#&s%OI&EsLV'$#&s%FI'#%&EGUS8#j#&C#j#%C#7CCCCCCOs%Is%Is%IOs%8sL^sL^s%7s%Ys%Ms%2.CI8CCS+s%KS+%s%Zs%N$II#.M-6..#ZSB0/-/%#VS=CIUSYCXSZC$E#/CsMP<Cs%2#)C#Ns%2*s%5HDDF#JVS>Cs%*)C#Ns%6*s%8HDDF#J1s%9HDDF&#)Cs%4Ns%8*s%;HDDF#J1s%<HDDF#&9s%=HDDF&s%3#l#)#s#zs#tl#*0s%@#l#+s%Ds%C#j#,C#j#3C#-sLxsMa&#G'#s#&&s%iE&IsL|'$#k##&#k#,C#k#3C#WGIPEl#.-$#XSCs#.s#,B#-Ks&#&#I&EK'$#m#'#XSACCIE4CC#&sM]#5CC%&#K'%#m#)#j#4s#>#j#5C#j#6C#V#EGj#7C#j#7C#YSDCCs#J#Gj#1sN6#ZSEsN7sMzs#S#RG]SFS$S.S/S'RKsMms#W#`SGS$S.S/S'RS-S%KS&EP#US7S#2#&LG-L$(G#+%#%sMi%#%#$#$#%#$#$#%#$#$#$#,#&sK{E2sKs-sK}#(E#+&#,s$@-sL%#(E#+*#Us&F&-sL)#(E#.M.;M//m#$#611#.CsL/.C.`S9S2CCCS(S(s&Os&Os&:sL(/#7CCCCCCOs&Ps&Ps&POs&?sL2sL2%4,#8CCS)s&QS)s&FEEs&E4,#ZS:747,(#XS;40#G/CsL6)C#Ns&3*s&6HDDF#J/C7<C&#)Cs&7S*#*s&:HDDF#J3s&;HDDF'#9s&<HDDF#s&2s$zl#)#s$ys$sl#*s&@s&?#l#+s&Cs&B#j#,C#j#-M#&sLDG(GB+$#k###s$gk#,C#k#-M#l#.)#s$Al#/8s#&#m##s$@j#0s#>#j#1C#&s#BsNi&sNhL'$#j#$sO$#&s#Fs$@&s$?L'$#k##sNl#j#2sO)#&s#9I&EsLY'$#&s#8I'#%7CCCCCCOs&{s&{s&{Os&jsL]sL]s#0s#?s#;s#.8CCS+s&|S+s$6s#?s#;#IIs$4.M(6))#ZSB+*(*%#)Cs#*Ns&^*s&aHDDF#J)Cs$.Ns#0*s&cHDDF#J1s&dHDDF%#9s&eHDDFs$.s&[#l#)#s%Fs%@l#*s$8s&h#l#+s&ls&k#j#,C#j#3C#&s#JE&IsLn'$#k##s$+#k#,C#k#3C#l#.)#s$'XSC<:5#-Ls#W&#I&EL'$#m#'#&s#ms$%&s$$L'$#m#&#j#4s$_#j#5C#j#6C#V#EGj#7C#j#7C#YSDCCs#/#Gj#1sOW#ZSEsOXsO?s#6#RG]SFS$S.S/S'RLs#|s#;#`SGS$S.S/S'RS-S%LS#EI#XS[sO7sO6s$$#j#8sO9#j#9sO;#j#:sO=#j#;sO?#V#EGj##sOB#j##sO_#YS\sO`sO_sOE#Gj#<sOb#j#=SH#j#'SH#j#>sOf#j#?C#j#@sOj#j#AS]##"). Qed.

Section SR.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis FS0 : stack_malloc_stmt H 0 P_A_FS_MALLOC_0.
  (* [comment removed for export] *)
  Hypothesis EXISTS : token_list_exists_stmt H.

  Definition otf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (P f ecA : Z) (name value : list byte) (E0 : ecv)
      (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (E' : ecv)
                    S' L' ns' ls' em' (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m'
      /\ AFieldsC m' (P + 80) S' L' ns' ls' em' /\ AFieldsOwn LB' em' /\ FT m'
      /\ rw_cells bsegs m' ecA (ErrCodeCells E')
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) (((ecA, ecA + 24) :: (P + 80, P + 80 + 48) :: elemsW L) ++ XS) m m'
      (* [comment removed for export] *)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ accessible m' ecA 24
      /\ as_AL H s' >= as_AL H s - as_Cm H (elem_block_size name (trim value))
      /\ ( (* [comment removed for export] *)
           (s' = s /\ LB' = LB /\ E' = E0 /\ S' = S /\ L' = L /\ ns' = ns /\ ls' = ls /\ em' = em)
           (* [comment removed for export] *)
        \/ (exists (p : bptr) (A : Z) pad tl,
              E' = EC_clear /\ rblock_range A (elem_block_size name (trim value))
              /\ LB' = (p, A, elem_block_size name (trim value)) :: LB
              /\ em' = <[A := mkElt f name (trim value) pad tl]> em /\ (A + 16) ∈ S' /\ A ∈ L') ).

  Definition otf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (P f np vp ecA : Z) (mb : byte) (name value : list byte) (E0 : ecv)
           (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_A_ON_TRAILER_FIELD_IMPL) fc None m (seg_rom bsegs) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 np -> a3 = Z_to_bv 64 (zlength name) ->
      a4 = Z_to_bv 64 vp -> a5 = Z_to_bv 64 (zlength value) -> a6 = Z_to_bv 64 ecA ->
      AFieldsC m (P + 80) S L ns ls em -> AFieldsOwn LB em -> FT m -> rw_cells bsegs m (P + 242) [C1 mb] ->
      bytes_at bsegs m np name -> np + zlength name < 2^64 ->
      bytes_at bsegs m vp value -> vp + zlength value < 2^64 ->
      zlength name <= 65533 -> zlength value <= 65533 -> 0 <= f < 2^16 ->
      rw_cells bsegs m ecA (ErrCodeCells E0) ->
      (ecA + 24 <= P + 80 \/ P + 80 + 48 <= ecA) -> (np + zlength name <= ecA \/ ecA + 24 <= np) -> (vp + zlength value <= ecA \/ ecA + 24 <= vp) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + (zlength name + zlength value + 67) <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - OTF_STACK ->
      rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      (* [comment removed for export] *)
      0 <= P -> aobj LB LF (P + 80) 48 ->
      aobj LB LF (P + 242) 1 -> accessible m (P + 242) 1 ->
      aobj LB LF ecA 24 -> ecA mod 8 = 0 -> accessible m ecA 24 ->
      (forall e d, em !! e = Some d -> ecA + 24 <= e \/ e + esize d <= ecA) ->
      aobj LB LF np (zlength name) -> accessible m np (zlength name) ->
      aobj LB LF vp (zlength value) -> accessible m vp (zlength value) ->
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_Cm H (elem_block_size name (trim value)) <= as_AL H s ->
      (* [comment removed for export] *)
      bv_unsigned mb <= 1 -> (length LF + 1 < AFS_MAXLIVE)%nat ->
      as_SR H (otf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P f ecA name value E0 S L ns ls em lo B shi m mo)
        (mkCfg msF mo).

  Lemma otf_spec : otf_stmt.
  Proof.
    unfold otf_stmt.
    intros until errv. intros VIS -> -> -> -> -> -> -> FC OWN FTm MAT NB NHI VB VHI NL VL FB ECC ECF ECN ECV HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16
                              P0 AOH AOM ACM AOE EAL ACE ECE AON ACN AOV ACV RF LFN AC SK SHI COST MB1 LFN1.
    unfold OTF_STACK, INS_STACK, AOPNEW_STACK, AMALLOC_STACK in LO. pose proof aceil_facts as (AF1 & AF2 & AF3).
    assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; lia).
    subst tp. rewrite EA in ERR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (stack0_bounds _ _ _ SK) as [SKB1 SKB2]. unfold AAPP_HI in SKB2.
    pose proof (bytes_at_bound _ _ _ _ NB) as NBB. pose proof (bytes_at_bound _ _ _ _ VB) as VBB.
    pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOE) as APE.
    pose proof (aapp_bounds _ _ APE ltac:(lia)) as (EB1 & EB2 & EB3 & EB4 & EB5). unfold AIMG_TOP in EB1. unfold AAPP_HI in EB3.
    pose proof FC as (_ & _ & _ & _ & _ & _ & _ & LEm & EOK & ESH & HA & HS).
    pose proof (AHdrA_bounds _ _ HA) as (HB1 & HB2 & HB3 & HB4 & HAL). unfold AIMG_TOP in HB1.
    pose proof (trim_length value) as TVL. pose proof (elem_block_size_range name (trim value)) as SZR.
    set (sz := elem_block_size name (trim value)) in *. unfold zlength in *.
    pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AON) as APN. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOV) as APV.
    pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOH) as APH.
    pose proof (aapp_bounds _ _ APN ltac:(lia)) as (NB1 & NB2 & NB3 & NB4 & NB5). unfold AIMG_TOP in NB1. unfold AAPP_HI in NB3.
    pose proof (aapp_bounds _ _ APV ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5). unfold AIMG_TOP in VB1. unfold AAPP_HI in VB3.
    (* [comment removed for export] *)
    assert (ELB : forall a, a ∈ L -> exists da, em !! a = Some da /\ 60 <= esize da /\ 6832128 <= a /\ a + esize da <= aceil).
    { intros a INa. apply LEm in INa. destruct (em !! a) as [da|] eqn:La; [| exfalso; exact (is_Some_None INa)].
      exists da. pose proof (esize_ge da).
      pose proof (aapp_bounds _ _ (em_ok_aapp _ _ _ EOK La) ltac:(lia)) as (Q1 & Q2 & _). unfold AIMG_TOP in Q1.
      split; [reflexivity|]. split; [lia|]. split; assumption. }
    set (X3 := ((ecA, ecA + 24) :: (P + 80, P + 80 + 48) :: elemsW L)).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS
      | eapply (otf_segA H HH FS0 EXISTS s LB LF P f np vp ecA mb name value S L ns ls em lo shi);
          unfold OTF_SEGA_STACK, AEXISTS_STACK, FINDIF_STACK, TOKIT_STACK, AINTRIN_STACK, zlength;
        [ exact FC | exact OWN | exact FTm | exact MAT | exact NB | exact NHI
        | clear - FB; lia | clear - VBB VHI; lia | clear - VL; lia | clear - EB4 EB3; lia
        | exact ST | clear - LO; lia | exact CEIL | exact MI | exact SP16 | reflexivity | exact AC | exact HP | exact RF | exact LFN
        | exact SK | exact SHI | exact P0 | exact AOH | exact AOM | exact ACM | exact AON | exact ACN | exact MB1 | exact LFN1 ] |].
    intros msF1 mo1 KREL1 MP1 PO. unfold otf_segA_post in PO.
    destruct PO as (kept & rax & x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & s4x & x3 & x4 & x5 & x6 & m2 & ff & fp & spa & gsz
                      & j16 & gj & fj & sh8 & h0 & h1 & h2 & h3 & tlp & tll & XS1
                      & MU & FS1 & WM & MI2 & FC2 & FT2 & HP2 & RF2 & AC2 & SK2 & LIVE & INW & VIS2).
    destruct LIVE as (GAPE & SPA1 & SPA32 & L2 & GAP2 & SAV2 & FH2 & NM2 & FTL2 & SHU2 & FL2 & ST2).
    lazymatch type of MU with munch (?w :: XS1) _ _ => change (munch ([w] ++ XS1) m m2) in MU end.
    destruct (scratch_Forall H HH LF m LB XS1 RF FS1) as (SCW & SCLO & SCHI).
    assert (FX1 : Forall awin [(lo, bv_unsigned sp)]%Z) by (repeat apply Forall_cons; [apply awin_stack; exact CEIL| apply Forall_nil]).
    assert (ERR2 : rw_cells bsegs m2 AERRNO [C4 errv]).
    { eapply (rw_cells_transport bsegs _ m m2); [exact ERR| exact MU| exact WM|]. apply disjoint_from_app2.
      - fit_zsizes; cbn [disjoint_from fst snd cells_size csize Nat.add]. unfold AERRNO, ATP. clear - CEIL AF1. lia.
      - apply SCLO. unfold AERRNO, ATP, AIMG_TOP. cbn. clear. lia. }
    assert (ECC2 : rw_cells bsegs m2 ecA (ErrCodeCells E0)).
    { eapply (rw_cells_transport_scr H HH LF m _ _ m m2); [exact RF| eapply (aobj_fsobj H HH); [exact HP| exact AOE]| exact APE| exact ECC| exact MU| exact WM| | exact FS1].
      unfold ErrCodeCells. fit_zsizes; cbn [disjoint_from fst snd cells_size csize Nat.add]. clear - EB2 CEIL; lia. }
    assert (NB2' : bytes_at bsegs m2 np name).
    { eapply (bytes_at_transport_scr H HH LF m _ _ m m2); [exact RF| intros _; split; [eapply (aobj_fsobj H HH); [exact HP| exact AON]| exact APN]| exact NB| exact MU| | exact FS1].
      cbn [disjoint_from fst snd]. clear - NB2 CEIL; lia. }
    assert (VB2' : bytes_at bsegs m2 vp value).
    { eapply (bytes_at_transport_scr H HH LF m _ _ m m2); [exact RF| intros _; split; [eapply (aobj_fsobj H HH); [exact HP| exact AOV]| exact APV]| exact VB| exact MU| | exact FS1].
      cbn [disjoint_from fst snd]. clear - VB2 CEIL; lia. }
    assert (W1OK : Forall (aclient_write_ok H LB) ([(lo, bv_unsigned sp)]%Z ++ XS1)).
    { apply Forall_app. split; [| exact SCW].
      repeat apply Forall_cons; [exact (proj1 (stack_window_ok' H HH s LB m LF lo _ HP CEIL))| apply Forall_nil]. }
    assert (AUX2 : as_rauxv_ok H m2 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact W1OK]).
    assert (ACE2 : accessible m2 ecA 24)
      by (eapply (accessible_transport_scr H HH LF m _ _ m m2); [exact RF| eapply (aobj_fsobj H HH); [exact HP| exact AOE]| exact APE| clear; lia| exact ACE| exact MU| exact FX1| exact FS1]).
    assert (ACN2 : accessible m2 np (Z.of_nat (length name)))
      by (eapply (accessible_transport_scr H HH LF m _ _ m m2); [exact RF| eapply (aobj_fsobj H HH); [exact HP| exact AON]| exact APN| clear; lia| exact ACN| exact MU| exact FX1| exact FS1]).
    assert (ACV2 : accessible m2 vp (Z.of_nat (length value)))
      by (eapply (accessible_transport_scr H HH LF m _ _ m m2); [exact RF| eapply (aobj_fsobj H HH); [exact HP| exact AOV]| exact APV| clear; lia| exact ACV| exact MU| exact FX1| exact FS1]).
    (* [comment removed for export] *)
    assert (XP2 : forall XS', xpres H LB (bv_unsigned sp) (X3 ++ (XS1 ++ XS')) m m2).
    { intros XS'. eapply xpres_of_munch_gen; [exact MU| exact WM|].
      intros a Ha [HC NR].
      pose proof (aclient_addr_range H _ _ _ HC) as HR.
      assert (Q01 : 0 < 1) by (clear; lia).
      pose proof (aclient_range_off_frame H HH _ _ _ _ _ _ lo HP HR CEIL Q01) as OF.
      rewrite !rin_ivs_app in NR.
      apply (proj2 (outside_app _ _ _)). split.
      - cbn [outside fst snd]. split; [clear - OF; lia| exact I].
      - apply outside_of_not_rin. intros K. apply NR. right. left. exact K. }
    (* [comment removed for export] *)
    pose proof (fresh_of_RFS _ HH _ _ _ _ _ RF2) as FF.
    pose proof (ff_facts _ _ _ _ _ FF) as (_ & _ & _ & _ & F1 & F2 & F3 & _ & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & APF & APP1 & SHFF & SF1 & SF2 & SF3 & NSB).
    fs_nums_in F2. fs_nums_in F9. fs_nums_in SF2. fs_nums_in SF3.
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, AHI_LO in F1, F2, F4, F5, F6, F7, F8, F9, F10, F11, SF1, SF2, SF3.
    rewrite <- SHFF in SF1, SF2, SF3.
    pose proof (aapp_not_shadowland _ _ APF) as NSF. fs_nums_in NSF. unfold ALOWSH_LO, AHI_LO in NSF.
    assert (FOF : fsobj H ((0, ff, fp) :: LF) ff 64)
      by (eapply (fsobj_inframe H); [left; reflexivity| unfold ff_addr; cbn [fst snd]; clear; lia| unfold ff_addr, ff_class; cbn [fst snd]; change (fsz 0) with 64; clear; lia]).
    assert (APF64 : aapp ff 64) by (change 64 with (fsz 0); exact APF).
    (* [comment removed for export] *)
    assert (RET : forall (s' : as_St H) (LB' : list block) (E' : ecv) S' L' ns' ls' em' (XS : list (Z * Z)) msF3 mo3 (m3 : mem) (errv3 : word)
        (rax' y0 y1 y2 c0 c1 c2 c3 c4 c5 c6 c7 s1' s4' s5' s6' s7' s8' s9' s10' y3 y4 y5 y6 h0' h1' h2' h3' n0 n1 l1 l2 l3 l4 l5 : word)
        (j16' fj' sh8' : list byte) (bflag : byte),
      as_AKREL H s' (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
      as_VIS H s' msF3 = MS (mkR rax' (Z_to_bv 64 spa) gp (Z_to_bv 64 ATP) y0 y1 y2 sp s1' c0 c1 c2 c3 c4 c5 c6 c7
                              (Z_to_bv 64 (Z.shiftr ff 3 + 2147450880)) (Z_to_bv 64 ff) s4' s5' s6' s7' s8' s9' s10' (Z_to_bv 64 ff) y3 y4 y5 y6)
                          F (Z_to_bv 64 P_A_OTF_RET) fc None m3 (seg_rom bsegs) ->
      rw_cells bsegs m3 spa [CB 16 j16'; C8 l1; C8 l2; C8 l3; C8 l4; C8 l5] ->
      rw_cells bsegs m3 (spa + 56) [CB gsz gj] ->
      rw_cells bsegs m3 (bv_unsigned sp + -104) (otf_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      rw_cells bsegs m3 ff [C8 h0'; C8 h1'; C8 h2'; C8 h3'] ->
      rw_cells bsegs m3 (ff + 32) [C8 n0; C8 n1] ->
      rw_cells bsegs m3 (ff + 48) [CB 8 fj'; C8 (Z_to_bv 64 fp)] ->
      rw_cells bsegs m3 (Z.shiftr ff 3 + 2147450880) [CB 8 sh8'] ->
      rw_cells bsegs m3 fp [C1 bflag] ->
      stk bsegs m3 lo spa -> mem_inv bsegs m3 ->
      as_RFS H ((0, ff, fp) :: LF) m3 -> ACONST m3 -> stack0 m3 lo shi ->
      as_RHEAP H s' LB' m3 -> as_rauxv_ok H m3 B -> rw_cells bsegs m3 AERRNO [C4 errv3] ->
      AFieldsC m3 (P + 80) S' L' ns' ls' em' -> AFieldsOwn LB' em' -> aobj LB' LF (P + 80) 48 -> FT m3 ->
      rw_cells bsegs m3 ecA (ErrCodeCells E') -> accessible m3 ecA 24 -> aobj LB' LF ecA 24 ->
      Forall (fs_scratch H LF) XS -> xpres H LB (bv_unsigned sp) (X3 ++ XS) m m3 ->
      (forall a, rin_ivs (otf_retW ff fp) a -> rin_ivs XS a) ->
      as_AL H s' >= as_AL H s - as_Cm H sz ->
      ((s' = s /\ LB' = LB /\ E' = E0 /\ S' = S /\ L' = L /\ ns' = ns /\ ls' = ls /\ em' = em)
       \/ (exists (p : bptr) (A : Z) pad tl, E' = EC_clear /\ rblock_range A sz /\ LB' = (p, A, sz) :: LB
             /\ em' = <[A := mkElt f name (trim value) pad tl]> em /\ (A + 16) ∈ S' /\ A ∈ L')) ->
      as_SR H (otf_post ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P f ecA name value E0 S L ns ls em lo B shi m mo)
        (mkCfg msF3 mo3)).
    { intros s' LB' E' S' L' ns' ls' em' XS msF3 mo3 m3 errv3 rax' y0 y1 y2 c0 c1 c2 c3 c4 c5 c6 c7 s1' s4' s5' s6' s7' s8' s9' s10' y3 y4 y5 y6 h0' h1' h2' h3' n0 n1 l1 l2 l3 l4 l5
             j16' fj' sh8' bflag KREL3 MP3 VIS3 L3 GAP3 SAV3 FH3 NM3 FTL3 SHU3 FL3 ST3 MI3 RF3 AC3 SK3 HP3 AUX3 ERR3 FC3 OWN3 AOH3 FT3 ECC3 ACE3 AOE3 FSX XPX INWX ALX DISJ.
      pose proof (Forall_inv_tail (fs_scratch_of_fresh H LF 0 ff fp FF)) as FSr. change (fsz 0) with 64 in FSr. change (fshn 0) with 8 in FSr.
      destruct (scratch_Forall H HH LF m LB' _ RF FSr) as (SCWr & SCLOr & SCHIr).
      eapply (ahh_evt H HH); [exact KREL3| exact VIS3
        | eapply (otf_retire H HH (fun m4 => as_RHEAP H s' LB' m4 /\ as_rauxv_ok H m4 B /\ rw_cells bsegs m4 AERRNO [C4 errv3]
                                              /\ AFieldsC m4 (P + 80) S' L' ns' ls' em' /\ FT m4 /\ rw_cells bsegs m4 ecA (ErrCodeCells E')
                                              /\ accessible m4 ecA 24 /\ xpres H LB (bv_unsigned sp) (X3 ++ XS) m m4));
          [ exact L3 | exact GAP3 | exact SAV3 | exact FH3 | exact NM3 | exact FTL3 | exact SHU3 | exact FL3 | exact ST3 | exact MI3
          | exact RF3 | exact AC3 | exact SK3 | | exact GAPE | exact SPA1 | clear - LO; lia | exact CEIL ] |].
      { (* [comment removed for export] *)
        intros m4 MUr WMr. unfold otf_retW in MUr.
        assert (MUr' : munch ([] ++ [(fp, fp + 1); (ff, ff + 64); (sh ff, sh ff + 8)])%Z m3 m4)
          by (eapply munch_weaken; [| exact MUr]; cbn [app]; intros xa OO; cbn [outside fst snd] in OO |- *; rewrite <- SHFF in OO; clear - OO; lia).
        assert (FX0 : Forall awin (@nil (Z * Z))) by apply Forall_nil.
        split. { eapply (RHEAP_transport_scr H HH s' LB' LF m); [exact HP3| exact RF| exact MUr'| exact WMr| apply Forall_nil| exact FSr]. }
        split. { eapply (ah_rauxv_frame H HH); [exact AUX3| exact MUr'| exact WMr| cbn [app]; exact SCWr]. }
        split. { eapply (rw_cells_transport bsegs _ m3 m4); [exact ERR3| exact MUr'| exact WMr|]. cbn [app]. apply SCLOr. unfold AERRNO, ATP, AIMG_TOP. cbn. clear. lia. }
        split. { eapply (AFieldsC_transport_scr H HH s' LB' m3 LF m); [exact HP3| exact RF| exact FC3| exact OWN3| exact AOH3| exact MUr'| exact WMr| exact FX0| exact FSr| cbn; exact I|].
                 intros e d Ld. cbn. exact I. }
        split. { eapply FT_transport; [exact FT3| exact MUr'| exact WMr|]. cbn [app]. apply SCLOr. unfold AG_FIELD_TABLE, AIMG_TOP. clear; lia. }
        pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP3 RF AOE3) as APE3.
        split. { eapply (rw_cells_transport_scr H HH LF m _ _ m3 m4); [exact RF| eapply (aobj_fsobj H HH); [exact HP3| exact AOE3]| exact APE3| exact ECC3| exact MUr'| exact WMr| cbn; exact I| exact FSr]. }
        split. { eapply (accessible_transport_scr H HH LF m _ _ m3 m4); [exact RF| eapply (aobj_fsobj H HH); [exact HP3| exact AOE3]| exact APE3| clear; lia| exact ACE3| exact MUr'| exact FX0| exact FSr]. }
        eapply xpres_trans; [exact XPX|].
        eapply xpres_of_munch_gen; [exact MUr| exact WMr|].
        intros a Ha [HC NR]. apply outside_of_not_rin. intros K. apply NR. apply rin_ivs_app. right. apply INWX. unfold otf_retW. exact K. }
      intros msF4 mo4 KREL4 MP4 PO4.
      destruct PO4 as (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & RF4 & AC4 & SK4
                        & HP4 & AUX4 & ERR4 & FC4 & FT4 & ECC4 & ACE4 & XP4).
      unfold otf_post. cbn [cfg_ms cfg_model].
      do 15 eexists. exists m4, errv3, s', LB', E', S', L', ns', ls', em', XS.
      split; [exact VIS4|]. split; [exact KREL4|]. split; [eapply (ah_mpres_trans H HH); [exact MP3| exact MP4]|].
      split; [exact MI4|]. split; [exact ST4|]. split; [rewrite EA; exact ERR4|]. split; [exact AUX4|]. split; [exact HP4|].
      split; [exact FC4|]. split; [exact OWN3|]. split; [exact FT4|]. split; [exact ECC4|]. split; [exact FSX|]. split; [exact XP4|].
      split; [exact RF4|]. split; [exact AC4|]. split; [exact SK4|]. split; [exact ACE4|]. split; [exact ALX|]. exact DISJ. }
    destruct kept.
    all: cycle 1.
    - (* [comment removed for export] *)
      eapply (RET s LB E0 S L ns ls em XS1 msF1 mo1 m2 errv);
        [ exact KREL1 | exact MP1 | exact VIS2
        | exact L2 | exact GAP2 | exact SAV2 | exact FH2 | exact NM2 | exact FTL2 | exact SHU2 | exact FL2 | exact ST2 | exact MI2
        | exact RF2 | exact AC2 | exact SK2 | exact HP2 | exact AUX2 | exact ERR2 | exact FC2 | exact OWN | exact AOH | exact FT2 | exact ECC2 | exact ACE2 | exact AOE
        | exact FS1 | pose proof (XP2 []) as K; rewrite app_nil_r in K; exact K | exact INW
        | pose proof (proj1 (ah_costs H HH) sz ltac:(clear - SZR; lia)) as K; clear - K; lia
        | left; repeat split; reflexivity ].
    - (* [comment removed for export] *)
      pose proof (aobj_LF_mono LB LF ((0, ff, fp) :: LF) _ _ AOH ltac:(intros g IN; right; exact IN)) as AOH'.
      pose proof (aobj_LF_mono LB LF ((0, ff, fp) :: LF) _ _ AOE ltac:(intros g IN; right; exact IN)) as AOE'.
      pose proof (aobj_LF_mono LB LF ((0, ff, fp) :: LF) _ _ AON ltac:(intros g IN; right; exact IN)) as AON'.
      pose proof (aobj_LF_mono LB LF ((0, ff, fp) :: LF) _ _ AOV ltac:(intros g IN; right; exact IN)) as AOV'.
      pose proof (ins_spec H HH FS0) as IS. unfold ins_stmt, ins_stmt_at in IS.
      eapply (ah_seq H HH).
      { eapply IS with (msF := msF1) (m := m2) (mo := mo1) (s := s) (LB := LB) (LF := (0, ff, fp) :: LF) (P := P + 80) (f := f) (np := np) (vp := vp) (ecA := ecA)
                       (name := name) (value := value) (E0 := E0) (S := S) (L := L) (ns := ns) (ls := ls) (em := em) (lo := lo) (B := B) (shi := shi) (errv := errv)
                       (sp := Z_to_bv 64 spa);
          rewrite ?Z.add_0_r; rewrite ?unsigned_lit by (clear - SPR LO CEIL AF1 SPA1 GAPE; lia); unfold zlength;
          [ exact VIS2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | exact FC2 | exact OWN | exact NB2' | exact VB2' | exact VHI | exact NL | exact VL | exact FB | exact ECC2
          | exact ECF | exact ECN | exact ECV | exact HP2 | exact KREL1 | exact BUD | exact BUDC | exact AUX2
          | clear - SPB SPA1 GAPE; lia | exact ST2 | exact CEIL | unfold INS_STACK, AOPNEW_STACK, AMALLOC_STACK; clear - LO SPA1 GAPE; lia
          | rewrite EA; exact ERR2 | exact MI2 | reflexivity
          | clear - SPA32; Z.div_mod_to_equations; lia
          | clear - P0; lia | exact AOH' | exact AOE' | exact EAL | exact ACE2 | exact ECE | exact AON' | exact ACN2 | exact AOV' | exact ACV2
          | exact RF2 | cbn [length]; clear - LFN1; lia | exact AC2 | exact SK2 | clear - SHI SPA1 GAPE; lia | exact COST ]. }
      intros [ms3 mo3] PO. unfold ins_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.add_0_r in PO. fold sz in PO.
      destruct PO as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m3 & errv3 & sI & p & A & pad & tl & S' & L' & ns' & ls' & XS2
                      & VIS3 & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & BR & HP3 & FC3 & INS & INL & OWN3 & ECC3 & FS2 & XP3 & RF3 & AC3 & SK3 & ACE3 & AL3).
      rewrite (unsigned_lit spa) in ST3, XP3 by (clear - SPR LO CEIL AF1 SPA1 GAPE; lia).
      destruct (scratch_Forall H HH ((0, ff, fp) :: LF) m2 LB XS2 RF2 FS2) as (SCW2 & SCLO2 & SCHI2).
      fold X3 in XP3.
      (* [comment removed for export] *)
      pose proof (fsobj_windows H HH LF ecA 24 0 ff fp _ RF (aobj_fsobj H HH _ _ _ _ _ _ HP AOE) FF ltac:(clear - EB4; lia) ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - EB3; lia)) as (DE1 & DE2 & DE3 & _).
      pose proof (fsobj_windows H HH LF (P + 80) 48 0 ff fp _ RF (aobj_fsobj H HH _ _ _ _ _ _ HP AOH) FF ltac:(clear - P0; lia) ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - HB3; lia)) as (DH1 & DH2 & DH3 & _).
      change (fsz 0) with 64 in DE1, DH1. change (fshn 0) with 8 in DE2, DH2. rewrite <- SHFF in DE2, DH2.
      assert (DL : forall a, a ∈ L -> exists da, em !! a = Some da /\ 60 <= esize da /\ (a + esize da <= ff \/ ff + 64 <= a)
                     /\ (sh a + nsh (esize da) <= Z.shiftr ff 3 + 2147450880 \/ Z.shiftr ff 3 + 2147450880 + 8 <= sh a) /\ (a + esize da <= fp \/ fp + 1 <= a)).
      { intros a INa. destruct (ELB a INa) as (da & La & G & Ra & Rb). exists da. split; [exact La|].
        destruct (OWN a da La) as (pa & INb & _).
        pose proof (fsobj_windows H HH LF a (esize da) 0 ff fp _ RF (fsobj_block H HH _ _ _ LF _ _ _ HP INb) FF ltac:(clear - Ra; lia) ltac:(clear - G; lia)
                      ltac:(unfold AAPP_HI; clear - Rb AF1 AF3; lia)) as (D1 & D2 & D3 & _).
        change (fsz 0) with 64 in D1. change (fshn 0) with 8 in D2. rewrite <- SHFF in D2. split; [exact G| split; [exact D1| split; [exact D2| exact D3]]]. }
      (* [comment removed for export] *)
      assert (XHI : forall A cs, rw_cells bsegs m2 A cs -> spa <= A -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells bsegs m3 A cs).
      { intros Ax cs C HAx HBx. eapply (rw_cells_xpres_hi H); [exact XP3| exact C| exact HAx|].
        apply Forall_app. split.
        - apply Forall_cons; [right; cbn [fst snd]; clear - HAx EB2 CEIL LO SPA1 GAPE; lia|].
          apply Forall_cons; [right; cbn [fst snd]; clear - HAx HB2 CEIL LO SPA1 GAPE; lia|].
          apply Forall_forall. intros [u v] INuv. apply in_map_iff in INuv. destruct INuv as (a & Euv & INa). injection Euv as <- <-.
          destruct (ELB a ltac:(apply (proj2 (list_elem_of_In _ _)); exact INa)) as (da & _ & G & _ & Ra). right. cbn [fst snd]. clear - HAx G Ra CEIL LO SPA1 GAPE. lia.
        - apply (proj1 (disjoint_from_Forall _ _ _)). apply SCHI2. clear - HAx CEIL LO SPA1 GAPE. lia. }
      pose proof (XHI _ _ L2 ltac:(clear; lia) ltac:(unfold otf_locals; cbn [cells_size csize Nat.add]; clear - SPA1 GAPE; lia)) as L3.
      pose proof (XHI _ _ GAP2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - SPA1 GAPE; lia)) as GAP3.
      pose proof (XHI _ _ SAV2 ltac:(clear - SPA1 GAPE; lia) ltac:(unfold otf_saved; cbn [cells_size csize Nat.add]; clear; lia)) as SAV3.
      (* [comment removed for export] *)
      assert (XFR : forall A cs, rw_cells bsegs m2 A cs -> ff <= A -> A + Z.of_nat (cells_size cs) <= ff + 64 -> rw_cells bsegs m3 A cs).
      { intros Ax cs C HAx HBx. eapply (xpres_rw_cells H); [exact XP3| exact C|]. split.
        - right; right; right; right; left. clear - HAx HBx F8 F9. unfold AFS_SIZE. lia.
        - apply Forall_app. split.
          + apply Forall_cons; [cbn [fst snd]; clear - HAx HBx DE1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - HAx HBx DH1; lia|].
            apply Forall_forall. intros [u v] INuv. apply in_map_iff in INuv. destruct INuv as (a & Euv & INa). injection Euv as <- <-.
            destruct (DL a ltac:(apply (proj2 (list_elem_of_In _ _)); exact INa)) as (da & La & G & D1 & _ & _). cbn [fst snd].
            clear - HAx HBx D1 G. lia.
          + pose proof (Forall_scratch H HH _ m2 XS2 ff 64 RF2 FOF ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - NSF F2 AF1 AF3; lia) APF64 FS2) as K.
            eapply Forall_impl; [| exact K]. intros [u v] Q. cbn [fst snd] in *. clear - Q HAx HBx. lia. }
      pose proof (XFR _ _ FH2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as FH3.
      pose proof (XFR _ _ NM2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as NM3.
      pose proof (XFR _ _ FTL2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as FTL3.
      (* [comment removed for export] *)
      assert (SHU3 : rw_cells bsegs m3 (Z.shiftr ff 3 + 2147450880) [CB 8 sh8]).
      { eapply (xpres_rw_cells H); [exact XP3| exact SHU2|]. cbn [cells_size csize Nat.add]. split.
        - right; right; right; right; right; left. rewrite SHFF.
          pose proof (sh_mono (as_FSB H) ff ltac:(clear - F8; lia)) as M1.
          pose proof (sh_mono (ff + 64) (as_FSB H + AFS_SIZE) ltac:(unfold AFS_SIZE; clear - F9; lia)) as M2.
          pose proof (sh_add8 ff 8) as A8. replace (ff + 8 * 8) with (ff + 64) in A8 by (clear; lia). change (Z.of_nat 8) with 8. clear - M1 M2 A8. lia.
        - apply Forall_app. split.
          + pose proof (aapp_not_shadowland _ _ APE) as NE. pose proof (aapp_not_shadowland _ _ APH) as NHd. unfold ALOWSH_LO, AHI_LO in NE, NHd.
            apply Forall_cons; [cbn [fst snd]; clear - NE SF1 SF2; lia|]. apply Forall_cons; [cbn [fst snd]; clear - NHd SF1 SF2; lia|].
            apply Forall_forall. intros [u v] INuv. apply in_map_iff in INuv. destruct INuv as (a & Euv & INa). injection Euv as <- <-.
            destruct (DL a ltac:(apply (proj2 (list_elem_of_In _ _)); exact INa)) as (da & La & G & _ & _ & _). cbn [fst snd].
            pose proof (aapp_not_shadowland _ _ (em_ok_aapp _ _ _ EOK La)) as Na. unfold ALOWSH_LO, AHI_LO in Na. clear - Na G SF1 SF2. lia.
          + pose proof (Forall_scratch_sh H HH _ m2 XS2 ff 64 RF2 FOF ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - NSF F2 AF1 AF3; lia) APF64 FS2) as K.
            rewrite <- SHFF in K. change (nsh 64) with 8 in K. exact K. }
      assert (FL3 : rw_cells bsegs m3 fp [C1 (b8 1)]).
      { eapply (xpres_rw_cells H); [exact XP3| exact FL2|]. cbn [cells_size csize Nat.add]. split.
        - right; right; right; right; left. clear - F6 F7. unfold AFS_SIZE. lia.
        - apply Forall_app. split.
          + apply Forall_cons; [cbn [fst snd]; clear - DE3; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DH3; lia|].
            apply Forall_forall. intros [u v] INuv. apply in_map_iff in INuv. destruct INuv as (a & Euv & INa). injection Euv as <- <-.
            destruct (DL a ltac:(apply (proj2 (list_elem_of_In _ _)); exact INa)) as (da & La & G & _ & _ & D3). cbn [fst snd]. clear - D3 G. lia.
          + eapply Forall_impl; [| exact FS2]. intros iv K. exact (scratch_flag H HH _ _ _ _ _ _ RF2 K). }
      replace (ret_pc (Z_to_bv 64 P_A_OTF_RET)) with (Z_to_bv 64 P_A_OTF_RET) in VIS3
        by (symmetry; apply ret_pc_even; [unfold P_A_OTF_RET; clear; lia| reflexivity]).
      rewrite EA in ERR3.
      assert (FT3 : FT m3).
      { eapply (AFT_xpres H); [exact FT2| exact XP3|]. apply Forall_app. split.
        - apply Forall_cons; [left; cbn [fst snd]; unfold AG_FIELD_TABLE; clear - EB1; lia|].
          apply Forall_cons; [left; cbn [fst snd]; unfold AG_FIELD_TABLE; clear - HB1; lia|].
          apply Forall_forall. intros [u v] INuv. apply in_map_iff in INuv. destruct INuv as (a & Euv & INa). injection Euv as <- <-.
          destruct (ELB a ltac:(apply (proj2 (list_elem_of_In _ _)); exact INa)) as (da & _ & _ & Q & _). left. cbn [fst snd]. unfold AG_FIELD_TABLE. clear - Q. lia.
        - apply (proj1 (disjoint_from_Forall _ _ _)). apply SCLO2. unfold AG_FIELD_TABLE, AIMG_TOP. clear. lia. }
      eapply (RET sI ((p, A, sz) :: LB) EC_clear S' L' ns' ls' _ (XS1 ++ XS2) ms3 mo3 m3 errv3);
        [ exact KREL3 | eapply (ah_mpres_trans H HH); [exact MP1| exact MP3] | exact VIS3
        | exact L3 | exact GAP3 | exact SAV3 | exact FH3 | exact NM3 | exact FTL3 | exact SHU3 | exact FL3 | exact ST3 | exact MI3
        | exact RF3 | exact AC3 | exact SK3 | exact HP3 | exact AUX3 | exact ERR3 | exact FC3 | exact OWN3
        | apply aobj_cons; exact AOH | exact FT3 | exact ECC3 | exact ACE3 | apply aobj_cons; exact AOE
        | apply Forall_app; split; [exact FS1| eapply Forall_scratch_pop; exact FS2]
        | | intros a K; apply rin_ivs_app; left; exact (INW a K)
        | exact AL3
        | right; exists p, A, pad, tl; split; [reflexivity|]; split; [exact BR|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact INS| exact INL] ].
      (* [comment removed for export] *)
      eapply xpres_trans; [exact (XP2 XS2)|].
      eapply xpres_weaken; [exact XP3| clear - SPA1 GAPE; lia| intros b Hb; exact Hb|].
      intros a K. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K| right; apply rin_ivs_app; right; exact K].
  Qed.
End SR.
End HCW.



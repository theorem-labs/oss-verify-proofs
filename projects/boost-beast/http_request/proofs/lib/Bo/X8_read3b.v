(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst X8_rsfree X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_A_kit4 X8_S_kit3 X8_S_rsD X8_R_read X8_R_readB X8_read_stmt X8_read2 X8_read3.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W2_objwin : forall lo (sp : word) fb E ff fp, aceil <= lo ->
  Forall (objwin H (bv_unsigned sp + -104) fb E ff fp) (rs_W2 lo sp fb ff fp).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(HCEIL); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read2.objwin); constr:(H); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read2.fwin); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.as_FSB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.AFS_FLAGS); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@Corelib.Lists.ListDef.Forall); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_R_readB.rs_W2)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @CEIL; @fp; @ff; @E; @fb; @sp; @lo|] "#'R#+#j#.#%#U#$###'#&#V#T#9#Z#[#2#(#)#5#;#A#B#C#L#O#Y#`#a#0#/#4#7#<#8#M#P#N#Q#S#\#R#]#b#c#d#^#*#h#i#j#l#k#3#1#E#H#:#g#=#I#@#X#W#>#f#e#F#G#J#D#6#?#K#_:#T%#U$#V%#W%#X%#Y&#Z$#[&#\$#]'#^*#_'#`%#a&#b&#c&#d'#e&#f)#g&#'$#h'#i%$O$#$#$#$#$#US,#US-#US.R##PVS/CCVS#'P)O$#)#$#$#$#US0#'*#[S1RL#HIDF.CCQ$+6'H#$-$#+#'H#.CC'#+:'S$#.CCS$#'D,.CCD#+8VS%D#):)#)#)#)#)#)#)#)#)#)#)#)#)#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#+#'A#+s#A'$#.CC%#+O'F#.CCF#US&s#A6s#B$#6s#C(#6s#Ds#-#6s#Es#0#6s#Fs#4#1CCs#<#s#J#2CCs#>##s#A%%##H'$s#>+#'H##)#%'##I-'Is#C#-#%%#*s#Vs#Ks#A3LDFs#L&$#&&#&+##s#]Q#s#Ss#SUS&S'US2S'VS(CDUS3CXS4C$F#US5CUS6CVS)COVS)Cs#o,C$M#-&KEEJ#NUS7E\S8(KEEJ$#$VS9)J9S*S+VS:GD*S*#S+m$%#WS;CS<FXS=GD$#l#$*)#l#%32#l#&87#j#'C#j#(C##GF#FDk##$#k#'C#k#(C#WGS>s#}Fl#))$#m##s#$VS(CF/Cs#w0C>#,C#M#-AKEEJ#Nl#$#;5l#%(s#$#l#&s#*s#)#j#'C#'Gs$####k#'C#VS#s$2Q7#l#)(%#m##s#38s#5s#43#%s#6s#5m#$#m##s#H4s#Is#:#1CCs$%#s$:#2CCs$'##s$1%%##H'#&s#L%$##I*#)s#K%$#*s$Bs$0s$-3LDFs$1&$#&&#&*##Hs$:#s$7s#W/Cs$=0Cs#D#,Cs#EM#-s#GKEEJ#Nl#$#s#As#;l#%s#.s#J#l#&s#Ps#O#j#'C#'Gs$E#G#k#'C#7Pl#)'$#m##1/Cs$G0Cs#R#/Cs#i0Cs#T#,C%M#-s#WKEEJ#Nl#$#s#Qs#Kl#%s#>s#Z#l#&s#`s#_#j#'C#'Gs$Q'Gs#r#$#k#'C#l#)'#3m##@8BA3#%s##Bm#$#m##s#.4s#/s#(#(s#3s#(#1CCs$X#s$p#2CCs$Z##s$g%%##H'#&s$&%$##I*#)s$%%$#*s$xs$cs$c3LDFs$d&$#&&#&*#9s$}s$h4('#(*'#(.'#(2'#1CCs$k#s%)#2CCs$m##s$|%%##H'#&s$;%$##I*#)s$:%$#*s%1s$vs$x3LDFs$w&$#&&#&*##D2$s%<$#+#'D##5#%(#*s%=s%&s$[#s$b:#9s$a%$#US?L'#S@.CC$#*s%Ds%-#&'#&+##DD#s%20,Cs$CMs$C-s$EKEEJ#Nl#$#s$?s$9l#%s$,s$H#l#&s$Ns$M#j#'C##GGk#'C#7Il#)&$#m##./C=0Cs$O#,Cs#jM#-s$RKEEJ#Nl#$#s$Ls$Fl#%s$9s$U#l#&s$[s$Z#j#'C#'Gs#%#s#j#k#'C#l#)&#0m##:8<;0#%=<m#$#m##s#*4s#+A#(s#7s#6#(s#9s#6#(s#=s#6#(s#As#6#1CCs%/#s%m#2CCs%1##s%d%%##H'#&s%#%$##I*#)s$~%$#*s%us%:s%`3LDFs%;&$#&&#&*##D2#1s#C%$#*s%}s%Bs%?#s%F6#5s%E%$#*s&%s%Fs#@&$#&(##s%Ls%L#s%Ks%K/Cs%O0Cs%%#,C#M#-s%(KEEJ#Nl#$#s$~s$xl#%s$ks%+#l#&s%1s%0#j#'C#'Gs%W###k#'C#VS%Is%y7#l#)(%#m##2/Cs%\0C1#,C#M#-s%7KEEJ#Nl#$#s%1s%+l#%s$zs%:#l#&s%@s%?#j#'C#'1s%d###k#'C#l#)&#0m##>8@?0#%A@m#$#m##s#'4s#(s#'#(s#,s#'#(s#.s#'#(s#6s#5#(s#8s#5#(s#<s#5#(s#@s#5#1CCs%o#s&T#2CCs%q##s&K%%##H'#&s%f%$##I*#)s%e%$#*s&\s%zs&G3LDFs%{&$#&&#&*##D2#1s$*%$#*s&ds&&s&&#s&-6#5s&,%$#*s&hs&*s$'&$#&(#9s&ks&-4*%#(,%#(43#(63#(:3#(>3#VSAs&rs&h5s&ss&is&5s&4$#5s&ts&js&9s&4s#&#5s&us&ks&^s&4s#j#5s&vs&ls&as&4s$S#5s&ws&ms&es&4s$i#5s&xs&ns&ms&4s%D#YSBQPHDFWSCs&zs&p#m#%#j#*s&}#j#+C#j#,C#j#-C#j#.C#j#/s'(#j#0C##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rs_put_tail : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> bv_unsigned ra mod 2 = 0 ->
  rs_at_putret H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (fun cf' => rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf'
                      \/ exists w', zlength (w_sds w') = zlength (w_sds w)
                           /\ rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w' cf') cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC RA AT.
  destruct C as [bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag].
  destruct cf as [msF mo]. unfold rs_at_putret, rs_frames in AT. unfold rs_static in STC. unfold rs_placed in PLC.
  cbn_w_all. cbn [cfg_ms cfg_model] in AT |- *.
  destruct STC as (AOP & AOE & AOF & P8 & E8 & BS8 & FB8 & SEPPE & SEPPF & SEPEF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL & MB1).
  destruct PLC as (SOB & LOS & SP16 & SPHI & SPB & SPC & FRB128).
  destruct AT as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s5x & s6x & t3 & t4 & t5 & t6 & m & s & errv & E2 & tot & d2 & q & spa & ff & fp & mw80 & tmp & gap & hw & optc & j56 & ectc & j120 & XS
                  & VIS & KREL & MP & RM & RP2 & ALK & ST & (FRM & SAVED & FR0 & SZFR & FAKE) & FF & (me & RF0) & FXS & FRX & XP0 & TOT0 & TOT & NRB & SZ1 & QR & EOUT2 & PROG & ST11 & WM0).
  destruct d2 as [c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 A2].
  unfold RWmF, pst_ret in RM. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct RM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP & ERR & AUX & MI & RF' & AC & SK & ATH & ACP & ACE & SVE & ACB & ACF & SVA).
  set (LB := (LBn2 ++ LBn) ++ LBin) in *.
  assert (SUBin : forall b, In b LBin -> In b LB) by (intros b Hb; unfold LB; apply in_or_app; right; exact Hb).
  pose proof RP2 as RPc. unfold RWp, w_after_put, pst_ret in RPc. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in RPc.
  destruct RPc as (_ & OWN & MOWN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STRM & SZS & NRK & CPM & _).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof aceil_facts as (AF1 & AF2 & AF3). unfold HREAD_STACK in LOS. pose proof BPUT_STACK_val as BSV.
  assert (AIS : AINTRIN_STACK = 4096) by reflexivity.
  subst tp. assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; clear; lia). rewrite EA in ERR.
  pose proof SOB as SOB0. unfold sobj in SOB.
  assert (HI : aceil <= bv_unsigned sp + -104) by (clear - CEIL LOS BSV; lia).
  destruct FRM as ((jl & LOW) & SLOTS & MW80 & MSZ & SH16 & (j96 & J96) & F120 & TMP & TSZ & GAP & GSZ & SPA).
  set (LF' := (2, ff, fp) :: LF) in *.
  assert (SUBF : forall f, In f LF -> In f LF') by (intros f Hf; right; exact Hf).
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & SF1 & SA & M1 & M2 & LSH & SHH & SIDE & APFF & APP1 & APB).
  (* [comment removed for export] *)
  assert (NE : FB <> FB_empty) by (intros ->; cbn in SZ1; unfold fb_size in SZ1; cbn in SZ1; clear - SZ1; lia).
  destruct (fb_window H HH _ _ LF _ _ _ _ HP FBU NE) as (_ & _ & _ & _ & [pf INf] & BPOS & CPOS & BTOP & BCE & BAP & BIO & BOLE & FSZ).
  pose proof FBU as (FBC & FOK & _ & BLK & ADR). destruct (BLK NE) as (pre & bj & BCH).
  unfold fb_size, fb_cap in *.
  (* [comment removed for export] *)
  pose proof (aobj_LB_mono _ LB _ _ _ AOP ltac:(intros b [])) as AOPn. pose proof (aobj_LB_mono _ LB _ _ _ AOE ltac:(intros b [])) as AOEn.
  pose proof (aobj_LB_mono _ LB _ _ _ AOF ltac:(intros b [])) as AOFn.
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOPn) as APP0. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOEn) as APE. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOFn) as APF.
  pose proof (aapp_sub _ _ P PARSER_SIZE APP0 ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear; lia)) as APP.
  pose proof (aapp_bounds _ _ APP0 ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (aapp_bounds _ _ APE ltac:(clear; lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (aapp_bounds _ _ APF ltac:(clear; lia)) as (T1 & T2 & T3 & T4 & T5).
  pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOPn) as FOP. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOEn) as FOE. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOFn) as FOF.
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOP FF ltac:(clear - Q4; lia) ltac:(clear; lia) ltac:(clear - Q2 AF1; unfold AAPP_HI in *; lia)) as (DPF & _).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOF FF ltac:(clear - T4; lia) ltac:(clear; lia) ltac:(clear - T2 AF1; unfold AAPP_HI in *; lia)) as (DFF & _).
  change (fsz 2) with 256 in DPF, DFF.
  pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
  destruct UWc as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & XS2).
  assert (EOK2 : ec_ok E2) by (destruct EOUT2 as [-> | (_ & _ & K & _)]; [unfold ec_ok, EC_clear; cbn; clear; lia | exact K]).
  (* [comment removed for export] *)
  pose proof (rs_after_put H HH) as AP.
  eapply (ahh_evt H HH); [exact KREL| exact VIS| |].
  { eapply (AP _ ra sp gp (Z_to_bv 64 ATP) _ _ _ _ _ _ _ _ _ _ s5x s6x _ _ _ _ s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc me m LF lo shi spa ff fp E bs fb P tot (q - fb_in FB) 248 248 FB E2 g2
                 hw mw80 tmp gap optc ectc j56 j120);
      [ exact RF0
      | split; [exists jl; exact LOW| split; [exact SLOTS| split; [exact MW80| split; [exact MSZ| split; [exact SH16| split; [exists j96; exact J96| split; [exact F120| split; [exact TMP| split; [exact TSZ| split; [exact GAP| split; [exact GSZ| exact SPA]]]]]]]]]]]
      | exact SAVED | exact FAKE | exact RF' | exact FF
      | exact FBC | exact FB8 | exact APF | exact FOF | exact ACF
      | clear - BPOS; lia | exact BIO | clear - BOLE; lia | exact BCE | intros _; exact BPOS | unfold fb_size; unfold zlength in FSZ; clear - QR FSZ; lia
      | exact EC | exact EOK2 | exact EOUT2 | exact APE | exact FOE | exact ACE | exact E8 | clear - SEPEF; lia | exact HCT | exact XS2
      | exact ST | unfold AASSIGN_STACK; clear - LOS BSV AIS; lia | exact CEIL
      | clear - SOB AF1; unfold AAPP_HI in *; lia | clear - Q4 Q3; unfold AAPP_HI in *; lia | exact TOT0
      | clear - QR FSZ TOT TOT0 NR; unfold zlength in *; lia | exact RA | exact SP16 | exact MI | exact AC | exact SK | exact SPHI ]. }
  clear AP. intros msF3 mo3 KREL3 MP3 (m3 & MU3 & WM3 & MI3 & FBC3 & EC3 & HC3 & XS3 & AC3 & SK3 & ACE3 & ALT).
  (* [comment removed for export] *)
  pose proof (W2_objwin lo sp fb E ff fp CEIL) as OWF.
  pose proof (fun O n => objwin_obj H HH LF ff fp _ fb E me FF RF0 _ O n OWF) as DJO.
  pose proof (fun O n => objwin_obj_sh H HH LF ff fp _ fb E me FF RF0 APF APE _ O n OWF) as DJS.
  pose proof (fun O n x => objwin_out_sh H HH LF ff fp _ fb E me FF RF0 APF APE _ O n x OWF) as OUS.
  pose proof (fun p0 A0 k0 IN0 => objwin_blk H HH LF ff fp _ fb E me FF RF0 APF APE _ s LB m p0 A0 k0 OWF HP IN0 AOF AOE) as DJB.
  pose proof (fun A0 k0 => objwin_img H LF ff fp _ fb E FF APF APE _ A0 k0 OWF) as DJI.
  pose proof (fun A0 k0 => objwin_hi H LF ff fp _ fb E FF APF APE HI _ A0 k0 OWF) as DJH.
  pose proof (objwin_fr H LF ff fp _ fb E FF APF APE _ OWF) as WFR.
  pose proof (objwin_client H HH LF ff fp _ fb E me FF RF0 _ s LB m OWF HP AOFn AOEn) as WCL.
  cbv beta in DJO, DJS, OUS, DJB, DJI, DJH.
  assert (DJP : forall a k, P <= a -> a + k <= P + 352 -> 0 <= k -> disjoint_from (rs_W2 lo sp fb ff fp) a k).
  { intros a k K1 K2 K3. eapply disjoint_from_sub; [| exact K1| exact K2].
    apply DJO; [exact FOP| exact APP0| clear; lia| unfold PARSER_SIZE in SEPPF; clear - SEPPF; lia| clear - SEPPE; lia]. }
  assert (OUP : forall x, P <= x < P + 352 -> outside (rs_W2 lo sp fb ff fp) (sh x)) by (intros x Hx; exact (OUS P 352 x FOP APP0 ltac:(clear; lia) Hx)).
  Local Ltac trw K := eapply (rw_cells_transport bsegs); [exact K| eassumption| eassumption|].
  assert (PC3 : rw_cells bsegs m3 P (ParserCoreCells c2 pad7 pad2)) by (trw PC; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]).
  assert (UW3 : PutUw P mb (mkPST c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 true rdi2 (LBn2 ++ LBn) A2) m3).
  { unfold PutUw. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    split.
    { eapply AFieldsC_transport_gen; [exact FC| exact MU3| exact WM3| | |].
      - apply DJP; [clear; lia| cbn; clear; lia| clear; lia].
      - intros x Hx. apply OUP. clear - Hx. lia.
      - intros e dd Ld. destruct (OWN e dd Ld) as (pa & INe & _). fold LB in INe. exact (DJB _ _ _ INe). }
    split; [trw HDR; apply DJP; [unfold O_PR_HDR; clear; lia| unfold O_PR_HDR; cbn; clear; lia| clear; lia]|].
    split; [trw USED; apply DJP; [unfold O_PR_USED; clear; lia| unfold O_PR_USED; cbn; clear; lia| clear; lia]|].
    split.
    { eapply AMBuf_transport_gen; [exact MB| exact MU3| exact WM3| | |].
      - apply DJP; [clear; lia| clear; lia| clear; lia].
      - intros x Hx. apply OUP. clear - Hx. lia.
      - intros x s0 IN. destruct (MOWN x s0 IN) as [px INx]. fold LB in INx. exact (DJB _ _ _ INx). }
    split; [trw RD; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [trw MRG; apply DJP; [unfold O_PR_MERGE; clear; lia| unfold O_PR_MERGE; cbn; clear; lia| clear; lia]|].
    split; [trw CBH; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [trw CBB; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [unfold APfTab in PFT |- *; trw PFT; apply DJI; [unfold APF_TABPTR; clear; lia| unfold APF_TABPTR, AIMG_TOP; cbn; clear; lia| left; unfold APF_TABPTR, AG_HTTP_CAT; cbn; clear; lia]|].
    split; [eapply FTInit_transport; [exact FI| exact MU3| apply DJI; [unfold P_A_FT_INIT; clear; lia| unfold P_A_FT_INIT, AIMG_TOP; clear; lia| left; unfold P_A_FT_INIT, AG_HTTP_CAT; clear; lia]]| exact XS3]. }
  assert (HOWN3 : HdrOwnA LB m3 h2).
  { assert (K : forall ptr len, ASvOwn LB m ptr len -> ASvOwn LB m3 ptr len).
    { intros ptr len [Z0|(L1 & p & bsx & IN & CE & AD)]; [left; exact Z0| right]. split; [exact L1|]. exists p, bsx.
      destruct (DJB _ _ _ IN) as [D1 D2]. split; [exact IN|]. split.
      - trw CE. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - L1; lia). exact D1.
      - eapply addressable_transport; [exact AD| exact MU3| exact WM3| exact D2]. }
    destruct HOWN as (O1 & O2 & O3 & O4). split; [exact (K _ _ O1)|]. split; [exact (K _ _ O2)|]. split; [exact O3| exact O4]. }
  Local Ltac trj K DJP := eapply (rw_cells_transport bsegs); [exact K| eassumption| eassumption| apply DJP; [clear; lia| cbn; clear; lia| clear; lia]].
  assert (RDI3 : rw_cells bsegs m3 (P + 240) [C1 rdi2]) by (trj RDI DJP).
  assert (J13' : rw_cells bsegs m3 (P + 243) [CB 13 j13]) by (trj J13 DJP).
  assert (J32a' : rw_cells bsegs m3 (P + 256) [CB 32 j32a]) by (trj J32a DJP).
  assert (J8a' : rw_cells bsegs m3 (P + 296) [CB 8 j8a]) by (trj J8a DJP).
  assert (J32b' : rw_cells bsegs m3 (P + 304) [CB 32 j32b]) by (trj J32b DJP).
  assert (J8b' : rw_cells bsegs m3 (P + 344) [CB 8 j8b]) by (trj J8b DJP).
  assert (FTS3 : AFieldTabZero m3 \/ FT m3).
  { eapply FTState_transport; [exact FTS| exact MU3| exact WM3|].
    apply DJI; [unfold AG_FIELD_TABLE; clear; lia| unfold AG_FIELD_TABLE, AIMG_TOP; clear; lia| right; unfold AG_FIELD_TABLE, AG_HTTP_CAT; clear; lia]. }
  assert (MV3 : AMiscVt48 m3).
  { unfold AMiscVt48 in MV |- *. eapply (ro_cells_transport bsegs); [exact MV| exact MU3|].
    apply DJI; [unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR; clear; lia| unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR, AIMG_TOP; cbn; clear; lia| left; unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR, AG_HTTP_CAT; cbn; clear; lia]. }
  destruct (DJB _ _ _ INf) as [DBF DBS].
  assert (FBU3 : AFlatBuf LB m3 fb (fb_consume FB (q - fb_in FB)) (skipn (Z.to_nat (q - fb_in FB)) fds)).
  { eapply AFlatBuf_consume; [exact FBC3| exact FOK| exact NE| exact FSZ| unfold fb_size; unfold zlength in FSZ; clear - QR FSZ; lia| |].
    - trw BCH. pose proof BCH as [[WF _] _]. cbn in WF. destruct WF as (Ln1 & Ln2 & Ln3 & _).
      cbn [cells_size csize]. rewrite Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id by (clear - BIO BOLE; lia). unfold zlength in FSZ.
      eapply disjoint_from_sub; [exact DBF| clear; lia| clear - FSZ BIO BOLE; lia].
    - unfold fb_cap. eapply addressable_transport; [exact (ADR NE)| exact MU3| exact WM3| exact DBS]. }
  assert (BSC3 : rw_cells bsegs m3 bs (BasicStreamCells stb)) by (trw BSC; apply DJH; clear - FRB128; lia).
  pose proof (rblock_bounds _ _ RBS) as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6).
  destruct (DJB _ _ _ (SUBin _ INS)) as [DSB DSS].
  assert (SB3' : AStateBlock LB m3 stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds).
  { eapply AStateBlock_transport; [exact SB| exact MU3| exact WM3| exact DSB| | exact DSS|]; cbn [st_fb].
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. unfold fb_cap. rewrite SA', SE.
      destruct (INA N1) as [p9 IN9]. replace (A + N - A) with N by (clear; lia). exact (proj1 (DJB _ _ _ (SUBin _ IN9))).
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. unfold fb_cap. rewrite SA', SE.
      destruct (INA N1) as [p9 IN9]. replace (A + N - A) with N by (clear; lia). exact (proj2 (DJB _ _ _ (SUBin _ IN9))). }
  pose proof (ah_RHEAP_frame H HH _ _ _ _ _ HP MU3 WM3 WCL) as HP3.
  assert (ERR3 : rw_cells bsegs m3 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
  { rewrite EA. trw ERR. apply DJI; [unfold AERRNO, ATP; clear; lia| unfold AERRNO, ATP, AIMG_TOP; cbn; clear; lia| right; unfold AERRNO, ATP, AG_HTTP_CAT; clear; lia]. }
  pose proof (ah_rauxv_frame H HH _ _ _ _ _ AUX MU3 WM3 WCL) as AUX3.
  pose proof (ah_thr H HH _ _ _ HP3) as ATH3.
  assert (F0 : 0 <= ff) by (clear - F1; unfold AIMG_TOP, AFS_HDR in *; lia). assert (F8' : ff mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
  pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACP MU3 WFR F0 F8' ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear - DPF; lia)) as ACP3.
  pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACB MU3 WFR F0 F8' ltac:(clear; lia) ltac:(clear - SOB F2; lia)) as ACB3.
  pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACF MU3 WFR F0 F8' ltac:(clear; lia) ltac:(clear - DFF; lia)) as ACF3.
  assert (SVA3 : 1 <= N -> shvis m3 A (A + N)).
  { intros N1. destruct (INA N1) as [p9 IN9]. exact (ah_blk_shvis H HH _ _ _ _ _ _ HP3 (SUBin _ IN9)). }
  assert (FR0' : rw_cells bsegs m3 (bv_unsigned sp) fr) by (trw FR0; apply DJH; clear; lia).
  (* [comment removed for export] *)
  assert (XP3 : xpres H LBin SP (hread_X P E fb stb [] [] ++ XS) m0 m3).
  { eapply xpres_trans; [exact XP0|].
    eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP| exact MU3| exact WM3|] | clear; lia| exact SUBin| intros a K; exact K].
    unfold rs_W2. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]; cbn [fst snd].
    - left. clear - CEIL SPC. lia.
    - right. intros a Ha. unfold hread_X. cbn. left. clear - Ha. lia.
    - right. intros a Ha. unfold hread_X, put_X. cbn. do 4 right. left. exact Ha.
    - right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
    - right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
    - right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia. }
  (* [comment removed for export] *)
  set (w' := w_after_put (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) (mkPST c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 A2) true (q - fb_in FB)) in RP2.
  assert (RMX : forall LFx, (forall f, In f LF -> In f LFx) -> as_RFS H LFx m3 ->
            RWmF H (mkC bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp (Z_to_bv 64 ATP) F fc MXc CXc) LFx w' s errv E2 m3).
  { intros LFx SUBx RFx. subst w'. unfold RWmF, w_after_put, pst_ret. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A]. fold LB. rewrite EA.
    pose proof (aobj_shvis H HH _ _ _ _ _ _ HP3 RFx (aobj_LF_mono _ _ LFx _ _ AOEn SUBx) ltac:(clear; lia)) as SVE3.
    split; [exact PC3|]. split; [exact UW3|]. split; [exact HOWN3|]. split; [exact RDI3|].
    split; [exact J13'|]. split; [exact J32a'|]. split; [exact J8a'|]. split; [exact J32b'|]. split; [exact J8b'|].
    split; [exact HC3|]. split; [exact FTS3|]. split; [exact MV3|]. split; [exact FBU3|]. split; [exact EC3|]. split; [exact BSC3|].
    split; [exact SB3'|]. split; [exact HP3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [exact MI3|].
    split; [exact RFx|]. split; [exact AC3|]. split; [exact SK3|]. split; [exact ATH3|].
    split; [exact ACP3|]. split; [exact ACE3|]. split; [exact SVE3|]. split; [exact ACB3|]. split; [exact ACF3| exact SVA3]. }
  assert (ZSK : zlength (skipn (Z.to_nat (q - fb_in FB)) fds) = zlength fds - (q - fb_in FB)).
  { unfold zlength in FSZ. rewrite zlength_skipn; [clear - QR; lia|]. clear - QR FSZ. lia. }
  assert (TOT' : 0 <= tot + (q - fb_in FB) /\ tot + (q - fb_in FB) + zlength (skipn (Z.to_nat (q - fb_in FB)) fds) + zlength sds <= N).
  { rewrite ZSK. clear - QR TOT TOT0 FSZ. unfold zlength in *. lia. }
  assert (WMle : wM N w' = wM N (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) - (q - fb_in FB)).
  { subst w'. unfold wM, w_after_put. cbn_w. rewrite ZSK. clear. lia. }
  (* [comment removed for export] *)
  destruct ALT as [(NM & RF3 & STK3 & RPOST) | (NM & RF3 & STK3 & FRM3 & SAVED3 & FAKE3 & DR)].
  - (* [comment removed for export] *)
    left. destruct RPOST as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & EMS).
    unfold rs_done. cbn [cfg_ms cfg_model]. cbn_w.
    exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, m3, w', s, errv, E2, (tot + (q - fb_in FB)), XS.
    split; [exact EMS|]. split; [exact KREL3|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP3)|].
    split; [apply (proj2 (RWm_RWmF H _ _ _ _ _ _)); exact (RMX LF ltac:(intros f Hf; exact Hf) RF3)|].
    split; [exact RP2|]. split; [subst w'; unfold w_after_put, pst_ret; cbn_w; cbn [ps_A]; exact ALK|].
    split; [exact STK3|]. split; [exact FR0'|]. split; [exact FXS|]. split; [exact XP3|].
    split; [exact (proj1 TOT')|]. split; [subst w'; unfold w_after_put; cbn_w; exact (proj2 TOT')|].
    split; [exact EOK2|]. split; [exact EOUT2|].
    split; [rewrite WMle; clear - WM0 QR; lia|].
    intros ECL NS. rewrite WMle. split; [| subst w'; unfold w_after_put; cbn_w; exact NRB].
    subst w'. unfold w_after_put, pst_ret in NS. cbn [w_d ps_c] in NS.
    destruct (PROG ECL) as [LT | S11]; [| exfalso; exact (NS S11)]. clear - WM0 LT. lia.
  - (* [comment removed for export] *)
    right. destruct DR as (rax' & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & EMS).
    exists w'. split; [subst w'; unfold w_after_put; cbn_w; reflexivity|].
    unfold rs_at_doread, rs_core, rs_frames. cbn [cfg_ms cfg_model]. cbn_w.
    exists rax', y0, y1, y2, z0, z1, z2, z3, z4, z5, z6, z7, (wz (q - fb_in FB)), s6x, y3, y4, y5, y6, m3, s, errv, E2, (tot + (q - fb_in FB)),
           spa, ff, fp, mw80, (ErrCodeCells (EC_http 3)), gap, hw, optc, j56, ectc, j120, XS.
    split; [exact EMS|].
    split. { subst w'. unfold w_after_put, pst_ret. cbn_w. cbn [ps_c]. intros S11. pose proof (ST11 S11) as ECL. rewrite ECL in NM. clear - NM. cbv in NM. discriminate. }
    split; [exact KREL3|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP3)|].
    split.
    { split; [exact (RMX LF' SUBF RF3)|]. split; [exact RP2|]. split; [subst w'; unfold w_after_put, pst_ret; cbn_w; cbn [ps_A]; exact ALK|].
      split; [exact STK3|]. split; [split; [exact FRM3| split; [exact SAVED3| split; [exact FR0'| split; [exact SZFR| exact FAKE3]]]]|].
      split; [exact FF|]. split; [exists me; exact RF0|].
      split; [exact FXS|]. split; [exact FRX|]. split; [exact XP3|]. split; [exact (proj1 TOT')|]. split; [subst w'; unfold w_after_put; cbn_w; exact (proj2 TOT')|].
      subst w'. unfold w_after_put. cbn_w. exact NRB. }
    rewrite WMle. clear - WM0 QR. lia.
Qed.

  Hypothesis BPUT : forall MX CX MA R, bput_stmtR H MX CX MA R.

(* [comment removed for export] *)
Lemma rs_put_round : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 ->
  rs_at_put H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (fun cf' => rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf'
                      \/ exists w', zlength (w_sds w') = zlength (w_sds w)
                           /\ rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w' cf') cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 RA AT.
  eapply (ah_seq H HH); [eapply (rs_put_call H HH BPUT); [exact STC| exact PLC| exact R0| exact AT]|].
  intros c' K. eapply rs_put_tail; [exact STC| exact PLC| exact RA| exact K].
Qed.
End HCW.

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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AS_InstChain BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst X8_rsfree X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_A_kit4 X8_A_kit3 X8_S_kit X8_S_kit3 X8_S_rs2 X8_R_read X8_R_readC X8_R_readF X8_R_readD X8_R_readE X8_read_stmt X8_read2 X8_read3 X8_read3b X8_read4 X8_read4b X8_read5 X8_read5b.
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
  Hypothesis FS0 : stack_malloc_0_stmt H.
  Hypothesis FS2 : stack_malloc_2_stmt H.
  Hypothesis HH7 : asan_rt_hyps7 H.
  Hypothesis HH8 : asan_rt_hyps8 H.
  Hypothesis ATR : incl AsTRList.TRLIST (as_TR H).
  Hypothesis BPUT : forall MX CX MA R, bput_stmtR H MX CX MA R.

(* [comment removed for export] *)
Lemma bput_stmtR_of : forall MX CX MA R, bput_stmt H MX CX MA R -> bput_stmtR H MX CX MA R.
Proof. intros MX CX MA R K. exact K. Qed.

Lemma rs_done_mono : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M1 M0 : Z) (cf : config),
  rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 cf -> M1 <= M0 ->
  rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 M0 cf D LE. unfold rs_done in *.
  destruct D as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & w & s & errv & E & tot & XS & D).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, w, s, errv, E, tot, XS.
  destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16).
  repeat (split; [assumption|]). split; [clear - D15 LE; lia|].
  intros K1 K2. destruct (D16 K1 K2) as [K3 K4]. split; [clear - K3 LE; lia | exact K4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rs_W1 (lo sp E fsb fp ff : Z) : list (Z * Z) :=
  [(lo, sp); (E, E + 24); (fsb, fsb + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]%Z.

Lemma W1_objwin : forall lo sp E fb ff fp, aceil <= lo -> Z.shiftr ff 3 + 2147450880 = sh ff ->
  Forall (objwin H sp fb E ff fp) (rs_W1 lo sp E (as_FSB H) fp ff).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(HCEIL); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read2.objwin); constr:(H); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.as_FSB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.AFS_FLAGS); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read2.fwin); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@Corelib.Lists.ListDef.Forall); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_read6.HCW.rs_W1)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @z; @SHFF; @CEIL; @fp; @ff; @fb; @E; @sp; @lo|] "#'H#,#i#/#&#%#U#(###)#'#>#V#T#Z#[#$#8#*#2#:#C#I#L#O#Y#`#a#1#<#=#A#B#M#P#N#Q#S#\#R#]#b#c#d#^#+#h#i#k#j#0#E#9#H#e#4#3#7#6#?#F#G#J#X#W#;#@#D#K#g#f#5#_;#R%#S%#T$#U%#V&#W%#X&#Y$#Z$#['#\&#]&#^'#_'#`*#a)#b&#c&#($#d'#e%#f&#g%#h%US,S###G*Q+#9E#*%*#*#*#*#*#*#*#*#*#*#*#*#*#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#+#(A#US$E)C$#VS-CC[S.S#KIJGDE,CCRI%s#)%#%#+#(G#,CCG#US/K(#S0,CC$#+Q(E#,CCE#%Q%#%#%#%#%#%#%#+#(D#,CCD#US$D+*($#,CC%#US%@3A$#3B)#3s##5#3s#$9#3s#%=#-CCs#$#s#M#.CCs#&##I$%##J'%s#'+#(J##)#$'##G-#,s#+$$#+@(S&#,CCS&#)s#7s#5#/KDEs#6&$#&)#&-##s#bR#IIUS%S'US1S'VS(CEUS2CXS3C$P#US4CUS5CVS)CQVS)Cs#70C$N#1&MFFL#OUS6F\S7(MFFL$#$VS8)L:S*S+VS9HE)S*#S+m$%#WS:CS;PXS<HE$#l#$*)#l#%32#l#&87#j#'C#j#(C##HP#PEk##$#k#'C#k#(C#WHS=s$&El#))$#m##s#$VS(CP0C=N=1?MFFL#Ol#$#93l#%&B#l#&s#(s#'#j#'C##HHk#'C#5Rl#)&$#m##s#/6s#1s#0/#$s#2s#1m#$#m##s#F4s#Gs#6#-CCs#h#s$;#.CCs#j##I$%##J'#&s#J$$##G*#)s#r$$#)s#{s#ss#G/KDEs#t&$#&&#&*##GG#s#zs#z5Il#)@>#m##&7Cs$#8Cs#C#0C#N#1s#FMFFL#Ol#$#s#@s#:l#%s#-s#I#l#&s#Os#N#j#'C#(Hs$+###k#'C#l#)&#0m##26430#$54m#$#m##=4>;#'B;#'s#&;#-CCs$2#s$d#.CCs$4##I$%##J'#&s#s$$##G*#)s$?$$#)s$Hs$=s#p/KDEs$>&$#&&#&*##D2#1s$6$$#)s$Ps$Es$B9Ds$t(#s$V##8($s$9#8#$%#)s$Ws$Ls$L&$#&+#:s$Zs$O''&#'.&#'0&#'87#':7#'>7#'B7#-CCs$T#s%-#.CCs$V##I$%##J'#&s$<$$##G*#)s$d$$#)s$ms$_s$9/KDEs$`&$#&&#&*##D2#1s$[$$#)s$us$gs$g#s#&6#5s#%$$#)s$ys$ks$n&$#&(#:s$|s$n4*%#',%#'43#'63#':3#'>3#-CCs$j#s%N#.CCs$l##I$%##J'#&s$]$$##G*#)s%)$$#)s%2s$us$Z/KDEs$v&$#&&#&*##D2#1s$|$$#)s%:s$}s%,#s#G6#5s#F$$#)s%>s%%s%3&$#&(##DD#s%*s%*5Jl#)s$=s$;#m##&7Cs%/8Cs$`#0C#N#1s$cMFFL#Ol#$#s$]s$Wl#%s$Js$f#l#&s$ls$k#j#'C#(Hs%7###k#'C#l#)&#0m##26430#$54m#$#m##?4@9#'s#(s#'#'s#*s#'#'s#.s#'#'s#2s#'#-CCs%?#s&'#.CCs%A##I$%##J'#&s%6$$##G*#)s%^$$#)s%gs%Js%3/KDEs%K&$#&&#&*##D2#1s%U$$#)s%os%Rs%a#s#|6#5s#{$$#)s%ss%Vs%h&$#&(#9Js&=(#s%{##H(Hs%^(%s%_#$#$&#j#*C##s$.s$.#s$-s$-7Cs&(8Cs%>#0C#N#1s%AMFFL#Ol#$#s%;s%5l#%s%(s%D#l#&s%Js%I#j#'C#(Hs&0###k#'C#57l#)'$#m##17Cs%s8C0#0C#N#1s%OMFFL#Ol#$#s%Is%Cl#%s%6s%R#l#&s%Xs%W#j#'C#(0s%{###k#'C#l#)&#0m##=6?>0#$@?m#$#ZS>Cs$Ns###s&(Hm##s#/4s#0s#/#'s#4s#/#'s#6s#/#'s#>s#=#'s#@s#=#'s#Ds#=#'s#Hs#=#VS?s&Ks&J2s&Ls&Ks&/s&.$#2s&Ms&Ls&4s&.s#P#2s&Ns&Ms&@s&.s$*#2s&Os&Ns&Ds&.s$L#2s&Ps&Os&Hs&.s$r#2s&Qs&Ps&Os&.s%@#ZS@RIGs&IEDWSAs&Ss&R#m#%#j#+s&V#j#,s&{#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C##"). Qed.

Lemma W1_fwin4 : forall fp ff, Z.shiftr ff 3 + 2147450880 = sh ff ->
  Forall (fwin H ff fp) [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]%Z.
Proof.
  intros fp ff SHFF.
  apply Forall_cons; [right; right; right; reflexivity|].
  apply Forall_cons; [right; left; reflexivity|].
  apply Forall_cons; [left; cbn [fst snd]; lia|].
  apply Forall_cons; [right; right; left; cbn [fst snd]; rewrite <- SHFF; lia| apply Forall_nil].
Qed.

(* [comment removed for export] *)
Lemma W1_obj : forall LF me lo sp E fp ff O n, fresh_frame H LF 2 ff fp -> as_RFS H LF me -> aceil <= lo ->
  fsobj H LF O n -> aapp O n -> 0 <= n -> (O + n <= E \/ E + 24 <= O) ->
  disjoint_from (rs_W1 lo sp E (as_FSB H) fp ff) O n.
Proof.
  intros LF me lo sp E fp ff O n FF RF0 CEIL FO AP N0 DE.
  pose proof (aapp_bounds _ _ AP N0) as (B1 & B2 & B3 & B4 & B5).
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & _).
  pose proof (fwinF_obj H HH LF ff fp FF _ me O n (W1_fwin4 fp ff SHFF) RF0 FO AP N0) as K. cbn [disjoint_from fst snd] in K.
  destruct K as (K1 & K2 & K3 & K4 & _).
  unfold rs_W1. cbn [disjoint_from fst snd].
  split; [left; clear - B2 CEIL; lia|]. split; [exact DE|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4| exact I].
Qed.

(* [comment removed for export] *)
Lemma W1_img : forall LF lo sp E fp ff A k, fresh_frame H LF 2 ff fp -> aceil <= lo -> AIMG_TOP <= E ->
  A + k <= AIMG_TOP -> disjoint_from (rs_W1 lo sp E (as_FSB H) fp ff) A k.
Proof.
  intros LF lo sp E fp ff A k FF CEIL HE HA.
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & _).
  pose proof aceil_facts as (AF1 & _).
  unfold rs_W1. cbn [disjoint_from fst snd]. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
  split; [left; clear - HA CEIL AF1; lia|]. split; [left; clear - HA HE; lia|]. split; [left; clear - HA F9; lia|].
  split; [left; clear - HA F4; lia|]. split; [left; clear - HA F1; lia|]. split; [left; clear - HA SF0; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma W1_axs : forall LF lo sp E fp ff, fresh_frame H LF 2 ff fp -> aceil <= lo -> AIMG_TOP <= E ->
  Forall (fun iv : Z * Z => 0x12a180 <= fst iv \/ snd iv <= 0x119000) (rs_W1 lo sp E (as_FSB H) fp ff).
Proof.
  intros LF lo sp E fp ff FF CEIL HE.
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & _).
  pose proof aceil_facts as (AF1 & _). unfold rs_W1. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
  repeat (apply Forall_cons; [left; cbn [fst snd]|]); [clear - CEIL AF1; lia| clear - HE; lia| clear - F9; lia| clear - F4; lia| clear - F1; lia| clear - SF0; lia| apply Forall_nil].
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_high : forall W A n, Forall (fun iv : Z * Z => aceil <= fst iv) W -> A + n <= aceil -> disjoint_from W A n.
Proof.
  induction W as [|[l h] W IH]; intros A n FW LE; cbn; [exact I|].
  split; [pose proof (Forall_inv FW) as K; cbn in K; left; clear - K LE; lia| exact (IH _ _ (Forall_inv_tail FW) LE)].
Qed.

Lemma rs_fake_high : forall LF m m' ff fp hw optc j56 ectc j120 ob eb W,
  fresh_frame H LF 2 ff fp -> rs_fake m ff fp hw optc j56 ectc j120 ob eb ->
  munch W m m' -> wmono bsegs m m' -> Forall (fun iv : Z * Z => aceil <= fst iv) W ->
  rs_fake m' ff fp hw optc j56 ectc j120 ob eb.
Proof.
  intros LF m m' ff fp hw optc j56 ectc j120 ob eb W FF (K1 & K2 & SZ2 & K3 & K4 & SZ4 & K5 & K6 & K7 & K8) MU WM FW.
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & SF1 & SA & _).
  assert (T : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= aceil -> rw_cells bsegs m' A cs)
    by (intros A cs K LE; eapply (rw_cells_transport bsegs); [exact K| exact MU| exact WM| exact (disjoint_from_high _ _ _ FW LE)]).
  split; [apply (T _ _ K1); cbn; clear - F2; lia|].
  split; [apply (T _ _ K2); rewrite SZ2; clear - F2; lia|]. split; [exact SZ2|].
  split; [apply (T _ _ K3); cbn; clear - F2; lia|].
  split; [apply (T _ _ K4); rewrite SZ4; clear - F2; lia|]. split; [exact SZ4|].
  split; [apply (T _ _ K5); cbn; clear - F2; lia|].
  split; [apply (T _ _ K6); cbn; clear - F2; lia|].
  split; [apply (T _ _ K7); rewrite SHFF; cbn; clear - SF1 SA; lia|].
  apply (T _ _ K8). cbn. clear - F5 F2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rs_read_round : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 ->
  rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (fun cf' => rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf'
                      \/ exists M1 w', M1 < M0 /\ rs_at_put H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 w' cf') cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 RA AT.
  eapply (ah_seq H HH); [exact (rs_read_A H HH HH7 HH8 ATR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 AT)|].
  intros cf1 (w1 & _ & AT1).
  eapply (ah_seq H HH); [exact (rs_read_B1 H HH FS0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 AT1)|].
  intros cf2 (n & eof & _ & AT2). exact (rs_read_B2 H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AT2).
Qed.

(* [comment removed for export] *)
Lemma rs_loop : forall (n : nat) (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 -> M0 < Z.of_nat n ->
  rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0) cf.
Proof.
  induction n as [|n IH]; intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 RA LT AT.
  - exfalso. pose proof AT as AT'. unfold rs_at_doread, rs_core in AT'.
    destruct AT' as (rax & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s5x & s6x & t3 & t4 & t5 & t6 & m & s & errv & E & tot
                     & spa & ff & fp & mw80 & tmp & gap & hw & optc & j56 & ectc & j120 & XS & _ & _ & _ & _ & _ & WM0).
    destruct C as [bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
    unfold rs_static in STC. cbn_w_all.
    destruct STC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NR & _). unfold wM in WM0. clear - WM0 NR LT. unfold zlength in WM0. cbn in LT. nia.
  - eapply (ah_seq H HH); [exact (rs_read_round _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AT)|].
    intros cf1 [D | (M1 & w1 & LT1 & AP)]; [apply (ah_done H HH); exact D|].
    eapply (ah_seq H HH); [exact (rs_put_round H HH BPUT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AP)|].
    intros cf2 [D | (w2 & _ & AD)]; [apply (ah_done H HH); eapply rs_done_mono; [exact D | clear - LT1; lia]|].
    eapply (ah_mono H HH); [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 w2); [exact STC | exact PLC | exact R0 | exact RA | clear - LT LT1; lia | exact AD]|].
    intros cf3 D. eapply rs_done_mono; [exact D | clear - LT1; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem hread_spec : forall MA MR, hread_stmt H MA MR.
Proof.
  intros MA MR C ra sp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 msF m mo fr w s errv E XS
         VIS STC PLC NS11 RM RP ALK ST FR0 SZFR FXS XP0 NRB KREL MP RA.
  pose proof STC as STC0. pose proof PLC as PLC0. pose proof RP as RP0.
  destruct C as [bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag].
  unfold rs_static in STC. unfold rs_placed in PLC. unfold RWm in RM. unfold RWp in RP. cbn_w_all.
  cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct STC as (AOP & AOE & AOF & P8 & E8 & BS8 & FB8 & SEPPE & SEPPF & SEPEF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL & MBLE).
  destruct PLC as (SOB & LOS & SP16 & SPHI & SPB & SPC & FRB128).
  destruct RM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP & ERR & AUX & MI & RF & AC & SK & ATH & ACP & ACE & SVE & ACB & ACF & SVA).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM_ & FRF & DJL & DJB0 & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  assert (R0 : 0 <= MR) by (destruct ALK as (_ & K & _); exact K).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof aceil_facts as (AF1 & AF2 & AF3). unfold HREAD_STACK in LOS. pose proof BPUT_STACK_val as BSV.
  assert (AIS : AINTRIN_STACK = 4096) by reflexivity. assert (AFSS : AFS_STACK = 1024) by reflexivity.
  subst tp. assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; clear; lia). rewrite EA in ERR.
  pose proof SOB as SOB0. unfold sobj in SOB.
  pose proof (AFlatBuf_shape _ _ _ _ _ FBU) as (B0 & BIO & BOLE & BCE & FS5).
  set (LB := LBn ++ LBin) in *.
  assert (SUBin : forall b, In b LBin -> In b LB) by (intros b Hb; unfold LB; apply in_or_app; right; exact Hb).
  pose proof (aobj_LB_mono _ LB _ _ _ AOP ltac:(intros b [])) as AOPn. pose proof (aobj_LB_mono _ LB _ _ _ AOE ltac:(intros b [])) as AOEn.
  pose proof (aobj_LB_mono _ LB _ _ _ AOF ltac:(intros b [])) as AOFn.
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOPn) as APP0. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOEn) as APE. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOFn) as APF.
  pose proof (aapp_sub _ _ P PARSER_SIZE APP0 ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear; lia)) as APP.
  pose proof (aapp_bounds _ _ APP0 ltac:(clear; lia)) as (PQ1 & PQ2 & PQ3 & PQ4 & _). pose proof (aapp_bounds _ _ APE ltac:(clear; lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (aapp_bounds _ _ APF ltac:(clear; lia)) as (T1 & T2 & T3 & T4 & T5).
  pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOPn) as FOP. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOEn) as FOE. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOFn) as FOF.
  pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
  destruct UWc as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & AXS).
  destruct (rw_cells_forget _ _ _ _ EC) as [ej ECb]. cbn [cells_size csize Nat.add ErrCodeCells length] in ECb.
  (* [comment removed for export] *)
  eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
  { eapply (rs_entry H HH FS2 ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF lo shi Ev bs fb P FB ej);
      [ exact (proj1 FBU) | exact FB8 | exact APF | exact FOF | exact ACF
      | exact ECb | exact APE | exact FOE | exact ACE | exact SVE | exact E8
      | clear - SEPEF; lia
      | exact B0 | exact BIO | clear - BOLE; lia | exact BCE
      | clear - SOB AF1; unfold AAPP_HI in *; lia | clear - PQ4 PQ3; unfold AAPP_HI in *; lia
      | exact ST | clear - LOS BSV AFSS; lia | clear - LOS BSV AIS; lia | exact CEIL
      | exact MI | exact SP16 | reflexivity | exact AC | exact ATH
      | exact RF | clear - LFL4; lia | exact SK | exact SPHI ]. }
  intros msF1 mo1 KREL1 MP1 (m1 & spa & ff & fp & jm & jt & gap & hw & j56 & j120 & jo & je & rax & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6
                              & MU1 & WM1 & MI1 & ST1 & FRM1 & SAVED1 & FAKE1 & RF1 & FF & AC1 & SK1 & FBC1 & EC1 & ACF1 & ACE1 & SVE1 & ALT).
  change (munch (rs_W1 lo (bv_unsigned sp) Ev (as_FSB H) fp ff) m m1) in MU1.
  set (LF' := (2, ff, fp) :: LF) in *.
  assert (SUBF : forall f, In f LF -> In f LF') by (intros f Hf; right; exact Hf).
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & SF1 & SA & M1 & M2 & LSH & SHH & SIDE & APFF & APP1 & APB).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF FOP FF ltac:(clear - PQ4; lia) ltac:(clear; lia) ltac:(clear - PQ2 AF1; unfold AAPP_HI in *; lia)) as (DPF & _).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF FOE FF ltac:(clear - R4; lia) ltac:(clear; lia) ltac:(clear - R2 AF1; unfold AAPP_HI in *; lia)) as (DEF & _).
  pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF FOF FF ltac:(clear - T4; lia) ltac:(clear; lia) ltac:(clear - T2 AF1; unfold AAPP_HI in *; lia)) as (DFF & _).
  change (fsz 2) with 256 in DPF, DEF, DFF.
  (* [comment removed for export] *)
  assert (HI : aceil <= bv_unsigned sp) by (clear - CEIL LOS BSV; lia).
  pose proof (W1_objwin lo (bv_unsigned sp) Ev fb ff fp CEIL SHFF) as OWF.
  pose proof (fun O n => objwin_obj H HH LF ff fp _ fb Ev m FF RF _ O n OWF) as DJO.
  pose proof (fun O n => objwin_obj_sh H HH LF ff fp _ fb Ev m FF RF APF APE _ O n OWF) as DJS.
  pose proof (fun O n x => objwin_out_sh H HH LF ff fp _ fb Ev m FF RF APF APE _ O n x OWF) as OUS.
  pose proof (fun p0 A0 k0 IN0 => objwin_blk H HH LF ff fp _ fb Ev m FF RF APF APE _ s LB m p0 A0 k0 OWF HP IN0 AOF AOE) as DJB.
  pose proof (fun A0 k0 => W1_img LF lo (bv_unsigned sp) Ev fp ff A0 k0 FF CEIL R1) as DJI.
  pose proof (fun A0 k0 => objwin_hi H LF ff fp _ fb Ev FF APF APE HI _ A0 k0 OWF) as DJH.
  pose proof (objwin_fr H LF ff fp _ fb Ev FF APF APE _ OWF) as WFR.
  pose proof (objwin_client H HH LF ff fp _ fb Ev m FF RF _ s LB m OWF HP AOFn AOEn) as WCL.
  cbv beta in DJO, DJS, OUS, DJB, DJI, DJH.
  assert (DJP : forall a k, P <= a -> a + k <= P + 352 -> 0 <= k -> disjoint_from (rs_W1 lo (bv_unsigned sp) Ev (as_FSB H) fp ff) a k).
  { intros a k K1 K2 K3. eapply disjoint_from_sub; [| exact K1| exact K2].
    apply DJO; [exact FOP| exact APP0| clear; lia| unfold PARSER_SIZE in SEPPF; clear - SEPPF; lia| clear - SEPPE; lia]. }
  assert (OUP : forall x, P <= x < P + 352 -> outside (rs_W1 lo (bv_unsigned sp) Ev (as_FSB H) fp ff) (sh x)) by (intros x Hx; exact (OUS P 352 x FOP APP0 ltac:(clear; lia) Hx)).
  Local Ltac trw K := eapply (rw_cells_transport bsegs); [exact K| eassumption| eassumption|].
  assert (PC1 : rw_cells bsegs m1 P (ParserCoreCells c pad7 pad2)) by (trw PC; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]).
  assert (UW1 : PutUw P mb (mkPST c S L ns ls em h u es insz g rdi LBn Ag) m1).
  { unfold PutUw. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A]. fold LB.
    split.
    { eapply AFieldsC_transport_gen; [exact FC| exact MU1| exact WM1| | |].
      - apply DJP; [clear; lia| cbn; clear; lia| clear; lia].
      - intros x Hx. apply OUP. clear - Hx. lia.
      - intros e dd Ld. destruct (OWN e dd Ld) as (pa & INe & _). fold LB in INe. exact (DJB _ _ _ INe). }
    split; [trw HDR; apply DJP; [unfold O_PR_HDR; clear; lia| unfold O_PR_HDR; cbn; clear; lia| clear; lia]|].
    split; [trw USED; apply DJP; [unfold O_PR_USED; clear; lia| unfold O_PR_USED; cbn; clear; lia| clear; lia]|].
    split.
    { eapply AMBuf_transport_gen; [exact MB| exact MU1| exact WM1| | |].
      - apply DJP; [clear; lia| clear; lia| clear; lia].
      - intros x Hx. apply OUP. clear - Hx. lia.
      - intros x s0x IN. destruct (MOWN x s0x IN) as [px INx]. fold LB in INx. exact (DJB _ _ _ INx). }
    split; [trw RD; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [trw MRG; apply DJP; [unfold O_PR_MERGE; clear; lia| unfold O_PR_MERGE; cbn; clear; lia| clear; lia]|].
    split; [trw CBH; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [trw CBB; apply DJP; [clear; lia| cbn; clear; lia| clear; lia]|].
    split; [unfold APfTab in PFT |- *; trw PFT; apply DJI; unfold APF_TABPTR, AIMG_TOP; cbn; clear; lia|].
    split; [eapply FTInit_transport; [exact FI| exact MU1| apply DJI; unfold P_A_FT_INIT, AIMG_TOP; clear; lia]|].
    eapply AXStatics2_transport; [exact AXS| exact MU1| exact WM1| exact (W1_axs LF lo (bv_unsigned sp) Ev fp ff FF CEIL R1)]. }
  assert (HOWN1 : HdrOwnA LB m1 h).
  { assert (K : forall ptr len, ASvOwn LB m ptr len -> ASvOwn LB m1 ptr len).
    { intros ptr len [Z0|(L1 & p & bsx & IN & CE & AD)]; [left; exact Z0| right]. split; [exact L1|]. exists p, bsx.
      destruct (DJB _ _ _ IN) as [D1 D2]. split; [exact IN|]. split.
      - trw CE. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - L1; lia). exact D1.
      - eapply addressable_transport; [exact AD| exact MU1| exact WM1| exact D2]. }
    destruct HOWN as (O1 & O2 & O3 & O4). split; [exact (K _ _ O1)|]. split; [exact (K _ _ O2)|]. split; [exact O3| exact O4]. }
  Local Ltac trj K DJP := eapply (rw_cells_transport bsegs); [exact K| eassumption| eassumption| apply DJP; [clear; lia| cbn; clear; lia| clear; lia]].
  assert (RDI1 : rw_cells bsegs m1 (P + 240) [C1 rdi]) by (trj RDI DJP).
  assert (J13' : rw_cells bsegs m1 (P + 243) [CB 13 j13]) by (trj J13 DJP).
  assert (J32a' : rw_cells bsegs m1 (P + 256) [CB 32 j32a]) by (trj J32a DJP).
  assert (J8a' : rw_cells bsegs m1 (P + 296) [CB 8 j8a]) by (trj J8a DJP).
  assert (J32b' : rw_cells bsegs m1 (P + 304) [CB 32 j32b]) by (trj J32b DJP).
  assert (J8b' : rw_cells bsegs m1 (P + 344) [CB 8 j8b]) by (trj J8b DJP).
  assert (HCT1 : AHttpCat m1 g).
  { eapply AHttpCat_transport; [exact HCT| exact MU1| exact WM1| |]; apply DJI; unfold AG_HTTP_CAT, AG_HTTP_CAT_GUARD, AIMG_TOP; clear; lia. }
  assert (FTS1 : AFieldTabZero m1 \/ FT m1).
  { eapply FTState_transport; [exact FTS| exact MU1| exact WM1|]. apply DJI; unfold AG_FIELD_TABLE, AIMG_TOP; clear; lia. }
  assert (MV1 : AMiscVt48 m1).
  { unfold AMiscVt48 in MV |- *. eapply (ro_cells_transport bsegs); [exact MV| exact MU1|]. apply DJI; unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR, AIMG_TOP; cbn; clear; lia. }
  assert (FBU1 : AFlatBuf LB m1 fb FB fds).
  { eapply AFlatBuf_transport; [exact FBU| exact MU1| exact WM1| | |].
    - apply (W1_obj LF m); [exact FF| exact RF| exact CEIL| exact FOF| exact APF| unfold SZ_FB; clear; lia| unfold SZ_FB; clear - SEPEF; lia].
    - intros NE. destruct FBU as (_ & FOK' & _). destruct FOK' as [EFB|(pf & INf & _)]; [exfalso; exact (NE EFB)|]. exact (proj1 (DJB _ _ _ INf)).
    - intros NE. destruct FBU as (_ & FOK' & _). destruct FOK' as [EFB|(pf & INf & _)]; [exfalso; exact (NE EFB)|]. exact (proj2 (DJB _ _ _ INf)). }
  assert (BSC1 : rw_cells bsegs m1 bs (BasicStreamCells stb)) by (trw BSC; apply DJH; clear - FRB128; lia).
  destruct (DJB _ _ _ (SUBin _ INS)) as [DSB DSS].
  assert (SB1' : AStateBlock LB m1 stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds).
  { eapply AStateBlock_transport; [exact SB| exact MU1| exact WM1| exact DSB| | exact DSS|]; cbn [st_fb].
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. unfold fb_cap. rewrite SA', SE.
      destruct (INA N1) as [p9 IN9]. replace (A + N - A) with N by (clear; lia). exact (proj1 (DJB _ _ _ (SUBin _ IN9))).
    - intros NEs. destruct STRM as [[_ ->]|(N1 & SA' & SE)]; [exfalso; exact (NEs eq_refl)|]. unfold fb_cap. rewrite SA', SE.
      destruct (INA N1) as [p9 IN9]. replace (A + N - A) with N by (clear; lia). exact (proj2 (DJB _ _ _ (SUBin _ IN9))). }
  pose proof (ah_RHEAP_frame H HH _ _ _ _ _ HP MU1 WM1 WCL) as HP1.
  assert (ERR1 : rw_cells bsegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
  { rewrite EA. trw ERR. apply DJI; unfold AERRNO, ATP, AIMG_TOP; cbn; clear; lia. }
  pose proof (ah_rauxv_frame H HH _ _ _ _ _ AUX MU1 WM1 WCL) as AUX1.
  pose proof (ah_thr H HH _ _ _ HP1) as ATH1.
  assert (F0 : 0 <= ff) by (clear - F1; unfold AIMG_TOP, AFS_HDR in *; lia). assert (F8' : ff mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
  pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACP MU1 WFR F0 F8' ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear - DPF; lia)) as ACP1.
  pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACB MU1 WFR F0 F8' ltac:(clear; lia) ltac:(clear - FRB128 CEIL LOS BSV F2; lia)) as ACB1.
  assert (SVA1 : 1 <= N -> shvis m1 A (A + N)).
  { intros N1. destruct (INA N1) as [p9 IN9]. exact (ah_blk_shvis H HH _ _ _ _ _ _ HP1 (SUBin _ IN9)). }
  assert (FR0' : rw_cells bsegs m1 (bv_unsigned sp) fr) by (trw FR0; apply DJH; clear; lia).
  assert (RM1 : RWmF H (mkC bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp (Z_to_bv 64 ATP) F fc MXc CXc) LF'
                     (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) s errv EC_clear m1).
  { unfold RWmF, PutUw. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A]. fold LB.
    pose proof (aobj_shvis H HH _ _ _ _ _ _ HP1 RF1 (aobj_LF_mono _ _ LF' _ _ AOEn SUBF) ltac:(clear; lia)) as SVE1'.
    split; [exact PC1|]. split; [exact UW1|]. split; [exact HOWN1|]. split; [exact RDI1|].
    split; [exact J13'|]. split; [exact J32a'|]. split; [exact J8a'|]. split; [exact J32b'|]. split; [exact J8b'|].
    split; [exact HCT1|]. split; [exact FTS1|]. split; [exact MV1|]. split; [exact FBU1|]. split; [exact EC1|]. split; [exact BSC1|].
    split; [exact SB1'|]. split; [exact HP1|]. split; [exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact SK1|]. split; [exact ATH1|].
    split; [exact ACP1|]. split; [exact ACE1|]. split; [exact SVE1'|]. split; [exact ACB1|]. split; [exact ACF1| exact SVA1]. }
  (* [comment removed for export] *)
  set (XS' := XS ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 2); (sh ff, sh ff + fshn 2)]%Z).
  assert (FXS' : Forall (fs_scratch H LF) XS').
  { subst XS'. apply Forall_app. split; [exact FXS| exact (fs_scratch_of_fresh H _ _ _ _ FF)]. }
  assert (FRX : forall a, (ff <= a < ff + 256 \/ Z.shiftr ff 3 + 2147450880 <= a < Z.shiftr ff 3 + 2147450880 + 32 \/ a = fp) -> rin_ivs XS' a).
  { intros a Ha. subst XS'. apply rin_ivs_app. right. rewrite SHFF in Ha. change (fsz 2) with 256. change (fshn 2) with 32. cbn [rin_ivs fst snd].
    destruct Ha as [Ha|[Ha|Ha]]; [right; right; left; exact Ha| right; right; right; left; exact Ha| right; left; clear - Ha; lia]. }
  assert (XP1 : xpres H LBin SP (hread_X P Ev fb stb [] [] ++ XS') m0 m1).
  { eapply xpres_trans.
    - eapply xpres_weaken; [exact XP0| clear; lia| intros b K; exact K|].
      intros a Ha. apply rin_ivs_app in Ha. apply rin_ivs_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right]. subst XS'. apply rin_ivs_app. left. exact Ha.
    - eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP| exact MU1| exact WM1|] | clear; lia| exact SUBin| intros a K; exact K].
      unfold rs_W1. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]; cbn [fst snd].
      + left. clear - CEIL SPC. lia.
      + right. intros a Ha. unfold hread_X, put_X. cbn. do 3 right. left. exact Ha.
      + right. intros a Ha. apply rin_ivs_app. right. subst XS'. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. left. exact Ha.
      + right. intros a Ha. apply rin_ivs_app. right. subst XS'. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. right; left. exact Ha.
      + right. intros a Ha. apply rin_ivs_app. right. subst XS'. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. right; right; left. change (fsz 2) with 256. exact Ha.
      + right. intros a Ha. apply rin_ivs_app. right. subst XS'. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. right; right; right; left. change (fshn 2) with 32. exact Ha. }
  set (C := mkC bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp (Z_to_bv 64 ATP) F fc MXc CXc) in *.
  set (w0 := mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) in *.
  assert (WMN : 0 <= wM N w0) by (subst w0; unfold wM; cbn_w; clear - NR; unfold zlength; nia).
  destruct ALT as [[Z0 EMS] | [POS EMS]].
  - (* [comment removed for export] *)
    eapply (rs_loop (Datatypes.S (Z.to_nat (wM N w0))) C MA MR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra fr (wM N w0) w0);
      [exact STC0 | exact PLC0 | exact R0 | exact RA | clear - WMN; lia |].
    unfold rs_at_doread, rs_core, rs_frames. subst C w0. cbn_w. cbn [cfg_ms cfg_model ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    exists rax, u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, s5, s6, u3, u4, u5, u6, m1, s, errv, EC_clear, 0,
           spa, ff, fp, (CB 8 jm), [CB 24 jt], gap, hw, [CB 24 jo], j56, [CB 24 je], j120, XS'.
    split; [exact EMS|]. split; [exact NS11|]. split; [exact KREL1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|].
    split; [| clear; lia].
    split; [exact RM1|]. split; [exact RP0|]. split; [exact ALK|]. split; [exact ST1|].
    split; [split; [exact FRM1| split; [exact SAVED1| split; [exact FR0'| split; [exact SZFR| exact FAKE1]]]]|].
    split; [exact FF|]. split; [exists m; exact RF|].
    split; [exact FXS'|]. split; [exact FRX|]. split; [exact XP1|]. split; [clear; lia|]. split; [clear - SZS; lia|]. exact NRB.
  - (* [comment removed for export] *)
    destruct FRM1 as (LOW1 & SLOTS1 & MW801 & MSZ1 & SH161 & J961 & F1201 & TMP1 & TSZ1 & GAP1 & GSZ1 & SPA1).
    eapply (ahh_evt_then H HH); [exact KREL1| exact EMS| |].
    { eapply (rs_parse rax sp gp (Z_to_bv 64 ATP) u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5 s6 u3 u4 u5 u6 F fc m1 lo spa ff Ev bs fb P 0 FB (CB 8 jm) [CB 24 jt] gap);
        [ split; [exact LOW1| split; [exact SLOTS1| split; [exact MW801| split; [exact MSZ1| split; [exact SH161| split; [exact J961| split; [exact F1201| split; [exact TMP1| split; [exact TSZ1| split; [exact GAP1| split; [exact GSZ1| exact SPA1]]]]]]]]]]]
        | exact FBC1 | exact FB8 | exact APF | exact ACF1
        | exact B0 | exact BIO | clear - BOLE; lia | exact BCE
        | clear - PQ4 PQ3; unfold AAPP_HI in *; lia | clear; lia | clear - R4 R3; unfold AAPP_HI in *; lia
        | exact F0 | clear - F2 AF1; lia
        | clear - LOS BSV; lia | exact CEIL | exact MI1 ]. }
    intros msF2 mo2 KREL2 MP2 (m2 & jtl & EMS2 & MU2 & WM2 & MI2 & FRM2).
    (* [comment removed for export] *)
    assert (QW2 : Forall (qwin (bv_unsigned sp) ff) [(spa + 128, spa + 152)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LOS BSV SPA1; lia| apply Forall_nil]. }
    pose proof (RWmF_quiet H HH C MA LF' w0 s errv EC_clear m1 m2 m _ (bv_unsigned sp) ff fp STC0 RP0 RM1 SUBF FF RF HI ltac:(subst C; cbn_w; clear - FRB128; lia) MU2 WM2 MI2 QW2) as RM2.
    assert (HW2 : Forall (fun iv : Z * Z => aceil <= fst iv) [(spa + 128, spa + 152)]%Z) by (apply Forall_cons; [cbn [fst snd]; clear - CEIL LOS BSV SPA1; lia| apply Forall_nil]).
    pose proof (rs_fake_high LF m1 m2 ff fp hw [CB 24 jo] j56 [CB 24 je] j120 248 248 _ FF FAKE1 MU2 WM2 HW2) as FAKE2.
    assert (SAVED2 : rw_cells bsegs m2 (bv_unsigned sp + -104) (rs_sv s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (rw_cells_transport bsegs); [exact SAVED1| exact MU2| exact WM2|]. cbn [disjoint_from fst snd]. split; [right; clear - GSZ1; lia| exact I]. }
    assert (FR02 : rw_cells bsegs m2 (bv_unsigned sp) fr).
    { eapply (rw_cells_transport bsegs); [exact FR0'| exact MU2| exact WM2|]. cbn [disjoint_from fst snd]. split; [right; clear - GSZ1; lia| exact I]. }
    assert (ST2 : stk bsegs m2 lo spa) by (eapply (stk_transport_disjoint bsegs); [exact ST1| exact MU2| exact WM2| cbn [disjoint_from fst snd]; split; [left; clear; lia| exact I]]).
    assert (XP2 : xpres H LBin SP (hread_X P Ev fb stb [] [] ++ XS') m0 m2).
    { eapply xpres_trans; [exact XP1|].
      eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP1| exact MU2| exact WM2|] | clear; lia| exact SUBin| intros a K; exact K].
      apply Forall_cons; [cbn [fst snd]; left; clear - CEIL LOS BSV SPA1 SPC; lia| apply Forall_nil]. }
    eapply (ah_seq H HH).
    { eapply (rs_put_round H HH BPUT C MA MR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra fr (wM N w0) w0); [exact STC0 | exact PLC0 | exact R0 | exact RA |].
      unfold rs_at_put, rs_core, rs_frames. subst C w0. cbn_w. cbn [cfg_ms cfg_model ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
      exists u0, u1, u2, b4, b5, b6, b7, s5, s6, u3, u4, u5, u6, m2, s, errv, EC_clear, 0,
             spa, ff, fp, (CB 8 jm), [C8 (wz (fb_in FB)); C8 (wz (fb_size FB)); CB 8 jtl], gap, hw, [CB 24 jo], j56, [CB 24 je], j120, XS'.
      split; [exact EMS2|].
      split; [clear - POS; lia|]. split; [exact NS11|]. split; [exact KREL2|]. split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP1 MP2))|].
      split; [| clear; lia].
      split; [exact RM2|]. split; [exact RP0|]. split; [exact ALK|]. split; [exact ST2|].
      split; [split; [exact FRM2| split; [exact SAVED2| split; [exact FR02| split; [exact SZFR| exact FAKE2]]]]|].
      split; [exact FF|]. split; [exists m; exact RF|].
      split; [exact FXS'|]. split; [exact FRX|]. split; [exact XP2|]. split; [clear; lia|]. split; [clear - SZS; lia|]. exact NRB. }
    intros cf2 [D | (w2 & _ & AD)]; [apply (ah_done H HH); exact D|].
    eapply (rs_loop (Datatypes.S (Z.to_nat (wM N w0)))); [exact STC0 | exact PLC0 | exact R0 | exact RA | clear - WMN; lia | exact AD].
Qed.
End HCW.

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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf X8_F_insert2 X8_F_insert4 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit X8_A_kit X8_A_kit2 X8_A_kit4 X8_A_kit5 X8_A_kit13 X8_S_kit3 AXImgKit X8_cobj X8_rsfree X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_reg3 X8_asio_stmt_sched3 X8_asio_stmt_sp2 X8_asio_stmt_use X8_stream_stmt X8_stream_stmt2 X8_sct_stmt X8_state1_stmt X8_state2_stmt X8_P_ftab_rep X8_pst X8_put_stmt X8_read_stmt X8_sro_stmt X8_dtor_stmt X8_D_dl X8_D_mb X8_D_pd AXFuzz_stmt X8_H_stmt X8_H_stmt2 X8_H_kit1 X8_H_C X8_H_D X8_H_E X8_H_F X8_H_G X8_H_G2 X8_H_H X8_H_cost X8_H_I0 X8_H_kit X8_H_I.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma hz_LB2_members : forall N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB,
  let LB2 := hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB in
  In (p1, allocb, SZ_ALLOCIMPL) LB2 /\ In (p2, regb, NEWSZ_REG) LB2 /\ In (p3, cfgb, NEWSZ_CFG) LB2 /\ In (p4, schedb, NEWSZ_SCH) LB2
  /\ In (q1, v, NEWSZ_SSVC) LB2 /\ In (q2, q, SZ_SPCI_IMPL) LB2 /\ In (q3, stb, SZ_SPCI_STATE) LB2 /\ In (q4, va, 8) LB2
  /\ (1 <= N -> In (q5, A, N) LB2) /\ (forall b, In b LB -> In b LB2).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_H_E.hz_LB2); constr:(@Stdlib.ZArith.BinInt.Z.eqb_spec); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.reflect); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_ALLOCIMPL); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SPCI_IMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_SSVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_SCH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_CFG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_REG); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.not)|] [|@b; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @K; @Hb; @e; @H; @n; @r; @LB2; @LB; @schedb; @p4; @cfgb; @p3; @regb; @p2; @allocb; @p1; @va; @q4; @stb; @q3; @q; @q2; @v; @q1; @A; @q5; @N|] "#)%#>#y#A#B#D#$#(#i###%#7#G#*#)#&#6#5#4#3#2#1#0#/#.#-#,#+#8#K#j#'#h#9#P#U#V#W#X#Y#Z#;#T#:#C#J#H#N#R#<#=#c#m#l#k#p#f#v#>#y#F#b#d#e#g#o#n#q#r#s#t#w#x#u#a#z#I#^#O#M#]#L#Q#\#`#_#E#S#[0#l&#m%#n'#o&#p&#q%#r&#s'#t%#u&#v7#w$#x%US<E-PQRS#S$S%S&S'S(S)S*S+MNGS/OJFIVSLKL#CKLVS=KLVS>$#VS=S,L#CS1LVS?DCVS?#C%DCS&S'%%C#S2%DCS$S%.S:.#.#US@#%+C'#%DCRS#%-C#S3%DCPQ%/C#S4%DCS,K%1C#S5%DCMN%3C#S6%DCS*S+%5C#S7%DCS(S)%7C#S8)75G)8$#)9'#):*#);-#)<0#)=3#)>6#%DCS;S1%AC#S9)A#%nS-#$##s#+F#%#&##&s##A#&s#$0$&s#%3%&s#&6&&s#'9'&s#(<(&s#)?)&s#*B*US@S:/#S9%DCS9S;%s#/C#SA%DCS#S$%s#1C#s#)%DCQR%s#3C#S3%DCKP%s#5C#S4%DCS1S,%s#7C#S5%DCS+M%s#9C#S6%DCS)S*%s#;C#S7%DCS'S(%s#=C#S8%DCS%S&%s#?C#S2)s#?#N)s#@&#)s#A)#)s#B,#)s#C/#)s#D2#)s#E5#)s#F8#)s#G;#nS-#$##s#QJ#%#$##&s#I=#k##@#&EIN%s#MCs#Cs#E%s#NCs#BS3%s#OCs#AS4%s#PCs#2S5%s#QCs#?S6%s#RCs#>S7%s#SCs#QS8%s#TCs#PS2)s#T#M)s#U%#)s#V'#)s#W)#)s#X+#)s#Y-#)s#Z/#)s#[1#%DCSAS9%s#^C#SB)s#^#%nS-#$##s#hO#%#&##&EF#k##8#k#$E#(;#(s#<#(s#>#(s#@#(s#B#(s#D#(s#F#(s#H#(s#J##CS;L&s#ms#ks#Q&s#ns#Zs#R&s#os#]s#S&s#ps#`s#T&s#qs#cs#U&s#rs#fs#V&s#ss#is#W&s#ts#ls#X&s#us#Is#1k##s#L#&EF>k##s#/#k#$E#(&#()#(+#(-#(/#(1#(3#(5##s$&s#zs$$#s$'s#ys$%#s$(s#xs$&#s$)s#ws$'#s$*s#vs$(#s$+s#us$)#s$,s#ts$*#s$-s$+s$+&s$.s$,G$$#$&#$(#$*#$,#$.#$0#+s$6s$4,,+#'.+#'0+#'2+#'4+#'6+#'8+#':+#m##s#0#s$@s$8s$,#s$As$7s$-#s$Bs$6s$.#s$Cs$5s$/#s$Ds$4s$0#s$Es$3s$1#s$Fs$2s$2#s$Gs$Es$3&s$Hs$4G$$#$&#$(#$*#$,#$.#$0#+s$Ps$<,-*#'/*#'1*#'3*#'5*#'7*#'9*#m##s#H#s$Ys$Qs$G#s$Zs$Ps$H#s$[s$Os$I#s$\s$Ns$J#s$]s$Ms$K#s$^s$Ls$L#s$_s$Ks$M#s$`s$^s$N&s$as$OG$$#$&#$(#$*#$,#$.#$0#+s$is$W,.)#'0)#'2)#'4)#'6)#'8)#m##s#_#s$qs$is$a#s$rs$hs$b#s$ss$gs$c#s$ts$fs$d#s$us$es$e#s$vs$ds$f#s$ws$cs$g#s$xs$vs$h&s$ys$iG$$#$&#$(#$*#$,#$.#$0#+s%%s$q,/(#'1(#'3(#'5(#'7(#m##s#u#s%,s%$s$z#s%-s%#s${#s%.s$~s$|#s%/s$}s$}#s%0s$|s$~#s%1s${s%##s%2s$zs%$#s%3s%1s%%&s%4s%&G$$#$&#$(#$*#$,#$.#$0#+s%<s%.,0'#'2'#'4'#'6'#m##s$.#s%Bs%:s%6#s%Cs%9s%7#s%Ds%8s%8#s%Es%7s%9#s%Fs%6s%:#s%Gs%5s%;#s%Hs%4s%<#s%Is%Gs%=&s%Js%>G$$#$&#$(#$*#$,#$.#$0#+s%Rs%F,1&#'3&#'5&#m##s$B#s%Ws%Os%M#s%Xs%Ns%N#s%Ys%Ms%O#s%Zs%Ls%P#s%[s%Ks%Q#s%\s%Js%R#s%]s%Is%S#s%^s%\s%T&s%_s%UG$$#$&#$(#$*#$,#$.#$0#+s%gs%],2%#'4%#m##s$U#s%ks%cs%c#s%ls%bs%d#s%ms%as%e#s%ns%`s%f#s%os%_s%g#s%ps%^s%h#s%qs%]s%i#s%rs%ps%j&s%ss%kG$$#$&#$(#$*#$,#$.#$0#+s%{s%s,3$#m##s$gUSMSCUS<SCVSNCFUSOCUSPCVSDCs%ZVSQCS:XSEC$SR#[SF&S0HHS.#SGUSSHVSDCLXSEC'ST#[SF*S0HHS.#SGZSU+S0HHS.O\SH,S0HHS.$'#\SH-S0HHS.)(#VSV.S.+S-SIVSWIJ#S-#SIm$%#WSXCLFXSYIJ$#l#%*)#l#&87#l#';:#j#(C#j#)SJ#/s%qI#CFLk###Ok##%#k#(C#k#)SJ#XISKSBFJl#**$#m##SKVSZs%0#j#+s%z##Es%[F#Es%[F#Es%[F#Es%[F#Es%[F#Es%[F#Es%[F#Es%[F&EFM$$#$&#$(#$*#$,#$.#$0#'+*I'-*#'/*#'1*#'3*#'5*#'7*#'9*#m##s%Hj#,s%u#j#$E#*s%Ls%I>#*s%Os%Is#F#*s%Qs%Is#Z#*s%Ss%Is#o#*s%Us%Is$)#*s%Ws%Is$@#*s%Ys%Is$X#*s%[s%Is$q#*s%]s%Is%/#(s%^s%Jm#$#j#-s%a#U#IUS[s%c&s&rs&ps&S&s&ss&_s&T&s&ts&bs&U&s&us&es&V&s&vs&hs&W&s&ws&ks&X&s&xs&ns&Y&s&ys&qs&Z&s&zs&Ns&5k##s&Q#&EFs%|k##s&4#k#$E#(&#()#(+#(-#(/#(1#(3#(5##s'+s&is')$s%ds%U'$#s%Mm##:#s'/s&ms&w$s%Ns%?'$#s%8m##=#s'3s&qs&}$s%9s%*'$#s%$m##@#s'7s&us''$s%%s$r'$#s$mm##s###s';s&ys'-$s$ns$_'$#s$[m##s#&#s'?s&}s'3$s$\s$M'$#s$Jm##s#)#s'Cs'%s'9$s$Ks$<'$#s$:m##s#,#s'Gs')s'?$s$;s$,'$#s$+m##s#/#s'Ks&{s&{#s'Ls&zs&|#s'Ms&ys&}#s'Ns&xs&~#s'Os&ws'##s'Ps&vs'$#s'Qs&us'%#s'Rs&ts'&#s'Ss&ss''&s'Ts'(N$$#$&#$(#$*#$,#$.#$0#$2#+s']s'1,5$#j#.s'5#m##s#C#Es&bF$s#ws#h'$#s#am##s#Fj#,s&x#j#$E#*s#Js#G)#*s#Ms#G@#*s#Os#Gs#%#*s#Qs#Gs#*#*s#Ss#Gs#/#*s#Us#Gs#4#*s#Ws#Gs#9#*s#Ys#Gs#>#*s#[s#Gs#C#(s#\s#Hm#$#j#/s#_#U#InS>$s'v%#$#0s&gF#%$#-s#b$#/#l#$s'xS-#l#0s'}s'z#%s'xCs'fS2-KPQRS#S$S%S&S'S(S)S*S+MNGS/OJF&s'y$#%s'{Cs'kS8&s'{#%%DCGS/%s'~C#S7&s'~#(%DCOJ%s(%C#S6&s(%#+%s('Cs'yS5&s('#-%s()Cs(%S4&s()#/%s(+Cs()S3&s(+#1%s(-Cs'us(%&s(-#3/s'aK%s(0Cs'ZS,-S,KPQRS#S$S%S&S'S(S)S*S+MNGS/OJ&s(1$#k##&#&EIJ-S1S,KPQRS#S$S%S&S'S(S)S*S+MNGS/O&EF#k##%#k#$E#((#(.#(1#(4#(7#(:#(>#(B#(s#%#m#s#)#l#1s(Js(K#j#2s(L#j#3C#j#4D#j#5C#j#6D#j#7C#j#8D#j#9C#j#:D#j#;C#j#<D#j#=C#j#>D#j#?C#j#@D#j#AC#j#BD#j#CC#j#DD#j#EC##"). Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis H8 : asan_rt_hyps8 H.
  Hypothesis ATR : incl TRLIST (as_TR H).
  Variable MA : Z.

  (* [comment removed for export] *)
  Definition hz_cost3 (N : Z) : Z := hz_cost2 H N + as_Cm H MA + as_Cf H (sro_phi0 N).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hzK5 (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
      (m0 : mem) (mo : Model) : config -> Prop :=
    fun cf => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (errv : word) (s' : as_St H) (spa ff fp : Z) (gap : list cell) (p1 : bptr) (allocb : Z) (p2 : bptr) (regb : Z) (p3 : bptr) (cfgb : Z) (p4 : bptr) (schedb : Z) (j24 j4 j16 j40 j32b j40b j392 : list byte) (XS : list (Z * Z)) (q1 : bptr) (v : Z) (q2 : bptr) (q : Z) (q3 : bptr) (stb : Z) (q4 : bptr) (va : Z) (q5 : bptr) (A : Z) (LB5 FBB : list block) (FB Fs : fbv) (fds sds : list byte) (nr : Z),
      as_VIS H s' (cfg_ms cf) = MS (mkR (Z_to_bv 64 P_HZ_RET_PDT) (Z_to_bv 64 spa) gp tp t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                       (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + 2147450880)) (Z_to_bv 64 (ff + 128)) (Z_to_bv 64 (ff + 208)) (Z_to_bv 64 (ff + 64))
                                       (Z_to_bv 64 (ff + 272)) (Z_to_bv 64 (ff + 352)) (Z_to_bv 64 ff) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                                  F (ret_pc (Z_to_bv 64 P_HZ_RET_PDT)) fc None m (seg_rom bsegs)
      /\ (spa = bv_unsigned sp + -160 \/ spa = bv_unsigned sp + -176)
      /\ fresh_frame H LF 4 ff fp
      /\ as_AKREL H s' cf
      /\ as_MPRES H mo (cfg_model cf)
      /\ as_RHEAP H s LB m0
      (* [comment removed for export] *)
      /\ as_RHEAP H s' LB5 m
      /\ Permutation LB5 (FBB ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB))
      /\ fbb_ok FB FBB
      (* [comment removed for export] *)
      /\ AFlatBuf LB5 m (ff + 128) FB fds
      /\ fb_cap FB <= CAPMAX N
      /\ (FB <> FB_empty -> blk_fresh H (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB) spa (fb_begin FB) (fb_cap FB))
      /\ rw_cells bsegs m (spa + 32) (BasicStreamCells stb)
      /\ AStateBlock LB5 m stb (ff + 208) q (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds
      /\ ((N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ fb_begin Fs = A /\ fb_end Fs = A + N))
      (* [comment removed for export] *)
      /\ rw_cells bsegs m spa [CB 24 j24; C8 (Z_to_bv 64 ff)]
      /\ rw_cells bsegs m (spa + 64) gap
      /\ Z.of_nat (cells_size gap) = bv_unsigned sp + -96 - (spa + 64)
      /\ rw_cells bsegs m (bv_unsigned sp + -96) (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m ff (hz_hdr spa ++ [C8 (Z_to_bv 64 AVP_CFGMAKER); C4 (wz 4294967295); CB 4 j4] ++ [CB 16 j16])
      /\ rw_cells bsegs m (ff + 88) [CB 40 j40]
      /\ rw_cells bsegs m (ff + 176) ([CB 32 j32b] ++ [C8 (Z_to_bv 64 allocb); C8 (Z_to_bv 64 regb); C8 (Z_to_bv 64 schedb)] ++ [CB 40 j40b])
      /\ rw_cells bsegs m (ff + 624) [CB 392 j392; C8 (Z_to_bv 64 fp)]
      /\ rw_cells bsegs m (Z.shiftr ff 3 + 2147450880) hz_sh3
      /\ rw_cells bsegs m fp [C1 (b8 1)]
      (* [comment removed for export] *)
      /\ AScheduler LB5 m schedb (mkSCH (sched_hdr (ff + 208) cfgb) 0 0 0)
      /\ ARegistry LB5 m regb (ff + 208) v 0
      /\ AConfigSvc LB5 m cfgb (cfg_hdr (ff + 208))
      /\ AAllocImpl LB5 m allocb
      /\ AStreamSvc LB5 m v (mkSVC AVP_SSVC 0 AG_ID_SSVC (ff + 208) schedb P_A_DESTROY_ALLOC_SSVC) q
      /\ AImplBlock LB5 m q (impl_after va stb)
      /\ rblock_range v NEWSZ_SSVC
      /\ rblock_range q SZ_SPCI_IMPL
      /\ rblock_range stb SZ_SPCI_STATE
      /\ rblock_range va 8
      /\ (1 <= N -> rblock_range A N /\ (A + N <= stb \/ stb + SZ_SPCI_STATE <= A))
      (* [comment removed for export] *)
      /\ AXImg m
      /\ acanary m
      /\ AHStat FT m
      /\ rw_cells bsegs m AERRNO [C4 errv]
      /\ as_rauxv_ok H m B
      /\ mem_inv bsegs m
      /\ stk bsegs m lo spa
      /\ as_RFS H ((4, ff, fp) :: LF) m
      /\ ACONST m
      /\ stack0 m lo shi
      /\ Forall (fs_scratch H ((4, ff, fp) :: LF)) XS
      /\ xpres H LB (bv_unsigned sp) ((fr4_XS H ff fp ++ [(AERRNO, AERRNO + 4); (AXH_LO, AXH_HI)]%Z) ++ XS) m0 m
      /\ as_AL H s' >= as_AL H s - hz_cost3 N.


  Lemma hz_E5 : forall (gp s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : as_St H) (LB : list block) (LF : list fframe)
      (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m0 : mem) (mo : Model) (msF : machine_state) (mo4 : Model),
    hz_pure H sp ra D N lo B shi LB LF -> hz_cost3 N <= as_AL H s ->
    hzK4p H MA gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo (mkCfg msF mo4) ->
    as_SR H (hzK5 gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo) (mkCfg msF mo4).
  Proof.
    intros until mo4. intros PU COST3 K.
    pose proof PU as (SPAL & CEIL & LO & SPB & BHI & SP47 & RAE & NR & DAL & D0 & DNH & SHI & INB & DEMP & LFN & BUD & BUDC).
    unfold AFUZZ_STACK in LO. unfold AFUZZ_FRAMES in LFN.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof aceil_facts as (AF1 & AF2 & AF3). pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; lia).
    unfold hzK4p in K. cbn [cfg_ms cfg_model] in K.
    destruct K as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & errv & s' & spa & ff & fp & gap & p1 & allocb & p2 & regb & p3 & cfgb & p4 & schedb & j24 & j4 & j16 & j40 & j32b & j40b & j392 & pad7 & pad2 & XS & q1 & v & q2 & q & q3 & stb & q4 & va & q5 & A & PBn & PB & FBB & FB & Fs & fds & sds & nr & c & S & L & ns & ls & em & h & es & out & insz & outpos & outend
 & VIS & SPA & FF & KREL & MP & HP0 & HP & PERM & PBO & NPO & FOK & CORE & W288 & W336 & FC & FOWN & HDR & HOWN & HDJ & MB & MOWN & BDJ & MSZ & HOFF & PACC & COST & FBU & CPM & FRF & BS & SB & STRM & LOC & GAP & GSZ & SAVED & FRMh & FRMj & FRMi & FRMB & SH & FL & SCH & REG & CFG & AI & SSV & IMP & RBV & RBQ & RBS & RBA & RBAN & XI & CA & HS & ERR & AUX & MI & ST & RF & AC & SK & THR & BACC & FACC & FXS & X0 & AL).
    assert (SPAR : bv_unsigned sp + -176 <= spa <= bv_unsigned sp + -160) by (clear - SPA; lia).
    assert (SPA16 : spa mod 16 = 0) by (clear - SPA SPAL SPR; Z.div_mod_to_equations; lia).
    assert (CEIL' : aceil <= spa) by (clear - CEIL LO SPAR; lia).
    pose proof (ff_facts _ _ _ _ _ FF) as (_ & _ & _ & _ & F1 & F2 & F3 & F3' & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & APF & APP1 & SHFF & SF1 & SF2 & SF3 & NSB).
    fs_nums_in F2. fs_nums_in F9. fs_nums_in SF2. fs_nums_in SF3. fs_nums_in APF.
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO in F1, F2, F4, F5, F6, F7, F8, F9, F10, F11, SF1, SF2, SF3, NSB.
    pose proof (ff_sh_in_fsb H _ _ _ _ FF) as (SHF1 & SHF2). fs_nums_in SHF2.
    pose proof (aapp_not_shadowland _ _ APF) as NSF. unfold ALOWSH_LO, AHI_LO in NSF.
    set (LB2 := hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB) in *.
    pose proof (hz_LB2_members N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB) as MEM2. cbn zeta in MEM2. fold LB2 in MEM2.
    destruct MEM2 as (IN1 & IN2 & IN3 & IN4 & IN5 & IN6 & IN7 & IN8 & IN9 & SUB02).
    set (LBc := PBn ++ LB2) in *.
    assert (INc : forall b, In b LB2 -> In b LBc) by (intros b Hb; subst LBc; apply in_or_app; right; exact Hb).
    assert (INf : forall b, In b FBB -> In b LBc).
    { intros b Hb. subst LBc. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    pose proof (ah_nodup H HH _ _ _ HP) as NDc.
    assert (ND2 : List.NoDup (map blk_id (FBB ++ LB2))).
    { pose proof (NoDup_ids_perm LBc ((PB ++ FBB) ++ LB2) ltac:(subst LBc; apply Permutation_app_tail; exact PERM) NDc) as X.
      rewrite <- app_assoc in X. exact (NoDup_ids_app_r _ _ X). }
    pose proof (rblock_bounds _ _ RBS) as (T1 & T2 & T3 & T4 & T5 & T6). unfold SZ_SPCI_STATE in T3, T5. unfold AIMG_TOP in T4. pose proof RBS as (TP & T16 & _ & APS & _).
    idtac "E5 start".
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply hz_F1; [clear - F1; lia| clear - F2 AF1; lia| exact MI]|].
    intros msF5 mo5 KREL5 MP5 VIS5.
    pose proof (parser_dtor_spec H HH ATR) as PD. unfold aparser_dtor_stmt in PD.
    assert (AOP : aobj LBc ((4, ff, fp) :: LF) (ff + 272) PARSER_SIZE_D) by (eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; unfold PARSER_SIZE_D; clear; lia]).
    destruct HOFF as [HOFF1 HOFF2]. unfold PARSER_SIZE in HOFF1, HOFF2, PACC.
    eapply (ah_seq H HH).
    { eapply PD with (P := ff + 272) (lo := lo) (B := B) (shi := shi) (LB := LBc) (LF := (4, ff, fp) :: LF) (s := s') (c := c) (pad7 := pad7) (pad2 := pad2)
                    (S := S) (L := L) (ns := ns) (ls := ls) (em := em) (h := h) (es := es) (out := out) (insz := insz) (outpos := outpos) (outend := outend) (errv := errv);
        [ exact VIS5 | reflexivity
        | exact CORE | replace (ff + 272 + 288) with (ff + 560) by (clear; lia); exact W288 | replace (ff + 272 + 336) with (ff + 608) by (clear; lia); exact W336
        | replace (ff + 272 + 80) with (ff + 352) by (clear; lia); exact FC | exact FOWN
        | replace (ff + 272 + 128) with (ff + 400) by (clear; lia); exact HDR | exact HOWN | exact HDJ
        | replace (ff + 272 + 168) with (ff + 440) by (clear; lia); exact MB | exact MOWN | exact BDJ
        | exact HP | exact KREL5 | exact AUX
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); clear - SPB SPAR; lia
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact ST | exact CEIL
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); unfold APARSER_DTOR_STACK, ABFIELDS_DTOR_STACK, RSFREE_STACK, AFREE_STACK; clear - LO SPAR; lia
        | rewrite EA; exact ERR | exact MI | reflexivity
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact SPA16
        | exact AOP | clear - F3; Z.div_mod_to_equations; lia | unfold PARSER_SIZE_D; exact PACC
        | unfold PARSER_SIZE_D; intros ML; apply HOFF2; clear - ML; lia
        | unfold PARSER_SIZE_D; intros TL; apply HOFF1; clear - TL; lia
        | exact RF | exact AC | exact SK
        | unfold hz_cost3 in COST3; pose proof (CM0 0 ltac:(clear; lia)) as KZ; clear - COST COST3 AL KZ; lia ]. }
    idtac "E5 after dtor".
    intros [msF6 mo6] PO. unfold aparser_dtor_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m6 & s6' & LB6
                    & VIS6 & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & HP6 & MEM6 & _ & _ & CORE6 & HDR6 & W288' & W336' & XPC & RF6 & AC6 & SK6 & PACC6 & AL6).
    rewrite (unsigned_lit spa) in ST6, XPC by (clear - SPAR SPR CEIL LO AF1; lia). rewrite EA in ERR6.
    clear PD CORE6 HDR6 W288' W336' PACC6.
    (* [comment removed for export] *)
    assert (PERM6 : Permutation LB6 (FBB ++ LB2)).
    { apply perm_of_members; [exact (ah_nodup H HH _ _ _ HP6)| exact ND2|]. intros b. rewrite MEM6. split.
      - intros [Hb NPb]. subst LBc. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply in_or_app; right; exact Hb].
        pose proof (Permutation_in _ PERM Hb) as K. apply in_app_or in K. destruct K as [K|K]; [exfalso; exact (NPb (PBO _ K))|].
        apply in_or_app. left. exact K.
      - intros Hb. split; [apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (INf _ Hb)| exact (INc _ Hb)]| exact (NPO _ Hb)]. }
    assert (INr6 : forall b, In b (FBB ++ LB2) -> In b LB6) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERM6| exact Hb]).
    assert (INr2 : forall b, In b LB2 -> In b LB6) by (intros b Hb; apply INr6; apply in_or_app; right; exact Hb).
    assert (SUB06 : forall b, In b LB -> In b LB6) by (intros b Hb; exact (INr2 _ (SUB02 _ Hb))).
    (* [comment removed for export] *)
    assert (KP : forall p0 b0 n0, In (p0, b0, n0) LB2 -> keeps_at LBc LB6 b0).
    { intros p0 b0 n0 Hb0. pose proof (reix_addr H HH _ _ _ _ _ (p0, b0, n0) HP MEM6 (INc _ Hb0) ltac:(apply NPO; apply in_or_app; right; exact Hb0)) as K.
      cbn [blk_addr fst snd] in K. exact K. }
    assert (KPF : forall p0 b0 n0, In (p0, b0, n0) FBB -> keeps_at LBc LB6 b0).
    { intros p0 b0 n0 Hb0. pose proof (reix_addr H HH _ _ _ _ _ (p0, b0, n0) HP MEM6 (INf _ Hb0) ltac:(apply NPO; apply in_or_app; left; exact Hb0)) as K.
      cbn [blk_addr fst snd] in K. exact K. }
    pose proof (AScheduler_reix _ _ _ _ _ (KP _ _ _ IN4) SCH) as SCH6a.
    pose proof (ARegistry_reix _ _ _ _ _ _ _ (KP _ _ _ IN2) REG) as REG6a.
    pose proof (AConfigSvc_reix _ _ _ _ _ (KP _ _ _ IN3) CFG) as CFG6a.
    pose proof (AAllocImpl_reix _ _ _ _ (KP _ _ _ IN1) AI) as AI6a.
    pose proof (AStreamSvc_reix _ _ _ _ _ _ (KP _ _ _ IN5) SSV) as SSV6a.
    pose proof IMP as IMP6a. eapply (AImplBlock_reix LBc LB6) in IMP6a; [| exact (KP _ _ _ IN6)| cbn [im_vcap im_vb impl_after]; intros _; exact (KP _ _ _ IN8)].
    pose proof SB as SB6a.
    eapply (AStateBlock_reix LBc LB6) in SB6a; [| exact (KP _ _ _ IN7)|].
    2:{ cbn [st_fb]. intros NE. destruct STRM as [[N0 E0]|(N1 & FB0 & FE0)]; [exfalso; exact (NE E0)|]. rewrite FB0. exact (KP _ _ _ (IN9 N1)). }
    pose proof FBU as FBU6a.
    eapply (AFlatBuf_reix LBc LB6) in FBU6a.
    2:{ destruct FOK as [[-> ->]|(NE & pf & ->)].
        - intros p n IN. exfalso. pose proof (ah_blocks H HH _ _ _ _ HP IN) as (K1 & _). cbn in K1. clear - K1. lia.
        - exact (KPF _ _ _ (or_introl eq_refl)). }
    clear SCH REG CFG AI SSV IMP SB FBU KP KPF.
    idtac "E5 reindexed".
    (* [comment removed for export] *)
    set (X6 := parser_dtor_X (ff + 272)) in *.
    assert (XW : forall O n, (O + n <= ff + 272 \/ ff + 432 <= O) -> Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) X6).
    { intros O n K0. subst X6. unfold parser_dtor_X. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; clear - K0; lia. }
    assert (XST : Forall (fun iv : Z * Z => snd iv <= spa) X6) by (subst X6; unfold parser_dtor_X; repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; clear - F2 CEIL LO SPAR; lia).
    assert (LOC6 : rw_cells bsegs m6 spa [CB 24 j24; C8 (Z_to_bv 64 ff)]).
    { eapply (xpres_rw_cells H); [exact XPC| exact LOC| split; [left; clear; lia|]]. eapply Forall_impl; [| exact XST]. intros [l h'] Q. cbn [fst snd] in *. clear - Q. lia. }
    pose proof (rw_cells_bound _ _ _ _ GAP) as GB.
    assert (GAP6 : rw_cells bsegs m6 (spa + 64) gap).
    { eapply (xpres_rw_cells H); [exact XPC| exact GAP| split; [left; clear; lia|]]. eapply Forall_impl; [| exact XST]. intros [l h'] Q. cbn [fst snd] in *. clear - Q. lia. }
    assert (SAVED6 : rw_cells bsegs m6 (bv_unsigned sp + -96) (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells H); [exact XPC| exact SAVED| split; [left; clear - SPAR; lia|]]. eapply Forall_impl; [| exact XST]. intros [l h'] Q. cbn [fst snd] in *. clear - Q SPAR. lia. }
    assert (BS6 : rw_cells bsegs m6 (spa + 32) (BasicStreamCells stb)).
    { eapply (xpres_rw_cells H); [exact XPC| exact BS| split; [left; clear; lia|]]. eapply Forall_impl; [| exact XST]. intros [l h'] Q. cbn [fst snd] in *. clear - Q. lia. }
    assert (FRMh6 : rw_cells bsegs m6 ff (hz_hdr spa ++ [C8 (Z_to_bv 64 AVP_CFGMAKER); C4 (wz 4294967295); CB 4 j4] ++ [CB 16 j16])).
    { eapply (xpres_rw_cells H); [exact XPC| exact FRMh|]. unfold hz_hdr. cbn [cells_size csize Nat.add length app]. rewrite <- (app_nil_r X6).
      eapply (xclient_range_aobj H HH); [exact HP6| exact RF6| eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; clear; lia]| clear; lia| apply XW; clear; lia| apply Forall_nil]. }
    assert (FRMj6 : rw_cells bsegs m6 (ff + 88) [CB 40 j40]).
    { eapply (xpres_rw_cells H); [exact XPC| exact FRMj|]. cbn [cells_size csize Nat.add length app]. rewrite <- (app_nil_r X6).
      eapply (xclient_range_aobj H HH); [exact HP6| exact RF6| eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; clear; lia]| clear; lia| apply XW; clear; lia| apply Forall_nil]. }
    assert (FRMi6 : rw_cells bsegs m6 (ff + 176) ([CB 32 j32b] ++ [C8 (Z_to_bv 64 allocb); C8 (Z_to_bv 64 regb); C8 (Z_to_bv 64 schedb)] ++ [CB 40 j40b])).
    { eapply (xpres_rw_cells H); [exact XPC| exact FRMi|]. cbn [cells_size csize Nat.add length app]. rewrite <- (app_nil_r X6).
      eapply (xclient_range_aobj H HH); [exact HP6| exact RF6| eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; clear; lia]| clear; lia| apply XW; clear; lia| apply Forall_nil]. }
    assert (FRMB6 : rw_cells bsegs m6 (ff + 624) [CB 392 j392; C8 (Z_to_bv 64 fp)]).
    { eapply (xpres_rw_cells H); [exact XPC| exact FRMB|]. cbn [cells_size csize Nat.add length app]. rewrite <- (app_nil_r X6).
      eapply (xclient_range_aobj H HH); [exact HP6| exact RF6| eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; clear; lia]| clear; lia| apply XW; clear; lia| apply Forall_nil]. }
    assert (SH6 : rw_cells bsegs m6 (Z.shiftr ff 3 + 2147450880) hz_sh3).
    { eapply (xpres_rw_cells H); [exact XPC| exact SH|]. split.
      - eapply (ffsh_client_range H _ _ _ _ _ _ _ _ FF); [clear; lia| unfold hz_sh3; cbn; fs_nums; clear; lia].
      - rewrite SHFF. subst X6. unfold parser_dtor_X, hz_sh3. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn; clear - NSF SF1 SF2; lia. }
    assert (FL6 : rw_cells bsegs m6 fp [C1 (b8 1)]).
    { eapply (xpres_rw_cells H); [exact XPC| exact FL|]. split; [eapply (fp_client_range H _ _ _ _ _ _ FF)|].
      cbn [cells_size csize Nat.add]. subst X6. unfold parser_dtor_X. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; clear - F5; lia. }
    idtac "E5 frame kept".
    (* [comment removed for export] *)
    assert (SEP6 : forall p b n, In (p, b, n) LB6 -> 0 <= n -> Forall (fun iv : Z * Z => b + n <= fst iv \/ snd iv <= b) X6
                                                         /\ Forall (fun iv : Z * Z => sh b + nsh n <= fst iv \/ snd iv <= sh b) X6).
    { intros p b n IN POS. pose proof (ah_blocks H HH _ _ _ _ HP6 IN) as (X1 & _ & X3 & X4 & X5 & X6' & X7). cbn [blk_addr blk_size fst snd] in X1, X3, X4, X5, X6', X7.
      unfold AFS_SIZE in X6'. split; [apply XW; clear - X6' F8 F9; lia|].
      pose proof (aapp_disjoint_sh ff 1024 b n APF (Z.lt_le_incl _ _ X1) ltac:(pose proof (aapp_bounds _ _ X7 X3) as (_ & _ & K & _); exact (Z.lt_le_incl _ _ K)) X3) as W6.
      subst X6. unfold parser_dtor_X. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; clear - W6; lia. }
    pose proof (SEP6 _ _ _ (INr2 _ IN4) ltac:(unfold NEWSZ_SCH; clear; lia)) as [Q1 Q2]. pose proof (AScheduler_xpres H _ _ _ _ _ _ _ SCH6a XPC Q1 Q2) as SCH6. clear Q1 Q2 SCH6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN2) ltac:(unfold NEWSZ_REG; clear; lia)) as [Q1 Q2]. pose proof (ARegistry_xpres H _ _ _ _ _ _ _ _ _ REG6a XPC Q1 Q2) as REG6. clear Q1 Q2 REG6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN3) ltac:(unfold NEWSZ_CFG; clear; lia)) as [Q1 Q2]. pose proof (AConfigSvc_xpres H _ _ _ _ _ _ _ CFG6a XPC Q1 Q2) as CFG6. clear Q1 Q2 CFG6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN1) ltac:(unfold SZ_ALLOCIMPL; clear; lia)) as [Q1 Q2]. pose proof (AAllocImpl_xpres H _ _ _ _ _ _ AI6a XPC Q1 Q2) as AI6. clear Q1 Q2 AI6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN5) ltac:(unfold NEWSZ_SSVC; clear; lia)) as [Q1 Q2]. pose proof (AStreamSvc_xpres H _ _ _ _ _ _ _ _ SSV6a XPC Q1 Q2) as SSV6. clear Q1 Q2 SSV6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN6) ltac:(unfold SZ_SPCI_IMPL; clear; lia)) as [Q1 Q2]. pose proof (SEP6 _ _ _ (INr2 _ IN8) ltac:(clear; lia)) as [Q3 Q4].
    pose proof (AImplBlock_xpres H _ _ _ _ _ _ _ IMP6a XPC Q1 Q2 ltac:(cbn [im_vcap im_vb impl_after]; intros _; exact Q3) ltac:(cbn [im_vcap im_vb impl_after]; intros _; exact Q4)) as IMP6.
    clear Q1 Q2 Q3 Q4 IMP6a.
    pose proof (SEP6 _ _ _ (INr2 _ IN7) ltac:(unfold SZ_SPCI_STATE; clear; lia)) as [Q1 Q2].
    assert (SB6 : AStateBlock LB6 m6 stb (ff + 208) q (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds).
    { eapply (AStateBlock_xpres H); [exact SB6a| exact XPC| exact Q1| exact Q2| |]; cbn [st_fb]; intros NE;
        destruct STRM as [[N0 E0]|(N1 & FB0 & FE0)]; [exfalso; exact (NE E0)| | exfalso; exact (NE E0)|]; unfold fb_cap; rewrite FB0, FE0;
        pose proof (SEP6 _ _ _ (INr2 _ (IN9 N1)) ltac:(clear - N1; lia)) as [Q3 Q4]; [exact Q3| replace (A + N - A) with N by (clear; lia); exact Q4]. }
    clear Q1 Q2 SB6a.
    assert (FBU6 : AFlatBuf LB6 m6 (ff + 128) FB fds).
    { eapply (AFlatBuf_xpres H); [exact FBU6a| exact XPC| | |].
      - rewrite <- (app_nil_r X6). eapply (xclient_range_aobj H HH); [exact HP6| exact RF6| eapply aobj_frame; [left; reflexivity| cbn; clear; lia| cbn; fs_nums; unfold SZ_FB; clear; lia]
          | unfold SZ_FB; clear; lia| apply XW; unfold SZ_FB; clear; lia| apply Forall_nil].
      - intros NE. destruct FOK as [[E0 _]|(_ & pf & ->)]; [exfalso; exact (NE E0)|].
        destruct FBU6a as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & _ & CAP & _)]; [exfalso; exact (NE E0)|].
        pose proof (SEP6 _ _ _ INp ltac:(clear - CAP; lia)) as [Q3 _]. unfold fb_cap in Q3.
        eapply Forall_impl; [| exact Q3]. intros [l h'] Q. cbn [fst snd] in *. clear - Q. lia.
      - intros NE. destruct FBU6a as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & _ & CAP & _)]; [exfalso; exact (NE E0)|].
        pose proof (SEP6 _ _ _ INp ltac:(clear - CAP; lia)) as [_ Q4]. exact Q4. }
    clear FBU6a.
    idtac "E5 world kept".
    (* [comment removed for export] *)
    assert (FWX : Forall (fun iv : Z * Z => AXDATA_HI <= fst iv \/ snd iv <= AXRELRO_LO) X6).
    { subst X6. unfold parser_dtor_X, AXDATA_HI, AXRELRO_LO. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; left; clear - F1; lia. }
    pose proof (AXImg_xpres_X H _ _ _ _ _ XI XPC FWX) as XI6.
    assert (CA6 : acanary m6).
    { eapply (acanary_xpres_lo H); [exact CA| exact XPC|]. subst X6. unfold parser_dtor_X. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd]; unfold AIMG_TOP; clear - F1; lia. }
    assert (HS6 : AHStat FT m6).
    { eapply (AHStat_local FT FT_local); [exact HS|]. intros a Ha.
      assert (XC : xclient H LB6 spa X6 a).
      { split; [right; left; unfold aimg_client, AXH_LO, AXH_HI in *; clear - Ha; lia|].
        subst X6. unfold parser_dtor_X. cbn [rin_ivs fst snd]. unfold AXH_LO, AXH_HI in Ha. clear - Ha F1. lia. }
      exact (proj1 (XPC a ltac:(unfold AXH_LO, AXH_HI in Ha; clear - Ha; lia) XC)). }
    (* [comment removed for export] *)
    set (XALL := ((fr4_XS H ff fp ++ [(AERRNO, AERRNO + 4); (AXH_LO, AXH_HI)]%Z) ++ XS)) in *.
    assert (X06 : xpres H LB (bv_unsigned sp) XALL m0 m6).
    { eapply (xpres_trans H); [exact X0|]. eapply xpres_reLB; [exact XPC|]. intros a Ha C NX. split.
      + eapply aclient_addr_weaken; [exact C| clear - SPAR; lia| exact SUB06].
      + intros K0. apply NX. subst XALL X6. unfold parser_dtor_X in K0. cbn [rin_ivs fst snd] in K0.
        apply rin_ivs_app. left. apply rin_ivs_app. left. unfold fr4_XS. cbn. clear - K0. lia. }
    idtac "E5 xpres".
    apply (ah_done H HH). unfold hzK5. cbn [cfg_ms cfg_model]. fold LB2.
    exists y0, y1, y2, e0, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, m6, errv, s6', spa, ff, fp, gap.
    exists p1, allocb, p2, regb, p3, cfgb, p4, schedb, j24, j4, j16, j40, j32b, j40b, j392, XS, q1, v, q2, q, q3, stb, q4, va, q5, A.
    exists LB6, FBB, FB, Fs, fds, sds, nr.
    split; [exact VIS6|]. split; [exact SPA|]. split; [exact FF|]. split; [exact KREL6|]. split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP5 MP6))|]. split; [exact HP0|].
    split; [exact HP6|]. split; [exact PERM6|]. split; [exact FOK|].
    split; [exact FBU6|]. split; [exact CPM|]. split; [exact FRF|]. split; [exact BS6|]. split; [exact SB6|]. split; [exact STRM|].
    split; [exact LOC6|]. split; [exact GAP6|]. split; [exact GSZ|]. split; [exact SAVED6|]. split; [exact FRMh6|]. split; [exact FRMj6|]. split; [exact FRMi6|]. split; [exact FRMB6|].
    split; [exact SH6|]. split; [exact FL6|].
    split; [exact SCH6|]. split; [exact REG6|]. split; [exact CFG6|]. split; [exact AI6|]. split; [exact SSV6|]. split; [exact IMP6|].
    split; [exact RBV|]. split; [exact RBQ|]. split; [exact RBS|]. split; [exact RBA|]. split; [exact RBAN|].
    split; [exact XI6|]. split; [exact CA6|]. split; [exact HS6|].
    split; [exact ERR6|]. split; [exact AUX6|]. split; [exact MI6|]. split; [exact ST6|].
    split; [exact RF6|]. split; [exact AC6|]. split; [exact SK6|].
    split; [exact FXS|]. split; [subst XALL; exact X06|].
    unfold hz_cost3. pose proof (CM0 0 ltac:(clear; lia)) as KZ. clear - AL AL6 COST KZ. lia.
  Qed.
End HCW.

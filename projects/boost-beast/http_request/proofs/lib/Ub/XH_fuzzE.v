(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt CXXRep CXXLib CXXLib2 HeapSR_iface CXXHeap XRep XPRep XA_leaves XL_mutex XA_alloc XS_sp XA_registry XA_sched_ctor2 XA_sched_ctor5 XS_ctor XS_ctor2 XS_ctor3 XS_dtor XS_dtor2 XS_dtor3 XF_rep XM_rep XP_req_stmt XP_dtor XP_dtor2
     XA_sched_hdr XFuzz_stmt XFuzz_stmt2 XUbsan XH_fuzzA XH_fuzzB XH_fuzzC XH_fuzzD XH_fuzzH XH_fuzzJ.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 Set StepFast.sf_check := true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac lia ::= lia2w.
(* [comment removed for export] *)
Local Ltac slia_consumed_abort :=
  match goal with
  | |- context [(?A + ?s <= ?A \/ ?h <= ?A)%Z] =>
      first [ assert (A < A + s /\ A < h)%Z by (zify_prune; xlia_noeuclid); fail 2 | fail ]
  | |- _ => idtac
  end.
Local Ltac slia ::= first [ exact I | slia_consumed_abort; slia2w ].
(* [comment removed for export] *)
Tactic Notation "callZc" uconstr(SPEC) tactic3(CLR) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | CLR; post_callZ segs m ]
  end.
Local Ltac clr_stk := idtac; match goal with STx : stk _ _ _ _ |- _ => clear STx end.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac fast_eassumption :=
  first [ lazymatch goal with
          | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
          | |- ro_cells _ _ ?A _ => match goal with H : ro_cells _ _ A _ |- _ => exact H end
          | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
          | |- u8arr _ _ ?A _ => match goal with H : u8arr _ _ A _ |- _ => exact H end
          end
        | eassumption ].
Local Ltac fast_assumption :=
  lazymatch goal with
  | |- ?G => tryif has_evar G then assumption else
             first [ lazymatch G with
                     | rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
                     | ro_cells _ _ ?A _ => match goal with H : ro_cells _ _ A _ |- _ => exact H end
                     | bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
                     | u8arr _ _ ?A _ => match goal with H : u8arr _ _ A _ |- _ => exact H end
                     end
                   | assumption ]
  end.
(* [comment removed for export] *)
Ltac2 fit_clear_arith () : unit :=
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if Bool.and (LiaTuning.zt_is_local id)
                     (Bool.and (LiaTuning.zt_is_prop ty) (Bool.or (LiaTuning.zt_plain_arith ty) (LiaTuning.zt_twoway ty)))
                then Some id else None
      end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac qtauto :=
  first [ solve [ lazymatch goal with H : _ |- _ => clear - H end; tauto ]     (* [comment removed for export] *)
        | solve [ ltac2:(Control.enter fit_clear_arith); tauto ]             (* [comment removed for export] *)
        | tauto ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fzF : forall rax gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P : Z),
  0 <= P -> P + 512 < 2^64 -> mem_inv usegs m ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 P_FZ_RET_PDT) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_PARSER_DTOR) fc None m (seg_rom usegs)
                       /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m)
    (MS (mkR rax (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_FZ_RET_SRO) fc None m (seg_rom usegs)).
Proof.
  ltac2:(KReplay.runc [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_evt_step); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@stdpp.bitvector.definitions.BV); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@LinuxProcessSemantics.Riscv.Instr.OpImm); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@LinuxProcessSemantics.Riscv.Prelude.TNode); constr:(@LinuxProcessSemantics.Riscv.Prelude.TEmpty); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.Riscv.DecodeC.decode_any); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_congT); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Prelude.sext); constr:(@Corelib.Init.Logic.eq_trans); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.alu_addi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.unsigned_Z_to_bv_add); constr:(@Corelib.Init.Logic.f_equal); constr:(@Stdlib.ZArith.BinInt.Z.add_0_r); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.lit_add_lit); constr:(@LinuxProcessSemantics.Riscv.Instr.Jal); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_transMR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_cong1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_btgt); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XH_fuzzA.P_FZ_RET_PDT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XP_dtor2.P_PARSER_DTOR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XH_fuzzA.P_FZ_RET_SRO)|] [|@ms'; @t; @b; @y; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat12; @__sat13; @H; @sfE; @WM; @MU; @HCEILB; @MI; @PHI; @P0; @P; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @a0; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @rax|] "#)P#M$Q#W#-#,#_#+#l#Y###.#)#*#J#I#H#G#F#B#A#@#?#>#=#<#;#:#9#8#7#6#5#4#3#2#1#0#/#E#D#~#S#$#(#C$#$%#K#%#P#&#a#f#g#w#|#}$$$&$'$+$,#p$($3$:$<$B$C$L#k#T#]#`#c#d#i#q#r#s#v#y$*$-$.$/$1$0$4$2$5$8$7$6$9$;$=$>$@$E$H$G$D$F$?$A$I$J$M$N$K#L$O$R$S$T$Q#V#R#x#U#z#\#m#n#b#{#u#t#X#[$)#Q#o#^#h#j#Z#e$P:$;$$<'$=$$>%$?$$@&#_%$A*$B%$C%$D%$E&$F%$G%$H%$I$$JB$K%$L&$M&$N%$O$$P'#S:##########2#USB#%*2#VSX#%2)USB#/IJ#+####'#0S;#'5'1VSY$#7&#4FSCUSZSD%S:%#%#%#%#%#%#%#%#%#%#%#%#%###%#%#%#%#%#%#%#%###############################################'#US[SD/$#%s#&%#%#%#%#%#%#%#%###############################################'#/s#%#+s#%#m#s#W#VSECC8#USF$m#$#VS\#S<5$S<S<VS]FL6FLL%s#p######%###%###%###%###%#####'##S:%#%#########%#%#%###%#%#%#%#####'#%/%#%#%#%#%#%#%#%#####'##4%#####'##8####'#)s$M8)s$NM3$#NOPQRS7S8#S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6K%s#:####%#%#####%###%#####'#)s$]<US^s$]US_F*3D%E$G#(HJ#8S`5#GG6FGG4FG+$#+&#+)#j#$H#)s$jL3N#OPQRS7S8S=S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6KD#s#O%#%#####'#)s$rs#,%s$u##%#######%#####%#%#'#-s$z#.s${$##s%#'#'/-s%%#.s%&%#-s%'s$y.s%(s$z##s$u##2#-#I.$I#XSaSG*(#'s%7USbs%2&s%3D$s%4$#$&s%5S($s%6$#&&s%7S7&s%8S0$s%9)#)$s%:&%#&s%;O&s%<S,$s%=-#-&s%>S$&s%?S4$s%@0#0$s%A&%#$s%B*)#&s%CN&s%DS*$s%E5#5&s%FS=&s%GS2$s%H8#8$s%I&%#&s%JQ&s%KS.$s%L<#<&s%MS&&s%NS6$s%O?#?$s%P&%#$s%Q*)#$s%R21#&s%SS)$s%Ts#$#s#$&s%US8&s%VS1$s%Ws#'#s#'$s%X&%#&s%YP&s%ZS-$s%[s#+#s#+&s%\S%&s%]S5$s%^s#.#s#.$s%_&%#$s%`*)#&s%as#V&s%bS+$s%cs#3#s#3&s%dS3$s%es#5#s#5$s%f%'#&s%gR&s%hS/$s%is#9#s#9&s%jS'&s%kK$s%ls#<#s#<$s%m&%#$s%n*)#$s%o10#$s%p@s#q##s$S####'#)s%vs$,*(E#Gs#wMs#vUSHs%r&s%ss#W,$#VSIFs#g(&#%m$%#,S9S>USJs#](S9#S>m$%#VSES?CUSH#XSKS?Cs#Us#T&%#,%#USLs#e('#%m$%#$s&-?As#Y$s&.#s#%s##&s&/S#$s&0s#+#s#)$s&1%s#L#&s&2S@$s&3$#s#1$s&4s#`s#]s#`$s&5#s#\s#Z$s&6#s#Ys#S&s&7s$H&s&8J$s&9s#R#s#O$s&:#s#Ns#H$s&;'&#$s&<+s$=#*#Ds#&Es$>Gs$=1H#j#%s&?#WSMs#qs&As#oWScSGs$6#0LI)s&D#VSds&Es$90#I)s&G#WSes$<s#xs#vVSfLIZSNs&I*%($#USOs&KUSgLZShCs&L$,L#ZSNs&M.,s$B&#YSPs&N1/s$C#0s$bs#|)s&Q#(s&QJs$cj#&s&R#,s&Ss$e)s&Us$%WSQs&Vs#>#VSis$is$'ZSjs&W)'&$#m#s$js&X(s&Y&#)s&[G3s$m#S@NOPQRS7#S=S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6*#Ks$^Ds$]Es$\(HJ#5s$[EE6FEE4FE+$#+&#+(#j#$H#$s&es#~s#0s#{$s&f#s#zs#t$s&gs#3s#2#$s&hs#7s$i#%s&n######%#############################%#%#%###%#%#%#%#'#-s'%#.s'&$#'S:'.-s'+#.s',%#%s$i2#'@-$#.%$#VSk(#&s'5s%G$s'6s#c#s$4$s'7#s%8s#.*#Ds%:Es%9Gs%8&s'41,s#}#VSIFs$$(s$##%m$%#USJ6(S9#S>m$s#}#XSKS?C/s$n&s#{#,s#{#USL<(s#}#%m$%#&s'Gs#P$s'Hs#u#s$F$s'I#s%Js#@WSM<s'K9WSQs'Ls$4#*%D#Es%MGs%L1H#*9D%Es%OGs%N1H#1H:$s'Qs$`s$bs$}$s'R#s$fs$d$s'S#s$#s$h$s'T#s#zs#|$s'Us%%s$Is%%$s'V#s$Ms$K$s'W#s$rs$)&s'Xs#\$s'Ys$c#s$`$s'Z#s$_s$Y$s'[&%#$s'\*s%]#*#K4Ds%^Es%]1H#j#%s'_#YSPs'`#s#is%rJ$s'a0s#.s$-$s'b#s%c)*#KJDs%dEs%c1H#j#'s'e#,Cs&&YSls%zs&'s#9s#6#XSm%?s%j#YSn><;+#VSos'^s']7Is'_/Is'_7Is'_k##$#k##&#/Is'dWSps'es'dS;j##SR#j#(%#/Is'fk##SR#k#((#8SSUSFSSVSqCS;USrCUSsCVStCS:VSuCIWSvC$#XSwC%Sx#[Sy'SzSTSTSU#S{VS|(SU,S9SVVS}JSA(S9#SVm$%#WS~CIS;XT#JSA$#l#)*)#l#*21#l#+54#j#,C#0JI(CJ#k#,C#UJDl#-'$#l#.@=#l#/s#*s#%#0MI(CM#)s(:E3s&L#T$S@NOPQR#S8S=S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5*#S6s&=Ks&<Ds&;(HJ#5s&:DD6FDD4FD+$#+&#+(#j#$H#*s#@Ks&FDs&EEs&D(H#s$G,Hs$H9s$Fs$ESAS<9s$Hs$ESC#9&s$E%#+'s$Fm#$#XT%F+*#l#097#fSWFs$Hs$DDs%7Es&OGs&Ns$&s#xs%{s#ts#os#ls#fs#C#l#1s$Vs$T#fSWFs&Fs&DEs&=Gs&QMs&Ps&/s%~s%}s%8s%2s%.s%&s$`#)s(RT&3#s&cNOPQRS7S8s&cS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6K)s(TT'*$D#Es&UGs&T(HJ#+#s&Nj#$H#)s(YT(*s&ME#Gs&ZMs&YWT)F%#m#-#l#2s'Ks'J#l#3s'Ns'M#l#4s'Ts'U#j#5s(O#j#6s(Q#j#7s([#j#8C#j#9T*#j#:s(_#j#;s(b#j#<s(f#j#=s(g#j#>s(h#j#?s(i#j#@s(j#j#As(k#j#Bs(l#j#Cs(m#j#Ds(n#j#Es(o#j#Fs(p#j#Gs(q#j#Hs(r#j#Is(s#j#Js(t#j#Ks(u#j#Ls(v#j#Ms(w#j#Ns(x#j#Os(y#j#Ps(z#j#Qs({#j#Rs(|#j#Ss(}#j#Ts(~#j#Us)##j#Vs)$#j#Ws)%#j#Xs)&#j#Ys)'##"). Qed.

Lemma fzG : forall rax gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P : Z),
  0 <= P -> P + 512 < 2^64 -> mem_inv usegs m ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 P_FZ_RET_SDT) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 360)) a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_STREAM_DTOR) fc None m (seg_rom usegs)
                       /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m)
    (MS (mkR rax (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_FZ_RET_PDT) fc None m (seg_rom usegs)).
Proof.
  ltac2:(KReplay.runc [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_evt_step); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@stdpp.bitvector.definitions.BV); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@LinuxProcessSemantics.Riscv.Instr.OpImm); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@LinuxProcessSemantics.Riscv.Prelude.TNode); constr:(@LinuxProcessSemantics.Riscv.Prelude.TEmpty); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.Riscv.DecodeC.decode_any); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_congT); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Prelude.sext); constr:(@Corelib.Init.Logic.eq_trans); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.alu_addi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.unsigned_Z_to_bv_add); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.lit_add_lit); constr:(@LinuxProcessSemantics.Riscv.Instr.Jal); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_transMR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_cong1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_btgt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XH_fuzzA.P_FZ_RET_SDT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.P_STREAM_DTOR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XH_fuzzA.P_FZ_RET_PDT)|] [|@ms'; @t; @b; @y; @sfE; @WM; @MU; @HCEILB; @MI; @PHI; @P0; @P; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @a0; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @rax|] "#)-#L$9#,#+#^#k#-###V#.#)#*#J#I#H#G#F#E#B#A#@#?#>#=#<#;#:#9#8#7#6#5#4#3#2#1#0#/#D#R#(#C#}#~$$#O#$#`#e#d#v#{#|$#$%$&#K$*$'$0#j#S#X#\#Y#&#_#b#f#c#h#p#q#r#u#x$)$,$-$.$+$1$/$2$5$4$3#'#%$6$9$:$;$8#U#Q#w#T#y#[#o#l#m#a#z#t#s#Z$(#P#n#W#]#g#i$78$$$$%'$&$$'%$($$)%$*&$+*$,%$-%$.%$/&$0%$1%$2$$3B$4%$5%$6&$7&$8'#S8##########1#US>#%*1#VSN#%1)US>#3SOH#+####'#/S?#'5'1VSP$#VSQ&#4ESRUSSS@%S8%#%#%#%#%#%#%#%#%#%#%#%#%###%#%#%#%#%#%#%#%###############################################'#USTS@3$#%s#&%#%#%#%#%#%#%#%###############################################'#3s#%#+s#%#m#s#W#VSAIIUSB#USU$m#$#VSV#S95$S9S9VSWEK6EKK%s#p######%###%###%###%#%#%#####'##S8%#%#########%#%#%#%#######%#####'#%0######%#%#%###########'##8%#%#%#%#####'##<####'#(s$Q<(s$RL%s#>######'#/L#(s$Y#2+*MNOPQRS7#S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6J%s#E##%#####%#%#%#%#######'#(s$hs#&USXs$hUSYE*3G%C$D#)FH#USBSZ5#DD6EDD4ED+$#+&#+)#j#$F#(s$uK2M#NOPQRS7S:S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6JG#s#Y%#####'#(s$|s#2#s#)####%###########%###%#######%#####%#%#'#-s%1#.s%2$##s%6'#'/-s%8#.s%9%#':-s%;#.s%<s%2##s%-##1#-#s#J.$s#K#XS[SC+(#'s%KUS\s%F&s%GG$s%H$#$&s%IS($s%J$#&&s%KR&s%LS0$s%M)#)$s%N&%#&s%ON&s%PS,$s%Q-#-&s%RS$&s%SS4$s%T0#0$s%U&%#$s%V*)#&s%WM&s%XS*$s%Y5#5&s%ZS:&s%[S2$s%\8#8$s%]&%#&s%^P&s%_S.$s%`<#<&s%aS&&s%bS6$s%c?#?$s%d&%#$s%e*)#$s%f21#&s%gS)$s%hs#$#s#$&s%iS7&s%jS1$s%ks#'#s#'$s%l&%#&s%mO&s%nS-$s%os#+#s#+&s%pS%&s%qS5$s%rs#.#s#.$s%s&%#$s%t*)#&s%us#_&s%vS+$s%ws#3#s#3/Ks$$(s%z#&s%z#&s%{S3$s%|s#8#s#8$s%}(%#&s%~Q&s&#S/$s&$s#<#s#<&s&%S'&s&&J$s&'s#?#s#?$s&(&%#$s&)*)#$s&*43#$s&+s##s#}##s$j####'#(s&1s$?*(C#Ds$'Ls$&USDs&-&s&.s#[,$#VSEEs#t)&#%m$%#,S;S<USFs#a)S;#S<m$%#VSAS=IUSD#XSGS=Is#Xs#W&%#,%#USHs#i)'#%m$%#$s&D?As#\$s&E#s#%s##&s&FS#$s&Gs#.#s#)$s&H%s#O#&s&ISI$s&J$#s#4$s&Ks#cs#`s#c$s&L#s#_s#]$s&M#s#\s#V&s&Ns$[&s&OH$s&Ps#U#s#R$s&Q#s#Qs#K$s&R'&#$s&S+s$I#*#Gs#&Cs$JDs$I0F#j#%s&V#WSJs#ts&Xs#rWS]SCs$B#VS^s&Zs$C/#s$b(s&\#WS_s$Fs#ys#wVS`Ks$eZSas&^(%s#C$#YSKs&_+)s#D#/s$os#y(s&b#)s&bHs$pj#&s&c#,s&ds$r(s&fs#~WSLs&gs#8#VSbs$vs$$ZScs&h)'&$#m#s$ws&i)s&j&#(s&lD/Ds$t(s&n#2s$|%SIMNOPQR#S:S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6*#Js$fGs$eCs$d)FH#5s$cCC6ECC4EC+$#+&#+(#j#$F#&s&xs$~$s&ys#~#s#{$s&z#s#zs#t$s&{s#0s#/#$s&|s#4s$r##s$H%###################################%#%#%###%#%#%#%#'#-s'9#.s':$#'S8'.-s'?#.s'@%#%s$j1#'@-$#.%$#VSd(#&s'Is%W$s'Js#`#s$4$s'K#s%As#.*#Gs%CCs%BDs%A&s'H1,s#z#VSEEs#})s#|#%m$%#USF6)S;#S<m$s#z#XSGS=I/s$n&s#x#,s#x#USH<)s#z#%m$%#&s'[s#S$s'\s#r#s$F$s']#s%Ss#@WSJ<s'_9WSLs'`s$1#*%G#Cs%VDs%U0F#*9G%Cs%XDs%W0F#0F:$s'es$`s$bs$}$s'f#s$fs$d$s'g#s#|s$h$s'h#s#ws#y$s'is%%s$Fs%%$s'j#s$Js$H$s'k#s$rs$&&s'ls#_&s'ms#^$s'ns$d#s$a$s'o#s$`s$Z$s'p'&#$s'q+s%g#*#J5Gs%hCs%g0F#j#%s't#YSKs'u#s#ms&'H$s'v1s#/s$+$s'w#s%m)*#JHGs%nCs%m0F#j#'s'z#,Is&:YSes&/s&;s#:s#7#XSf%@s%t#YSg?=<+#)Fs#5s%s,Fs%t7s%qs%pS?Sh7s%ss%pSi#7&s%p%#+'s%qm#$#XSjEs#ms#<#fSMEs#ns#iGs$YCs%}Ds%|s#Ks#As%Ds#=s#8s#5s#/+#l#(s#~s#|#fSMEs%ts%rCs%lDs&#Ls%~s%Us%Gs%Fs$Zs$Ts$Ps$Hs$,#(s(/Sk2#s&<MNOPQRS7s&5S#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6J(s(1Sl*$G#Cs&'Ds&&)FH#+#s%|j#$F#(s(6Sm*s%{C#Ds&,Ls&+WSnE%#m#-#l#)s'(s''#l#*s'+s'*#l#+s'1s'2#j#,s(,#j#-s(.#j#.s(8#j#/I#j#0So#j#1s(<#j#2s(?#j#3s(C#j#4s(D#j#5s(E#j#6s(F#j#7s(G#j#8s(H#j#9s(I#j#:s(J#j#;s(K#j#<s(L#j#=s(M#j#>s(N#j#?s(O#j#@s(P#j#As(Q#j#Bs(R#j#Cs(S#j#Ds(T#j#Es(U#j#Fs(V#j#Gs(W#j#Hs(X#j#Is(Y#j#Js(Z#j#Ks([#j#Ls(\#j#Ms(]#j#Ns(^#j#Os(_#j#Ps(`##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma FieldsC_stk : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> stk usegs m Fa (Fa + 48).
Proof.
  intros m Fa S L ns ls em FC. pose proof FC as (NSC & LSC & _ & RB & _ & DL & _).
  destruct RB as (T & _ & ((hd & LK & _) & _) & _).
  destruct (NSCells_lookup _ _ _ _ NSC LK) as [pad RC].
  pose proof DL as (_ & DOM & _). assert (K : is_Some (ls !! (Fa + 32))) by (apply DOM; left).
  destruct (ls !! (Fa + 32)) as [n|] eqn:E; [| exfalso; exact (is_Some_None K)].
  pose proof (LSCells_lookup _ _ _ _ LSC E) as RL.
  eapply stk_merge; [| | ].
  - pose proof (stk_of_rw_cells usegs _ _ _ RC) as K1. rewrite NodeCells_size in K1. exact K1.
  - pose proof (stk_of_rw_cells usegs _ _ _ RL) as K2. rewrite LNodeCells_size in K2.
    replace (Fa + Z.of_nat 32) with (Fa + 32) by lia. replace (Fa + 48) with (Fa + 32 + Z.of_nat 16) by lia. exact K2.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma MBraw_stk : forall m b es out insz outpos outend, MBraw m b es out insz outpos outend -> stk usegs m b (b + 64).
Proof.
  intros m b es out insz outpos outend (ls & R0 & R24 & DL & LSC & _).
  pose proof DL as (_ & DOM & _). assert (K : is_Some (ls !! (b + 8))) by (apply DOM; left).
  destruct (ls !! (b + 8)) as [n|] eqn:E; [| exfalso; exact (is_Some_None K)].
  pose proof (LSCells_lookup _ _ _ _ LSC E) as RL.
  pose proof (stk_of_rw_cells usegs _ _ _ R0) as K0. cbn [cells_size csize Nat.add] in K0.
  pose proof (stk_of_rw_cells usegs _ _ _ RL) as K1. rewrite LNodeCells_size in K1.
  pose proof (stk_of_rw_cells usegs _ _ _ R24) as K2. cbn [cells_size csize Nat.add] in K2.
  eapply stk_merge; [exact K0| | lia]. replace (b + Z.of_nat 8) with (b + 8) by lia.
  eapply stk_merge; [exact K1| | lia]. replace (b + 8 + Z.of_nat 16) with (b + 24) by lia.
  replace (b + 64) with (b + 24 + Z.of_nat 40) by lia. exact K2.
Qed.

(* [comment removed for export] *)
Lemma nodup8_neq : forall (a b c d e f g h : bptr), List.NoDup [a; b; c; d; e; f; g; h] ->
  h <> b /\ h <> c /\ h <> a /\ g <> b /\ g <> c /\ g <> a /\ f <> b /\ f <> c /\ f <> a
  /\ e <> b /\ e <> c /\ e <> a /\ d <> b /\ d <> c /\ d <> a.
Proof.
  intros a b c d e f g h ND.
  inversion ND as [|? ? Na X1]; subst. inversion X1 as [|? ? Nb X2]; subst. inversion X2 as [|? ? Nc X3]; subst.
  cbn in Na, Nb, Nc. clear X1 X2 X3 ND.
  repeat match goal with |- _ /\ _ => split end.
  - intros E. apply Nb. rewrite <- E. do 5 right. left. reflexivity.
  - intros E. apply Nc. rewrite <- E. do 4 right. left. reflexivity.
  - intros E. apply Na. rewrite <- E. do 6 right. left. reflexivity.
  - intros E. apply Nb. rewrite <- E. do 4 right. left. reflexivity.
  - intros E. apply Nc. rewrite <- E. do 3 right. left. reflexivity.
  - intros E. apply Na. rewrite <- E. do 5 right. left. reflexivity.
  - intros E. apply Nb. rewrite <- E. do 3 right. left. reflexivity.
  - intros E. apply Nc. rewrite <- E. do 2 right. left. reflexivity.
  - intros E. apply Na. rewrite <- E. do 4 right. left. reflexivity.
  - intros E. apply Nb. rewrite <- E. do 2 right. left. reflexivity.
  - intros E. apply Nc. rewrite <- E. do 1 right. left. reflexivity.
  - intros E. apply Na. rewrite <- E. do 3 right. left. reflexivity.
  - intros E. apply Nb. rewrite <- E. do 1 right. left. reflexivity.
  - intros E. apply Nc. rewrite <- E. do 0 right. left. reflexivity.
  - intros E. apply Na. rewrite <- E. do 2 right. left. reflexivity.
Qed.

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma StreamSvc_reix : forall s L L' m m0 p0 v S implb,
    hs_RHEAP H s L m0 -> In (p0, v, NEWSZ_SSVC) L -> In (p0, v, NEWSZ_SSVC) L' -> StreamSvc L m v S implb -> StreamSvc L' m v S implb.
  Proof.
    intros s L L' m m0 p0 v S implb HP IN IN' (p & j7 & INp & C). exists p, j7. split; [| exact C].
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP IN ltac:(unfold NEWSZ_SSVC; lia) INp). exact IN'.
  Qed.

  Lemma ImplBlock_reix : forall s L L' m m0 p0 pv b I,
    hs_RHEAP H s L m0 -> In (p0, b, SZ_SPCI_IMPL) L -> In (p0, b, SZ_SPCI_IMPL) L' ->
    (0 < im_vcap I -> In (pv, im_vb I, 8 * im_vcap I) L /\ In (pv, im_vb I, 8 * im_vcap I) L') ->
    ImplBlock L m b I -> ImplBlock L' m b I.
  Proof.
    intros s L L' m m0 p0 pv b I HP IN IN' INV (p & j7 & INp & RB & CH & OK & EV & PM & VC & LE & ST). exists p, j7.
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP IN ltac:(unfold SZ_SPCI_IMPL; lia) INp).
    repeat (split; [fast_assumption|]). destruct ST as [K|(q & junk & INq & RBq & CAP & RC)]; [left; exact K| right].
    exists q, junk. destruct (INV CAP) as [I1 I2].
    rewrite (in_pin H HH _ _ _ _ _ _ _ HP I1 ltac:(lia) INq). split; [exact I2|]. split; [exact RBq|]. split; [exact CAP| exact RC].
  Qed.

  Lemma FlatBuf_reix : forall s L L' m m0 pf a Fb ds,
    hs_RHEAP H s L m0 -> (Fb <> FB_empty -> In (pf, fb_begin Fb, fb_cap Fb) L /\ In (pf, fb_begin Fb, fb_cap Fb) L') ->
    FlatBuf L m a Fb ds -> FlatBuf L' m a Fb ds.
  Proof.
    intros s L L' m m0 pf a Fb ds HP INF (C & OK & LEN & DATA). split; [exact C|]. split; [| split; [exact LEN| exact DATA]].
    destruct OK as [E|(p & IN & RB & CAP & O)]; [left; exact E| right]. exists p.
    assert (NE : Fb <> FB_empty). { intros E. subst Fb. unfold fb_cap, FB_empty in CAP. cbn in CAP. lia. }
    destruct (INF NE) as [I1 I2]. rewrite (in_pin H HH _ _ _ _ _ _ _ HP I1 CAP IN). split; [exact I2|]. split; [exact RB|]. split; [exact CAP| exact O].
  Qed.

  Lemma StateBlock_reix : forall s L L' m m0 p0 pf b ioc implb S ds,
    hs_RHEAP H s L m0 -> In (p0, b, SZ_SPCI_STATE) L -> In (p0, b, SZ_SPCI_STATE) L' ->
    (st_fb S <> FB_empty -> In (pf, fb_begin (st_fb S), fb_cap (st_fb S)) L /\ In (pf, fb_begin (st_fb S), fb_cap (st_fb S)) L') ->
    StateBlock L m b ioc implb S ds -> StateBlock L' m b ioc implb S ds.
  Proof.
    intros s L L' m m0 p0 pf b ioc implb S ds HP IN IN' INF (p & j7 & j16 & j4 & INp & RB & CH & OK & EV & CE & CW & PM & FB & PC & CO & E).
    exists p, j7, j16, j4. rewrite (in_pin H HH _ _ _ _ _ _ _ HP IN ltac:(unfold SZ_SPCI_STATE; lia) INp).
    repeat (split; [fast_assumption|]). split; [eapply FlatBuf_reix; [exact HP| exact INF| exact FB]|].
    split; [exact PC|]. split; [exact CO| exact E].
  Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stream_fb_blk (N A : Z) (Fs : fbv) : Prop :=
  (N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ fb_begin Fs = A /\ fb_end Fs = A + N).

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis RHEAP_canary : forall s LB m, hs_RHEAP H s LB m -> CanaryReads m.
  Variable FT : mem -> Prop.
  Hypothesis FT_local : ft_local FT.

  Definition fzK3p (gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P D N lo B : Z) (ra s0 s1 : word) (LB : list block) (m0 : mem) (mo : Model) : config -> Prop :=
    fun cf => exists rax t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m (s' : PState) (errv : word) (W : fzw) (LBc PB FBB : list block)
                     (FB Fs : fbv) (dss : list byte) (code nr nb : Z)
                     (c : pcore) (pad7 pad2 : list byte) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (h : hdrv)
                     (es : list mbe) (out insz outpos outend : Z) (c232 : cell) (c240 c256 c296 c304 c344 c352 cE : list cell),
      cfg_ms cf = MS (mkR rax (Z_to_bv 64 P) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_FZ_RET_SRO) fc None m (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model cf) /\ hs_MPRES H mo (cfg_model cf)
      /\ mem_inv usegs m /\ stk usegs m lo P
      /\ rw_cells usegs m (errno_addr tp) [C4 errv] /\ hs_rauxv_ok H m B
      /\ hs_RHEAP H s' LBc m
      /\ Permutation LBc (PB ++ (FBB ++ fz_NEW2 N W) ++ LB)
      /\ (forall b, In b PB -> powned em h es b) /\ (forall b, In b ((FBB ++ fz_NEW2 N W) ++ LB) -> ~ powned em h es b)
      (* [comment removed for export] *)
      /\ rw_cells usegs m P (ParserCoreCells c pad7 pad2)
      /\ rw_cells usegs m (P + 288) [C8 (wz 0)] /\ rw_cells usegs m (P + 336) [C8 (wz 0)]
      /\ FieldsC m (P + 80) S L ns ls em /\ FieldsOwn LBc em
      /\ rw_cells usegs m (P + 128) (HdrCells h) /\ HdrOwn LBc h /\ HdrDisj em h
      /\ MBraw m (P + 168) es out insz outpos outend /\ MBufOwn LBc es /\ BodyDisj em h es
      /\ rw_cells usegs m (P + 232) [c232] /\ csize c232 = 8%nat
      /\ rw_cells usegs m (P + 240) c240 /\ cells_size c240 = 16%nat
      /\ rw_cells usegs m (P + 256) c256 /\ cells_size c256 = 32%nat
      /\ rw_cells usegs m (P + 296) c296 /\ cells_size c296 = 8%nat
      /\ rw_cells usegs m (P + 304) c304 /\ cells_size c304 = 32%nat
      /\ rw_cells usegs m (P + 344) c344 /\ cells_size c344 = 8%nat
      /\ rw_cells usegs m (P + 352) c352 /\ cells_size c352 = 8%nat
      (* [comment removed for export] *)
      /\ rw_cells usegs m (P + 392) (IoCtxCells (w_allocb W) (w_regb W) (w_schedb W))
      /\ rw_cells usegs m (P + 360) (BasicStreamCells (w_stb W))
      /\ AllocImpl LBc m (w_allocb W)
      /\ Registry LBc m (w_regb W) (P + 392) (w_v W) 0
      /\ ConfigSvc LBc m (w_cfgb W) (cfg_hdr (P + 392))
      /\ Scheduler LBc m (w_schedb W) (mkSCH (sched_hdr (P + 392) (w_cfgb W)) 0 0 0)
      /\ StreamSvc LBc m (w_v W) (ssvc_hdr (P + 392) (w_schedb W)) (w_q W)
      /\ ImplBlock LBc m (w_q W) (impl_after (w_va W) (w_stb W))
      /\ StateBlock LBc m (w_stb W) (P + 392) (w_q W) (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 Fs code nr nb) dss
      /\ stream_fb_blk N (w_A W) Fs
      (* [comment removed for export] *)
      /\ rw_cells usegs m (P + 416) (FlatBufCells FB) /\ fb_inv FB FBB
      /\ rw_cells usegs m (P + 464) cE /\ cells_size cE = 24%nat
      /\ rw_cells usegs m (P + 488) [C8 s1; C8 s0; C8 ra]
      /\ HStat FT m
      /\ xpres LB (P + 512) XH_X m0 m.

  Lemma fz_FG : forall gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32)
      (P D N lo B : Z) (ra s0 s1 : word) (LB : list block) (m0 : mem) (mo : Model) (cf : config),
    fz_pure H P D N lo B ra LB -> XImg m0 -> tp = Z_to_bv 64 RATP ->
    fzK3p gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P D N lo B ra s0 s1 LB m0 mo cf ->
    hs_SR H (fzK4 H FT gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P lo B ra s0 s1 LB m0 mo) cf.
  Proof.
    intros until cf. intros PU XI TP K3.
    pose proof PU as (AL & CEIL & LO & PB' & BHI & P47 & RAE & NR & DAL & D0 & DNH & INB & DEMP & BUD & BUDC).
    unfold FUZZ_STACK in LO. clear BUD BUDC DEMP DAL D0 DNH. hcb.
    destruct cf as [ms moc]. unfold fzK3p in K3. cbn [cfg_ms cfg_model] in K3.
    destruct K3 as (rax & t0 & t1 & t2 & s0x & s1x & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & s' & errv & W & LBc & PB & FBB
                    & FB & Fs & dss & code & nr & nb & c & pad7 & pad2 & S & L & ns & ls & em & h & es & out & insz & outpos & outend
                    & c232 & c240 & c256 & c296 & c304 & c344 & c352 & cE
                    & -> & KREL & MP & MI & ST & ERR & AUX & HP & PERM & PBO & NPO & CORE & W288 & W336 & FC & FOWN & HDR & HOWN & HDJ
                    & MB & MOWN & BDJ & R232 & Z232 & R240 & Z240 & R256 & Z256 & R296 & Z296 & R304 & Z304 & R344 & Z344 & R352 & Z352
                    & IOC & BS & AI & REG & CFG & SCH & SSVC & IMPL & SB & SFB & FBC & FBI & FRE & SZE & SAV & HS & XP).
    destruct W as [p1 allocb p2 regb p3 cfgb p4 schedb p5 v p6 q p7 stb p8 va p9 A].
    cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A] in *.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = RERRNO) by (unfold RATP, RERRNO; rewrite unsigned_lit; lia).
    subst tp. rewrite EA in ERR.
    assert (AL360 : (P + 360) mod 8 = 0) by (clear - AL; Z.div_mod_to_equations; lia). change (alg 8 (P + 360)) in AL360.
    change (alg 16 P) in AL.
    unfold fz_NEW2 in PERM, NPO. cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A] in PERM, NPO.
    unfold SZ_SPCI_STATE, SZ_SPCI_IMPL, NEWSZ_SSVC, NEWSZ_SCH, NEWSZ_CFG, NEWSZ_REG, SZ_ALLOCIMPL in PERM, NPO.
    set (OURS := [(p8, va, 8); (p7, stb, 312); (p6, q, 96); (p5, v, 79); (p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)]) in *.
    set (AB := if N =? 0 then [] else [(p9, A, N)]) in *.
    (* [comment removed for export] *)
    pose proof (hh_nodup H HH _ _ _ HP) as NDc.
    pose proof (NoDup_ids_perm _ _ PERM NDc) as NDall.
    assert (INr : forall b, In b ((FBB ++ AB ++ OURS) ++ LB) -> In b LBc).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    assert (SUB : forall b, In b LB -> In b LBc) by (intros b Hb; apply INr; apply in_or_app; right; exact Hb).
    assert (INo : forall b, In b OURS -> In b LBc) by (intros b Hb; apply INr; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb).
    pose proof (INo (p8, va, 8) ltac:(subst OURS; cbn; qtauto)) as IN8. pose proof (INo (p7, stb, 312) ltac:(subst OURS; cbn; qtauto)) as IN7.
    pose proof (INo (p6, q, 96) ltac:(subst OURS; cbn; qtauto)) as IN6. pose proof (INo (p5, v, 79) ltac:(subst OURS; cbn; qtauto)) as IN5.
    pose proof (INo (p4, schedb, 287) ltac:(subst OURS; cbn; qtauto)) as IN4. pose proof (INo (p3, cfgb, 71) ltac:(subst OURS; cbn; qtauto)) as IN3.
    pose proof (INo (p2, regb, 79) ltac:(subst OURS; cbn; qtauto)) as IN2. pose proof (INo (p1, allocb, 16) ltac:(subst OURS; cbn; qtauto)) as IN1.
    assert (IN9 : 1 <= N -> In (p9, A, N) LBc).
    { intros K. apply INr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. subst AB. destruct (Z.eqb_spec N 0); [lia| left; reflexivity]. }
    assert (FR : forall b, In b (FBB ++ AB ++ OURS) -> ~ In (blk_id b) (map blk_id LB)).
    { intros b Hb. eapply (mine_fresh _ LB b); [| exact Hb]. pose proof NDall as X. rewrite map_app in X. exact (List.NoDup_app_remove_l _ _ X). }
    pose proof (hh_blocks H HH _ _ _ _ HP IN7) as (T1 & T2 & _ & T4 & T5). cbn in T1, T2, T4, T5. change (alg 16 stb) in T2.
    pose proof (hh_blocks H HH _ _ _ _ HP IN6) as (Q1 & _ & _ & Q4 & Q5). cbn in Q1, Q4, Q5.
    pose proof (hh_blocks H HH _ _ _ _ HP IN8) as (E1 & _ & _ & E4 & E5). cbn in E1, E4, E5.
    (* [comment removed for export] *)
    pose proof (FieldsC_stk _ _ _ _ _ _ _ FC) as STF. replace (P + 80 + 48) with (P + 128) in STF by lia.
    pose proof (MBraw_stk _ _ _ _ _ _ _ MB) as STM. replace (P + 168 + 64) with (P + 232) in STM by lia.
    (* [comment removed for export] *)
    eapply (hh_evt_then H HH); [exact KREL| eapply fzF; [lia| lia| exact MI]|]. intros ms1 (-> & _ & _ & _).
    pose proof (parser_dtor_spec H HH) as PD. unfold parser_dtor_stmt in PD.
    eapply (hh_seq H HH).
    { eapply PD with (P := P) (lo := lo) (B := B) (LB := LBc) (s := s') (c := c) (S := S) (L := L) (ns := ns) (ls := ls) (em := em) (h := h) (es := es);
        unfold wz; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI | exact ST | exact KREL | rewrite EA; exact ERR | exact HP | exact AUX | fast_assumption
                     | unfold PARSER_DTOR_STACK, BFIELDS_DTOR_STACK, RFREE_STACK; lia ].
      - exact CORE. - exact MB. }
    intros [ms2 mo2] PO. unfold parser_dtor_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m2 & s2' & LB2
                    & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & MEM2 & _ & _ & CORE2 & HDR2 & W288' & W336' & XPC).
    unfold wz in XPC, ST2. rewrite (unsigned_lit P) in ST2, XPC by lia. rewrite EA in ERR2.
    apply (hh_mpres_trans H HH _ _ _ MP) in MP2. clear MP PD.
    (* [comment removed for export] *)
    assert (PERM2 : Permutation LB2 ((FBB ++ AB ++ OURS) ++ LB)).
    { apply Permutation.NoDup_Permutation.
      - apply NoDup_of_ids. exact (hh_nodup H HH _ _ _ HP2).
      - apply NoDup_of_ids. pose proof NDall as X. rewrite map_app in X. exact (List.NoDup_app_remove_l _ _ X).
      - intros b. rewrite MEM2. split.
        + intros [Hb NPb]. pose proof (Permutation_in _ PERM Hb) as K. apply in_app_iff in K. destruct K as [K|K]; [| exact K].
          exfalso. exact (NPb (PBO _ K)).
        + intros Hb. split; [exact (INr _ Hb)| exact (NPO _ Hb)]. }
    pose proof (hh_nodup H HH _ _ _ HP2) as ND2.
    assert (INr2 : forall b, In b ((FBB ++ AB ++ OURS) ++ LB) -> In b LB2).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM2| exact Hb]. }
    assert (SUB2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply INr2; apply in_or_app; right; exact Hb).
    assert (INo2 : forall b, In b OURS -> In b LB2) by (intros b Hb; apply INr2; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb).
    pose proof (INo2 (p8, va, 8) ltac:(subst OURS; cbn; qtauto)) as IN8'. pose proof (INo2 (p7, stb, 312) ltac:(subst OURS; cbn; qtauto)) as IN7'.
    pose proof (INo2 (p6, q, 96) ltac:(subst OURS; cbn; qtauto)) as IN6'. pose proof (INo2 (p5, v, 79) ltac:(subst OURS; cbn; qtauto)) as IN5'.
    pose proof (INo2 (p4, schedb, 287) ltac:(subst OURS; cbn; qtauto)) as IN4'. pose proof (INo2 (p3, cfgb, 71) ltac:(subst OURS; cbn; qtauto)) as IN3'.
    pose proof (INo2 (p2, regb, 79) ltac:(subst OURS; cbn; qtauto)) as IN2'. pose proof (INo2 (p1, allocb, 16) ltac:(subst OURS; cbn; qtauto)) as IN1'.
    assert (IN9' : 1 <= N -> In (p9, A, N) LB2).
    { intros K. apply INr2. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. subst AB. destruct (Z.eqb_spec N 0); [lia| left; reflexivity]. }
    (* [comment removed for export] *)
    xp_frame XPC P.
    eapply (xpres_stk _ _ _ m m2) in STF; [| exact XPC| lia| unfold parser_dtor_X; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    eapply (xpres_stk _ _ _ m m2) in STM; [| exact XPC| lia| unfold parser_dtor_X; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
    assert (XF : forall a n, a + n <= hceil -> Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) (parser_dtor_X P)).
    { intros a n K. unfold parser_dtor_X. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    eapply (AllocImpl_reix H HH _ _ LB2) in AI; [| exact HP| exact IN1| exact IN1'].
    eapply (AllocImpl_xpres _ _ _ m m2) in AI; [| exact XPC| apply XF; pose proof (hh_blocks H HH _ _ _ _ HP IN1) as (_ & _ & _ & K & _); exact K].
    eapply (Registry_reix H HH _ _ LB2) in REG; [| exact HP| exact IN2| exact IN2'].
    eapply (Registry_xpres _ _ _ m m2) in REG; [| exact XPC| apply XF; pose proof (hh_blocks H HH _ _ _ _ HP IN2) as (_ & _ & _ & K & _); exact K].
    eapply (ConfigSvc_reix H HH _ _ LB2) in CFG; [| exact HP| exact IN3| exact IN3'].
    eapply (ConfigSvc_xpres _ _ _ m m2) in CFG; [| exact XPC| apply XF; pose proof (hh_blocks H HH _ _ _ _ HP IN3) as (_ & _ & _ & K & _); exact K].
    eapply (Scheduler_reix H HH _ _ LB2) in SCH; [| exact HP| exact IN4| exact IN4'].
    eapply (Scheduler_xpres _ _ _ m m2) in SCH; [| exact XPC| apply XF; pose proof (hh_blocks H HH _ _ _ _ HP IN4) as (_ & _ & _ & K & _); exact K].
    eapply (StreamSvc_reix H HH _ _ LB2) in SSVC; [| exact HP| exact IN5| exact IN5'].
    eapply (StreamSvc_xpres _ _ _ m m2) in SSVC; [| exact XPC| apply XF; pose proof (hh_blocks H HH _ _ _ _ HP IN5) as (_ & _ & _ & K & _); exact K].
    eapply (ImplBlock_reix H HH _ _ LB2 m _ p6 p8) in IMPL; [| exact HP| exact IN6| exact IN6'| cbn [im_vcap im_vb impl_after]; intros _; split; [exact IN8| exact IN8']].
    eapply (ImplBlock_xpres _ _ _ m m2) in IMPL; [| exact XPC| apply XF; unfold SZ_SPCI_IMPL; lia| cbn [im_vcap im_vb impl_after]; intros _; apply XF; lia].
    assert (SIN : Fs <> FB_empty -> In (p9, fb_begin Fs, fb_cap Fs) LBc /\ In (p9, fb_begin Fs, fb_cap Fs) LB2).
    { intros NE. destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [exact (False_ind _ (NE E0))|].
      unfold fb_cap. rewrite FB0, FE0. replace (A + N - A) with N by lia. split; [exact (IN9 N1)| exact (IN9' N1)]. }
    eapply (StateBlock_reix H HH _ _ LB2 m _ p7 p9) in SB; [| exact HP| exact IN7| exact IN7'| cbn [st_fb]; exact SIN].
    eapply (StateBlock_xpres _ _ _ m m2) in SB; [| exact XPC| apply XF; unfold SZ_SPCI_STATE; lia|].
    2:{ cbn [st_fb]. intros NE. destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [exact (False_ind _ (NE E0))|]. rewrite FB0, FE0. apply (XF A N).
        pose proof (hh_blocks H HH _ _ _ _ HP (IN9 N1)) as (_ & _ & _ & K & _). exact K. }
    assert (XP2 : xpres LB (P + 512) XH_X m0 m2).
    { eapply (xp_lift_gen H HH s2' LB2 LB m2); [exact XP| exact XPC| lia| lia| exact HP2| exact SUB2|].
      unfold parser_dtor_X. intros a [R|[R|[R|[]]]]; cbn in R; left; left; lia. }
    assert (HS2 : HStat FT m2).
    { eapply (HStat_xpres_keep FT _ P _); [exact FT_local| exact HS| exact XPC|].
      unfold parser_dtor_X. intros a Ha [R|[R|[R|[]]]]; cbn in R; unfold XH_LO, XH_HI in Ha; lia. }
    clear MI ST ERR AUX HS XP XPC FC FOWN HDR HOWN HDJ MB MOWN BDJ CORE W288 W336 MEM2 PBO NPO INr INo IN9 XF.
    assert (OFF : forall b b', In b LB2 -> In b' LB2 -> b <> b' -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb' NE. exact (blocks_neq_disjoint H HH _ _ _ _ _ HP2 Hb Hb' NE). }
    assert (NI9 : 1 <= N -> ~ In p9 [p8; p7; p6; p5; p4; p3; p2; p1]).
    { intros N1. pose proof NDall as X. rewrite map_app in X. apply List.NoDup_app_remove_l in X. rewrite map_app in X. apply List.NoDup_app_remove_r in X.
      rewrite map_app in X. apply List.NoDup_app_remove_l in X. subst AB OURS. destruct (Z.eqb_spec N 0); [lia|]. cbn in X.
      inversion X; subst. fast_assumption. }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_PDT)) with (Z_to_bv 64 P_FZ_RET_PDT)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_PDT; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL2| eapply fzG; [lia| lia| exact MI2]|]. intros ms3 (-> & _ & _ & _).
    pose proof (stream_dtor_spec H HH) as SD. unfold stream_dtor_stmt in SD.
    eapply (hh_seq H HH).
    { eapply SD with (bs := P + 360) (stb := stb) (ioc := P + 392) (implb := q) (vb := va) (i := 1) (vcap := 1) (lo := lo) (B := B)
                     (LB := LB2) (s := s2') (S := mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 Fs code nr nb) (ds := dss);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI2 | exact ST2 | exact KREL2 | rewrite EA; exact ERR2 | exact HP2 | exact AUX2 | exact BS | exact SB | exact IMPL | exact AL
                     | unfold STREAM_DTOR_STACK, SHCOUNT_DTOR_STATE_STACK, STATE_DTOR_STACK, RFREE_STACK; lia
                     | unfold SZ_BS; lia | unfold P_FZ_RET_SDT; cbn; lia ].
      - clear - AL. unfold alg in AL. Z.div_mod_to_equations. lia.
      - pose proof (OFF _ _ IN7' IN6' ltac:(congruence)) as Xo. unfold SZ_SPCI_STATE, SZ_SPCI_IMPL. cbn in Xo. lia.
      - pose proof (OFF _ _ IN7' IN8' ltac:(congruence)) as Xo. unfold SZ_SPCI_STATE. cbn in Xo. lia.
      - pose proof (OFF _ _ IN8' IN6' ltac:(congruence)) as Xo. unfold SZ_SPCI_IMPL. cbn in Xo. lia.
      - cbn [st_fb]. intros NE. destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [exact (False_ind _ (NE E0))|].
        unfold fb_off. rewrite FB0, FE0. unfold SZ_SPCI_STATE, SZ_SPCI_IMPL.
        pose proof (NI9 N1) as NI.
        pose proof (OFF _ _ (IN9' N1) IN7' ltac:(intros E; injection E; intros; apply NI; subst; cbn; qtauto)) as Xo1.
        pose proof (OFF _ _ (IN9' N1) IN6' ltac:(intros E; injection E; intros; apply NI; subst; cbn; qtauto)) as Xo2.
        pose proof (OFF _ _ (IN9' N1) IN8' ltac:(intros E; injection E; intros; apply NI; subst; cbn; qtauto)) as Xo3. cbn in Xo1, Xo2, Xo3. lia.
      - eapply XStatics_xpres0; [exact XI| exact XP2]. }
    intros [ms4 mo4] PO. unfold stream_dtor_post in PO. cbn [cfg_ms cfg_model st_fb st_hdr] in PO.
    destruct PO as (y0 & y1 & y2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & s4' & pf & px
                    & -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & INX & INF & HP4 & BS4 & IMPL4 & XS4 & XPC).
    rewrite (unsigned_lit P) in ST4, XPC by lia. rewrite EA in ERR4.
    apply (hh_mpres_trans H HH _ _ _ MP2) in MP4. clear MP2 SD.
    unfold SZ_SPCI_STATE in INX. rewrite (in_pin H HH _ _ _ _ _ _ _ HP2 IN7' ltac:(lia) INX) in HP4, IMPL4. clear INX px.
    (* [comment removed for export] *)
    set (L4 := hs_lb_remove H p7 (sd_LB H Fs pf LB2)) in *.
    assert (PN4 : Permutation L4 ([(p8, va, 8); (p6, q, 96); (p5, v, 79); (p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)] ++ FBB ++ LB)
                  /\ List.NoDup (map blk_id L4)).
    { subst L4. unfold sd_LB.
      assert (PE0 : Permutation LB2 (AB ++ (p7, stb, 312) :: ([(p8, va, 8); (p6, q, 96); (p5, v, 79); (p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)] ++ FBB ++ LB))).
      { eapply Permutation_trans; [exact PERM2|]. rewrite <- !app_assoc.
        eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head.
        eapply Permutation_trans; [apply Permutation_app_swap_app|]. subst OURS. cbn [app]. apply perm_swap. }
      destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)].
      - subst Fs AB. rewrite (proj2 (Z.eqb_eq N 0) N0) in PE0. cbn [fb_begin FB_empty Z.eqb app] in PE0 |- *.
        destruct (bperm_free H HH _ _ _ ND2 PE0) as [PE1 ND1]. cbn [blk_id fst snd] in PE1, ND1. split; [exact PE1| exact ND1].
      - subst AB. destruct (Z.eqb_spec N 0); [lia|]. rewrite FB0. unfold fb_cap in INF. rewrite FB0, FE0 in INF.
        pose proof (hh_blocks H HH _ _ _ _ HP2 (IN9' N1)) as (A1 & _). cbn in A1. destruct (Z.eqb_spec A 0); [lia|].
        assert (EFs : Fs = mkFB A (fb_in Fs) (fb_out Fs) (fb_last Fs) (A + N)) by (destruct Fs; cbn in FB0, FE0; subst; reflexivity).
        assert (NE : Fs <> FB_empty) by (rewrite EFs; unfold FB_empty; intros E; injection E; lia).
        specialize (INF NE). replace (A + N - A) with N in INF by lia.
        rewrite (in_pin H HH _ _ _ _ _ _ _ HP2 (IN9' N1) ltac:(lia) INF).
        cbn [app] in PE0. destruct (bperm_free H HH _ _ _ ND2 PE0) as [PE1 ND1]. cbn [blk_id fst snd] in PE1, ND1.
        destruct (bperm_free H HH _ _ _ ND1 PE1) as [PE2 ND2']. cbn [blk_id fst snd] in PE2, ND2'. split; [exact PE2| exact ND2']. }
    destruct PN4 as [PERM4 ND4].
    assert (INr4 : forall b, In b ([(p8, va, 8); (p6, q, 96); (p5, v, 79); (p4, schedb, 287); (p3, cfgb, 71); (p2, regb, 79); (p1, allocb, 16)] ++ FBB ++ LB) -> In b L4).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM4| exact Hb]. }
    (* [comment removed for export] *)
    assert (A4N : 1 <= N -> 0 < A /\ A + N <= hceil /\ (A + N <= 0x10000 \/ 0xb8000 <= A)).
    { intros N1. pose proof (hh_blocks H HH _ _ _ _ HP2 (IN9' N1)) as (K1 & _ & _ & K4 & K5). cbn in K1, K4, K5. lia. }
    assert (XCF : forall a n, hceil <= a -> (a + n <= P + 376 \/ P + 392 <= a) ->
                  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) (bsd_X (P + 360) stb q va 1 Fs)).
    { intros a n K1 K2. unfold bsd_X. repeat (apply Forall_cons; [cbn; lia|]).
      destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [subst Fs; cbn; apply Forall_nil|].
      rewrite FB0, FE0. pose proof (A4N N1). destruct (Z.eqb_spec A 0); [lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (XCH : forall pb b sz, In (pb, b, sz) LB2 -> pb <> p7 -> pb <> p6 -> pb <> p8 -> (1 <= N -> pb <> p9) ->
                  Forall (fun iv : Z * Z => b + sz <= fst iv \/ snd iv <= b) (bsd_X (P + 360) stb q va 1 Fs)).
    { intros pb b sz Hb N7 N6 N8 N9. pose proof (hh_blocks H HH _ _ _ _ HP2 Hb) as (_ & _ & _ & K4 & _). cbn in K4. unfold bsd_X.
      apply Forall_cons; [cbn; lia|].
      apply Forall_cons; [pose proof (OFF _ _ Hb IN7' ltac:(congruence)) as Xo; cbn in Xo |- *; lia|].
      apply Forall_cons; [pose proof (OFF _ _ Hb IN6' ltac:(congruence)) as Xo; cbn in Xo |- *; lia|].
      apply Forall_cons; [pose proof (OFF _ _ Hb IN8' ltac:(congruence)) as Xo; cbn in Xo |- *; lia|].
      destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [subst Fs; cbn; apply Forall_nil|].
      rewrite FB0, FE0. pose proof (A4N N1). destruct (Z.eqb_spec A 0); [lia|].
      apply Forall_cons; [| apply Forall_nil]. pose proof (OFF _ _ Hb (IN9' N1) ltac:(specialize (N9 N1); congruence)) as Xo. cbn in Xo |- *. lia. }
    (* [comment removed for export] *)
    assert (NDO : List.NoDup [p8; p7; p6; p5; p4; p3; p2; p1]).
    { pose proof NDall as X. rewrite map_app in X. apply List.NoDup_app_remove_l in X. rewrite map_app in X. apply List.NoDup_app_remove_r in X.
      rewrite map_app in X. apply List.NoDup_app_remove_l in X. rewrite map_app in X. apply List.NoDup_app_remove_l in X. subst OURS. cbn in X. exact X. }
    (* [comment removed for export] *)
    Ltac xpk XPC XCF Hc := eapply (xpres_rw_cells _ _ _ _ _) in Hc; [| exact XPC| split; [left; cbn; lia| apply XCF; cbn; lia]].
    xpk XPC XCF CORE2. xpk XPC XCF HDR2. xpk XPC XCF W288'. xpk XPC XCF W336'.
    pose proof (rw_cells_bound _ _ _ _ R240) as B240. pose proof (rw_cells_bound _ _ _ _ R256) as B256.
    pose proof (rw_cells_bound _ _ _ _ R296) as B296. pose proof (rw_cells_bound _ _ _ _ R304) as B304. pose proof (rw_cells_bound _ _ _ _ R344) as B344.
    pose proof (rw_cells_bound _ _ _ _ R352) as B352.
    pose proof (rw_cells_bound _ _ _ _ FRE) as BE.
    eapply (xpres_rw_cells _ _ _ _ _) in R232; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| cbn [cells_size]; rewrite Z232; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R240; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z240; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R256; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z256; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R296; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z296; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R304; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z304; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R344; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z344; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in R352; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite Z352; lia]]].
    eapply (xpres_rw_cells _ _ _ _ _) in FRE; [| exact XPC| split; [left; cbn; lia| apply XCF; [lia| rewrite SZE; lia]]].
    xpk XPC XCF IOC. xpk XPC XCF FBC. xpk XPC XCF SAV.
    eapply (xpres_stk _ _ _ m2 m4) in STF; [| exact XPC| lia| eapply Forall_impl; [| apply (XCF (P + 80) 48); lia]; intros [x y] K; cbn in K |- *; lia].
    eapply (xpres_stk _ _ _ m2 m4) in STM; [| exact XPC| lia| eapply Forall_impl; [| apply (XCF (P + 168) 64); lia]; intros [x y] K; cbn in K |- *; lia].
    pose proof (nodup8_neq _ _ _ _ _ _ _ _ NDO) as (A17 & A16 & A18 & B27 & B26 & B28 & C37 & C36 & C38 & D47 & D46 & D48 & E57 & E56 & E58).
    assert (N9x : forall px, In px [p8; p7; p6; p5; p4; p3; p2; p1] -> 1 <= N -> px <> p9).
    { intros px Hpx N1 E. apply (NI9 N1). rewrite <- E. exact Hpx. }
    eapply (AllocImpl_xpres _ _ _ m2 m4) in AI; [| exact XPC| apply (XCH _ _ _ IN1'); [exact A17| exact A16| exact A18| apply N9x; do 7 right; left; reflexivity]].
    eapply (AllocImpl_reix H HH _ _ L4) in AI; [| exact HP2| exact IN1'| apply INr4; do 6 right; left; reflexivity].
    eapply (Registry_xpres _ _ _ m2 m4) in REG; [| exact XPC| apply (XCH _ _ _ IN2'); [exact B27| exact B26| exact B28| apply N9x; do 6 right; left; reflexivity]].
    eapply (Registry_reix H HH _ _ L4) in REG; [| exact HP2| exact IN2'| apply INr4; do 5 right; left; reflexivity].
    eapply (ConfigSvc_xpres _ _ _ m2 m4) in CFG; [| exact XPC| apply (XCH _ _ _ IN3'); [exact C37| exact C36| exact C38| apply N9x; do 5 right; left; reflexivity]].
    eapply (ConfigSvc_reix H HH _ _ L4) in CFG; [| exact HP2| exact IN3'| apply INr4; do 4 right; left; reflexivity].
    eapply (Scheduler_xpres _ _ _ m2 m4) in SCH; [| exact XPC| apply (XCH _ _ _ IN4'); [exact D47| exact D46| exact D48| apply N9x; do 4 right; left; reflexivity]].
    eapply (Scheduler_reix H HH _ _ L4) in SCH; [| exact HP2| exact IN4'| apply INr4; do 3 right; left; reflexivity].
    eapply (StreamSvc_xpres _ _ _ m2 m4) in SSVC; [| exact XPC| apply (XCH _ _ _ IN5'); [exact E57| exact E56| exact E58| apply N9x; do 3 right; left; reflexivity]].
    eapply (StreamSvc_reix H HH _ _ L4) in SSVC; [| exact HP2| exact IN5'| apply INr4; do 2 right; left; reflexivity].
    assert (XP4 : xpres LB (P + 512) XH_X m0 m4).
    { eapply (xp_lift_gen H HH s2' LB2 LB m2); [exact XP2| exact XPC| lia| lia| exact HP2| exact SUB2|].
      assert (FR2 : forall b, In b OURS -> ~ In (blk_id b) (map blk_id LB)).
      { intros b Hb. apply FR. apply in_or_app. right. apply in_or_app. right. exact Hb. }
      unfold bsd_X. intros a R.
      cbn [rin_ivs fst snd app] in R.
      destruct R as [R|[R|[R|[R|R]]]].
      - left. left. lia.
      - left. right. exists (p7, stb, 312). split; [exact IN7'|]. split; [apply FR2; subst OURS; right; left; reflexivity| cbn; lia].
      - left. right. exists (p6, q, 96). split; [exact IN6'|]. split; [apply FR2; subst OURS; do 2 right; left; reflexivity| cbn; lia].
      - left. right. exists (p8, va, 8). split; [exact IN8'|]. split; [apply FR2; subst OURS; left; reflexivity| cbn; lia].
      - destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [subst Fs; cbn in R; destruct R|].
        rewrite FB0, FE0 in R. destruct (Z.eqb_spec A 0); cbn in R; [destruct R|]. destruct R as [R|[]].
        left. right. exists (p9, A, N). split; [exact (IN9' N1)|]. split; [| cbn; lia].
        apply FR. apply in_or_app. right. apply in_or_app. left. subst AB. destruct (Z.eqb_spec N 0); [lia| left; reflexivity]. }
    assert (HS4 : HStat FT m4).
    { eapply (HStat_xpres_keep FT _ P _); [exact FT_local| exact HS2| exact XPC|].
      unfold bsd_X. intros a Ha R. cbn [rin_ivs fst snd app] in R. unfold XH_LO, XH_HI in Ha.
      destruct R as [R|[R|[R|[R|R]]]]; [lia| lia| lia| lia|].
      destruct SFB as [[N0 E0]|(N1 & FB0 & FE0)]; [subst Fs; cbn in R; destruct R|].
      rewrite FB0, FE0 in R. pose proof (A4N N1). destruct (Z.eqb_spec A 0); cbn in R; [destruct R|]. destruct R as [R|[]]. lia. }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_SDT)) with (Z_to_bv 64 P_FZ_RET_SDT)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_SDT; lia| reflexivity]).
    apply (hh_done H HH). unfold fzK4. cbn [cfg_ms cfg_model].
    unfold ParserCoreCellsD in CORE2.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in CORE2. destruct CORE2 as [C8H CTL]. cbn [cells_size csize Nat.add] in CTL.
    do 18 eexists. exists m4, s4', errv, (mkFZW p1 allocb p2 regb p3 cfgb p4 schedb p5 v p6 q p7 stb p8 va p9 A), L4, FB, FBB.
    exists (C8 (wz VP_BASIC_PARSER)), (BasicStreamCells stb), cE.
    cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A].
    split; [reflexivity|]. split; [exact KREL4|]. split; [exact MP4|]. split; [exact MI4|]. split; [exact ST4|].
    split; [rewrite EA; exact ERR4|]. split; [exact AUX4|]. split; [exact HP4|].
    split. { unfold fz_ours4. cbn [w_p1 w_allocb w_p2 w_regb w_p3 w_cfgb w_p4 w_schedb w_p5 w_v w_p6 w_q w_p7 w_stb w_p8 w_va w_p9 w_A].
             unfold SZ_SPCI_IMPL, NEWSZ_SSVC, NEWSZ_SCH, NEWSZ_CFG, NEWSZ_REG, SZ_ALLOCIMPL. rewrite <- app_assoc. exact PERM4. }
    split; [exact IOC|]. split; [exact AI|]. split; [exact REG|]. split; [exact CFG|]. split; [exact SCH|]. split; [exact SSVC|].
    split; [unfold impl_after in IMPL4; exact IMPL4|].
    split; [exact C8H|]. split; [reflexivity|].
    split. { (* [comment removed for export] *)
      pose proof (stk_of_rw_cells usegs _ _ _ CTL) as K0. cbn [cells_size csize Nat.add ParserCoreCells length tl] in K0.
      replace (P + Z.of_nat 8) with (P + 8) in K0 by lia. replace (P + 8 + 72) with (P + 80) in K0 by lia.
      eapply stk_merge; [exact K0| | lia]. eapply stk_merge; [exact STF| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ HDR2) as K1. cbn [cells_size csize Nat.add HdrCells length] in K1. replace (P + 128 + 40) with (P + 168) in K1 by lia.
      eapply stk_merge; [exact K1| | lia]. eapply stk_merge; [exact STM| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R232) as K2. cbn [cells_size] in K2. rewrite Z232 in K2. replace (P + 232 + Z.of_nat (8 + 0)) with (P + 240) in K2 by lia.
      eapply stk_merge; [exact K2| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R240) as K3. rewrite Z240 in K3. replace (P + 240 + Z.of_nat 16) with (P + 256) in K3 by lia.
      eapply stk_merge; [exact K3| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R256) as K4. rewrite Z256 in K4. replace (P + 256 + Z.of_nat 32) with (P + 288) in K4 by lia.
      eapply stk_merge; [exact K4| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ W288') as K5. cbn [cells_size csize Nat.add] in K5. replace (P + 288 + 8) with (P + 296) in K5 by lia.
      eapply stk_merge; [exact K5| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R296) as K6. rewrite Z296 in K6. replace (P + 296 + Z.of_nat 8) with (P + 304) in K6 by lia.
      eapply stk_merge; [exact K6| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R304) as K7. rewrite Z304 in K7. replace (P + 304 + Z.of_nat 32) with (P + 336) in K7 by lia.
      eapply stk_merge; [exact K7| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ W336') as K8. cbn [cells_size csize Nat.add] in K8. replace (P + 336 + 8) with (P + 344) in K8 by lia.
      eapply stk_merge; [exact K8| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R344) as K9. rewrite Z344 in K9. replace (P + 344 + Z.of_nat 8) with (P + 352) in K9 by lia.
      eapply stk_merge; [exact K9| | lia].
      pose proof (stk_of_rw_cells usegs _ _ _ R352) as K10. rewrite Z352 in K10. replace (P + 352 + Z.of_nat 8) with (P + 360) in K10 by lia. exact K10. }
    split; [exact BS4|]. split; [reflexivity|]. split; [exact FBC|]. split; [exact FBI|]. split; [exact FRE|]. split; [exact SZE|].
    split; [exact SAV|]. split; [exact HS4| exact XP4].
  Qed.
End W.
End HCW.

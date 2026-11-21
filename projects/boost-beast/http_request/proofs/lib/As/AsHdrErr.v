(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail
  LazyRestrict LazySR LazyFdNodes LazySym Spec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HF_FR : Z := 2400%Z.
Definition STOPSH : list Z := [0x104dfc; 0x0a2ec4]%Z.
Definition FUELH : nat := 8000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition hf_cells : list (Z * nat * Z) :=
  [(0x11d1f0, 8%nat, 0x10592c)   (* [comment removed for export] *);
   (0x129478, 8%nat, 0x7fff8000) (* [comment removed for export] *);
   (0x12a158, 1%nat, 0x1)        (* [comment removed for export] *);
   (0x11fc30, 4%nat, 0x5)        (* [comment removed for export] *);
   (0x11fc50, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x11fc78, 8%nat, 0x104dfc)   (* [comment removed for export] *);
   (0x11fc88, 8%nat, 0x67dbb8)   (* [comment removed for export] *);
   (0x11fc90, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x11fca8, 4%nat, 0x2)        (* [comment removed for export] *);
   (0x11fcb8, 4%nat, 0x0)        (* [comment removed for export] *);
   (0x11fcbc, 4%nat, 0xffffffff) (* [comment removed for export] *);
   (0x7fffc5e8, 8%nat, 0x0); (0x7fffc5f0, 8%nat, 0x0)   (* [comment removed for export] *);
   (0x7ffface8, 8%nat, 0x0); (0x7fffacf0, 8%nat, 0x0)   (* [comment removed for export] *)]%Z.

Definition h_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI;
   KWr (SA (EVar 0) (- HF_FR)) HF_FR;
   KImg 0x10000 0x4d000; KImg 0x115000 0x11d000;
   KWord (SA (ELit 0) 0x67d4f0) 8 (EVar 1);
   KWr (SA (ELit 0) 0x11fc30) 232]%Z
  ++ kn_cells hf_cells.

Definition sc_dummy : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0a2e88 h_sr [] h_kn 34) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x1059b4 (sc_sr hs_sc) [] (sc_kn hs_sc) 66) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary :
  s_pc (fst (fst hs_rA)) = 0x104dfc%Z /\ snd (fst hs_rA) = [] /\ snd (fst hs_cA) = []
  /\ stdio_call 34 hs_srA hs_knA = Some hs_sc
  /\ (sc_ret hs_sc, sc_f hs_sc, sc_fd hs_sc, sc_s hs_sc, sc_l hs_sc) = (0x1059b4%Z, 0x11fc30%Z, 2%Z, ELit 0x22f72%Z, ELit 31%Z)
  /\ s_pc (fst (fst hs_rC)) = 0x0a2ec4%Z /\ snd (fst hs_rC) = [] /\ snd (fst hs_cC) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_res); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_rA); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_cA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_srA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_knA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_fd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_rC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hs_cC)|] Array.empty "#0q###Y#?#=#(#T#K#,#2#/#:#D#E#3#L#I#1#6#7#8#B#C#4#M#O#P#Q#R#S#U#V#W#X#Y#Z#[#*#+#<#>#)#A#@#9#5#;#'#-#G#&#F#J#H#N#.#07#E$#F$#G&#H$#I$#J%#K&#L$#M$#N$#O&#P%#Q'#R'#S%#T&#U%#V&#W$#X$#H########$#####$#$#$#$#$###############'##H########$#####$#$###$#$#$#$#$#$#$#####'#$H####$#$#$#$#$###$#$###$#$#$###$#$#$#######'#$s#,##$#$#$#$###$#$#$#####$###'#$s#7$#####$#$###$#$###$#####'#$?$#$#$#$#$#########$#$#########'#$+##$#########'#$(######'#$/##$#######'##5########'#$B######'#$s#+##$#$#$#######'##s#m$#######$#####$#$###########'#$s$8######$###$#$#$###$#$#######$#####'##s$G####################'#$s$V$###$#########################'##s$:$#########################'##s$-$#########################'##s$h$#####$#$#$#$#########'#$:$#$#$#$#########'##s$^##$###$#$#####'##s#Q$#####$###$#######$#$#$#$#######'#$2########$###$###$#$#######'#$s$`$#######'##s$S##$#######'#$)########'##s$_$#######'#$s$c####'#$s%s$#$#$#$#$#$#$#$#$#$#$#$#$#$#######$###$#$#$#$###$#######'#$)########'##9$###$#$#####$#$#$###$#######'#$)########'#-Es&Rs&R5J6J-$##UQI$s&~$#$#$#$#$#$###$#$#$###$#########'#'s'6$s'1$###$#$#####$#$#$#######'#$H####$###$#$#$###$#$#$###$#$#$#$#$#$#######'#+s&x+R#s#<$#$#$#$###$#$#$#####$###'#+s&y$s#*$#$#'#+#*K#7$#########,#+#WS#S$+#&K&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#*#+s'B*B*B&'&#&#&#&#*#&$*#&$*#'H+#&&&#&#&#*#&$*#&$*#&$*#&$*#&$*#&$*#+s'Q*s#/*s#/*s#/*s#/*s#/*s#/&+&#&#&#&#&#&#&#&#&#&#*#&$*#&$*#&$*#6D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#8#%Ds#9#%Ds#(#%Ds#w#%Ds#+#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds$##%Ds$$#%Ds#E#%Ds#H#%Ds#K#%Ds#N#%Ds#U#%Ds#W#%Ds#}#%Ds#Z#%Ds#\#$s$q$#########'#(s$Is(.)#s$$s$K$*######'#(s$Ps(0)#s$+s$R$s%)##########$#######'#(s$]s(6)#s$8s$_#?########'#(s$es(8)#s$@s$f$s%8######'#(s$ls(:)#s$Gs$m$<##$#$#######'#(s$vs(;$s$e$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#'#+#)s#@s%6##s%C$#######,#(s%J#)#s%:s$l#*######,#(s%Q#)#s%As$s$s*d$#$#$#######,#(s%[#)#s%Ks$k#*######,#(s%b#)#s%Rs%i#2$#######,#(s%j#)#s%Zs%l#*######,#(s%q#)#s%as%r#B$#$#######,#(s%z##s&J$#######$#$#$#$###$#$#######'#+s)U)4s%{##s&6####,#(s&5#*s%r)$s&&##;,#(s&:#*s%x)$s&+#$s+Q######,#(s&B#*s&%)$s&3#,s+U(s&F#*s&*)$s&7#,s#,(s&J#*s&7)$s&;#,s+^(s&N#*s&<)$s&?#,s+c(s&R#$5$#############$#$#$#$#####'#+s)u)3s&R#'s+uVS%s&e##s$Y$#$#$#$#$#$#$#################################################'#'s$ZWS&s',$#$s,@##$#$###########,#(s'7#'%VL$##s,J####################'#$;##$#########################'#VMs*]s*L#s'j$#########################'##s(V$#########################'#VMs*\s*M#s(>$#$#$#####$#$#########'#(s(<s*N*s'z)$s't#(s(?s,,$s$X######'#VL(#$s#&$#$#####$#########'#(s(Qs*Y#s(u$###$#$#########'#+s*[).s(7##s#x##$###$#$#######$#$#$#######'#(s(ns*[#s&L############################'#+#)4s(Z#$s#%######$#$#######$#$#######'#(s)4s*n)#s(rs(A's%B+#)s#Ws(r#$s'A$#######'#(s)?s*s+s-r)$s(w#$s'K##$#######'#(s)Is*v)#s)$s)K$+########'#(s)Qs*x)#s),s)R#s'B$#######'#(s)Ys*z+s*%)$s)9#$s'I####'#(s)`s*}'s'.+#)%s)A##s'@####$###$#$#$#$###$#######'#(s)ss*r)#s)Ns)t$+########'#(s){s*t)#s)Vs)|$s#l##$#$#####$#$#$###$#######'#(s*0s*u)#s)gs*1$+########'#(s*8s*w)#s)os*96C%C$#%C-#%C?#%Cs#(#%Cs#:#%Cs#C#%Cs#M#%Cs#V#%Cs#`#%Cs#j#%Cs#n#%Cs$$#%Cs$H#%Cs$a#%Cs$i#%Cs$z#%Cs%>#%Cs%\#%Cs%j#%Cs&2#%Cs&5#%Cs&I#%Cs&N#%Cs&S#%Cs&X#%Cs&a#%Cs&g#%Cs&o#%Cs'.#%Cs'6#%Cs'?#%Cs'G#%Cs'R#%Cs'Z#%Cs'c#%Cs(O#%Cs(W#%Cs(`#%Cs(n#%Cs(v#`S's.Ps+.s.as*ds*ds*ds*cs*Ts*Os*Es)$#VNI#-s+C##1EE1#E1#D1#D/EEs.hs.W/'E#s+6/'D#s*]/'D#s*Y-'##-Es-ms-m.s+Os+O.$#.&#.0#.s+S#.s+T#3Es/L3s+Xs+W3s+V632.3Es-x0s+Zs+Z&&0/.$#01.&#0;.(#0s+^.*#0s+_.+#0s+c.-#1Gs+c2#OS(2Gs+e#UP#-E#s/\4Gs+h&-s+i#s+h5C1#s+k5S)2$#S*4&s+n#-s+o#s+nWS+s*OS,S-VNIF-s+o$#US.FUS/F/EE$#US0F/s#2E$#US1F/s#3D$#US2F/s#4D$#-s#4#s#02<OS32Gs+~#UP#-E#s.A4Gs,%&-s,&#s,%2:9S44<s,(#-s,)#s,(.&#.)#..#.9#.=#.s#$#.s#'#m$s#-##"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0a2ea4 h_sr [] h_kn 34) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x1059b4 (sc_sr ho_sc) [] (sc_kn ho_sc) 66) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary :
  s_pc (fst (fst ho_rA)) = 0x104dfc%Z /\ snd (fst ho_rA) = [] /\ snd (fst ho_cA) = []
  /\ stdio_call 34 ho_srA ho_knA = Some ho_sc
  /\ (sc_ret ho_sc, sc_f ho_sc, sc_fd ho_sc, sc_s ho_sc, sc_l ho_sc) = (0x1059b4%Z, 0x11fc30%Z, 2%Z, ELit 0x1678d%Z, ELit 31%Z)
  /\ s_pc (fst (fst ho_rC)) = 0x0a2ec4%Z /\ snd (fst ho_rC) = [] /\ snd (fst ho_cC) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_res); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_rA); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_cA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_srA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_knA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_fd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.sc_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_rC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.ho_cC)|] Array.empty "#0w###Y#?#=#(#T#K#,#2#/#:#D#E#3#L#I#1#6#7#8#B#C#4#M#O#P#Q#R#S#U#V#W#X#Y#Z#[#*#+#<#>#)#A#@#9#5#;#'#-#G#&#F#J#H#N#.#07#E$#F$#G&#H$#I$#J%#K&#L$#M$#N$#O&#P%#Q'#R'#S%#T&#U%#V&#W$#X$#H########$#####$#$#$#$#$###############'##H########$#####$#$###$#$#$#$#$#$#$#####'#$H####$#$#$#$#$###$#$###$#$#$###$#$#$#######'#$s#.$#####$#$#$#$#######$#$###$#'#$s#8$#####$#$###$#$###$#####'#$s#J$#$#$#$#$#$#########$#$#########'#$+##$#########'#$(######'#$/##$#######'##5########'#$B######'#$s#+##$#$#$#######'##s#o$#######$#####$#$###########'##s#j####$###$#$#$###$#$#######$#####'##s$H####################'#$s$W$###$#########################'##s#{$###$#########################'##s$.$#########################'##s$k$#####$#$#$#$#########'#$:$#$#$#$#########'##s$`##$###$#$#####'##s#S$#####$###$#######$#$#$#$#######'#$2########$###$###$#$#######'#$s$a$#######'##s$T##$#######'#$)########'##s$`$#######'#$s$d####'#$s%v$#$#$#$#$#$#$#$#$#$#$#$#$#$#######$###$#$#$#$###$#######'#$)########'##9$###$#$#####$#$#$###$#######'#$)########'#-Es&Us&U5J6J-$##UQI$s'%$#$#$#$#$#$###$#$#$###$#########'#'s'9$s'4$###$#$#####$#$#$#######'#$H####$###$#$#$###$#$#$###$#$#$#$#$#$#######'#+s&{+R$s'a$#####$#$#$#$#######$#$###$#'#+s&}$s#,$#$#'#+#*K#s#S##$#########,#+#WS#S$,#&K&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#*#+s'G*B*B&'&#&#&#&#*#&$*#&$*#'H+#&&&#&#&#*#&$*#&$*#&$*#&$*#&$*#&$*#+s'U*s#/*s#/*s#/*s#/*s#/*s#/&+&#&#&#&#&#&#&#&#&#&#*#&$*#&$*#&$*#6D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#8#%Ds#9#%Ds#(#%Ds#x#%Ds#+#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds$$#%Ds$%#%Ds#E#%Ds#H#%Ds#K#%Ds#N#%Ds#U#%Ds#W#%Ds#}#%Ds#Z#%Ds#\#$s$t$#########'#(s$Ls(2)#s$$s$N$*######'#(s$Ss(4)#s$+s$U$s%,##########$#######'#(s$`s(:)#s$8s$b#?########'#(s$hs(<)#s$@s$i$s%;######'#(s$os(>)#s$Gs$p$<##$#$#######'#(s$ys(?$s$f$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#'#+#)s#@s%6##s%C$#######,#(s%K#)#s%:s$l#*######,#(s%R#)#s%As$s$s*j$#$#$#######,#(s%\#)#s%Ks$k#*######,#(s%c#)#s%Rs%j#2$#######,#(s%k#)#s%Zs%m#*######,#(s%r#)#s%as%s#B$#$#######,#(s%{##s&M$#######$#$#$#$###$#$#######'#+s)Y)4s%{##s&7####,#(s&6#*s%r)$s&&##;,#(s&;#*s%x)$s&+##s&T####,#(s&B#*s&$)$s&2#,s+Z(s&F#*s&))$s&6#,s#+(s&J#*s&6)$s&:#,s+c(s&N#*s&;)$s&>#,s+h(s&R#$5$#############$#$#$#$#####'#+s)y)3s&Q#'s+zVS%s&e##s$X$#$#$#$#$#$#$#################################################'#'s$YWS&s',$#$s,E##$#$###########,#(s'7#'%VL$##s,O####################'#$;##$#########################'#VMs*as*P$s'V##$#########################'##s(Y$#########################'#VMs*_s*P#s(A$#$#$#####$#$#########'#(s(?s*Q*s'z)$s't#(s(Bs,0$s$X######'#VL(#$s#&$#$#####$#########'#(s(Ts*\#s(x$###$#$#########'#+s*^).s(7##s#y##$###$#$#######$#$#$#######'#(s(qs*^#s&L############################'#+#)4s(Z#$s#%######$#$#######$#$#######'#(s)7s*q)#s(rs(A's)8+#)s#Ws(r#$s'A$#######'#(s)Bs*v+s-x)$s(w#$s'K##$#######'#(s)Ls*y)#s)$s)N$+########'#(s)Ts*{)#s),s)U#s'B$#######'#(s)\s*}+s*()$s)9#$s'I####'#(s)cs+$'s'.+#)%s)A##s'@####$###$#$#$#$###$#######'#(s)vs*u)#s)Ns)w$+########'#(s)~s*w)#s)Vs*#$s#l##$#$#####$#$#$###$#######'#(s*3s*x)#s)gs*4$+########'#(s*;s*z)#s)os*<6C%C$#%C-#%C?#%Cs#(#%Cs#:#%Cs#C#%Cs#M#%Cs#V#%Cs#`#%Cs#j#%Cs#n#%Cs$$#%Cs$H#%Cs$a#%Cs$i#%Cs$z#%Cs%?#%Cs%]#%Cs%k#%Cs&3#%Cs&6#%Cs&J#%Cs&O#%Cs&T#%Cs&Y#%Cs&a#%Cs&g#%Cs&o#%Cs'.#%Cs'6#%Cs'?#%Cs'G#%Cs'R#%Cs'Z#%Cs'c#%Cs(O#%Cs(W#%Cs(`#%Cs(n#%Cs(v#`S's.Ts+1s.fs*gs*gs*gs*fs*Us*Ps*Es)$#VNI#-s+F##1EE1#E1#D1#D/EEs.ms.[/'E#s+9/'D#s*^/'D#s*Z-'##-Es-rs-r.s+Rs+R.$#.&#.0#.s+V#.s+W#3Es/R3s+[s+Z3s+Y632.3Es-}0s+]s+]&&0/.$#01.&#0;.(#0s+a.*#0s+b.+#0s+f.-#1Gs+f2#OS(2Gs+h#UP#-E#s/b4Gs+k&-s+l#s+k5C1#s+n5S)2$#S*4&s+q#-s+r#s+qWS+s*OS,S-VNIF-s+r$#US.FUS/F/EE$#US0F/s#2E$#US1F/s#3D$#US2F/s#4D$#-s#4#s#02<OS32Gs,%#UP#-E#s.F4Gs,(&-s,)#s,(2:9S44<s,+#-s,,#s,+.&#.)#..#.9#.=#.s#$#.s#'#m$s#-##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x22f72) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1678d) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_len : length msg_short = 31%nat. Proof. reflexivity. Qed.
Lemma msg_overrun_len : length msg_overrun = 31%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : list sregion :=
  [(SA (EVar 0) (- HF_FR), HF_FR); (SA (ELit 0) 0x11fc30, 232)]%Z.

Lemma hs_covA : log_covered h_regions (s_log (fst (fst hs_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hs_covC : log_covered h_regions (s_log (fst (fst hs_rC))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covA : log_covered h_regions (s_log (fst (fst ho_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covC : log_covered h_regions (s_log (fst (fst ho_rC))) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition h_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - HF_FR), HF_FR); (Z_to_bv 64 0x11fc30, 232%Z)].

  Lemma h_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) h_regions = h_regions_w.
  Proof.
    intros vals P0 Hlo. unfold ASP_LO in Hlo. unfold h_regions, h_regions_w, rdenot, estart, HF_FR.
    cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma h_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z ->
    regions_flat (ENV vals) h_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold h_regions, HF_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    (* LPS 75d69e00: + Hrd2, the channel-reader premise, immediately after Hfd2. *)
    intros vals R M msF mo K HL P0 HR HK Hfd2 Hrd2 OK RS HKnil HCONT;
    pose proof (know_nth RSEGS _ _ h_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg;
    unfold ASP_LO, ASP_HI in Hrg;
    pose proof (h_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF;
    pose proof (h_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD;
    pose proof ITIN as (PCA & SCA & CCA & SC & _ & PCC & SCC & CCC);
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 pcA h_sr h_kn 34 (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA)
      | exact HR | exact HK | rewrite SCA; constructor | rewrite CCA; constructor | exact OK | exact RS | ];
    clear HR HK; intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA;
    pose proof (log_covered_frame (ENV vals) M h_regions _ COVA RF LFA) as FA; rewrite <- EQA, RD in FA;
    change (s_regs (fst (fst rA))) with srA in HR; change (fst (fst cA)) with knA in HK;
    rewrite PCA in RSA;
    (* [comment removed for export] *)
    apply (stdio_call_sound_post vals (blobs_ev []) srA knA RA MA L S Zr msFA moA sc [] msg K
             HR HK (eq_trans (f_equal (fun n => stdio_call n srA knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn sc edenot ev ENV app];
      rewrite ?MSG_LEN; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    [ unorm; lia
    | unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | (* [comment removed for export] *)
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 31 = _ =>
        rewrite (kimg_rdn RSEGS (ENV vals) _ knA ltac:(let i := kidx knA (is_kimg_cov a 31) in exact i)
                   _ _ a 31 HK eq_refl) by (cbn; lia) end;
      apply MSG_IMG
    | rewrite (same_but_materialized_fds _ _ SBA); exact Hfd2
    (* LPS 75d69e00: the reader fact, transported the same way the fds fact is. *)
    | rewrite (same_but_materialized_reader _ _ SBA); exact Hrd2
    | exact OKA
    | exact RSA
    | exact HKnil
    | (* [comment removed for export] *)
      clear HR HK; intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC;
      assert (FC0 : frame_mod MA MC h_regions_w);
      [ eapply sw_post_frame_mod; [exact HPOST|]; intros x Hx; unfold h_regions_w, HF_FR in Hx; cbn [outside] in Hx;
        unfold in_rng in Hx; rewrite P0, alu_add, vadd_wZ; revert Hx; unorm; intros (N1 & N2 & _); lia |];
      set (vals' := vals ++ junk_vals Rj) in *;
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity);
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
      pose proof (h_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF';
      pose proof (h_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD';
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK;
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 0x1059b4 (sc_sr sc) (sc_kn sc) 66 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ];
      clear HR HK; intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      rewrite PCC in RSF;
      apply (HCONT Rj RC MF msFF moF HR HK);
      [ eapply frame_mod_trans_same; [exact FA|]; eapply frame_mod_trans_same; [exact FC0 | exact FC]
      | exact OKF
      | eapply same_but_materialized_trans; [exact SBA|]; eapply same_but_materialized_trans; [exact SBC | exact SBF]
      | eapply hid_same_trans; [exact HSA|]; eapply hid_same_trans; [exact HSC | exact HSF]
      | exact RSF ] ].
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Theorem hs_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    (* LPS 75d69e00: the channel-reader premise, after fd_lookup, as stdio_call_sound_post
       now takes it. *)
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x0a2e88) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x0a2ec4) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof.
    (* LPS 75d69e00: the recorded proof applied stdio_call_sound_post one argument short of
       the reader premise.  The tactic it was recorded from is plain text in this file
       ([Ltac hf_sound] above), which now takes the premise (one intro, one bullet), so the
       proof is that tactic, as in boost-json As/AsHdrErr.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6. *)
    unfold W.
    hf_sound 0x0a2e88%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
  Qed.

  Theorem ho_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x0a2ea4) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x0a2ec4) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof.
    unfold W.
    hf_sound 0x0a2ea4%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
             ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (ASP_LO <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0x4d000)%Z -> mem (Z_to_bv 64 i) = None;
    Hgot  : forall i, (0x115000 <= i < 0x11d000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem hf_cells;
    Hcan  : rdn RSEGS mem (Z_to_bv 64 0x67d4f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Hcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x11fc30, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x11fc30) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x11fc38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x11fc40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x11fc50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67dbb8));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x11fc58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67dbb8));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x11fc68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67dbb8));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x11fcb8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x11fcbc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x67d4f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
    [sp; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma h_ev_junk : forall regs sp can i, (2 <= i < 34)%nat ->
    ev (ENV (h_vals regs sp can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Peano.lt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.length); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.eq_Transitive); constr:(@Corelib.Lists.ListDef.nth); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.junk_vals); constr:(@Corelib.Classes.Morphisms.reflexive_proper); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive); constr:(@Corelib.Classes.RelationClasses.eq_Reflexive); constr:(@Corelib.Classes.RelationClasses.symmetry); constr:(@Corelib.Classes.RelationClasses.eq_Symmetric); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Lists.ListDef.seq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.nth_map_seq); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.Lists.List.app_nth2_plus); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.vals_ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.Env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.blobs_ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.Plain.h_vals)|] [|@y; @x; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__p2; @__arith; @z0; @H0; @cstr; @Hi0; @default; @l; @lemma; @b; @i; @__p3; @H; @Hi; @can; @sp; @regs|] "#'7#+$<#4#h#5#@#$#i#%#g###B#&#'#+#s#W#(#)#2#:#O#9#8#7#N#R#[#p#0#3#I#J#K#G#H#Q#P#M#S#T#o#t#j#v#y#z#;$&$6$2$8$9#<#.#F#E#^#]#\#b#c#a#d#f#q#u#w#{#|#x$%$-$+$/$.$)$$$4$3#*$5$7$;$:$=$<#6#V#A$##1#L#n#m#?#D#>#r#k#C#U#Z#Y#e$1#/#=#X#_#`#l#~#}$($'$*$,$0L#8$#V&#x%#,$#:%#6%#y&#z%#{%#|$#}%#~'$#*$$%$%/$&%$'%$(*#Q'#5%$)$#V$$*%$+%$,&$-+$.%$/$#9%$0%$1%$2$$3$$4)$5%$6%$7$$8&$9'$:'$;%,S$US.#>#,%,#,#,#,#>#US/#VSG*##S'##?#K#$##############################################################6K#%s#$#@Gs#&####$E#G&G7s#7*$#0F#7S$2$#2#$$C#)8E8C&K$C-#$EGKVSHGKWSI%$#j#$E#j#%E#2K/j#%C#*GK0F#j#&C#j#'C#-C9-C9fS0EEECCCS1LLL%S2G;$s#C:#`S3EECCS(LL*S4@9#`S3EECCS(LL+S4@8#1EC6L5.@8#G>'?s#GG6Gs#'%$#'ABUS.s#S,#7#(s#&#%'#1ECS)LS*S5s#Ps#'0Gs#(1-C&1ECS%LS&S+Gs#*3s#1'#ZS6.-+'%#XS7-'#KUS8I&I'F#&M*#s#0VS9F#(F$0F%$C#&%%#'(F$C&F%$#9&#&N*#s#;0F#:Cs#f:Cs#h:CS';C$#;C&#A#S,:Cs#jUSJS$VSKC#WSLC#+;C#*;C'#A#S,A%S,BQ)Q$#)Q&#)Q.#CQVSMCIUSNCXSOC$G#USPCUSQCD#JDDHNVS:CS$VS:Cs$03Cs#XWSRC$#.C&S-#/)JDDH#P4*JDDH)#3CF.C'S;#/-JDDH#P.C,S-%//JDDH#P40JDDH%#[S<1JDDH)#USSD.C/S;0/4JDDH#PD5JDDHR46JDDH$#3Cs#fWS=C6#WS=C#$.C#S-7/;JDDH#P<<JDDH(,#<=JDDH.-#VST>H-S>S?VSUKI$S>#S?m$%#WSVCFGXSWKI$#l#(*)#l#)s#(s#'#l#*s#-s#,#j#+C#j#,C#j#-O#j#.O#*Gs#~$CK#%I#'%F$CKF%$#9&#'s$)I%#N2Is$(2#s$)$C#Mk##&#k##)#k#+C#k#,C#k#-O#k#.O#&S#(#s#o*$s$6(F#ZK%#&GINl#/:(#l#0s#\C#l#1s#hs#`#l#2s#ns#l#l#3s#ps#u#XS@s$@s$8s$##+s$lIBs$l)s$m$#)s$nM#Es$o#F#s$I$E#Gm#*#+s$tM)s$t#*)s$uN#Es$v#@Is$tF$#$E#I8s$zUSXs${+s$}N)s$}#3)s$~R#GS#Hs%$$#+s%&F5s%&M$#Es%''@Ms%%F$#5s%*#('Cs%+k#4s%,s%,k#5$#k#'E#8&Is%0s%044I('$#IE's$[#USYs%3Js%4s%48#J,+'#JE+'#WSZ+'#USAs%8US[EZS\Es$c#3MKK29Ks%<9aS]1-('M6%;;$::#&8+s%F#=S##Ks%A#]S^s%Bs#&s#%>:'$$#j#6s#(#GR5s%Es#,#B$s%FK(j#7s%G#&s#/+s%P#=R#-s%K#+s%Ss$s=S##j#8E#VS_S's%-XS`Es%P$#5s%Qs#8#s#.6s#9s%0*s$Xs%'0F#7s%X($#-Cs$\fS0EEECCCS1LLLs$sS2Is$]#s%Us%,s$q-C&1ECS%LS&S+s#A($s%8'#?s%XI6Is%8%$#'s%2s$c(s$ds$m%$#1ECS)LS*S5s%^s%5s$zIs$f,1ECS%LS&S+Is$g-s%>s$ps$lZS6*)'&$#XS7)&#GUS8M'Fs$iVS9Fs$^(Fs$_$Cs$_s$`%$#'s$bF$Cs$bF%$#9&#&R*#s%D0F#)Qs$bs$Y4s$QJDDHs$>s$D[S<s$RJDDHs$J#Ds$SJDDHS#3Cs%(.Cs$RSB#/s$VJDDH#P4s$WJDDH&#3Cs#'.Cs$WSB#/s$ZJDDH#P<s$[JDDH&s$K#<s$\JDDH,s$L#l#(#s$As$;l#)s$`s$_#l#*1s$d#j#+C#j#,C#j#-O#j#.O#j#9O#%Ms$79s$:#(Is%;%R#(Is#8k##$#k##'#k#+C#k#,C#k#-O#k#.O#k#9O#&Sa's%h#*$s%i'#F(F$[K&$#'GINl#/5)#l#0s#+C#l#1s#6s#/#l#2s#9s#8#l#3s#;s#?#XS@s#Ns#Js#F#ZSbs&Cs#Ss$*s%}s#|#ZSCs&Ds#Xs#[s#Ws#Q#$s&Es#^s#Ym#$#Hs&Gs$0s#a5s&Hs$.#s$%YScs&Is$2s#cs$&s$0ZSCs&Js#cs#a&$#Vs#fK#l#:s$8s$9#GNHs&Ns$>#VSD#G&s&)+s&X#=N#$s&S&#m#*#USD)>s&[US/#C#B#USd#VSe(#VSE#G$s&]#-m#,#WSfNMIUSg#VSE#G$s&b#2m#'#j#;s&>#j#8E#j#<C#j#=s&g#j#>s&g##"). Qed.
Scheme kc__2 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.Plain.hfH Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

  Lemma h_regs_ok : forall regs mem sp can, hfH regs mem sp can ->
    regs_ok (ENV (h_vals regs sp can)) h_sr regs.
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.Plain.hfH); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.regs_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.Plain.h_vals); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.h_sr); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.stk_ok); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.HF_FR); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.cells_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.hf_cells); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.regs_ok_by_idx); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@kc__3); constr:(@Corelib.Lists.ListDef.nth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.allregs32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.edenot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SeqExec.getr_zero); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Nat.sub); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsHdrErr.Plain.h_ev_junk); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.X)|] [|@i; @Hi; @n; @b; @__ff; @__varmap; @__wit; @__arith; @x; @Ha; @__x1; @__p1; @__sat66; @__sat67; @__sat68; @cstr; @Hi0; @Hcan65; @Hcan0; @Hcells0; @Hgot0; @Himg0; @Hstk0; @HspHi0; @HspLo0; @Hsp17; @H3; @Hcan64; @Hcan; @Hcells; @Hgot; @Himg; @Hstk; @HspHi; @HspLo; @Hsp16; @H2; @PH; @can; @sp; @mem; @regs|] "#>6$)%.$3$W$s##$a$t$r$9$[$]$y$>$Q$X$J%($g$C$k$x$z$j$B#$#%#&#D#F#H#J#L#N#P#R#T#V#X#Z#\#^#`#b#d#f#h#j#l#n#p#r#t#v#x#z#'#>#A#@#B#E#G#I#K#M#O#Q#S#U#W#Y#[#]#_#a#c#e#g#i#k#m#o#q#s#u#w#y#($R#C$G#*#-#7#?#{#|$0#8#;#=#}$2$4$D$E$F#)$H$L#.$M$N$O$P#,$T$S#1#3#<$m$}$~%,%.%0$)$($,$6$?$U#/#0#2#4#6#9$^$_$l$n$o$q${%#%$$|%%%)#~%*$$%+%-%/%1%3$&$%$V#+$5$Z$;$:$/$8$7$\%&$I$c$v$u$i$=$K$w$<%'%2$Y$.$d$b$h$p$f$e$`$A$-$1$@I#/$$j'$k%$l&#0%$m$$n&$o$$p%$q%$r%$s%$t'$u*$v/#4%$w$#1%$x%$y%$z&#'$${/$|&$}'$~$%#%%$%#3%%%)%&*%''%((%))%*%%+$%,$%-%(Ss<#F#(%(#(#(#(#F#G#VT7*#F)G#USx#k##'#XSyS,S+S*FXSySIS,S+S*)SiS,S+*#WT8#JSij##&#37VT96#m$N#78%#%SI#&3#S+E5S,39H$#&C#S)E9SI2Sz#E;Si2#S{XS|SlSmS}S~(?(#(#(#(#(#(#(#(#(#3#(Ss(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#3#<2<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#<B(#<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#<4<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#<Ss(#(#<#<#<#<#<#(#<#(#<#(#(#<#<#<#<#(#(#(#(#3#2s#NF<s$/<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#4Fs#O-5#5s$=S*USn#UT#s$;&s$;$#k##'#k#$C#<s$G(#<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#2s#WF<5<#(#<#(#(#(#(#(#(#(#(#(#(#(#(#3#4Fs#X-5#UT$s#.&s$e#s#-k##%#k#$C#VT%SnT&UT's$jUSx#<Ss(#(#<#(#<#<#<#(#<#(#<#<#<#(#(#<#<#(#(#(#(#3#5s%+s#a#Sj##############XT(SlT$+#5s%5T)VT*%#VT+s#'#&s#'&#2S)Sn3s%;VT:s%.#4Sn#-&#7s%Ds%1N%T,#&s%?#T;Es%AT<H#s%.&C#S)Es%DT,2Sz#Es%FT=2#S{XS|SlT>T-S~USos#j&s%E#s#ik##s#m#k#$C#USts#n&s%I#s#mk##s#E#k#$C#VT%SoT&XT(SlSts#)A5s%ST?VT*s###VT+s#E#&s#E&#2S)So4So?-$#)SuT@St*##s#+##############################################'F#Gs%{7s%|S)N$$S*K#%Sp#)SpSvT.*#UTAS)$LS*J#+%#&s%}(#k#%-#j#&D#'Sj0UTBSJ$0SjK/%SJ#)SJT.Su*#$LSjJ.+$#&s&,'#m#*#j#%,##F'#<#S*$<#K;%SK#)SKSpSJ*#$L'J:+$#&s&8'#k#%+#j#&D#'s#ns#'>s#ms#n8#5s&E#%SL#3Ss7s&H#N%SK#&s&C#Fj#'s&D#.s&E()SLSJSv*#=#s#y?s#{s#z#s#6##'s#}#-&#3s$=2s&C#3s$k4%#-%#.Cs&G.C(1DCS#GS$S(s$+s&I$s$*)#.C(1DCPGQS%s$,+%.)#@1.+)%#UTCT/UT'T/UTDCUTECUTFC6Cs&R6C3/C$S&#0&IEEH#M6C4/C&S'#0)IEEH#MA*IEEH&#VTG+H.T0T1VTHFS+&T0#T1m$%#WTICS)S*XTJFS+$#l#(*)#l#)54#l#*87#l#+#@FBs#&A;#CSLSJSvs$G#Ds&ss#6s#1s#0s#-#$s#^s$KKs#]%SL#$Ls$MJs#Z+s#2#&s&x%#m#(#j#%s#A##s#N'#s#h#s#N$s#h#Ks#g%Sk#)SkSKSL*#$L'Js#f+$#&s'('#k#%+#j#&D#'s$]s#s%SMs$M)SMSLSp*#=#Sj&s'0&#m#T-#$s#xs$dKs#w%SM#$Ls$fJs#t+)#&s'6%#m#(#j#%/##<'#s$&#<$s$&#Ks$%%SN#)SNSkSM*#$L'Js$$+$#&s'B'#k#%+#j#&D#'s$vs$1>s$us$x8#5s'O#%S-#7s'Qs#ZN%SN#&s'L#Fj#'s'M#.s'N')S-SMSK*#=#s%$?s%(s%%'s%&s#f-$#3s']2s'J#4$s#e-$#.C&1DCS#GS$S(s%0s'Ns#es%-'#1DCPGQS%s%.($s#ns#is#c@,+('$#6C*/Cs#^S&#0s#`IEEH#M/C%S's#\0s#bIEEH#MAs#cIEEH%#l#(#s#[s#Ul#)s#gs#f#l#*s#js#i#l#+#0FB51-#CS-SMSKs%;#Ds'iB>=:#$s$Ts%?Ks$S%S-#$Ls%AJs$P+?#&s'n%#m#(#j#%s#-##s#:'#s$^#s#:$s$^#Ks$]%SO#)SOSNS-*#$L'Js$\+$#&s'z'#k#%+#j#&D#'s%Qs$i>s%Ps%T8#5s(+#%S.#3s(,7s(.#N%SO#&s()#Fj#'s(*#.s(+()S.S-Sk*#=#s%\?s%as%]'s%^s$C-$#3s%|2s('#4$s$B-$#.C&1DCS#GS$S(s%is(+s$Bs%e'#1DCPGQS%s%f($s$Ks$Fs$@@,+('$#6C*/Cs$;S&#0s$=IEEH#M/C%S's$90s$?IEEH#MAs$@IEEH%#l#(#s$8s$2l#)s$Ds$C#l#*s$Gs$F#l#+#0FB51-#CS.S-Sks%s#Ds(Fs##>=:#$s%1s%wKs%0%S.#$Ls%yJs%-+?#&s(K%#m#(#j#%s#.##s#;'#s%;#s#;$s%;#Ks%:%SP#)SPSOS.*#$L'Js%9+$#&s(W'#k#%+#j#&D#'s&-s%F>s&,s&18#5s(d#%S/#7s(fs#hN%SP#&s(a#Fj#'s(b#.s(c')S/S.SN*#=#s&7?s&=s&8's&9s${-$#<s&Y3#2s(`#4$s${-$#.C&1DCS#GS$S(s&Fs(ds${s&A'#1DCPGQS%s&B($s%(s%#s$y@-,('$#6C*/Cs$tS&#0s$vIEEH#M/C%S's$r0s$xIEEH#MAs$yIEEH%#l#(#s$qs$kl#)s$}s$|#l#*s%$s%##l#+#0FB61-#CS/S.SNs&O#Ds)#s##?>;#$s%js&SKs%i%S/#$Ls&UJs%f+@#&s)(%#m#(#j#%s#.##s#;'#s%t#s#;$s%t#Ks%s%SQ#)SQSPS/*#$L'Js%r+$#&s)4'#k#%+#j#&D#'s&es&#>s&ds&j8#5s)A#%S0#7s)Cs#hN%SQ#&s)>#Fj#'s)?#.s)@')S0S/SO*#=#s&o?s&vs&p's&qs%X-$#3s)L2s)<#4$s%W-$#.C&1DCS#GS$S(s&~s)@s%Ws&x'#1DCPGQS%s&y($s%`s%[s%U@,+('$#6C*/Cs%PS&#0s%RIEEH#M/C%S's%N0s%TIEEH#MAs%UIEEH%#l#(#s%Ms%Gl#)s%Ys%X#l#*s%\s%[#l#+#0FB51-#CS0S/SOs'*#Ds)[B>=:#$s&Fs'.Ks&E%S0#$Ls'0Js&B+?#&s)`%#m#(#j#%s#-##s#:'#s&P#s#:$s&P#Ks&O%SR#)SRSQS0*#$L'Js&N+$#&s)l'#k#%+#j#&D#'s'@s&[>s&ss'F8#5s)y#%S1#7s){s#gN%SR#&s)v#Fj#'s)w#.s)x')S1S0SP*#=#s&~?s'Rs'#'s'$s&4-$#3s(X2s)t#4$s&3-$#.C&1DCS#GS$S(s'Zs)xs&3s'+'#1DCPGQS%s',($s&<s&7s&1@,+('$#6C*/Cs&,S&#0s&.IEEH#M/C%S's&*0s&0IEEH#MAs&1IEEH%#l#(#s&)s&#l#)s&5s&4#l#*s&8s&7#l#+#0FB51-#CS1S0SPs'9#Ds*7B>=:#$s&~s'eKs&}%S1#$Ls'gJs&z+?#&s*<%#m#(#j#%s#-##s#:'#s',#s#:$s',#Ks'+%SS#)SSSRS1*#$L'Js'*+$#&s*H'#k#%+#j#&D#'s'ws'7>s'Ns'~8#5s*U#%S2#7s*Ws#gN%SS#&s*R#Fj#'s*S#.s*T')S2S1SQ*#=#s'Y?s(.s'Z's'[s&l-$#(s*c3#2s*Q#4$s&l-$#.C&1DCS#GS$S(s(7s*Us&ls'c'#1DCPGQS%s'd($s&us&ps&j@-,('$#6C*/Cs&eS&#0s&gIEEH#M/C%S's&c0s&iIEEH#MAs&jIEEH%#l#(#s&bs&\l#)s&ns&m#l#*s&qs&p#l#+#0FB61-#CS2S1SQs'q#Ds*ps##?>;#$s'[s(AKs'Z%S2#$Ls(CJs'W+@#&s*u%#m#(#j#%s#.##s#;'#s'e#s#;$s'e#Ks'd%ST#)STSSS2*#$L'Js'c+$#&s+%'#k#%+#j#&D#'s(+s'p>s(*s([8#5s+2#%S3#7s+4s#hN%ST#&s+/#Fj#'s+0#.s+1')S3S2SR*#=#s(5?s(gs(6's(7s'I-$#<s+@3#2s+.#4$s'I-$#.C&1DCS#GS$S(s(ps+2s'Is(?'#1DCPGQS%s(@($s'Rs'Ms'G@-,('$#6C*/Cs'BS&#0s'DIEEH#M/C%S's'@0s'FIEEH#MAs'GIEEH%#l#(#s'?s'9l#)s'Ks'J#l#*s'Ns'M#l#+#0FB61-#CS3S2SRs(M#Ds+Ms##?>;#$s(8s(QKs(7%S3#$Ls(SJs(4+@#&s+R%#m#(#j#%s#.##s#;'#s(B#s#;$s(B#Ks(A%SU#)SUSTS3*#$L'Js(@+$#&s+^'#k#%+#j#&D#'s(cs(M>s(bs)88#5s+k#%S4#7s+ms#hN%SU#&s+h#Fj#'s+i#.s+j')S4S3SS*#=#s(m?s)Ds(n's(os(&-$#3s)^2s+f#4$s(%-$#.C&1DCS#GS$S(s)Ls+js(%s(v'#1DCPGQS%s(w($s(.s()s(#@,+('$#6C*/Cs'zS&#0s'|IEEH#M/C%S's'x0s'~IEEH#MAs(#IEEH%#l#(#s'ws'ql#)s('s(&#l#*s(*s()#l#+#0FB51-#CS4S3SSs)(#Ds,)B>=:#$s(ps),Ks(o%S4#$Ls).Js(l+?#&s,.%#m#(#j#%s#-##s#:'#s(z#s#:$s(z#Ks(y%SV#)SVSUS4*#$L'Js(x+$#&s,:'#k#%+#j#&D#'s)>s))>s)=s)p8#5s,G#%S5#7s,Is#gN%SV#&s,D#Fj#'s,E#.s,F')S5S4ST*#=#s)H?s)|s)I's)Js(^-$#<s*;3#2s,C#4$s(^-$#.C&1DCS#GS$S(s*)s,Gs(^s)R'#1DCPGQS%s)S($s(gs(bs(\@-,('$#6C*/Cs(WS&#0s(YIEEH#M/C%S's(U0s([IEEH#MAs(\IEEH%#l#(#s(Ts(Nl#)s(`s(_#l#*s(cs(b#l#+#0FB61-#CS5S4STs)`#Ds,bs##?>;#$s)Ms)dKs)L%S5#$Ls)fJs)I+@#&s,g%#m#(#j#%s#.##s#;'#s)W#s#;$s)W#Ks)V%SW#)SWSVS5*#$L'Js)U+$#&s,s'#k#%+#j#&D#'s)vs)b>s)us*M8#5s-$#%S6#7s-&s#hN%SW#&s,}#Fj#'s,~#.s-#')S6S5SU*#=#s*$?s*Ys*%'s*&s);-$#(s&z3#2s,|#4$s);-$#.C&1DCS#GS$S(s*bs-$s);s*.'#1DCPGQS%s*/($s)Ds)?s)9@-,('$#6C*/Cs)4S&#0s)6IEEH#M/C%S's)20s)8IEEH#MAs)9IEEH%#l#(#s)1s)+l#)s)=s)<#l#*s)@s)?#l#+#0FB61-#CS6S5SUs*<#Ds-?s##?>;#$s**s*@Ks*)%S6#$Ls*BJs*&+@#&s-D%#m#(#j#%s#.##s#;'#s*4#s#;$s*4#Ks*3%SX#)SXSWS6*#$L'Js*2+$#&s-P'#k#%+#j#&D#'s*Rs*?>s*Qs+*8#5s-]#%S7#7s-_s#hN%SX#&s-Z#Fj#'s-[#.s-\')S7S6SV*#=#s*\?s+6s*]'s*^s)t-$#<s'W3#2s-Y#4$s)t-$#.C&1DCS#GS$S(s+?s-]s)ts*f'#1DCPGQS%s*g($s)}s)xs)r@-,('$#6C*/Cs)mS&#0s)oIEEH#M/C%S's)k0s)qIEEH#MAs)rIEEH%#l#(#s)js)dl#)s)vs)u#l#*s)ys)x#l#+#0FB61-#CS7S6SVs*t#Ds-xs##?>;#$s*cs*xKs*b%S7#$Ls*zJs*_+@#&s-}%#m#(#j#%s#.##s#;'#s*m#s#;$s*m#Ks*l%SY#)SYSXS7*#$L'Js*k+$#&s.-'#k#%+#j#&D#'s+.s*x>s+-s+c8#5s.:#%S8#7s.<s#hN%SY#&s.7#Fj#'s.8#.s.9')S8S7SW*#=#s+8?s+os+9's+:s*Q-$#2s.4s.-4s..s*O-$#.Cs.01DCS#GS$S(s+vs.8s*Os+@s.1#1DCPGQS%s+As.2$s*Xs*Ss*M@+*('$#6Cs.4/Cs*HS&#0s*JIEEH#M/C%S's*F0s*LIEEH#MAs*MIEEH%#l#(#s*Es*?l#)s*Qs*P#l#*s*Ts*S#l#+#0FB41-#CS8S7SWs+N#Ds.SA=<9#$s+>s+RKs+=%S8#$Ls+TJs+:+>#&s.X%#m#(#j#%s#,##s#9'#s+H#s#9$s+H#Ks+G%SZ#)SZSYS8*#$L'Js+F+$#&s.d'#k#%+#j#&D#'s+ds+S>s+cs,>8#5s.q#%S9#7s.ss#fN%SZ#&s.n#Fj#'s.o#.s.p')S9S8SX*#=#s+n?s,Js+o's+ps+,-$#3s-72s.l#4$s++-$#.C&1DCS#GS$S(s,Rs.ps++s+w'#1DCPGQS%s+x($s+4s+/s+)@,+('$#6C*/Cs+$S&#0s+&IEEH#M/C%S's*~0s+(IEEH#MAs+)IEEH%#l#(#s*}s*wl#)s+-s+,#l#*s+0s+/#l#+#0FB51-#CS9S8SXs,)#Ds//B>=:#$s+vs,-Ks+u%S9#$Ls,/Js+r+?#&s/4%#m#(#j#%s#-##s#:'#s,$#s#:$s,$#Ks,#%S[#)S[SZS9*#$L'Js+~+$#&s/@'#k#%+#j#&D#'s,?s,/>s,>s,v8#5s/M#%S:#7s/Os/5N%S[#&s/J#Fj#'s/K#.s/L')S:S9SY*#=#s,I?s-&s,J's,Ks+d-$#(s.,3#2s/I#4$s+d-$#.C&1DCS#GS$S(s-/s/Ms+ds,S'#1DCPGQS%s,T($s+ms+hs+b@-,('$#6C*/Cs+]S&#0s+_IEEH#M/C%S's+[0s+aIEEH#MAs+bIEEH%#l#(#s+Zs+Tl#)s+fs+e#l#*s+is+h#l#+#0FB61-#CS:S9SYs,a#Ds/hs##?>;#$s,Ss,eKs,R%S:#$Ls,gJs,O+@#&s/m%#m#(#j#%s#.##s#;'#s,]#s#;$s,]#Ks,\%S\#)S\S[S:*#$L'Js,[+$#&s/y'#k#%+#j#&D#'s,ws,h>s,vs-S8#5s0*#%S;#7s0,s#hN%S\#&s0'#Fj#'s0(#.s0)')S;S:SZ*#=#s-%?s-_s-&'s-'s,A-$#3s.d2s0%#4$s,@-$#.C&1DCS#GS$S(s-gs0)s,@s-.'#1DCPGQS%s-/($s,Is,Ds,>@,+('$#6C*/Cs,9S&#0s,;IEEH#M/C%S's,70s,=IEEH#MAs,>IEEH%#l#(#s,6s,0l#)s,Bs,A#l#*s,Es,D#l#+#0FB51-#CS;S:SZs-<#Ds0DB>=:#$s-/s-@Ks-.%S;#$Ls-BJs-++?#&s0I%#m#(#j#%s#-##s#:'#s-9#s#:$s-9#Ks-8%S]#)S]S\S;*#$L'Js-7+$#&s0U'#k#%+#j#&D#'s-Rs-D>s-Qs./8#5s0b#%S<#7s0ds#gN%S]#&s0_#Fj#'s0`#.s0a')S<S;S[*#=#s-\?s.;s-]'s-^s,y-$#(s(k3#2s0^#4$s,y-$#.C&1DCS#GS$S(s.Ds0bs,ys-f'#1DCPGQS%s-g($s-&s,}s,w@-,('$#6C*/Cs,rS&#0s,tIEEH#M/C%S's,p0s,vIEEH#MAs,wIEEH%#l#(#s,os,il#)s,{s,z#l#*s,~s,}#l#+#0FB61-#CS<S;S[s-t#Ds0}s##?>;#$s-hs-xKs-g%S<#$Ls-zJs-d+@#&s1&%#m#(#j#%s#.##s#;'#s-r#s#;$s-r#Ks-q%S^#)S^S]S<*#$L'Js-p+$#&s12'#k#%+#j#&D#'s..s-}>s.-s.h8#5s1?#%S=#7s1As#hN%S^#&s1<#Fj#'s1=#.s1>')S=S<S\*#=#s.8?s.ts.9's.:s-V-$#<s)H3#2s1;#4$s-V-$#.C&1DCS#GS$S(s.}s1?s-Vs.B'#1DCPGQS%s.C($s-_s-Zs-T@-,('$#6C*/Cs-OS&#0s-QIEEH#M/C%S's-M0s-SIEEH#MAs-TIEEH%#l#(#s-Ls-Fl#)s-Xs-W#l#*s-[s-Z#l#+#0FB61-#CS=S<S\s.P#Ds1Zs##?>;#$s.Es.TKs.D%S=#$Ls.VJs.A+@#&s1_%#m#(#j#%s#.##s#;'#s.O#s#;$s.O#Ks.N%S_#)S_S^S=*#$L'Js.M+$#&s1k'#k#%+#j#&D#'s.fs.Z>s.es/E8#5s1x#%S>#7s1zs#hN%S_#&s1u#Fj#'s1v#.s1w')S>S=S]*#=#s.p?s/Qs.q's.rs.3-$#(s)H3#2s1t#4$s.3-$#.C&1DCS#GS$S(s/Zs1xs.3s.z'#1DCPGQS%s.{($s.<s.7s.1@-,('$#6C*/Cs.,S&#0s..IEEH#M/C%S's.*0s.0IEEH#MAs.1IEEH%#l#(#s.)s.#l#)s.5s.4#l#*s.8s.7#l#+#0FB61-#CS>S=S]s/,#Ds27s##?>;#$s.~s/0Ks.}%S>#$Ls/2Js.z+@#&s2<%#m#(#j#%s#.##s#;'#s/,#s#;$s/,#Ks/+%S`#)S`S_S>*#$L'Js/*+$#&s2H'#k#%+#j#&D#'s/Bs/7>s/As/~8#5s2U#%S?#7s2Ws#hN%S`#&s2R#Fj#'s2S#.s2T')S?S>S^*#=#s/L?s0.s/M's/Ns.l-$#<s*%3#2s2Q#4$s.l-$#.C&1DCS#GS$S(s07s2Us.ls/V'#1DCPGQS%s/W($s.us.ps.j@-,('$#6C*/Cs.eS&#0s.gIEEH#M/C%S's.c0s.iIEEH#MAs.jIEEH%#l#(#s.bs.\l#)s.ns.m#l#*s.qs.p#l#+#0FB61-#CS?S>S^s/d#Ds2ps##?>;#$s/[s/hKs/Z%S?#$Ls/jJs/W+@#&s2u%#m#(#j#%s#.##s#;'#s/e#s#;$s/e#Ks/d%Sa#)SaS`S?*#$L'Js/c+$#&s3%'#k#%+#j#&D#'s/zs/p>s/ys0[8#5s32#%S@#7s34s#hN%Sa#&s3/#Fj#'s30#.s31')S@S?S_*#=#s0(?s0gs0)'s0*s/I-$#(s1%3#2s3.#4$s/I-$#.C&1DCS#GS$S(s0ps32s/Is02'#1DCPGQS%s03($s/Rs/Ms/G@-,('$#6C*/Cs/BS&#0s/DIEEH#M/C%S's/@0s/FIEEH#MAs/GIEEH%#l#(#s/?s/9l#)s/Ks/J#l#*s/Ns/M#l#+#0FB61-#CS@S?S_s0@#Ds3Ms##?>;#$s08s0DKs07%S@#$Ls0FJs04+@#&s3R%#m#(#j#%s#.##s#;'#s0B#s#;$s0B#Ks0A%Sb#)SbSaS@*#$L'Js0@+$#&s3^'#k#%+#j#&D#'s0Vs0M>s0Us188#5s3k#%SA#7s3ms#hN%Sb#&s3h#Fj#'s3i#.s3j')SAS@S`*#=#s0`?s1Ds0a's0bs0&-$#3s1]2s3f#4$s0%-$#.C&1DCS#GS$S(s1Ls3js0%s0i'#1DCPGQS%s0j($s0.s0)s0#@,+('$#6C*/Cs/zS&#0s/|IEEH#M/C%S's/x0s/~IEEH#MAs0#IEEH%#l#(#s/ws/ql#)s0's0&#l#*s0*s0)#l#+#0FB51-#CSAS@S`s0w#Ds4)B>=:#$s0ps0{Ks0o%SA#$Ls0}Js0l+?#&s4.%#m#(#j#%s#-##s#:'#s0z#s#:$s0z#Ks0y%Sc#)ScSbSA*#$L'Js0x+$#&s4:'#k#%+#j#&D#'s11s1)>s10s1p8#5s4G#%SB#7s4Is#gN%Sc#&s4D#Fj#'s4E#.s4F')SBSASa*#=#s1;?s1|s1<'s1=s0^-$#(s*^3#2s4C#4$s0^-$#.C&1DCS#GS$S(s2)s4Gs0^s1E'#1DCPGQS%s1F($s0gs0bs0\@-,('$#6C*/Cs0WS&#0s0YIEEH#M/C%S's0U0s0[IEEH#MAs0\IEEH%#l#(#s0Ts0Nl#)s0`s0_#l#*s0cs0b#l#+#0FB61-#CSBSASas1S#Ds4bs##?>;#$s1Ms1WKs1L%SB#$Ls1YJs1I+@#&s4g%#m#(#j#%s#.##s#;'#s1W#s#;$s1W#Ks1V%Sd#)SdScSB*#$L'Js1U+$#&s4s'#k#%+#j#&D#'s1is1b>s1hs2M8#5s5$#%SC#7s5&s#hN%Sd#&s4}#Fj#'s4~#.s5#')SCSBSb*#=#s1s?s2Ys1t's1us1;-$#<s+;3#2s4|#4$s1;-$#.C&1DCS#GS$S(s2bs5$s1;s1}'#1DCPGQS%s1~($s1Ds1?s19@-,('$#6C*/Cs14S&#0s16IEEH#M/C%S's120s18IEEH#MAs19IEEH%#l#(#s11s1+l#)s1=s1<#l#*s1@s1?#l#+#0FB61-#CSCSBSbs2/#Ds5?s##?>;#$s2*s23Ks2)%SC#$Ls25Js2&+@#&s5D%#m#(#j#%s#.##s#;'#s24#s#;$s24#Ks23%Se#)SeSdSC*#$L'Js22+$#&s5P'#k#%+#j#&D#'s2Es2?>s2Ds3*8#5s5]#%SD#7s5_s#hN%Se#&s5Z#Fj#'s5[#.s5\')SDSCSc*#=#s2O?s36s2P's2Qs1t-$#(s+;3#2s5Y#4$s1t-$#.C&1DCS#GS$S(s3?s5]s1ts2Y'#1DCPGQS%s2Z($s1}s1xs1r@-,('$#6C*/Cs1mS&#0s1oIEEH#M/C%S's1k0s1qIEEH#MAs1rIEEH%#l#(#s1js1dl#)s1vs1u#l#*s1ys1x#l#+#0FB61-#CSDSCScs2g#Ds5xs##?>;#$s2cs2kKs2b%SD#$Ls2mJs2_+@#&s5}%#m#(#j#%s#.##s#;'#s2m#s#;$s2m#Ks2l%Sf#)SfSeSD*#$L'Js2k+$#&s6-'#k#%+#j#&D#'s2}s2x>s2|s3c8#5s6:#%SE#7s6<s#hN%Sf#&s67#Fj#'s68#.s69')SESDSd*#=#s3+?s3os3,'s3-s2Q-$#<s+t3#2s66#4$s2Q-$#.C&1DCS#GS$S(s3xs6:s2Qs35'#1DCPGQS%s36($s2Zs2Us2O@-,('$#6C*/Cs2JS&#0s2LIEEH#M/C%S's2H0s2NIEEH#MAs2OIEEH%#l#(#s2Gs2Al#)s2Ss2R#l#*s2Vs2U#l#+#0FB61-#CSESDSds3C#Ds6Us##?>;#$s3@s3GKs3?%SE#$Ls3IJs3<+@#&s6Z%#m#(#j#%s#.##s#;'#s3J#s#;$s3J#Ks3I%Sg#)SgSfSE*#$L'Js3H+$#&s6f'#k#%+#j#&D#'s3Ys3U>s3Xs4@8#5s6s#%SF#7s6us#hN%Sg#&s6p#Fj#'s6q#.s6r')SFSESe*#=#s3c?s4Ls3d's3es3.-$#(s+t3#2s6o#4$s3.-$#.C&1DCS#GS$S(s4Us6ss3.s3m'#1DCPGQS%s3n($s37s32s3,@-,('$#6C*/Cs3'S&#0s3)IEEH#M/C%S's3%0s3+IEEH#MAs3,IEEH%#l#(#s3$s2zl#)s30s3/#l#*s33s32#l#+#0FB61-#CSFSESes3{#Ds72s##?>;#$s3ys4#Ks3x%SF#$Ls4%Js3u+@#&s77%#m#(#j#%s#.##s#;'#s4'#s#;$s4'#Ks4&%Sh#)ShSgSF*#$L'Js4%+$#&s7C'#k#%+#j#&D#'s45s42>s44s4y8#5s7P#%SG#7s7Rs#hN%Sh#&s7M#Fj#'s7N#.s7O')SGSFSf*#=#s4??s5)s4@'s4As3g-$#<s,Q3#2s7L#4$s3g-$#.C&1DCS#GS$S(s52s7Ps3gs4I'#1DCPGQS%s4J($s3ps3ks3e@-,('$#6C*/Cs3`S&#0s3bIEEH#M/C%S's3^0s3dIEEH#MAs3eIEEH%#l#(#s3]s3Wl#)s3is3h#l#*s3ls3k#l#+#0FB61-#CSGSFSfs4W#Ds7ks##?>;#$s4Vs4[Ks4U%SG#$Ls4]Js4R+@#&s7p%#m#(#j#%s#.##s#;'#s4`#s#;$s4`#Ks4_%Sq#)SqShSG*#$L'Js4^+$#&s7|'#k#%+#j#&D#'s4ms4k>s4ls5V8#5s8-#%SH#7s8/s#hN%Sq#&s8*#Fj#'s8+#.s8,')SHSGSg*#=#s4w?s5bs4x's4ys4D-$#3s862s8(#4$s4C-$#.C&1DCS#GS$S(s5js8,s4Cs5$'#1DCPGQS%s5%($s4Ls4Gs4A@,+('$#6C*/Cs4<S&#0s4>IEEH#M/C%S's4:0s4@IEEH#MAs4AIEEH%#l#(#s49s43l#)s4Es4D#l#*s4Hs4G#l#+#0FB51-#CSHSGSgs52#Ds8GB>=:#$s52s56Ks51%SH#$Ls58Js5.+?#&s8L%#m#(#j#%s#-##s#:'#s5<#s#:$s5<#Ks5;%Sw#)SwSqSH*#$L'Js5:+$#&s8X'#k#%+#j#&D#'s5Hs5G>s4ps628#5s8e#%Sr#7s8gs#gN%Sw#&s8b#Fj#'s8c#.s8d')SrSHSh*#=#s4{?s6>s4|'s4}s4|-$#<s8o3#2s8a#4$s4|-$#.C&1DCS#GS$S(s6Gs8es4|s5)'#1DCPGQS%s5*($s5)s5$s4z@-,('$#6C*/Cs4uS&#0s4wIEEH#M/C%S's4s0s4yIEEH#MAs4zIEEH%#l#(#s4rs4ll#)s4~s4}#l#*s5%s5$#l#+#0FB61-#CSrSHShs57#Ds9$s##?>;#$s5ks5nKs5j%Sr#$Ls5pJs5g+@#&s9)%#m#(#j#%s#.##s#;'#s5u#s#;'#s5w8S*,#s5O,#s5P,#s5Q,#s5R,#s5S,#s5T,#s5U,#s5V,#s5W,#s5X,#s5Y,#s5Z,#s5[,#s5\,#s5],#s5^,#s5_,#s5`,#s5a,#s5b,#s5c,#s5d,#s5e,#s5f,#s5g,#s5h,#s5i,#s5j,#s5k,#s5l,#s5m,#s5n4#s#|,Fs5pj#,C#U#s#&U$#U%#U&#U'#U(#U)#U*#U+#U,#U-#U.#U/#U0#U1#U2#U3#U4#U5#U6#U7#U8#U9#U:#U;#U<#U=#U>#U?#U@#UA#UB#.Cs#F9DDCCOGGs#$RS*s#G#9DDCCOGGs#%Rs6Gs#$#9DDCCOGGs#&Rs5Xs#$#9DDCCOGGs#'Rs5?s#$#9DDCCOGGs#(Rs4ds#$#9DDCCOGGs#)Rs4,s#$#9DDCCOGGs#*Rs3Ps#$#9DDCCOGGs#+Rs2us#$#9DDCCOGGs#,Rs2>s#$#9DDCCOGGs#-Rs1bs#$#9DDCCOGGs#.Rs1*s#$#9DDCCOGGs#/Rs0Os#$#9DDCCOGGs#0Rs/ss#$#9DDCCOGGs#1Rs/;s#$#9DDCCOGGs#2Rs._s#$#9DDCCOGGs#3Rs.)s#$#9DDCCOGGs#4Rs-Ns#$#9DDCCOGGs#5Rs,rs#$#9DDCCOGGs#6Rs,;s#$#9DDCCOGGs#7Rs+_s#$#9DDCCOGGs#8Rs+'s#$#9DDCCOGGs#9Rs*Ks#$#9DDCCOGGs#:Rs)os#$#9DDCCOGGs#;Rs)7s#$#9DDCCOGGs#<Rs(\s#$#9DDCCOGGs#=Rs($s#$#9DDCCOGGs#>Rs'Hs#$#9DDCCOGGs#?Rs&ls#$#9DDCCOGGs#@Rs&4s#$#9DDCCOGGs#ARs%Xs#$#9DDCCOGGs#BRs$|s#$#9DDCCOGGs#CRs$Es#$#1DCPGQS%s#is#$#s7%s$ds$`XTKs#is#G#FUTLS+8S+2S)#Es:?TMVTN#s:,2S)$2S)s:.Es:CTOH#s:02S)#k##&#k##(#VTPs:;s7l4S)s:<2S)s7n4S)s7nk##$#k##&#2S)s:AWTQs:Bs7sS*j##T2#j#-%#2S)s7uk##T2#k#-(#VTRCS*XT3Cs6XS*#XT3C#S*s6Y6CS)VTSCs8F/C$S&#0s6[IEEH#MUT#E6Cs6z:C'#:C#$:C#%:C#&:C#':C#(:C#):C#*:C#+:C#,:C#-:C#.:C#/:C#0:C#1:C#2:C#3:C#4:C#5:C#6:C#7:C#8:C#9:C#::C#;:C#<:C#=:C#>:C#?:C#@:C#A:C#B/C#S's%D0s7#IEEH#MZTTs7$IEEHS,\T4s7%IEEH$s#'#\T4s7&IEEHs#)s#(#l#(#s6zs6tl#)s#/s7)#l#*s7-s7,#j#.C#j#/T5#2S)F,S*s7J,#s7K,#s7L,#s7M,#s7N,#s7O,#s7P,#s7Q,#s7R,#s7S,#s7T,#s7U,#s7V,#s7W,#s7X,#s7Y,#s7Z,#s7[,#s7\,#s7],#s7^,#s7_,#s7`,#s7a,#s7b,#s7c,#s7d,#s7e,#s7f,#s7g,#s7h,#s7i4#s%wk###S,k##s#%#k#.C#k#/T5##Sm##############################################################$s8[#Ks8Z%T6#)T6TUTV*#$L'Js8Y+$#&s;w'#8SmXF$#SISil#+s#Rs#,#l#0s$-s$*#l#1s$7s$2#l#2s$@s$9#l#3s$Es$C#l#4s$Gs%0#j#%s%U#j#$D#U#Fj#&D#;s&,s%[#Fj#&D#U#Fj#&D#;s&hs&<#Fj#&D#U#Fj#&D#;s'Is&x#Fj#&D#U#Fj#&D#;s(*s'Y#Fj#&D#U#Fj#&D#;s(gs(:#Fj#&D#U#Fj#&D#;s)Hs(w#Fj#&D#U#Fj#&D#;s*)s)X#Fj#&D#U#Fj#&D#;s*fs*9#Fj#&D#U#Fj#&D#;s+Fs*v#Fj#&D#U#Fj#&D#;s,'s+V#Fj#&D#U#Fj#&D#;s,ds,7#Fj#&D#U#Fj#&D#;s-Es,t#Fj#&D#U#Fj#&D#;s.&s-U#Fj#&D#U#Fj#&D#;s.cs.6#Fj#&D#U#Fj#&D#;s/Cs.s#Fj#&D#U#Fj#&D#;s0$s/S#Fj#&D#U#Fj#&D#;s0`s04#Fj#&D#U#Fj#&D#;s1?s0p#Fj#&D#U#Fj#&D#;s1|s1O#Fj#&D#U#Fj#&D#;s2]s20#Fj#&D#U#Fj#&D#;s3>s2m#Fj#&D#U#Fj#&D#;s3zs3N#Fj#&D#U#Fj#&D#;s4[s4.#Fj#&D#U#Fj#&D#;s5<s4k#Fj#&D#U#Fj#&D#;s5xs5L#Fj#&D#U#Fj#&D#;s6Xs6,#Fj#&D#U#Fj#&D#;s79s6h#Fj#&D#U#Fj#&D#;s7vs7I#Fj#&D#U#Fj#&D#;s8Vs8*#Fj#&D#U#Fj#&D#;s8ts8f#Fj#&D#U#Fj#&D#;s9hs9(#Fj#&D#U#Fj#&D#;s:'s9x#S*U#Fj#%s:5#j#$D#XTWs:PJSu#j#5s:S#j#6s:W#j#7s:]#j#8s:_#j#9s:d#j#:s:i#j#;s:k#j#<s:n#j#=s:q#j#>s:u#^#T)TXSmS}SiSIS,S+S*Fj#?s:z#j#@s;$#j#As;L#j#Bs;N#j#Cs;y#j#Ds=C#j#Es=E#j#Fs=H#j#Gs=K#j#Hs=P#[TYSIS,S+S*s=W#Fj#Is=]#j#JC#j#Ks=e#j#Ls=a#j#Ms=f##"). Qed.

  Lemma h_know_ok : forall regs mem sp can, hfH regs mem sp can ->
    know_ok RSEGS (ENV (h_vals regs sp can)) mem h_kn.
  Proof.
    intros regs mem sp can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (h_vals regs sp can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (h_vals regs sp can)) 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold ASP_LO, ASP_HI in *.
    unfold h_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | assumption]].
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp HF_FR); [exact E0 | assumption | unfold HF_FR; lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  Qed.

  Ltac hf_plain SOUND :=
    (* LPS 75d69e00: + Hrd2, immediately after Hfd2, passed straight to SOUND. *)
    intros regs mem msF mo sp can K PH OK RS Hfd2 Hrd2 HKnil HCONT;
    pose proof (h_regs_ok regs mem sp can PH) as HR; pose proof (h_know_ok regs mem sp can PH) as HK;
    destruct PH; pose proof (u64_range sp) as Hsp; unfold ASP_LO, ASP_HI in *;
    apply (SOUND sp L S Zr (h_vals regs sp can) regs mem msF mo K);
      [ unfold h_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd2 | exact Hrd2 | exact OK | exact RS | exact HKnil |];
    clear HR HK; intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS';
    set (vals' := h_vals regs sp can ++ junk_vals Rj) in *;
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity;
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity;
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))));
    [ intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold h_vals; rewrite length_app, junk_vals_length; cbn; lia);
      apply (h_ev_junk regs sp can i Hi) |];
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']; split;
    [ regv HR (2 : reg); exact P0
    | regv HR (10 : reg); reflexivity
    | intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity
    | exact FM
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | let Hc := fresh "Hc" in krd HK 0x67d4f0%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.False Sort Prop.

  Theorem as_hdr_short_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x0a2e88) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x0a2ec4) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof. hf_plain hs_sound. Qed.

  Theorem as_hdr_overrun_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x0a2ea4) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x0a2ec4) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

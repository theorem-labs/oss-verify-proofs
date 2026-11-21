(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail
  LazyRestrict LazySR LazyFdNodes LazySym Spec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import RefExitBase RefStdioDefs.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsLazyRun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsStdioWrite AsStdioCall.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsScLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsPrintfFirst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HF_FR : Z := 2400%Z.
Definition STOPSH : list Z := [0x109138; 0x0a4190]%Z.
Definition FUELH : nat := 8000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition hf_cells : list (Z * nat * Z) :=
  [(0x1214b0, 8%nat, 0x109c68)   (* [comment removed for export] *);
   (0x12d7b8, 8%nat, 0x7fff8000) (* [comment removed for export] *);
   (0x12e498, 1%nat, 0x1)        (* [comment removed for export] *);
   (0x123ef0, 4%nat, 0x5)        (* [comment removed for export] *);
   (0x123f10, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x123f38, 8%nat, 0x109138)   (* [comment removed for export] *);
   (0x123f48, 8%nat, 0x681ef8)   (* [comment removed for export] *);
   (0x123f50, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x123f68, 4%nat, 0x2)        (* [comment removed for export] *);
   (0x123f78, 4%nat, 0x0)        (* [comment removed for export] *);
   (0x123f7c, 4%nat, 0xffffffff) (* [comment removed for export] *);
   (0x7fffc620, 8%nat, 0x0); (0x7fffc628, 8%nat, 0x0)   (* [comment removed for export] *);
   (0x7fffad00, 8%nat, 0x0); (0x7fffad08, 8%nat, 0x0)   (* [comment removed for export] *)]%Z.

Definition h_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI;
   KWr (SA (EVar 0) (- HF_FR)) HF_FR;
   KImg 0x10000 0x4e000; KImg 0x119000 0x121000;
   KWord (SA (ELit 0) 0x681830) 8 (EVar 1);
   KWr (SA (ELit 0) 0x123ef0) 232]%Z
  ++ kn_cells hf_cells.

Definition sc_dummy : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0a4154 h_sr [] h_kn 34) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x109cf0 (sc_sr hs_sc) [] (sc_kn hs_sc) 66) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary :
  s_pc (fst (fst hs_rA)) = 0x109138%Z /\ snd (fst hs_rA) = [] /\ snd (fst hs_cA) = []
  /\ stdio_call 34 hs_srA hs_knA = Some hs_sc
  /\ (sc_ret hs_sc, sc_f hs_sc, sc_fd hs_sc, sc_s hs_sc, sc_l hs_sc) = (0x109cf0%Z, 0x123ef0%Z, 2%Z, ELit 0x23131%Z, ELit 31%Z)
  /\ s_pc (fst (fst hs_rC)) = 0x0a4190%Z /\ snd (fst hs_rC) = [] /\ snd (fst hs_cC) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_res); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_rA); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_cA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_srA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_knA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_fd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_rC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hs_cC)|] Array.empty "#0p###Y#?#=#(#T#K#,#2#/#:#D#E#3#L#I#1#6#7#8#B#C#4#M#O#P#Q#R#S#U#V#W#X#Y#Z#[#*#+#<#>#)#A#@#9#5#;#'#-#G#&#F#J#H#N#.#07#E$#F$#G&#H$#I$#J%#K&#L$#M$#N$#O&#P%#Q'#R'#S%#T&#U%#V&#W$#X$#H######$#####$#####$###$#$#######$#####'##H######$#####$#######$#####$#$#$#######'#$H##$#############$#$#$#$###$#$#$#$#$#######'#$s#,$#######$#####$#$#######$#'#$s#6$#####$#$#$#$#########'#$s#I######$#$#$#$#$###$#$#$#$#########'#$-######$#########'#$(######'#$/##$#######'##5########'#$s#$######'#$B$#$#$#######'##s#p##$#$###$###$#####$###$#$#####'#$s$;####$###########$#$#####$#########'##s$K######################'#$s#o$###########################'#$s$<########################'##s$.$#########################'##s$i########$#$#########'#$;####$###$#$#########'##s$b$#$###$#######'#$s$`$###$###$#$#$#$###$#$#$#######'#$2####$#####$#####$#$#######'#$s$_$#######'##s$S##$#######'#$)########'##s$_$#######'#$s$c####'#$s%u$#$#$#$#$#$#$#$#$#$#$#$#$#$#######$#$#######$###########'#$(######'##8$###$#$###$#################'#$(######'#-Es&Rs&R5J6J-$##UQI$s'#####$#############$#####$#########'#'s'7$s'1$#$#####$#$#$#$#$#####'#$H####$#$#######$#########$#####$#$#$#######'#+s&x+R$s'\$#######$#####$#$#######$#'#+s&z$s#+$#$#'#+#*K#8##$#########,#+#WS#S$,#&K&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#*#+s'E*B*B&'&#&#&#&#*#&$*#&$*#'H+#&&&#&#&#*#&$*#&$*#&$*#&$*#&$*#&$*#+s'R*s#/*s#/*s#/*s#/*s#/*s#/&+&#&#&#&#&#&#&#&#&#&#*#&$*#&$*#&$*#6D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#8#%Ds#9#%Ds#(#%Ds#x#%Ds#+#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds$$#%Ds$%#%Ds#E#%Ds#H#%Ds#K#%Ds#N#%Ds#U#%Ds#W#%Ds#}#%Ds#Z#%Ds#\#$s$r$#########'#(s$Ks(-)#s$$s$M$*######'#(s$Rs(/)#s$+s$T$s%'####$#######'#(s$\s(2)#s$5s$^#<########'#(s$ds(4)#s$=s$e$s%6######'#(s$ks(6)#s$Ds$l$s%B######$#$#######'#(s$ws(:$s$e$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#'#+#)s#@s%5##s%B$#######,#(s%J#)#s%9s$k#*######,#(s%Q#)#s%@s$r$s*d$#$#######,#(s%Z#)#s%Is$i#*######,#(s%a#)#s%Ps%h#2$#######,#(s%i#)#s%Xs%k#*######,#(s%p#)#s%_s%q$s+&$#######,#(s%x##s&I$#$###$#$###$###$###$#$#####'#+s)Q)4s%x##s&4####,#(s&3#*s%o)$s&###;,#(s&8#*s%u)$s&(#$s+P######,#(s&@#*s%~)$s&0##s+U,#(s&E#*s&()$s&5#,s#-(s&I#*s&5)$s&9#,s+^(s&M#*s&:)$s&=#,s+c(s&Q#$7########$#$#######$#########'#+s)s)4s&Q#'s+vVS%s&e##s$Y$#$#$#$#$#$#$#################################################'#'s$ZWS&s',$#$s'{$###########,#(s'5#'%VL$##s#S####################'#$s(7$###########################'#VMs*Xs*H$s'g########################'##s(T##$#########################'#VMs*Ys*J#s(?$#$###$#####$#$#$#########'#(s(=s*N*s'y)$s's#(s(@s,,$s$Z######'#VL(#$s#)$#####$###$#########'#(s(Ss*X#s(x$#$#$#$#$###$#####'#+s*[)/s(8#$s#z$#####$###$#$#$#$#######'#(s(os*Z#s&L############################'#+#)4s(Y#$s$@####$#$#####$###$#$#######'#(s)5s*m)#s(qs(@'s%D+#)s#Ws(q#$s'C$#######'#(s)@s*r+s-s)$s(v#$s'M##$#######'#(s)Js*u)#s)#s)L$+########'#(s)Rs*w)#s)+s)S#s'B$#######'#(s)Zs*y+s*%)$s)8#$s'I####'#(s)as*|'s'.+#)%s)@##s'@####$#$#######$###########'#(s)ts*q)#s)Ms)u$*######'#(s){s*s)#s)Ts)|$s#k##$#$###$#################'#(s*0s*t)#s)es*1$*######'#(s*7s*v)#s)ls*86C%C$#%C,#%C>#%Cs#&#%Cs#8#%Cs#A#%Cs#K#%Cs#T#%Cs#^#%Cs#h#%Cs#l#%Cs#~#%Cs$D#%Cs$_#%Cs$g#%Cs$z#%Cs%>#%Cs%\#%Cs%h#%Cs&0#%Cs&3#%Cs&H#%Cs&M#%Cs&R#%Cs&X#%Cs&a#%Cs&g#%Cs&o#%Cs'-#%Cs'5#%Cs'>#%Cs'F#%Cs'P#%Cs'X#%Cs'a#%Cs(O#%Cs(W#%Cs(`#%Cs(k#%Cs(s#`S's.Ns+,s.as*cs*cs*cs*bs*Rs*Ms*Bs(}#VNI#-s+B##1EE1#E1#D1#D/EEs.hs.U/'E#s+4/'D#s*[/'D#s*W-'##-Es-is-i.s+Ns+N.$#.&#.0#.s+R#.s+S#3Es/K3s+Ws+V3s+U632.3Es-t0s+Ys+Y&&0/.$#01.&#0;.(#0s+].*#0s+^.+#0s+b.-#1Gs+b2#OS(2Gs+d#UP#-E#s/[4Gs+g&-s+h#s+g5C1#s+j5S)2$#S*4&s+m#-s+n#s+mWS+s*LS,S-VNIF-s+n$#US.FUS/F/EE$#US0F/s#2E$#US1F/s#3D$#US2F/s#4D$#-s#4#s#02<OS32Gs+}#UP#-E#s.=4Gs,$&-s,%#s,$2:9S44<s,'#-s,(#s,'.&#.)#..#.9#.=#.s#$#.s#'#m$s#-##"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0a4170 h_sr [] h_kn 34) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x109cf0 (sc_sr ho_sc) [] (sc_kn ho_sc) 66) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary :
  s_pc (fst (fst ho_rA)) = 0x109138%Z /\ snd (fst ho_rA) = [] /\ snd (fst ho_cA) = []
  /\ stdio_call 34 ho_srA ho_knA = Some ho_sc
  /\ (sc_ret ho_sc, sc_f ho_sc, sc_fd ho_sc, sc_s ho_sc, sc_l ho_sc) = (0x109cf0%Z, 0x123ef0%Z, 2%Z, ELit 0x16823%Z, ELit 31%Z)
  /\ s_pc (fst (fst ho_rC)) = 0x0a4190%Z /\ snd (fst ho_rC) = [] /\ snd (fst ho_cC) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_res); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_rA); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_cA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_srA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_knA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_fd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.sc_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_rC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.ho_cC)|] Array.empty "#0x###Y#?#=#(#T#K#,#2#/#:#D#E#3#L#I#1#6#7#8#B#C#4#M#O#P#Q#R#S#U#V#W#X#Y#Z#[#*#+#<#>#)#A#@#9#5#;#'#-#G#&#F#J#H#N#.#07#E$#F$#G&#H$#I$#J%#K&#L$#M$#N$#O&#P%#Q'#R'#S%#T&#U%#V&#W$#X$#H######$#####$#####$###$#$#######$#####'##H######$#####$#######$#####$#$#$#######'#$H##$#############$#$#$#$###$#$#$#$#$#######'#$s#.$###$###########$#######$#$#'#$s#7$#####$#$#$#$#########'#$s#J######$#$#$#$#$###$#$#$#$#########'#$-######$#########'#$(######'#$/##$#######'##5########'#$s#$######'#$B$#$#$#######'##s#q##$#$###$###$#####$###$#$#####'##s#l##$###########$#$#####$#########'##s$K######################'#$s#n$###########################'#$s$i$#####$#########################'##s$1$#########################'##s$m########$#$#########'#$;####$###$#$#########'##s$e$#$###$#######'#$s$c$###$###$#$#$#$###$#$#$#######'#$2####$#####$#####$#$#######'#$s$b$#######'##s$V##$#######'#$)########'##s$b$#######'#$s$f####'#$s%y$#$#$#$#$#$#$#$#$#$#$#$#$#$#######$#$#######$###########'#$(######'##8$###$#$###$#################'#$(######'#-Es&Vs&V5J6J-$##UQI$s''####$#############$#####$#########'#'s';$s'5$#$#####$#$#$#$#$#####'#$H####$#$#######$#########$#####$#$#$#######'#+s&|+R$s'b$###$###########$#######$#$#'#+s&~$s#,$#$#'#+#*K$s'w####$#########,#+#WS#S$-#&K&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#*#+s'J*B*B&'&#&#&#&#*#&$*#&$*#'H+#&&&#&#&#*#&$*#&$*#&$*#&$*#&$*#&$*#+s'W*s#/*s#/*s#/*s#/*s#/*s#/&+&#&#&#&#&#&#&#&#&#&#*#&$*#&$*#&$*#6D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#8#%Ds#9#%Ds#(#%Ds#y#%Ds#+#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds$%#%Ds$&#%Ds#E#%Ds#H#%Ds#K#%Ds#N#%Ds#U#%Ds#W#%Ds#}#%Ds#Z#%Ds#\#$s$t$#########'#(s$Ms(2)#s$$s$O$*######'#(s$Ts(4)#s$+s$V$s%)####$#######'#(s$^s(7)#s$5s$`#<########'#(s$fs(9)#s$=s$g$s%8######'#(s$ms(;)#s$Ds$n$s%D######$#$#######'#(s$ys(?$s$f$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#'#+#)s#@s%5##s%B$#######,#(s%K#)#s%9s$k#*######,#(s%R#)#s%@s$r$s*j$#$#######,#(s%[#)#s%Is$i#*######,#(s%b#)#s%Ps%i#2$#######,#(s%j#)#s%Xs%l#*######,#(s%q#)#s%_s%r$s+,$#######,#(s%y##s&K$#$###$#$###$###$###$#$#####'#+s)V)4s%x##s&5####,#(s&4#*s%o)$s&###;,#(s&9#*s%u)$s&(##s&R####,#(s&@#*s%})$s&/##s+Z,#(s&E#*s&')$s&4#,s#,(s&I#*s&4)$s&8#,s+c(s&M#*s&9)$s&<#,s+h(s&Q#$7########$#$#######$#########'#+s)x)4s&P#'s+{VS%s&e##s$X$#$#$#$#$#$#$#################################################'#'s$YWS&s',$#$s'|$###########,#(s'5#'%VL$##s#S####################'#$s(8$###########################'#VMs*]s*M$s'T####$#########################'##s(X##$#########################'#VMs*]s*N#s(C$#$###$#####$#$#$#########'#(s(As*R*s'{)$s'u#(s(Ds,3$s$\######'#VL(#$s#)$#####$###$#########'#(s(Ws*\#s(|$#$#$#$#$###$#####'#+s*_)/s(:#$s#}$#####$###$#$#$#$#######'#(s(ss*^#s&N############################'#+#)4s([#$s$C####$#$#####$###$#$#######'#(s)9s*q)#s(ss(B's):+#)s#Ws(s#$s'E$#######'#(s)Ds*v+s-{)$s(x#$s'O##$#######'#(s)Ns*y)#s)%s)P$+########'#(s)Vs*{)#s)-s)W#s'D$#######'#(s)^s*}+s*))$s):#$s'K####'#(s)es+$'s'0+#)%s)B##s'B####$#$#######$###########'#(s)xs*u)#s)Os)y$*######'#(s*#s*w)#s)Vs*$$s#k##$#$###$#################'#(s*4s*x)#s)gs*5$*######'#(s*;s*z)#s)ns*<6C%C$#%C,#%C>#%Cs#&#%Cs#8#%Cs#A#%Cs#K#%Cs#T#%Cs#^#%Cs#h#%Cs#l#%Cs#~#%Cs$D#%Cs$_#%Cs$g#%Cs$z#%Cs%A#%Cs%_#%Cs%k#%Cs&3#%Cs&6#%Cs&K#%Cs&P#%Cs&U#%Cs&[#%Cs&c#%Cs&i#%Cs&q#%Cs'/#%Cs'7#%Cs'@#%Cs'H#%Cs'R#%Cs'Z#%Cs'c#%Cs(Q#%Cs(Y#%Cs(b#%Cs(m#%Cs(u#`S's.Us+0s.hs*gs*gs*gs*fs*Us*Ps*Ds)##VNI#-s+F##1EE1#E1#D1#D/EEs.os.\/'E#s+8/'D#s*^/'D#s*Z-'##-Es-qs-q.s+Rs+R.$#.&#.0#.s+V#.s+W#3Es/S3s+[s+Z3s+Y632.3Es-|0s+]s+]&&0/.$#01.&#0;.(#0s+a.*#0s+b.+#0s+f.-#1Gs+f2#OS(2Gs+h#UP#-E#s/c4Gs+k&-s+l#s+k5C1#s+n5S)2$#S*4&s+q#-s+r#s+qWS+s*NS,S-VNIF-s+r$#US.FUS/F/EE$#US0F/s#2E$#US1F/s#3D$#US2F/s#4D$#-s#4#s#02<OS32Gs,%#UP#-E#s.E4Gs,(&-s,)#s,(2:9S44<s,+#-s,,#s,+.&#.)#..#.9#.=#.s#$#.s#'#m$s#-##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x23131) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x16823) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_len : length msg_short = 31%nat. Proof. reflexivity. Qed.
Lemma msg_overrun_len : length msg_overrun = 31%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : list sregion :=
  [(SA (EVar 0) (- HF_FR), HF_FR); (SA (ELit 0) 0x123ef0, 232)]%Z.

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
    [(Z_to_bv 64 (bv_unsigned sp0 - HF_FR), HF_FR); (Z_to_bv 64 0x123ef0, 232%Z)].

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
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 0x109cf0 (sc_sr sc) (sc_kn sc) 66 (fst (fst rC)) (snd (fst rC)) (snd rC)
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
    (* LPS 75d69e00: the channel-reader premise, after fd_lookup. *)
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x0a4154) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x0a4190) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof.
    (* LPS 75d69e00: as As/AsHdrErr.v - the recording was one argument short of the reader
       premise; the proof is this file's own plain [Ltac hf_sound], which now takes it. *)
    unfold W.
    hf_sound 0x0a4154%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
  Qed.

  Theorem ho_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x0a4170) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x0a4190) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof.
    unfold W.
    hf_sound 0x0a4170%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
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
    Himg  : forall i, (0x10000 <= i < 0x4e000)%Z -> mem (Z_to_bv 64 i) = None;
    Hgot  : forall i, (0x119000 <= i < 0x121000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem hf_cells;
    Hcan  : rdn RSEGS mem (Z_to_bv 64 0x681830) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Hcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x123ef0, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x123ef0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x123ef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x123f00) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x123f10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x681ef8));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x123f18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x681ef8));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x123f28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x681ef8));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x123f78) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x123f7c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x681830) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
    [sp; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma h_ev_junk : forall regs sp can i, (2 <= i < 34)%nat ->
    ev (ENV (h_vals regs sp can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Peano.lt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.length); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.eq_Transitive); constr:(@Corelib.Lists.ListDef.nth); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.junk_vals); constr:(@Corelib.Classes.Morphisms.reflexive_proper); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive); constr:(@Corelib.Classes.RelationClasses.eq_Reflexive); constr:(@Corelib.Classes.RelationClasses.symmetry); constr:(@Corelib.Classes.RelationClasses.eq_Symmetric); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Lists.ListDef.seq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.nth_map_seq); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.Lists.List.app_nth2_plus); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.vals_ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.Env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.blobs_ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.h_vals)|] [|@y; @x; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__p2; @__arith; @z0; @H0; @cstr; @Hi0; @default; @l; @lemma; @b; @i; @__p3; @H; @Hi; @can; @sp; @regs|] "#'7#+$<#4#h#5#@#$#i#%#g###B#&#'#+#s#W#(#)#2#:#O#9#8#7#N#R#[#p#0#3#I#J#K#G#H#Q#P#M#S#T#o#t#j#v#y#z#;$&$6$2$8$9#<#.#F#E#^#]#\#b#c#a#d#f#q#u#w#{#|#x$%$-$+$/$.$)$$$4$3#*$5$7$;$:$=$<#6#V#A$##1#L#n#m#?#D#>#r#k#C#U#Z#Y#e$1#/#=#X#_#`#l#~#}$($'$*$,$0L#8$#V&#x%#,$#:%#6%#y&#z%#{%#|$#}%#~'$#*$$%$%/$&%$'%$(*#Q'#5%$)$#V$$*%$+%$,&$-+$.%$/$#9%$0%$1%$2$$3$$4)$5%$6%$7$$8&$9'$:'$;%,S$US.#>#,%,#,#,#,#>#US/#VSG*##S'##?#K#$##############################################################6K#%s#$#@Gs#&####$E#G&G7s#7*$#0F#7S$2$#2#$$C#)8E8C&K$C-#$EGKVSHGKWSI%$#j#$E#j#%E#2K/j#%C#*GK0F#j#&C#j#'C#-C9-C9fS0EEECCCS1LLL%S2G;$s#C:#`S3EECCS(LL*S4@9#`S3EECCS(LL+S4@8#1EC6L5.@8#G>'?s#GG6Gs#'%$#'ABUS.s#S,#7#(s#&#%'#1ECS)LS*S5s#Ps#'0Gs#(1-C&1ECS%LS&S+Gs#*3s#1'#ZS6.-+'%#XS7-'#KUS8I&I'F#&M*#s#0VS9F#(F$0F%$C#&%%#'(F$C&F%$#9&#&N*#s#;0F#:Cs#f:Cs#h:CS';C$#;C&#A#S,:Cs#jUSJS$VSKC#WSLC#+;C#*;C'#A#S,A%S,BQ)Q$#)Q&#)Q.#CQVSMCIUSNCXSOC$G#USPCUSQCD#JDDHNVS:CS$VS:Cs$03Cs#XWSRC$#.C&S-#/)JDDH#P4*JDDH)#3CF.C'S;#/-JDDH#P.C,S-%//JDDH#P40JDDH%#[S<1JDDH)#USSD.C/S;0/4JDDH#PD5JDDHR46JDDH$#3Cs#fWS=C6#WS=C#$.C#S-7/;JDDH#P<<JDDH(,#<=JDDH.-#VST>H-S>S?VSUKI$S>#S?m$%#WSVCFGXSWKI$#l#(*)#l#)s#(s#'#l#*s#-s#,#j#+C#j#,C#j#-O#j#.O#*Gs#~$CK#%I#'%F$CKF%$#9&#'s$)I%#N2Is$(2#s$)$C#Mk##&#k##)#k#+C#k#,C#k#-O#k#.O#&S#(#s#o*$s$6(F#ZK%#&GINl#/:(#l#0s#\C#l#1s#hs#`#l#2s#ns#l#l#3s#ps#u#XS@s$@s$8s$##+s$lIBs$l)s$m$#)s$nM#Es$o#F#s$I$E#Gm#*#+s$tM)s$t#*)s$uN#Es$v#@Is$tF$#$E#I8s$zUSXs${+s$}N)s$}#3)s$~R#GS#Hs%$$#+s%&F5s%&M$#Es%''@Ms%%F$#5s%*#('Cs%+k#4s%,s%,k#5$#k#'E#8&Is%0s%044I('$#IE's$[#USYs%3Js%4s%48#J,+'#JE+'#WSZ+'#USAs%8US[EZS\Es$c#3MKK29Ks%<9aS]1-('M6%;;$::#&8+s%F#=S##Ks%A#]S^s%Bs#&s#%>:'$$#j#6s#(#GR5s%Es#,#B$s%FK(j#7s%G#&s#/+s%P#=R#-s%K#+s%Ss$s=S##j#8E#VS_S's%-XS`Es%P$#5s%Qs#8#s#.6s#9s%0*s$Xs%'0F#7s%X($#-Cs$\fS0EEECCCS1LLLs$sS2Is$]#s%Us%,s$q-C&1ECS%LS&S+s#A($s%8'#?s%XI6Is%8%$#'s%2s$c(s$ds$m%$#1ECS)LS*S5s%^s%5s$zIs$f,1ECS%LS&S+Is$g-s%>s$ps$lZS6*)'&$#XS7)&#GUS8M'Fs$iVS9Fs$^(Fs$_$Cs$_s$`%$#'s$bF$Cs$bF%$#9&#&R*#s%D0F#)Qs$bs$Y4s$QJDDHs$>s$D[S<s$RJDDHs$J#Ds$SJDDHS#3Cs%(.Cs$RSB#/s$VJDDH#P4s$WJDDH&#3Cs#'.Cs$WSB#/s$ZJDDH#P<s$[JDDH&s$K#<s$\JDDH,s$L#l#(#s$As$;l#)s$`s$_#l#*1s$d#j#+C#j#,C#j#-O#j#.O#j#9O#%Ms$79s$:#(Is%;%R#(Is#8k##$#k##'#k#+C#k#,C#k#-O#k#.O#k#9O#&Sa's%h#*$s%i'#F(F$[K&$#'GINl#/5)#l#0s#+C#l#1s#6s#/#l#2s#9s#8#l#3s#;s#?#XS@s#Ns#Js#F#ZSbs&Cs#Ss$*s%}s#|#ZSCs&Ds#Xs#[s#Ws#Q#$s&Es#^s#Ym#$#Hs&Gs$0s#a5s&Hs$.#s$%YScs&Is$2s#cs$&s$0ZSCs&Js#cs#a&$#Vs#fK#l#:s$8s$9#GNHs&Ns$>#VSD#G&s&)+s&X#=N#$s&S&#m#*#USD)>s&[US/#C#B#USd#VSe(#VSE#G$s&]#-m#,#WSfNMIUSg#VSE#G$s&b#2m#'#j#;s&>#j#8E#j#<C#j#=s&g#j#>s&g##"). Qed.
Scheme kc__2 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.hfH Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

  Lemma h_regs_ok : forall regs mem sp can, hfH regs mem sp can ->
    regs_ok (ENV (h_vals regs sp can)) h_sr regs.
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.hfH); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.regs_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.h_vals); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.h_sr); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ASP_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ASP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.stk_ok); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.HF_FR); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.cells_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hf_cells); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.regs_ok_by_idx); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@kc__3); constr:(@Corelib.Lists.ListDef.nth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.allregs32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.edenot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SeqExec.getr_zero); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Nat.sub); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.h_ev_junk); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.X)|] [|@i; @Hi; @n; @b; @__ff; @__varmap; @__wit; @__arith; @x; @Ha; @__x1; @__p1; @__sat66; @__sat67; @__sat68; @cstr; @Hi0; @Hcan65; @Hcan0; @Hcells0; @Hgot0; @Himg0; @Hstk0; @HspHi0; @HspLo0; @Hsp17; @H3; @Hcan64; @Hcan; @Hcells; @Hgot; @Himg; @Hstk; @HspHi; @HspLo; @Hsp16; @H2; @PH; @can; @sp; @mem; @regs|] "#>8$)%.$3$W$s##$a$t$r$9$[$]$y$>$Q$X$J%($g$C$k$x$z$j$B#$#%#&#D#F#H#J#L#N#P#R#T#V#X#Z#\#^#`#b#d#f#h#j#l#n#p#r#t#v#x#z#'#>#A#@#B#E#G#I#K#M#O#Q#S#U#W#Y#[#]#_#a#c#e#g#i#k#m#o#q#s#u#w#y#($R#C$G#*#-#7#?#{#|$0#8#;#=#}$2$4$D$E$F#)$H$L#.$M$N$O$P#,$T$S#1#3#<$m$}$~%,%.%0$)$($,$6$?$U#/#0#2#4#6#9$^$_$l$n$o$q${%#%$$|%%%)#~%*$$%+%-%/%1%3$&$%$V#+$5$Z$;$:$/$8$7$\%&$I$c$v$u$i$=$K$w$<%'%2$Y$d$b$h$p$f$e$`$.$A$-$1$@I#/$$j'$k%$l&#0%$m$$n&$o$$p%$q%$r%$s%$t'$u*$v/#4%$w$#1%$x%$y%$z&#'$${/$|&$}'$~%%#%#3%%$)%%*%&'%'(%()%)$%*%%+$%,$%-%(SsD#F#(%(#(#(#(#F#G#VT7*#F)G#USx#k##'#XSyS,S+S*FXSySIS,S+S*)SiS,S+*#WT8#JSij##&#37VT96#m$N#78%#%SI#&3#S+E5S,39H$#&C#S)E9SI2Sz#E;Si2#S{XS|SlSmS}S~(?(#(#(#(#(#(#(#(#(#3#(Ss(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#3#D2D#D#(#(#(#(#(#(#(#(#(#(#(#(#(#3#DBD#(#(#D#(#(#(#(#(#(#(#(#(#(#(#(#3#(s#%(#(#(#D#(#(#(#(#(#(#(#(#(#(#(#(#3#DSs(#D#(#(#(#(#(#(#D#D#(#(#(#(#(#D#D#(#(#(#(#3#2s#OFDs$0D#D#(#(#(#(#(#(#(#(#(#(#(#(#(#3#4Fs#P-5#5s$>S*USn#UT#s$<&s$<$#k##'#k#$C#Ds$HD#(#(#D#(#(#(#(#(#(#(#(#(#(#(#(#3#2s#XF(s#.(#(#(#D#(#(#(#(#(#(#(#(#(#(#(#(#3#4Fs#Y-6#UT$s#/&s$g#s#.k##%#k#$C#VT%SnT&UT's$lUSx#DSs(#(#D#D#(#(#(#(#D#D#(#D#(#(#D#D#D#(#(#(#(#3#5s%-s#b#Sj##############XT(SlT$+#5s%7T)VT*%#VT+s#'#&s#'&#2S)Sn3s%=VT:s%0#4Sn#-&#7s%Fs%3N%T,#&s%A#T;Es%CT<H#s%0&C#S)Es%FT,2Sz#Es%HT=2#S{XS|SlT>T-S~USos#k&s%G#s#jk##s#n#k#$C#USts#o&s%K#s#nk##s#E#k#$C#VT%SoT&XT(SlSts#)A5s%UT?VT*s###VT+s#E#&s#E&#2S)So4So?-$#)SuT@St*##s#+##############################################'F#Gs%}7s%~S)N$$S*K#%Sp#)SpSvT.*#UTAS)$LS*J#+%#&s&#(#k#%-#j#&D#'Sj0UTBSJ$0SjK/%SJ#)SJT.Su*#$LSjJ.+$#&s&.'#m#*#j#%,##F'#<#S*$<#K;%SK#)SKSpSJ*#$L'J:+$#&s&:'#k#%+#j#&D#'s#ns#'=s#ms#n8#5s&G#%SL#3Ss7s&J#N%SK#&s&E#Fj#'s&F#.s&G()SLSJSv*#<#s#y>s#{s#z#s#6##'s#}#-&#3s$=2s&E#(s$m3#4&#-&#.Cs&J.C)1DCS#GS$S(s$,s&L$s$+*#.C(1DCPGQS%s$-,%/)#?2/,)%#UTCT/UT'T/UTDCUTECUTFC6Cs&U6C4/C$S&#0&IEEH#M6C4/C&S'#0)IEEH#M@*IEEH&#VTG+H.T0T1VTHFS+&T0#T1m$%#WTICS)S*XTJFS+$#l#(*)#l#)54#l#*87#l#+#@FAs#'A;#BSLSJSvs$H#Cs&vs#7s#2s#1s#.#$s#_s$LKs#^%SL#$Ls$NJs#[+s#3#&s&{%#m#(#j#%s#B##s#O'#s#i#s#O$s#i#Ks#h%Sk#)SkSKSL*#$L'Js#g+$#&s'+'#k#%+#j#&D#'s$^s#t%SMs$N)SMSLSp*#<#Sj&s'3&#m#T-#$s#ys$eKs#x%SM#$Ls$gJs#u+)#&s'9%#m#(#j#%/##<'#s$'#<$s$'#Ks$&%SN#)SNSkSM*#$L'Js$%+$#&s'E'#k#%+#j#&D#'s$ws$2=s$vs$y8#5s'R#%S-#7s'Ts#[N%SN#&s'O#Fj#'s'P#.s'Q')S-SMSK*#<#s%%>s%)s%&'s%'s#g-$#3s'`2s'M#4$s#e-$#.C&1DCS#GS$S(s%1s'Qs#es%.'#1DCPGQS%s%/($s#os#is#c?,+('$#6C*/Cs#^S&#0s#`IEEH#M/C%S's#\0s#bIEEH#M@s#cIEEH%#l#(#s#[s#Ul#)s#gs#f#l#*s#js#i#l#+#0FA51-#BS-SMSKs%<#Cs'lB>=:#$s$Us%@Ks$T%S-#$Ls%BJs$Q+?#&s'q%#m#(#j#%s#-##s#:'#s$_#s#:$s$_#Ks$^%SO#)SOSNS-*#$L'Js$]+$#&s'}'#k#%+#j#&D#'s%Rs$j=s%Qs%U8#5s(.#%S.#3s(/7s(1#N%SO#&s(,#Fj#'s(-#.s(.()S.S-Sk*#<#s%]>s%bs%^'s%_s$D-$#3s%}2s(*#4$s$B-$#.C&1DCS#GS$S(s%js(.s$Bs%f'#1DCPGQS%s%g($s$Ls$Fs$@?,+('$#6C*/Cs$;S&#0s$=IEEH#M/C%S's$90s$?IEEH#M@s$@IEEH%#l#(#s$8s$2l#)s$Ds$C#l#*s$Gs$F#l#+#0FA51-#BS.S-Sks%t#Cs(Is##>=:#$s%2s%xKs%1%S.#$Ls%zJs%.+?#&s(N%#m#(#j#%s#.##s#;'#s%<#s#;$s%<#Ks%;%SP#)SPSOS.*#$L'Js%:+$#&s(Z'#k#%+#j#&D#'s&.s%G=s&-s&28#5s(g#%S/#7s(is#hN%SP#&s(d#Fj#'s(e#.s(f')S/S.SN*#<#s&8>s&>s&9's&:s$|-$#Ds&Z3#2s(c#4$s${-$#.C&1DCS#GS$S(s&Gs(gs${s&B'#1DCPGQS%s&C($s%)s%#s$y?-,('$#6C*/Cs$tS&#0s$vIEEH#M/C%S's$r0s$xIEEH#M@s$yIEEH%#l#(#s$qs$kl#)s$}s$|#l#*s%$s%##l#+#0FA61-#BS/S.SNs&P#Cs)&s##?>;#$s%ks&TKs%j%S/#$Ls&VJs%g+@#&s)+%#m#(#j#%s#.##s#;'#s%u#s#;$s%u#Ks%t%SQ#)SQSPS/*#$L'Js%s+$#&s)7'#k#%+#j#&D#'s&fs&$=s&es&k8#5s)D#%S0#7s)Fs#hN%SQ#&s)A#Fj#'s)B#.s)C')S0S/SO*#<#s&p>s&ws&q's&rs%Y-$#3s)O2s)?#4$s%W-$#.C&1DCS#GS$S(s'#s)Cs%Ws&y'#1DCPGQS%s&z($s%as%[s%U?,+('$#6C*/Cs%PS&#0s%RIEEH#M/C%S's%N0s%TIEEH#M@s%UIEEH%#l#(#s%Ms%Gl#)s%Ys%X#l#*s%\s%[#l#+#0FA51-#BS0S/SOs'+#Cs)^B>=:#$s&Gs'/Ks&F%S0#$Ls'1Js&C+?#&s)c%#m#(#j#%s#-##s#:'#s&Q#s#:$s&Q#Ks&P%SR#)SRSQS0*#$L'Js&O+$#&s)o'#k#%+#j#&D#'s'As&\=s&ts'G8#5s)|#%S1#7s)~s#gN%SR#&s)y#Fj#'s)z#.s){')S1S0SP*#<#s'#>s'Ss'$'s'%s&5-$#3s(Z2s)w#4$s&3-$#.C&1DCS#GS$S(s'[s){s&3s','#1DCPGQS%s'-($s&=s&7s&1?,+('$#6C*/Cs&,S&#0s&.IEEH#M/C%S's&*0s&0IEEH#M@s&1IEEH%#l#(#s&)s&#l#)s&5s&4#l#*s&8s&7#l#+#0FA51-#BS1S0SPs':#Cs*:B>=:#$s'#s'fKs&~%S1#$Ls'hJs&{+?#&s*?%#m#(#j#%s#-##s#:'#s'-#s#:$s'-#Ks',%SS#)SSSRS1*#$L'Js'++$#&s*K'#k#%+#j#&D#'s'xs'8=s'Os(#8#5s*X#%S2#7s*Zs#gN%SS#&s*U#Fj#'s*V#.s*W')S2S1SQ*#<#s'Z>s(/s'['s'\s&m-$#(s*f3#2s*T#4$s&l-$#.C&1DCS#GS$S(s(8s*Xs&ls'd'#1DCPGQS%s'e($s&vs&ps&j?-,('$#6C*/Cs&eS&#0s&gIEEH#M/C%S's&c0s&iIEEH#M@s&jIEEH%#l#(#s&bs&\l#)s&ns&m#l#*s&qs&p#l#+#0FA61-#BS2S1SQs'r#Cs*ss##?>;#$s'\s(BKs'[%S2#$Ls(DJs'X+@#&s*x%#m#(#j#%s#.##s#;'#s'f#s#;$s'f#Ks'e%ST#)STSSS2*#$L'Js'd+$#&s+('#k#%+#j#&D#'s(,s'q=s(+s(\8#5s+5#%S3#7s+7s#hN%ST#&s+2#Fj#'s+3#.s+4')S3S2SR*#<#s(6>s(hs(7's(8s'J-$#Ds+C3#2s+1#4$s'I-$#.C&1DCS#GS$S(s(qs+5s'Is(@'#1DCPGQS%s(A($s'Ss'Ms'G?-,('$#6C*/Cs'BS&#0s'DIEEH#M/C%S's'@0s'FIEEH#M@s'GIEEH%#l#(#s'?s'9l#)s'Ks'J#l#*s'Ns'M#l#+#0FA61-#BS3S2SRs(N#Cs+Ps##?>;#$s(9s(RKs(8%S3#$Ls(TJs(5+@#&s+U%#m#(#j#%s#.##s#;'#s(C#s#;$s(C#Ks(B%SU#)SUSTS3*#$L'Js(A+$#&s+a'#k#%+#j#&D#'s(ds(N=s(cs)98#5s+n#%S4#7s+ps#hN%SU#&s+k#Fj#'s+l#.s+m')S4S3SS*#<#s(n>s)Es(o's(ps('-$#3s)_2s+i#4$s(%-$#.C&1DCS#GS$S(s)Ms+ms(%s(w'#1DCPGQS%s(x($s(/s()s(#?,+('$#6C*/Cs'zS&#0s'|IEEH#M/C%S's'x0s'~IEEH#M@s(#IEEH%#l#(#s'ws'ql#)s('s(&#l#*s(*s()#l#+#0FA51-#BS4S3SSs))#Cs,,B>=:#$s(qs)-Ks(p%S4#$Ls)/Js(m+?#&s,1%#m#(#j#%s#-##s#:'#s({#s#:$s({#Ks(z%SV#)SVSUS4*#$L'Js(y+$#&s,='#k#%+#j#&D#'s)?s)*=s)>s)q8#5s,J#%S5#7s,Ls#gN%SV#&s,G#Fj#'s,H#.s,I')S5S4ST*#<#s)I>s)}s)J's)Ks(_-$#Ds*<3#2s,F#4$s(^-$#.C&1DCS#GS$S(s**s,Js(^s)S'#1DCPGQS%s)T($s(hs(bs(\?-,('$#6C*/Cs(WS&#0s(YIEEH#M/C%S's(U0s([IEEH#M@s(\IEEH%#l#(#s(Ts(Nl#)s(`s(_#l#*s(cs(b#l#+#0FA61-#BS5S4STs)a#Cs,es##?>;#$s)Ns)eKs)M%S5#$Ls)gJs)J+@#&s,j%#m#(#j#%s#.##s#;'#s)X#s#;$s)X#Ks)W%SW#)SWSVS5*#$L'Js)V+$#&s,v'#k#%+#j#&D#'s)ws)c=s)vs*N8#5s-'#%S6#7s-)s#hN%SW#&s-$#Fj#'s-%#.s-&')S6S5SU*#<#s*%>s*Zs*&'s*'s)<-$#(s&z3#2s-##4$s);-$#.C&1DCS#GS$S(s*cs-'s);s*/'#1DCPGQS%s*0($s)Es)?s)9?-,('$#6C*/Cs)4S&#0s)6IEEH#M/C%S's)20s)8IEEH#M@s)9IEEH%#l#(#s)1s)+l#)s)=s)<#l#*s)@s)?#l#+#0FA61-#BS6S5SUs*=#Cs-Bs##?>;#$s*+s*AKs**%S6#$Ls*CJs*'+@#&s-G%#m#(#j#%s#.##s#;'#s*5#s#;$s*5#Ks*4%SX#)SXSWS6*#$L'Js*3+$#&s-S'#k#%+#j#&D#'s*Ss*@=s*Rs++8#5s-`#%S7#7s-bs#hN%SX#&s-]#Fj#'s-^#.s-_')S7S6SV*#<#s*]>s+7s*^'s*_s)u-$#Ds'W3#2s-\#4$s)t-$#.C&1DCS#GS$S(s+@s-`s)ts*g'#1DCPGQS%s*h($s)~s)xs)r?-,('$#6C*/Cs)mS&#0s)oIEEH#M/C%S's)k0s)qIEEH#M@s)rIEEH%#l#(#s)js)dl#)s)vs)u#l#*s)ys)x#l#+#0FA61-#BS7S6SVs*u#Cs-{s##?>;#$s*ds*yKs*c%S7#$Ls*{Js*`+@#&s.$%#m#(#j#%s#.##s#;'#s*n#s#;$s*n#Ks*m%SY#)SYSXS7*#$L'Js*l+$#&s.0'#k#%+#j#&D#'s+/s*y=s+.s+d8#5s.=#%S8#7s.?s#hN%SY#&s.:#Fj#'s.;#.s.<')S8S7SW*#<#s+9>s+ps+:'s+;s*R-$#2s.7s.04s.1s*O-$#.Cs.31DCS#GS$S(s+ws.;s*Os+As.4#1DCPGQS%s+Bs.5$s*Ys*Ss*M?+*('$#6Cs.7/Cs*HS&#0s*JIEEH#M/C%S's*F0s*LIEEH#M@s*MIEEH%#l#(#s*Es*?l#)s*Qs*P#l#*s*Ts*S#l#+#0FA41-#BS8S7SWs+O#Cs.VA=<9#$s+?s+SKs+>%S8#$Ls+UJs+;+>#&s.[%#m#(#j#%s#,##s#9'#s+I#s#9$s+I#Ks+H%SZ#)SZSYS8*#$L'Js+G+$#&s.g'#k#%+#j#&D#'s+es+T=s+ds,?8#5s.t#%S9#7s.vs#fN%SZ#&s.q#Fj#'s.r#.s.s')S9S8SX*#<#s+o>s,Ks+p's+qs+--$#3s-92s.o#4$s++-$#.C&1DCS#GS$S(s,Ss.ss++s+x'#1DCPGQS%s+y($s+5s+/s+)?,+('$#6C*/Cs+$S&#0s+&IEEH#M/C%S's*~0s+(IEEH#M@s+)IEEH%#l#(#s*}s*wl#)s+-s+,#l#*s+0s+/#l#+#0FA51-#BS9S8SXs,*#Cs/2B>=:#$s+ws,.Ks+v%S9#$Ls,0Js+s+?#&s/7%#m#(#j#%s#-##s#:'#s,%#s#:$s,%#Ks,$%S[#)S[SZS9*#$L'Js,#+$#&s/C'#k#%+#j#&D#'s,@s,0=s,?s,w8#5s/P#%S:#7s/Rs/8N%S[#&s/M#Fj#'s/N#.s/O')S:S9SY*#<#s,J>s-'s,K's,Ls+e-$#3s-^2s/K#4$s+c-$#.C&1DCS#GS$S(s-/s/Os+cs,S'#1DCPGQS%s,T($s+ms+gs+a?,+('$#6C*/Cs+\S&#0s+^IEEH#M/C%S's+Z0s+`IEEH#M@s+aIEEH%#l#(#s+Ys+Sl#)s+es+d#l#*s+hs+g#l#+#0FA51-#BS:S9SYs,a#Cs/jB>=:#$s,Ss,eKs,R%S:#$Ls,gJs,O+?#&s/o%#m#(#j#%s#-##s#:'#s,]#s#:$s,]#Ks,\%S\#)S\S[S:*#$L'Js,[+$#&s/{'#k#%+#j#&D#'s,ws,h=s,vs-S8#5s0,#%S;#7s0.s#gN%S\#&s0)#Fj#'s0*#.s0+')S;S:SZ*#<#s-%>s-_s-&'s-'s,A-$#3s.e2s0'#4$s,?-$#.C&1DCS#GS$S(s-gs0+s,?s-.'#1DCPGQS%s-/($s,Is,Cs,=?,+('$#6C*/Cs,8S&#0s,:IEEH#M/C%S's,60s,<IEEH#M@s,=IEEH%#l#(#s,5s,/l#)s,As,@#l#*s,Ds,C#l#+#0FA51-#BS;S:SZs-<#Cs0FB>=:#$s-/s-@Ks-.%S;#$Ls-BJs-++?#&s0K%#m#(#j#%s#-##s#:'#s-9#s#:$s-9#Ks-8%S]#)S]S\S;*#$L'Js-7+$#&s0W'#k#%+#j#&D#'s-Rs-D=s-Qs./8#5s0d#%S<#7s0fs#gN%S]#&s0a#Fj#'s0b#.s0c')S<S;S[*#<#s-\>s.;s-]'s-^s,y-$#(s(j3#2s0`#4$s,x-$#.C&1DCS#GS$S(s.Ds0ds,xs-f'#1DCPGQS%s-g($s-&s,|s,v?-,('$#6C*/Cs,qS&#0s,sIEEH#M/C%S's,o0s,uIEEH#M@s,vIEEH%#l#(#s,ns,hl#)s,zs,y#l#*s,}s,|#l#+#0FA61-#BS<S;S[s-t#Cs1#s##?>;#$s-hs-xKs-g%S<#$Ls-zJs-d+@#&s1(%#m#(#j#%s#.##s#;'#s-r#s#;$s-r#Ks-q%S^#)S^S]S<*#$L'Js-p+$#&s14'#k#%+#j#&D#'s..s-}=s.-s.h8#5s1A#%S=#7s1Cs#hN%S^#&s1>#Fj#'s1?#.s1@')S=S<S\*#<#s.8>s.ts.9's.:s-V-$#Ds)G3#2s1=#4$s-U-$#.C&1DCS#GS$S(s.}s1As-Us.B'#1DCPGQS%s.C($s-_s-Ys-S?-,('$#6C*/Cs-NS&#0s-PIEEH#M/C%S's-L0s-RIEEH#M@s-SIEEH%#l#(#s-Ks-El#)s-Ws-V#l#*s-Zs-Y#l#+#0FA61-#BS=S<S\s.P#Cs1\s##?>;#$s.Es.TKs.D%S=#$Ls.VJs.A+@#&s1a%#m#(#j#%s#.##s#;'#s.O#s#;$s.O#Ks.N%S_#)S_S^S=*#$L'Js.M+$#&s1m'#k#%+#j#&D#'s.fs.Z=s.es/E8#5s1z#%S>#7s1|s#hN%S_#&s1w#Fj#'s1x#.s1y')S>S=S]*#<#s.p>s/Qs.q's.rs.3-$#(s)G3#2s1v#4$s.2-$#.C&1DCS#GS$S(s/Zs1zs.2s.z'#1DCPGQS%s.{($s.<s.6s.0?-,('$#6C*/Cs.+S&#0s.-IEEH#M/C%S's.)0s./IEEH#M@s.0IEEH%#l#(#s.(s-~l#)s.4s.3#l#*s.7s.6#l#+#0FA61-#BS>S=S]s/,#Cs29s##?>;#$s.~s/0Ks.}%S>#$Ls/2Js.z+@#&s2>%#m#(#j#%s#.##s#;'#s/,#s#;$s/,#Ks/+%S`#)S`S_S>*#$L'Js/*+$#&s2J'#k#%+#j#&D#'s/Bs/7=s/As/~8#5s2W#%S?#7s2Ys#hN%S`#&s2T#Fj#'s2U#.s2V')S?S>S^*#<#s/L>s0.s/M's/Ns.l-$#Ds*$3#2s2S#4$s.k-$#.C&1DCS#GS$S(s07s2Ws.ks/V'#1DCPGQS%s/W($s.us.os.i?-,('$#6C*/Cs.dS&#0s.fIEEH#M/C%S's.b0s.hIEEH#M@s.iIEEH%#l#(#s.as.[l#)s.ms.l#l#*s.ps.o#l#+#0FA61-#BS?S>S^s/d#Cs2rs##?>;#$s/[s/hKs/Z%S?#$Ls/jJs/W+@#&s2w%#m#(#j#%s#.##s#;'#s/e#s#;$s/e#Ks/d%Sa#)SaS`S?*#$L'Js/c+$#&s3''#k#%+#j#&D#'s/zs/p=s/ys0[8#5s34#%S@#7s36s#hN%Sa#&s31#Fj#'s32#.s33')S@S?S_*#<#s0(>s0gs0)'s0*s/I-$#(s1%3#2s30#4$s/H-$#.C&1DCS#GS$S(s0ps34s/Hs02'#1DCPGQS%s03($s/Rs/Ls/F?-,('$#6C*/Cs/AS&#0s/CIEEH#M/C%S's/?0s/EIEEH#M@s/FIEEH%#l#(#s/>s/8l#)s/Js/I#l#*s/Ms/L#l#+#0FA61-#BS@S?S_s0@#Cs3Os##?>;#$s08s0DKs07%S@#$Ls0FJs04+@#&s3T%#m#(#j#%s#.##s#;'#s0B#s#;$s0B#Ks0A%Sb#)SbSaS@*#$L'Js0@+$#&s3`'#k#%+#j#&D#'s0Vs0M=s0Us188#5s3m#%SA#7s3os#hN%Sb#&s3j#Fj#'s3k#.s3l')SAS@S`*#<#s0`>s1Ds0a's0bs0&-$#3s1]2s3h#4$s0$-$#.C&1DCS#GS$S(s1Ls3ls0$s0i'#1DCPGQS%s0j($s0.s0(s/~?,+('$#6C*/Cs/yS&#0s/{IEEH#M/C%S's/w0s/}IEEH#M@s/~IEEH%#l#(#s/vs/pl#)s0&s0%#l#*s0)s0(#l#+#0FA51-#BSAS@S`s0w#Cs4+B>=:#$s0ps0{Ks0o%SA#$Ls0}Js0l+?#&s40%#m#(#j#%s#-##s#:'#s0z#s#:$s0z#Ks0y%Sc#)ScSbSA*#$L'Js0x+$#&s4<'#k#%+#j#&D#'s11s1)=s10s1p8#5s4I#%SB#7s4Ks#gN%Sc#&s4F#Fj#'s4G#.s4H')SBSASa*#<#s1;>s1|s1<'s1=s0^-$#(s*]3#2s4E#4$s0]-$#.C&1DCS#GS$S(s2)s4Is0]s1E'#1DCPGQS%s1F($s0gs0as0[?-,('$#6C*/Cs0VS&#0s0XIEEH#M/C%S's0T0s0ZIEEH#M@s0[IEEH%#l#(#s0Ss0Ml#)s0_s0^#l#*s0bs0a#l#+#0FA61-#BSBSASas1S#Cs4ds##?>;#$s1Ms1WKs1L%SB#$Ls1YJs1I+@#&s4i%#m#(#j#%s#.##s#;'#s1W#s#;$s1W#Ks1V%Sd#)SdScSB*#$L'Js1U+$#&s4u'#k#%+#j#&D#'s1is1b=s1hs2M8#5s5&#%SC#7s5(s#hN%Sd#&s5##Fj#'s5$#.s5%')SCSBSb*#<#s1s>s2Ys1t's1us1;-$#Ds+:3#2s4~#4$s1:-$#.C&1DCS#GS$S(s2bs5&s1:s1}'#1DCPGQS%s1~($s1Ds1>s18?-,('$#6C*/Cs13S&#0s15IEEH#M/C%S's110s17IEEH#M@s18IEEH%#l#(#s10s1*l#)s1<s1;#l#*s1?s1>#l#+#0FA61-#BSCSBSbs2/#Cs5As##?>;#$s2*s23Ks2)%SC#$Ls25Js2&+@#&s5F%#m#(#j#%s#.##s#;'#s24#s#;$s24#Ks23%Se#)SeSdSC*#$L'Js22+$#&s5R'#k#%+#j#&D#'s2Es2?=s2Ds3*8#5s5_#%SD#7s5as#hN%Se#&s5\#Fj#'s5]#.s5^')SDSCSc*#<#s2O>s36s2P's2Qs1t-$#(s+:3#2s5[#4$s1s-$#.C&1DCS#GS$S(s3?s5_s1ss2Y'#1DCPGQS%s2Z($s1}s1ws1q?-,('$#6C*/Cs1lS&#0s1nIEEH#M/C%S's1j0s1pIEEH#M@s1qIEEH%#l#(#s1is1cl#)s1us1t#l#*s1xs1w#l#+#0FA61-#BSDSCScs2g#Cs5zs##?>;#$s2cs2kKs2b%SD#$Ls2mJs2_+@#&s6#%#m#(#j#%s#.##s#;'#s2m#s#;$s2m#Ks2l%Sf#)SfSeSD*#$L'Js2k+$#&s6/'#k#%+#j#&D#'s2}s2x=s2|s3c8#5s6<#%SE#7s6>s#hN%Sf#&s69#Fj#'s6:#.s6;')SESDSd*#<#s3+>s3os3,'s3-s2Q-$#Ds+s3#2s68#4$s2P-$#.C&1DCS#GS$S(s3xs6<s2Ps35'#1DCPGQS%s36($s2Zs2Ts2N?-,('$#6C*/Cs2IS&#0s2KIEEH#M/C%S's2G0s2MIEEH#M@s2NIEEH%#l#(#s2Fs2@l#)s2Rs2Q#l#*s2Us2T#l#+#0FA61-#BSESDSds3C#Cs6Ws##?>;#$s3@s3GKs3?%SE#$Ls3IJs3<+@#&s6\%#m#(#j#%s#.##s#;'#s3J#s#;$s3J#Ks3I%Sg#)SgSfSE*#$L'Js3H+$#&s6h'#k#%+#j#&D#'s3Ys3U=s3Xs4@8#5s6u#%SF#7s6ws#hN%Sg#&s6r#Fj#'s6s#.s6t')SFSESe*#<#s3c>s4Ls3d's3es3.-$#(s+s3#2s6q#4$s3--$#.C&1DCS#GS$S(s4Us6us3-s3m'#1DCPGQS%s3n($s37s31s3+?-,('$#6C*/Cs3&S&#0s3(IEEH#M/C%S's3$0s3*IEEH#M@s3+IEEH%#l#(#s3#s2yl#)s3/s3.#l#*s32s31#l#+#0FA61-#BSFSESes3{#Cs74s##?>;#$s3ys4#Ks3x%SF#$Ls4%Js3u+@#&s79%#m#(#j#%s#.##s#;'#s4'#s#;$s4'#Ks4&%Sh#)ShSgSF*#$L'Js4%+$#&s7E'#k#%+#j#&D#'s45s42=s44s4y8#5s7R#%SG#7s7Ts#hN%Sh#&s7O#Fj#'s7P#.s7Q')SGSFSf*#<#s4?>s5)s4@'s4As3g-$#Ds,P3#2s7N#4$s3f-$#.C&1DCS#GS$S(s52s7Rs3fs4I'#1DCPGQS%s4J($s3ps3js3d?-,('$#6C*/Cs3_S&#0s3aIEEH#M/C%S's3]0s3cIEEH#M@s3dIEEH%#l#(#s3\s3Vl#)s3hs3g#l#*s3ks3j#l#+#0FA61-#BSGSFSfs4W#Cs7ms##?>;#$s4Vs4[Ks4U%SG#$Ls4]Js4R+@#&s7r%#m#(#j#%s#.##s#;'#s4`#s#;$s4`#Ks4_%Sq#)SqShSG*#$L'Js4^+$#&s7~'#k#%+#j#&D#'s4ms4k=s4ls5V8#5s8/#%SH#7s81s#hN%Sq#&s8,#Fj#'s8-#.s8.')SHSGSg*#<#s4w>s5bs4x's4ys4D-$#3s882s8*#4$s4B-$#.C&1DCS#GS$S(s5js8.s4Bs5$'#1DCPGQS%s5%($s4Ls4Fs4@?,+('$#6C*/Cs4;S&#0s4=IEEH#M/C%S's490s4?IEEH#M@s4@IEEH%#l#(#s48s42l#)s4Ds4C#l#*s4Gs4F#l#+#0FA51-#BSHSGSgs52#Cs8IB>=:#$s52s56Ks51%SH#$Ls58Js5.+?#&s8N%#m#(#j#%s#-##s#:'#s5<#s#:$s5<#Ks5;%Sw#)SwSqSH*#$L'Js5:+$#&s8Z'#k#%+#j#&D#'s5Hs5G=s4ps628#5s8g#%Sr#7s8is#gN%Sw#&s8d#Fj#'s8e#.s8f')SrSHSh*#<#s4{>s6>s4|'s4}s4|-$#Ds8q3#2s8c#4$s4{-$#.C&1DCS#GS$S(s6Gs8gs4{s5)'#1DCPGQS%s5*($s5)s5#s4y?-,('$#6C*/Cs4tS&#0s4vIEEH#M/C%S's4r0s4xIEEH#M@s4yIEEH%#l#(#s4qs4kl#)s4}s4|#l#*s5$s5##l#+#0FA61-#BSrSHShs57#Cs9&s##?>;#$s5ks5nKs5j%Sr#$Ls5pJs5g+@#&s9+%#m#(#j#%s#.##s#;'#s5u#s#;'#s5w8S*,#s5O,#s5P,#s5Q,#s5R,#s5S,#s5T,#s5U,#s5V,#s5W,#s5X,#s5Y,#s5Z,#s5[,#s5\,#s5],#s5^,#s5_,#s5`,#s5a,#s5b,#s5c,#s5d,#s5e,#s5f,#s5g,#s5h,#s5i,#s5j,#s5k,#s5l,#s5m,#s5n4#s#|,Fs5pj#,C#U#s#&U$#U%#U&#U'#U(#U)#U*#U+#U,#U-#U.#U/#U0#U1#U2#U3#U4#U5#U6#U7#U8#U9#U:#U;#U<#U=#U>#U?#U@#UA#UB#.Cs#F9DDCCOGGs#$RS*s#G#9DDCCOGGs#%Rs6Gs#$#9DDCCOGGs#&Rs5Ws#$#9DDCCOGGs#'Rs5>s#$#9DDCCOGGs#(Rs4cs#$#9DDCCOGGs#)Rs4+s#$#9DDCCOGGs#*Rs3Os#$#9DDCCOGGs#+Rs2ts#$#9DDCCOGGs#,Rs2=s#$#9DDCCOGGs#-Rs1as#$#9DDCCOGGs#.Rs1)s#$#9DDCCOGGs#/Rs0Ns#$#9DDCCOGGs#0Rs/rs#$#9DDCCOGGs#1Rs/:s#$#9DDCCOGGs#2Rs.^s#$#9DDCCOGGs#3Rs.(s#$#9DDCCOGGs#4Rs-Ms#$#9DDCCOGGs#5Rs,rs#$#9DDCCOGGs#6Rs,;s#$#9DDCCOGGs#7Rs+_s#$#9DDCCOGGs#8Rs+'s#$#9DDCCOGGs#9Rs*Ks#$#9DDCCOGGs#:Rs)os#$#9DDCCOGGs#;Rs)7s#$#9DDCCOGGs#<Rs(\s#$#9DDCCOGGs#=Rs($s#$#9DDCCOGGs#>Rs'Hs#$#9DDCCOGGs#?Rs&ls#$#9DDCCOGGs#@Rs&4s#$#9DDCCOGGs#ARs%Xs#$#9DDCCOGGs#BRs$|s#$#9DDCCOGGs#CRs$Es#$#1DCPGQS%s#is#$#s7%s$ds$`XTKs#is#G#FUTLS+8S+2S)#Es:ATMVTN#s:.2S)$2S)s:0Es:ETOH#s:22S)#k##&#k##(#VTPs:=s7l4S)s:>2S)s7n4S)s7nk##$#k##&#2S)s:CWTQs:Ds7sS*j##T2#j#-%#2S)s7uk##T2#k#-(#VTRCS*XT3Cs6WS*#XT3C#S*s6X6CS)VTSCs8F/C$S&#0s6ZIEEH#MUT#E6Cs6z:C'#:C#$:C#%:C#&:C#':C#(:C#):C#*:C#+:C#,:C#-:C#.:C#/:C#0:C#1:C#2:C#3:C#4:C#5:C#6:C#7:C#8:C#9:C#::C#;:C#<:C#=:C#>:C#?:C#@:C#A:C#B/C#S's%D0s6~IEEH#MZTTs7#IEEHS,\T4s7$IEEH$s#'#\T4s7%IEEHs#)s#(#l#(#s6ys6sl#)s#/s7(#l#*s7,s7+#j#.C#j#/T5#2S)F,S*s7J,#s7K,#s7L,#s7M,#s7N,#s7O,#s7P,#s7Q,#s7R,#s7S,#s7T,#s7U,#s7V,#s7W,#s7X,#s7Y,#s7Z,#s7[,#s7\,#s7],#s7^,#s7_,#s7`,#s7a,#s7b,#s7c,#s7d,#s7e,#s7f,#s7g,#s7h,#s7i4#s%wk###S,k##s#%#k#.C#k#/T5##Sm##############################################################$s8[#Ks8Z%T6#)T6TUTV*#$L'Js8Y+$#&s;y'#8SmXF$#SISil#+s#Rs#,#l#0s$-s$*#l#1s$7s$2#l#2s$@s$9#l#3s$Es$C#l#4s$Gs%0#j#%s%U#j#$D#U#Fj#&D#;s&,s%[#Fj#&D#U#Fj#&D#;s&hs&<#Fj#&D#U#Fj#&D#;s'Is&x#Fj#&D#U#Fj#&D#;s(*s'Y#Fj#&D#U#Fj#&D#;s(gs(:#Fj#&D#U#Fj#&D#;s)Hs(w#Fj#&D#U#Fj#&D#;s*)s)X#Fj#&D#U#Fj#&D#;s*fs*9#Fj#&D#U#Fj#&D#;s+Fs*v#Fj#&D#U#Fj#&D#;s,'s+V#Fj#&D#U#Fj#&D#;s,ds,7#Fj#&D#U#Fj#&D#;s-Es,t#Fj#&D#U#Fj#&D#;s.&s-U#Fj#&D#U#Fj#&D#;s.cs.6#Fj#&D#U#Fj#&D#;s/Cs.s#Fj#&D#U#Fj#&D#;s0#s/S#Fj#&D#U#Fj#&D#;s0_s03#Fj#&D#U#Fj#&D#;s1>s0o#Fj#&D#U#Fj#&D#;s1{s1N#Fj#&D#U#Fj#&D#;s2\s2/#Fj#&D#U#Fj#&D#;s3=s2l#Fj#&D#U#Fj#&D#;s3ys3M#Fj#&D#U#Fj#&D#;s4Zs4-#Fj#&D#U#Fj#&D#;s5;s4j#Fj#&D#U#Fj#&D#;s5ws5K#Fj#&D#U#Fj#&D#;s6Ws6+#Fj#&D#U#Fj#&D#;s78s6g#Fj#&D#U#Fj#&D#;s7us7H#Fj#&D#U#Fj#&D#;s8Us8)#Fj#&D#U#Fj#&D#;s8ss8e#Fj#&D#U#Fj#&D#;s9hs9'#Fj#&D#U#Fj#&D#;s:'s9x#S*U#Fj#%s:5#j#$D#XTWs:PJSu#j#5s:S#j#6s:W#j#7s:]#j#8s:_#j#9s:d#j#:s:i#j#;s:k#j#<s:n#j#=s:q#j#>s:u#^#T)TXSmS}SiSIS,S+S*Fj#?s:z#j#@s;$#j#As;L#j#Bs;N#j#Cs;z#j#Ds=E#j#Es=G#j#Fs=J#j#Gs=M#j#Hs=R#[TYSIS,S+S*s=Y#Fj#Is=_#j#JC#j#Ks=g#j#Ls=c#j#Ms=h##"). Qed.

  Lemma h_know_ok : forall regs mem sp can, hfH regs mem sp can ->
    know_ok RSEGS (ENV (h_vals regs sp can)) mem h_kn.
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.hfH); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.know_ok); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.Plain.h_vals); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.h_kn); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.getr); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ASP_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.ASP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.stk_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.HF_FR); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.cells_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsHdrErr.hf_cells); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@Corelib.Init.Logic.proj2); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@Stdlib.ZArith.BinInt.Z.opp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.kn_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDriveX.know_ok_app); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.kentry_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.kalign_intro); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.edenot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.krange_intro); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.AND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.kwr_of_stk_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.kimg_intro); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRun.kword_intro); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefExitBase.store_ok_data); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.X); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.flat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.estart); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.cells_know); constr:(@Stdlib.Lists.List.forallb); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsPrintfFirst.cell_wf_b)|] [|@i; @__ff; @__varmap; @__wit; @__arith; @b; @Ha; @__x1; @__sat66; @__sat67; @__sat68; @__sat0; @__sat1; @z; @x; @y; @m; @n; @d; @__x2; @__p1; @cstr; @__x3; @Hm; @Hd; @Z0; @E1; @E0; @Hsp; @Hcan65; @Hcan0; @Hcells0; @Hgot0; @Himg0; @Hstk0; @HspHi0; @HspLo0; @Hsp17; @H3; @Hcan64; @Hcan; @Hcells; @Hgot; @Himg; @Hstk; @HspHi; @HspLo; @Hsp16; @H2; @PH; @can; @sp; @mem; @regs|] "#/y#G$o#Q$5$6#a$4##$:#U#%$K#$#y#&#>#'$T#=#c#d#f$=$>#(#?#)#l#p#7#:#+$U#b#B#N#*#-$9$R#,#1#2#9#<$/$W#O#P#R#X#]#[#Z#e#j#.#k#m#/#8#|#~$%$(#@$-$D$F#A$N$V#C#G$g$e$+$q#J#^#s#0#4#3#6#t#;#{#}$$$'$&$)#x$*$0$1$3$;$?$@$<$.$E$G$C$M$O$Y$[$\$]$Z$P$a#D$d$c$f$i#F$_$j$k$l$m$n$p$r$o#w#S#M#L#g$7$2#Y#\#`$8#i#h#u$I#T#o#z$L$X$A$,#W#V#_$J$^$`#K#n#r#q#v$#$B$H$S$Q$b$hL$I$$J$#B%$K%$L'$M*#O%$N&$O$$P%$Q%$R%$S%$T%$U+$V'$W$$X&$Y*$Z&$[)$\)$]&$^$$_%#A$$`%$a'$b%$c$$d'$e%$f%$g%$h%$i%$j%$k/$l'$m'$n%#S4$#@##%########@#US@#VS_*#@)US@#USA#k##'#XSBOKMHXSBQOKM9S)OK:#2J#QSCj##&#+7VS`6#m$SD#WSE8%#VSFQ#*3#K,5O+9;$#*C#F,9Q%S$#,;S)%#S%XSGJS5S+S&#?##################+##S4##############################+#$2$#$###########################+#$B$#####$#########################+##s#%######$#########################+#$S4##$#############$#$###########$#$#########+#$s#)$#$#$#$###$#$#$#$#########+#$s#9############$#$###$#########+#$s#J####$#$#$#$#####$#$###########+#$2$#$#$#$#####$#############+##s#W$###$#$#$#$###$#$#$#####$#############+#$s#g############################+#%s$WH$s%8$#$###########################+#/Hs$X&5#.s%FMUS6#USHs%D*s%D$#k##'#k#$C#$s%P$#####$#########################+#%s$`H#s#.######$#########################+#/Hs$a&6#USIs#/*s%o#s#.k##%#k#$C#VSJS6S,USKs%tUSA#$S4####$#$#########$#$###$#####$#$#$#########+#.s&5s$j3S-3#3#3#3#3#3#3#AJSI+#.s&?S9B%#Cs#'#*s#'&#%FS6+s&EVSas&8#/S6#&&#WSEs&Ns&;SDVSFS:#*s&I#SL,s&KSb;#s&8*C#F,s&NS:%S$#,s&PS;%#S%XSGJScSdS&US.s#k*s&O#s#jk##s#n#k#$C#USMs#o*s&S#s#nk##s#E#k#$C#VSJS.S,AJSMs#)A.s&]SeBs###Cs#E#*s#E&#%FS./S.?&$#USfS<,s&eS<%F#/$s#$&$#0s&hS/9S=S/S<:#D#S-*s&l#S/.s&nS/0s&n#9S#SgS/:#D#s#>*s&r#'0CF.s&uF,s&v#*C#F9S*S#S=:#USNS-VSh#s&gWSi$S$S%USjS&E&#VSO#S&VSPs&Is&8VSPs&'s%qUSkFE#s%\USNs#PWSl$s#J#$s$(############$#####$#########+#E6s%`$s#{##$#######+#VSO*#USQN4N$#4N>#4Ns###4Ns#%#4Ns#'#4Ns#+#4Ns#-#USmS,WSnN$#2Js#2P#9SRPS#:#2J#S*(2J$S*(&$#k##(#2Js#9P,2Js#:P,&$#2J*S*-k##$#YSoJs#>P10WSSJs#?PUSQS>USKS>USpCUSqCUSrC-CF-Cs'M'C$S7#(&GDDE#IVSs'E0S'S(VStHK*S'#S(m$%#WSuCFMXSvHK$#l#%*)#l#&10#l#'43#/Fs'Zl#($#H,s'pH;#s']*C#Fj#)s'r#Ds#YS-7s'tS#$SL#KFs#[s#Z,s'w#;#s'd*C#Fm#'#[SwJs#`Ps#_s'g.#%S$.%/S%&$#j#)s'~#,s($S#VST#s'm%F$%Fs'o,s((S*;#s'q%F#k##&#k##(#VSxs'|s$G/Fs'}%Fs$I/Fs$Ik##$#k##&#%Fs(&WSys('s$NMj##SU#j#*%#%Fs$Pk##SU#k#*(#GCM=CS4$s#_$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#+#-C#'Cs#1L#(s#jGDDE#IUSHD#s#($#$#$#$#$#$#$#################################################+#-C#'C#Ls#V(s$3GDDE#I5s$4GDDE#s#(1s$5GDDE$s#(#1s$6GDDEs#*s#)#l#%#s$2s$,l#&s#]s$9#l#'s$=s$<#j#+C#%Hs#2%.M%/K%Ks#5&$#k##&#k##(#k#+C#,s)DSVWH#S:S;l#(-%#l#,s#os#l#l#-s#ys#t#l#.s$&s#{#%S$s$(%s$)S%&$#m#&#7s)MS#s$-#s$8K%S$s$6%s$7S%&$#m#&#[SzJs%8Ps%7S$S%#$s&S$###########+#-C#'Cs$[L#(s$]GDDE#I'C%Ls$&(s$_GDDE#I5s$`GDDE%#1s$aGDDEs#0s#T#l#%#s$]s$Wl#&s$,s$d#l#'s$hs$g#j#+C#%s#8H%F/%0M&$#k##&#k#+C#VHs#+S;l#(*$#l#,s$;s$8#l#-s$Es$@#l#.s$Ns$G#%FS&%S&s$Q&$#m#&#]S{Js%[Ps%ZS#S&KS9#-Cs)@'Cs$vL#(s$xGDDE#Il#%#s$ts$nl#&s$|s${#l#'s%#s$~#%Fs)Fl#($#H-Cs)7-Cs)sWS|C#s*%'C%L#(s%&GDDE#Il#%#s$~s$xl#&s%*s%)#l#'s%-s%,#%s)?s&Dl#($#Hl#/s$Us$R#l#0s$_s$Z#\SWJs%pPs)Ts)C/#S0-Cs)2'Cs%/L#(s%1GDDE#Il#%#s%-s%'l#&s%5s%4#l#'s%8s%7#%Fs)8l#($#H-Cs)('C#L6(s%9GDDE#Il#%#s%5s%/l#&s%=s%<#l#'s%@s%?#%s).s&Wl#($#Hl#/s$hs$e#l#0s$rs$m#\SWJs&'Ps)Ds)2-#S5.s*CS=0s*Cs&-VS8s&ms&f+S4+s*K%$#0C%0C%HRCS8S1S2SXs&s'$s&l&#-C(-C('C$L#(s%NGDDE#Il#%#s%Js%Dl#&s%Rs%Q#l#'s%Us%T#l#(#-HI1.+#VS8s&vs&v%11HRCS8S1S2SXs&x2/s&x2/'C-L-(s%XGDDE#Il#%#s%Ts%Nl#&s%\s%[#l#'s%_s%^#l#(#)HI+*)#)Hs)8%F#j#1C#-Cs);6Cs%a#'Cs%bL#(s%dGDDE#Il#%#s%`s%Zl#&s%hs%g#l#'s%ks%j#)Fs)B%F#l#(%#H7CF-#s&TH<s'2)1#%#s',j#1C#)*&%#s'/),s#.%#s'1j#2CH%MHUS}#j#3C#j#2C#)MHXS~CCT##0C#j#4C#j#5C#0C8<H0C#j#2R#`T$RCCCS1S100#s'Hs#>s#;fT%CCCCCCS?111S?(=='9s#?#0Cs'BHCCS23S2/75$s'Cs'C#6Cs#&s#<'C#Ls#e(s&,GDDE#Il#%#s&(s%~l#&s&0s&/#l#'s&3s&2#l#(#;Hl#/s%Zs%W#l#0s%ds%_#I@>,#m##A7CFs#$#s&zH.s+7s#6AJS*#s'Y.s+9S#Bs'[#Cs'}#*s'}&#j#1C#7CF#S)s'&HdT&Js'$Ps&ws'(s)ts'`s&us#Zs#YMs#Is#?s#1+#)Hs)f%F#/$s'[%Fs&`)&s&a%#s'^&%#&'#&)#%FM<M)K#%#s&i)Qs)s)#O.s+O#>JSY#K*S'#S(k##(#k##,#k#4R#k#6C#&0#j#1C#)Fs)~%F#/$s's)%s&x%#s'u&<#&&#&(#)*O.s+a#>JS3#K*S'#S(k##:#k##>#k#4R#k#6C#-Cs*26Cs&g#'Cs&hL#(s&jGDDE#I'C%S7s$I(s&lGDDE#I-Cs'/'Cs&mL#(s&oGDDE#I6C*%'C#Ls$O(s&rGDDE#I5s&sGDDE&#5s&tGDDE*#5s&uGDDE-#l#%#s&qs&kl#&s&ys&x#l#'s&|s&{#l#(#=Hl#/s&Gs&D#l#0s&Qs&L#%s*GH<O)H#$s'T####$#$#$#########+#%.s*E&1##s%;$###########################+#%s*FH#s%F################+#%s#+s*B&.##s)/$#$#$#$#$#########################+#%s*BH$s)@############################+#%s#Qs*C&4#?s#)#?s#G#j#1C#UT'K<K%F#,s,zS3VST#s,g%F$,s,}T(;#s,j%F#k##s'[#k##'#GCKJC#Ms((=Cs-06Cs'L#'C#Ls#v(s(*GDDE#I'Cs(*Ls'O(s(,GDDE#I6Cs$#s'Q'Cs$%L#(s(/GDDE#I6C%+-Cs+H'C$L#(s(3GDDE#I5s(4GDDE'#ZT)s(5GDDEQ[T*s(6GDDE$#1s(7GDDE-s'*#1s(8GDDE0s'+#l#%#s(4s(.l#&6s(;#l#'s(?s(>#j#+C#j#7C#j#8SZ#)HM%#s(^)s$HK%s+i#)$O%#s+[&%#?#Qk##s$]#k##*#k#+C#k#7C#k#8SZ#)s$SS0%s+S#<S5)%#%#s+G&&#%s+4(%&s+%&$#?&#YH#*S0S)S+l#(;.#l#,s(%s'~#l#-s(/s(*#l#.s#>s#8#l#9s#Cs#A#,s-]s$ZKCs*'KCs*)KCS-WS[C$#WS[C&#VT+#T,4S>#s(gGCOJCs(gO#JC#Ms#C=Cs*K'Cs(gL#(s(iGDDE#I6Cs(2%'C#Ls$\(s(lGDDE#I=Cs*R'Cs'?L#(s(oGDDE#I'Cs(oLs#E(s(qGDDE#I'Cs#GS7s&P(s(sGDDE#I5s(tGDDE%#1s(uGDDE(s'h#1s(vGDDEs#Ls'i#1s(wGDDE-s'j#1s(xGDDE1s'k#l#%#s(ts(nl#&6s({#l#':s(~#j#+C#j#7C#j#:C#%FK)MO%#s)C%s'TQ)s%.Q%F#/$s*C&$#k##'#k##+#k##*#k##-#k#+C#k#7C#k#:C#,s.3T-[Hs#C#S0QS)S+S.l#(4%#l#,s(^s([#l#-s(hs(c#l#.s#ws#q#l#9s#|s#z#VS\s%8#7Cs%9s$#s#=s#<#XT.S3s%9K#j#;s%O#j#<s%S#j#4R#j#6C#XS]s%@s%8s%##'Cs)@Ls)@(s)BGDDE#I'Cs)BS7s&}(s)DGDDE#I5s)EGDDE%#l#%#s)As);l#&s)Is)H#l#'s)Ls)K#%FF&#s(yl#(%#Hl#/s(us(r#l#0s)#s(z#VS\F#7CFs%W1s*8#UT/s)uFs*7#,s.S#UT0s)x)$#%F#/$s*p)%s)u%#s*r&s%u#&&#&(#9SYSVSR:#F#0,s.`#)#/)#O.s.c#>JS3#K*S'#S(k##s%x#k##s%|#k#4R#k#6C#&0#m#=#WT1s*Qs*4s*-VT21s*5)#O.s.o#>JS3#K*S'#S(k##s&(#k##s&,#k#4R#k#6C#&,#m#.#XSSJs*]Ps*8m#$#VT3Ns)~8Ns*#s*;s*:$#8Ns*$s*Us*:s&?#8Ns*%s*Zs*:s'=#8Ns*&s*\s*:s'Q#8Ns*'s*^s*:s'g#8Ns*(s*bs*:s(/#8Ns*)s*ds*:s)d#VS^CRVS^#CWT4#T5S,*S'#S(m$s*##YT6s*lPS,#S+XS]s*6s*5)#XT7s*8s*3s*2#2Js*oPSCm#$#m##$l#=s*ws*t#l#>s*}s*y#l#?s+(s+$#l#@s+.s+*#j#As+0#j#Bs+4#j#Cs+:#j#Ds+<#j#Es+A#j#Fs+F#j#Gs+H#j#Hs+K#j#Is+N#j#Js+R#^#S9S0S5S+S)QOKMHj#Ks+W#j#Ls+]#j#Ms,)#j#Ns,+#j#Os,W#j#Ps/*#j#Qs/,#j#Rs//#j#Ss/2#j#Ts/7#[T8QOKMs/>#Hj#Us/D#j#VC#j#Ws/L#j#Xs/H#j#Ys/M##"). Qed.

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
    | let Hc := fresh "Hc" in krd HK 0x681830%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.False Sort Prop.

  Theorem as_hdr_short_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x0a4154) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x0a4190) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof. hf_plain hs_sound. Qed.

  Theorem as_hdr_overrun_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x0a4170) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x0a4190) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

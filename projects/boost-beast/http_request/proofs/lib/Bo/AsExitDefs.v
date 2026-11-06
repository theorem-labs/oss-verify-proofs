(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsCarryKeep.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition AEXIT : Z := 0x1035e8.
Definition AEXIT_ECALL : Z := 0x1033c0.
Definition AX_FR : Z := 400.
Definition XFUEL : nat := 60000.   (* [comment removed for export] *)
Definition XSTOPS : list Z := [0x109138]%Z.

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x6617f0%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition ax_atexit_cells (two : bool) : list (Z * nat * Z) :=
  (if two then [(0x681848, 4%nat, 2); (0x681868, 8%nat, 0x103594); (0x681968, 8%nat, 0x0a43c4); (0x65fe14, 1%nat, 0)]
   else [(0x681848, 4%nat, 1)])%Z.

(* [comment removed for export] *)
Definition ax_lit_cells (two : bool) : list (Z * nat * Z) :=
  [(0x681a60, 4%nat, 0);          (* [comment removed for export] *)
   (0x681a83, 1%nat, 0);          (* [comment removed for export] *)
   (0x681844, 4%nat, 0)]%Z        (* [comment removed for export] *)
  ++ ax_atexit_cells two ++
  [(0x681850, 8%nat, 0x681858);   (* [comment removed for export] *)
   (0x681858, 8%nat, 0);          (* [comment removed for export] *)
   (0x681860, 8%nat, 0x103594);   (* [comment removed for export] *)
   (0x681960, 8%nat, 0x0939fc);   (* [comment removed for export] *)
   (0x1bf660, 1%nat, 0);          (* [comment removed for export] *)
   (0x12a150, 1%nat, 0);          (* [comment removed for export] *)
   (0x121460, 8%nat, 0x121460);   (* [comment removed for export] *)
   (0x12a100, 8%nat, 1);          (* [comment removed for export] *)
   (0x12d01c, 1%nat, 1);          (* [comment removed for export] *)
   (0x12e498, 1%nat, 1);          (* [comment removed for export] *)
   (0x12d7b8, 8%nat, 0x7fff8000); (* [comment removed for export] *)
   (0x12b070, 8%nat, 0);          (* [comment removed for export] *)
   (0x12afd0, 4%nat, 1);          (* [comment removed for export] *)
   (0x121608, 8%nat, 0x111eb8);   (* [comment removed for export] *)
   (0x1bf360, 8%nat, 0xffffffffffffffff);    (* [comment removed for export] *)
   (0x681ee8, 8%nat, 0);          (* [comment removed for export] *)
   (0x123f7c, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x12406c, 4%nat, 0xffffffff)  (* [comment removed for export] *)]%Z.

(* [comment removed for export] *)
Definition ax_flush_cells : list (Z * nat * Z) :=
  [(0x124018, 8%nat, 0x681f00); (0x124028, 8%nat, 0x109138); (0x124038, 8%nat, 0x681f00); (0x124040, 8%nat, 1024); (0x124058, 4%nat, 1)]%Z.

Definition ax_kn (two fl : bool) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-400)) 400; KRange (EVar 1) 1 2147483647;
   KImg 0x10000 0x4e000; KImg 0x119000 0x121000; KImg 0x123fd8 0x123fe0; KImg 0x1240c8 0x12a100;
   KWord (SA (ELit 0) 0x661748) 4 (EVar 1); KWord (SA (ELit 0) 0x681830) 8 (EVar 3);
   KWord (SA (ELit 0) 0x123f18) 8 (EVar 5); KWord (SA (ELit 0) 0x123f28) 8 (EVar 5);
   KWord (SA (ELit 0) 0x123ef8) 8 (EVar 6); KWord (SA (ELit 0) 0x123f00) 8 (EVar 6);
   KWord (SA (ELit 0) 0x123fe8) 8 (EVar 7); KWord (SA (ELit 0) 0x123ff0) 8 (EVar 7);
   KWr (SA (ELit 0) 0x681840) 32; KWr (SA (ELit 0) 0x681a60) 4; KWr (SA (ELit 0) 0x12a150) 1; KWr (SA (ELit 0) 0x12a100) 8;
   KWr (SA (ELit 0) 0x12b070) 8; KWr (SA (ELit 0) 0x65fe10) 32; KWr (SA (ELit 0) 0x7fffa000) 0xce800; KWr (SA (ELit 0) 0x123fe0) 232]%Z
  ++ (if fl then [KWord (SA (ELit 0) 0x124008) 8 (EVar 4); KRange (EVar 4) 0x681f01 0x682300]%Z ++ kn_cells ax_flush_cells
      else [KWord (SA (ELit 0) 0x124008) 8 (EVar 4); KWord (SA (ELit 0) 0x124018) 8 (EVar 4)]%Z)
  ++ kn_cells (ax_lit_cells two).

Definition scr0 : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition keep_nonshadow (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) _ _ => negb ((0x7fff0000 <=? a) && (a <? 0x900000000))%Z
  | _ => true
  end.
Definition kn_drop_shadow (kn : list kentry) : list kentry := List.filter keep_nonshadow kn.
Lemma know_ok_drop_shadow : forall E M kn, know_ok RSEGS E M kn -> know_ok RSEGS E M (kn_drop_shadow kn).
Proof. intros E M kn H. unfold know_ok, kn_drop_shadow in *. apply Forall_forall. intros K HK. apply filter_In in HK as [HK _].
  exact (proj1 (Forall_forall _ _) H K HK). Qed.
Definition one_carry (a : Z) (w : nat) (v : expr) (kn : list kentry) : list kentry :=
  fst (fst (carry [SE (SA (ELit 0) a) w v] kn [])).


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true true) 40) []).
Definition srX1f := Eval vm_compute in (s_regs (fst (fst rX1f))).
Definition cX1f := Eval vm_compute in (carry (s_log (fst (fst rX1f))) (ax_kn true true) []).
Definition knX1f := Eval vm_compute in (fst (fst cX1f)).
(* [comment removed for export] *)
Definition srX2if := Eval vm_compute in (sr_upd (sr_upd srX1f (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x681a60) 4 (sr_get srX1f 12)] knX1f []).
Definition knX2if := Eval vm_compute in (fst (fst cX2if)).
(* [comment removed for export] *)
Definition rX2f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x103614 srX2if [] knX2if 40) []).
Definition srX2f := Eval vm_compute in (s_regs (fst (fst rX2f))).
Definition cX2f := Eval vm_compute in (carry (s_log (fst (fst rX2f))) knX2if []).
Definition knX2f := Eval vm_compute in (fst (fst cX2f)).
(* [comment removed for export] *)
Definition srX3if := Eval vm_compute in (sr_upd (sr_upd srX2f (ridx 13) (sr_get srX2f 12)) (ridx 15) (ELit 0)).
Definition cX3if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x12b070) 8 (sr_get srX2f 14)] knX2f []).
Definition knX3if := Eval vm_compute in (fst (fst cX3if)).
(* [comment removed for export] *)
Definition rX3f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5ecc0 srX3if [] knX3if 40) []).
Definition srX3f := Eval vm_compute in (s_regs (fst (fst rX3f))).
(* [comment removed for export] *)
Definition cX3f := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3f))) knX3if []).
Definition knX3f := Eval vm_compute in (kn_drop_shadow (fst (fst cX3f))).
(* [comment removed for export] *)
Definition srX4if := Eval vm_compute in (sr_upd (sr_upd srX3f (ridx 6) (sr_get srX3f 10)) (ridx 7) (ELit 0)).
Definition cX4if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x12b070) 8 (sr_get srX3f 5)] knX3f []).
Definition knX4if := Eval vm_compute in (fst (fst cX4if)).
(* [comment removed for export] *)
Definition rX4f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5f030 srX4if [] knX4if 40) []).
Definition srX4f := Eval vm_compute in (s_regs (fst (fst rX4f))).
Definition cX4f := Eval vm_compute in (carry (s_log (fst (fst rX4f))) knX4if []).
Definition knX4f := Eval vm_compute in (fst (fst cX4f)).
(* [comment removed for export] *)
Definition x_scf : stdio_res := Eval vm_compute in
  (match stdio_call 40 srX4f knX4f with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
Definition rX5f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS (sc_ret x_scf) (sc_sr x_scf) [] (sc_kn x_scf) 72) []).
Definition srX5f := Eval vm_compute in (s_regs (fst (fst rX5f))).
Definition cX5f := Eval vm_compute in (carry (s_log (fst (fst rX5f))) (sc_kn x_scf) []).

Lemma x_itinerary_flush :
  s_pc (fst (fst rX1f)) = 0x103608 /\ snd (fst rX1f) = [] /\ snd (fst cX1f) = []
  /\ snd (fst cX2if) = [] /\ kread RSEGS knX1f (ELit 0) 0x681a60 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX2f)) = 0x5ecb4 /\ snd (fst rX2f) = [] /\ snd (fst cX2f) = []
  /\ snd (fst cX3if) = [] /\ kread RSEGS knX2f (ELit 0) 0x12b070 8 = Some (sr_get srX2f 12)
  /\ s_pc (fst (fst rX3f)) = 0x5f024 /\ snd (fst rX3f) = [] /\ snd (fst cX3f) = []
  /\ snd (fst cX4if) = [] /\ kread RSEGS knX3f (ELit 0) 0x12b070 8 = Some (sr_get srX3f 10)
  /\ s_pc (fst (fst rX4f)) = 0x109138 /\ snd (fst rX4f) = [] /\ snd (fst cX4f) = []
  /\ stdio_call 40 srX4f knX4f = Some x_scf
  /\ s_pc (fst (fst rX5f)) = AEXIT_ECALL /\ snd (fst rX5f) = [] /\ snd (fst cX5f) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_res); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EExt); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.rX1f); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX1f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX2if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.kread); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.knX1f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.rX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX3if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.knX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sr_get); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.srX2f); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.rX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX4if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.knX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.srX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.rX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.srX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.knX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.x_scf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.rX5f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.AEXIT_ECALL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsExitDefs.cX5f)|] Array.empty "#=a###k#?#2#(#K#M#,#6#:#T#/#1#L#_#^#\#Z#5#;#<#B#C#D#7#N#P#Q#R#U#V#W#X#Y#]#[#`#a#b#c#d#e#f#g#h#i#j#k#l#m#*#+#>#)#9#A#@#-#8#4#'#=#&#J#O#F#H#3#I#G#.#0#E#S;#S$#T$#U&#V$#W$#X%#Y&#Z%#[$#\$#]&#^$#_'#`&#a&#b%#c%#d%#e$#f%#g$#h$#i&#j(#H##########$#$###$#$#$#$#####$###$#####&##H##########$#$###$#$###########$#######&#$7$#$#$###$#$#####$###$#$###$#####&#$1############$#####$#####&#$s#4####$#######$#####$#$#$#######&#$H##$#############$#$#$#$#$#################&#$s#&$#$#$#$#####$#######&##s#$$#$#########$###$#$#$#$#$#$#$#########&#$s$#######$#$#$#$#$#$#$#$#$###########&#$3############################&#$s#V######$#$#################&#$7######&#$=$#######&#$s$U##$###$#####&#$s#F##$#########$#################&#$1##########$#$#$#########&##;$#$#$#$#########&#$s$L##$#$###$#####$###$#$#$###$#&#$s%+$#$#$#$###$#######&#$s$e$#$###$#####$#####$#$###########&#$s#X$#####$#####$###$###########&#$)########&#$.######&##s#]$#$#########&#$s#b######&#$s$Q$#$#$#$#########&#$s$&##$#########&##s%M######$#############&#$)########&#$.######&#$9####$#$###########&##s&^##################&#$s%L$###########################&#$s&|$#####$#########################&##s%k$#########################&##s%r$#$#######&#$s%k$#####$#######&##s&;$#####$#######&##s#v$#$#########&##s&9####$#$#######&#$*##$#######&##s&J$#$#$#$#$#######&##:########&#$s&U######&#$s&[########&##s'%$#$#$#$#$#$#$#$#########$#########&#$s'7##$#######################&#$s'W&#$s&v##$#######&#$)$#######&#$s'(############&#$)$#######&#$s$w##########$#$#&#$s%5####&#$s%<##$#######&##s(}$#$#####$###$#####&#$s%Q##$#$###$#######&##s)*##$#########$#$#$#$#######$#####&#$s#n####&#$s%f######&##s#8######&##s#(######&#$s(/$#####$#$#$#$#$#$#$#####&#$s&}$###$#$#####$#$###########&#$s%M######$#$###########&##s',$###############$#$#$#####&##s'3$#$#######&#$6$#$#$###$#$#$#######&#$s(E$#$#$#$#$###$#########&#$s#=##########$#######&##s&K####$#$#$#$###$###$#$#$#######&##s#f$#$###$#$###########&##s*6$#$#$###$#######&#$s&0$#$#$#$#####&#$s%8##$#$#####&##s+=$#$#$#$#############&#-Es+=s+=7L8L-$##UMD,S#4D#-%##$s+n$#$#$###$#$#$#######$#$###$#####&#-Es+Es+E$2######$#$###$#####$#####&#-Es+Fs+F#s,/##########################################################################################################&#,#4D#-s#a##$s,k####$#####$###$#$#######$#####&#-Es,%s,%UMI$s-$####$###########$#$###############&#&H$s#&####$###$###$###$#####&#$H####$#$#######$#########$###$#############&#,s,H'J'#'#'#+#&s$.,#+J.s-b,#WS$S%%#'*'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#+#,s,m+B#s#E$#$#####$#$#$#$###$#######&#,s,i'6'#'#'#'#+#'$+#'$+#,s,a+s#8'&'#'#'#+#'$+#'$+#'$+#'$+#'$+#'$+#+s#A+s#A+s#A+s#A+s#A+s#A+s#A+s#A+s#A+s#A'.'#'#'#'#'#'#'#'#'#'#+#'$+#'$+#'$+#8D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#&#%Ds#(#%Ds#*#%Ds#,#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds#@#%Ds&*#%Ds#G#%Ds#I#%Ds#K#%Ds#N#%Ds#Q#%Ds#X#%Ds#i#%Ds$5#%Ds#l#%Ds#n#$s$p##########&#(s&<s-L$s$X##$###$#############&#,s-J)0s$I#$7######&#(s&Ps-L)#s$Ps$_$?$#######&#(s&Xs-N)#s$Xs$g(s$`s$_+s$g)$s$[##s%$.#(s$e#$s/a$###########&#,s-V),s$h#$s%S##$#######$###$#$#############&#(s&{s-X)#s${s&|$3####$#######$#$#########&#(s'/s-Z)#s%/s'0$s%w$#######.#(s%=##s&:&#,#)&s%:##-######.#(s%G##s#.##$#########&#,s-k),s%J##s#?##.#(s%U#$s%u##$#$###$#####$###$#$#$###$#&#,s-q)4s%`##s&J####.#(s%l#&s0t,#)%s%h#$s0u$#######.#(s%v#,s&H)$s%q##+######.#(s%~#)#s%xs#A#s&u.#(s&&##s'c$#$###$#######&#,s.0)-s&*#$s&P########.#(s&8#$)$#$###$###$#########$###########&#,s.9)6s&E##6####.#(s&Q#$s$@$#####$#$#####$#$###########&#,s.@)4s&\##s'$####.#(s&h#$0########&#,s.G)*s&i##s$l####.#(s&u#$<######&#,s.N))s&u##s$'####.#(s'%#&s(d,#)%s&}#$s$1########.#(s'/##s$e$#$#$#$#$#########&#,s.b)/s'5#$6######.#(s'B#$s$r######&#,s.j))s'B##s$Q######.#(s'O#$s(-$#$#####$#########&#,s.s)/s'U##s)R####.#(s'a#)#s'[s&]#s)Y######.#(s'h#)#s'bs&e#s)a$#######.#(s'p#)#s'js&n#*######.#(s'w#)#s'qs&v.s%7(s'z#)#s'ts&z$s%d######$#########&#(s*$s/:)#s(2s$n$s'Z##$###############&#(s*1s/;)#s(?s${$+########&#(s*9s/=)#s(9s*:$2######&#(s*@s/?&s3J,#)%s(M#$s'y####$###$###########&#(s*Ps/D+s(^XS&S'Js(\#)%s(]#.s3^(s([#+s(M)$s(V#.s3c(s(_#+s(X)$s(Z#&s3fVS(s(c#$s$)$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#################################################&#$s#$$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#9s)Ts#$##s%M.#(s)W#&%2$#&:9s#bs*,#&s+(#s'$##################&#6s0Ks0;$s&T########################&#$s&l########################&#6s0Fs07#s*a$#$#$#$#######&#6s0:s3M#s%B##$#$###$#######&#6s0<s2q#s)k$#############&#(s,Bs0=)#s*Ms$P#s${$#$#$#########&#(s,Ms0@+s*Y)$s*N##s+2$###$#$#$#######&#(s,Zs0D+s*])$s*[#$.####$#######&#(s,es0H)#s*e-#7$#$#######&#(s,ns0G+s*p)$s*o##@########&#(s,ws0J)#s*w+$s+V######&#(s,~s0L+s+#)$s+##$s+_########&#(s-+s0O)#s+++2s%Zs%J&s6:2s%=#2s%js+c&s6<2s(q#2s(b$$s'4$#$#$#$#$#$#$#$#$#$###$#########&#(s-Fs0W2#s%d#s$y$###########################&#(s-X##s#'$#######################&#21s0i(s-hs5,&s'N2$#$s+|&#9s+vs0ms4n$s,N####$#######&#(s-vs0o,s6*)$s+w#$,$#######&#(s.#s0r)#s,#s,2$5##########&#(s.,s0s)#s,,s,4$+$#######&#(s.4s0u)#s,?s(~$s&M########$#$#&#(s.>s0v)#s,Ls.?$s&r####&#(s.Ds0x)#s,Os.E$s&{##$#######&#(s.Ms0z#s7P##$###########&#,s0y)-s,W#$s'5$###$###$#######&#(s.cs0{$s'V######$###$###$#######$#####&#,s0z)4s,t#$s$7####&#(s.zs0|)#s-,s.{$s'K######&#(s/%s0~)#s-%s/&#s#>######&#(s/,s1$)#s-,s#4#s#/######&#(s/3s1&$s-w$###$#$###$#$#$#$#$#####&#,s1')2s-B#$s)m$#$###########$###########&#(s/Ss1))#s-as/T$s&A$###################&#(s/as1+,s1,)$s-b##s)v$#######$#$#$###$#$#$#####&#(s/ss1.)#s.%s*a#s*#$#$#######&#(s/|s10)#s..s*j$;####$###$#$#$#$#######&#(s0/s13#s%F##########################&#,#)3s.?##s)s##$#########&#(s0Is1@)#s.Ts+7$s#S$###$###$#######&#(s0Us1A$s+@############$#######$#####&#,s1@)3s.e##s$$$###$#####$###########&#(s0ts1C$s(+$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#)6s/+##s/D$###$#######&#(s15s1V)#s/5s16#s'q##$#$#$#####&#(s1?s1X&s(a,#)%s/L##s'r####$#$#####&#(s1Ks1])#s/V-8C%C$#%C/#%C<#%Cs#'#%Cs#J#%Cs#g#%Cs#r#%Cs$6#%Cs$@#%Cs$R#%Cs$b#%Cs$t#%Cs%/#%Cs%7#%Cs%?#%Cs%F#%Cs%d#%Cs%x#%Cs&##%Cs&.#%Cs&7#%Cs&A#%Cs&J#%Cs&V#%Cs&Z#%Cs&^#%Cs'##%Cs'8#%Cs':#%Cs'=#%Cs'?#%Cs'B#%Cs'D#%Cs'M#%Cs'V#%Cs'_#%Cs'j#%Cs'u#%Cs('#%Cs(4#%Cs(@#%Cs(L#%Cs(W#%Cs(u#%Cs)'#%Cs)*#%Cs)0#%Cs)~#%Cs*%#%Cs**#%Cs*/#%Cs*@#%Cs*J#%Cs*S#%Cs*a#%Cs*n#%Cs*r#%Cs*z#%Cs+'#%Cs+/#%Cs+6#%Cs+J#%Cs+X#%Cs+m#%Cs+v#%Cs,'#%Cs,5#%Cs,M#%Cs,i#%Cs,x#%Cs-$#%Cs-.#%Cs-7#%Cs-N#%Cs-_#%Cs-k#%Cs-|#%Cs.4#%Cs.B#%Cs.F#%Cs.O#%Cs.W#`S)s9ds0ws:0s0Rs0Ms0Rs0Ks2Ds2Ds0Gs.n#4I#-s11###s;K$###$#####$#$#####&#-Es2Xs2X*s2Us2U*$#*1#*s2X#*s2Y#*s1D#*s1W#*s2\#*s2]#*s2^#*s29#*s2\#*s2a#*s2b#*s2c#*s2M#*s2a#*s2f#*s2g#*s2h#3Es;K3s2ls2k3s2js2h3Es;<3Es;/3s2ms1k3Es:|3s1Ys#+3Es2u/s2rs2r**/A@$#/s#.@&#/s2u@-#/s2v@.#/s1a@*#/s1t@,#/s2y@1#/s2z@2#/s2{@3#/s2V@1#/s2y@4#/s2~@6#/s3#@7#/s3$@8#/s2j@7#/s2~@9#/s3'@;#/s3(@<#/s3)@=#/s3-@?#VNFs3-0#GS*0Fs3/#5#-E#s;m1Fs32&-s33#s327CVN#s357S+0$#S,1&s38#-s39#s380'&S-1)s3;#-s3<#s3;:KS.s39s8-s1C-s3;#s3904GS/0Fs3@#5#-E#s;l1Fs3C&-s3D#s3C021S014s3F#-s3G#s3F054S117s3I#-s3J#s3I:KS2s3Gs9rs1FUS3s3E&s1lVO$#m$P#WQ&%#VRS4#4D#-s3P*#0s#)GS50Fs3U#5#-E#s;s1Fs3X&-s3Y#s3X0s#'s#&S61s#)s3[#-s3\#s3[0s#*s#)S71s#,s3^#-s3_#s3^:KS8s3\s:+s1[&s,WVO8#m$P#WQ:%#VRS9#4D#-s3d)#0s#=GS:0Fs3i#5#-E#s;v1Fs3l&-s3m#s3l0s#;s#:S;1s#=s3o#-s3p#s3oWS<s1LS=S>4IS?-s2Z$#0s#IGS@0Fs3u#5#-E#SA1Fs3x&-s3y#s3x0s#Gs#FSB1s#Is3{#-s3|#s3{*&#*)#*.#*2#*6#*9#*>#*s#'#*s#+#*s#/#*s#2#*s#7#*s#A#*s#E#*s#I#*s#L#*s#Q#*s#T#*s#X#*s#_#*s#b#m$s#h##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false) 40) []).
Definition srX1c := Eval vm_compute in (s_regs (fst (fst rX1c))).
Definition cX1c := Eval vm_compute in (carry (s_log (fst (fst rX1c))) (ax_kn true false) []).
Definition knX1c := Eval vm_compute in (fst (fst cX1c)).
(* [comment removed for export] *)
Definition srX2ic := Eval vm_compute in (sr_upd (sr_upd srX1c (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x681a60) 4 (sr_get srX1c 12)] knX1c []).
Definition knX2ic := Eval vm_compute in (fst (fst cX2ic)).
(* [comment removed for export] *)
Definition rX2c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x103614 srX2ic [] knX2ic 40) []).
Definition srX2c := Eval vm_compute in (s_regs (fst (fst rX2c))).
Definition cX2c := Eval vm_compute in (carry (s_log (fst (fst rX2c))) knX2ic []).
Definition knX2c := Eval vm_compute in (fst (fst cX2c)).
(* [comment removed for export] *)
Definition srX3ic := Eval vm_compute in (sr_upd (sr_upd srX2c (ridx 13) (sr_get srX2c 12)) (ridx 15) (ELit 0)).
Definition cX3ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x12b070) 8 (sr_get srX2c 14)] knX2c []).
Definition knX3ic := Eval vm_compute in (fst (fst cX3ic)).
(* [comment removed for export] *)
Definition rX3c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5ecc0 srX3ic [] knX3ic 40) []).
Definition srX3c := Eval vm_compute in (s_regs (fst (fst rX3c))).
Definition cX3c := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3c))) knX3ic []).
Definition knX3c := Eval vm_compute in (kn_drop_shadow (fst (fst cX3c))).
(* [comment removed for export] *)
Definition srX4ic := Eval vm_compute in (sr_upd (sr_upd srX3c (ridx 6) (sr_get srX3c 10)) (ridx 7) (ELit 0)).
Definition cX4ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x12b070) 8 (sr_get srX3c 5)] knX3c []).
Definition knX4ic := Eval vm_compute in (fst (fst cX4ic)).
(* [comment removed for export] *)
Definition rX4c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5f030 srX4ic [] knX4ic 40) []).
Definition srX4c := Eval vm_compute in (s_regs (fst (fst rX4c))).
Definition cX4c := Eval vm_compute in (carry (s_log (fst (fst rX4c))) knX4ic []).
Definition knX4c := Eval vm_compute in (fst (fst cX4c)).

Lemma x_itinerary_clean :
  s_pc (fst (fst rX1c)) = 0x103608 /\ snd (fst rX1c) = [] /\ snd (fst cX1c) = []
  /\ snd (fst cX2ic) = [] /\ kread RSEGS knX1c (ELit 0) 0x681a60 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX2c)) = 0x5ecb4 /\ snd (fst rX2c) = [] /\ snd (fst cX2c) = []
  /\ snd (fst cX3ic) = [] /\ kread RSEGS knX2c (ELit 0) 0x12b070 8 = Some (sr_get srX2c 12)
  /\ s_pc (fst (fst rX3c)) = 0x5f024 /\ snd (fst rX3c) = [] /\ snd (fst cX3c) = []
  /\ snd (fst cX4ic) = [] /\ kread RSEGS knX3c (ELit 0) 0x12b070 8 = Some (sr_get srX3c 10)
  /\ s_pc (fst (fst rX4c)) = AEXIT_ECALL /\ snd (fst rX4c) = [] /\ snd (fst cX4c) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

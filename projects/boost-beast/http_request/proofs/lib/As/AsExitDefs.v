(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsCarryKeep.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition AEXIT : Z := 0x0ff2ac.
Definition AEXIT_ECALL : Z := 0x0ff084.
Definition AX_FR : Z := 400.
Definition XFUEL : nat := 60000.   (* [comment removed for export] *)
Definition XSTOPS : list Z := [0x104dfc]%Z.

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x65d4b0%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition ax_atexit_cells (two : bool) : list (Z * nat * Z) :=
  (if two then [(0x67d508, 4%nat, 2); (0x67d528, 8%nat, 0x0ff258); (0x67d628, 8%nat, 0x0a30f8); (0x65bad4, 1%nat, 0)]
   else [(0x67d508, 4%nat, 1)])%Z.

(* [comment removed for export] *)
Definition ax_lit_cells (two : bool) : list (Z * nat * Z) :=
  [(0x67d720, 4%nat, 0);          (* [comment removed for export] *)
   (0x67d743, 1%nat, 0);          (* [comment removed for export] *)
   (0x67d504, 4%nat, 0)]%Z        (* [comment removed for export] *)
  ++ ax_atexit_cells two ++
  [(0x67d510, 8%nat, 0x67d518);   (* [comment removed for export] *)
   (0x67d518, 8%nat, 0);          (* [comment removed for export] *)
   (0x67d520, 8%nat, 0x0ff258);   (* [comment removed for export] *)
   (0x67d620, 8%nat, 0x092730);   (* [comment removed for export] *)
   (0x1bb320, 1%nat, 0);          (* [comment removed for export] *)
   (0x125e10, 1%nat, 0);          (* [comment removed for export] *)
   (0x11d1a0, 8%nat, 0x11d1a0);   (* [comment removed for export] *)
   (0x125dc0, 8%nat, 1);          (* [comment removed for export] *)
   (0x128cdc, 1%nat, 1);          (* [comment removed for export] *)
   (0x12a158, 1%nat, 1);          (* [comment removed for export] *)
   (0x129478, 8%nat, 0x7fff8000); (* [comment removed for export] *)
   (0x126d30, 8%nat, 0);          (* [comment removed for export] *)
   (0x126c90, 4%nat, 1);          (* [comment removed for export] *)
   (0x11d348, 8%nat, 0x10db7c);   (* [comment removed for export] *)
   (0x1bb020, 8%nat, 0xffffffffffffffff);    (* [comment removed for export] *)
   (0x67dba8, 8%nat, 0);          (* [comment removed for export] *)
   (0x11fcbc, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x11fdac, 4%nat, 0xffffffff)  (* [comment removed for export] *)]%Z.

(* [comment removed for export] *)
Definition ax_flush_cells : list (Z * nat * Z) :=
  [(0x11fd58, 8%nat, 0x67dbc0); (0x11fd68, 8%nat, 0x104dfc); (0x11fd78, 8%nat, 0x67dbc0); (0x11fd80, 8%nat, 1024); (0x11fd98, 4%nat, 1)]%Z.

Definition ax_kn (two fl : bool) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-400)) 400; KRange (EVar 1) 1 2147483647;
   KImg 0x10000 0x4d000; KImg 0x115000 0x11d000; KImg 0x11fd18 0x11fd20; KImg 0x11fe08 0x125dc0;
   KWord (SA (ELit 0) 0x65d408) 4 (EVar 1); KWord (SA (ELit 0) 0x67d4f0) 8 (EVar 3);
   KWord (SA (ELit 0) 0x11fc58) 8 (EVar 5); KWord (SA (ELit 0) 0x11fc68) 8 (EVar 5);
   KWord (SA (ELit 0) 0x11fc38) 8 (EVar 6); KWord (SA (ELit 0) 0x11fc40) 8 (EVar 6);
   KWord (SA (ELit 0) 0x11fd28) 8 (EVar 7); KWord (SA (ELit 0) 0x11fd30) 8 (EVar 7);
   KWr (SA (ELit 0) 0x67d500) 32; KWr (SA (ELit 0) 0x67d720) 4; KWr (SA (ELit 0) 0x125e10) 1; KWr (SA (ELit 0) 0x125dc0) 8;
   KWr (SA (ELit 0) 0x126d30) 8; KWr (SA (ELit 0) 0x65bad0) 32; KWr (SA (ELit 0) 0x7fffa000) 0xcde00; KWr (SA (ELit 0) 0x11fd20) 232]%Z
  ++ (if fl then [KWord (SA (ELit 0) 0x11fd48) 8 (EVar 4); KRange (EVar 4) 0x67dbc1 0x67dfc0]%Z ++ kn_cells ax_flush_cells
      else [KWord (SA (ELit 0) 0x11fd48) 8 (EVar 4); KWord (SA (ELit 0) 0x11fd58) 8 (EVar 4)]%Z)
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
Definition cX2if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x67d720) 4 (sr_get srX1f 12)] knX1f []).
Definition knX2if := Eval vm_compute in (fst (fst cX2if)).
(* [comment removed for export] *)
Definition rX2f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x0ff2d8 srX2if [] knX2if 40) []).
Definition srX2f := Eval vm_compute in (s_regs (fst (fst rX2f))).
Definition cX2f := Eval vm_compute in (carry (s_log (fst (fst rX2f))) knX2if []).
Definition knX2f := Eval vm_compute in (fst (fst cX2f)).
(* [comment removed for export] *)
Definition srX3if := Eval vm_compute in (sr_upd (sr_upd srX2f (ridx 13) (sr_get srX2f 12)) (ridx 15) (ELit 0)).
Definition cX3if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX2f 14)] knX2f []).
Definition knX3if := Eval vm_compute in (fst (fst cX3if)).
(* [comment removed for export] *)
Definition rX3f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5d9f4 srX3if [] knX3if 40) []).
Definition srX3f := Eval vm_compute in (s_regs (fst (fst rX3f))).
(* [comment removed for export] *)
Definition cX3f := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3f))) knX3if []).
Definition knX3f := Eval vm_compute in (kn_drop_shadow (fst (fst cX3f))).
(* [comment removed for export] *)
Definition srX4if := Eval vm_compute in (sr_upd (sr_upd srX3f (ridx 6) (sr_get srX3f 10)) (ridx 7) (ELit 0)).
Definition cX4if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX3f 5)] knX3f []).
Definition knX4if := Eval vm_compute in (fst (fst cX4if)).
(* [comment removed for export] *)
Definition rX4f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5dd64 srX4if [] knX4if 40) []).
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
  s_pc (fst (fst rX1f)) = 0x0ff2cc /\ snd (fst rX1f) = [] /\ snd (fst cX1f) = []
  /\ snd (fst cX2if) = [] /\ kread RSEGS knX1f (ELit 0) 0x67d720 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX2f)) = 0x5d9e8 /\ snd (fst rX2f) = [] /\ snd (fst cX2f) = []
  /\ snd (fst cX3if) = [] /\ kread RSEGS knX2f (ELit 0) 0x126d30 8 = Some (sr_get srX2f 12)
  /\ s_pc (fst (fst rX3f)) = 0x5dd58 /\ snd (fst rX3f) = [] /\ snd (fst cX3f) = []
  /\ snd (fst cX4if) = [] /\ kread RSEGS knX3f (ELit 0) 0x126d30 8 = Some (sr_get srX3f 10)
  /\ s_pc (fst (fst rX4f)) = 0x104dfc /\ snd (fst rX4f) = [] /\ snd (fst cX4f) = []
  /\ stdio_call 40 srX4f knX4f = Some x_scf
  /\ s_pc (fst (fst rX5f)) = AEXIT_ECALL /\ snd (fst rX5f) = [] /\ snd (fst cX5f) = [].
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sidecond); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_res); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.SCR_); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EExt); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.KImg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.s_pc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sym_state); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.rX1f); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX1f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX2if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymDrive.kread); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.knX1f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.rX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX3if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.knX2f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sr_get); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.srX2f); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.BvWf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.rX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX4if); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.knX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.srX3f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.rX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStdioCall.stdio_call); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.srX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.knX4f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.x_scf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.rX5f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.AEXIT_ECALL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsExitDefs.cX5f)|] Array.empty "#=Z###k#?#2#(#K#M#,#6#:#T#/#1#L#_#^#\#Z#5#;#<#B#C#D#7#N#P#Q#R#U#V#W#X#Y#]#[#`#a#b#c#d#e#f#g#h#i#j#k#l#m#*#+#>#)#9#A#@#-#8#4#'#=#&#J#O#F#H#3#I#G#.#0#E#S;#S$#T$#U&#V$#W$#X%#Y&#Z%#[$#\$#]&#^$#_'#`&#a&#b%#c%#d%#e$#f%#g$#h$#i&#j($H$#$#$#$#$#$###$#######$###$#########&#$H$#$#$#$#$#$#####$###$#$#####$#$#####&##H$#$#$###$#$#####$#$#$#$###$#######&#$/##$###$###$#$#######&##A######$#####$#$###$#$#$#$#$#$#$#####&##s#I##$#$#$#$#$###$#$###$#$#$#$#############&#$s#'##$#####$#######$#$#####&##s#$$#$#$###$###$#####$###$#$#########&#$s#L$#$#$#$#$#$###$#####$###########&#$+############&#$s#J$#$#$#$#############&#$4######&#$:$#######&#$s$L######$#$#######&#$s$,####$###$#$#$###$#$#$#############&#$2##$#$###$#####$#$#########&##:$#$#########&##s%,$#$#####$#$#$#####$#####$#&##s$n##$#$#$#####&#$s$Y$#$#######$#$#$#$#####$###########&#$s#U##$#########$###$#$###########&#$)########&#$.######&##s#[$#$#$#$#########&#$s#`######&#$s$Z$#####$#$#########&#$s$)########$#########&##s%I$###$#################&#$)########&#$.######&#$9$#####$###########&##s&)####################&#$s$j##$#########################&##s%Y$###$#########################&##s%h$#########################&##s%o$#$#######&##s#~########$#######&##s&8######$#######&##s#y$#$#$#$#########&##s&:##$###$#$#######&#$*##$#######&##2$#$#$#######&##8########&#$s&T######&#$s&Z########&##s&|$#$#$###$###$#$###$#########&##s'S$#$#$#$###################&#$s'R&#$s&z##$#######&#$)$#######&#$s'5##############&#$)$#######&#$s$v########$#$#&#$s%4####&#$s%;##$#######&##s(w$###$#$#######&##s%8####$###$#######&##s)#####$#$#########$#$#$#$#$#######&#$s#l####&#$s%c######&##s#6######&##s#(######&##s'X$#$#$#####$#$#########&#$s'%$#####$#$#####$###########&#$s%G$###$###########&##s'-##$#$#####$#$###$#$#$#####&##s'4$#$#######&#$8##$#######$#$#$#$#######&##s'5##$#########&#$s%~$###$#####$#######&#$s*)$###$#$###$#$###$#$#$#$#$#####&##s#`######$###########&##s*&$###$#######&#$s%}##$#$#$#$#####&#$s%-##$#$#####&##s+.##$#########$#####&#-Es+.s+.7L8L-$##UMD,S#4D#-%###H$#$#$###$#$###$#$###$#$###########&#-Es+6s+6$0$###$#$###$#########&#-Es+7s+7#s######################################################################################################################&#,#4D#-s#e##$s#>####$#$#$#$#$###############&#-Es+ss+sUMI$s#R$#$#$#$#$#$#$###$#$#############&#&H$s#&##$#$#########$#########&##s-8##$###$#$#$###$#$#$#$###################&#,s,:'J'#'#'#+#&s$,,#+J.s$4,#WS$S%%#'*'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#+#,s,]+B#s#C$#$###$###$###$#######&#,s,Y'4'#'#'#'#+#'$+#'$+#,s,R+s#6'&'#'#'#+#'$+#'$+#'$+#'$+#'$+#'$+#+s#?+s#?+s#?+s#?+s#?+s#?+s#?+s#?+s#?+s#?'.'#'#'#'#'#'#'#'#'#'#+#'$+#'$+#'$+#8D%D$#%D'#%D*#%D-#%D:#%D<#%D>#%D@#%DB#%Ds#$#%Ds#&#%Ds#(#%Ds#*#%Ds#,#%Ds#.#%Ds#1#%Ds#4#%Ds#7#%Ds#:#%Ds#=#%Ds#@#%Ds&*#%Ds#G#%Ds#I#%Ds#K#%Ds#N#%Ds#Q#%Ds#X#%Ds#g#%Ds$3#%Ds#j#%Ds#l#$s$n##########&#(s&<s-E$s$Y######$###################&#,s-I)3s$J#$:######&#(s&Ss-K)#s$Qs$`$B$#######&#(s&[s-M)#s$Ys$h(s$as$`+s$h)$s$\##s%%.#(s$f#$s/U####$#$#$#####&#,s-T)-s$j#$s&J####$###$#$#$#$#$#$###############&#(s'%s-V)#s%#s'&$4##$#$#$###$#$#$#$#########&#(s'6s-X)#s%4s'7$s#($#######.#(s%B##s&=&#,#)&s%?##-######.#(s%L##s#0$###$#########&#,s-l)-s%P#$s#C######.#(s%]##s0U$#$#####$#$#$#####$#####$#&#,s-t)3s%g##s#Y####.#(s%s#&s'm,#)%s%o##s&Y####.#(s%{#,s&M)$s%v##s&a######.#(s&'#)#s%}s#A$s'[######.#(s&.##s'm##$###$#####&#,s.6),s&1#$s&W########.#(s&?#$)$#####$#########$#$#$###########&#,s.>)6s&L##6####.#(s&X#$s#^######$#$#####$###########&#,s.C)3s&b##s')##.#(s&m#$/########&#,s.I)*s&n##s$p####.#(s&z#$;######&#,s.P))s&z##s$%####.#(s'*#$s(}##$###&#,#))s'*##s2(######.#(s'7##s$e$#$#########&#,s.b),s':##s27####.#(s'F#$s$q######&#,s.i))s'F##s$N######.#(s'S##s$A######$#$###$#########&#,s.s)1s'[##s)X##.#(s'f#)#s'`s&d#s)_######.#(s'm#)#s'gs&l#s)g$#######.#(s'u#)#s'os&u#*######.#(s'|#)#s'vs&}.s%7(s(##)#s'ys'%$s%c##$#########&#(s*)s/4)#s(5s$l$s'^##$#############&#(s*5s/3)#s(As$x$+########&#(s*=s/5)#s(;s*>$2######&#(s*Ds/7&s)z,#)%s(O##s(a##$###$#$###########&#(s*Ts/<+s(`XS&S'Js(^#)%s(_#.s*2(s(]#+s(O)$s(X#.s*7(s(a#+s(Z)$s(\#&s*:VS(s(e#$s3X$#$#$#$#$#$###$#$#$#$#$#$#$#################################################&#$s#$$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#9s)Ss#$##s%G.#(s)V#&%2$#&:9s#_s*+#&s+%$s&s########################&#6s0Bs02$s&K##$#########################&##s*\$#########################&#6s0As02#s*e$#$#$#######&#6s04s3D$s*p$###$###$#######&#6s05s2o#s)q##############&#(s,Hs06)#s*Qs$R#s$|$#$#########&#(s,Rs06+s*\)$s*Q##s+6$#$#$#$#$#$#######&#(s,`s0:+s*a)$s*_##s+B######$#######&#(s,ls0?)#s*j.#8$#$#######&#(s,us0@+s*u)$s*t##A########&#(s,~s0C)#s*|+$s+[######&#(s-)s0E+s+()$s+(#$s+d########&#(s-2s0H)#s+0+2s%]s%M&s,m2s%@#2s%ls+h&s,o2s(r#2s(b$#s+X$#$#$#$#####$#####$#########&#(s-Ks0Q2#s%e#s$}$###########################&#(s-]#$s'V$#$#$###################&#21s0c(s-ms4~&s'L2$#$s,#&#9s+ys0gs4o#s$A######$#######&#(s-|s0j,s5{)$s+{#$,$#######&#(s.)s0m)#s,'s,6$5##########&#(s.2s0m)#s,0s,8$+$#######&#(s.:s0o)#s,Cs(}$s&P##########$#$#&#(s.Es0r)#s,Qs.F$s&u####&#(s.Ks0t)#s,Ts.L$s&~##$#######&#(s.Ts0v#s7J$#$#$#$###$#$#$#####&#,s0z)0s,_##s&x##$#$###$#######&#(s.ms0|$s'X$#####$#####$#$#$#########&#,s0z)3s,{#$s$;####&#(s/'s0|)#s-3s/($s'P######&#(s/.s0~)#s-,s//#s#@######&#(s/5s1$)#s-3s#3#s#.######&#(s/<s1&#s+(####$###$###$#######&#,s1&)0s-G#$s)k$###$#####$#$#$###########&#(s/Zs1()#s-fs/[$s&@$###$#############&#(s/gs1+,s1,)$s-f#$s*q$#$###$#####$#$#$#####&#(s/ws1,)#s.'s*^#s){$#$#######&#(s0$s1.)#s.0s*g$s+.##$#$#######$#$#$#######&#(s04s10#s%F##########################&#,#)3s.B##s+x$###$#########&#(s0Os1C)#s.Xs+6$s'6####$#$#$###$#######&#(s0]s1F$s+;##$#$#$###$#################&#,s1F)4s.l##s$%##$#$#$#$###########&#(s0|s1I$s(2$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#)6s/1##s/M$#$#$#$###$#######&#(s1@s1a)#s/>s1A$s'=##$#$#$#####&#(s1Js1b&s(k,#)%s/U#$s&9####$#$#####&#(s1Vs1g)#s/_-8C%C$#%C/#%C<#%Cs#*#%Cs#L#%Cs#l#%Cs#x#%Cs$=#%Cs$G#%Cs$W#%Cs$f#%Cs$x#%Cs%1#%Cs%9#%Cs%A#%Cs%H#%Cs%e#%Cs%|#%Cs&'#%Cs&3#%Cs&<#%Cs&F#%Cs&O#%Cs&\#%Cs&`#%Cs&d#%Cs')#%Cs'<#%Cs'>#%Cs'A#%Cs'C#%Cs'F#%Cs'H#%Cs'Q#%Cs'Z#%Cs'c#%Cs'n#%Cs'z#%Cs(-#%Cs(9#%Cs(E#%Cs(Q#%Cs([#%Cs(|#%Cs)1#%Cs)4#%Cs):#%Cs*)#%Cs*,#%Cs*1#%Cs*6#%Cs*G#%Cs*Q#%Cs*Z#%Cs*g#%Cs*r#%Cs*v#%Cs*~#%Cs++#%Cs+3#%Cs+9#%Cs+O#%Cs+\#%Cs+m#%Cs+z#%Cs,+#%Cs,8#%Cs,O#%Cs,k#%Cs,|#%Cs-(#%Cs-0#%Cs-9#%Cs-Q#%Cs-c#%Cs-o#%Cs.%#%Cs.;#%Cs.J#%Cs.N#%Cs.W#%Cs._#`S)s9`s1$s:)s0[s0Vs0[s0Ts2Os2Os0Ps.y#4I#-s19###s&Z########$#######&#-Es2bs2b*s2_s2_*$#*0#*s2b#*s2c#*s1K#*s1]#*s2f#*s2g#*s2h#*s2D#*s2f#*s2k#*s2l#*s2m#*s2V#*s2k#*s2p#*s2q#*s2r#3Es;F3s2vs2u3s2ts2r3Es;63Es;+3s2ws1q3Es:u3s1`s#*3Es3#/s2|s2|**/A@$#/s#-@&#/s3#@-#/s3$@.#/s1h@*#/s1z@,#/s3'@1#/s3(@2#/s3)@3#/s2a@1#/s3'@4#/s3,@6#/s3-@7#/s3.@8#/s2s@7#/s3,@9#/s31@;#/s32@<#/s33@=#/s37@?#VNFs370#GS*0Fs39#5#-E#s;h1Fs3<&-s3=#s3<7CVN#s3?7S+0$#S,1&s3B#-s3C#s3B0'&S-1)s3E#-s3F#s3E:KS.s3Cs8+s1K-s3E#s3C04GS/0Fs3J#5#-E#s;f1Fs3M&-s3N#s3M021S014s3P#-s3Q#s3P054S117s3S#-s3T#s3S:KS2s3Qs9ss1NUS3s3N&s1tVO$#m$P#WQ&%#VRS4#4D#-s3Z*#0s#)GS50Fs3_#5#-E#s;o1Fs3b&-s3c#s3b0s#'s#&S61s#)s3e#-s3f#s3e0s#*s#)S71s#,s3h#-s3i#s3h:KS8s3fs:,s1c&s,ZVO8#m$P#WQ:%#VRS9#4D#-s3n)#0s#=GS:0Fs3s#5#-E#s;o1Fs3v&-s3w#s3v0s#;s#:S;1s#=s3y#-s3z#s3yWS<s1TS=S>4IS?-s2a$#0s#IGS@0Fs4##5#-E#SA1Fs4&&-s4'#s4&0s#Gs#FSB1s#Is4)#-s4*#s4)*&#*)#*.#*2#*6#*9#*>#*s#'#*s#+#*s#/#*s#2#*s#7#*s#A#*s#E#*s#I#*s#L#*s#Q#*s#T#*s#X#*s#_#*s#b#m$s#h##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false) 40) []).
Definition srX1c := Eval vm_compute in (s_regs (fst (fst rX1c))).
Definition cX1c := Eval vm_compute in (carry (s_log (fst (fst rX1c))) (ax_kn true false) []).
Definition knX1c := Eval vm_compute in (fst (fst cX1c)).
(* [comment removed for export] *)
Definition srX2ic := Eval vm_compute in (sr_upd (sr_upd srX1c (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x67d720) 4 (sr_get srX1c 12)] knX1c []).
Definition knX2ic := Eval vm_compute in (fst (fst cX2ic)).
(* [comment removed for export] *)
Definition rX2c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x0ff2d8 srX2ic [] knX2ic 40) []).
Definition srX2c := Eval vm_compute in (s_regs (fst (fst rX2c))).
Definition cX2c := Eval vm_compute in (carry (s_log (fst (fst rX2c))) knX2ic []).
Definition knX2c := Eval vm_compute in (fst (fst cX2c)).
(* [comment removed for export] *)
Definition srX3ic := Eval vm_compute in (sr_upd (sr_upd srX2c (ridx 13) (sr_get srX2c 12)) (ridx 15) (ELit 0)).
Definition cX3ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX2c 14)] knX2c []).
Definition knX3ic := Eval vm_compute in (fst (fst cX3ic)).
(* [comment removed for export] *)
Definition rX3c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5d9f4 srX3ic [] knX3ic 40) []).
Definition srX3c := Eval vm_compute in (s_regs (fst (fst rX3c))).
Definition cX3c := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3c))) knX3ic []).
Definition knX3c := Eval vm_compute in (kn_drop_shadow (fst (fst cX3c))).
(* [comment removed for export] *)
Definition srX4ic := Eval vm_compute in (sr_upd (sr_upd srX3c (ridx 6) (sr_get srX3c 10)) (ridx 7) (ELit 0)).
Definition cX4ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX3c 5)] knX3c []).
Definition knX4ic := Eval vm_compute in (fst (fst cX4ic)).
(* [comment removed for export] *)
Definition rX4c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5dd64 srX4ic [] knX4ic 40) []).
Definition srX4c := Eval vm_compute in (s_regs (fst (fst rX4c))).
Definition cX4c := Eval vm_compute in (carry (s_log (fst (fst rX4c))) knX4ic []).
Definition knX4c := Eval vm_compute in (fst (fst cX4c)).

Lemma x_itinerary_clean :
  s_pc (fst (fst rX1c)) = 0x0ff2cc /\ snd (fst rX1c) = [] /\ snd (fst cX1c) = []
  /\ snd (fst cX2ic) = [] /\ kread RSEGS knX1c (ELit 0) 0x67d720 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX2c)) = 0x5d9e8 /\ snd (fst rX2c) = [] /\ snd (fst cX2c) = []
  /\ snd (fst cX3ic) = [] /\ kread RSEGS knX2c (ELit 0) 0x126d30 8 = Some (sr_get srX2c 12)
  /\ s_pc (fst (fst rX3c)) = 0x5dd58 /\ snd (fst rX3c) = [] /\ snd (fst cX3c) = []
  /\ snd (fst cX4ic) = [] /\ kread RSEGS knX3c (ELit 0) 0x126d30 8 = Some (sr_get srX3c 10)
  /\ s_pc (fst (fst rX4c)) = AEXIT_ECALL /\ snd (fst rX4c) = [] /\ snd (fst cX4c) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

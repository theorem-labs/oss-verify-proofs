(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface7 AsWalk AsCXXHeap AS_InstStubs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Stubs7.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis Lsr : SR_laws H.
  Hypothesis Lmpres : MPRES_laws H.

  Let SRmono : forall (Q Q' : config -> Prop) c, as_SR H Q c -> (forall c', Q c' -> Q' c') -> as_SR H Q' c. Proof. exact (proj1 (proj2 Lsr)). Qed.
  Let SRlift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
      as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
      (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).
  Proof. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Let MPtrans : forall mo1 mo2 mo3, as_MPRES H mo1 mo2 -> as_MPRES H mo2 mo3 -> as_MPRES H mo1 mo3. Proof. exact (proj2 Lmpres). Qed.

  (* [comment removed for export] *)
  Definition jstub (pc target : Z) : Prop :=
    (pc = AOPDEL /\ target = AFREE_STUB) \/ (pc = AOPDEL2 /\ target = AOPDEL) \/ (pc = AOPDEL_ARR /\ target = AOPDEL).
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma j_evt7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m : mem) (pc target : Z),
    jstub pc target -> mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 target) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_InstStubs7.Stubs7.jstub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@kc__1); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.AOPDEL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.AFREE_STUB); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.AOPDEL2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface7.AOPDEL_ARR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_evt_step); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@stdpp.bitvector.definitions.BV); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@LinuxProcessSemantics.Riscv.Instr.Jal); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.Riscv.DecodeC.decode_any); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_cong1); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@LinuxProcessSemantics.Riscv.Prelude.sext); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_btgt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done)|] [|@ms'; @pc; @target; @y; @H0; @MI; @PT; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @a0; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra|] "#(y#S$*#]###j#0#1#/#`#2#-#.#d#3#I#H#G#F#E#D#C#B#A#@#?#>#=#<#;#:#9#8#7#6#5#4#J#e#g#h#,#+#K#*#L#$#)#M#&#'#(#N#O#|#}$$#P#w#Y#V#%#y$($,#Q#a#Z#^#_#n#o$##R#\#[#X#c#k#m#s#b#i#x#l#u#t#z#q#W#f#v#{#~$%$&$*$)$+$'#r#p>#k$#l$#m&#n*#o%#p$#q%#r&#s%#tB#u%#v&#w%#x)#y$#z%#{%#|%#}$#~'$#$$$&$%&$&($''$(5$)($SK$#$#$#$#$#1#USL##*1#VSS#%1)USL#VSTS>DVSUISA%CSAM%CSMS6)$#%CSAS7%CSMM)$#%CSAS8)#%2%#2)#,S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGFHLKS9'6SBUSV6USWI&&S:%S<$S?#%ED#j#$E#,OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGFHLKS9S:&#S<)S?(SC'*I%#j##-#%CSBM%CSAS6)$#%CSCM%CSBS6)$#,S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGFHL's#'S?&$K#S93S:2%ED#j#$E#,S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGFHLK&#S9'S:7S<6*I%#j##+#%CSCS6%CS<M%CS:S6,SISESDS@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJ's#3K&$G#F?H>%ED#j#$E#,SESDS@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJG's#8S>&$F#Hs#$Ls##*I&#k##,#j#%C#%CS<S6&.G(Fs#)Hs#(%ED#j#$E#'s#AM&-F#Hs#-Ls#,*I%#j#&C##SK##$#$#####$#$###########$#####$#$#(##SK##$#$#####$#$###$#$#######$###$#$#(##4$#$#$#$#$###$###$#####$#$#$#$#$#(##'$#$#(##,$#$#$#(#'s$*>&s#RF#Hs#rLs#q%ED#j#$E#,SDS@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGF#s#G$#$#$#$#$#####$#####$#####$#$#$#(#'s$As##$s#[##$#$#$###$###$#####$#$#$#$#$###$#$#$#$#$#$#####$#########(#-s$\#.s$]$#(--s$a#.s$bSJ#$s$d##1#$s#)$#$#$###$#####$###$#$#$###$###$#$#(#-6#.7$#3;#(s%(&s#THs#XLs$kKs$jUSNs${/s$|B+$#4Is#E%&#%m$%#+SFSG5s#(%SF#SGm$%#VSXSHCUSN#6SHC10/%#+%#7s#0%'#%m$%#&s$^FDHs$~Ls$}VSOE#j#'s%8#8s#0s%:;9s%;s#X#+Cs$0:s#{s$1s#3>#;'%s#r#+E=XSPIs#q>#<Is#rs#qHs#^Ls%,Ks%+s#=A@?95-%#'s%BS6&s$jF#Hs%.Ls%-%ED#j#$E#&s#vHs$cLs%1Ks%0*I$#m#)#0CS6s$c#S:Dj#(s$k#0CMs$m#S:Dj#(s$z#V#S>Dj##s$}#j##s%.#=s%/s%.s%$#Dj#(s%1#U#Dj##s%H#%CSBS7)#s%L%CSBS8)#s%N2%#%CSCS7)#s%<%CSCS8)#s%>2%#j###s%3%CS?S7)#s%?%CS<S7%CS?M)$#'s%dS:&s$9H#Ls%PKs%O%ED#j#$E#,S@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4NJGFH&#L'Ks%TS9s%S*I%#j##*#%CS9S7%CKM,SYSQSISESDS@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4's%oH&$N#Js%[Gs%Z%ED#j#$E#,SQSISESDS@S=S;S5OPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4N&#Js%>Gs%_Fs%^*I%#k##+#j#%C#%CS9M&-Ns%CJs%dGs%c%ED#j#$E#'s%|S7&,J#Gs%hFs%g*I%#j#&C#&/Js$AGs%kFs%j%ED#j#$E##s$I$#$#(#'s&+s$e#s$[##########$###################$#$#$#$#$#####$#########(#-s&D#.s&E$#(--s&I#.s&JSJ##?################$#$#(#-s$P#.s$Q$#31#&s&-Gs$zFs&HHs&G/s&X6+s$<#4Is#7%s$>#%m$%#5;%SF#SGm$s$<#6SHC,s$E/s$:#+s$:#7A%s$<#%m$%#&s#WJDGs&WFs&VVSOE#j#'s&m#8s$es&o69s&ps#G#+Cs%S:s%Ps%Ts$h9#;'%s%4#+E9XSPIs#Q:#<Is#Rs&FGs#MFs&aHs&`s#.<s$U;63-%#&s#bJs&8Gs&bFs&a%ED#j#$E#&s&JGs#\Fs&eHs&d*I$#m#(#0CMs#\#KDj#(s#d#0CS7s#f#KDj#(s#r#V#S>Dj##s&T#j##s$$#=s$%s$$s#w#Dj#(s$'#U#Dj##s$/#%CS?S8)#s&h%CS<S8)#s$+j###s$$%CS9S8's'2S8&s#zJ#Gs&zFs&y*Is#s#j#&C##s%[$#$#$#$#$#(#'s'=s%r$s#l$###################$#$#$#$#$#####$#########(#-s'Q#.s'R$#(--s'V#.s'WSJ#$s#d$#$#(#-s%U#.s%V$#3)#/s'\-+s%@#4Is#)%s%B#%m$%#52%SF#SGm$s%@#6SHC+s%I/s%>#+s%>#78%s%@#%m$%#8s%fs'p29s'qs#6#:s&Ks&Ts%h4s#_;s#c$s&4#<Is$Ps'DGs#9Fs'_Hs'^?5s%Ss#u0-'#s#]&s'EGs#EFs'`Hs'_*Is#[#m#%#0CMs#E#KDj#(s$_#0CS8s$a#KDj#(s#L#V#S>Dj##s'O#j##s#R#=s#Ss${s#Q#Dj#(s#U#U#Dj##s%(#ZSRs%+s%)s%'s#Z#Dj#(s%.#U#Dj##s'u#ZSRs'|s'vs'js%6#S>j#)s($#j#*s(&#j#&C#j#%C#j#+SZ#j#,s(+#j#-s(.#j#.s(2#j#/s(3#j#0s(4#j#1s(5#j#2s(6#j#3s(7#j#4s(8#j#5s(9#j#6s(:#j#7s(;#j#8s(<#j#9s(=#j#:s(>#j#;s(?#j#<s(@#j#=s(A#j#>s(B#j#?s(C#j#@s(D#j#As(E#j#Bs(F#j#Cs(G#j#Ds(H#j#Es(I#j#Fs(J#j#Gs(K#j#Hs(L#j#Is(M#j#Js(N#j#Ks(O#j#Ls(P##"). Qed.

  (* [comment removed for export] *)
  Lemma free_stmt_via_j7 : forall pc target pc0, jstub pc target -> free_stmt_at H target pc0 -> free_stmt_at H pc pc0.
  Proof.
    intros pc target pc0 PT FS. unfold free_stmt_at. intros until sbs. intros VIS HP K IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0.
    eapply SRlift; [exact K | exact VIS | apply j_evt7; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB p A n lo B errv mo' CH bs sbs
                E HP K' IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0). }
    intros c' PO. unfold free_post in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma free_null_stmt_via_j7 : forall pc target, jstub pc target -> free_null_stmt_at H target -> free_null_stmt_at H pc.
  Proof.
    intros pc target PT FS. unfold free_null_stmt_at. intros until CH. intros VIS HP K CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH.
    eapply SRlift; [exact K | exact VIS | apply j_evt7; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB lo B errv mo' CH
                E HP K' CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH). }
    intros c' PO. unfold free_null_post in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma opdel_arr_of_opdel : opdel_stmt H -> opdel_arr_stmt H.
  Proof. intros FS. exact (free_stmt_via_j7 AOPDEL_ARR AOPDEL APC0_FREE (or_intror (or_intror (conj eq_refl eq_refl))) FS). Qed.
  Lemma opdel_arr_null_of_opdel_null : free_null_stmt_at H AOPDEL -> opdel_arr_null_stmt H.
  Proof. intros FS. exact (free_null_stmt_via_j7 AOPDEL_ARR AOPDEL (or_intror (or_intror (conj eq_refl eq_refl))) FS). Qed.

  (* [comment removed for export] *)
  Lemma free_wild_stmt_via_j7 : forall pc target, jstub pc target -> free_wild_stmt_at H target -> free_wild_stmt_at H pc.
  Proof.
    intros pc target PT FS. unfold free_wild_stmt_at. intros until sbs. intros VIS HP K IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC NS8 A0.
    eapply SRlift; [exact K | exact VIS | apply j_evt7; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB p A n lo B errv mo' bs sbs
                E HP K' IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC NS8 A0). }
    intros c' PO. unfold free_wild_post in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma opdel_wild_of_free_wild : free_wild_stmt_at H AFREE_STUB -> free_wild_stmt_at H AOPDEL.
  Proof. intros FS. exact (free_wild_stmt_via_j7 AOPDEL AFREE_STUB (or_introl (conj eq_refl eq_refl)) FS). Qed.
  Lemma opdel2_wild_of_free_wild : free_wild_stmt_at H AFREE_STUB -> free_wild_stmt_at H AOPDEL2.
  Proof. intros FS. exact (free_wild_stmt_via_j7 AOPDEL2 AOPDEL (or_intror (or_introl (conj eq_refl eq_refl))) (opdel_wild_of_free_wild FS)). Qed.
  Lemma opdel_arr_wild_of_free_wild : free_wild_stmt_at H AFREE_STUB -> free_wild_stmt_at H AOPDEL_ARR.
  Proof. intros FS. exact (free_wild_stmt_via_j7 AOPDEL_ARR AOPDEL (or_intror (or_intror (conj eq_refl eq_refl))) (opdel_wild_of_free_wild FS)). Qed.

  (* [comment removed for export] *)
  Lemma asan_rt_hyps7_of : opdel_stmt H -> free_null_stmt_at H AOPDEL -> free_wild_stmt_at H AFREE_STUB -> asan_rt_hyps7 H.
  Proof.
    intros F1 F2 F3. unfold asan_rt_hyps7.
    split; [exact (opdel_arr_of_opdel F1)|]. split; [exact (opdel_arr_null_of_opdel_null F2)|].
    split; [exact F3|]. split; [exact (opdel_wild_of_free_wild F3)|].
    split; [exact (opdel2_wild_of_free_wild F3)| exact (opdel_arr_wild_of_free_wild F3)].
  Qed.
End Stubs7.

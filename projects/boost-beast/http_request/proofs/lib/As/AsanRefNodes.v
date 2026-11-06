(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanCeil Scfg RelSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  realizes segs (nx T1) A -> realizes segs (nx T2) B -> realizes segs (nx T3) C ->
  realizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall i, sstep_cfg segs the_scfg c (evs i) (SNext (nx i))) ->
  (forall e st, sstep_cfg segs the_scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok segs c I evs nx.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.apply_zeros_one); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.zfill); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_unmaps); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_empty); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.None); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_set); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_ret); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fregs); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc_val); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_resv); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fcsr); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_writes); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_copies); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_unmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_zeros); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_copies); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_writes); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.mkst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.regupd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_addi); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.b_npc4); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@Corelib.Numbers.BinNums.N); constr:(@kc__1); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Logic.and); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentNodes.epend); constr:(@stdpp.bitvector.definitions.BvWf)|] [|@b; @o; @b2; @b1; @n; @z; @e; @H; @Hc; @Hm; @a; @r; @x8; @rom; @mem; @pc; @regs|] "#%k#-#v###)#%#$#(#*#&#'#C#+#k#N#p#J#,#A#G#I#M#O#]#^#_#\#`#[#i#u#t#4#2#0#6#7#F#H#Q#R#S#e#f#g#m#n#j#-#q#o#r#s#h#B#v#w#D#8#T#X#5#l#3#9#E#U#W#Y#Z#?#1#=#K#V#;#<#:#>#L#P#a#c#d#b#@@#Y+#Z&#[$#\$#]$#^%#_$#`%#a$#b$#c$#d$#e$#f%#g$#h$#i(#j$#k%#l'#m&#n&#o&#p)#q&#r&#s%#t'#u))S0US1#1#)%)#)#)#)#1#'#VS2*#1)'#US3#k##'#WS4GFC5))6**FC2$7%$#*G#8FCG$*$#m#*#0G(*#($.#'m#&#VS5<5VS#6GUS671;VS$#P#Q'L&%#HD)s##US%#9s#$#NUS7;5?#2#6AAIE7;#92S85s#$S92#:J(&=%#US&#+03s#0s#).$#%2,344-5&6.7/8#*)('&%$#nR#$##KC#%#:##+#%$,%4&-'&(.)US'60$#US(8*$#US):WS*($#US+<VS,$#/2#210/.-$#+#%$,%US%s#MVS$s#I#;s#J%#-)&*.+/,#,+'s#9&%$#<Qs#4J=L+8IEH>%$#D$K'#j#$R#=H03s#]s#Vs#;JQ##s#/Ls#Cs#Bs#+HD%#&$0Hs#Q*#s#;#(&Ls#Hs#G%#D%#&$#+$Cs#Js#J#&D#,s#M2s#Ks#Ks#I1D$K$#j#$s#b#8EFD#0.Ls#Ps#O-CD%#&$#3$9s#Rs#R#CD$K#*j#%s#d#3s#qs#js#OIL##s#X8s#Vs#Vs#T*GVS:K#0Ds#d6s#ns#nEF7s#h#s#f*%#?s#l0*'#C;s#sHs#,US;H?s#tA4%$#VS#s#uJ#Ls#cH#s#as#_DG%#&$#1$H&s#d#DG%#&$#4$H)s#g#.G%#&$#7$/s#js#j#1G<Ls#eI>#s#.@G$K%#m#1#:Is#f7s#{s#cs#aUS&#+23s$2s$+s#l$#,445-6.7/8#(8'&%7$#+#%$,%4&-'&(.)US'30$#US(5*$#US)7WS*($#US+9VS,$#/2#210/.-$#+#%$,%;s$G#s#\-'&(.)/*#*)'s$6&%$#$K#s#)m#s#(#m##$9s$VPNWS<s$Ws$5#'s$X$#s$7%'C'F'E$#FC(IE(IF$M$#k##&#(EF(EC$M$#'I$#EFk##%#VS=)#(JI(JE$M$#k##(#j##'#'J$#IEk##2#j###Fj##3#WS>EFCYS?5/)$#j#&<#j#'>#j#(S-#k#&?9k#'A#k#(S-#XCs${s$Ys#'F(s$|s$Z(s$}s#)$M$#nM#$#)S@C#&#O$##SA$##Oj#*M#ZSBMs$`#NPCVSCOCl#+$O#l#,+(#l#+0-#j#,s#/#USDs#0m#$#XSEs%-s$gs#5#?RSFs$1s#7s#5#VS.s#ls#^US/#$K#s#cm#&#l#-s$vs$w#YSGHDGJI:Es$ls%$s%%s$is$gVS.$#US/#VSHs%8s$sm$N#9s%:s$u#<H#E=Ds$L>$#s%*J$K)#m#.#j#(s%9#j#.s%:#j#/s%;#j#0s%<#j#1s%8#j#2s%9#j#3s%?#j#4s%?##"). Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_unmaps); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.unfill); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.Bool.Bool.orb_false_r); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_writes); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros); constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_empty); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_set); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_ret); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fregs); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc_val); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_resv); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fcsr); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_copies); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_unmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_zeros); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_copies); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_writes); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.mkst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.regupd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_addi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.b_npc4); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@Corelib.Numbers.BinNums.N); constr:(@kc__1); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentNodes.epend); constr:(@stdpp.bitvector.definitions.BvWf)|] [|@b; @z; @x; @o; @b2; @b1; @n; @e; @H; @Hc; @Hm; @a; @r; @x8; @rom; @mem; @pc; @regs|] "#&9#-$####)#%#$#*#&#(#?#'#Q#+#u#[#y#W#,#F#G#I#8#=#U#V#Z#\#h#i#j#g#k#s#~#}#4#2#0#6#H#J#L#M#K#7#P#T#^#_#p#q#v#w#t#-#z#x#{#|#r$#$$#E#R#B#`#d#5#3#S#a#c#e#f#O#N#1#<#>#X#b#:#;#9#A#D#C#@#Y#]#l#n#o#mE#_&#`+#a%#b$#c$#d$#e$#f$#g$#h$#i$#j$#6%#k%#l%#m$#n$#o)#p(#q$#r%#s'#t&#7&#u%#v%#w%#x%#y&#z)#{&#|&#}%#~')S4US5#2#)%)#)#)#)#2#(#VS6*#2)(#US7#k##'#7((8))FC3$9%$#/I#:FCI%/E%0C;$#%2F<&#=&#>&#US#2UGFnJ#$##3C#%#$##%9H;#*<$.=,#>%#nJ#$##9##%#*#)#:)#j#$J#UDCnJ#$##=/#%#.##VS$>#VS81S%US924J3(%$#WS:s#&s#&C%s#(#;#9WS;s#)s#)C%s#+#<&#==#>'#j#%s#(#8s#/s#/EF9s#*#s#(WS<s#+%#nJ#$##s#.##%#?#4#s#/#4m#1#WS&D'CXS'EFDC#s#3$#m#&#j#&s#9#YS=s#:s#6s#0s#/#0s#1s#3US>s#97s#=#3#1&##s#;#s#5m#)#VS?s#Is#BVS(s#CIUS#s#D2s#HVS)#Q$R'M&%#GD)s#PUS*#?s#Q#O8s#Ks#KHE9s#F#s#D3S@7s#NSA3#@K4s#H&%#US+#*-5s#Zs#S+$#&/+061,2'3-4.5$*)('&%$#nJ#$##LC#%#7##*#&$+%6&,''(-)US,6/$#US-80$#US.:WS/($#US0<1$#.2$210/.-$#*#&$+%US*s#wVS)s#s#As#t%#,)'*-+.,$,+'s#6&%$#BRs#1KCM+:HEGD%$#D#L'#j#$J#CG05s$+s$$s#8KR$#s#/Ms#@s#?s#+GD&#'$/Gs#:0#s#}1#s#J$)'Ms#Fs#E&#D&#'$$,$Cs#Hs#H#&D$-s#K3s#Is#Is#G2D#L$#j#$s$1#:EFD$1/Ms#Ns#M.CD&#'$$4$:s#Ps#P#CD#L#*j#'s$3#5s$@s$9s#MHM$#s#V9s#Ts#Ts#R*IVS$L#/Ds#j0#s$51#s#^4s$:/)&#CAs$AGs#,USBG4s$BA3%$#VS(s$CK$Ms#`G#s#^s#\DI&#'$$0$G&s#a#DI&#'$$3$G)s#d#.I&#'$$6$/s#gs#g#1IBMs#bHD#s#.?I#L%#m#1#@Hs#rs$Js$$s#cs#aUS+#*25s$\s$Us#i$#+465,6-7.8$(8'&%7$#*#&$+%6&,''(-)US,3/$#US-50$#US.7WS/($#US091$#.2$210/.-$#*#&$+%As$q#s#\,''(-).*$*)'s$3&%$##L#s#)m#s#(#m##$?s%$QOWSCs%%s$2#(s%&##s$4%(C(F(E##FC%HE%HF#N$#k##&#%EF%EC#N$#(H##EFk##%#VSD)#%KH%KE#N$#k##(#j##'#(K##HEk##2#j###Fj##3#WSEEFCYSF5/)$#j#(<#j#)>#j#*S1#k#(?9k#)A#k#*S1#XCs%Is$Vs#'F%s%Js$W%s%Ks#)#N$#nN#$#%SGC#&#P$##SH$##Pj#+N#ZSINs$]#OQCVSJPCl#,$P#l#-+(#l#,0-#j#-s#/#USKs#0m#$#XSLs%Ws$ds#5#4JS%s$1s#7s#5#VS2s#ls#^US3##L#s#cm#&#l#.s$ss$t#YSMGDIKH@Es$xs%Ps%Os$is$gVS2$#US3#VSNs%bs$pm$O#?s%ds$r#BG#ECDs$LD$#s%UK#L)#m#.#j#*s%c#j#/s%d#j#0s%e#j#1s%f#j#2s%b#j#3s%c#j#4s%i#j#5s%i##"). Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma munmap_model_simple : forall (a n : word) m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  munmap_model a n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Numbers.BinNums.Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.forget_vm_ranges); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_model_next); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract); constr:(@Corelib.Init.Datatypes.app); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grants); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.maps_subtract_ranges); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps); constr:(@stdpp.bitvector.definitions.bv_sub); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@stdpp.bitvector.definitions.bv_sub_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_unmaps_grow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_grants_grow); constr:(@Stdlib.Bool.Bool.andb_false_r); constr:(@Corelib.Init.Logic.proj2); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_model)|] [|@Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__p1; @__p2; @__p3; @__p4; @__arith; @__sat3; @H10; @H9; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @__sat1; @__sat2; @__sat4; @z; @__p5; @E; @l; @b; @b2; @b1; @n; @x; @y; @m; @Hreq0; @Hlt; @Hureq; @req; @Hbr; @Hdal; @Hbal; @Hnw; @Hb0; @Hd; @h; @d|] "#5W#J$o$%#N#r$&$$#^#W##$-#J#$#&#0#.#/#-#'$/#%$+#1#+#,#2#M#)#*$:#<#;#=#(#:#?#C#4#9#>#@#A#3#8#6#B#5#E$P#7$6$>#D$Y$`#U#x$H$J$K$L$M$N$O$Q$U$[#H#Z#V#O#[#f#i#w#y#z$,$2$;#c#X$B#F$S$X$]#S#_#e#g#}$#$.$5$7$<$=$8$@$A#G#I$C$Z$b$d$f$g$h$e$c$a$_$i$^$j$k$l$m$o$n$p#P#q#~#\#a#`$($'#]#Y#k$0#j$E#{#d#h#l#m#n#o$?$G$)$9#p#T$\#R#|$3$I$R#b#u#t$1$T#v$4$D$W$V#Q#s$*$FU$A&$B+$C&#f%$D%#r%$E%$F'$G*$H%$I%$J%$K*$L%$M%$N'$O%$P%$Q%$R%$S%$T%$U)$V+$W%$X%$Y($Z$$[%$\$$]%$^&$_'$`%$a%$b%$c&$d)$e&$f$$g&$h%$i%$j%$k$#e%$l%$m$#*=$n&USWMOJ>SH>#>#>#>#>#USh#@#&IS%(%M&I#('S%-#S#USX/USX+P$#&&#(-N,#H%D#I,S,H%D#IUSiS2(3S2'I#&$,)$#(7S,-#S(E9#(:S--#S)3S)H'IS)'IH,PH'I#k##%#k##'#(s##S(3#H'I$(s#&R,#H'I#k##-#k##'#VSjs#$s##&Is#%'Is#%&Is#%k##$#k##&#'Is#*WSks#+s#*Mj##SY#j#$%#'Is#,k##SY#k#$(#(s#8P4#H%DHIUSZ#(s#<Q.#H0H#,%H-$#%D'#k##)#5)H&IH(s#EO,#H'I#&$H)$#k##(#6(H&HI(s#MS',#H&H#'$I)$#k##(#7(H(s#TS*.#H%D#Ik##?#8&H(s#YS;,#H%D#$k##s#$#.&H(s#^S6,#H4SBH.S<H0H#,S<H-$#%DS<#k##s#-#5S<H,S7H'I#&$H)$#k##s#*#6S7H,S3H&H#'$I)$#k##s#(#7S3H.S0H%D#Ik##s#>#8S0H,S/H%D#S/k##s#B#.S/H,S1H(s#}S/'I#&$s#v)$#(s$%S1-#S4'I#&$s#{)$#j##(#&(s#~(s$,S8'I#(s$.S4&#s$&USBM'IQk##s#r#JS[J#FD#FD%FDS[GD$#GD&#Q#SIUS\E#E$##E%##E&##E'##E(##E)##E*##E+##E,##E-##E.##E/##E0##E1##E2##E3##E4##E5##E6##E7##E8##E9##E:##E;##E<##E=##E>##E?##E@##EA##EB##Es####Es#$##Es#%##Es#&##Es#'##Es#(##Es#)##Es#*##Es#+##Es#,##Es#-##Es#.##Es#/##Es#0##Es#1##Es#2##Es#3##Es#4##Es#5##Es#6##Es#7##Es#8##Es#9##Es#:##Es#;##Es#<##Es#=##Es#>##Es#?##Es#@##Es#A##Es#B##Es#C##Es#D##Es#E##Es#F##Es#G##Es#H##Es#I##Es#J##Es#K##Es#L##Es#M##Es#N##Es#O##Es#P##Es#Q##Es#R##Es#S##Es#T##Es#U##Es#V##Es#W##Es#X##Es#Y##Es#Z##Es#[##Es#\##Es#]##Es#^##Es#_##Es#`##Es#a##Es#b##Es#c##Es#d##Es#e##Es#f##Es#g##Es#h##Es#i##Es#j##Es#k##Es#l##Es#m##Es#n##Es#o##Es#p##Es#q##Es#r#US]EADS#ADS,2D$S%#ADS2ADS-2D$N#2D&M#USlDUSmDRs%_;D#VS^DI*D$S&#+'GCCF#KUSnC;Ds%d;Ds%f*D$S&#+,GCCF#K$-GCCF('#RSHR#;D#*D#S&.+2GCCF#K$3GCCF.-#*D2S$1+5GCCF#K*D4S$/+7GCCF#KH8GCCFS)/9GCCF$#$:GCCF'4#*D8S$9+<GCCF#KH=GCCFR*D7S$<+?GCCF#K/@GCCF%#$AGCCF';#ZS_BGCCF=KDA5BD#=*D=S&#+s#&GCCF#K$s#'GCCF'A#;D<;DSH*D$S&#+s#+GCCF#K$s#,GCCFs#'s#&#>A;D#*D#S&s#,+s#0GCCF#K$s#1GCCFs#,s#+#*Ds#0S$,+s#3GCCF#KHs#4GCCFP/s#5GCCF$#$s#6GCCFs##s#0#Hs#7GCCFQ*D2S$s#6+s#9GCCF#K/s#:GCCF%#$s#;GCCFAs#5#KDs#:0BD#7*D7S&#+s#?GCCF#K$s#@GCCF@s#:#*Ds#:S&s#>+s#BGCCF#K*D=S&s#@+s#DGCCF#KBD>s#=VS^Ds&9WSoD#s&A*D%S$#+s#IGCCF#K*Ds#GS$s##+s#KGCCF#K*Ds#IS$s#D+s#MGCCF#K*Ds#KSC++s#OGCCF#K/s#PGCCF#)$s#QGCCF&s#K#$s#RGCCF)s#L#$s#SGCCF,s#M#$s#TGCCF2s#N#$s#UGCCF5s#O#$s#VGCCF8s#P#$s#WGCCF>s#Q#$s#XGCCFs#$s#R#$s#YGCCFs#*s#S#$s#ZGCCFs#0s#T#$s#[GCCFs#6s#U#$s#\GCCFs#=s#V#$s#]GCCFs#Es#W#$s#^GCCFs#Ms#X#$s#_GCCFs#Ts#Y#VSps#`F<S.S`VSqJS%%S.#S`m$%#WSrDIMXSsJS%$#l#%*)#l#&s#js#i#l#'s#ss#r#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/L#j#0L#j#1L#j#2L#%DS#I%DS#S%k##$#%DS2I%DS(Ik##$#&S,I&S-S,)#Rk##%#&IS-&S-S()Q#k##%#k##,SD0S)P-#S(%DS,#k##&#%DS)I%DS(S,k##$#%DRI%DQIk##$#&PI&QR)#S6k##%#&IQ&PO)S=#k##%#%DOIk###SD0S'S*-#Q%DR#k##&#-QO&#s'2&IO&IS*-S*S;'I#&$s'7)$#k##'#k##)#k##+#k##3#k##4#k##0#k##7#k##<#k##A#k##s#%#k##s#)#k##s#/#k##s#4#k##s#9#k##s#=#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/L#k#0L#k#1L#k#2L#'IO'OI'IS,'S,I(s'`S>S'&%$S-S'HS,OSE#S(S)RPQS*S;S6S?S=S1S8S4S9S:l#3s#R)#l#4s&5s&3#j#5s&7#j#6s&:#V#MJj##s&>#j##s&H#=s&Is&Hs&A#S=l#7s&LD#l#8s&ND#l#9s&Ss&P#l#:s&Xs&U#l#;s&_s&Z#l#<s&fs&a#l#=s&ns&h#l#>s&pD#l#?s&sD#l#@s&ys&u#l#As'#s&{#l#Bs',s'%#l#Cs'5s'.#l#Ds'@s'7#l#Es'Fs'C#l#Fs'Ps'K#l#4s'Xs'R#l#Gs'as'[#VSas'c#(s'}J%D#s'em#%#-s'_R(s(%S)&#Jj#HD#3RH'IR,QH'I#k##s'l#k##&#3+H'I,,s'VH'I#k##s'r#k##&#4s'VH.s'NH0H#-#s'O%Ds'Q#k##s'\#5s'SH'Is'K&s'LH)$#k##s'X#6s'PH,s'JH&H#'$I)$#k##s'V#7s'OH%Ds'GIk##s'k#8s'MH%Ds'Hs'Ik##s'n#.s'KH(s(LS?,#H4S<H.S7H0H#-#s'G%DS7#k##s'v#5S7H'Is'E&s'FH)$#k##s'r#6S3H,S0H&H#'$I)$#k##s'p#7S0H%Ds'CIk##s()#8S/H%Ds'ES1k##s(,#.S1H,S8H'Is'D)#s'?-s'?S9&s'@#j##%#&s'Bs(c'Is'A(s(nS9&#s(fADS%UStD2D$M#*Ds%RS$s%6+s%zGCCF#K$s%{GCCFs%0s%u#l#%#s$zs$tl#&'s%~#l#'s'?s&+#j#(D#j#)D#&IM-MS%&M#k##%#k#(D#k#)D#(s)%S5WJS@#S>l#3+%#l#4s'Vs'T#j#58#j#6;#V#MJj##>#j##s#$#=s#%s'aA#SBl#7s#'D#l#8s#)D#l#9s#-s#+#l#:s#1s#/#l#;s#8s#3#l#<s#>s#:#l#=s#Es#@#l#>s#GD#l#?s#JD#l#@s#Ns#L#l#As#Rs#P#l#Bs#Ys#T#l#Cs#_s#[#l#Ds#fs#a#l#Es(gs(d#l#Fs(qs(l#l#4s#os#j#l#Gs#vs#q#9Ds#{s#x#s)>J&s(}s)?Es)CI%s)CS%#USbs)EZSus)ED#N%J(s)G&%Ds)=#(s)IS#%DJ%j#HD#-s(rOZScD&$J#N%D$)3S'H'IS',S;H'I#k##s)7#k##&#3s(nH'Is(o'Is#uk##s)<#k##%#4s(_H0Hs#n-#s([%Ds(]#k##s)%#5s(_H'Is#q&s#rH)$#k##s(}#6s#vH(s)eS=,#H&H#'$I)$#k##s(|#7(H(s)lSB.#H%D#Ik##s)7#8&H(s)qS<,#H%D#$k##s)<#.&H(s)vS7,#H4S/H0Hs#r-#s(\%DS1#k##s)C#5S1H'Is#v&s#wH)$#k##s)?#6S8H,S4H&H#'$I)$#k##s)=#7S4H.S9H%D#Ik##s)S#8S9H,S:H%D#S:k##s)W#.S:H,S>H(s*6S:'I#&$s*/)$#j###SD&s%9s*2'Is#u(s*=SE&#s*5Js(iJ#FD#GD#s(hQ#SI#E#s(g#E$##E%##E&##E'##E(##E)##E*##E+##E,##E-##E.##E/##E0##E1##E2##E3##E4##E5##E6##E7##E8##E9##E:##E;##E<##E=##E>##E?##E@##EA##EB##Es####Es#$##Es#%##Es#&##Es#'##Es#(##Es#)#2Ds'xS#s$X2D#S%s'wADN2D$M#*Ds'nS&s'N+s'vGCCF#K$s'wGCCFs'Is'q#;Ds*v*D#S&s'v+s'zGCCF#K$s'{GCCFs'Ms'u#*Ds'PS$s'y+s'}GCCF#K*Ds'RS$s'w+s(#GCCF#KHs($GCCFS(/s(%GCCF$#$s(&GCCF's'|#*Ds($S$s'W+s((GCCF#K*Ds'~S$s'Y+s(*GCCF#K/s(+GCCFs'q#$s(,GCCF&s(&#ZS_s(-GCCFs'[KDs'^4BD#s((*Ds'eS&#+s(1GCCF#K$s(2GCCF's(,#*Ds'iS&s(++s(4GCCF#K$s(5GCCFs'cs(/#*Ds'fS$s'l+s(7GCCF#K/s(8GCCF#s'y$s(9GCCF:s(3#*Ds'pS$s'j+s(;GCCF#K/s(<GCCFs'f#$s(=GCCF7s(7#BDs(6s's*D#S&s(<+s(@GCCF#K$s(AGCCFs'Ts(;s'h$s(BGCCFs'Ss(<#$s(CGCCFs']s(=#$s(DGCCFs'`s(>#$s(EGCCF's(?#$s(FGCCF+s(@#$s(GGCCF0s(A#$s(HGCCF5s(B#$s(IGCCF9s(C#$s(JGCCF@s(D#$s(KGCCFs#'s(E#$s(LGCCFs#/s(F#$s(MGCCFs#4s(G#l#%#s'Ls'Fl#&s#9s(P#l#'s#>s(Y#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#/L#j#0L#j#1L#j#2L#j#IL#%DS#Mk##s'F#%DS-Ik##s'E#)s'BS)k##s'D#)Ps'@k##s'B#0S)R-#S(%DS2#k##s'B#%DS(S-k##s'?#&RI&PS))#S*k##%#&IP&RQ)S6#k##%#-S)S(%D#Ik##s'@S3k##s'A#k##s'H#k##s'I#k##'#k##*#k##/#k##4#k##7#k##<#k##?#k##B#k##s#%#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#/L#k#0L#k#1L#k#2L#k#IL#(s,*Svi#;JSDs'-s',s'+s'*S-HS,O#SwS(S)RPQS*S6S?S0S>S5S@Sdl#3s#5%#l#4s*[s*Y#j#5s$N#j#6s$Q#V#MJj##s$T#j##s$Y#=s$Zs$Ys$W#S0l#7s$]D#l#8s$_D#l#9s$ds$a#l#:s$is$f#l#;s$ps$k#l#<s$vs$r#l#=s$|s$x#l#>s$~D#l#?s%%D#l#@s%+s%'#l#As%1s%-#l#Bs%9s%3#l#Cs%?s%;#l#Ds%Es%A#l#Es+ls+i#l#Fs+vs+q#l#4s%Ms%I#l#Gs%Ts%O#l#Js%Ws%V#l#Js%_s%]#j#Js%b#USZs%cm#$#VSxs,Js,JUS]#US\$TQS#S#1#S'LJ#USJQEs,ROCs,Rs,RP#USKQ#,$#USLQUSMQUSNQUSOQUSPQ:,('&S#%$#1#S'%S+/#j#K4#DIs,)VSQ#JWSe/s%vs,+WSRS#S#PI:#1nS.#$##:&#%#%##MS#PN2#:8%#2S#10/1#S'%S+#/j#LS.#nS.#$##AJ#%#,#*:=#(7S#6541#S'%S+#4j#LS.#WSfs,pNRCs,ps,pR##s#)#s#'Is#*JA:s#%#0?S#>=<1#S'%S+#<j#Ks#-#WSfs,xS#PCs,xs,xP##s#1#s#/Is#2#s#)Ns#(J:s#.$#s#(S#s#'s#&s#%1#S'%S+#s#%j#Ks#6#@J@M@S%%#MJ(NS%(NM%D$#k##&#(S%M(S%J%D$#@N%#S%Mk##%#))#@S#%#NS%k##-#j##&#j##$Jj##/#WSyS%MJ=1+&$#j#M8#j#N:#j#OSF#k#M;/k#N=#k#OSF#?s&Ws,hVSSs-C#Es-DS'(s-E#%D#Jj#HD#?Js,jVSSs-I#%D'#j#HD#?s&^s,r-s,oS'?#s,p%DJ#j#HD#3OH,S*H'I#k##s-8#k##s(W#3s,xH'Is,yk##s-<s'{k##$#4s,dH0Hs,\-#s,`%Ds,b#k##s-%#5s,dH'Is,_&s,`H)$#k##s,}#6s,dH&Hs'v's'wI)$#k##s,z#7s'{H.s&cH%D#Ik##s-4#8s&fH,s&`H%D#s&ak##s-8#4S0H0Hs,U-#s,Y%DS/#k##s-<#5S/H'Is,Y&s,ZH)$#k##s-8#6S1H&Hs't's'uI)$#k##s-5#7S8H.S4H%D#Ik##s-K#8S4H,S9H%D#S9k##s-O#'Is'x)#s'x-s&VS5?#s&W%DS5#j##&#'Is)0&s'ls.*WSgDs%Zs+2*Ds*pS&#+s+<GCCF#Kl#%#s*;s*5l#&s($s+?#l#'s,\s+H#j#(D#j#)D#-MJ?#M%DJ#k#(D#k#)D#(s.ASdVJ#STl#3*%#l#4s,rs,p#j#54#j#66#V#MJj##s&n#j##?#=@s(9;#S3l#7s&xD#l#8s&}D#l#9s#'s#$#l#:s#,s#)#l#;s#2s#.#l#<s#8s#4#l#=s#>s#:#l#>s'>D#l#?s'DD#l#@s#Es#B#l#As#Js#G#l#Bs#Ps#L#l#Cs#Vs#R#l#Ds#\s#X#l#Es.'s.$#l#Fs.1s.,#l#4s#cs#`#l#Gs#is#e#(s.]s$i'IS5&S5s.V)$#j##s#6#FDs'%GDs-0s-.GD$#Q#SI#E#s--#E$##E%##E&##E'##E(##E)##E*##E+##E,##E-##E.##E/##E0##E1##E2##E3##E4##E5##E6##E7##E8##E9##E:##E;##E<##E=##E>##E?##E@##EA##EB##Es####Es#$##Es#%##Es#&##Es#'##Es#(##Es#)##Es#*##Es#+##Es#,##Es#-##Es#.##Es#/##Es#0##Es#1##Es#2##Es#3##Es#4##Es#5##Es#6##Es#7##Es#8##Es#9##Es#:##Es#;##Es#<##Es#=##Es#>##Es#?##Es#@##Es#A##Es#B##Es#C##Es#D##Es#E##Es#F##Es#G##Es#H##Es#I##Es#J##Es#K##Es#L##Es#M##Es#N##Es#O##Es#P##Es#Q##Es#R##Es#S##Es#T##Es#U##Es#V##Es#W##Es#X##Es#Y##Es#Z##Es#[##Es#\##Es#]##Es#^##Es#_##Es#`##Es#a##Es#b##Es#c##Es#d##Es#e##Es#f##Es#g##Es#h##Es#i##Es#j##Es#k##Es#l##Es#m##Es#n##Es#o##Es#p##Es#q#2Ds-'S#s)f2D#S%s-)2Ds)hNs-,2D$M#/s-'GCCFs'bs,m$s-(GCCFs'es,~#/s-)GCCFs,js']$s-*GCCFs'`s-$#$s-+GCCFs,Ys-%s,w/s-,GCCFs'Ss,V$s--GCCFs'js-'#/s-.GCCFs,Us'Q$s-/GCCFs'es-)#KDs,`s,~BD#s,g*Ds-*S&#+s-3GCCF#K$s-4GCCFs'es-.#*Ds'US$s,L+s-6GCCF#K*Ds-4SCs,l+s-8GCCF#K*Ds,nS$s,P+s-:GCCF#K/s-;GCCF%#$s-<GCCFs,Os-6#$s-=GCCFs,Ns-7#$s->GCCF*s-8#$s-?GCCFs,Ys-9#$s-@GCCFs,\s-:#$s-AGCCF/s-;#$s-BGCCF5s-<#$s-CGCCF8s-=#$s-DGCCF;s->#$s-EGCCFs'ns-?#$s-FGCCFs'rs-@#$s-GGCCF?s-A#$s-HGCCFBs-B#$s-IGCCFs(,s-C#$s-JGCCFs(1s-D#l#%#s,Is,Cl#&s#(s-M#l#'s#-s-V#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/L#j#0L#j#1L#j#2L#%DS2s,2k##s,5#%DPs+|k##s,##-OQ&#s0O&IS''IS*&S*s0R)$#k##&#k##'#k##)#k##s,.#k##s,/#k##.#k##s,2#k##s,7#k##s,<#k##s'a#k##5#k##s,J#k##s,O#k##s,T#k##s'r#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/L#k#0L#k#1L#k#2L#Ss+ys+xs+ws+vS-S'HS,Os%8STS(S)RPQS*S;S6S?S=S:S>S5SES@l#3s#($#l#4s/Ks/I#j#5s%I#j#6s%K#V#MJj##s)G#j##s%T#=s%Us*ns$|#S3l#7s)QD#l#8s)VD#l#9s%\s%Y#l#:s%as%^#l#;s%gs%c#l#<s%ms%i#l#=s%ss%o#l#>s)sD#l#?s)yD#l#@s%zs%w#l#As&#s%|#l#Bs&)s&%#l#Cs&/s&+#l#Ds&5s&1#l#Es0\s0Y#l#Fs0fs0a#l#4s&<s&9#l#Gs&Bs&>#VSaO#9DOs&Es%9s%8#VSSs18s&J'Is&KUSGs1:Ps14#&s&N#)&#&s&Ps15)(#<L)WSz**#j#PDJ&MJUS{#j#QD#j#PD#<Ds&YPMJXS|DDS}#<D#j#RD#j#OD#<Ds1FUSGJ<D#j#PSF#<Ds1I`S~SFDDDSGSG22$s1Rs1J#fT#DDDDDDSU333SU)s1Ls1L(;s1K#`T$DDSV4SV0s&fs&f/;s1K#ZT%>;>96#'Is&)&s&*s1N)$#j##s&.#$s.`GCCFs.2s.Zs.V*Ds.YS&s)4+s.bGCCF#K$s.cGCCFs)8s.]#$s.dGCCFs.6s.^s.;*Ds.>S&s$6+s.fGCCF#K$s.gGCCFs)<s.a#WSgDs.%s.A*Ds.fSC#+s.jGCCF#K*D%S$s.&+s.lGCCF#K/s.mGCCF%#$s.nGCCFs.#s.h#$s.oGCCFs.&s.i#$s.pGCCFs.)s.j#$s.qGCCFs./s.k#$s.rGCCFs.2s.l#$s.sGCCF.s.m#$s.tGCCFs$Gs.n#$s.uGCCFs$Js.o#$s.vGCCFs$Ms.p#$s.wGCCF5s.q#$s.xGCCF7s.r#$s.yGCCFs$Qs.s#$s.zGCCFs$Ts.t#$s.{GCCFs)^s.u#$s.|GCCF>s.v#l#%#s-{s-ul#&s$Zs/##l#'s$_s/,#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/L#j#0L#j#1L#j#2L#?s-IS*'I#&$s1~)$#k##s-N#k##s-P#k##s-R#k##s-Z#k##s-[#k##s-W#k##s-^#k##s-c#k##s-h#k##s-l#k##s-p#k##s-v#k##s-{#k##s.$#k##s.(#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/L#k#0L#k#1L#k#2L#Ss-Is-Hs-Gs-FS-S'HS,OSTs&dS(S)RPQS*S;S6S?S=S:S>S5SES@l#3B$#l#4s0ws0u#j#5s&u#j#6s&w#V#MJj##s*s#j##s'$#=s'%s,>s#T#S3l#7s*}D#l#8s+&D#l#9s',s')#l#:s'1s'.#l#;s'7s'3#l#<s'=s'9#l#=s'Cs'?#l#>s+CD#l#?s+ID#l#@s'Js'G#l#As'Os'L#l#Bs'Us'Q#l#Cs'[s'W#l#Ds'as']#l#Es2,s2)#l#Fs26s21#l#4s'hs'e#l#Gs'ns'j#XT&s$'s$%s#k#UT's2c&s'v#)s$.#m#&#WT(s2gs'y#9Ds'zs(#s$3s$2#9Ds+{s'|#s+~N(s2js(PWT)s2kS#P9Ds(+s('%$#XJs2ms(ys(S#l#Ds(2s(/#Es2oQ%s2o#s(^USJOCs2qs2qQJUSKO#s)+$#USLOUSMOUSNOUSOOUSPO:+('&S2%$#1#S*Cs2{s2{Qs(:#s)4#,:/#+*S2)('1#S*%S+'#j#Ls3$#<S+s)(ZScs3&s)3$#s(iJl#D86#USJPUSKPIs)>s(s#USLPN#s)>USMPUSNPUSOPUSPP:+)'&N%$#1#OCs33s33Rs###s)H#-:/#,*N)('1#O%S+'#m#3#MNR3QH,S'H'I#k##s2~#k##s1l#3s2fH'Is2gk##s3&s2Yk##$#4s2UH0Hs2N-#s-d%Ds2Q#k##s2k#5s2SH'Is2N&s2OH)$#k##s2g#6s2SH&Hs2N's2OI)$#k##s2d#7s2SH.s-fH%D#Ik##s2z#8s-iH%Ds,Ps,Qk##s2}#4S3H0Hs2E-#s-`%DS0#k##s3%#5S0H'Is2F&s2GH)$#k##s2}#6S/H&Hs2G's2HI)$#k##s2z#7S1H.S8H%D#Ik##s34#8S8H%Ds,IS4k##s37#)s-as2C's-as,Yj##$#*Ds0RS$s0q+s0zGCCF#K*Ds0TSCs0s+s0|GCCF#K$s0}GCCF%s0w#l#%#s/|s/vl#&s-es1$#l#'s2As1-#j#(D#j#)D#&JM'MS%k##$#k#(D#k#)D#(s4&S@WJs2Y#S/l#3*%#l#4s2Ws2U#j#5s,M#j#6s,R#V#MJj##s-x#j##s-{#=s-|s2^;#S7l#7s(eD#l#8s(jD#l#9s##A#l#:s#(s#%#l#;s#.s#*#l#<s#4s#0#l#=s#:s#6#l#>s)'D#l#?s),D#l#@s#@s#>#l#As#Es#B#l#Bs#Ks#G#l#Cs#Qs#M#l#Ds#Ws#S#l#Es3hs3e#l#Fs3rs3m#l#4s#^s#[#l#Gs#ds#`#WT*NR#9s*Us*Ts)}s#hs#g#WSRNNRZT+NNRJS(M9s*Xs*2s*-%$#DIs4#VSQ#SAUT,$9S.SAs*9&$#Ds4@s4'%S.#SA's3ss-bk##$#'s4+s4DDs-es3v%S.#SAk##%#VT-s4Hs4/XT.($#59S.SAs*I-,#OP(s4W#DI#Ds4N$VSQ$#WSes$3s4P&WSRNN(Is*p#s$5nS.#$##s*p&#%#%##MN+Ns$6#:s$:%#s$5Ns$4s$3s$21#O%S+#s$.m#1#TPNN1#O%S+#s$2m#&#Ls*z%%S+#s$5m#%#9s*~s*}s*l#s$4s#,L0)%S+#s$9m#%#USWOO#MN#T%NN1#OL%#%S+#s$Am#*#m##$WT/NNO%S+#s$Em#%#l#Ss+4s+5#l#Ts.>s.=#l#Us/]s/^#l#Vs4hs4~#l#Ws4ps4l#j#Xs4r#j#Ys4u#j#Zs4y#j#[s5$#j#\s5'#l#Ls51s5)#l#]s53T0#j#^D#j#RS+##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool := grant_ok_na_pin m a n.

Lemma grant_ok_na_of_pin : forall hint m a n, grant_ok_na_pin m a n = true -> grant_ok_na hint m a n = true.
Proof. intros. exact H. Qed.

Lemma grant_ok_na_pin_of_grant_ok : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok, place_ok in H. unfold grant_ok_na_pin.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma grant_ok_na_pin_of_gate : forall hint m a n,
  grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true.
Proof. intros. exact H. Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na, grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. auto.
Qed.

Lemma grant_na_pin_not_errno : forall m a n,
  (0 <= n)%Z -> grant_ok_na_pin m a n = true -> a <> errno_ret ENOMEM.
Proof.
  intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  intros E. apply (f_equal bv_unsigned) in E.
  rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
  alloc_top_bounds. unfold two_pow_64, ENOMEM in *. lia.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma mmap_noaccess_outcome_si : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_err_out model o
    \/ exists a, grant_ok_na_pin model a n = true
                 /\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (noaccess_model a (Z_to_bv 64 n) model) [].
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.mmap_noaccess_args_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.grant_ok_na_pin); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.noaccess_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_222); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_sysno_si); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_noaccess_outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b); constr:(@Corelib.Init.Logic.eq_refl); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_b); constr:(@Corelib.Init.Logic.eq_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_add_lazy); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Logic.conj); constr:(@kc__2); constr:(@Corelib.Init.Logic.or_introl); constr:(@kc__3); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.proj2); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Stdlib.ZArith.BinInt.Z.eqb_eq); constr:(@Corelib.Classes.Morphisms.iff_impl_subrelation); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Classes.Morphisms.subrelation_proper); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Program.Basics.impl); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Classes.Morphisms.subrelation_respectful); constr:(@Corelib.Classes.Morphisms.subrelation_refl); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg5_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg4_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg3_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg2_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg1_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg0_si); constr:(@kc__3 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@a; @o; @n; @lemma; @b; @nZ; @h; @He; @H; @G4; @G3; @G2; @G1; @x; @B; @A; @m; @Hg; @E1; @H5; @H4; @H3; @H2; @H1; @Hno; @model; @x8; @ms|] "#6e#Z$q###|#~#o#$#t#%#d#&#9#:#Z#'#(#u$=#=#)#;#x#+#,#0#4#/#5#*#-#2#8#<#3#.#1$0#m#>#E#6#7$Q$S$T#?#F#Q$i#a$&#b#A#D#P$b$g$o#p$j#_#^#f#j$3$4$P$R$W$^#@#B#C#H#I#J#L#M#N#O#R$c$d$e$a$`$_$]$f$k$m$h$l#Y#h#q#s$'$*$+$-$.$/$5$8$9$6$;$O$U#G#K$n$p$q#X$V$r$s$t$u$v$w#]#c$(#k$X$#$@$B#n#{$?#e$)$$$:#y$H$G$[$A$D$E$C$I$J$K$L$M$N$7#z$<$>$Y$Z#i$2$1#`#r#w#g#v#}$,$\#l$%$FU$A&#[%$B&$C%$D%$E'$F%$G&$H%$I%$J%$K%$L'$M)$N$$O%$P+$Q%$R%$S$$T$$U$$V&$W$$X$$Y$$Z$$[$$\$$])#1%$^%$_%$`%$a%$b%$c($d%$e,$f$$g$$h&$i$$j&$k&$l&$m'$n$$o$$p'JSBJ#J#J#J#J#USM#USN#.$GMSBJ#M#M#M#M#J#USO##J+#USoKRS6&O#+1F#1$#USP#R'&O##5#'R%&O#M=J#USO#+<##<'#R)&O#USpSB+A##A%#R'&O##s#$#6$&#$,#$4#$8#&P=.s#+#K#USqHLS&S-S$N#PCBPCOS$CI#D#EUSMs#7USN#USr#VSCs#5#S#VSCs#7s#7S#+s#:I/s#:s#:C#%&#%SSsVSCs#=StS#0C+)&%#PC)S$SSu(H%$##9G#$5#j#$s#E#,s#F#2:#A<#k#%?#l#&AJ#j##s#%#&Ps#;#s#M#s#?&Ps#:#s#O#s#6&Ps#5#s#Q#s#3&Ps#2#s#S#s#E$%#$(#$+#&S$s#K#s#X#s#JUSP#&S-s#I#s#[#s#M&S-s#H#s#]#s#D&S-s#C#s#_#s#A&S-s#@#s#a#s#S$%#$(#$+#&S's#T#s#f#s#X&S's#S#s#h#s#O&S's#N#s#j#s#L&S's#K#s#l#s#^$%#$(#$+#&S(s#d.s#r#K#LS&S3S.N#S(CBS(COS.CI#D#EPCs#AS.(Hs#<#s#:#s#PG#$&#j#$s#|#,s#}#2+#A-#k#%s#V#l#&1J#j##5#&S(s#o#s$(#s#k&S(s#j#s$*#s#h&S(s#g#s$,#s#z$%#$(#&S.s#z#s$0#s#~&S3s#y#s$2#s#u&S3s#t#s$4#s#r&S3s#q#s$6#s$($%#$(#&S+s$%#s$:#s#}&S+s#|#s$<#s#z&S+s#y#s$>#s$0$%#$(#&S)s$5.s$C#K#LS&S/S4N#S)CBS)COS4CI#D#EPCs#nS4(Hs#i#s#g#s#}G#$&#j#$s$M#,s$N#2+#A-#k#%s$'#l#&1J#j##5#&S)s$9#s$U#s$7&S)s$6#s$W#s$I$%#&S4s$E#s$Z#s$A&S/s$@#s$\#s$>&S/s$=#s$^#s$P$%#&S2s$E#s$a#s$C&S2s$B#s$c#s$U$%#&S*s$Y.s$g#K#LS&S9S,N#S*CBS*COS,CI#D#EPCs$6S,(Hs$1#s$/#s$EG#$&#j#$s$q#,s$r#2+#A-#k#%s$K#l#&1J#j##5#&S*s$X#s$y#s$k&S,s$_#s${#s$]&S9s$\#s$}#s$o&S:s$r.s%$#K#&Ls$uXSvs%'#s$tS/USw$#D#S5m#%#LS&MLN#S0GH$S6H%s$}H&s$yH's$wH(s$qH)s$mI('&%$#*S0GA*#LS&S%MN#LIH$S6H%s%+H&s%'H's%%H(s${H)s$wI('&%$#*LIBLIOMCO#D#E+s%AO/s%As%AC#%s$i#s$h0Cs$ks$i#s$es$cPC&M(H$#s$b#s$xK#$*#j#$s%H#,s%I#2/#VSxN#]SQNQSR92C$$#j#'<#.s%OC#J#s%Fj#(s%P#USys#)WSzS&ML@s%SL%S:$#XS{s#,S0G#&MS6ICA@?>=s#$LIA#/j#(s%X#&Ms%M&S%S6I#Cs#%s#$s##Bs#)LIA#4j#(s%]#&Ms%M&S%s%SI(#Cs#)s#(s#'s#.LIA#9j#(s%b#&Ms%O&S%s%SI-(#Cs#-s#,s#3LIA#>j#(s%g#&Ms%M&S%s%UI2-(#Cs#1s#8LIA#s##j#(s%l#&Ms%M&S%s%SI72-(#Cs#=LIA#s#(j#(s%q#1S0.s%t6K#+s%vC&S#S6&S#s%k&S#s%g&S#s%e&S#s%_&S#s%[LS&S#S1I)('&%$#S%OBS%OCs#3R#J#FDFs#5)s#6I6K-$#7K8K9s%R$#*#CG#D#E$(#$,#$.#/s&1s&1CG%s%Y#s%X0Cs%[s%Y#s%Us%S&S7s%|%s%\&-:K%s%^(#;K<K=K>K?K36*('&%$#4#S1T-CG#(H/#s%]#s%sP#$4#j#$s&C#,s&D#2s#%#As#'#l#&s#0s&G#l#)s#2J#l#*s#5S|#&S%s&*Is#Os#Js#Es#@s#;#s#uLI&S1s&@.s&N#K#)s#_#1M6#-%#7%8&9s%|$#+s&W**$C##D#E$)#$s#7#$s#9#/s&\s&\C(%s&(#s&'0Cs&*s&(#s&$s%~&S1s&K%s&+&.:3%s&-(#;5<6=7>8?937*('&%$#4#MT-C6#(H/#s&,#s&BK#$4#j#$s&n#,s&o#2s$5#]SQNQSRs#(#Cs$)s$)s$(j#'s#+#USSC#D#Ej#(s&u#VS;DEUSSs&i#D#Em$%#@s&zs&l'#s#kKUSTC#D#Ej#(s&}#USTs&e#D#Em$,#@s'%s&h&#s#|S'WS<Cs#ws#:#D#S5j#(s'(#WS<s&wCs#=#D#S5j#(s'+#WS<s&zs&oC#D#S5j#(s'.#VS;DS5WS<s&~s&ss&~#D#S5m$%#@s'3s'%'#s$$K@s'4s&w+#s$/S'@s'5s''/#s$5S+WS=Cs$+s#J#D#Ej#(s'8#WS=s'+Cs#M#D#Ej#(s';#WS=s'.s'#C#D#Ej#(s'>#WS=s'1s'&s'1#D#Em$s#)#@s'Bs'4&#s$3K@s'Cs'**#s$>S'@s'Ds'6.#s$DS+bS}s$Ns$Js$Es$@s$;s$6s$yS0Gs#)BC2#TGCs#Ns#;(Hs#G#s&d#s&zK#$s#L#j#$s'J#,s'K#2s$m#A#s$aj#(s'N#US~s'6#DS5#m$s#$#BMK)s$cP1S%6#-%#7%8&9s'$$#+s'[P*$C##D#E$)#$s$;#$s$=#/s'`s'`C(%s',#s'+0Cs'.s',#s'(s'&%s'.%-:2%s'0'#;4<5=6>7?836*('&%$#4#S%WSUC5#nD#$##SDG#%###$(H/#s'0#s'FO#$4#j#$s'r#,s's#2s#$#Es$TFFFs%*'$#5s#'s#%'$#'#A#D#E(H<2s'=#s'SO#$%#j#$s(##,s($#2s#1#A0#j#(D#)s%8O-#s$6*s$3Cs%H#D#E$%#$s$f#$s$h#%s'Vs%Ls$9%s'Ws%Ms$-3s$<$#s$,s$+s$*s$)s$(4#M(Hs%N#s'P#s'fK#$)#j#$s(6#,s(7#2s%Y#k###654s$G'B#'#4#D#E$#,j#$s(?#,s(@#2s%b#$s#As##j#$s(C#,s(D#2s#Q#k##'#)s%WS$1S16#5%#'s#2#7&8'9s'u$#+s(PS$*$C#'(##D#E/s(Ss(SC&%s'{#s'z0Cs'}s'{#s'ws'u%s'}%+:1%s(#'#;3<4=5>6?734*('&%$#4#S1(H-#s'}#s(7P#$2#j#$s(c#,s(d#2s%E#j##s###BS1P)s%xS-1S#6#5%#'s#S#7&8'9s(:$#+s(qS-*$C#'(##D#E/s(ts(tC&%s(@#s(?0Cs(Bs(@#s(<s(:%s(B%+:1%s(D'#;3<4=5>6?734*('&%$#4#S#(H-#s(B#s(XS$#$2#j#$s)(#,s))#WSVA#Cj#+s%g#U#Cj##s$9#-s#Es#C#Ds#=E$$#$s%j#$s%l#$#s#0j#$s)4#,s)5#-s#,s#*#Ds#$E$$#$s%r#$s%t#$#7j#$s)<#,s)=#BS#S$)s&OS'1S76#5%#'s$*#7&8'9s(m$#+s)HS'*$C#'(##D#E/s)Ks)KC&%s(s#s(r0Cs(us(s#s(os(m%s(u%+:1%s(w'#;3<4=5>6?734*('&%$#4#S7(H-#s(u#s)/S-#$2#j#$s)[#,s)\#2A#j##s###-B@#D:E$$#$s&?#$s&A#$#-j#$s)e#U#C)s&wS(1S>6#-%#7%8&9s)8$#+s)oS(*$C##D#E$)#$s&O#$s&Q#/s)ts)tC(%s)@#s)?0Cs)Bs)@#s)<s):%s)B%-:2%s)D'#;4<5=6>7?836*('&%$#4#S>(H-#s)B#s)XS'#$2#Cs*'R#J#FDFs*))s**S.1SW6#-%#7%8&9s)X$#+s*3S.*$G##D#E$)#$.#$0#/s*8s*8G(%s)`#s)_0Gs)bs)`#s)\s)Z%s)b%-:2%s)d'#;4<5=6>7?836*('&%$#4#SW(H-#s)b#s)xS(#$2#BSES.)s'YS+1SX6#5%#'s%4#7&8'9s)w$#+s*RS+*$C#'(##D#E/s*Us*UC&%s)}#s)|0Cs*#s)}#s)ys)w%s*#%+:1%s*%'#;3<4=5>6?734*('&%$#4#SX(H-#s*##s*9S3#$2#j#$s*e#,s*f#2A#j##s###+s*jS3/s*js*jI#%s*6#s*50Is*8s*6#s*2s*01SE7#8$%s*;(#:&%s*=*#;(<)=*>+?,3,*('&%$#4#SE(H0#s*;#s*QS.#.s*}KC#R#J#FDF%)&S+-#s#8*s#4Ks#3#D#E$%#$(#$*#.s+,OC#R#J#FDF%)&S)1SY6#-%#7%8&9s*\$#+s+7S)*$O##D#E$)#$.#$0#+s+=S4/s+=s+=P#%s*e#s*d0Ps*gs*e#s*as*_1SF7#8$%s*j(#:&%s*l*#;(<)=*>+?,3,*('&%$#4#SF(H0#s*j#s+$S)#BS8S4)s(`S21S?6#5%#'s&;#7&8'9s*~$#+s+YS2*$C#'(##D#E/s+\s+\C&%s+(#s+'0Cs+*s+(#s+$s*~%s+*%+:1%s+,'#;3<4=5>6?734*('&%$#4#S?(H-#s+*#s+@S/#$2#j#$s+l#,s+m#2A#k##s###j##s#7#.s+rPDF#)$S46s#6-$#9s+As#7s#6*#Ps#=#D#E$&#$*#.s+|S$C#R#J#F.s,#S-DF#)$S2-#s#1*s#-S-s#,#D#E$%#$(#.s,+S'DF#)$S*1T#6#-%#7%8&9s+Y$#+s,4S**$S'##D#E$)#$.#+s,9S,/s,9s,9S(#%s+a#s+`0S(s+cs+a#s+]s+[1SZ7#8$%s+f(#:&%s+h*#;(<)=*>+?,3,*('&%$#4#SZ(H0#s+f#s+|S*#BS[S,)s)\S:1S\6#5%#'s'7#7&8'9s+z$#+s,US:*$C#'(##D#E/s,Xs,XC&%s,$#s,#0Cs,&s,$#s+|s+z%s,&%+:1%s,('#;3<4=5>6?734*('&%$#4#S\(H-#s,&#s,<S9#$2#j#$s,h#,s,i#2A#k##s###j##s#7#.s,nS()#S,6s#5-$#9s,<s#6s#5*#S(s#<#D#E$&#.s,vS.DF#.s,xS3)#S:-#s#-*s#)S3s#(#D#E$%#.s,~S+)#S01T$6#-%#7%8&9s,O$#+s-*S0*$S+##D#E$)#+s-.L/s-.s-.S)#%s,V#s,U0S)s,Xs,V#s,Rs,P1S]7#8$%s,[(#:&%s,]*#;(<)=*>+?,3,*('&%$#4#S](H0#s,[#s,qS0#BS^L)s*QS%1S_6#5%#'s(,#7&8'9s,o$#+s-JS%*$C#'(##D#E/s-Ms-MC&%s,u#s,t0Cs,ws,u#s,qs,o%s,w%+:1%s,y'#;3<4=5>6?734*('&%$#4#S_(H-#s,w#s-1M#$2#j#$s-]#,s-^#2A#k##s###j##s#7#9s--s#2s#1*#S)s#8#D#E.s-fS4)#M1S^6#-%#*s#$S/s###D#E+s-mS1/s-ms-mS2#%s-9#s-80S2s-;s-9#s-5s-31S`7#8$%s->(#:&%s-@*#;(<)=*>+?,3,*('&%$#4#S`(H0#s->#s-TS%#+s.$S#/s.$s.$S*#%s-L#s-K0S*s-Ns-L#s-Hs-F1SG7#8$%s-Q(#:&%s-S*#;(<)=*>+?,3,*('&%$#4#SG(H0#s-QBS@C)s+FS>1Sa6#5%#'s(}#7&8'9s-d$#+s.?S>*$C#'(##D#E/s.Bs.BC&%s-j#s-i0Cs-ls-j#s-fs-d%s-l%+:1%s-n'#;3<4=5>6?734*('&%$#4#Sa(H-#s-l#s.&G#$2#j#$s.R#,s.S#2A#j#%s.+#BSGs#$)s+gS71S@6#5%#'s)B#7&8'9s.)$#+s.`S7*$C#'(##D#E/s.cs.cS,&%s./#s..0S,s.1s./#s.+s.)%s.1%+:1%s.3'#;3<4=5>6?734*('&%$#4#S@(H-#s.1/s.qs.qC4%s.=#s.<0Cs.?s.=#s.9s.7%s.?%9%s.@&03<$#/.-,+4#S@(H'#s.9#s.O+#$:#j#$s.{#,s.|#.s.~S,FF#'C#)%S75#s#*'%#*s#'S,s#&'$##D#E#s.\88$$#j#(D#'EC'#+'#*#D#E$#)j#(D#'EE'#C'#0#D#E$#/j#(D#'(E'#C#D#E$#4j#(D#''E#D#E#s.rs#js#jVS;s.ss#kQ%$s+*#9s.js#ys#x*#S*s$#@DE*%#G.s/GS*)#S#6s$#5$##D#E-s#)s#Pk##$#-('#Ds#+Ek##$#VSb+*XSH'$#I@DE</+#FF/#D#EDFs#6k##$#DF3#Ds#8Ek##$#VScF6XSH'$#S$@DEs#,,+#C9RE#F#D#ECs#AR#J#Fk##%##J(FE&F#D#Ek##%#VSd,FXSH($#S.@DEs#?/-#XSes/js#MS*#WSfs#ss#M#@s/Bs$:s#u#S1Cj#,s$M#j#-s$a#j#.s$d#V#GCj##s$k#j##s%O#Gs%Ps%Js$p#Cj#,s%V#j#/s%]#V#GCj##s%a#j##s&O#Gs&Ps&Es%k#Cj#,s&S#j#0s&\#V#GCj##s&a#j##s'S#Gs'Ts'Gs&m#Cj#,s'X#V#GCj##s'e#j##s(N#Gs(Os(@s'z#Cj#,s(`#j#$s0*#V#GCj##s)$#j#1s0-#YSgs0.s)Ps).#Cj#,s)X#U#Cj##s*K#ZShs+>s*Ls**s)c#Cj#,s*Y#2s,ps)]j##s*n#WSVs*-s)WCj#+s,s#U#Cj##s+E#,s0:s)32s)[#j##s)q#Us)@C5s)5s)3's+&#'#s)/#D#E$#s(zEs(yFFFs0C'$#5s(ys(w'$#'#s(s#D#E$#s(b-s(`s(^#Ds(XE$$#$s-+#$s--#$#s(Kj#$s0Q#,s0R#2s(i#j##,#Es(6FFFs(8'$#5s(6s(k'$#'#s(6#D#E/s0\s0\Os((%s0(#s0'0Os0*s0(#s0$s/~%s0*%s(-:s(2%s0,'#;s(4<s(5=s(6>s(7?s(83s(6*('&%$#4#SY(H-#s0*#s0@S+#BS8C-s'zs'x#Ds'rE$$#$s-L#$s-N##s0GGs'f$$#j#$s0s#,s0t#2,#j#%s0L#BSFs(,)s.,S/1S86#-%#7%8&9s0I$#+s1$S/*$C##D#E$)#$s-`#$s-b#/s1)s1)S$(%s0Q#s0P0S$s0Ss0Q#s0Ms0K%s0S%-:2%s0U'#;4<5=6>7?836*('&%$#4#S8(H-#s0S/s17s17C6%s0_#s0^0Cs0as0_#s0[s0Y%s0a%;%s0b&03>$#/.-,+4#S8(H'#s0[#s0q+#$:#j#$s1A#,s1B#Cs(0RE#FFFs(2'$#5s(2s(1'$#'#s(0#D#E#D%E$#s(2A%#Es(0FFFs(2'$#)s(4S/5#s#6'%#*s#4S$s#3'$##D#E#D&E#D&E$$#WSi&#Cj#'0#VSI6s(CV$#G#D0E#D/E$$#A,#k#2NNk#3N#k##NNXSANNQQXSAN$Q#XSANNQSjXSAN(Q#VT%NQ\SkNNQQ#QSjSi\SkN+QQ$(&#Cs(LRE#FFFs(N'$#5s(Ns(|'$##D#E#D&E#D&E$$#WT&NQT'XSJNQ#s(RaSl74SKSL2Sm/(%Cs(Ss(S#j#':#VSIs#,s#*V$#C$>s#&#D2E#D2E$$#A/#Cs(YRE#FFFs(['$##D#E5s(\s(Z#D#E$%##D)E#D)E$$#$#'XSJNQ9(ZSL+%C))#XSJNQ;s(\aSls#/s#,SKSLs#*Sms#'*&$s(]s(]#j#'3#VSIs#'s#&V$#C$7B$#s(p$,s(cCs(,R#J#FDFs(.$#s(($%##s1rs(Us(U$$#j##*#Cs(,RE#F#D#EFFs(/#D#E$%#)s(2S91S[6#5%##D#E$(#Cs(6RE#F#D#EFFs(9#D#E$%#5s(;s(e#D#E$%#.s2YS)C#R#J#FDF%)&L6s(.-$#$#s'Y$'#$)##s28s(&s(&$$#k##s(;#j##0#5s(Fs(D#D#EE1F#D#EFF4#D#E$%#Cs'fRE#F#D#EFFs'i#D#E$%#.s2tS/)#S%5#s(4#D#E9s2Bs'ds'c*#S2s'j#D#E#Ds&8E$s&0#$s&'#$s%x#$#s&@k##(#k##,#j##1#FF1#D#E.s3)S2C#RE#F#D#E*s'MS9s'L#D#EEGC#D#E#JIGk##$##JGCEIG#D#Ek##%#$'##JKIk##&#j##%#EKI#D#Ek##.#j###Gj##/#VSdGCG1-)$#j#4J#j#&J#k#4J4k#&J#.s3FS0C#RWC#FO#J$FFGC#D#EDIGk##$#DGCFIG#D#Ek##%#$'#DKIk##&#j##%#FKI#D#Ek##.#j###Gj##/#VScGCG1-)$#j#4J#j#&J#k#4J4k#&J#.s3aMWCF#PDF$5GC#D#E-IGk##$#-GC5IG#D#Ek##%#$'#-KIk##&#j##%#5KI#D#Ek##.#j###Gj##/#VSbGCG1-)$#j#4J#j#&J#k#4J4k#&J#.s3{S1)#S81T(6#WC%#S$-&$.s4%S#C#R#J#FDF%)&S?1Sn6#-%#7%8&9s3U$#+s40S?*$S###D#E$)#$.#$0#/s45s45S#(%s3]#s3\0S#s3_s3]#s3Ys3W%s3_%-:2%s3a'#;4<5=6>7?836*('&%$#4#Sn(H-#s3_#s3u##Q;5CS$Q@5I#QB5O#VS;s3y'Q6'$#l#.s#)s#(#l#,s#1s#/#l#/s#Hs#G#l#,s#Ms#K#l#0s#ds#c#l#,s#js#h#j#-s$$#j#.s'`#j#/s'[#j#0s$)#V#GCj##s$/#j##s$D#Gs$Es$Cs$3#Cj#,s$I#V#GCj##s$P#j##s$d#Gs$es$cs$T#Cj#,s$l#V#GCj##s*I#j##s%1#Gs%2s+-s$|#Cl#5s%,s%*#l#5s%Es%D#l#5s%ds%u#XSes4ds&%P#WSfs&Ls&%#@s4<s+ws&N#S)Cj#,s&[#j#5s&k#V#GCj##s,M#j##s'$#Gs'%s-(s&v#Cj#,s'-#j#$s4n#V#GCj##s'5#j#1s4q#YSgs4rs.Ls'8#Cj#,s.m#U#Cj##s/S#ZShs0&s/Ts'Cs'?#Cj#,s/8#Qs/As/4s'G#ZT)DS5s/T#s0,Cl#,s0+s0,#BS0G)s20s1f1L6#-%#7%8&9s4M$#+s5(s1m*$C##D#E$)#$s1d#$s1f#/s5-s5-C(%s4U#s4T0Cs4Ws4U#s4Qs4O%s4W%-:2%s4Y'#;4<5=6>7?836*('&%$#4#LWSUC5#nD#$##SDs0J#%###$(H/#s4Y#s4oI#$4#j#$s5?#,s5@#2s#$#)s2RK5#s##'s0+#+s5FK*BC#'%##D#E/s5Is5IC&%s4q#s4p0Cs4ss4q#s4ms4k%s4s%s#)%s4t&>3s#,$#=<;:94#L(H'#s4m#s5'I#$,#j#$s5S#,s5T#2s#8#A7#m#s#;#Ts5?Cs#3A(Hs#,#s4v#s50I#$s#1#j#$s5\#,s5]#2s#A#OLCK#D#EPC>L(H9#s5##s59I#$&#j#$s5e#,s5f#2s#J#A,#m#4#@s5js5Qs0z#s2eS'Vs1Ws1(#WT*S&ML@s5ms2^s2Z$s3>#WT+S&ML@s5os2es2a$s3A#WT,S&ML@s5qs2ls2h$s3D#WT-S&ML@s5ss2ss2o$s3G#WT.S&ML@s5us2zs2v$s3J#WT/S&ML@s5ws3$s2}$s3M#Vs3-s3&#l#6s3Rs3S#j#%s5P#l#&s3YJ#j#7s3]#j#8s3`#V#GCj##s3d#j##s3}#Gs3~s3|s3h#Cj#,s4%#j#9s4+#V#GCj##s4/#j##s4N#Gs4Os4Js46#Cj#,s4R#j#:s4[#V#GCj##s4_#j##s5(#Gs5)s4}s4i#Cj#,s5,#j#;s58#V#GCj##s5=#j##s6&#Gs6's5ns5J#Cj#,s6-#j#<s6/#j#=SD#j#>s6;#j#?T0##"). Qed.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> a <> errno_ret ENOMEM.
Proof. intros hint model a n Hn Hg. exact (grant_na_pin_not_errno model a n Hn Hg). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_err_out model o
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.S); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.page_round_up_Z_bounds); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.mprotect_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_226); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_sysno_si); constr:(@Corelib.Init.Logic.eq_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_model_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_expose_outcome); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_grows_conflict_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@Corelib.Init.Logic.f_equal); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_modeled_b); constr:(@Corelib.Classes.RelationClasses.reflexivity); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.mprotect_model_next_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg2_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg1_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg0_si)|] [|@__ff; @__varmap; @__wit; @__x1; @__arith; @r; @q; @H6; @H5; @H4; @H3; @H; @__sat9; @Ha; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__p1; @__p2; @H9; @H8; @H7; @__sat10; @__sat11; @b; @lemma; @m; @z; @E; @Hu1; @Hlen'; @o; @Hma; @Hna; @n; @H2; @Hnw; @Hlen; @H1; @Hal; @H0; @Hno; @len; @addr; @model; @x8; @ms|] "#+7#B$i#K#w#S#T#x#v#2###3#&#~#p#%#[#)#-#.#_#1#(#4#B#$#|#*#b#+#Q#,#/#0#5$8$;$I#I#Z#'$$$F#7#:#J$`#G#F#]#`#g#6#q$'$*$.#;#<#=$5$B#@$H$G$O$W$Y$L$M#M$]#a#s#u$#$%$($)$&#c$+$,$-$/#8#9#>$7$6$:$>$@$A#A$0$E$D$U$V$X$[$\$Z$a$c$b$d$e$_$f$g$h$i$j$k#E#L#W#e#k$1#z#y#t#R$3#H#P$C#U#X$4$J#V#i#}#Y$Q$N#o$2$K#N#h#r$9$P$T$R$^#O#\#d#f#j#l#m#n$<#^#{$=$?$SU$9&$:%$;%#f%$<%$=&$>'$?*$@+$A%$B&$C$$D%$E)$F$$G%$H%$I)#J%$J%$K%$L%$M$$N'$O%$P$$Q%$R%$S$$T%$U%$V'$W&$X'$Y)$Z&$[$$\&$]%$^%$_%$`%$a%$b%$c*$d$$e%$f)$g&$h%.S6.#.#.#.#.#US?#US@#&$LGS6G#.#.#.#G#.#?##C+#/S&S.#.#O,.E#C#F1S./S+#64L#4$#$FS8&7Q9S&2$#$#S71+/R#?:6>##>%#9S+6A#PRUSA#H#S/J#P#S$PS#USB#H#RS)#P#S$USXS,&s#+S0I#E%F$%FE&s#/S%,#E%F#k##&#k##(#&s#4S1J#E#CEFUSC#7+E@E#2#,#C.#k##'#K0E$FE&s#?I,#E%F#$$E'$#k##(#L(E$EF&s#GK,#E$E#%$F'$#k##(#M(E&s#NS'7#E#C#Fk##=#N&E&s#SS2,#E#C#$k##B#7&E&s#XSD,#E<NUSENACS)USYCUSZCQCF8CS6)C$S*#*&HDDG#MUS[D)C'S9&*)HDDG#M+*HDDG&%#VS\+GVSFPS$VS]JO#P#S$m$%#WS^CFS)XS_JO$#l#$*)#l#%54#l#&87#j#'C#$FJ%FS)k##$#k#'C#VJS;Il#(($#l#)AC#l#*s#$C#l#+s#*s#&#l#,s#0s#,#l#-s#9s#2#l#.s#Bs#;#l#/s#Ks#D#l#0s#Us#N#VS`S##9S#%S##2S#E?S6VSG$#%'#''#USaS1%Fs#W?s$4?s$0VSb$#$s#[#''#VSc'&$F(%F($F(k##$#k##&#%F-WSd.-S)j##SH#j#1%#%F/k##SH#k#1(#Is#WE%Fs#X%Fs#Lk##s#s#k##%#Js#UE@Es#M2#s#Q#Cs#S#k##s#p#Ks#UE%Fs#P$s#QE'$#k##s#n#Ls#UE&s$PS;,#E$E#%$F'$#k##s#m#M(E&s$WSe7#E#C#Fk##s$&#N&E&s$\Sf,#E#C#$k##s$+#7&E&s$aS<,#E&s$cSI%F#$$s#7'$#$SIS7j##$#&s$iSJ$#s#<&s$kSK%F#&s$mSg$#s#@US#S)%FS&k##s$E#1s$Y1#1#1#1#1#1#3C#UShS6VSiC#3C)WSLC$#-C'#=#S33C/3C1-C$#-C,#=#S31/3C#-C#'=#S3-C%.=#S33Cs$r3Cs$|WSLC4#3CS.-C$#-C'#-C3#-C.#=#S33CB-C,)-C8#-C%#=#S3(N#s$A(N$#(N*#(N+#(N,#(N-#(N.#(N/#(N0#(N1#(N2#(N<#(N?#(Ns#$#(Ns#*#ACS+USjCBC$L#ACS&BC$O#ACS8ACQBC$S+#BC&S)#8Cs%Q)C#S4s$U*s$WHDDG#M8Cs%]Gs%_8C#)C%S4#*s$\HDDG#M+s$]HDDG(s$X#8Cs%b)C#S4s$^*s$`HDDG#M+s$aHDDG,s$\#)C/S*s$a*s$cHDDG#M)C1S*.*s$eHDDG#MRs$fHDDGS/Os$gHDDG$#+s$hHDDG's$c#)Cs$hS*6*s$jHDDG#MRs$kHDDGR)C6S*9*s$mHDDG#MOs$nHDDG%#+s$oHDDG's$j#ZSks$pHDDG;WSlC>5SC#<)C;S4#*s$tHDDG#M+s$uHDDG's$p#)Cs$uS9>*s$wHDDG#M.s%u8C#)Cs$xS9#*s${HDDG#MSCs$zs#)QCs$WWSmC$#)C(S9#*s%$HDDG#MOs%%HDDG(#SCs#*+8Cs&-)C$S*#*s%)HDDG#M)Cs#0S4s%)*s%+HDDG#M)Cs%*S*'*s%-HDDG#M+s%.HDDG%s%)#+s%/HDDG(s%*#+s%0HDDG-s%+#+s%1HDDG8s%,#+s%2HDDG;s%-#+s%3HDDGBs%.#+s%4HDDGs#*s%/#+s%5HDDGs#2s%0#+s%6HDDGs#7s%1#l#$#s%.s%(l#%s#Bs%9#l#&s#Ls%<#j#'C#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8S(#j#9S(##CS&F#CLS8k##$##CQF#CS-Fk##$#$S+F$S-S&'#Rk##%#$FS-$QS/'S0#k##%##CS/Fk###SM@RS#2#S+#CS-#k##&#%FS-%QR2QS#VSG#s%4%R#'&#2RS#$#S-#CRF$S/Rk##$#k##&#k##)#k##/#k##1#k##8#k##=#k##B#k##s#&#k#'C#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8S(#k#9S(#%FQ%QF9SN&s&vSnfJ&%S+E$#QS7SNS-S/RS#S0LS'S<SKl#(s#8(#l#0s$hs$f#j#:s$j#j#.s$m#V#S)Jj##s$q#j##s$x#YSos$ys$xs$u#Rl#)s$|C#l#*s%#C#l#;s%)s%%#l#<s%/s%+#l#+s%7s%1#l#,s%=s%9#l#-s%Cs%?#l#0s%Is%E#l#=s%Ns%K#l#>s%Xs%S#l#.s%`s%Z#l#/s%is%b#$S#S76s'1S0&s'2J#C#S1j#?s'3#Is&TE%Fs&U,s&GE%F#k##s&i#k##&#Js&RE@Es&K2#(#Cs&N#k##s&f#Ks&PE$s&KE's%^#k##s&c#Ls&OE$Es&J%s&KF'$#k##s&`#Ms&OE7s%XE#C#Fk##s&t#Ns%[E,s%UE#C#s%Vk##s&x#QCs&%WSpC#s'R)Cs&QS*#*s&THDDG#MOs&UHDDGs&N#+s&VHDDGs&Rs&Q#+s&WHDDG%s&R#l#$#s&Os&Il#%s&[s&Z#l#&s&^s&]#j#'C#$Js&.$FS)%FO$Os&1'$#k##&#k##(#k#'C#WJS<S#S2l#(,$#l#)s%gC#l#*s%mC#l#+=:#l#,B?#l#-s#(s#$#l#.s#-s#*#l#/s#3s#/#l#0s#:s#5#l#=s&4s&1#l#>s&>s&9#VSqS0#/Ks'a0s'qs#Cs#@$#S-&s's$#C#S0WSOS5S'KWSP#IO>$S.>%s'h>&s'`4%$#'IO5'#WSOS5S2S'WSP#KL>$S.>%s'o>&s'g4%$#'KLVSQKLCKIQ#P#S$6s()FUS?s(.US@#USE#Ts(,#<#Ts(.s(.Ds(/s(/IQ<$(%$#<SrTs(3Ss<#E/*&'%#WSRIQK<St:S,%$##s'nL#'5#;8#VSSS(#]STS(S:SU?;J$$#j#@B##Cs#ls(6j#?s(@#USus#+WSvS5S'K0s(CK%S0$#XSws#.IO#/S'S.4Js#&s#%s#)KL5#.j#?s(H#/S's(:/S2S.4#Js#*s#.KL5#3j#?s(M#/S's(6/S2s(@4(#Js#3KL5#8j#?s(R#/S2s(;4J'#s#7KL5#<j#?s(V#4I*Js#:KL5#?j#?s(Y#FIS%S&4I.s(@s#>KL:S,s#)Js#'#s(6L#'s#9#;s#<#5'#j#AS=#4S%;s(Gs#LIOVSQIO&s(e=9#6s(g#CIS%##P#S$Ds(is(iS%%(s#>#s#<Es#Es#@#s#=s#;s#9FIS%(:S,$#s#8#s(GO#')#;/#51#&s(ss#%9#6s(u#CKI##P#S$Ds(ws(wI%(s#L#s#JEs#Ss#N#s#Ks#Is#GFKI(:S,$#s#F#s(UL#')#;s#[#FKIQ:S,s#M#s#K#s(ZL#'s#]#;s#`#VSSS(#]STS(S:SUs#,)J$$#j#@7#VSFPS>USxs(m#P#S>m$%##s)/s#Ds#eUSVs)1ZSys)1C#s#@s#gJ&s)3s#h#C?#/SDs)%&s)6##CJ&j#BC#ZSWC%#JIO#CI)Is(KE%Fs(Lk##s(ms'Pk##$#Js(JE7s(FE@E#2#s(G#Cs(I#k##s(k#Ks(KE%Fs'S$s'TE'$#k##s(i#Ls'XE$Es$[%s$\F'$#k##s(f#Ms'VE#Cs'NFk##s(y#Ns'TE#Cs'Os'Pk##s(|#7s'RE,s'QEBCs&hS)s(Y8Cs)U)C#S4s(X*s(ZHDDG#M)Cs(ZS*%*s(\HDDG#MRs(]HDDGL+s(^HDDG$s(Y#+s(_HDDG's(Z#l#$#s(Ws(Ql#%,s(b#l#&s(fs(e#j#'C#j#8S(##CJFk##s$gLk##$#k#'C#k#8S(#XJSMSJS/S;l#()$#l#)8C#l#*:C#l#+><#l#,B@#l#-s#(s#$#l#.s#.s#*#l#/s#5s#0#l#0s#:s#7#l#Cs#=s#<#l#Cs#Es#C#j#Cs#H#USCs#Im#$#XSzs)ys$1s$R#US{s$2#P#S>m#%#9J2s)A#$#S7j#BC#0CS1#S+s#zJUS|s)f#P#S$m$s(z#PKUSA#6s*+,H$I##P#S$j#BC#0CS1#S8s$(JUSB)H#I(#P#S$j#BC#0CS1#Ls$-JaS}S%s$Is)us$zIOs#dR72/(#CKI-#P#S$Ds*7s*7I/(s$h#s$fEs$os$j#s$gs$es$cFKI2:S,$#s$b#s)qL#')#;s$w#5#s#vj#BC#CIS%S&#P#S$Ds*Cs*CS%S&(s$t#s$rEs${s$v#s$ss$qs$o:S,#s$Js$m#s)|O#'(#;s$D#XS~S(S:T##0CS1-#s$EJVs$$:#WSRS%S&IWT$IS%S&ZSWS=s$Ss$L%$#0s*Ps*5s$U#s$`Q0s*QS%s$Y#s$jS#WT%S5S'K0s*Ss$cs$_$s%9#WT&S5S'K0s*Us$js$f$s%<#WT'S5S'K0s*Ws$ps$m$s%?#Vs$xs$r#l#Ds%Fs%D#l#Es&.s&-#j#Fs*4#j#Gs*6#j#Hs*;#l#Is*@s*^#j#Js*C#j#Ks*I#j#Ls*N#j#Ms*P#j#Ns*U#j#Os*X#j#Ps*[#j#QC#j#Rs*g#j#SS=#j#Ts*i#j#UT(##"). Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma fixed_noaccess_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_noaccess_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.vm_forget_range_id); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.with_vmmaps_lazy'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.fixed_noaccess_model)|] [|@l; @m; @n; @addr|] "##T#(#G#%###'#&#1#4#$#7#/#.#,#+#2#5#8#<#;#=#?#A#@#>#B#C#D#E#F#:#9#H#G#6#I#-#0#3&#D$#E&#F$#L##########UM#UN#VO##UG#%DUH%$%$#UG(UPIUH*$%$#VJ-EVJ.FVQ$#URCUS##US$$XS%22EFUS&&WS'#*(WS(4%#US))US**US++US,,US--\S.-,('&%$#VS/#C%C$<D:j#$=#%&VS0(CZS1@'%I$#YS297)#DWS3EFC$K#+m#%#j##>#j##s###j#%K#j#&s#*#j#'s#+##"). Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_ceiling)%Z -> init_sp_ok h ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Numbers.BinNums.Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.alloc_ceiling); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.init_sp_ok); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.alloc_ceiling_val); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.alloc_ceiling_le_alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@stdpp.bitvector.definitions.bv_sub); constr:(@Corelib.Init.Logic.eq_sym); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.Z_to_bv_u_eq'); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@stdpp.bitvector.definitions.bv_sub_unsigned); constr:(@Corelib.Init.Logic.proj2); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.page_round_up_Z_aligned); constr:(@Stdlib.ZArith.BinInt.Z.add_mod); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok)|] [|@Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__p1; @__p2; @__p3; @__p4; @__arith; @__sat3; @H10; @H9; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @__sat1; @__sat2; @__sat4; @z; @b; @x; @y; @m; @n; @__x9; @Hureq; @Htop; @Hbr; @Hcv; @Hlive; @Hrf; @Hisp; @Hce; @Hb0; @Hd; @Hdal; @Hbal; @h; @d|] "#>_#L$q$'#P$<$=$;#[#\#b$C###i#L#$$0$A#0#2#1#/#+#)$E#*#-#.#3#4#,#%#6#C#'#5#D#&#7#>#@$K$R#E#=#?#A#B#F#W#`#<#(#q#I$B$J#H$a$m#S#8$.$H#9$]$^#]$\#Q#w#;$,$1#K$j#G$n$o$p#U#T#a#e#o#r#v#x#z$/$2$3$4$7$8$:$D$L$M$P$Q$N#t$[$Z#:#J$c$e$g$h$i$f$d$b$`$k$_$l$q$r#l#R#O$&$9#X#^#_$?$>#p#V#Z$)#Y$T$(#n$5#h$F$W$X#|#{$+$*$U$S#c$-$I$@$6$O$%#u#y#}#~$#$$$V#k#f#g#d#j#s$G$Y#mU$@&$A+$B&#c%$C%$D%$E'$F*$G%$H$$I%$J&$K%$L%$M%$N$$O'$P%$Q*$R%$S%$T%$U%$V$$W%$X%$Y)$Z&$[&$\&$]%$^%$_%$`($a%$b%$c%$d%$e%$f%$g$$h$$i$$j$$k&$l$$m$$n)$o&$p$USUOUSLL,SA,#,#,#,#,#US`#USa#-$L/#H%D#I/S5H%D#I&IS2-*S5&I#-,S2(#S''#SBUSbS'VSc//MS)NS)O%$#(S&H45#>%S'#%J#MPS*(#S.LS&'$#2SA2#2#2#2#2#2#2#2#2#2#2#2#2#,#2#2#2#2#2#2#2#2#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#T#%DSB#USdS.-s#MS.'I#Ts#UTs#QVSE$#&'#+'#VSeS+S2QS+'SB#-s#WS+(#RERH'IR'IH/S#H'I#k##%#k##'#-s#`S%E#H'I$-s#cS$/#H'I#k##-#k##'#VSf;:&I<'I<&I<k##$#k##&#'IAWSgBAOj##SV#j#$%#'Is##k##SV#k#$(#-s#uS#F#H%DHIUSh#-s#yS,8#H9H#/%H($#%D'#k##)#G)H&IH-s$&S-/#H'I#&$H+$#k##(#H(H&HI-s$.S3/#H&H#'$I+$#k##(#I(H-s$5S08#H%D#Ik##?#J&H-s$:S6/#H%D#$k##s#$#8&H-s$?SM/#HFSWH8SCH9H#/SCH($#%DSC#k##s#-#GSCH/S<H'I#&$H+$#k##s#*#HS<H/S7H&H#'$I+$#k##s#(#IS7H8S=H%D#Ik##s#>#JS=H/S8H%D#S8k##s#B#8S8H/S>H-s$^S8'I#&$s#m+$#-s$bS>(#S1'I#&$s#r+$#j##(#&(s#u-s$iS?'I#-s$kS1&#s#yUS6O'IS%k##s#r#:SX:#:#:#:#:#:#:#:#:#;D#USiSAVSND#;D)?D$#.D'#1#P:*:#;D#?D*#.D-#1#P;D(.D#&1#P.D%.1#P:,:#:#;D#.D#41#P.D%01#P;DA;Ds##;DSX.D$#.D&#1#P?D@5;Ds#*;Ds#..D$#.D&#1#PTSAVSND#VSNDIXSjD$SA#WSYDs%L#?D#s#-.Ds#++.D$#1#P;Ds#9.D#6.D2#1#P:A;D#.D#s#31#P.D%s#/1#PUSkC#C=##C8##C?##C:##CA##C/##Cs####C5##Cs#%##C@##Cs#'##CB##Cs#)##C7##Cs#+##C=##C:##Cs#.##Cs#/##C=##CB##Cs#2##Cs#3##CA##Cs#/##Cs#6##Cs#7##Cs#2##Cs#3##Cs#:##Cs#;##Cs#6##Cs#7##Cs#>##Cs#?##Cs#:##Cs#;##Cs#B##Cs#C##Cs#>##Cs#2##Cs#F##Cs#G##Cs#9##Cs#6##Cs#J##Cs#K##Cs#9##Cs#M##Cs#H##Cs#I##Cs#P##Cs#Q##Cs#L##Cs#M##Cs#T##Cs#U##Cs#P##Cs#Q##Cs#X##Cs#Y##Cs#T##Cs#[##Cs#I##Cs#]##Cs#O##Cs#Y##Cs#`##Cs#a##Cs#\##Cs#]##Cs#d##Cs#e##Cs#`##Cs#a##Cs#h##Cs#i##Cs#d##Cs#e##Cs#l##Cs#m##Cs#h##Cs#i##Cs#p##Cs#q##Cs#l##Cs#m##Cs#t##Cs#u##Cs#p##Cs#q##Cs#x##Cs#y##Cs#t##Cs#u##Cs#|##Cs#}##Cs#x##Cs#y##Cs$$##Cs$%##Cs#|##Cs#p##Cs$(##Cs$)##Cs#s##Cs#x##Cs$,##Cs$-##Cs#w##Cs$)##Cs$0##Cs$1##Cs$,##Cs$-##Cs$4##Cs$5##Cs$0##Cs$1##Cs$8##Cs$9##Cs$4##Cs$5##Cs$<##Cs$=##Cs$8##Cs$9##Cs$@##Cs$A##Cs$<##Cs$=##Cs$D##Cs$E##Cs$@##Cs$A##Cs$H##Cs$I##Cs$D##Cs$E##Cs$L##Cs$M##Cs$H##Cs$<##Cs$P##Cs$Q##Cs$C##Cs$@##Cs$T##Cs$U##Cs$C##Cs$W##Cs$R##Cs$Y##Cs$T##Cs$[##Cs$I##Cs$]##Cs$O##Cs$x##Cs$y##Cs$t##Cs$u##Cs$s##Cs$t##Cs$s##Cs$t##Cs$P##Cs$Q##Cs$P##Cs$Q##Cs$~##Cs%###Cs%*##Cs%+##Cs%,##Cs$p##Cs$q##Cs$l##Cs$m##Cs$t##Cs$u##Cs$_##Cs%)##Cs$x##Cs$y##Cs$k##Cs$h##Cs$|##Cs$}##Cs%;##Cs%<##Cs%$##Cs%%##Cs$o##Cs$t##Cs%(##Cs%)##Cs%8##Cs%3##Cs%,##Cs%-##Cs%(##Cs%)##Cs%0##Cs%1##Cs%K##Cs%L##Cs%M##Cs%H##Cs%I##Cs%=##Cs%>##Cs%A##Cs%B##Cs%I##Cs%J##Cs%M##Cs%N##Cs%R##Cs%S##Cs%Z##Cs%[#USlCBDS2BDS)USmD3D$S&#3D&S/#BDS'3D#SD&BDS&3D#S&(3D%S5#3D(O#USnDUSoD2s(5AD#VSGDI)D$Q#*'GEEF#KUSpEADs(;ADs(=)D$Q#*,GEEF#K$-GEEF('#2s(A2#AD#)D#Q.*2GEEF#K$3GEEF.-#)D2S(1*5GEEF#K)D4S(/*7GEEF#KR8GEEFS*59GEEF$#$:GEEF'4#)D8S(9*<GEEF#KR=GEEFS+)D7S(<*?GEEF#K5@GEEF%#$AGEEF';#ZSOBGEEF=WSHDA5@D#=)D=Q#*s#&GEEF#K$s#'GEEF'A#ADs(;ADSA)D$Q#*s#+GEEF#K$s#,GEEFs#'s#&#,AAD#)D#Qs#,*s#0GEEF#K$s#1GEEFs#,s#+#)Ds#0S(,*s#3GEEF#KRs#4GEEFS%5s#5GEEF$#$s#6GEEFs##s#0#Rs#7GEEFR)D2S(s#6*s#9GEEF#K5s#:GEEF%#$s#;GEEFAs#5#WSHDs#:0@D#7)D7Q#*s#?GEEF#K$s#@GEEF@s#:#ADs#5VSGDs(')D$Q#*s#DGEEF#K@D>s#=)D#S9'*s#GGEEF#K)Ds#ES(A*s#IGEEF#K)Ds#GS(s#B*s#KGEEF#K)Ds#EQs#I*s#MGEEF#K)Ds#(Qs#K*s#OGEEF#K)Ds#MS9-*s#QGEEF#KVSGDs(2WSqD#s)$)D1S(#*s#UGEEF#K5s#VGEEF'#$s#WGEEF*s#Q#$s#XGEEF-s#R#$s#YGEEF0s#S#$s#ZGEEF3s#T#$s#[GEEF6s#U#$s#\GEEF:s#V#$s#]GEEF?s#W#$s#^GEEFs#%s#X#$s#_GEEFs#+s#Y#$s#`GEEFs#1s#Z#$s#aGEEFs#7s#[#$s#bGEEFs#=s#\#$s#cGEEFs#Ds#]#$s#dGEEFs#Ls#^#$s#eGEEFs#Ts#_#$s#fGEEFs#[s#`#VSrs#gFCJMVSsLS/%J#Mm$%#WStDIOXSuLS/$#l#%*)#l#&s#qs#p#l#'s#~s#}#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0N#j#1N#j#2N#j#3N#%DSDI%DS2S/k##$#%DS'I%DS.Ik##$#&S)I&S&S'+#S+k##%#&IS&&S)S.+R#k##%#k##,S:9S*S%(#S&%DS'#k##&#%DS*I%DS&S'k##$#%DS+I%DRIk##$#&S%I&RS*+#S3k##%#&IR&S+S$+S6#k##%#%DS$Ik###S:9S#S,(#S%%DS*#k##&#%DS$s)-(S+S%'#S#&IS%&IS$%DS-I(S,S-'I#&$s).+$#k##'#k##(#k##*#k##,#k##.#k##1#k##3#k##:#k##?#k##s#$#k##s#(#k##s#,#k##s#2#k##s#7#k##s#<#k##s#@#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0N#k#1N#k#2N#k#3N#'RI'IS''S'I-s*BS@i#?Ls)G&%$S)S$HSBS'RSI#S&S.S*S+S%S#S,S-S3S0S<S>S?S1S4S;l#4s#U(#l#5s(6s(4#j#6s(8#j#7s(;#V#OLj##s(?#j##s(I#Ds(Js(Is(B#S0l#8s(MD#l#9s(OD#l#:s(Ts(Q#l#;s(Ys(V#l#<s(`s([#l#=s(gs(b#l#>s(os(i#l#?s(qD#l#@s(tD#l#As(zs(v#l#Bs)$s(|#l#Cs)-s)&#l#Ds)6s)/#l#Es)As)8#l#Fs)Gs)D#l#Gs)Qs)L#l#5s)Ys)S#l#Hs)bs)\#VSvs)d#4s*_s)e-s*`#%D#s)g(s)`S$-s*cR<I#<$L0$#K&KL<$#QS$6%#MS$NS$Os*`$#4s*o*(*H7#,4s*r#>'&#0+#nJ#$##J.#%###MPS,(6S#4s*x#Ss*y#R-s*z#('#LS$6$#0+#nJ#$##J;#%###M%J#Mj#ID#<A-0L#K/<@#6$>(%H7#s##4s+-#>>=#0'#nJ#$##J)#%###M0#2nJ#$##J-#%###M%J#Mj#JJ#0MLnJ#$##J##%#'#M%J#Mj#JJ#<L34s+:L72L4s+<#>s#-%#06#nJ#$##J(#%###M0#A%J#Mj#ID#6Ls#74s+Ds#?(LH7#s#A4s+G#>s#8&#0(#nJ#$##Js#C#%###M0#s#,%J#Mj#ID#6s#5s#B(s#6H7#s#K4s+Q#>s#B0#0'#nJ#$##JL#%###M0#s#6%J#Mj#JJ#0L(0#s#:%J#Mj#JJ#4s+\s*ZCDs*[WSwS%s*\#XSxs+^%S%#%s+_S%&MS#NS#Os+U$#(s*_S,(#H7#s*a4s+g#>'L#0M#PS-4s+k)Ss+l#S$-s+m#(&#LS#6$#0*#%J#Mj#Js+r#ES#H'IS#/S-H'I#k##s*{#k##&#Es*uH'Is*v'Is*^k##s+$#k##%#Fs*[H8s*TH9H#(#s*U%Ds*W#k##s*j#Gs*YH/s*SH'I#&$H+$#k##s*g#Hs*XH&Hs*S's*TI+$#k##s*d#Is*XH8s*TH%D#Ik##s*z#Js*WH-s,9SP/#H%D#$k##s+##8&H-s,>Sy/#HFS<H8S7H9H#(#s*R%DS7#k##s++#GS7H/S=H'I#&$H+$#k##s+(#HS=H&Hs*R's*SI+$#k##s+%#IS8H8S>H%D#Ik##s+;#JS>H/S?H%D#S?k##s+?#8S?H/S1H&s*Ps+h+s*P#(S;H(s*QS;(#H7#s*S%D&#j##(#-s,cS4'I#-s,eS;&#s+sBDS/BDS53D$O#@Ds&ss&r@D#s'6WSQD#s&u)Ds&YQ#*s'AGEEF#Kl#%#s&9s&3l#&)s'D#l#'s)xs'Q#j#(D#j#)D#j#*D#(LO(S/L(#O7#S/%D&#k#(D#k#)D#k#*D#-s,}SIWL#HSzl#4-%#l#5s*qs*o#j#6=#j#7@#V#OLj##s*v#j##s*y#Ds*zs#-s#&#SMl#8s#/D#l#9s#1D#l#:s#6s#3#l#;s#;s#8#l#<s#As#=#l#=s#Hs#C#l#>s#Os#J#l#?s#QD#l#@s#TD#l#As#Zs#V#l#Bs#_s#\#l#Cs#es#a#l#Ds#ls#g#l#Es#ss#n#l#Fs,&s,##l#Gs,0s,+#l#5s#{s#w#l#Hs$&s#}#(S#H%D#s$L(S,HMS,NS,Os-4$#>#S#s$g0M#PS3(s,/S-4s-G#Ss-H#S#-s-I#('#LS,6$#0+#%J#Mj#ID#0s$y&%J#Mj#JJ#-s-Ss$F7#s,OVSRs-U#%DS-Lj#ID#7Ls,AVSRs-Y#%DS-#j#ID#7s$Vs,WES,H'IS,/S3H'I#k##s,d#k##&#Es,LH'Is,Mk##s,hs,?k##$#Fs,;H9Hs,4(#s$A%Ds,7#k##s,Q#Gs,9H'Is,4&s,5H+$#k##s,M#Hs,9H&Hs,4's,5I+$#k##s,J#Is,9H%Ds$<Ik##s,_#Js$BH%Ds$=s$>k##s,b#8s$@H-s-}SW/#HFS7H9Hs,-(#s$<%DS=#k##s,i#GS=H'Is,.&s,/H+$#k##s,e#HS8H&Hs,/'s,0I+$#k##s,b#IS>H%Ds$8Ik##s,w#JS?H%Ds$:S1k##s,z#8S1H/S4H'Is,-+#s,-(s$7S@7#s$8%DS@#j##&#&s$;s-M'Is$:&s&^s-O3Ds$:Os(|@Ds(ks(LWSQD#s(l)Ds(NQ#*s(vGEEF#Kl#%#s'ns'hl#&(s(y#l#'s+Qs)*#j#(D#j#)D#(OL7#O%DL#k#(D#k#)D#-s.RSFVL#SZl#4*%#l#5s,Fs,D#j#66#j#78#V#OLj##;#j##B#Ds##s,M>#SPl#8s#%D#l#9s#'D#l#:s#+s#)#l#;s#/s#-#l#<s#5s#1#l#=s#;s#7#l#>s#As#=#l#?s#CD#l#@s#FD#l#As#Js#H#l#Bs#Ns#L#l#Cs#Ts#P#l#Ds#Zs#V#l#Es#`s#\#l#Fs-Ws-T#l#Gs-as-\#l#5s#gs#d#l#Hs#ns#i#VSRs.ns#p'Is#qUSJs.pVSEs.$#&s#t#+&#&s#vs.%+(#CN)WS{**#j#KDL&OLUS|#j#LD#j#KD#CDs$#VSEOLXS}DDS~#CD#j#MD#j#ND#CDs.6USJLCD#j#KS[#CDs.9`T#S[DDDSJSJ22$s/,s.:#fT$DDDDDDSE333SE)s.<s.<(;s.;#`T%DDSS4SS0s$0s$0/;s.;#ZT&>;>96#'Is#Q&s#Rs.>+$#j##s#V#.Ds,Ss,X.Ds,Z#.Ds,\#1#P#C#s,?#C$##C%##C&##C'##C(##C)##C*##C+##C,##C-##C.##C/##C0##C1##C2##C3##C4##C5##C6##C7##C8##C9##C:##C;##C<##C=##C>##C?##C@##CA##CB##Cs####Cs#$##Cs#%##Cs#&##Cs#'##Cs#(##Cs#)##Cs#*##Cs#+##Cs#,##Cs#-##Cs#.##Cs#/##Cs#0##Cs#1##Cs#2##Cs#3##Cs#4##Cs#5##Cs#6##Cs#7##Cs#8##Cs#9##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs#@##Cs#A##Cs#B##Cs#C##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs#T##Cs#U##Cs#V##Cs#W##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#]##Cs#^##Cs#_##Cs#`##Cs#a##Cs#b##Cs#c##Cs#d##Cs#e##Cs#f##Cs#g##Cs#h##Cs#i##Cs#j##Cs#k##Cs#l##Cs#m##Cs#n##Cs#o##Cs#p##Cs#q#3Ds+(S2s+#3Ds+&S&s+)3D$S/#BDSD3D#S5s++3D%O#$s+$GEEFs*Rs*zs*v,s08,#AD#)D#Qs+%*s+)GEEF#K$s+*GEEFs*Xs+$#)Ds*[S(s+(*s+,GEEF#K)Ds*]S(s+&*s+.GEEF#K5s+/GEEF#s*u$s+0GEEF&s+*#)Ds+.S(s*a*s+2GEEF#K)Ds+,S(s*c*s+4GEEF#K5s+5GEEFs*v#$s+6GEEF&s+0#ZSOs+7GEEFs*eWSHDs*h3@D#s+2)Ds+2Q#*s+;GEEF#K$s+<GEEF's+6#$s+=GEEFs*ks+7s*p$s+>GEEFs*ls+8s+.)Ds*oS(s*u*s+@GEEF#K5s+AGEEF#s*k$s+BGEEF8s+<#)Ds*yS(s*s*s+DGEEF#K5s+EGEEFs*l#$s+FGEEF6s+@#WSHDs*ws+9@D#s*~)Ds*~Q#*s+JGEEF#K$s+KGEEF6s+E#WSQDs*es+%)Ds+JS9#*s+NGEEF#K)D%S(s*Z*s+PGEEF#K5s+QGEEF%#$s+RGEEFs*as+L#$s+SGEEFs*ds+M#$s+TGEEFs*gs+N#$s+UGEEFs*js+O#$s+VGEEFs*ms+P#$s+WGEEFs*qs+Q#$s+XGEEF/s+R#$s+YGEEF5s+S#$s+ZGEEF:s+T#$s+[GEEF?s+U#$s+\GEEFAs+V#$s+]GEEFs##s+W#$s+^GEEFs#*s+X#$s+_GEEFs#1s+Y#$s+`GEEFs#8s+Z#$s+aGEEFs#?s+[#l#%#s*Ys*Sl#&s#Bs+d#l#'s#Is+q#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0N#j#1N#j#2N#j#3N#7s*%S,'I#&$s0Q+$#k##s**#k##s*+#k##s*-#k##s*/#k##s*1#k##s*4#k##s*6#k##s*=#k##s*B#k##s*G#k##s*K#k##s*O#k##s*U#k##s*Z#k##s*_#k##s*c#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0N#k#1N#k#2N#k#3N#i#?Ls0fs*%s*$s*#S)S$HSBS'RSZs%nS&S.S*S+S%S#S,S-S3S0S8S4S;S@S\SIl#4s#$$#l#5s/Us/S#j#6s&%#j#7s&'#V#OLj##s&*#j##s&1#Ds&2s/\s%9#SPl#8s&4D#l#9s&6D#l#:s&:s&8#l#;s&>s&<#l#<s&Ds&@#l#=s&Js&F#l#>s&Ps&L#l#?s&RD#l#@s&UD#l#As&Ys&W#l#Bs&]s&[#l#Cs&cs&_#l#Ds&is&e#l#Es&os&k#l#Fs0fs0c#l#Gs0ps0k#l#5s&vs&s#l#Hs&}s&x#XT's%hs%fs%P#UT(s1~&s'%#+s%o#m#&#WT)s2&s'(#=Ds')s'.s%ts%s#=Ds(~s'+#s'3S/WT*s2)s(xS$=Ds'3s'1$s(w#%DS,s(x0MMPS0(#LLS-6$#0'#%J#Mj#ID#0*L%J#Mj#JJ#(s'PS-6#s'K%J#M(/S3'#.k##%#'(s'P6&1%J#Mk##%#VS],s'TXSK($#S)=JM/s+h-#ZSTDS-3#s'YLl#E=<#4s2Fs'e>s)BS$#=JMs'T%#S)ZSTDs'hs'X#s)ALl#Es'ls'j#ZSTs2JRs)6#s)eLl#Es)Ks)J#QR6s*J#%J#M's*7s*Dk##$#'s*N'%Js)cMk##$#VS]s*Q*ES$H'IS$/S,H'I#k##s1]#k##&#Es*WH'Is*X/s1GH'I#k##s1c#k##&#Fs1GH8s1?H9H#(#s1@%Ds1B#k##s1M#Gs1DH'Is1<&s1=H+$#k##s1I#Hs1AH&Hs)F's)GI+$#k##s1F#Is1?H%Ds17Ik##s1[#Js1=H%Ds18s19k##s1^#FSCH8S<H9H#(#s14%DS<#k##s1c#GS<H'Is12&s13H+$#k##s1_#HS7H&Hs)?'s)@I+$#k##s1\#IS=H%Ds1/Ik##s1q#JS8H%Ds11S>k##s1t#'Is1.+#s1)(s1)S4QS1'$#j##&#.Ds0us0[1#P#C#s0A#C$##C%##C&##C'##C(##C)##C*##C+##C,##C-##C.##C/##C0##C1##C2##C3##C4##C5##C6##C7##C8##C9##C:##C;##C<##C=##C>##C?##C@##CA##CB##Cs####Cs#$##Cs#%##Cs#&##Cs#'##Cs#(##Cs#)##Cs#*##Cs#+##Cs#,##Cs#-##Cs#.##Cs#/##Cs#0##Cs#1##Cs#2##Cs#3##Cs#4##Cs#5##Cs#6##Cs#7##Cs#8##Cs#9##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs#@##Cs#A##Cs#B##Cs#C##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs#T##Cs#U##Cs#V##Cs#W##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#]##Cs#^##Cs#_##Cs#`##Cs#a##Cs#b##Cs#c##Cs#d##Cs#e##Cs#f##Cs#g##Cs#h##Cs#i##Cs#j##Cs#k##Cs#l##Cs#m##Cs#n##Cs#o##Cs#p##Cs#q#BDS.3Ds/+S2#3Ds/-S's/,3D$S/#3Ds/)S.s/.3Ds&bS5#3D%O#)Ds.DQs.{*s/(GEEF#K$s/)GEEFs.Ws/##)Ds.ZS(s.G*s/+GEEF#K5s/,GEEF#s.m$s/-GEEFs&_s/'#)Ds.KS(s.^*s//GEEF#K5s/0GEEFs.Z#$s/1GEEFs&]s/+#@Ds&Xs.O)Ds/+Q#*s/4GEEF#K$s/5GEEFs&\s//#)Ds//Qs.k*s/7GEEF#K$s/8GEEFs.fs/2#5s/9GEEFs&is.`$s/:GEEFs&ls/4#Rs/;GEEFS$5s/<GEEF#s&f$s/=GEEFs&is/7#@Ds&Us/7)Ds.tQ#*s/@GEEF#K$s/AGEEFs&hs/;#ADs&{)D#S9s.y*s/DGEEF#K)D%Qs.a*s/FGEEF#K)Ds.`S9'*s/HGEEF#K)Ds.fQs/F*s/JGEEF#K)Ds.dS9s/%*s/LGEEF#K$s/MGEEFs.^s/G#$s/NGEEF&s/H#$s/OGEEFs.bs/I#$s/PGEEFs.es/J#$s/QGEEF+s/K#$s/RGEEF.s/L#$s/SGEEF1s/M#$s/TGEEF5s/N#$s/UGEEF:s/O#$s/VGEEF>s/P#$s/WGEEFs&ws/Q#$s/XGEEFBs/R#$s/YGEEFs#&s/S#$s/ZGEEFs#+s/T#$s/[GEEFs#0s/U#$s/\GEEFs'4s/V#$s/]GEEFs#6s/W#l#%#s.Us.Ol#&s#;s/`#l#'s#Cs/m#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#OD#j#0N#j#1N#j#2N#j#3N#%DSDS/k##s.M#%DS)Ik###s.?&S&I&S.S)+#S%k##%#&IS.&S&S*+S$#k##%#k##s.HS:9S+R(#S.%DS'#k##&#%DS.S'k##s.K#%DS%Ik###s.B&RI&S$S++#S0k##%#&S%S#+SM#k##s.?#%DS#Ik###S:9S,S-(#R%DS*#k##&#'S#S%%DS,s4v(S%R'#S-&IS#%DS0I(S-S3'#S0k##%#k##&#k##(#k##s._#k##+#k##.#k##0#k##2#k##9#k##=#k##B#k##s#%#k##s#(#k##s#.#k##s#3#k##s#8#k##s#;#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#OD#k#0N#k#1N#k#2N#k#3N#QSI-s6,S\i#ALs51s.Ls.Ks.JS)S$HSBS'R$SF#S&S.S*S+S%S#S,S-S3S0SCS7S?S1S4S;S@l#4s#N&#l#5s3|s3z#j#6s*N#j#7s*U#V#OLj##s,6#j##s%`#Ds%as4+s%\#S6l#8s,>D#l#9s,CD#l#:s%gs%e#l#;s%ks%i#l#<s%qs%m#l#=s%ws%s#l#>s%~s%y#l#?s,aD#l#@s,gD#l#As&(s&&#l#Bs&,s&*#l#Cs&2s&.#l#Ds&8s&4#l#Es&?s&:#l#Fs51s5.#l#Gs5;s56#l#5s&Hs&C#l#Hs&Os&J#XSKs&Us&Rs&Q#=JMs-Ls&[s&Y#<s5Hs.F%J#M&s.Gs.3k##$#&s5Ls.J%Js.+Mk##$#VS^s5Os.M&s4Gs%|j##s%~#)Ds0\S(s0@*s1(GEEF#K$s1)GEEFs0<s1##l#%#s/}s/wl#&s*ss1,#l#'s3`s19#j#(D#j#)D#&IO(OS/&O#k##%#k#(D#k#)D#WLSFs#8S4l#4*$#l#5s4Us4S#j#6s+'#j#7s+.#V#OLj##s,k#j##s&9#Ds&:s4`9#S6l#8s,sD#l#9s,xD#l#:s&@s&>#l#;s&Ds&B#l#<s&Js&F#l#=s&Ps&L#l#>s&Ws&R#l#?s-:D#l#@s-@D#l#As&]s&[#l#Bs&as&_#l#Cs&gs&c#l#Ds&ms&i#l#Es&ts&o#l#Fs5fs5c#l#Gs5ps5k#l#5s&}s&x#l#Hs'(s'##XSKs#2s#/s#.#=JMs.)s#7s#6#Ks.{'Is&Nj##s&P#;Ds4i?Ds4es4L.D$#1#P?Ds4hs4j.D'#1#P;Ds4o.D#&1#P.D%+1#P;Ds4`.D#.1#P.D%-1#P?Ds4u,.D#s4U1#PWSYDs1hs4Q?D#7.Ds4as4Y.D$#1#P;Ds4l.D#;1#P.D%:1#P#C-s4K#C.##Cs4T##C+##C1##C2##Cs4X##C/##Cs4Z##Cs4[##C2##Cs4]##C9##C:##C;##C<##C=##C>##C?##C@##Cs4f##C=##Cs4h##Cs4i##Cs#%##Cs#&##Cs#'##Cs#(##Cs#)##Cs#*##Cs#+##Cs4q##Cs#(##Cs#.##Cs#/##Cs#0##Cs#1##Cs#2##Cs#3##Cs#4##Cs#5##Cs#6##Cs#7##Cs#8##Cs#9##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs5)##Cs5*##Cs#=##Cs5,##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs5=##Cs#P##Cs5?##Cs5@##Cs#X##Cs#Y##Cs5C##Cs#V##Cs#l##Cs#j##Cs#h##Cs#g##Cs#X##Cs#W##Cs#o##Cs#s##Cs#t##Cs#e##Cs#f##Cs#_##Cs#p##Cs#d##Cs5S##Cs#{##Cs#|##Cs5V##Cs#i##Cs#w##Cs#u##Cs#q##Cs#r##Cs$'##Cs$(##Cs$&##Cs#y##Cs#|##Cs$$##Cs$'##Cs$+##Cs$/#3Ds34S2s353Ds*hS)s353D$S/#3Ds34S)s373Ds38S5#3D%O#Rs30GEEFS.5s31GEEFs*a#$s32GEEFs*ds3,#5s33GEEFs2ys*]$s34GEEFs*`s3.#5s35GEEFs*Ss2v$s36GEEFs*hs30#5s37GEEFs2as*Q$s38GEEFs*ds32#$s39GEEFs2Hs33s2F$s3:GEEFs2Ks34#$s3;GEEFs2Ns35#$s3<GEEFs2Qs36#$s3=GEEFs*Ps37#$s3>GEEF(s38#$s3?GEEF+s39#$s3@GEEFs*`s3:#$s3AGEEFs*bs3;#$s3BGEEFs*ds3<#$s3CGEEF1s3=#$s3DGEEF4s3>#$s3EGEEFs*ys3?#$s3FGEEFs+$s3@#l#%#s2>s28l#&;s3I#l#'Bs3V#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#0N#j#1N#j#2N#j#3N#%DS2Ik###s26%DS&Ik##s29#&S'I&S)S'+#S*k##%#&IS)&S)S&+S%#k##%#k##,S:9S.S+(#S&%DS'#k##&#k##s2Cs23k##s25s&D&S+I&S%S*+#S-k##%#&S+R+S0#k##s2%#k##s29S:9S$S#(#S%%DS*#k##&#&IS*(S$S#'I#k##s&K#k##s&L#k##s20#k##(#k##*#k##0#k##4#k##9#k##;#k##=#k##s###k##s#(#k##s#-#k##s#0#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#0N#k#1N#k#2N#k#3N#i#<Ls8es2$s2#s1~S)S$HS'RSFs&7S&S.S*S+S%S#S,S-S3S0S1S4S;S@l#4s#?$#l#5s7Ts7R#j#6s.&#j#7s.-#V#OLj##s/j#j##s)8#Ds)9s7_s%F#S6l#8s/rD#l#9s/wD#l#:s)?s)=#l#;s)Cs)A#l#<s)Is)E#l#=s)Os)K#l#>s)Vs)Q#l#?s09D#l#@s0?D#l#As)\s)Z#l#Bs)`s)^#l#Cs)fs)b#l#Ds)ls)h#l#Es)ss)n#l#Fs8es8b#l#Gs8os8j#l#5s)|s)w#l#Hs*'s)~#/s8zH/S$H($#/#H%DLIj#ID#(Ls9(/#H%D#Ij#ID#(IL/#H%D#Ij#ID#CDI=DI$#0S*=DI)#2S+/s2-H,s:3,#,#,#,#,#T#VSGD#)D#Qs4f*s4jGEEF#KZSOs4kGEEF#l#%#s3cs3]l#&s4ws4n#l#'s7Fs4{#%D*Ik###S:l#4%#Lm##s9)XT+s9BS$H#=Ds#$B76#WS_s2Bs#)#=Ds2Cs1Xs&'s&&#Ks9Fj##s)ts8=BDO)Ds4wS9s4S*s4{GEEF#K$s4|GEEFs45s4v#l#%#s3ts3nl#&'s5##l#'s7Ws50#j#(D#&IL'IOk##$#k#(D#VLs',S1l#4($#l#5s8Is8G#j#6s.w#j#7s.~#V#OLj##s0_#j##s*-#Ds*.s8T7#S6l#8s0gD#l#9s0lD#l#:s*4s*2#l#;s*8s*6#l#<s*>s*:#l#=s*Ds*@#l#>s*Ks*F#l#?s1.D#l#@s14D#l#As*Qs*O#l#Bs*Us*S#l#Cs*[s*W#l#Ds*as*]#l#Es*hs*c#l#Fs9Zs9W#l#Gs9ds9_#l#5s*qs*l#l#Hs*xs*s#j##s*@s$K?Ds8Ts84.D#s8;1#P?Ds8Ws8?.Ds8?#1#P?Ds&@s8Y.Ds8Cs8:.D$#1#P?Ds8^s&X.D#s8>1#P.Ds8Hs&J1#P#C/s8,#C0##C1##C+##C)##C*##C+##C,##C-##C.##C/##C0##C4##C<##C=##C>##C?##C@##CA##C;##C9##C:##C;##C<##C=##C>##C?##C@##Cs#$##Cs#,##Cs#-##Cs#.##Cs#/##Cs#-##Cs#.##Cs#+##Cs#)##Cs#1##Cs#2##Cs#,##Cs#+##Cs#5##Cs#6##Cs#.##Cs#/##Cs#9##Cs#:##Cs#2##Cs#3##Cs#=##Cs#>##Cs#6##Cs#7##Cs#A##Cs#B##Cs#:##Cs#=##Cs#E##Cs#F##Cs#@##Cs#D##Cs#I##Cs#J##Cs#N#)Ds60Qs5n*s69GEEF#K$s6:GEEFs5hs64#)Ds5kS(s63*s6<GEEF#K5s6=GEEF#s%k$s6>GEEFs-ps68#@Ds-es67)Ds5vQ#*s6AGEEF#K$s6BGEEFs-is6<#)Ds5xQs6<*s6DGEEF#K$s6EGEEFs5ss6?#@Ds-]s5{)Ds6@Q#*s6HGEEF#K$s6IGEEFs-ps6C#)Ds6GS9s5z*s6KGEEF#K$s6LGEEF#s6Fs$/)Ds6JS(s6F*s6NGEEF#K)Ds6LS(s6)*s6PGEEF#K)Ds6IQs6N*s6RGEEF#K)Ds6,Qs6P*s6TGEEF#K$s6UGEEF#s6O#$s6VGEEF&s6P#$s6WGEEF)s6Q#$s6XGEEF,s6R#$s6YGEEF/s6S#$s6ZGEEF3s6T#$s6[GEEFs-{s6U#$s6\GEEF9s6V#$s6]GEEF=s6W#$s6^GEEFBs6X#$s6_GEEFs.7s6Y#$s6`GEEFs#(s6Z#l#%#s5Xs5Rl#&s&5s6c#l#'s#.s6p#j#(D#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#0N#%DS/S5k##s%v#&S)S2+#S*k##s%u#k##s)_S:9S&S*(#SD%DS'#k##&#%DSDS&k##s%~#k##s5Us5C9S+S%(#S)%DS*#k##s)`#'IS+'IS&k##$#&IS+k##s5Ls)^k##s5M#k##%#k##&#k##(#k##,#k##1#k##3#k##6#k##<#k##s&5#k##A#k#(D#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#0N#hLs5'S)S$Hs)<SFS'RS&S.S*S%S#S,S0OS1S4S;S@l#4s#-$#l#5s:Ys:W#j#6s1+#j#7s12#V#OLj##s2o#j##s,=#Ds,>s:ds$[#S6l#8s2wD#l#9s2|D#l#:s,Ds,B#l#;s,Hs,F#l#<s,Ns,J#l#=s,Ts,P#l#>s,[s,V#l#?s3>D#l#@s3DD#l#As,as,_#l#Bs,es,c#l#Cs,ks,g#l#Ds,qs,m#l#Es,xs,s#l#Fs;js;g#l#Gs;ts;o#l#5s-%s,|#l#Hs-,s-'#WS_s<#s$o#=Ds<$s4Bs%=s%<#<s%=s(b6s(cs-9MRNROs<y$#4s=,s%B(s(hH7#s%D4s=/#>'&#0+#nJ#$##J-#%###MPS#4s=4s50Ss=5#S%-s=6#(&#LR6$#0*#nJ#$##Js-m#%###M%J#Mm#9#=JMs4d#s)Rs({<Is<=%J#M&Is5<k##$#&Is<A%Js5>Mk##$#VS^Is<DXSK'$#S&=JMs4r,+#-s=I7=Ds5Fs5'$#LUSLR-s=L#<I#<$'0$#K&K*<$#6$s-d4s=T&(&H7#(4s=W#>s#/&#0(#nJ#$##J*#%###MSs=[s#)2-s=\#(s#,#6#s#(0'#nJ#$##J3#%###M%J#Mm#:#USUS#USL#-s=e#<I#<$@0$#K&<#;Q*6=#M,N-Os=a$#4s=p)7>*4s=r#>&%#0*#nJ#$##J-#%###MSs=vs#D4-s=w#(s#G#L86$#0(#nJ#$##J6#%###M%J#Mm#>#WT,S#s#Ms#M%J#Mm#%#l#Ps6&s6##l#Qs=1s=/#l#Rs=:s=3#l#ST-s=<#j#Ts=m#j#Us=r#j#Vs={#j#Ws=}#j#Xs>%#j#Ys>(#j#Zs>*#j#[s>-#l#Js>9s>1#l#\s>;T.#j#]D#j#MT/##"). Qed.

(* [comment removed for export] *)
Lemma brk_grow_admissible_init : forall reserved (brk0 mbase sp : word) lim (model : Model) d,
  (sp_window_lo <= bv_unsigned sp)%Z ->
  (reserved_top reserved <= bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 + d <= alloc_ceiling)%Z ->
  (d <= lim)%Z ->
  m_vmmaps model = mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp ->
  m_vm_lazy model = [] -> m_vm_materialized model = [] ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned brk0 + d)) (Z_to_bv 64 (bv_unsigned brk0 + d)) = true.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_lo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.reserved_top); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.alloc_ceiling); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.brk_grow_ok_aligned_intro); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanCeil.init_sp_ok); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.region_free_above_top); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_backed_bytes); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.WithSegs.vm_backing_used_simple)|] [|@b; @h; @v; @l; @z; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @H; @r0; @q0; @H9; @H8; @H7; @H6; @H5; @r; @q; @H4; @H3; @H2; @H1; @H0; @__sat1; @__sat2; @Hmt; @Hlz; @Hvm; @Hlim; @Hce; @Hb0; @Hd; @Hdal; @Hbal; @Htop; @Hsp; @d; @model; @lim; @sp; @mbase; @brk0; @reserved|] "#'3#M$<#^#V#_###6#l#r#8#1#9#:#7#)#0#*#5#;$1#c#4#3#<#=#&#.#b#2#G#%#'#-#/#+#H#$$2#,#>#I$0#U#{#|#~$$$&$'$(#?#J#F$)$5$4$6$3$7#S#R#Q#Y#[#g#h#i#(#v#x#y#}#A#C#K#E#L#D$+$,$*$-$/$8$:$9$.$;$=$>$?$<$@#W#\#Z#X#a#]#`#e#j#q#T$##n#m#d#k#s#u$%#P#f#o#p#t#w#z<$#&$$%$%%$&%$'%$(%$)+$*$$+%$,$$-%$.&$/&$0$$1$$2$$3&$4%$5$$6$$7$$8$$9$$:)$;$,S;,#,#,#,#,#USL#USM#VSN##5#$&S*%SO#USPQ$)O%$#$+Q'#C#D#E'S*C#D#E(ES0$1S1(E#$3S+&#O%#S,%QS70S766)K##PPS1S2S+#S%%#USQS1#9#&5<USRS+6>#%$#VSSS2S+0S2*F$s#$F'#C#D#E'KC#D#E(ES-(Es#&$s#+S0&#S&%#S,1O7Q8Q.s#/$#&GC+s#3#/%O##H#I2J&#N9S3%$#$s#:S3&#J+s#<#3L###H#Ik##(#k##-#k##5#k##7#k##;#k##=#k##?#k##B#l#$s#&s#F#l#%s#(S%#0P$s#Js#)'#C#D#E*S*$s#N#(E#*S0$s#Q#&#S&%#S,1ST7O8O.s#U$#*O/$#s#(#H#I9Q%s#'#*S3$s#^#&#J+s#`#3L###H#Ik##)#k##,#k##3#k##5#k##:#k##s#A#k##s#C#k##@#j#&S%#)Rs#Vs#VS&S&KS'S-ZSUS%s#&$F#S**$$s#o#'#C#D#E'PC#D#E(EK)Js#_s#_NNS&GR*#$s#w#(E#)Ls#cs#cJJRNG*#$s#{#&#S'%#S,)Ms#hs#hLLGJN1#)S#s#js#jMMNLJ7#8$.s$%$#*&&RC+s$*#/&%##H#I2N&#G)S(s#us#uS#S#JML9#%%#)S)s#xs#xS(S(LS#M*#$s$4#&#N+s$6#3J###H#Ik##*#k##0#k##:#k##=#k##s###k##s#(#k##s#*#k##s#-#&KC+s$B#/FG##H#Ij#'s$B#&PC+s$G#XSVGR#S+.s$GGs$3VSWs$HG:s$HG(%$#0K;#&FK%#S'j#(D#)Gs$;s$;RRS-S&S';F&#K%#S'j#&S%#VS<PC%EP%EC'S-C%E#k##%#k##'#$s$]GVS<#C%E$$s$`J'#C%E#k##-#k##'#$s$eNVS=#C#DCEUSX#-+CVS>C#&#,#D.#k##'#VS?0C(EC$s$pL'#C%E#($C4$#k##(#VS@(C(CE$s$xM'#C(C#%$E4$#k##(#VSA(C$s%#S#-#C#D#Ek##=#VSB&C$s%(S('#C#D#$k##B#-&C$s%-S)'#CVS=LC-MCVS>C#'MC&$##DM#k##s#+#VS?MC'S#C%E#($C4$#k##s#*#VS@S#C'S(C(C#%$E4$#k##s#(#VSAS(C-S)C#D#Ek##s#<#VSBS)C'S8C#D#S8k##s#@#-S8C'SCCUS'S)#DFE(ESY$s%OS.(E#$s%QS4&#SZ%#S,)SDs%>s%>S9S9SES4S.1#.s%TS[s%@&S\C+s%X#/%SD##H#I2S.&#SE%#S4$s%^S]&#S.+s%`#3S4###H#Ik##(#k##,#k##2#k##5#k##9#k##<#k##>#UFS)UFS^6SF5SFVS_DS/US`DXSaD$S5#USbDUScDVSGDS;VSGDs%zXSHD$SI#[SJ&S:S$S$S6#SKUSdS$VSeDEWSfD#(XSHD#SI([SJ+S:S$S$S6#SK\Sg,S:S$S$S6('#VSh-S6VSiHIVSjFS/#H#Im$%#WSkDES5XSlFS/$#l#)*)#l#*76#l#+<;#j#,D#j#-D#%FS5&ES5%#S/k##%#k#,D#k#-D#WFS9S.SCl#.*$#l#/s#(s#/#l#/s#*s#/#l#/s#+s#/#l#/s#,s#/#l#/s#-s#/#l#/s#Ls#/#l#0s#ND#l#1s#PD#l#2s#Us#R#l#3s#Zs#W#l#4s#as#\#l#5s#hs#c#l#6s#ps#j#l#7s#rD#l#8s#uD#l#9s#{s#w#l#:s$%s#}#l#;s$.s$'#l#<s$7s$0#l#=s$@s$9#l#>s$Is$C#l#?s$Rs$L#;s$X&#P%#S-m#&#:S%s$\s$X#s$aS02KWSmKS*S/:Ds$cs$`%$#\FS1S7S3QOS2s$f#l#/s%Es$r#l#/s&6s%k#j#@s&8#j#As&=#j#Bs&@#j#Cs&E#j#Ds&G#j#Es&K#j#Fs&N#j#Gs&P#j#Hs&S#j#Is&W#j#Js&[#j#KD#j#LSn#j#MD#j#Ns&c#j#Os&d#j#Ps&e#j#Qs&d##"). Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.
Scheme kc__4 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@kc__4); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.live_bytes); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Init.Datatypes.true); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.min_spec); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract)|] [|@E1; @b; @E2; @m; @n; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__p4; @__arith; @H2; @H; @H1; @H0; @__sat5; @__sat6; @z4; @H4; @z3; @H3; @__sat4; @y; @x; @__sat3; @Hlh; @hi; @lo; @sz; @a|] "#.-#C$;#J$#$$#~###$#N$-#T#n#%#&#'#t#(#C#)#*#.#/$+$1#0#1$/#,#+#d#6#>#-#2#=$:#I#4#3#?#@#<#R#U#[#a#j#l#8#s$*$3#G#F#L#Q#Z#f#h#5#k#m#:#9#;#w#v#z#{#}$0$4$6$7$5#B#A#7$9$;$<#K#P#M#V$($'#b#p#O#\#`#|#o#e$&#^#S#i#x#X#H#_#Y#q$%$2#]#r#y$)$.#c$,$8#g#u#WH#r%#s%#t%#u&#v'#w*#x%#y&#z%#{&#|%#}+#~%$#($$*$%%$&%$'%$('$)$$*$$+%$,&$-%$.*$/&$0'$1$$2%$3%$4)$5%$6&$7%$8)$9&$:'7S57#7#7#7#7#USE#USF##HGUSGO+&O#I#US;.US;*VSH$#$'#%'#+-S#3#OVS<KG+0S$3#Q&K#G+3S,3#S$&K#GVSI55US=#+8S1-S-#8)#2;#=;;S1#US>),*$#nK#$##*H#%###$)*/3S$#B,S$2s###-&$2s#%#=s#%s#%%#,3#,nK#$##3)#%###-95,#6###:k#$9#j#%K#+s#.S-3#S#&K#S.)@%3S##&K4G+s#4S&+s#5S%)$#3S,#&K#G+s#9S)-S%#8)#2s#<#=s#<s#<S)#,s#*#s##B(S12s#@#)*/-#%2s#C#=s#Cs#C&#,s#1#s#*nK#$##s#1H#%###s#+9s#3+#6###7k#&4#j#%K#)9s#63S-#&K#S.3HG&K#S.$MHk##$#$HG3MH&K#S.k##%#%'#$NMk##&#j##%#3NM&K#S.k##.#j###Hj##/#VSJHG01-)$#j#'C#j#(C#k#'C4k#(C#WGs#/S%O$s#0S%+s#hS2+s#iS*)$#WGS&#N$S&$+s#mS7-S*#8)#+s#pS6)#&B$S*-$#2s#t#+s#u#)#I)G###-j#)C#)/4B0S)-$#-S2/83#)GI)$###6j#)C#VSK8S)$9S)&C,S)%$##S)<&C/=%$#4&#+s$/SL-S7#VS??#$@$8A%&C#B%%##(s#$&C&)%$#4&#+s$:S/-S6#8/#VSMs$7s$6$Is$8#Is$8$Is$8k##$#k##&##Is$=WSNs$>s$=Hj##S@#j#*%##Is$?k##S@#k#*(#+s$JSA#I#$$s$D%$#+s$NSO+s$OSP)$#-#Q)#I)N###'j##*#$)s$N#I++s$XSQ$#s$Q+s$ZS3#I#$$s$T%$#+s$^S0)#'-#S,)#I)S$###+j##)#$)s$]+s$fS8#I#+s$hS9$#s$a>SB>#>#>#:C#:C&:C(*C$#*C&#/#P>):C#USRS5VSSC#FC#,:CSB*C,#*C%#*C)#/#P:C4*C#1*C-#/#PUS>L,L2#,L%#,L*#,L5#US=L?CO?CS#5C$M#?CQUSTC5C$N#5C&H#USUCUSVCUSCS5@C#USCs%=@C#@Cs%?CC$#'C'S'#(*FDDE#JA+FDDES-1,FDDE$#A-FDDES,@CS5'C#S+)(0FDDE#J11FDDE&#;2FDDE(#USWDA4FDDES1@Cs%L75@C#'C%S+#(9FDDE#J1:FDDE(#'C&S(6(<FDDE#JA=FDDES%1>FDDE$#;?FDDE'#<C;>'C,S'#(BFDDE#J'C>S'?(s#$FDDE#J'CAS(0(s#&FDDE#JCC)4VSDCI<C$#<C>#'C#S(s#)(s#,FDDE#J.s#-FDDE)<#.s#.FDDE,=#.s#/FDDE/>#.s#0FDDE3?#.s#1FDDEA@#VSXs#2EVS<KS.VSYGM&K#S.m$%#WSZCIHXS[GM$#l#+*)#l#,s#<s#;#l#-s#Es#D#j#.C#j#/C#j#0C#j#1C#j#2C#j#3C#j#4R#j#5R#j#6R#j#7R#-OH$M#%#S#&CG%%S$#4%#&COS#%S,##S#M%#S14%#)NO$S$#$OS$#S-S,)S#S$-#S-)#I)Q###S$k##(#k##*#k##,#k##/#k##5#k#.C#k#/C#k#0C#k#1C#k#2C#k#3C#k#4R#k#5R#k#6R#k#7R#+s&?S\&CS)#$$S8-S9%+s&CS]#$#&CS%$cG('$#S8S9S)%)S%S&S*S2S6S0l#8s#.+#j#9s$=#j#:s$@#V#HGj##s$D#j##s$O#0s$Ps$Os$G#SAj#;s$S#j#<s$V#V#HGj##s$Y#j##s$e#0s$fs$es$\#S7l#=s$ls$i#l#>s$vs$q#l#?s$xC#l#@s%(s$|#l#As%DC#l#Bs%4s%-#2s&Zs%<+s&[##Is%$$s%%s&U%$#+s&_S^)s$t#-#N#I#$$s&[%$#j##)#$)s&^#Is$m%#s$m+s&iS:)#s$p-#S$#I#$$s&e%$#j##)#$)s&h*Cs$Qs$U*Cs$b#*Cs$\#/#PFCs$\s$^*Cs$es$[*C$#/#P>s$c:C#*C#&/#P*Cs$ms$b*Cs$g#/#P,L#s$\,L'#,L,#,L1#5Cs$ZMs$V5C#Hs$V'Cs$HS's$P(s$UFDDE#J'Cs$TS+s$R(s$WFDDE#J1s$XFDDE%#As$YFDDES$'Cs$XS+s$N(s$[FDDE#J1s$\FDDE%#;s$]FDDE'#<Cs$Rs$Y'Cs$[S'#(s$`FDDE#J'Cs$US's$N(s$bFDDE#JVSDCs'3WS_C#s':'Cs$`S'#(s$fFDDE#J'Cs$TS(s$c(s$hFDDE#JCC-s$g'Cs$DS(#(s$kFDDE#J'C%S'*(s$mFDDE#J1s$nFDDE%#.s$oFDDE)s$^#.s$pFDDE,s$_#.s$qFDDE1s$`#.s$rFDDE4s$a#.s$sFDDE8s$b#l#+#s$Ds$>l#,s#$s$v#l#-s#'s%##j#.C#j#/C#j#0C#j#1C#j#2C#j#4R#$GO&CMO%$#&CMG%Q#4%#)HM$Q#$MQ$Os'T#S$S-)QS#-#S$#I#$$s'Y%$#k##(#k##*#k##,#k##.#k##1#k#.C#k#/C#k#0C#k#1C#k#2C#k#4R##S3s%d_G#S3S0S%s%gs%eS&S)S2QS:l#8@%#j#9s%j#j#:s%u#V#HGj##s#b#j##s#l#0s#ms%{s#e#S/j#;s&##j#<s&/#V#HGj##s#r#j##s#}#0s#~s#}s#u#S*l#Cs&9s&6#l#=s&Cs&>#l#As&kC#l#Bs&[s&T#Ds&c#ECs&ds&^s$+s$)#2s('s&r+s((#VS?s&{s&u$s&|s&v&Cs&vs&}%$##s&ys'#&Cs&ys&z%$#4&##IN$Ns(*%$#j##s$4##IS$$S$s(.%$#j##s$.#*Cs%us%z*Cs$##/#P*Cs&+s%|*Cs&-#*Cs&'#/#P*Cs&0s&.*Cs$%#/#P*Cs$,s$//#P,L#s%},L&#,L*#,L/#CCs%ns%`'Cs%pS'#(s%uFDDE#J'Cs%jS+s%r(s%wFDDE#J1s%xFDDE%#'Cs%mS+((s%zFDDE#J1s%{FDDEs$$#;s%|FDDE&#<Cs%js%y'Cs%|S'#(s&#FDDE#J'Cs%mS's%{(s&%FDDE#J'Cs%~S's#|(s&'FDDE#J'Cs&#S(s&&(s&)FDDE#J'Cs%`S(s%z(s&+FDDE#J'Cs%|S's$&(s&-FDDE#J1s&.FDDE%#.s&/FDDE(s%z#.s&0FDDE+s%{#.s&1FDDE.s%|#.s&2FDDE1s%}#.s&3FDDE5s%~#l#+#s%`s%Zl#,s$@s&6#l#-Bs&?#j#.C#j#/C#j#0C#j#1C#j#2C#j#4R#-HN$O#&CGO%$#&CG&%Q#4%#)OQ$N#$QN#QS##IQ$Qs(s%$#k##&#k##s#J#k##)#k##+#k##.#k#.C#k#/C#k#0C#k#1C#k#2C#k#4R#-S0s&~##s'%_G#s'&s'$S3S0S%S&S)S2QS:l#8?&#j#9s')#j#:s'4#V#HGj##s$}#j##s%+#0s%,s':s#[#S/j#;s'>#j#<s'J#V#HGj##s%1#j##s%<#0s%=s%<s#e#S*l#Cs'Ts'Q#l#=s'^s'Y#l#As'zC#l#Bs#ts#m#Ds(/#ECs(0s(&s#ys#w#l#&s(5s(4#l#;s(>s(<#l#$s(<s(;#l#;s(@s(>#-S1s(p8s(p#2s)H#=s)Hs)HS&#,s)6#s)/Bs(uS,2s)L#-s(u$2s)N#=s)Ns)N%#,s)<#s)59s)=)#6###s(|m#1#j#&s(e#&Ks(gS4&Ks(fS4#HMk##$##GH&Ks(eS4k##$#%&##MNk##&#j##%#&Ks(dS4k##,#j###Hj##-#VS`HG0/,($#j#DC#j#EC#k#DC2k#EC##s(_S&#s(Ks(]j#)C#)NI##s%nj##s%p#)S$I##s'xj##s%i#/s$:P,L#s'Q?CM5Cs'MNs'I5C$H#As'GFDDES#'Cs'<S+s'C(s'IFDDE#J1s'JFDDE%#CCs'Is'G'C#S(s'G(s'MFDDE#J'Cs'BS+%(s'OFDDE#J1s'PFDDE%#;s'QFDDE)#<Cs'Fs','C#S(s'N(s'TFDDE#J.s'UFDDE&s'D#l#+#s'&s&|l#,3s'X#l#-7s'a#j#.C#j#/C#j#0C#j#1C#j#4R#&CGH%O#-MN##H&CG$%$#4'#)HI##Mk##%#k#.C#k#/C#k#0C#k#1C#k#4R#$s(;s#uZG#s(:S0s(<S%S&l#84%#j#9s(?#j#:s(J#V#HGj##s&7#j##s&A#0s&Bs(Ps#6#S/j#;s(T#j#<s(`#V#HGj##s&G#j##s&R#0s&Ss&Rs#?#S*l#Cs(js(g#l#=s(ts(o#l#As)4C#l#Bs%.s%'#*Cs(Fs&>*Cs(@#/#P*Cs(?s$~/#P/s(>P/(P,L#s(9,L%#,L'#,L*#?CN5C#Ms(45Cs(9Os(55C$H#1s(3FDDEs#Js$v'Cs${S(s(0(s(5FDDE#J1s(6FDDE#s$v;s(7FDDE&#'Cs'nS(s(4(s(9FDDE#J.s(:FDDE#s()s$j.s(;FDDEs$rs(*#.s(<FDDEs$us(+#.s(=FDDE(s(,#l#+#s'js'dl#,/s(@#l#-4s(I#j#.C#j#/C#j#0C#j#1C#j#4R#&CGN%O#-HM##N&CG$%$#4'##IS##IO%#s&'k##%#k##s$f#k##s*.#k##)#k#.C#k#/C#k#0C#k#1C#k#4R#]Gs#Js)'s)%S0S%S&S2QS#l#87$#j#9s)*#j#:s)5#V#HGj##s&~#j##s',#0s'-s);s%\#S/j#;s)?#j#<s)K#V#HGj##s'2#j##s'=#0s'>s'=s%f#S*l#Cs)Us)R#l#=s)_s)Z#l#As){C#l#Bs%us%n#Ds*0#ECs*1s$3s#Ks%x#l#&s*6s$6#l#;s$:s$8#l#$s*=s*<#l#;s*As*?#9s+3s$[s+,6###s*rm#&#j#&s$S#Gs*_s$U#HU#Gl#&s+As*y#l#%s*{K#j#$s*~#&Ks+$S49s+>s+7s*j6###s*~k#&s*{#j#%K##S%s*|)s'UI##s'Xj##s'Z#)s'NI##s)bj##s'S#FCs)Es)L*C#s)D/#P*Cs)P$/#P,L#s)?,L&#1s)3FDDEs$Js'6;s)4FDDEs':#<Cs'*s(k'C#S(s)1(s)7FDDE#J.s)8FDDE&s)'#l#+#s(es(_l#,s$Rs);#l#-+s)D#j#.C#j#/C#j#0C#j#1C#j#4R#$GN&CMN%$#%Os&~4$#-s&}N)#I##Mk##&#k#.C#k#/C#k#0C#k#1C#k#4R#ZGs&qS3S%s)ys)wS&l#82$#j#9s)|#j#:s*+#V#HGj##s't#j##s'~#0s(#s*1s#-#S/j#;s*5#j#<s*A#V#HGj##s((#j##s(3#0s(4s(3s#6#S*l#Cs*Ks*H#l#=s*Us*P#l#As*}C#l#Bs*ms*f#*Cs)ys'{/#P*Cs*)s)y/#P*Cs*+s&`/#P*Cs*&(/#P,L#s)w,L&#,L)#,L,#'Cs)GS(s)h(s)nFDDE#J.s)oFDDE#s)^s'_.s)pFDDEs'hs)_#.s)qFDDEs'os)`#.s)rFDDEs#@s)a#l#+#s)Cs)=l#,s%0s)u#l#-+s)~#j#.C#j#/C#j#0C#j#1C#j#4R#$Os'V-s&:S##I#$$s,L%$#k##s$4#k##s''#k##)#k##s#@#k#.C#k#/C#k#0C#k#1C#k#4R#]Gs'OS3S%s*Ws*US&S)QS#l#82$#j#9s*Z#j#:s*e#V#HGj##s(R#j##s(\#0s(]s*ks(U#S/j#;s*o#j#<s*{#V#HGj##s(b#j##s(m#0s(ns(ms(e#S*l#Cs+)s+&#l#=s+3s+.#l#As+[C#l#Bs+Ks+D#Ds+S#ECs+Ts%cs#>s(u#l#&s+fs+e#l#;s+os+m#l#$s+ms#|#l#;s%ls%j#9s,cs,\s&)6###s,Fm#&#j#&s,/##Is+j$s+ks,u%$##Is+Rj##$#$s+Ts,y#Is+5%#s+/j###$$s+9s,}?CH.s*UFDDEs',s*Ds',l#+#s*&s)|l#,%s*X#l#-s*fs*a#j#.C##IG#IHk##$#k#.C#VGs+8S#l#8($#j#9s)$#j#:s).#V#HGj##2#j##6#07s+C5#S6j#;s)4#j#<s)?#V#HGj##<#j##B#0s##B?#S&l#Fs+Zs+W#l#Cs+ds+_#l#&s,7s&7#l#;s&;s&9#l#$s,>s$M#l#;s&=s&;#9s-4s--s--6###s,sm#&#j#&s&T#Gs$Us#0#HU#Gl#&s-Bs,z#l#%s,|K#j#$s$^#Gs-'s$`#HU#Gl#$s-Gs-D#l#%s-IK#XSaS#QON6#+s-XQ#$#m#'#l#<s-Xs-Q#l#:s-Ys-R#j#Gs-[#j#HC#j#IC#j#Js-_#j#Ks-`##"). Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Init.Datatypes.prod_ind); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.and_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.zconflictb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.zconflict)|] [|@lemma; @B; @p; @H1; @H0; @H; @b; @a0; @n; @a|] "#$@#+#O#+###4#%#$#6#=#&#'#@#(#7#E#D#H#>#)#*#L#.#3#1#0#/#B#C#F#G#J#I#N#K#O#P#A#:#9#5#2#;#<#8#M#?/#E%#F%#G%#H&#2%#I$#J&#K&#%%#L%#M'#N,(S'(#(#(#(#(#US(#US)#VS*##)$$D$&#*&&D$(#%%#,F#%FG,(#VN%#&H#I&H'I&H&I'$#+&#)22G$4#*44G$6#%%#,J#%JF,(#VN%#&H#I&H'I&H&I'$##J+#/*'$#VS+C#.CEL*'D$$#j#$5#VS,><#F@+;#'+-WS-CES.XOCE#/ZP1.D00#.CEL0&#--,j#$(#VQFs#(#s#,s#'+s###k#%CCXS/CCEEXOCE,6_S0C%E$RP7#96D.CEL/6#665j#$(#VQs#4s#/#Js#2#s#6s##'$#+##j#&s#;#-s#=s#=GD)s#>s#>#$s#@#*s#@s#@%$s#B#%%##K#%KJ#(#'%#-s#Gs#GFG)s#Hs#H#$s#J#*s#Js#J%$s#L#%%##M#%MK#(#'%#k##-#-s#Rs#RJF)s#Ss#S#$s#U#%S#M#$#-s#Ws#WKJ)s#Xs#X#$s#Z#*s#Zs#Z%$s#\#%%##S$#%S$S##(#XS%%#GDj#'-#j#(7#YS1865#Dj#)@#XS%66##j#*s#f#j#+s#g#YS2s#hs#hs#.#DVs#5s#4#Vs#?s#>#Vs#Is#H#WS3FGD&H#IWS4FGD+$#m#'#j#&s#p#j#,S&#j#-S&##"). Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. rewrite bottomup_floor_val. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand N j) n p.
Proof.
  intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.
Scheme kc__5 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__6 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanRefNodes.zconflict); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__5); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.iv_overlap); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Bool.Bool.negb_true_iff); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.Bool.Bool.andb_false_iff); constr:(@Stdlib.ZArith.ZArith_dec.Z_lt_le_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@kc__6); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.Bool.Bool.andb_true_r); constr:(@kc__5 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@p; @n; @a; @l; @Hno; @Hnw; @Hn; @Ha; @b; @z; @l'; @In; @b2; @b1; @s; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @__sat1; @__sat2; @H; @l0; @s0; @__sat0; @Hp; @IH|] "#(##7$/#A#s###L#$#t#r#%#Z#+#&#O#C#)#*#,#(#'#-#{#.#x#k#?#:#/#2$##G#J#I#P#Q#X#7#`#_#d#1#i#~#f$-$)$.$0$(#=#<#;#F#\#b#c#0#g#3#h#j#n#o#q#z#|#}$$$&$'$%#5#6#e$/$1#R#@#K#E#B#D#]#^#p#v#u#V#>#H#W#[#M#S#a#m#l#w$+$*#U#N#T#Y#y$,A#o&#p%#q%#r%#s%#t%#u+#v'#w*#x%#y$#z&#{$#|%#}&#~&$#%$$%$%'$&%#%&$'%$(&$))$*%$+'$,($-&$.$#%%-S*-#-#-#-#-#USB#USC#VSD##US+#%OG$MJUS/.US/*VSE$#&&#.*EPWS0PS#GUS1#k##%#k#$.#;1S#;2S$1P$##F#Nk##'#k##-#k##3#k##4#k#%C#k#&C#j#'8#US2:.;E#k###2k#$=#VS3FNj#($#j#)9#j#*?#j#+@#j#%C#j#&C#2s#%LQ.s#&E#k###=k#$s#(#1&<;#F#Nk##%#k##s#%#k##s#+#k##s#,#k#%C#k#&C#k##;#k#'s#1#j#$s#3#<s#5s#5RL2s#5#Q.s#6E#k###s#-k#$s#8#;s#;PXS4#s#-S%R/#,#E#F#Nj#,F#XS4s#2s#1RL/##FENj#,F#/E#F#N#FGKk##$##FEK/G#F#Nk##%#0'#/J#F#Nk##+#j##&#j##$Ej##-#USFE=/+&$#j#,F#k#,F-(s#XS'(s#YS%$$#'E#(s#\s##$E#'(#,&##F#Kj#-C#'Q*$QE'.#,%##F#Kj#-C#<s#gs#gS%R#s#g##k#'s#gS5k#&s#i##s#jGMVS$ME3$#nS+$s#m$#'S5E#%#S6%#,#.#j#'s#m#j#&s#o#p$#$#/)#V#-LVS3s#r.WS7.$#VG0#WS0PS#1US1#,GE#F#K#FJK3#s#7k##%#3s#9s#7,JG#F#Kk##%#0'#,MJ#F#Kk##+#j##&#j##$Ej##-#VSGGE=/+&$#j#0F#j#1F#k#0F.k#1F#(s$3S,$#s#:'L#$LQ'&#VSHL&&L'%(LVS8$#(s$<SI$#,&R#%$RVS8$#(s$AS9$#('S%##F#K$S%R''##F#K3&#j#2+#&S%*(s$KS-$#-'S'##F#K$S'S%''##F#K'GE#F#K%GJk##$#%EG'JG#F#Kk##%#0'#'MJ#F#Kk##+#j##&#j##$Ej##-#VSJGE=/+&$#j#3C#j#4C#k#3C.k#4C#(s$gSK$S,S'VSLs$cs$b&Os$d%Os$d&Os$dk##$#k##&#%Os$iWSMs$js$iGj##S:#j#+%#%Os$kk##S:#k#+(#US2S)US+S)4CS$USNC5C$J#4CM5C$G#USOCUSPC6CS*USQS*6C#6Cs%+>C$#*C'S(#+)IDDH#S&USRD6Cs%1>C+#*C*S(#+.IDDH#S&[S;/IDDH(#ZSS0IDDH#*C'S..+2IDDH#S&)3IDDH%+#)4IDDH-,#VST5HVSUEJ#F#Nm$s$v#WSVCOGXSWEJ$#l#5)(#l#6>=#l#7s#%s#$#j#8C#j#9C#j#:C#j#;C#$JM&E#$MS$&G#$GJ&M#0%#k###S6%*S$k##$#k##+#k#8C#k#9C#k#:C#k#;C#(s%QSX(s%RSYZE$#S9S-S$Ll#<5&#l#=s#As#>#l#>s#Ks#F#7s#Ns#M#l#?s#Rs#P#WS<s#is#f#j#@s#n#U#Ej#'s#|#%s#yS%$s#Us#q4CJ5C#Gs#C)s#AIDDHs#1s#9s#1l#5#s#/s#*l#6%s#D#l#7s#Ls#K#j#8C#j#9C#j#:C#$EG%#J%s#&Mk##$#k#8C#k#9C#k#:C#XES-@?S$l#<+$#l#=s#]s#Z#l#>s#gs#b#7S,7#l#?s#ns#l#WS7s$)s$&#j#@;#U#Ej#'s$;#ZSZs$=s$<s$2?#El#As$Ds$A#7s$Hs$F#l#?s$Ns$L#l#(s$es$c#(s%~s%o?S=?#?#8C#8C&8CS=9C$#9C&#VS>#S?2S)#s#p5Cs#,Gs#n>Cs#as#iVS@Cs&)WS[C#s&0*C%S(#+s#nIDDH#S&VS@CO*C#S.s#o+s#qIDDH#S&*C%S.s#i+s#sIDDH#S&*Cs#sS(*+s#uIDDH#S&[S;s#vIDDH'#)s#wIDDH&s#o#)s#xIDDH)s#p#)s#yIDDH-s#q#l#5#s#gs#bl#64s#|#l#76s$'#j#8C#j#9C#$GE&#s&<%OM&Ms&>0$#k##%#k##s&E#k##(#k#8C#k#9C#YERLS#PQl#<.$#l#Bs$;s$8#l#=s$Es$@#VSAS##:CS#s%Is#3s#2#8Cs#19C#s#.9Cs#1#VS>#S?2S)#s$?*Cs$.S(s#*+s$9IDDH#S&)s$:IDDHs#'s$2B)s$;IDDHs#&s$3#)s$<IDDH%s$4#l#5#s$*s$%l#6s#3s$?#l#7*s$F#j#8C#j#9C#&s#Xs&Z%OJk###?k##$#k##&#k#8C#k#9C#YELRS#PQl#<+$#l#Bs$Ws$T#l#=s$as$\#VSAP#:CPs%k>s%p##Fs&5Km#$#@s&7#l#?s%zs%y#,s&3NUS\s&4:Fs&5s&3%$#1Qs&gs&f4CG)s$XIDDHs#Es$Ps#El#5#s$Fs$Al#6%s$[#l#7s$cs$b#j#8C#%OEk###s&zk#8C#@LPl#<'$#l#Bs$ns$k#l#=s$xs$s#@QS#l#<+(#l#Bs$rs$o#l#=s$|s$w#)s$hIDDHs#1s$`s#1l#5#s$Vs$Ql#6s#_s$k#l#7s$ss$r#j#8C#j#9C#&s$Js'*k##s#/#k#8C#k#9C#7QLS$l#<($#l#Bs%$s$}#l#=s%.s%)#.s'8EL<s':s':S'S%#s':#G.s';GRWS<$#EVJG#j#C(#j#$s'?#ZPS#S$=9+#:FNs&as#,s#+#1s&ks'5s'4#F#Nm#%#j#(s&k#j#)s'?#j#*s'E#j#+s'F#j#%C#j#&C#j#Ds'5#j#'s'K#j#2s'N#j#,s'O#V#GEj#,s'Q#j#,s'R#YS]s'Ss'Ss&}#Ej#&s'S#YS^s'Ts'=s'2#Ej#'s'T##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

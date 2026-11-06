(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanNodesAux AsanStartLoops AsanNodesStartX Scfg.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Context {SC : StepCfg}.   (* [comment removed for export] *)
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 ph sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
    pose proof (u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U3.
    pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_str0 eq_refl Hev7).
    split; [exact U1|]. split; [|exact U3].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0_early = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
    rewrite e_sp0_early_eq. unfold uE.
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_sp0 eq_refl Hev7).
    exact (u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  (* [comment removed for export] *)
  Lemma SINV0_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(SINV); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(usp); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.e_pg_early); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pagedown); constr:(SINV_SINV0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.SINV0); constr:(ph); constr:(sp); constr:(rdraw); constr:(brk0); constr:(argv); constr:(envp); constr:(uid); constr:(hw); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.NX0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.E0); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.wrap_mem); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.e_pg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.edenot); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.u_e_pg); constr:(Hsp); constr:(Hva); constr:(Hve); constr:(Hfit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesAux.edenot_ev_agree); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesAux.nb_lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.e_pg_early_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.e_sp0_early); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_sp0)|] [|@z; @n; @a; @Hn; @e; @b; @Hev7; @_H; @Hev; @HS; @M; @E|] "#$##-#^#$###8#@#A#B#D#E#F#G#T#%#I#N#<#C#K#(#'#P#*#+#2#1#&#=#9#,#S#U#4#5#6#>#?#J#M#Q#R#V#W#X#Y#Z#[#^#]#\#_#H#`#a#0#:#3#;#L#O#7)#X&#Y$#Z%#[%#\,#])$S1$#$#$#$#$#US)#US*#US)(US*#US2#k##&#VS3CD%S+QUS,D#E$#j#$E#WS4NCD^S5FGHRIJKLNCVS6DS#&S$C\S7FGHRIJKL&#C#2%#k##'#k#%O#'FGHIJKLS%D#P#S&US%C\S8FGIJKLHC#6$#k##&#k#&;#VS9*#%S%QUS,S-#E$#j##&#'FGHIJKLS$D#P#S&US$C#A#.k##%#k#&s#&#&S'C#s#(#9k##=#k#%O#'FGHIJKLS'D#P#S&US'C#s#+#8k##%#k#&s#0#VS+CDj#'s#&#j#%O#&S.C#s#5#s#&k##s#*#k#%O#%S.D#E#=j#(S/#VS0s#-MVS:s#=D#E#Aj#)s#>#`S;FGHRIJKLS<S=S>S?VS0S(MVS@S#MVSAP#ZSBS#S(s#5M#D(s#D+('&#%S(M#E#s#*m#%#(S/M0#QSCl#*84#j#+<#j#,s###V#CDj##s#)#j##s#<#YSDs#=s#6s#1#Dl#-s#Fs#E#%NSEWSFNCD(ES-s#J%$#j#-s#O#j#.s#Q#j#/SG##"). Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. pose proof HS as HS'. destruct HS as [_ HM]. apply HM. rewrite (argH0_SINV0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a HS'). unfold argB0. apply orb_true_intro. left. apply orb_true_intro. left.   (* [comment removed for export] *)
    pose proof (proj1 (proj1 Hva)) as ARGC1. apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold argc, envc; lia.
  Qed.

  Lemma s0_fits : Z.of_nat (length s0) + 1 <= total_arg_bytes argv.
  Proof.
    unfold s0. rewrite total_arg_bytes_Z. destruct argv as [|a r]; [destruct Hva as [H _]; cbn in H; lia|].
    cbn [nth]. rewrite total_arg_bytes_cons. lia.
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 8 * envc + 184 <= bv_unsigned a <= usp + 8 * argc + 8 * envc + 184 + Z.of_nat (length s0) ->
    M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(SINV); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(usp); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(argc); constr:(envc); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(s0); constr:(SINV_SINV0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.SINV0); constr:(ph); constr:(sp); constr:(rdraw); constr:(brk0); constr:(argv); constr:(envp); constr:(uid); constr:(hw); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.NX0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.E0); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.wrap_mem); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argB0); constr:(@Stdlib.Bool.Bool.orb_true_intro); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.entry_page_top); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.W_range); constr:(Hva); constr:(Hve); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.length_bsb_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.stack_image_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.s0_fits); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.total_arg_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.total_arg_bytes_Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.total_arg_bytes_nat); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Datatypes.andb_true_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0_SINV0); constr:(Hsp); constr:(Hfit)|] [|@n; @a; @b; @__ff; @__varmap; @__wit; @__arith; @m; @Ha; @__x1; @__x2; @__x3; @__x4; @__p1; @__sat5; @__sat6; @__sat7; @__sat8; @__sat9; @cstr3; @cstr2; @cstr1; @cstr0; @cstr; @heq_usp; @heq_argc; @heq_envc; @H; @__x5; @__x6; @__x7; @__x8; @__x9; @__x10; @__x11; @Hpd; @TE; @F; @L; @W3; @W2; @W1; @HM; @_H; @HS'; @HS; @M; @E|] "#)q#H$[$*$:$;#$$9##$)#p#r#f#e#b#a#c#g#h$?#-#%#+#'$W#&#.#,#0#O#1#d#(#*#H#2#)$4$e#M#L#X#U#Y#`#j#s#{$'$($.$2$>$K$N$X#E$`$f#3#v#P#Q#^#_#k#l#o#u#~#|#w$#$&$+$,$/$0$3$5$6$8$@$C$D$A$1#8$H#9$J$L$M$O$Y#G$Z$c$b$\$d$[#/#4#5#7$G$F$-$%$$$g$h$i#t#K#T#m#S#N$T#V$<$7#Z$U$R$_#R#W#y#z$P#[$Q$^$E$]$=$V#\#x#}#i$I#]#q$B#n$S$aF$8%$9&$:%$;$$<&$=%$>'$?*$@$$A%$B+$C$$D%$E$$F%$G%$H'$I%$J%$K%$L%$M&$N%$O&$P$$Q%$R%$S($T$$U%$V,$W%$X%$Y*$Z&&S-&#&#&#&#&#US7#US8#US7(US8#USM#k##&#VSNS%F0-(#S9#S:#(%S;#$#+4+#+#&#&#&#0##*#46F%$#@5SO;##'#%'#/'#WSPS'S)F^S<ONPS/MLQRS'S)^S<ONPS/MLQRS0S'VSQHSRCS&F\SSONPS/MLQRC#F$s##%#k##'#k#$S=#AONPMLQRS1H$J#KUS1F\S>ONMLQRPF$s#'$#k##&#k#%s#,#/*#US4S0\S>ONMLQRPS0$s#-$#j##&#AONPMLQRS&H$J#KUS&F$s#2#.k##%#k#%s#7#CS$F$s#9#9k##=#k#$S=#AONPMLQRS$H$J#KUS$F$s#<#8k##%#k#%s#A#\STONPMLQRS&$JHKj#&J#4s#FN+S-&#&#&#0##(#4s#MS&1$#US?s#L@#M;#(s#K##/#@'L;#(s#O##&###/2.#<.##&s#I1#1[SUONMLQRP@s#[#;#0s#c=$##2.##s#Q=%#VSV#s#^(s#_##.#2=#</#VSW2##s#'.1#AVSXN22s###<%#$J(K$J$K$J:K$J,K]SYONPMLQRS@SA%I2$C24+s#{&#&#&#+#&#+#+#+#&#&#&#&#&#&#0#%s#$#/4#/6#4s$.S$1s#2#2$s#'<$#$J#Kj##(#4s$4S.1s#8#2$s#-<$#$J#Kj##/#[SZONPMLQRVS[ML$Cs#;#0S-#s$'#USBM%$#US\LUSBLUS]L;#$C%##s#S+(#s$@#s$A##s#R.(#s$C#%#&s$@&#&#&#&#0##)###6##4VSC#s$N=s$O#US^S5US?S5US_CUS`CUSaC9CI9Cs$V)C$SD#*&GDDE#S#VSb'EBJKVScHS%$J#Km$%#WSdCIFXSeHS%$#l#'*)#l#(10#l#)43#7Is$cl#*$#HWSf8s$e#VSC9s$f%I#7$s$h/$#4s$qSg1s#u#2$s#j$J$K$J$K1FH$J#K%S%Fk##$#%FH1S%F$J#Kk##%#/'#1S)S%$J#Kk##+#j##&#j##$Hj##-#VShFH>/+&$#j#+C#j#$C#k#+C.k#$C#4s%/SiBCs$9$CS;s$:m#$#BCs$@$CS9s$Am#$#BCs$N$CS:s$Om#$#?s%#%Is%#?s$I%Is$I?s$G%Is$G?s#Z%Is#Z?s$A%Is$AVSjs$=s%<%Is$>%Is%>k###s$/k##%#VSEs#Rs%A%Is#S%Is#Sk##(#k##%#0s%S0s%OVSk$#7I%%I%VSl'&7I#k##%#k##'#%I+WSm,+Fj##SF#j#,%#%I*k##SF#k#,(#VSEs#es%V%Is#fk##<s#Ok##$#5CS'3C#S%s#g5CS)3C$F#,CS-,Cs%l:Cs#h#'C%#,Cs%$:Cs#k#'C%#9Cs%Z'C$#,Cs%s)C$S(#*s#sGDDE#S#ZSGs#tGDDES4Ds#uGDDE$#USnD-s#wGDDE$#&l#'#s#ss#ml#(4s#z#l#)s#~s#}#j#-C#j#.C#j#/C#j#0C#j#1S2#(s%vF#H#(s%xS%#$###s%o%#S)/#S'#F'(s%~S)#$###s%u%#S'k##(#k#-C#k#.C#k#/C#k#0C#k#1S2#4s&3So#s%7s%y%$#ZH#%s%?s%Cs%NSHl#*9'#l#2s#9s#6#l#3s#>s#;#l#4s#Is#C#l#5s#Qs#M#l#6s#Ws#S#l#7s#Zs#Y#l#8s#]s#\#l#9s#`s#_#l#:s#cs#b#l#;s#fs#e#l#<s#hs#i#l#=s#ls#m#l#>s#ps#q#WHs%Hs#t#l#?s#xs#v#2FH$J#K7S%Fk##$#7FH2S%F$J#Kk##%#/'#2S)S%$J#Kk##+#j##&#j##$Hj##-#VSpFH>/+&$#j#+C#j#$C#k#+C.k#$C#.SI.#.#.#.#.#.#.#.#.#.#6C#6C(USqS-VSrC#6C,EC$#6C/6C1EC'#6C4EC)#6C86CSI8C$#8C&#8C)#8C,#8C.#8C3#8C5#VSs#StWSuS5#s%'5CS&3Cs%'S'#5CS45CS$3C$S*#3C&S%#5CS+3Cs%-S0#5CS15CS*3C$S*#3C&S)#3C)F#+s&E+#,C#)Cs%3S(#*s%5GDDE#S#)Cs%5S(s$#*s%7GDDE#S#)Cs%7S(s$**s%9GDDE#S#,Cs%I)Cs%:S(#*s%<GDDE#S#&.,C#)Cs%>S(#*s%@GDDE#S#ZSGs%AGDDES,Ds%BGDDE$#+s&V,C#)C#S64*s%FGDDE#S#9Cs%e'C0#,Cs&[)C$S(#*s%KGDDE#S#,Cs'<'Cs$?(:C#s%L'Cs%M#'Cs$=+:C#s%O'C%#9Cs%]'C$#'C#.'C#4'C#;9Cs&S'C$#)C0S6#*s%[GDDE#S#,Cs'M:Cs%[#WSJC4(:Cs%]s$L'Cs$Q#'C#s$PWSJC&#)C(S6#*s%dGDDE#S#'Cs$Zs$V'C#)'C#s$V)C#S(s$^*s%iGDDE#S#'C%s#2)Cs$aS(#*s%lGDDE#S#Ds%mGDDE&#'C)3)Cs$eSD#*s%pGDDE#S#-s%qGDDE&s$Y#-s%rGDDE0s$Z#-s%sGDDE:s$[#-s%tGDDEs#+s$\#-s%uGDDEs#1s$]#-s%vGDDEs#6s$^#-s%wGDDEs#=s$_#-s%xGDDEs#As$`#-s%yGDDEs#Ds$a#-s%zGDDEs#Gs$b#l#'#s%vs%pl#(s#Ns%}#l#)s#\s&$#j#-C#j#.C#j#/C#j#0C#j#@C#j#AC#j#BC#j#CC#j#DC#j#EC#j#FC#j#1S2#%IS$%IS'%IS&%IS,/#S3$CS,S3#S*s&R%#S,#S+s&T(#s(-#s(.##S$s&W(#s(0#%###s&F##S.##S3##SK##s';$CS,#(s(8Sv=S.s'>(s(:S$(s(;S*#$###s(2='#$C)##S$'##+##s(7%#S+#$S.%S+#/%##S*1(s(HS,#$###s(?(s(KS.#$#7S$#k##*#k##2#k##;#k##s#(#k##s#+#k##s#-#k##s#0#k##s#2#k##s#3#k##s#5#k#-C#k#.C#k#/C#k#0C#k#@C#k#AC#k#BC#k#CC#k#DC#k#EC#k#FC#k#1S2#i#9Hs&Zs')s&\s'+s'.s'js(Ts'ds'ts'xs('s%:S1S&S+S$S3SKSwSxSySHl#*s#D$#l#2s%ns%k#l#3s%ss%p#l#4s%~s%x#l#5s&*s&&#l#6s&0s&,#l#7s&3s&2#l#8s&6s&5#l#9s&9s&8#l#:s&<s&;#l#;s&?s&>#l#<s&As&B#l#=s&Es&F#l#>s&Is&J#WHs&Ms'q#l#?s%$s$~#XSzs&fs&es%8#WS{s&is&h#l#Gs&ps&l#l#Hs'@s'<#l#IS|s'B#l#Js'Is'G#j#Ks'Y#j#Ls'k#V#FHj##s'\#j##s'n#>s'os'^s'P#Hj#?s'^#j#Ms'r#V#FHj##s'a#j##s'u#>s'vs'cs'\#Hl#?s'xs'c#WS}s'{s'z#WSLs(8s()#WS~s(#s'~#WSLs(*s(%#$Js(RKm#$#AONPMLQRS$S&dT#ONPS/MLQRT$S@SAT%S$S+S&S'ZT&Js(Vs(T%$#VHS&#j#Ns(Y#j#Os(`#V#FHj##s(f#j##s(y#>s(zs(ss(n#Fl#PHs)&#l#Qs))s)(#j#,s)+#j#Qs)@#j#%s)F#j#Rs)C#j#ST'##"). Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartX.x_sound_envscan); constr:(segs); constr:(A); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.NX0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.LIMIT); constr:(SINV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0); constr:(ph); constr:(sp); constr:(rdraw); constr:(argv); constr:(envp); constr:(uid); constr:(hw); constr:(FS0); constr:(SC); constr:(SEGS_wx); constr:(SEGS_in_hull); constr:(HULL_ok); constr:(SINV_frame); constr:(we1); constr:(we2); constr:(we3); constr:(Xenv); constr:(Fe1); constr:(Fe2); constr:(Fe3); constr:(Ee); constr:(De1); constr:(De2); constr:(De3); constr:(Hva); constr:(Hve); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.sp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.sp_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_vals); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_envp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_sp0)|] [|@H; @M; @E; @H0; @a|] "##S#(#^#$###%#3#5#6#0#N#2#4#7#8#P#O#X#Z#\#[#Y#1#R#S#T#]#V#^#U#_#'#&#`#+#,#-#.#/#9#:#;#<#=#>#?#@#A#B#C#D#E#F#G#H#I#J#K#L#M#Q#W%#\$#]%[S&KFLGHMN#S'##########UO#UP#UO(UP#US(#k##&#VICDWS)ECDj#$$#j#%&#j#&J#VIECVQ.FUR3US*-VS##GUS$#VS%&#$(#UR8$$#VQ7CVS+$#VS#+HUS$#VS%.#$(#$#0VS,)#VS-)#YS.S/S0ECDj#'$#j#$7#j#(B#j#%?#j#&J#WS1ECDj#$A#j#%s###j#&J#i#HS2S3S4S5S6Is#1S7S8S9S:S;S<S=S>S?S@SASBSCSDSESFSGKFLGHMNSHSISJSK@'##"). Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartX.x_sound_pnscan); constr:(segs); constr:(A); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.NX0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.LIMIT); constr:(SINV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0); constr:(ph); constr:(sp); constr:(rdraw); constr:(argv); constr:(envp); constr:(uid); constr:(hw); constr:(FS0); constr:(SC); constr:(SEGS_wx); constr:(SEGS_in_hull); constr:(HULL_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0_high); constr:(Hsp); constr:(Hva); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymRun3.env_agree); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanInit.argH0_agree); constr:(@Corelib.Init.Logic.eq_refl); constr:(SINV_frame); constr:(SINV_agree); constr:(wp0); constr:(wp1); constr:(wp2); constr:(wp3); constr:(wp4); constr:(Xpn); constr:(Fp0); constr:(Fp1); constr:(Fp2); constr:(Fp3); constr:(Fp4); constr:(Ep); constr:(Dp0); constr:(Dp1); constr:(Dp2); constr:(Dp3); constr:(Dp4); constr:(Hve); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.sp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.sp_hi); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_vals); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Lists.ListDef.nth); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_str0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesStartXInit.GenericInit.SINV0_sp0)|] [|@H; @a; @E; @E'; @M; @H0|] "##j#(#p#$#5###%#3#6#>#2#4#7#8#0#1#@#?#D#E#H#.#&#g#i#h#e#B#C#F#G#I#J#K#b#c#l#p#n#o#d#q#'#r#+#,#-#/#9#:#;#<#=#L#M#N#O#P#Q#R#S#T#U#V#W#X#Y#Z#[#\#]#^#_#`#a#A#f#k#j#m(#k$#l%#m%#n$#o$[OJGKDHLM#S+##########UP#UQ#]OJGKDHLMCEWS,R#S#`S-JGKDHLMS.S$FCEj#$$#j#%'#j#&I#WS/S%FC_S0JGKDHLMS&FCEj#$$#j#%,#j#'I#j#&I#VS1RS#UP5UQ#US2#k##3#VNCEWS3FCEj#$$#j#(&#j#&I#VNFCVS';GUS(@US4-%#D&#VS)&#$(#%'H&#VS)*#$&#'s#,'#'#######US(#$*#VS's#.CVS*$#US5@XS66S7D#%B#&#$)#VS*)#VS8)#YS9S:S&FCEj#)$#j#$A#j#%s#9#j#(s#)#j#&I#WS;FCEj#$s#+#j#(s#-#j#&I#i#RS<S=S>S%S?Ns#HS@SASBSCSDs#:s#4s#3SESFSGSHSISJSKSLSMSNSOSPSQSRSSSTSUSVSWJGKDHLMS$SXSYSZs#*'##"). Qed.
  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.

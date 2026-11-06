(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec ShapeAlg ShapeLaws Scfg Spec HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import SpinAlg ASegs AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsTRList AsDriverLaws
  AsCXXHeap AsStack0 AXPres AXFuzz_stmt AsDrvDefs AsMainPre AsMainTails AsInstance AsInstanceMain AS_InstDefs AS_InstLaws1 AS_InstanceKit
  AsanInit AsPlanImages AsMainState AsStartupTop.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AS_SREALIZES : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    @srealizes asegs hunspell_scfg
      (init_config asegs OSSVerify.boost_beast.http_request.images.Asan.M.init_pc
                   OSSVerify.boost_beast.http_request.images.Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Definition AS_REALIZES : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    @realizes asegs hunspell_scfg
      (init_config asegs OSSVerify.boost_beast.http_request.images.Asan.M.init_pc
                   OSSVerify.boost_beast.http_request.images.Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AFUZZ : Prop :=
  forall (HCEIL : HeapCeil) (H : asr),
    asan_rt_hyps H -> asan_rt_hyps5 H -> asan_rt_hyps5x H -> asan_rt_hyps6 -> asan_rt_hyps6b -> asan_rt_hyps7 H -> asan_rt_hyps8 H ->
    incl TRLIST (as_TR H) ->
    afuzz_stmt H.

(* [comment removed for export] *)
Definition ACOST : Prop := forall k : mctx, ACOST_at k.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ACOST_of_one : forall k0 : mctx, ACOST_at k0 -> ACOST.
Proof. intros k0 C k. exact C. Qed.

Definition AFUZZ_COST_MAX : Z := 2 ^ 20 * 7800 - 13 * 2 ^ 26.   (* [comment removed for export] *)

Lemma AMAIN_COST_inst : forall (HCEIL : HeapCeil) (p : iparams),
  AMAIN_COST (KHp p) = 13 * 2 ^ 28 + 4 * afuzz_cost (KHp p) (2 ^ 26).
Proof. intros HCEIL p. unfold AMAIN_COST. cbn [as_Cm as_Cf KHp]. unfold ICm, ICf. change (2 ^ 26 <=? 64512) with false. cbv iota. lia. Qed.

Lemma ACOST_of_bound : (forall (HCEIL : HeapCeil) (p : iparams), afuzz_cost (KHp p) (2 ^ 26) <= AFUZZ_COST_MAX) -> ACOST.
Proof.
  intros B k. unfold ACOST_at, KH. rewrite AMAIN_COST_inst. specialize (B (KCEIL k) (kip k)).
  unfold AFUZZ_COST_MAX, AsIface7.ACWILD, AsIface7.AWMAX in *. lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.list Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.option Sort Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.Fs.Fs); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.TSet); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.t_die); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.msg_usage); constr:(@Stdlib.Lists.List.hd); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.msg_cannot_open); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.list_byte_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.dot_path); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.t_alt2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.t_opened_dir); constr:(@LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.t_opened); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeLaws.t_emit_has_nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.W); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.t_exit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.exit_code); constr:(@Corelib.Init.Datatypes.cons); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeLaws.t_alt2_has_nil_l); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.spec); constr:(@kc__1 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))); constr:(@kc__3 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))|] [|@x; @data; @l1; @l2; @l3; @l0; @path; @argv; @l; @b; @o; @p; @a0; @fs|] "#Qh#2#V###<#M#$#%#5#(#L#'#&#,#.#)#*#-#/#G#+#1#D#A#0#V#9#7#6#C#N#Q#S#W#X#:#B#=#H#?#>#P#O#T#E#F#K#R#I#J#8#@#U#;5#D$#E%#F%#G&#H$#I%#J%#K&#L$#M%#N%#O%#P%#Q%#R$#S$#T'#U(1S*1#1#US+#US,#UH#UH#2%&%#C'#$#F&(&G'#$#L#S-##############################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################VS&sO<FVS'$#+F$#I,FsO=,FS#/FI%&#0IF+G$#O-CO%$#nJ$sOH$#$D'#%$#%##,nE#$##D+#%#)##nE#$##D-#%#.##nE#$##D1#%#/##&sOLsOJO'#$#PnH$sOO$#&DC#%#&%#'#(#nH$sOP$#)DC#%#sOH%#*#&#nH$sOQ$#+DC#%#sOL%#,#)#2S.U$#j#,sOS#US/sOZ2sOV&sOWsOU#'#(&#US0'.#C)%#*sO]GC&sO^sO\#'#$#I$s#&P/FP%$#0PF$s##S$-CS$%$#nJ$sOh$#$D&#%$#%##)nE#$##Ds#+#%#(##nE#$##Ds#-#%#+##nE#$##Ds#1#%#,##*sOlOK&sOmsOk#'#$#MnH$sOp$#&DC#%#'%#'#(#nH$sOq$#)DC#%#3%#*#&#U#Bj#,sOr#*sOtF@&sOusOs#'#(s#$#.@K)$#VS&sO{GVS's#C#$s#:M,GsO{,GS#/GM%&#0MG+L$#Q-CQ%$#nJ$sP*$#$D'#%$#%##,nE#$##D+#%#)##nE#$##D-#%#.##nE#$##D0#%#/##*sP.KG*sP/S$#&sP0sP.#'#$#NnH$sP3$#&DC#%#(%#'#(#U#s#@j#,sP4#,LsP4,LS#/LQ%4#0QL+K$#N-CN%$#nJ$sP?$#$D'#%$#%##:nE#$##D+#%#)##nE#$##D-#%#<##nE#$##DC#%#=##U#s#Oj#-E#(s#Ns#_.s#JM)$#,KS#/KN%0#0NK+I$#R-CR%$#nJ$sPP$#$D'#%$#%##6nE#$##D+#%#)##nE#$##DC#%#8##U#s#_j#-E#(s#^s#1.s#ZQ)$#/IR%.#0RI+O$#S(-CS(%$#nJ$sP_$#$D'#%$#%##4nE#$##DC#%#)##U#s#mj#-E#(s#ls#*.s#hN)$#WS)s#,?#UJsPg+P$#S%-CS%%$#nJ$sPl$#$DC#%$#%##2U#s#yj#.)#(s#x).s#tS%)$#WS)+*#j#,sPs#U#Cj#,sPu#(s$#s#,.s#{R)$#YS1sPy-&#Cl#.s#15#3;7#Cl#-s#GE#3s#+s#(#Cl#-s#_E#3s#=s#:#Cl#-s$FE#*sQ%FC*sQ&I#*sQ'M#&sQ(sQ&#'#(s$3#)#2j#,sQ+#j#$sQ-#V#FCj#,sQ.#j#,sQ0#4sQ1s#Z/#Cj#)sQ1#j#/sQ3#V#FCj#,sQ4#j#,sQ6#4sQ7s#~s#x#Cj#)sQ7#j#0sQ9#V#FCj#,sQ:#j#,sQ<#4sQ=s$Gs$?#FWS2FCs$Jm#$#j#1S3#j#+sQ@##"). Qed.

Section Top.
  Hypothesis AF : AFUZZ.
  Hypothesis AC : ACOST.

  (* [comment removed for export] *)
  Lemma as_main_phase : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (c : config),
    valid_argv (in_argv inp) -> valid_fs (in_fs inp) ->
    P_main sp brk mbase rnd inp c -> realizes asegs c (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp c Hva Hfs PM.
    destruct (as_instance_kit AC sp brk mbase rnd inp c PM)
      as (HCEIL & H & s0 & regs & mem & B & tid & can & HH & DL & (H5 & H5x & H6 & H7 & H8 & ATR) & LIVE & PRE & EFS).
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in PRE, EFS. rewrite <- EFS.
    assert (H6b : asan_rt_hyps6b).
    { exact (@inst_rt_hyps6b HCEIL). }
    apply (as_main_realizes_closed H HH DL (AF HCEIL H HH H5 H5x H6 H6b H7 H8 ATR) sp (in_argv inp) s0 msF mo regs mem B tid can Hva);
      [rewrite EFS; exact Hfs | exact PRE].
  Qed.

  Theorem as_realizes_spec : AS_REALIZES.
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs [Huid _] Hhw.
    rewrite <- LIMIT_eq.
    apply (as_startup_realizes sp brk mbase rnd inp (spec (in_argv inp) (in_fs inp))); try assumption; [apply spec_has_nil|].
    intros c PM. exact (as_main_phase sp brk mbase rnd inp c Hva Hfs PM).
  Qed.

  Theorem as_srealizes_spec : AS_SREALIZES.
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs Hcr Hhw.
    apply srealizes_of_realizes. exact (as_realizes_spec sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs Hcr Hhw).
  Qed.
End Top.

Check as_realizes_spec.
Check as_srealizes_spec.

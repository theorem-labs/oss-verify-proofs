(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanNodesAux AsanStartLoops AsanNodesStartX Scfg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemanticsfLinuxProcessSem5Statehfcsp_window_lo46Stdlib6ZArith6BinInt1Zlc2le35stdpp9bitvectorbdefinitionsn9bbv_unsignedhfcsp_window_hi79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~r32uEn92bv37Corelib4Init9Datatypeshg16option37Corelib4Init5Logichi32eq01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hk0ae_pg_earlyhk0be_sp0_earlyr38pagedown79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hq63env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~hue5LIMIThue5argH0hk03NX0hk08XEnvScanr36x_stmthk07XPnScanhk07XLayouthg14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypein57Segmenthk06atablein58PhdrInfo69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~isbewx_segs_nowraphg14Nonehg14boolhg15false3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjj1cfind_segmentr37in_hullr37hull_okhk09x_envscanhi33andlc3addhk0bx_envscan_klc2ltlc3powhg14Somejj1afetch_wordn97Z_to_bvjj18is_ecallhi31I3h5LinuxProcessSemantics5Riscv5Instrjv15instrn92BVn94BvWfhg14prodhg14pairhg14true3h5LinuxProcessSemantics5Riscv7DecodeCkk2adecode_anyjv1|41L1o1a1djv13SZ8jv17ALU_ADDjv15OpImmjv15BC_NEjv16Branchhk08x_pnscanhk0ax_pnscan_klc3subjv15Storejv13SZ1jv15BC_EQ3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutkua9EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem2Fslib2Fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runllc8valid_spllcavalid_argvllcavalid_envpllch0entry_stack_fitshue5SINV069OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AxSymRun3~~~~~~lse9env_agree" s.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  (* [comment removed for export] *)
  Variable segs : ltac2:(zQ "20!imd!iqa@1$0$1").
  Context {SC : StepCfg}.   (* [comment removed for export] *)
  Variable A : ltac2:(zQ "10!ir5$0").
  Variable ph : ltac2:(zQ "10!irf$0").
  Hypothesis SEGS_wx : ltac2:(zQ "10!jg6@1$0?4segs").
  Hypothesis SEGS_in_hull : ltac2:(zQ "b0!h9!hj7!iqa!p6!jh8!ji0!ji8!hh9!jm8!jn8!vc>1a@1$a@1$0#k0>0@3$1$5@2$9?1A@2$3@1$0#k0^1$6@3$1@1$7$2@3$8?4segs@2$3@1$0#k0^2+1@1$4$2").
  Hypothesis HULL_ok : ltac2:(zQ "10!jo2@1$0?1A").

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : ltac2:(zQ "90!joc!jp9!jq0!hj7!hjd!jq6!n4!jr5!jra@2$1@2$6Z@1$0?1A@2$1@2$7@2$2@1$0?1A+c@2$8+2+k0@3$3$4@1$5?1A@2$2@1$0?1A+c").
  Hypothesis Fe1 : ltac2:(zQ "80!h9!vc!js0!hh9!hj7!js8!joc!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$7@1$0#k0@1$6?1A@2$2@1$1@1$0#i0?3we1").
  Hypothesis Fe2 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!joc!jq0!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+4@2$2@1$1@1$0#i0?3we2").
  Hypothesis Fe3 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!joc!jq0!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+8@2$2@1$1@1$0#i0?3we3").
  Hypothesis Ee : ltac2:(zQ "50!ji0!ji8!hj7!ju0!jp9@2$4@3$2$0@1$3?3we1$1@2$4@3$2$0@1$3?3we2$1@3$2$0@1$3?3we3$1").
  Hypothesis De1 : ltac2:(zQ "f0!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!kja!hj7!km8!kn6!ko3@3$b@1$8@2$6$3$2@1$c?3we1@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
  Hypothesis De2 : ltac2:(zQ "e1!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!koa!kp5&@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$a@1$8@2$6$3$2@1$b?3we2@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
  Hypothesis De3 : ltac2:(zQ "e0!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!kpe!kq7@3$a@1$8@2$6$3$2@1$b?3we3@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8+4").
  Hypothesis Xpn : ltac2:(zQ "90!kr1!jp9!jq0!hj7!hjd!krd!n4!jr5!jra@2$1@2$6+8@1$0?1A@2$1@2$7@2$2@1$0?1A+c@2$8+2+k0@3$3$4@1$5?1A@2$2@1$0?1A+c").
  Hypothesis Fp0 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!kr1!ksb!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+8@2$2@1$1@1$0#i0?3wp0").
  Hypothesis Fp1 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!kr1!ksb!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+4@2$2@1$1@1$0#i0?3wp1").
  Hypothesis Fp2 : ltac2:(zQ "80!h9!vc!js0!hh9!hj7!js8!kr1!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$7@1$0#k0@1$6?1A@2$2@1$1@1$0#i0?3wp2").
  Hypothesis Fp3 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!kr1!jq0!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+4@2$2@1$1@1$0#i0?3wp3").
  Hypothesis Fp4 : ltac2:(zQ "90!h9!vc!js0!hh9!hj7!js8!kr1!jq0!jt6@3$4@1$3@1$1@1$0#i0@2$5?4segs@2$8@1$0#k0@2$7@1$6?1A+8@2$2@1$1@1$0#i0?3wp4").
  Hypothesis Ep : ltac2:(zQ "50!ji0!ji8!hj7!ju0!jp9@2$4@3$2$0@1$3?3wp0$1@2$4@3$2$0@1$3?3wp1$1@2$4@3$2$0@1$3?3wp2$1@2$4@3$2$0@1$3?3wp3$1@3$2$0@1$3?3wp4$1").
  Hypothesis Dp0 : ltac2:(zQ "e0!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!ko3!kt1@3$a@1$8@2$6$3$2@1$b?3wp0@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
  Hypothesis Dp1 : ltac2:(zQ "e1!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!koa!kp5&@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$a@1$8@2$6$3$2@1$b?3wp1@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
  Hypothesis Dp2 : ltac2:(zQ "f0!h9!juc!hjd!kh5!khe!ki3!kia!js0!ji8!hh9!kj2!hj7!km8!kn6!kta@3$b@1$9@2$6$3$2@1$c?3wp2@2$7@2$6$3$2@4$a$3$2@5$d$e$8@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+vvfKv$1@2$5@1$0#c+vvf+4").
  Hypothesis Dp3 : ltac2:(zQ "e0!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!ku1!kq7@3$a@1$8@2$6$3$2@1$b?3wp3@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
  Hypothesis Dp4 : ltac2:(zQ "e0!h9!juc!hjd!kh5!khe!ki3!kia!js0!hh9!kj2!hj7!km8!kpe!kq7@3$a@1$8@2$6$3$2@1$b?3wp4@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").

  (* 75d69e00: the launch.  [AsanInit.inp] now has twenty fields, so every one of them
     is a section variable here too; [apc] is the image's ELF entry.  The old [Hfit]
     ([entry_stack_fits sp argv envp]) is gone from AsanInit's lemmas: at this revision
     the block is pinned by [Hlau] instead.  Donor for the shape:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/As/AsanNodesStartXInit.v:40-154. *)
  Variable sp : word.
  Variable rdraw : ltac2:(zQ "10!lhe$0").   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile sigmask : word.
  Variable abterm : bool.
  Variable vasz : VaSize.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Variable chrdr sigdfl sigterm : bool.
  Variable apc : N.
  Variable FS0 : ltac2:(zQ "10!ll6$0").
  Hypothesis Hsp : ltac2:(zQ "10!lo8@1$0?2sp").
  Hypothesis Hva : ltac2:(zQ "10!lp4@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!lq2@1$0?4envp").

  #[local] Notation INP :=
    (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp
                  kern execfn chrdr sigdfl sigterm).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kern execfn).
  #[local] Notation argH0a := (AsanInit.argH0 sp rdraw argv envp kern execfn).
  #[local] Notation SINV0a :=
    (AsanInit.SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile
                    sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc).
  #[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).

  (* 75d69e00: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct.
     Both are new premises of the revised model; the published statements discharge them. *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  (* [comment removed for export] *)
  Variable SINV : ltac2:(zQ "40!h9!vc!hh9!hu7>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : ltac2:(zQ "60!h9!hu7!vc!hh9!ijb!mga>1E$1>2E'$1>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@3$5$4^3^2>0@2?4SINV^4^2@2?4SINV^4^3").

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let rseq := kb_rseq kern.
  Let top := ed_top rdraw.
  (* argv[0]'s first byte: the head C plus the [arch_align_stack] pad W.  WAS
     [usp + 8 * argc + 8 * envc + 184], which is OBSOLETE -- the strings moved to the
     TOP of the stack VMA and no sp-relative constant reaches them. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : ltac2:(zQ "40!h9!kd!n4!p6@2$2$1@2$3@1$0#k0?2sp").
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : ltac2:(zQ "40!h9!q4!n4!p6@2$2@2$3@1$0#k0?2sp$1").
  Proof. ndestruct Hsp as (_ & H & _). exact H. Qed.

  (* instantiate the hypotheses AsanInit's Section discharged (its [inst_hyps]) *)
  Ltac inst_init H :=
    repeat match type of H with
           | ?P -> _ =>
               let Hp := fresh "Hp" in
               assert (Hp : P) by first [ assumption | exact Hsp | exact Hva | exact Hve
                                        | exact Hlaunch | exact Hlau ];
               specialize (H Hp); clear Hp
           end.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (AsanInit.u_e_envp ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as U1.
    inst_init U1.
    pose proof (AsanInit.u_e_str0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as U3.
    inst_init U3.
    pose proof (AsanInit.uE0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as UA.
    inst_init UA. ndestruct UA as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0a n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0a e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E E0a e_str0 eq_refl Hev7).
    split; [unfold usp, argc; exact U1|]. split.
    - change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
      rewrite (edenot_ev_agree NX0 E E0a (EVar V_ENVC) eq_refl Hev7).
      apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
    - unfold STR0, usp, rseq, top, cat_string_off. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0_early = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0a n) by (intros n Hn; apply Hev; exact Hn).
    rewrite e_sp0_early_eq. unfold uE.
    rewrite (edenot_ev_agree NX0 E E0a e_sp0 eq_refl Hev7).
    pose proof (AsanInit.u_e_sp0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as U.
    inst_init U. exact U.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_pg : ltac2:(zQ "a0!h9!v7!vc!hh9!hj7!hjd!hne!hoc!hpb!hu7>1E$9>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2?4SINV^2^1@3$4$5@2$1^3$6@1$8@2$1^3$7").
  Proof.
    intros E M HS. rewrite (SINV0_sp0 E M HS). apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0a n) by (intros n Hn; apply Hev; exact Hn).
    rewrite e_pg_early_eq. unfold uE.
    rewrite (edenot_ev_agree NX0 E E0a e_pg eq_refl Hev7).
    pose proof (AsanInit.u_e_pg ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as U.
    inst_init U. unfold usp. exact U.
  Qed.

  (* the hidden-argument predicate, as [argB0], for the two range lemmas below *)
  Lemma argH0_argB0 : forall E M a, SINV E M -> argH0a E a = AsanInit.argB0 sp rdraw argv envp kern execfn a.
  Proof.
    intros E M a HS. apply SINV_SINV0 in HS.
    pose proof (AsanInit.argH0_SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as AB.
    inst_init AB. exact (AB E M a HS).
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (argH0_argB0 E M a HS) as AB.
    apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. rewrite AB.
    unfold AsanInit.argB0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha.
    (* the lower end needs argc >= 1: the envp array starts at [usp + 8*argc + 16],
       which is above [usp + 24] only because argv is non-empty *)
    pose proof Hva as HA. destruct HA as [Hav _].
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (argH0_argB0 E M a HS) as AB.
    apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. rewrite AB.
    unfold AsanInit.argB0. apply orb_true_intro. right.
    (* [STR0] <= a <= [STR0] + |argv[0]| < top: argv[0] and its NUL are inside the
       string area, and the area ends 8 bytes below the stack VMA's end *)
    pose proof (AsanInit.str0_hi sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as SH.
    inst_init SH.
    pose proof (AsanInit.s0_in_strings sp rdraw argv envp kern execfn apc) as SI.
    inst_init SI.
    apply andb_true_intro. unfold STR0, usp, s0, rseq, top, cat_string_off in *.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* the three facts AsanNodesStartX asks for about [argH0], at this section's names *)
  Lemma argH0_high' : forall E (a : word), argH0a E a = true -> CEIL <= bv_unsigned a.
  Proof.
    pose proof (AsanInit.argH0_high sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc) as AH.
    inst_init AH. exact AH.
  Qed.

  Lemma argH0_agree' : forall E E' (a : word), env_agree NX0 E E' -> argH0a E a = argH0a E' a.
  Proof. exact (AsanInit.argH0_agree sp rdraw argv envp kern execfn). Qed.

  Lemma E_SP0' : AP.expr_vars_lt NX0 e_sp0_early = true.
  Proof. exact AsanInit.E_SP0. Qed.

  (* AsanNodesStartX quantifies the launch as [inp], so its premises arrive as
     [valid_argv (in_argv ?inp)].  [exact Hva] cannot solve that -- [in_argv ?inp]
     and [argv] are not first-order unifiable -- so restate the three at [INP],
     where the head symbol matches and [?inp := INP] follows. *)
  Lemma Hva' : valid_argv (in_argv INP).
  Proof. exact Hva. Qed.
  Lemma Hve' : valid_envp (in_envp INP).
  Proof. exact Hve. Qed.

  (* every remaining premise of [x_sound_envscan] / [x_sound_pnscan], in one tactic.
     The launch arguments are NOT passed by name: they are explicit arguments of the
     Section, and [(x := v)] in an application names only IMPLICIT ones. *)
  Ltac close_init :=
    first [ exact Hva' | exact Hve' | exact Hlaunch | exact Hlau
          | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp0
          | exact sp_lo | exact sp_hi | exact E_SP0'
          | exact argH0_high' | exact argH0_agree' | exact SINV_frame | exact SINV_agree
          | eassumption ].

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 AsanInit.LIMIT SINV argH0a FS0 XEnvScan.
  Proof.
    eapply (x_sound_envscan segs A NX0 AsanInit.LIMIT SINV argH0a FS0).
    all: close_init.
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 AsanInit.LIMIT SINV argH0a FS0 XPnScan.
  Proof.
    eapply (x_sound_pnscan segs A NX0 AsanInit.LIMIT SINV argH0a FS0).
    all: close_init.
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A NX0 AsanInit.LIMIT SINV argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.

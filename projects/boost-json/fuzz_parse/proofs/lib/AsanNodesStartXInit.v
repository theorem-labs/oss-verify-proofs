(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : ltac2:(zQ "10!lhe$0").   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : ltac2:(zQ "10!ll6$0").
  Hypothesis Hsp : ltac2:(zQ "10!lo8@1$0?2sp").
  Hypothesis Hva : ltac2:(zQ "10!lp4@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!lq2@1$0?4envp").
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : ltac2:(zQ "10!lr0@3$0?2sp?4argv?4envp").   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : ltac2:(zQ "40!h9!vc!hh9!hu7>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
  Hypothesis SINV_SINV0 : ltac2:(zQ "50!h9!vc!hh9!ls5!hu7>1E$4>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>0@2?4SINV^2^1@a$3?2ph?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw^3^2").
  Hypothesis SINV_frame : ltac2:(zQ "81!h9!vc!hh9!hj7!ji0!kja!ij2!hu7&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1E$7>1M~0>2M'~0>0>1a@1$1@1$0#k0>0@3$3$4@9$6?2ph?2sp?5rdraw?4argv?4envp?3uid?2hw^4^1$5@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2>0@2?4SINV^4^3@2?4SINV^5^3").
  Hypothesis SINV_agree : ltac2:(zQ "60!h9!hu7!vc!hh9!ijb!mga>1E$1>2E'$1>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@3$5$4^3^2>0@2?4SINV^4^2@2?4SINV^4^3").

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].

  Lemma sp_lo : ltac2:(zQ "40!h9!kd!n4!p6@2$2$1@2$3@1$0#k0?2sp").
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : ltac2:(zQ "40!h9!q4!n4!p6@2$2@2$3@1$0#k0?2sp$1").
  Proof. ndestruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
    pose proof (u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U3.
    npose (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & _ & U2 & _).
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

  (* [comment removed for export] *)
  Lemma SINV0_pg : ltac2:(zQ "a0!h9!v7!vc!hh9!hj7!hjd!hne!hoc!hpb!hu7>1E$9>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2?4SINV^2^1@3$4$5@2$1^3$6@1$8@2$1^3$7").
  Proof.
    intros E M HS. rewrite (SINV0_sp0 E M HS). apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
    rewrite e_pg_early_eq. unfold uE.
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_pg eq_refl Hev7).
    eapply u_e_pg; eassumption.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. pose proof HS as HS'. destruct HS as [_ HM]. apply HM. rewrite (argH0_SINV0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a HS'). unfold argB0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
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
    intros E M a HS Ha. apply SINV_SINV0 in HS. pose proof HS as HS'. destruct HS as [_ HM]. apply HM. rewrite (argH0_SINV0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a HS'). unfold argB0. apply orb_true_intro. right.
    npose (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
    pose proof (length_bsb_eq ph sp rdraw argv envp uid hw) as L. pose proof s0_fits as F.
    pose proof (total_arg_bytes_Z envp) as TE.
    unfold stack_image_size in L.
    assert (Hpd : 0 <= (8 - (8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160
                              + total_arg_bytes argv + total_arg_bytes envp) mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Theorem init_x_sound_envscan : ltac2:(zQ "50!ii9!ij2!ijb!ik2!ike@a$4?2fx?4segs?2SC?1A$2$0?4SINV@7$1?2ph?2sp?5rdraw?4argv?4envp?3uid?2hw?3FS0$3").
  Proof.
    eapply (x_sound_envscan segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0);
      eauto using sp_lo, sp_hi, SINV0_vals, SINV0_envp, SINV0_sp0.
  Qed.

  Theorem init_x_sound_pnscan : ltac2:(zQ "50!ii9!ij2!ijb!il7!ike@a$4?2fx?4segs?2SC?1A$2$0?4SINV@7$1?2ph?2sp?5rdraw?4argv?4envp?3uid?2hw?3FS0$3").
  Proof.
    eapply (x_sound_pnscan segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0);
      eauto using sp_lo, sp_hi, SINV0_vals, SINV0_str0, SINV0_sp0,
        (argH0_high ph sp rdraw argv envp uid hw Hsp Hva), (argH0_agree ph sp rdraw argv envp uid hw).
  Qed.
  Theorem init_x_sound_layout : ltac2:(zQ "50!ii9!ij2!ijb!im2!ike@a$4?2fx?4segs?2SC?1A$2$0?4SINV@7$1?2ph?2sp?5rdraw?4argv?4envp?3uid?2hw?3FS0$3").
  Proof. apply x_sound_layout. Qed.
End GenericInit.

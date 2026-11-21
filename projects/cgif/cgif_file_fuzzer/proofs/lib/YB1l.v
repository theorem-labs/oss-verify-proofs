(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; AT_EXECFN; the launch's group id; the launch's SIGPIPE disposition left free): changed urnd, SINV, argH, E0a, startup_cert, HOLES_sound, tfib_XN1_sound, tfib_startup; added kb, execfn, sdef, INP, RZ, Hmb, Hzr, Hnof and 8 more. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK06 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB12 YB1h YB1k YB1j YB1p.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition tfib_XN1 (i : nat) (args : list expr) (cs : acs) : option acs :=
match i with O => xn_sealedtop NX0G args cs | S O => xn_range_align NX0G args cs | S (S _) => None end.
#[local] Instance tfibstartup_fx : YK11.FPState := YK11.fx0.
Section b.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream. Variable tmp : Fs.Fs.
(* [kb] and [execfn] joined [YA02]'s section in the start-up port (YA02.v:51-52): [YA02.inp]
   discharges FIFTEEN arguments now, and [YA0h]'s section took them with it.  [kb_rseq kb]
   stays FREE -- see the note in YA0h.v. *)
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdef : bool.
Let INP : ProcInput := YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Let RZ : Z := rseq_z (kb_rseq kb).
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk TSEGS brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hzr : YK06.zero_random_draw (ed_random rdraw).
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask INP.
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
Hypothesis Hvi : valid_input INP.
#[local] Notation SINV := (SINV0 TPH AsanUbsan.M.init_pc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
#[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
#[local] Notation E0a := (E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation TOP := (YA02.TOP sp).
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound TSEGS IT0.
Variable HS : nat -> option acs.
Variable hole_le : nat -> nat -> bool.
Variable startup_plan : plan.
Variable startup_shape : shape.
Variables KC0 BFUEL FUEL : nat.
Hypothesis startup_cert :
check TSEGS IT0 TFIB NX0G LIM RZ (XNG TSEGS tfib_XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None (init_acs_of_g RZ TFIB) startup_plan
= COk startup_shape.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt TSEGS TFIB LIM TOP HS SINV argH HOLES FSQ.
(* [YA02]'s [argH0_high]/[argH0_agree]/[SINV0_frame]/[SINV0_agree] are applied by unification
   on their CONCLUSION rather than by a hand-written positional list: the start-up port changed both
   the variable set and the hypothesis set they discharge, and only the conclusion is
   checkable by eye.  Idiom from the landed YA0b.v:169. *)
Lemma AH : forall E (a : word), argH E a = true -> TOP <= bv_unsigned a.
(* [argH0_high]'s leading discharged [apc : N] does not occur in its type after its binder,
   and this section has no [apc] for [assumption] to find; it is given the image's entry, the
   [apc] of this file's [SINV]. *)
Proof. intros E a H. exact (argH0_high AsanUbsan.M.init_pc sp rdraw argv envp kb execfn Hva E a H). Qed.
Lemma AA : forall E E' (a : word), env_agree NX0G E E' -> argH E a = argH E' a.
Proof. reflexivity. Qed.
Lemma SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Proof. intros E M M' Hf HSv. eapply SINV0_frame; try eassumption. Unshelve. all: assumption. Qed.
Lemma SA : forall E E' M, env_agree NX0G E E' -> SINV E M -> SINV E' M.
Proof. intros E E' M Hag HSv. eapply SINV0_agree; try eassumption. Unshelve. all: assumption. Qed.
Lemma tfib_XN1_sound : forall i args, node1_stmt TSEGS TFIB NX0G LIM TOP SINV argH FSQ always (tfib_XN1 i args).
Proof.
intros [|i] args.
- cbn [tfib_XN1]. rewrite tsegs_tfasegs.
exact (xn_sealedtop_sound TFIB NX0G LIM TOP
(eq_rect _ (fun s => YK04.wx_segs_nowrap s) tfib_wx _ tsegs_tfasegs)
(eq_rect _ (fun s => forall a : word, in_hull TFIB (bv_unsigned a) = false -> find_segment s (bv_unsigned a) 1 = None) tfib_in_hull _ tsegs_tfasegs)
tfib_hull_okP (top_ok0 sp Hsp) SINV argH AH AA SF SA FSQ args).
- destruct i as [|i].
+ cbn [tfib_XN1]. apply xn_range_align_sound.
+ intros cs cs' E R FULL model T _ _ H _. cbn [tfib_XN1] in H. discriminate H.
Qed.
Theorem tfib_startup :
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT INP)
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
(* [asan_startup_init] took [apc] and [Z.of_N apc = a_entry A] as its LAST two arguments before
   the start-up port; [apc] is a section variable of YA0h now, so both move into the middle of the
   discharged list.  Applying by unification instead of position is what makes that reshuffle
   a non-event here. *)
eapply asan_startup_init;
try solve [ assumption | reflexivity
| exact tfib_img_facts | exact tfib_wx | exact tfib_in_hull | exact tfib_res_len
| exact tfib_hull_ok | exact tfib_shadow_ok | exact tfib_res_cover | exact tfib_segs_wr
| exact tfib_Xenv | exact tfib_Fe1 | exact tfib_Fe2 | exact tfib_Fe3 | exact tfib_Ee
| exact tfib_De1 | exact tfib_De2 | exact tfib_De3
| exact tfib_Xpn | exact tfib_Fp0 | exact tfib_Fp1 | exact tfib_Fp2 | exact tfib_Fp3
| exact tfib_Fp4 | exact tfib_Ep | exact tfib_Dp0 | exact tfib_Dp1 | exact tfib_Dp2
| exact tfib_Dp3 | exact tfib_Dp4
| exact tfib_SUM_imemset | exact tfib_SUM_memset | exact tfib_SUM_imemcpy
| exact tfib_SUM_memcpy | exact tfib_SUM_miz | exact tfib_SUM_istrncpy | exact tfib_SUM_popfree
| exact tfib_XN1_sound | exact startup_cert ].
(* [itab_sound TSEGS ?IT0] comes before the goal that fixes [?IT0], and [assumption] does not
   instantiate an evar; it is closed once [startup_cert] has fixed it. *)
all: exact IT0_ok.
Qed.
End b.

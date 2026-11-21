(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1l.v (theorem-labs/oss-verify-proofs@6b32741d849a) with its module paths changed. It states no image address of its own: its only definition, tfib_XN1, is byte-equal to the one in the collector scratch file ZReplyB/YB1l.v of the image-B' run, h-pre-b3's YB1l.v sha256 87a357f127631515470c94b5ea0baeacebe3482df4bf7f68c7ec365998508f4c (port-reply's tools/startup/replyscratch.py, run sha cf47e327b300f8ce; CHECKED here, the two tfib_XN1 bodies are the same text). The sealed-top pc/end that scratch file carries for this image, 0x661ec / 0x662a0 (GetMaxUserVirtualAddress 0x661b8 + 52 / + 232), live in lib/Reusable/YB1k.v in this unit and are regenerated there - checked equal. The theorem below consumes the plan of lib/Reusable/YB05.v, the table of lib/Reusable/YB12.v and the states of lib/Reusable/YB01.v and YB03.v, all of the same image-B' run. *)
(* Modified by Theorem Labs, 2026-10-29: route R1 (h-hpreset-7; merged here) edits this file: SINV0, SINV0_frame and SINV0_agree are applied to TSEGS as their new first argument (the SINV notation and the tfib_hull_okP application). A re-relocation from cgif must re-apply it. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack). *)
(* Read from: fuzz_preset.asan-ubsan (omx-clap-core/fuzz_preset asan-ubsan, harness fix #102) pin sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994; unstripped twin sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175 *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB12 YB1h YB1k YB1j YB1p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
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
(* The launch's kernel record, exec file name and SIGPIPE disposition, as in [YA02]'s
   Section: free, so the CONFIG_RSEQ flag [RZ] is the run's own. *)
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdef : bool.
Let INP : ProcInput := YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Let RZ : Z := rseq_z (kb_rseq (in_kernel INP)).
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk TSEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask INP.
Hypothesis Hvl : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
#[local] Notation SINV := (SINV0 TSEGS TPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef AsanUbsan.M.init_pc).
#[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
#[local] Notation E0a := (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
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
(* [YA02]'s lemmas applied by unification on their conclusions (cgif/cgif_file_fuzzer's
   A/AB1l.v in this working copy has the same idiom). *)
Lemma AH : forall E (a : word), argH E a = true -> TOP <= bv_unsigned a.
(* [argH0_high] also abstracts the entry pc [apc], which its statement does not read. *)
Proof. intros E a H. eapply argH0_high; try eassumption. Unshelve. all: first [assumption | exact AsanUbsan.M.init_pc]. Qed.
Lemma AA : forall E E' (a : word), env_agree NX0G E E' -> argH E a = argH E' a.
Proof. reflexivity. Qed.
(* this unit's start-up invariant also carries memnorm (YA02.SINV0's last conjunct), so its frame
   lemma takes the memnorm step as well *)
Lemma SF : forall E M M', (forall a, argH E a = true -> M' a = M a) ->
(YAkMemnorm.memnorm TSEGS M -> YAkMemnorm.memnorm TSEGS M') -> SINV E M -> SINV E M'.
Proof. intros E M M' Hf Hmn HSv. eapply SINV0_frame; try eassumption. Unshelve. all: assumption. Qed.
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
(* [asan_startup_init] is applied by unification: its Section grew ([kb], [execfn], [apc]
   and the launch premises), and the entry pc [apc] is fixed by the goal. *)
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
(* [itab_sound TSEGS ?IT0] comes before the goal that fixes [?IT0]; it is closed once
   [startup_cert] has fixed it. *)
all: exact IT0_ok.
Qed.
End b.

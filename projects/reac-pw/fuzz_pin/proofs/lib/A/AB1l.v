(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1l.v (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ-sized auxiliary vector; the launch's ProcInput, mmap base and entry draw; the start-up nodes' CONFIG_RSEQ argument); internal commit ids in comments replaced by public commits or removed. *)
(* Ported to libreac/fuzz_knock by c-libc-fmt (lane KnockA) from proofs/cgif/cgif_file_fuzzer/lib/A/AB1l.v at theorem-labs/oss-verify-proofs@6b32741d849a: module paths renamed; the donor states no image literal, so none is relocated (its image facts come from A/AB12, AB1h, AB1k and AB1p). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_pin.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1p.
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
#[local] Notation SINV := (SINV0 TPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef Asan.M.init_pc).
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
Proof. intros E a H. eapply argH0_high; try eassumption. Unshelve. all: first [assumption | exact Asan.M.init_pc]. Qed.
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
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT INP)
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

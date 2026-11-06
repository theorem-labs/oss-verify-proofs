(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1l.v, with its module paths changed; every one of its 1 image numerals names the same object in omx-clap-core/fuzz_preset's ASan build as in cgif_file_fuzzer.asan's (c-asan's checker e55e1b52a8a0, all SAME-* verdicts). *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob 43b4d1fe4e96); a re-relocation of this file from cgif must be checked against that edit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1p.
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
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk TSEGS brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
#[local] Notation SINV := (SINV0 TSEGS TPH sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation E0a := (E0 TPH sp rdraw brk0 argv envp uid hw).
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
check TSEGS IT0 TFIB NX0G LIM (XNG TSEGS tfib_XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None (init_acs_of_g TFIB) startup_plan
= COk startup_shape.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt TSEGS TFIB LIM TOP HS SINV argH HOLES FSQ.
Lemma tfib_XN1_sound : forall i args, node1_stmt TSEGS TFIB NX0G LIM TOP SINV argH FSQ always (tfib_XN1 i args).
Proof.
intros [|i] args.
- cbn [tfib_XN1]. rewrite tsegs_tfasegs.
exact (xn_sealedtop_sound TFIB NX0G LIM TOP
(eq_rect _ (fun s => YK04.wx_segs_nowrap s) tfib_wx _ tsegs_tfasegs)
(eq_rect _ (fun s => forall a : word, in_hull TFIB (bv_unsigned a) = false -> find_segment s (bv_unsigned a) 1 = None) tfib_in_hull _ tsegs_tfasegs)
tfib_hull_okP (top_ok0 sp Hsp) SINV argH
(argH0_high TPH sp rdraw argv envp uid hw Hsp Hva) (argH0_agree TPH sp rdraw argv envp uid hw)
(SINV0_frame TSEGS TPH sp rdraw brk0 argv envp uid hw) (SINV0_agree TSEGS TPH sp rdraw brk0 argv envp uid hw) FSQ args).
- destruct i as [|i].
+ cbn [tfib_XN1]. apply xn_range_align_sound.
+ intros cs cs' E R FULL model T _ _ H _. cbn [tfib_XN1] in H. discriminate H.
Qed.
Theorem tfib_startup :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
exact (asan_startup_init TSEGS TFIB TPH tfib_img_facts tfib_wx tfib_in_hull tfib_res_len tfib_hull_ok tfib_shadow_ok
tfib_res_cover tfib_segs_wr
_ _ _ _ _ _ _ _ tfib_Xenv tfib_Fe1 tfib_Fe2 tfib_Fe3 tfib_Ee tfib_De1 tfib_De2 tfib_De3
tfib_Xpn tfib_Fp0 tfib_Fp1 tfib_Fp2 tfib_Fp3 tfib_Fp4 tfib_Ep tfib_Dp0 tfib_Dp1 tfib_Dp2 tfib_Dp3 tfib_Dp4
sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
tfib_SUM_imemset tfib_SUM_memset tfib_SUM_imemcpy tfib_SUM_memcpy tfib_SUM_miz tfib_SUM_istrncpy tfib_SUM_popfree
tfib_XN1 tfib_XN1_sound IT0 IT0_ok HS hole_le startup_plan startup_shape KC0 BFUEL FUEL startup_cert
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound
Asan.M.init_pc eq_refl).
Qed.
End b.

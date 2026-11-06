(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB06 YB0l YB0o YB0n YB0t.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition tra_XN1 (i : nat) (args : list expr) (cs : acs) : option acs :=
match i with O => xn_sealedtop NX0G args cs | S O => xn_range_align NX0G args cs | S (S _) => None end.
#[local] Instance trastartup_fx : YK11.FPState := YK11.fx0.
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
#[local] Notation SINV := (SINV0 TPH sp rdraw brk0 argv envp uid hw).
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
check TSEGS IT0 TRA NX0G LIM (XNG TSEGS tra_XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None (init_acs_of_g TRA) startup_plan
= COk startup_shape.
Hypothesis startup_live : lv startup_plan = true.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt TSEGS TRA LIM TOP HS SINV argH HOLES FSQ.
Lemma tra_XN1_sound : forall i args, node1_stmt TSEGS TRA NX0G LIM TOP SINV argH FSQ always (tra_XN1 i args).
Proof.
intros [|i] args.
- cbn [tra_XN1]. rewrite tsegs_tfasegs.
exact (xn_sealedtop_sound TRA NX0G LIM TOP
(eq_rect _ (fun s => YK05.wx_segs_nowrap s) tra_wx _ tsegs_tfasegs)
(eq_rect _ (fun s => forall a : word, in_hull TRA (bv_unsigned a) = false -> find_segment s (bv_unsigned a) 1 = None) tra_in_hull _ tsegs_tfasegs)
tra_hull_okP (top_ok0 sp Hsp) SINV argH
(argH0_high TPH sp rdraw argv envp uid hw Hsp Hva) (argH0_agree TPH sp rdraw argv envp uid hw)
(SINV0_frame TPH sp rdraw brk0 argv envp uid hw) (SINV0_agree TPH sp rdraw brk0 argv envp uid hw) FSQ args).
- destruct i as [|i].
+ cbn [tra_XN1]. apply xn_range_align_sound.
+ intros bm cs cs' E R FULL model T _ _ H _. cbn [tra_XN1] in H. discriminate H.
Qed.
Theorem tra_startup :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
exact (asan_startup_init TSEGS TRA TPH tra_img_facts tra_wx tra_in_hull tra_res_len tra_hull_ok tra_shadow_ok
tra_res_cover tra_segs_wr
_ _ _ _ _ _ _ _ tra_Xenv tra_Fe1 tra_Fe2 tra_Fe3 tra_Ee tra_De1 tra_De2 tra_De3
tra_Xpn tra_Fp0 tra_Fp1 tra_Fp2 tra_Fp3 tra_Fp4 tra_Ep tra_Dp0 tra_Dp1 tra_Dp2 tra_Dp3 tra_Dp4
sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
tra_SUM_imemset tra_SUM_memset tra_SUM_imemcpy tra_SUM_memcpy tra_SUM_miz tra_SUM_istrncpy tra_SUM_popfree
tra_XN1 tra_XN1_sound IT0 IT0_ok HS hole_le startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_live
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound
Asan.M.init_pc eq_refl).
Qed.
End b.

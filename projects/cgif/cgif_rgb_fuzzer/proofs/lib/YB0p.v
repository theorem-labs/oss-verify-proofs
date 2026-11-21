(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (tra_startup stated over the run's ProcInput and mmap base in place of its separate fields, with the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits and the recorded-kernel premise on the run's kernel; SINV0, argH0 and E0 over the input; the start-up certificate's check and init_acs_of_g take the run's CONFIG_RSEQ flag; valid_input's channel-reader conjunct Hrdr passed to asan_startup_init for cs_ok's new co_rdr field). *)
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
(* 08b1429: over the run's input [inp] (recipes/procinput-fields.md step 3), as YA02. *)
Variable inp : ProcInput.
#[local] Notation FSQ := (in_fs inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk TSEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Huid : valid_id (in_uid inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* #38 (rules 12f, 12r): [valid_input]'s own recorded-kernel conjunct
   (75d69e00:Run.v:4596) in place of the whole-record pin; kb_rseq stays free. *)
Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
(* LPS 727298f3: [valid_input]'s channel-reader conjunct, for [cs_ok]'s new last field
   [co_rdr]; [YA0h.asan_startup_init] takes it right after [Hrec]. *)
Hypothesis Hrdr : in_channel_reader inp = true.
#[local] Notation SINV := (SINV0 TRA TPH sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0a := (E0 sp rdraw brk0 inp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation TOP := (YA02.TOP sp).
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound TSEGS IT0.
Variable HS : nat -> option acs.
Variable hole_le : nat -> nat -> bool.
Variable startup_plan : plan.
Variable startup_shape : shape.
Variables KC0 BFUEL FUEL : nat.
(* #38: [init_acs_of_g] gained the run's CONFIG_RSEQ flag as its FIRST argument
   (YA01.v:719, via [init_kn_g] YA01.v:713).  Taken from the run, as YA02.v:84-86
   takes it; nothing here pins it.
   #38 (rule 2g): [APG.check] gained the same flag as a section [Variable rz : Z]
   declared after [LIMIT] (YA0c.v), so it is the sixth argument of the discharged
   [check], before [XN]; this is the shape [YA0h.asan_startup_init] now expects. *)
Hypothesis startup_cert :
check TSEGS IT0 TRA NX0G LIM (APC.rseq_z (kb_rseq (in_kernel inp))) (XNG TSEGS tra_XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None
(init_acs_of_g (APC.rseq_z (kb_rseq (in_kernel inp))) TRA) startup_plan
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
(argH0_high sp rdraw inp Hsp Hva) (argH0_agree sp rdraw inp)
(SINV0_frame TRA TPH sp rdraw brk0 mbase inp) (SINV0_agree TRA TPH sp rdraw brk0 mbase inp) FSQ args).
- destruct i as [|i].
+ cbn [tra_XN1]. apply xn_range_align_sound.
+ intros bm cs cs' E R FULL model T _ _ H _. cbn [tra_XN1] in H. discriminate H.
Qed.
Theorem tra_startup :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
inp)
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
exact (asan_startup_init TSEGS TRA TPH tra_img_facts tra_wx tra_in_hull tra_res_len tra_hull_ok tra_shadow_ok
tra_res_cover tra_segs_wr
_ _ _ _ _ _ _ _ tra_Xenv tra_Fe1 tra_Fe2 tra_Fe3 tra_Ee tra_De1 tra_De2 tra_De3
tra_Xpn tra_Fp0 tra_Fp1 tra_Fp2 tra_Fp3 tra_Fp4 tra_Ep tra_Dp0 tra_Dp1 tra_Dp2 tra_Dp3 tra_Dp4
sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec Hrdr
tra_SUM_imemset tra_SUM_memset tra_SUM_imemcpy tra_SUM_memcpy tra_SUM_miz tra_SUM_istrncpy tra_SUM_popfree
tra_XN1 tra_XN1_sound IT0 IT0_ok HS hole_le startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_live
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound
Asan.M.init_pc eq_refl).
Qed.
End b.

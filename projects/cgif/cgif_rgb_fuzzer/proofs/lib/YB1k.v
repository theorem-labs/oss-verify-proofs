(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the trb start-up section is over the run's ProcInput, with the mmap base's validity, valid_launch, the launch premise entry_launch_ok_va and valid_input's recorded-kernel conjunct in place of the separate input fields and entry_stack_fits; SINV0, argH0 and E0 over the run; the start-up certificate's check and init_acs_of_g take the run's CONFIG_RSEQ flag; valid_input's channel-reader conjunct Hrdr passed to asan_startup_init for cs_ok's new co_rdr field). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB11 YB1g YB1j YB1i YB1o.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition trb_XN1 (i : nat) (args : list expr) (cs : acs) : option acs :=
match i with O => xn_sealedtop NX0G args cs | S O => xn_range_align NX0G args cs | S (S _) => None end.
#[local] Instance trbstartup_fx : YK11.FPState := YK11.fx0.
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
#[local] Notation SINV := (SINV0 TRB TPH sp rdraw brk0 mbase inp).
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
check TSEGS IT0 TRB NX0G LIM (APC.rseq_z (kb_rseq (in_kernel inp))) (XNG TSEGS trb_XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None
(init_acs_of_g (APC.rseq_z (kb_rseq (in_kernel inp))) TRB) startup_plan
= COk startup_shape.
Hypothesis startup_live : lv startup_plan = true.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt TSEGS TRB LIM TOP HS SINV argH HOLES FSQ.
Lemma trb_XN1_sound : forall i args, node1_stmt TSEGS TRB NX0G LIM TOP SINV argH FSQ always (trb_XN1 i args).
Proof.
intros [|i] args.
- cbn [trb_XN1]. rewrite tsegs_tfasegs.
exact (xn_sealedtop_sound TRB NX0G LIM TOP
(eq_rect _ (fun s => YK05.wx_segs_nowrap s) trb_wx _ tsegs_tfasegs)
(eq_rect _ (fun s => forall a : word, in_hull TRB (bv_unsigned a) = false -> find_segment s (bv_unsigned a) 1 = None) trb_in_hull _ tsegs_tfasegs)
trb_hull_okP (top_ok0 sp Hsp) SINV argH
(argH0_high sp rdraw inp Hsp Hva) (argH0_agree sp rdraw inp)
(SINV0_frame TRB TPH sp rdraw brk0 mbase inp) (SINV0_agree TRB TPH sp rdraw brk0 mbase inp) FSQ args).
- destruct i as [|i].
+ cbn [trb_XN1]. apply xn_range_align_sound.
+ intros bm cs cs' E R FULL model T _ _ H _. cbn [trb_XN1] in H. discriminate H.
Qed.
Theorem trb_startup :
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
inp)
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
exact (asan_startup_init TSEGS TRB TPH trb_img_facts trb_wx trb_in_hull trb_res_len trb_hull_ok trb_shadow_ok
trb_res_cover trb_segs_wr
_ _ _ _ _ _ _ _ trb_Xenv trb_Fe1 trb_Fe2 trb_Fe3 trb_Ee trb_De1 trb_De2 trb_De3
trb_Xpn trb_Fp0 trb_Fp1 trb_Fp2 trb_Fp3 trb_Fp4 trb_Ep trb_Dp0 trb_Dp1 trb_Dp2 trb_Dp3 trb_Dp4
sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec Hrdr
trb_SUM_imemset trb_SUM_memset trb_SUM_imemcpy trb_SUM_memcpy trb_SUM_miz trb_SUM_istrncpy trb_SUM_popfree
trb_XN1 trb_XN1_sound IT0 IT0_ok HS hole_le startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_live
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound
AsanUbsan.M.init_pc eq_refl).
Qed.
End b.

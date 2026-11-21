(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (hs_all_ok and HS_asan_ok per value of the CONFIG_RSEQ flag over the hand-off states computed in the build, in place of the three recorded hand-off lemmas; handoff_holes over the launch's ProcInput and launch premises; PlanRegen imported). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X047 X0jw X080.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms.
Local Instance topah_fx : X0ms.FPState := X0ms.fx0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0n0 X0k2 X0m4 X0m6
X0li X0lh X0ll X0lj X0kj X0ly X0lv PlanRegen X0n2 X0n6 X0lx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X03o X03r X03n X03l X03m X03k
X0fy X0fg X0ed X0ef X03q X03p X0jf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X002.

From OSSVerify.speex.speex_decode_fuzzer_float.images Require AsanUbsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0v5 X1ab.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require X0lk X0lz X0lw X0n3 X0n7 X0m9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0up X0um X0uk X0ul X0uj X16j X161 X14y X150 X0uo X0un X19w.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r1.
Module B_TWIN.

Import OSSVerify.speex.speex_decode_fuzzer_float.images.AsanUbsan.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1da.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X080.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ms.
Local Instance topah_fx : X0ms.FPState := X0ms.fx0.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0mx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0n0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0li OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ll OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0kj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0n3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0n7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m9.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X03o.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0up OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0um OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ul OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X150 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0un OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19w.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r1.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* per value of the plan's CONFIG_RSEQ flag [r] (through [hs_start_ok r], A/X03k.v) *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
(Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_B ch && hs_lib_ok ch)%bool.

Lemma asan_segtop : img_hi ASAN_B = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_B = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : X0kj.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

(* every hand-off state AS/X0n3.v computes passes [hs_all_ok] at its flag; [HS_both r] is empty
   at every other [r] *)
Lemma HS_asan_ok : forall r h ch, HS_both r h = Some ch -> hs_all_ok r ch = true.
Proof.
intros r h ch. unfold HS_both.
destruct (Z.eqb r 0) eqn:E0; [apply Z.eqb_eq in E0; subst r;
  apply (hlookup_forall (hs_all_ok 0)); vm_cast_no_check (eq_refl true)|].
destruct (Z.eqb r 1) eqn:E1; [apply Z.eqb_eq in E1; subst r;
  apply (hlookup_forall (hs_all_ok 1)); vm_cast_no_check (eq_refl true)|].
discriminate.
Qed.

Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Main.

Variable T : list (list byte) -> Fs.Fs -> TSet.
Variable D : list (list byte) -> Fs.Fs -> Prop.
Hypothesis T_nil : forall argv fs, T argv fs [].
Hypothesis MAIN : forall (argv : list (list byte)) (fs : Fs.Fs), valid_argv argv -> D argv fs ->
forall c, STARTF RTA OUT_repA ERR_repA XENVA LIB_A argv fs c -> realizes bsegs c (T argv fs).

Lemma handoff_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp -> D (in_argv inp) (in_fs inp) ->
APS.holes_stmt ASEGS ASAN_B NX0 X0kj.LIMIT (HS_both (rseq_z (kb_rseq (in_kernel inp))))
(SINV0 APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
(fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).
Proof using MAIN.
intros sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau HD.
intros h ch Hh E R FULL model HC.
pose proof (HS_asan_ok _ h ch Hh) as HT. unfold hs_all_ok in HT.
apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
exact (hs_hole_rt ASAN_B NX0 X0kj.LIMIT (in_fs inp) APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau
asan_in_hull asan_hull_ok asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
(hs_lib ASAN_B NX0 X0kj.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok (argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva)
E ch R FULL model HC HTL)
(T (in_argv inp) (in_fs inp)) (MAIN (in_argv inp) (in_fs inp) Hva HD)).
Qed.

Theorem asan_side_of_main : forall en inp,
valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input_either inp -> D (in_argv inp) (in_fs inp) ->
srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
target_alloc_limit inp)
(T (in_argv inp) (in_fs inp)).
Proof using T_nil MAIN.
exact (asan_startup_gen IT0 IT0_ok HS_both su_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes T D T_nil handoff_holes).
Qed.
End Main.
End B_TWIN.

Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* per value of the plan's CONFIG_RSEQ flag [r] (through [hs_start_ok r], A/X03k.v) *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
(Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_A ch && hs_lib_ok ch)%bool.

Lemma asan_segtop : img_hi ASAN_A = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_A = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : X0kj.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

(* every hand-off state AS/X0n2.v computes passes [hs_all_ok] at its flag; [HS_asan r] is empty
   at every other [r] *)
Lemma HS_asan_ok : forall r h ch, HS_asan r h = Some ch -> hs_all_ok r ch = true.
Proof.
intros r h ch. unfold HS_asan.
destruct (Z.eqb r 0) eqn:E0; [apply Z.eqb_eq in E0; subst r;
  apply (hlookup_forall (hs_all_ok 0)); vm_cast_no_check (eq_refl true)|].
destruct (Z.eqb r 1) eqn:E1; [apply Z.eqb_eq in E1; subst r;
  apply (hlookup_forall (hs_all_ok 1)); vm_cast_no_check (eq_refl true)|].
discriminate.
Qed.

Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Main.

Variable T : list (list byte) -> Fs.Fs -> TSet.
Variable D : list (list byte) -> Fs.Fs -> Prop.
Hypothesis T_nil : forall argv fs, T argv fs [].
Hypothesis MAIN : forall (argv : list (list byte)) (fs : Fs.Fs), valid_argv argv -> D argv fs ->
forall c, STARTF RTA OUT_repA ERR_repA XENVA LIB_A argv fs c -> realizes asegs c (T argv fs).

Lemma handoff_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp -> D (in_argv inp) (in_fs inp) ->
APS.holes_stmt ASEGS ASAN_A NX0 X0kj.LIMIT (HS_asan (rseq_z (kb_rseq (in_kernel inp))))
(SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
(fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).
Proof using MAIN.
intros sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau HD.
intros h ch Hh E R FULL model HC.
pose proof (HS_asan_ok _ h ch Hh) as HT. unfold hs_all_ok in HT.
apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
exact (hs_hole_rt ASAN_A NX0 X0kj.LIMIT (in_fs inp) APH Asan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau
asan_in_hull asan_hull_ok asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
(hs_lib ASAN_A NX0 X0kj.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok (argH0_high Asan.M.init_pc sp rdraw inp Hsp Hva)
E ch R FULL model HC HTL)
(T (in_argv inp) (in_fs inp)) (MAIN (in_argv inp) (in_fs inp) Hva HD)).
Qed.

Theorem asan_side_of_main : forall en inp,
valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input_either inp -> D (in_argv inp) (in_fs inp) ->
srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
target_alloc_limit inp)
(T (in_argv inp) (in_fs inp)).
Proof using T_nil MAIN.
exact (asan_startup_gen IT0 IT0_ok HS_asan su_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes T D T_nil handoff_holes).
Qed.
End Main.

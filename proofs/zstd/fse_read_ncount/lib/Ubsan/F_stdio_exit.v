(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_refl :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
end.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
impl usegs (at_node usegs) t Q ms -> (forall r ms', Q r ms' -> evt usegs (Q' r) ms') ->
impl usegs (at_node usegs) t Q' ms.
Proof.
induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt' : forall {St A} (c : M St A) s Q Q' ms,
implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
implM usegs c s Q' ms.
Proof.
intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.
Section StdioExit.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
#[using="get_set set_set set_get"] Theorem stdio_exit_proof : stdio_exit_spec_stmt get_so set_so.
Proof.
unfold stdio_exit_spec_stmt. intros until tm1. intros ST LIBC OFL SIN SOUT SERR SOF SEF GOT GUARD MI -> LO GLO SP47.
unfold GLOBALS_TOP, got_ssp, ssp_guard in *.
destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
change usegs with usegs in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
remember (get_so s) as so eqn:ESO.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x1edc8); (RSTDOUT_BUF, 0x4fa08)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 6) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
- change 64 with (2^6). Local Ltac2 Set LiaHints.tbl := fun () => "01k0?12428134302.110124405130.90   13740802296.11015685060272.95 16622434386.93 16622434386.95 17416023030.92 17798943865.11019006120615.93 20392859730.93 20392859730.95 20433961190.84 2172651747.2   22961942245.0  23062596592.11124490529657.11024997440241.90 25387547474.93 25387547474.95 25435258127.95 25566553219.93 26323796050.93 26323796050.95 26494647592.90 26494647592.93 26494647592.95 26773361674.90 27335527918.90 27335527918.93 27810329426.93 27810329426.95 28626770891.11129073259129.11129108108270.90 29108108270.93 30886953776.11131017011448.11031399144472.88 31401241662.10831835855737.11031852377209.11132027975233.0  32162886226.93 32162886226.95 32377744366.90 32377744366.93 32600174396.90 33510054780.86 34202051574.92 34813674361.1113523399062.5   35561507310.90 35561507310.93 36562602617.11137616238057.11137738008046.90 37738008046.93 38238797294.90 38238797294.93 3830406688.89  3834310178.109 39941652000.87 40201484047.11840201484047.93 40201484047.98 40881292791.11141072247790.90 41072247790.93 42831019478.93 42831019478.95 43000880110.90 43000880110.93 43035628988.3  43061776187.82 43104399792.93 436370553.111  43931159869.90 44516413688.11045221239098.90 45221239098.93 4866047897.93  49553520722.93 49553520722.95 50470234962.93 50470234962.95 50575413842.93 50575413842.95 50916096121.1105180980284.93  52712884706.11054164510851.11654164510851.90 54164510851.96 56278489841.90 57136921209.11058135773316.85 58266672110.90 58266672110.93 58477417733.11159178106163.95 59308587280.3  59310859210.1  59310859210.2  59624177333.0  62385105144.11162583080755.93 63135048575.0  63448664057.11163617233490.93 63617233490.95 63779719325.95 63792152522.83 63967133241.82 66095943928.11167081926311.90 67180215544.11167432794360.11167663283182.90 67663283182.93 68094715463.87 7426071800.110 8052345080.110 9509867768.111 00000100<00H00L00T00\00a00f00k01301;01@01F01G01S01X01]01e01m02202702?02G02H02I02J02U02]02e02m03503@03E03M03U03Z03f03g03l04104204304;04C04K04S04W04\04a04f05205:05B05G05N05V05^05f05n06206:06B06G06L06M06R06Z06b06h06n07607>07B07J07N07S07`07l08208808908A08I08Q08Y08a08i08n09209309809=09>09C09H09P09X09`09a09f09n0:30:80:90:E0:J0:K0:R0:Z0:b0:c0:i0:j0;60;;0;G0;S0;[0;c0;h0<40<@0<LFS3LTB2CF2HqS2LO3GLO3LTBS2HBS2LO3GLOS2LO3GLOS3LTBS3LTBS3LTBS2LO3GLOS2LO3GLOS3LTBS4SP47SS2LO3GLO3LTBS3LTBS3LTBS2LO3GLOS2LO3GLOS3LTBS3LTBS2LO3GLOS2LO3GLOSSSS3LTB2CF2HqS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS3LTB2CF2HqS3LTBS2LO3GLOS2LO3GLOS3LTBS2LO3GLO3LTBSS3LTBS3LTBFSS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS2HBS3LTBS3LTBS3LTBS2LO3GLO3RSPS2LO3GLOS2LO3GLOS3LTBS3LTB1HS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS2LOS2LO3LTBS2LO3LTBS3LTBS3LTBSS3LTBS2LO3GLOS2LO3GLOS4SP47S4SP47S2LO3GLOS2LO3GLOS2LOS2LO3LTBS2HBS3LTBS4BUFL3LTB2CFS2LO3GLO3LTBS4SP47S4SP47SS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLOS3LTBS2HBFS3LTBS3LTBSS3LTBS3LTBS2LO3LTBS2LO3GLOS2LO3GLOFS3LTBS3CF'2HqS3CF'S3CF'SS2LO3GLO3LTBS3LTBSS3LTB1HS2LO3GLOS2LO3GLOSS2NE1eSS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLOS2LO3GLOS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTB".
rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
unfold file_cells in FC, EFC.
unfold implM, stdout_exit_flush. apply (implM_rdso usegs get_so). rewrite <- ESO.
eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
carve_frame 16%nat ST.
do 4 step.
carve_frame 16%nat ST.
step. step. fix_lit_store. do 5 step.
do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
step.
do 5 step.
release_frame FR0 ST (bv_unsigned sp + -16).
step. step. if_false.
step. step. step. if_true.
step. step. step. if_false.
step. step. if_lit.
step. step.
destruct (0 <? zlength (so_buf so)) eqn:CF.
-
pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
assert (ACT : so_active so = true).
{ destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
rewrite ACT in FC |- *.
step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
do 4 step. step.
rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
replace (Z_to_bv 64 (if so_first so then 95952 else 95544) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
by (rewrite <- ESO; reflexivity).
apply evt_done.
eapply implM_post_evt'.
{ eapply (stdout_writefn_spec get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := guard);
[ rewrite <- ESO; exact ACT
| unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; exact FC
| exact FL64
| rewrite <- ESO; eapply CB_prefix_bytes_at; [exact BUF| rewrite LTB; exact BUFP]
| rewrite <- ESO; exact BUFL
| apply bytes_at_nil; clear; lia
| reflexivity | reflexivity | reflexivity
| rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
| split; [exact GOT | exact GUARD] | exact MI
| clear; lia | unfold zlength; cbn; clear; lia
| rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia
| left; reflexivity ]. }
cbv beta. intros [] st2 ms2 PO2.
destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
rewrite (ret_pc_even 95192) by (cbn; lia).
transport_after_call usegs m1 m2 MU2 WM2.
unfold stdout_cells, file_cells in FC2.
step. step. step. if_lit.
step. step. step. if_lit.
step. step. if_lit.
step. step. step. if_refl.
step. step. step. if_lit.
step. step. step. step.
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold stdio_exit_post.
do 15 eexists. exists (so_after so). eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
split; [reflexivity|].
split.
{ unfold stdout_file. exists flags, mode, tail, bufbytes.
unfold stdout_cells, wfn_of, lbf_of in FC2 |- *. cbn [so_active so_buf so_first so_lbf_nl so_after] in FC2 |- *.
split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
split; [unfold zlength; cbn; clear; lia|]. intros X; discriminate X. }
split; [reflexivity|].
split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. split; [exact GOT2 | exact GUARD2].
-
pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
assert (E0 : so_buf so = []).
{ destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
step. if_refl.
step. step. step. if_lit.
step. step. step. if_lit.
step. step. if_lit.
step. step. step. if_refl.
step. step. step. if_lit.
step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. apply evt_done. unfold stdio_exit_post.
do 15 eexists. exists so. eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [rewrite ESO, set_get; reflexivity|].
split.
{ unfold stdout_file. exists flags, mode, tail, bufbytes. rewrite E0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
split; [exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
split; [clear; lia|]. intros _; reflexivity. }
split; [exact E0|].
split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
split; [exact GOT | exact GUARD].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StdioExit.
Theorem stdio_exit_proof_ps : stdio_exit_spec_stmt ps_so set_so_ps.
Proof.
apply stdio_exit_proof.
- intros s so. reflexivity.
- intros s so so'. reflexivity.
- intros [mm b f so]. reflexivity.
Qed.

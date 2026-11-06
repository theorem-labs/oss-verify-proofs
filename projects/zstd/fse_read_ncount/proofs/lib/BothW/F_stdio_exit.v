(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Prog.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg MonadF AExit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.
End CANSEC1.
Ltac if_refl :=
lazymatch goal with
| |- evtF _ _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
end.
Ltac if_lit :=
lazymatch goal with
| |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac raise_high :=
repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
lazymatch A with Zpos _ => idtac | _ => fail end;
lazymatch eval vm_compute in (0x5c7dc0 <=? A)%Z with true => idtac | false => fail end;
move H at bottom;
lazymatch type of H with ?T => change T with (sf_hide T) in H end
end; sf_unhide.
Ltac hstep := raise_high; step.
Section CANSEC2. Context {rc : runConstT}.
Section StdioExit.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
#[using="get_set set_set set_get"] Theorem stdio_exit_proof : stdio_exit_spec_stmt2 get_so set_so.
Proof.
unfold stdio_exit_spec_stmt2. intros until tm1. intros ST LIBC OFL SIN SINF SOUT SERR SOF SEF GOT GUARD MI -> LO GLO RSTK RIMG RG0 SP47.
unfold GLOBALS_TOP, got_ssp, ssp_guard, RSTDIN, stdin_cells in *.
destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
remember (get_so s) as so eqn:ESO.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x9e0a0); (RSTDOUT_BUF, 0x5f5fe0)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 6) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
- change 64 with (2^6). Local Ltac2 Set LiaHints.tbl := fun () => "01i0?10951812997.11712428134302.11615685060272.10116006764370.10116006764370.99 17776320431.10018894816773.11619006120615.99 20433961190.90 21228674566.96 2172651747.2   21750412114.10121750412114.99 22961942245.0  25076088621.11725301904978.10125301904978.99 25435258127.10125566553219.99 26323796050.10126323796050.99 26494647592.10126494647592.96 26494647592.99 2713962757.117 27428160133.11727730847314.10127730847314.99 31399144472.94 31401241662.11432008302853.11732027975233.0  32600174396.96 33510054780.92 34090419190.98 35012330478.96 35012330478.99 3523399062.5   35369591045.11635369591045.11736936768494.96 36936768494.99 3834455829.95  3836733332.115 38606608901.11739937472148.93 40054548974.96 40054548974.99 40201484047.10440201484047.12440201484047.99 41072247790.96 41072247790.99 42831019478.10142831019478.99 43035628988.3  43061776187.88 43104399792.99 4316683909.117 43987951405.98 45221239098.96 45221239098.99 47785173259.1174866047897.99  49978085870.96 49978085870.99 51056098798.96 51056098798.99 51139856210.10151139856210.99 5180980284.99  51842272261.11652712884706.11653767577774.10353767577774.12353767577775.98 54164510851.10254164510851.12254164510851.96 54269560302.96 54269560302.99 55739122813.96 56170415931.4  57601324989.96 57622410744.11758146277394.91 58809737021.96 59178106163.10159308587280.3  59310859210.1  59310859210.2  59624177333.0  59964306054.96 60679622738.10160679622738.99 61874979822.96 61874979822.99 61892124754.10161892124754.99 62158310226.10162158310226.99 62583080755.99 63135048575.0  63196519557.11663219220728.11763235321900.10163235321900.12163235321901.95 63394812498.10163394812498.99 63779719325.10163792152522.89 63967133241.88 65620170672.11767081926311.96 67324480494.96 67324480494.99 68094715463.93 7618315246.96  7618315246.99  7822655350.98  00000100200:00F00R00Z00f00k01001501;01G01S01T01`01l02802=02B02N02Z02_02d02i03503A03M03Y03^03c03o04004804=04B04N04Z04f05205>05J05V05^05f06206:06F06R06W06\06a06m07907C07M07Q07Y07a07m08508?08I08N08S08_08k09709C09O09[09c09o0:00:80:@0:H0:M0:R0:W0:c0:o0;40;50;:0;G0;O0;\0;a0;i0;n0<30<40<90<E0<Q0<]0<i0=50=A0=M0=Y0=^0=_0=k0>70>?0>G0>O0>[0>g0>l0?20?30?80?=0?I0?U0?Z0?f0@20@7FFS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS4SP47S2LO3GLO3LTBS2LO3GLO3LTBSS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBSS3LTB2HBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3RSPS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4SP473LTBS4SP473LTBS2LOS2LO3LTBS3LTB2HBS2LO3GLO3LTBS2LO3LTBS4SP473LTBS4SP473LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB2HBS2LO3GLO3LTBFS2LO3LTBS2LO3LTBS2LO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBSS3LTBS3LTB2CF2Hq1HS2LO3LTBS4BUFL3LTB2CFS3LTBS3CF'2HqS3CF'S3CF'SS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBSS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2NE1eSS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB".
rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
unfold file_cells in FC, EFC.
unfold stdout_exit_flush. apply (implAM_rdso get_so). rewrite <- ESO.
eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
carve_frame 16%nat ST.
do 4 hstep.
carve_frame 16%nat ST.
hstep. hstep. fix_lit_store. do 5 hstep.
do 3 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
hstep.
do 5 hstep.
release_frame FR0 ST (bv_unsigned sp + -16).
hstep. hstep. if_false.
hstep. hstep. hstep. if_false.
hstep. hstep. if_lit.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. if_false.
hstep. hstep. if_lit.
hstep. hstep.
destruct (0 <? zlength (so_buf so)) eqn:CF.
-
pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
assert (ACT : so_active so = true).
{ destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
rewrite ACT in FC |- *.
hstep. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
do 4 hstep. hstep.
rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
replace (Z_to_bv 64 (if so_first so then 586560 else 583996) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
by (rewrite <- ESO; reflexivity).
apply evtF_done.
eapply implAM_post_evt'.
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
| left; reflexivity
| rewrite ESP; eapply rng_sub'; [exact RSTK | clear - LO RSP; lia] | apply (rng0_use _ _ RG0); clear; lia | exact RIMG
| rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia ]. }
cbv beta. intros [] st2 ms2 PO2.
destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
rewrite (ret_pc_even 585676) by (cbn; lia).
transport_after_call bsegs m1 m2 MU2 WM2.
unfold stdout_cells, file_cells in FC2.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. if_lit.
hstep. hstep. if_lit.
hstep. hstep. hstep. if_refl.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. hstep.
release_frame FR ST2 (bv_unsigned sp).
apply evtF_done. unfold stdio_exit_post.
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
destruct SSP2 as [GOT2 GUARD2]. split; [exact GOT2 | exact GUARD2].
-
pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
assert (E0 : so_buf so = []).
{ destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
hstep. if_refl.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. if_lit.
hstep. hstep. if_lit.
hstep. hstep. hstep. if_refl.
hstep. hstep. hstep. if_lit.
hstep. hstep. hstep. hstep.
release_frame FR ST (bv_unsigned sp).
apply evtF_done. apply implAM_ret. apply evtF_done. unfold stdio_exit_post.
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
End CANSEC2.

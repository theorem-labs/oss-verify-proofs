(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Prog.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg MonadF AExit.
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
repeat match goal with H : rw_cells asegs _ ?A _ |- _ =>
lazymatch A with Zpos _ => idtac | _ => fail end;
lazymatch eval vm_compute in (0x5c6f80 <=? A)%Z with true => idtac | false => fail end;
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
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x9df10); (RSTDOUT_BUF, 0x5f5f20)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 6) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
- change 64 with (2^6). Local Ltac2 Set LiaHints.tbl := fun () => "01m0?12428134302.11613216478589.96 13667934854.96 15685060272.10117416023030.98 17776320431.10019006120615.99 19743703890.10119743703890.99 20433961190.90 20791982469.11721255171901.96 2172651747.2   21750412114.10121750412114.99 22882010094.96 22882010094.99 22961942245.0  25076088621.11725435258127.10125566553219.99 25792298245.11625886974446.96 25886974446.99 26494647592.10126494647592.96 26494647592.99 2752239627.117 28766967813.11629283202992.11731361185874.10131361185874.99 31399144472.94 31401241662.11431521058898.10131521058898.99 32027975233.0  32600174396.96 32716547054.96 32716547054.99 33510054780.92 3523399062.5   36936768494.96 36936768494.99 38238797294.96 38238797294.99 3834455829.95  3836733332.115 38903146501.11739937472148.93 40059657198.96 40059657198.99 40201484047.10440201484047.12440201484047.99 40583097326.96 40583097326.99 42144350469.11742831019478.10142831019478.99 43035628988.3  43061776187.88 43104399792.99 4316683909.117 43744974469.11743987951405.98 45099762158.96 45099762158.99 45221239098.96 45221239098.99 45243835141.11646554080445.96 4866047897.99  50575413842.10150575413842.99 50861135698.10150861135698.99 5180980284.99  52712884706.1165300105810.101 5300105810.99  53767577774.10353767577774.12353767577775.98 54164510851.10254164510851.12254164510851.96 56007886318.96 56007886318.99 56170415931.4  56563479429.11657440577106.10157440577106.99 57622410744.11758146277394.91 59178106163.10159308587280.3  59310859210.1  59310859210.2  59624177333.0  61674577390.96 61674577390.99 62583080755.99 63085006710.98 63135048575.0  63235321900.10163235321900.12163235321901.95 63779719325.10163792152522.89 63967133241.88 64311140434.10164311140434.99 64513056262.96 66017866578.10166017866578.99 66267610360.11766747928658.10166747928658.99 67081926311.96 67943285742.96 67943285742.99 68037941509.11768094715463.93 9317519877.117 00000100600;00C00H00P00U00a00m01201>01K01Q01]01i02502A02B02N02S02X02d03003<03A03F03K03P03\03a03m04904>04C04O04[04\04d05005<05A05M05Y05e06106=06E06M06Y06a06m07907>07C07H07T07`07l08608@08D08L08T08U08a08i09509A09K09U09a09f09k0:70:C0:O0:[0:c0:d0;00;<0;D0;L0;T0;Y0;^0;c0;o0<;0<<0<H0<T0<`0<m0=50=:0=B0=G0=L0=M0=Y0=e0=j0=o0>00>80>@0>H0>M0>S0>T0>`0>l0?10?=0?I0?U0?a0?m0@20@>0@J0@V0@[0@gFS3LTBS3LTBS3LTB2HBS3LTBS2LO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS4BUFL3LTB2CFS4SP47S2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBSS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBSS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3RSPS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4SP473LTBS4SP473LTBS2LOS2LO3LTBS3LTB2HBFS2LO3GLO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4SP473LTBS4SP473LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB2HBFS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3LTBS2LO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBSS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB2CF2Hq1HS2LO3LTBS3LTBS3CF'2HqS3CF'S3CF'SS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBSS2LO3LTBS2LO3LTBS2LO3LTBS3LTBS2NE1eSS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTB".
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
replace (Z_to_bv 64 (if so_first so then 586160 else 583596) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
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
rewrite (ret_pc_even 585276) by (cbn; lia).
transport_after_call asegs m1 m2 MU2 WM2.
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

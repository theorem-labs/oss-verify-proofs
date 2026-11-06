(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
RefNodes HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvA.FPX_1.DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A0"; "1list"; "1nil"; "1prod"; "2and"; "2eq"; "3Z"; "0HI"; "0KA"; "0KF"; "0LK0"; "4Fs"; "5mkCfg"; "6FdEntry"; "6Model"; "6event"]; ["6m_fds"; "6m_fs"; "7openat_errnos"; "8ALU_ADD"; "9bvmap"; ":alu64"; "0M0"; "0R"; ";mrestrict"; "<ahid"; "=ENVA"; "=fds0"; "=file_kA"; "=open_err_kA"; ">kn_mainA"; ">sr_mainA"]; [">vals_mainA"; "?dinv"; "@mkst"; "@seg_rom"; "ATSet"; "At_alt2"; "Bsrealizes"; "Cknow_ok"; "Cregs_ok"; "Dloaded_segments"; "EIn"; "Fadd"; "Fle"; "0ar"; "0can"; "0cr0"]; ["0e"; "0fs0"; "0fx"; "0k"; "0model"; "0p0"; "0p1"; "0scfg"; "0sp0"; "GZ_to_bv"; "Gbv"; "Gbv_unsigned"; "0tid"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac drv_block_post HIok Hsp DL DI P0 bls Hbl HZ :=
match goal with
| EQM : mrestrict _ ?M' = mem_denot _ _ ?log, EQH : (forall a, _ = true -> ?M' a = _),
HZn : lzinv _ _ _ ?model', SBM : same_but_materialized _ ?model' |- _ =>
let D := fresh "DI" in
pose proof (dinv_block _ _ _ _ _ _ HIok _ Hsp DL _ _ _ bls _ _ _ _ _ _ _ _ log P0 DI Hbl ltac:(vm_compute; reflexivity) EQM EQH HZn SBM) as D;
clear HZ HZn;
match goal with HKn : know_ok _ _ (mrestrict (ahid ?A ?model) M') _ |- _ => rewrite <- (ahid_sbm A model model' SBM) in HKn end
end.
Ltac drv_block_post0 HIok Hsp DL DI P0 HZ :=
match goal with
| EQM : mrestrict _ ?M' = mem_denot _ _ ?log, EQH : (forall a, _ = true -> ?M' a = _),
HZn : lzinv _ _ _ ?model', SBM : same_but_materialized _ ?model' |- _ =>
let D := fresh "DI" in
pose proof (dinv_block _ _ _ _ _ _ HIok _ Hsp DL _ _ _ (@nil (nat * Z)) _ _ _ _ _ _ _ _ log P0 DI (no_bls _) ltac:(vm_compute; reflexivity) EQM EQH HZn SBM) as D;
clear HZ HZn;
match goal with HKn : know_ok _ _ (mrestrict (ahid ?A ?model) M') _ |- _ => rewrite <- (ahid_sbm A model model' SBM) in HKn end
end.
Ltac drv_block HIok Hsp DL HR HK DI P0 bls Hbl scr NX :=
let HZ := fresh "HZ" in
pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
run_block_lz_with HR HK HZ asegs_wx FUELA STOPSA scr NX true;
[ .. | drv_block_post HIok Hsp DL DI P0 bls Hbl HZ ].
Ltac drv_block0 HIok Hsp DL HR HK DI P0 scr NX :=
let HZ := fresh "HZ" in
pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
run_block_lz_with HR HK HZ asegs_wx FUELA STOPSA scr NX true;
[ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].
Lemma openat_errnos_rangeA : ltac2:(TCodec.tc2 tcn__Ja0DrvA "?'6&Q:r1&B%33421'4&Q<+1r2%3221+SoO%5231%7231p091pS2>1").
Proof.
intros e He. unfold openat_errnos in He. cbn in He.
unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvA.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variables a0s path : list byte.
Variable fs0 : Fs.Fs.
Variable fdata : list byte.
Variables p0 p1 can : word.
Variable M0 : word -> option byte.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hpne : path <> [].
Hypothesis Hppl : openat_plain_name path = true.
Hypothesis Hfs : sc_fs scfg = true.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) path.
Hypothesis P1lo : bv_unsigned sp0 <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 <= 2 ^ 47.
Hypothesis P1str : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
Variable LK0 : list fframe.
Variable cr0 : credit.
Variable A0 : list (Z * Z).
Hypothesis Hcr0 : acredit_ok L cr0 65536.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
Definition ENVA (vals : list word) : env := Env (vals_ev vals) (blobs_ev [[]; []; []; []; fdata]).
Definition fds0 : list (word * FdEntry) :=
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Definition fds1 : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)).
Definition open_err_kA (KA : TSet) : Prop :=
forall e vals R M (model : Model),
1 <= e <= 4095 ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 -> vals_ev vals 38 = errno_ret e ->
regs_ok (ENVA vals) (sr_upd srA (ridx 10) (EVar 38)) R ->
know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model) M) knA ->
dinvA [] LK0 cr0 A0 M model -> m_fds model = fds0 -> m_fs model = fs0 ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x125988) M (seg_rom ASEGS)) model) KA.
Definition file_kA (KF : TSet) : Prop :=
forall vals R M (model : Model) A (A1 : Z),
length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = p0 -> vals_ev vals 2 = p1 -> vals_ev vals 3 = can ->
vals_ev vals 48 = Z_to_bv 64 A1 ->
regs_ok (ENVA vals) srC0 R -> know_ok ASEGS (ENVA vals) (mrestrict (ahid A model) M) knC0 ->
dinvA [(A1, 65536)] LK0 (adebit L cr0 65536) A M model -> incl A0 A ->
m_fds model = fds1 -> m_fs model = fs0 ->
ablock_range L ar A1 65536 ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7200) M (seg_rom ASEGS)) model) KF.
Lemma alu_add_w_litA : ltac2:(TCodec.tc2 tcn__Ja0DrvA "D'QJyR0%211'6'5&E(Cr2&QIr1%2291%63541&Q;&QK%12=7%3216%82?1%=3?61pS8?1pSNA1").
Proof.
intros x k. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_drv_openA := (ltac2:(TCodec.tc2 tcn__Ja0DrvA "S7&Q4&Dy5'QJyR0%211%5241'>'1%114&Q0vQHvQEvQFvQ>r1r3%76654321&Q8&J%115&Or4%53321&Q7&Q9r2%811&H&Iv0%2219vF%5221&N%;4:821'Q1vQ=v7(2'3'6%2211%411v:vQ?r5%;::9Q4?432A?1'5'=%:2Q=1%Q;11&@r6%211&K%83521&;&Ar7%211vQA%>3521&Mr;%211&L%113r<'?%O11%311'Q6vQG(<&Q2vQB&QI+dl]<%22R;1&Q3%11QH%756>3QB1%921C&Q5r>r=%3221%@4QO?51p0B1p0G1p0J1p0N1p0Q51p0Q?1p0QL1p0R91tSLRHR@1pSJRM1pS:RL1pQ@RN1pDS51pBS61")) (only parsing).
Variable KA : ltac:(sec_ty2 constr:(SEC_T_drv_openA) 0%nat 0%nat).
Variable KF : ltac:(sec_ty2 constr:(SEC_T_drv_openA) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_drv_openA) 2%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_drv_openA) 3%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_drv_openA) 4%nat 0%nat).
Theorem drv_openA : ltac:(sec_stmt2 constr:(SEC_T_drv_openA) 5%nat 0%nat).
Proof.
intros vals HR HK DI Hfds Hfs0 HKA HKF HKF0.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainA; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0) by reflexivity.
assert (P2 : vals_ev vals 2 = p1) by reflexivity.
assert (P3 : vals_ev vals 3 = can) by reflexivity.
clearbody vals.
drv_block0 HIok Hsp DL HR HK DI P0 scr0 38%nat.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
clear EQM EQH SBM HR HK DI Hfds Hfs0. clear model.
assert (Sr' : rdn ASEGS M p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite <- P1str. apply rdn_agree. intros j Hj. apply (di_above _ _ _ _ _ _ _ _ _ _ DI0). lia. }
eapply (rz_openat_file_lz ASEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- exact (di_halt _ _ _ _ _ _ _ _ _ _ DI0).
- regv HR0 (17%bv : reg). reflexivity.
- regv HR0 (10%bv : reg). apply bv_eq. reflexivity.
- regv HR0 (12%bv : reg). vm_compute. reflexivity.
- exact Hfs.
- regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2.
apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ DI0)); [lia|].
intros k Hk. right. left. lia.
- rewrite F1. reflexivity.
- split; [exact Hplen|]. split; [exact Hnonul|].
regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2. exact Sr'.
- exact Hpne.
- exact Hppl.
- rewrite F2. exact Hfile.
-
intros e He. rewrite v_addi_pc4 by lia. change (0x125984 + 4)%Z with 0x125988%Z.
lazymatch type of HR0 with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR0) as HR2 end.
lazymatch type of HK0 with know_ok _ _ ?Mc ?kn =>
pose proof (env_app_know ASEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK0) as HK2 end.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev [[]; []; []; []; fdata])) with (ENVA (vals ++ [errno_ret e])) in HR2, HK2.
eapply (HKA e (vals ++ [errno_ret e])).
+ apply openat_errnos_rangeA. exact He.
+ rewrite length_app, HL. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
+ rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVA].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ exact HK2.
+ exact DI0.
+ exact F1.
+ exact F2.
-
rewrite v_addi_pc4 by lia. change (0x125984 + 4)%Z with 0x125988%Z.
rewrite F1. change (alloc_fd fds0) with (Z_to_bv 64 3).
set (model1 := with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0).
assert (DI1 : dinvA [] LK0 cr0 A0 M model1).
{ apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model0 model1 DI0); [apply with_fds_vm|].
unfold model1. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DI0). }
assert (HK1 : know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model1) M) knA) by exact HK0.
assert (G1 : m_fds model1 = fds1) by (unfold model1; apply with_fds_fds).
assert (G2 : m_fs model1 = fs0) by (unfold model1; rewrite with_fds_fs; exact F2).
pose proof (regs_set_a0 (ENVA vals) _ _ (Z_to_bv 64 3) (ELit 3) HR0 eq_refl) as HR1.
clearbody model1. clear HR0 HK0 DI0 F1 F2. clear model0.
drv_block0 HIok Hsp DL HR1 HK1 DI1 P0 scr0 38%nat.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
clear EQM EQH SBM HR1 HK1 DI1 G1 G2 Sr'. clear model1.
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ kn _ _ model [] LK0 cr0 A0 65536 (-128) [] [] 0xa7200 KF) end;
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity
| rewrite HL; vm_compute; reflexivity
| rewrite HL; lia
| exact P0
| vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
| lia
| reflexivity
| regv HR (10%bv : reg); reflexivity
| lia
| exact Hcr0
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| exact HKF0
| ].
intros R' M' model' A' u vals' E' HL' HA' HR' HK' DI' HRT HINC HBR HAP HSHB HAB HBLK HIMG. subst vals' E'.
destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
apply (HKF (vals ++ junk_vals R') R' M' model' A' u); try assumption.
* rewrite HL', HL. reflexivity.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P3.
* rewrite <- HA'. rewrite HL. reflexivity.
* rewrite HL in HR'. exact HR'.
* rewrite HL in HK'. exact HK'.
Qed.
End SE.
End DrvA.
End FPX_1.

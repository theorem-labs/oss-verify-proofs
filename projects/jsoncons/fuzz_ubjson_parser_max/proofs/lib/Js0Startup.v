(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout Js0Img Js0StartupDefs Js0Startup1 Js0Memset Js0Startup2 Js0Startup3 Js0Startup4.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Startup () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Startup.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0K"; "4Fs"; "5Segment"]; ["6machine_state"; "6store_ok"; "7SpuriousCfg"; "7init_config"; "7mkCfg"; "7segments_reserved"; "7valid_argv"; "7valid_brk"; "7valid_envp"; "7valid_sp"; "8EntryDraw"; "8ed_random"; "9InputStream"; "9Model"; "9NetQueue"; "9ProcInput"]; ["9VaSize"; "9in_argv"; "9in_envp"; "9in_hwcap"; "9in_uid"; "9init_model"; "9m_halted"; "9m_vm_lazy"; "9mkProcInput_full"; "9stack_max_size"; "9with_tid"; ":bvmap"; ";main_entry"; "<D_main"; "=fx0"; "=mkst"]; ["=rdn"; "=seg_rom"; "=wrap_mem"; ">TSet"; "?srealizes"; "@bwd"; "Ainit_pc"; "Aloaded_segments"; "Aphdrs"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bof_nat"; "Bpow"; "Bsub"]; ["0a"; "0abt"; "0argv"; "0av"; "0brk"; "0envp"; "0ev"; "0fs0"; "0gid"; "0groups"; "0hw"; "0inp"; "0lim"; "0mbase"; "0mem"; "0model"]; ["0n"; "0net"; "0nofile"; "0rdraw"; "0regs"; "0scfg"; "0segs"; "0sigmask"; "0sp"; "0sp0"; "0st"; "0stdin0"; "CBV"; "Cbv"; "Cbv_unsigned"; "0tid"]; ["0tmp0"; "0uid"; "0urnd"; "0va"]]).
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. #[local] Existing Instance PropExec.fx0.
Lemma bwd_rz : ltac2:(TCodec.tc2 tcn__Js0Startup "Q>'2'?%211'B'M&QC':'5'RMyR0%211%411&Q6r2%211(0%116%;3631'6%1299%D11&Q7r3%211(4%116%D3631&QEr6'@'QDr7(Dr1r5%3221r4%746921qUF91%<2;1p0>1p0H1pLQ51pU0Q71pU<Q91pU>Q;1").
Proof.
intros segs scfg model K Hh Hlazy st st' Hms Hst'. eapply srz_msteps; eassumption.
Qed.
Definition J_main (sp0 : word) (av ev : list (list byte)) (uid hw : word) (s1v : word) : word -> option byte :=
let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
(Z_to_bv 64 0x98278) (pn_w sp0 av ev) s1v (Z_to_bv 64 0xe7ef0)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
(Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x98280)))
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x98474)))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))
(Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))
(Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x983c4)))
(Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xaf1d0)).
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
(regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
me_ra : getr regs 1 = Z_to_bv 64 0x98484;
me_sp : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
me_gp : getr regs 3 = Z_to_bv 64 0x10800;
me_tp : getr regs 4 = Z_to_bv 64 0xc7c60;
me_s0 : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
me_s1 : getr regs 9 = argcN av;
me_a0 : getr regs 10 = argcN av;
me_a1 : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
me_a2 : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
me_s2 : getr regs 18 = Z_to_bv 64 0x33bac;
me_s3 : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
me_mem : exists (J : word -> option byte) (s1v : word),
wfJ sp0 J /\ J = J_main sp0 av ev uid hw s1v
/\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main sp0 av ev hw (ed_random rdraw) tid)
}.
Section Assembly.
Variable scfg : SpuriousCfg.
Variable sp : word.
Variables argv envp : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hvsp : valid_sp sp.
Lemma Hlo : ltac2:(TCodec.tc2 tcn__Js0Startup "7&QJ+SoonPPPPP0&RNyR0vRH%3221%6251").
Proof. destruct Hvsp as [H _]. exact H. Qed.
Lemma Hhi : ltac2:(TCodec.tc2 tcn__Js0Startup "7&QJ&RNyR0vRH%3221+TPPPPPPPP0%6221").
Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
Lemma Hal : ltac2:(TCodec.tc2 tcn__Js0Startup ";':'<&QL&RNyR0vRH%3221+@%6221z%:3921").
Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.
Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).
Ltac side Hva Hve HG :=
first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
| apply wfJ_const
| lazymatch goal with |- getr _ _ = _ =>
gres; first [ assumption | reflexivity | bveq
| match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
first [reflexivity | f_equal; lia | bveq] end ] end
| idtac ].
Section SE.
Local Abbreviation SEC_T_ref_startup_sec := (ltac2:(TCodec.tc2 tcn__Js0Startup "S>'RMyR0%211'<&>'L'2%115'N'1'Q0&QC&Q;y5%221<'5y8%A11%311p0A1'9&QKz&RNr3%22H1%5241&QN+2+F%3221%:261%<261'Q<vRHvR2vR5vS1vR:vRCr4r2%998765432B1'QD&QGvRE(D&Q?&Q>(RL+V^m<(8%33QC21/01QC&QA%11;%958@3Q01&Q:r5&Q5&E%11ArDrCrB(Q8rAr@r?r>r=r<r;r:r9r8r7%<?Q:Q9;:Q898765Q74321%C6A@?Q<>1%F2E1%Q22H1r6%Q74Q6Q521p0Q91p0QD1pTNR21pU:R81pV0RE1&C&QF&QH%J?QHQGEDQFCBA@?QE:Q1QCR3%49Q@32QJIHQEG1%QB4QAQ@1QDp071pLRD1pV2RL1pV6RL1pV8RH1pT4RJ1pU@S21pU6S31pU4RN1pTDS01pTBS61pUHS41pT@S61pTJS81pTLS:1pT:S;1")) (only parsing).
Variable brk : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 0%nat 0%nat).
Variable mbase : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 1%nat 0%nat).
Variable lim : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 2%nat 0%nat).
Variable fs0 : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 3%nat 0%nat).
Variable stdin0 : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 4%nat 0%nat).
Variable gid : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 5%nat 0%nat).
Variable groups : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 6%nat 0%nat).
Variable net : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 7%nat 0%nat).
Variable nofile : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 8%nat 0%nat).
Variable sigmask : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 9%nat 0%nat).
Variable abt : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 10%nat 0%nat).
Variable va : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 11%nat 0%nat).
Variable urnd : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 12%nat 0%nat).
Variable tmp0 : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 13%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_ref_startup_sec) 14%nat 0%nat).
Theorem ref_startup_sec : ltac:(sec_stmt2 constr:(SEC_T_ref_startup_sec) 15%nat 0%nat).
Proof.
intros HK.
pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
pose proof (u64_range sp) as Hsp.
unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp in_uid in_hwcap].
set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0)).
assert (Hh : m_halted model = None) by reflexivity.
assert (Hlazy : m_vm_lazy model = []) by reflexivity.
assert (Ht0 : m_tid model = None) by reflexivity.
set (RZ := fun st : machine_state => srealizes rsegs scfg (mkCfg st model) K).
assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
rewrite init_mkst.
replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x33a60 : word) by (apply bv_eq; reflexivity).
rewrite cmem_init. fold (regs_init sp).
destruct (p1_run sp argv envp uid hw rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
eapply srz_msteps; [exact Hh | exact Hlazy | exact R1 |].
assert (A1' : getr regs1 1 = (0x98194 : word)) by (rewrite A1; apply bv_eq; reflexivity).
destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
(seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x98194 : word) A1')
as [regs2 [mem2 (R2 & M2 & G2)]].
{ unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ exact A10. } { exact A11. } { exact A12. }
{ rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
{ rewrite u_Z2bv by lia. lia. }
{ apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
rewrite wbytes_cmem_win by region_side.
carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
carry G2 A3 (3:reg) B3.
change (srealizes SEGS scfg (mkCfg ?st model) K) with (RZ st).
eapply (p3_run sp argv envp uid hw rdraw) with (G := RZ); try side Hva Hve HG.
{ unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
intros regs3 C1 C2 C10 C18 G3.
carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
{ intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
pose proof (Cz 27 ltac:(in_list)) as Z27.
change (J1 sp argv J0) with (J_lsm sp argv J0).
eapply (tls_c1 sp J0 argv envp uid hw rdraw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4a; intros.
eapply (tls_c2 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4b; intros.
eapply (tls_c3 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4c; intros.
eapply (tls_c4 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4; intros.
unfold RZ at 1.
eapply (rz_set_tid SEGS scfg regs4 (0x986e4 : word) _ (seg_rom SEGS) model K (ltac:(oW' 0x986e4%Z)) (ltac:(oF' 0x986e4%Z)) (ltac:(oE' 0x986e4%Z)));
[exact Hh | exact Hlazy | assumption | exact Ht0 |].
intros tid Htid.
replace (v_addi (0x986e4 : word) 4) with (0x986e8 : word) by (apply bv_eq; reflexivity).
set (model' := with_tid tid model).
assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
set (RZ' := fun st : machine_state => srealizes rsegs scfg (mkCfg st model') K).
assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
change (srealizes SEGS scfg (mkCfg ?st model') K) with (RZ' st).
eapply (tls_c5 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
intros regs5; intros.
eapply (fin_c6 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
intros regs6; intros.
eapply (fin_c7 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
intros regs7; intros.
eapply (fin_c8 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
intros regs8; intros.
eapply (fin_c9 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
unfold RZ'. apply (HK tid regs9). { exact Htid. }
split; try assumption.
- intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
- eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
+ unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
+ unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
Qed.
End SE.
End Assembly.
Theorem ref_startup : ltac2:(TCodec.tc2 tcn__Js0Startup "S<'B'RMyR0%211'J'<'O&QC&Ir7%211&G&QG%2214&F&Q1r4%211%411&H&Q2r5%211%411&Q;y5%221G'5y8%L11%311p0L1'9&QKz&RNr3%22Q31%5241&QN+2+F%3221%:261%<261'Q<r?r:%Q111%M12&Q4%114&Q3%116r<r2%;9:87532Q8D1'QDrA(D&Q?&Q>(RL+V^m<(8%33QO21/01QO&QA%11QH%958QE3Q11&Q:&Q5&E%11QMr>r@r;%664O32G1%82QI1%D2:1%G4R4F1Q1p0I1p0Q61pTNQD1pU:QJ1pV0RB1r=&C&QF&QHr9r8%59R@43Q6@Q=21RCr6%Q54RB821p0:1p0R91p0R?1p0RE1p0RI1pLRM1pTHRO1pTJS11pU8S31pTLS51pT:S61pUBS71pU<S;1").
Proof.
intros scfg sp brk mbase rdraw lim [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0] K Hsp Hbrk Hva Hve HK.
cbn [in_argv in_envp in_uid in_hwcap] in *.
exact (ref_startup_sec scfg sp argv envp uid hw rdraw Hva Hve Hsp brk mbase lim fs0 stdin0 gid groups net nofile sigmask abt va urnd tmp0 K HK).
Qed.
Section Consumers.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Lemma main_entry_rdn_above : ltac2:(TCodec.tc2 tcn__Js0Startup "QC'2'?%211'RMyR0%211'3&QJ&RNvRI%2261r2%4281%6231&QIr3%82<1&QM%117%5231&QN+2+R0%3221%A251':'5y8%I11%M11%411&Q@r5vR>r4%44321D&QB&QHvR3vR6vS1vR:vRC%776Q254321%=4<1:M%D3?:1p0F1p0Q21pU2Q:1pT2Q<1pU>Q@1").
Proof.
intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_above; assumption.
Qed.
Lemma main_entry_mem_above : ltac2:(TCodec.tc2 tcn__Js0Startup "M'RMyR0%211&QJ&RNvRI%2251r1%4271%6231':'5y8%=11%311vR>r2%211&QB&QHvR3vR6vS1vR:vRC%786D543219%@3<91p0B1pT2J1").
Proof.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_above. exact Ha.
Qed.
Lemma main_entry_win_mapped : ltac2:(TCodec.tc2 tcn__Js0Startup "Q0'RMyR0%211'9&QJ&QO&RNvRI%2271&Q9%5221r1%62;1%9231&QK%1237%=231&;':'5y8%E11%311vR>r2%211(0%116%:3631%<11p0>1pT2M1").
Proof.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
Qed.
Lemma main_entry_store_ok_win : ltac2:(TCodec.tc2 tcn__Js0Startup "Q6'2'?%211'RMyR0%211'3&QJ&QO&RNvRI%2271&Q9%5221r2%62;1%9231&QIr3%:2?1&QM%117%5231%@21<':'1&Ar5vR>r4%44321<(7%83721p0:1p0B1pU2M1pT2O1pU>Q31").
Proof.
intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
Qed.
Lemma main_entry_mem_data : ltac2:(TCodec.tc2 tcn__Js0Startup "Q1'RMyR0%211&QK&RNr1%2251&QOvRI%5281&Q9%4221%9261':'5y8%@11%311vR>r2%211&Q=vR3vR6vR:&KvRC%211vRO%87E76521:%A3=:1p0C1pT2N1").
Proof.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_data. unfold win_lo. exact Ha.
Qed.
Lemma main_entry_rdn_data : ltac2:(TCodec.tc2 tcn__Js0Startup "Q@'2'?%211'RMyR0%211'3&QJ&QI&RNr2%2271&QMr1%211%7241&QOvRI%92>1&Q9%4221%>261':'5y8%F11%J11%411&Q@r4vR>r3%44321F&Q=vR3vR6vR:&KvRC%211vRO%86H76521%>4=1;Q0%E3@;1p0G1pU2Q71pT2Q91pU>Q=1").
Proof.
intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_data. unfold win_lo. exact Ha.
Qed.
End Consumers.
End FPX_1.

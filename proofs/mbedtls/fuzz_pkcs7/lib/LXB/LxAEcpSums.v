(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts A_mpi_core_mla A_mpi_core_add A_mpi_core_mul A_amemmove_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface Arr CellsX MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum LxSoundSum LxDenot LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_LxAEcpSums () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "Corelib.Init.Datatypes.true"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MAobj"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FCr"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okO"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "SUM_amemsetWinA"; "LXE_AMEMCPY"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.B.A_amemmove_stmt.A_ASAN_MEMMOVE"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_add.A_MPI_CORE_ADD"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRo"; "LXE_GOT"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "LXE_GSB"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_add.MPI_CORE_ADD_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcpy_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemmove"; "SUM_amemcpyWinA"; "RocqVerifyHarness.AgentSubmission.B.A_amemmove_stmt.amemmove_stmtA"; "SUM_amemmoveWinA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mul.A_MPI_CORE_MUL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mul.MPI_CORE_MUL_STACK_A"; "SUM_coremulA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.A_MPI_CORE_MLA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.MPI_CORE_MLA_STACK_A"; "SUM_mlaWin1A"; "SUM_coreaddWin1A"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).

(* [comment removed for export] *)
Definition LXE_AMEMCPY : Z := 0x67dbc.
Definition LXE_GOT : Z := 0x0f5e50.
Definition LXE_GSB : Z := 0x1099f8.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38557627424.3000009S1z2H12H2". (* [comment removed for export] *)
Lemma lxe_uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, two64 in *. cbn in *. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxe_pows :=
  try change (2 ^ Z.of_N 1)%Z with 2%Z in *; try change (2 ^ Z.of_N 2)%Z with 4%Z in *;
  try change (2 ^ Z.of_N 3)%Z with 8%Z in *; try change (2 ^ Z.of_N 4)%Z with 16%Z in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L32766075502.8L36743337827.8L60414246488.800000;00F00QS2ws1i1k2LES2ws1i1k2LES2ws1i1k2LE". (* [comment removed for export] *)
Lemma lxe_arr_win_u8 : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "Psegs,(0.$1.)Pmq,P,(2.&40.)(3.(2.&8.))Pa,$4.Pws,(0.(2.&40.))Pi,$5.Pk,$5.P,(6.R6.R5.R4.R3.)P,(7.(8.R3.R2.)(9.(2.&40.)R4.))(:.(;.R8.R7.(<.R6.(=.+4.(>.R4.)))(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.))))(12.$4.(>.(9.(2.&8.)(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.)))))(=.+4.(>.R3.))))")
(* [comment removed for export] *).
Proof.
  intros segs mq a ws i k H LE.
  rewrite <- (firstn_skipn i ws) in H. apply u32arr_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn k (skipn i ws)) in H. apply u32arr_app in H. destruct H as [H _].
  split; [apply MpiWalkAux.u8arr_of_u32arr; exact H|].
  rewrite u32s_length, firstn_length_le by (rewrite length_skipn; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma lxe_arr_win_ro : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "Psegs,(0.$1.)Pmq,P,(2.&40.)(3.(2.&8.))Pa,$4.Pws,(0.(2.&40.))Pi,$5.Pk,$5.P,(6.R6.R5.R4.R3.)P,(7.(8.R3.R2.)(9.(2.&40.)R4.))(:.(13.R8.R7.(<.R6.(=.+4.(>.R4.)))(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.))))(12.$4.(>.(9.(2.&8.)(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.)))))(=.+4.(>.R3.))))")
(* [comment removed for export] *).
Proof.
  intros segs mq a ws i k H LE. destruct (lxe_arr_win_u8 segs mq a ws i k H LE) as [U L]. split; [exact (proj1 U) | exact L].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L32766075502.8L36743337827.8L60414246488.8L66882424594.800000;00F00Q00^S2ws1i1k2LES2ws1i1k2LES2ws1i1k2LES1a2ws1i1k2LE". (* [comment removed for export] *)
Lemma lxe_ro_win_ro : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "Psegs,(0.$1.)Pmq,P,(2.&40.)(3.(2.&8.))Pa,$4.Pws,(0.(2.&40.))Pi,$5.Pk,$5.P,(13.R6.R5.R4.(?.R3.))P,(7.(8.R3.R2.)(9.(2.&40.)R4.))(:.(13.R8.R7.(<.R6.(=.+4.(>.R4.)))(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.))))(12.$4.(>.(9.(2.&8.)(?.(10.(2.&40.)R3.(11.(2.&40.)R4.R5.)))))(=.+4.(>.R3.))))")
(* [comment removed for export] *).
Proof.
  intros segs mq a ws i k H LE.
  rewrite <- (firstn_skipn i ws) in H. rewrite u32s_app in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite u32s_length, firstn_length_le in H by lia. replace (a + Z.of_nat (4 * i)) with (a + 4 * Z.of_nat i) in H by lia.
  rewrite <- (firstn_skipn k (skipn i ws)) in H. rewrite u32s_app in H. apply bytes_at_app in H. destruct H as [H _].
  split; [exact H|]. rewrite u32s_length, firstn_length_le by (rewrite length_skipn; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L15053324435.27L15937462552.24L1887002239.30 L36743402216.22L54042079150.27L55298753081.26L60414231660.2300000P00e01K01b02T03F03XS2ws1i1k1n3bs'2LE2EN2HL2L12L22L3S2ws1i1k3bs'2LE2L12L2S2ws1i1k1n3bs'2LE2EN2HL2L12L22L32wm2LMS2ws1i1k1n3bs'2LE2EN2HLS1a2ws1i1k1D1n3lo'3hi'3bs'2LE2ED2EN2AP2HL2L12L22L3S1a2ws1i1k1D1n3lo'3hi'3bs'2LE2ED2EN2AP2HL2L12L22L3S2ws1i1k3bs'2LE2L1". (* [comment removed for export] *)
Lemma lxe_arr_upd_win : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "Psegs,(0.$1.)Pmq,P,(2.&40.)(3.(2.&8.))Pmq',P,(2.&40.)(3.(2.&8.))Pa,$4.Pws,(0.(2.&40.))Pi,$5.Pk,$5.PD,$4.Pn,$4.Plo',$4.Phi',$4.Pbs',(0.(2.&8.))P,(6.R<.R;.R9.R8.)P,(7.(8.R8.R7.)(9.(2.&40.)R9.))P,(12.$4.R7.(<.R;.(=.+4.(>.R9.))))P,(12.$4.R7.(=.+4.(>.R9.)))P,(14.(15.(16.$4.$4.)(17.$4.$4.R9.(<.R9.R8.))(15.(16.$4.$4.)(17.$4.$4.R7.R6.)(18.(16.$4.$4.))))R?.R>.)P,(19.R11.R10.R?.)P,(1:.(1;.(<.R?.(=.+4.(>.(9.(2.&40.)R>.))))R9.)(1;.R8.R?.))P,(;.R13.R11.R<.R8.)P,(12.$4.(>.(9.(2.&8.)R9.))R<.)(1<.(0.(2.&40.))Lws',(0.(2.&40.))(:.(6.R16.R14.R13.R1.)(12.$5.(9.(2.&40.)R1.)(9.(2.&40.)R12.))))")
(* [comment removed for export] *).
Proof.
  intros segs mq mq' a ws i k D n lo' hi' bs' H LE ED EN MU WM AP HU HL.
  rewrite <- (firstn_skipn i ws) in H. apply u32arr_app in H. destruct H as [H1 H].
  assert (L1 : length (firstn i ws) = i) by (apply firstn_length_le; lia).
  rewrite L1 in H.
  rewrite <- (firstn_skipn k (skipn i ws)) in H. apply u32arr_app in H. destruct H as [_ H3].
  assert (L2 : length (firstn k (skipn i ws)) = k) by (apply firstn_length_le; rewrite length_skipn; lia).
  rewrite L2 in H3.
  assert (L3 : length (skipn k (skipn i ws)) = (length ws - i - k)%nat) by (rewrite !length_skipn; lia).
  pose proof (u32arr_transport segs _ _ _ _ _ H1 MU WM) as T1. rewrite L1 in T1.
  specialize (T1 ltac:(cbn [disjoint_from]; lia)).
  pose proof (u32arr_transport segs _ _ _ _ _ H3 MU WM) as T3. rewrite L3 in T3.
  specialize (T3 ltac:(cbn [disjoint_from]; lia)).
  destruct (MpiWalkAux.u32arr_of_u8arr segs mq' D bs' k HU ltac:(lia)) as (wm & UM & LM).
  exists (firstn i ws ++ wm ++ skipn k (skipn i ws)). split.
  - apply u32arr_app. split; [exact T1|]. rewrite L1. apply u32arr_app. split; [rewrite <- ED; exact UM|]. rewrite LM. exact T3.
  - rewrite !length_app, L1, LM, L3. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L48712026502.2100000GS2ws1i1k1n3ds'2LE2EN2HL". (* [comment removed for export] *)
Lemma lxe_arr_upd_win32 : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "Psegs,(0.$1.)Pmq,P,(2.&40.)(3.(2.&8.))Pmq',P,(2.&40.)(3.(2.&8.))Pa,$4.Pws,(0.(2.&40.))Pi,$5.Pk,$5.PD,$4.Pn,$4.Plo',$4.Phi',$4.Pds',(0.(2.&40.))P,(6.R<.R;.R9.R8.)P,(7.(8.R8.R7.)(9.(2.&40.)R9.))P,(12.$4.R7.(<.R;.(=.+4.(>.R9.))))P,(12.$4.R7.(=.+4.(>.R9.)))P,(14.(15.(16.$4.$4.)(17.$4.$4.R9.(<.R9.R8.))(15.(16.$4.$4.)(17.$4.$4.R7.R6.)(18.(16.$4.$4.))))R?.R>.)P,(19.R11.R10.R?.)P,(1:.(1;.(<.R?.(=.+4.(>.(9.(2.&40.)R>.))))R9.)(1;.R8.R?.))P,(6.R13.R11.R<.R8.)P,(12.$5.(9.(2.&40.)R9.)R>.)(1<.(0.(2.&40.))Lws',(0.(2.&40.))(:.(6.R16.R14.R13.R1.)(12.$5.(9.(2.&40.)R1.)(9.(2.&40.)R12.))))")
(* [comment removed for export] *).
Proof.
  intros segs mq mq' a ws i k D n lo' hi' ds' H LE ED EN MU WM AP HU HL.
  eapply (lxe_arr_upd_win segs mq mq' a ws i k D n lo' hi' (u32s ds')); try eassumption.
  - apply MpiWalkAux.u8arr_of_u32arr. exact HU.
  - rewrite u32s_length. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17449162868.1300000DS1A1n1a1k2H12H21x2Hx". (* [comment removed for export] *)
Lemma lxe_cw_sub : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "PL,$1=.PLBs,(0.$1>.)Plo,$4.Ptop,$4.PA,$4.Pn,$4.Pa,$4.Pk,$4.P,(1?.R8.R7.R6.R5.R4.R3.)P,(1;.R5.R3.)P,(1;.(<.R4.R3.)(<.R6.R5.))(1?.R;.R:.R9.R8.R5.R4.)")
(* [comment removed for export] *).
Proof. intros L LBs lo top A n a k CW H1 H2 x Hx. apply CW. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_amemsetWinA (k kn : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(20.+68258.$21.#;.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^2.)(15.(16.$4.$22.)(17.$4.$22.+;.^3.)(15.(16.$4.$22.)(17.$4.$22.+<.^4.)(15.(16.$4.$22.)(17.$4.$22.+2.^6.)(18.(16.$4.$22.))))))(15.(16.$22.$5.)(17.$22.$5.^1.O2.)(15.(16.$22.$5.)(17.$22.$5.^8.#1.)(15.(16.$22.$5.)(17.$22.$5.^9.#2.)(15.(16.$22.$5.)(17.$22.$5.^:.#3.)(15.(16.$22.$5.)(17.$22.$5.^;.O1.)(18.(16.$22.$5.)))))))(23.$22.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^5.)$21.)(18.$24.))(28.(16.$22.$22.)(17.$22.$22.^7.^6.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^5.)))(18.$24.))(15.$2;.(2<.(26.^5.)(26.^;.))(15.$2;.(2=.(2>.=)(26.^3.))(15.$2;.(2?.(26.^3.)(2>.+100.))(15.$2;.(2=.(26.^1.)(26.^2.))(15.$2;.(30.(31.(26.^2.)(2:.-1.(26.^1.)))&2.)(15.$2;.(30.(26.^4.)&2.)(15.$2;.(2=.(2>.=)(26.^4.))(15.$2;.(2=.(31.(26.^2.)(26.^4.))(31.(26.^1.)(2:.+4.(26.^5.))))(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2?.(31.(26.^1.)(2:.+4.(26.^5.)))(2>.(32.+2.+40.)))(15.$2;.(2=.(26.^:.)(26.^7.))(15.$2;.(2=.(26.^7.)(31.(26.^6.)(2:.-1.(26.^9.))))(15.$2;.(33.(26.^7.)(31.(26.^6.)(2:.-1.(26.^7.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^5.)))(26.^7.)(26.^6.)(26.^1.))(15.$2;.(34.(26.^4.)(2>.=)(31.(31.(26.^2.)(26.^4.))(2>.+8.))(2>.(32.+2.+2?.)))(15.$2;.(2?.(26.^4.)(2>.(32.+2.+28.)))(15.$2;.(2=.(26.^6.)(26.^8.))(15.$2;.(2=.(2>.=)(26.^6.))(15.$2;.(2=.(26.^6.)(2>.(35.$36.+1.)))(18.$2;.))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^2.)(31.(26.^2.)(26.^4.)))(15.(16.$37.$37.)(17.$37.$37.(26.^7.)(26.^6.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+:.^<.)(15.(16.$4.$22.)(17.$4.$22.+5.^=.)(15.(16.$4.$22.)(17.$4.$22.+6.^>.)(15.(16.$4.$22.)(17.$4.$22.+7.^?.)(15.(16.$4.$22.)(17.$4.$22.+;.^10.)(15.(16.$4.$22.)(17.$4.$22.+<.^11.)(15.(16.$4.$22.)(17.$4.$22.+=.^12.)(15.(16.$4.$22.)(17.$4.$22.+>.^13.)(15.(16.$4.$22.)(17.$4.$22.+?.^14.)(15.(16.$4.$22.)(17.$4.$22.+10.^15.)(15.(16.$4.$22.)(17.$4.$22.+11.^16.)(15.(16.$4.$22.)(17.$4.$22.+1<.^17.)(15.(16.$4.$22.)(17.$4.$22.+1=.^18.)(15.(16.$4.$22.)(17.$4.$22.+1>.^19.)(15.(16.$4.$22.)(17.$4.$22.+1?.^1:.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^2.)(26.^5.)$21.)(15.$24.(38.(26.^7.)(26.^6.))(18.$24.)))(15.$2;.(2<.(26.^<.)(26.^2.))(18.$2;.))(15.$5.#0.(18.$5.)))")
(* [comment removed for export] *).

Eval vm_compute in (su_wf (SUM_amemsetWinA 4 5), su_nl (SUM_amemsetWinA 4 5), su_nrl (SUM_amemsetWinA 4 5)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SOXW.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).
  Hypothesis AMS : arl_amemset R = 0x68258 \/ arl_memset_i R = 0x68258.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L10351776431.97 L168181405.122  L170273881.99   L32200301299.122L32202331469.101L32765967519.115L33391704940.101L33391883132.102L4233288932.98  L4233347736.101 L44956540796.102L50242612090.122L51855138771.122L55808936278.102L55979665626.125L58751640149.102L5951348035.102 L62220318701.125L66201921237.101L66202005189.102L67543993069.125L67730654805.109L7751425327.122 00000H00o01S01k02F02k03C03[04304K04e05@05[06106U07;07V08108F08[08\09609\S1X1p1n2ws2XP2N01i2kk2EpS1X2NX1p1n2ws2LX2XP2N02PN1i2kk2Ep2En2LUS1X2NX1p1n2ws2LX2XP2N02PN1i2kk2Ep2EnS1X1p1n2ws2XP2N01i2kk2EpS1X1p1n2ws2XP2N01i2kk2Ep2LUS1X1p2ws2r13PAL2q12kk2q01r1H2H02q22H9S1X2NX1p1n2ws2N02PN1i2kkS1X2NX1p1n2ws2N02PN1i2kkS1X1p1n2ws2XP2N01i2kk2EnS1X1p1n2ws2N01i2kk2Hk2LUS1X1p1v1n2ws2V02V12N01i2kkS1X1p1n2ws2XP2N01i2kk2En2LUS1X1p1n2ws2XP2N01i2kk2En2LUS1X1p1n2ws2N03N471i2kkS1X2NX1p1n2ws2LX2XP2N01i2kk3ws'4LEN'S1X2NX1p1n3SPu2LO2ws2XP2N02PN3SEP1i2kkS1X1p1n2ws2XP2N01i2kk2En2LUS1X1p1n2ws2N01i2kk3ws'4LEN'S1X1p1n2ws2XP2N01i2kkS1X1p1n2ws2XP2N01i2kkFS1X1p1n2ws2XP1r3NAL1i2q01HS1X2NX1p1n3SPu2LO2ws2LX2XP2N03SEP1i2kk". (* [comment removed for export] *)
  Lemma sum_amemsetWinA_okO (k kn : nat) (X NX : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(12.P,$4.Sp(39.$3:.VR,VHIA,Vh,)O1.)P,(12.$4.(3;.$4.O5.VGS,=)O3.)P,(12.$4.(3;.$4.O4.VGS,=)O2.)P,(1?.(3<.VR,)(3=.$1>.VLB,(3>.VLF,))(3?.VR,)(40.$3:.VR,VHIA,Vh,)O3.(=.+4.O2.))(41.$3:.(42.VR,)VGS,VOPS,O1.(43.O5.O4.))")
(* [comment removed for export] *).
  Proof.
    intros ECS GX GN CW. subst CS. apply apply_summary_soundO.
    unfold SUM_amemsetWinA, q; lx_sum_unfold.
    intros X0 p v n NX0 SPu LO HT NA SL NG.
    intros ws F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GX' GHT GNA GSL GN' R10 R11 R12 R2 ST [HX LX] OD.
    intros ENG V0 V1 XP PAL NAL N0 PN X0P XT SLLO LOSP SCR SEP N47 N40 SPTOP SP0 SP1 OQ0.
    change (X0 = nth k GS 0) in GX'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL; change (NG = nth kn GS 0) in GN';
    change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GX in GX'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite GN in GN'; rewrite O0 in OQ0; cbv beta in OQ0.
    subst X0 HT NA SL NG. rewrite !ENG in *; clear ENG NX0. lxe_pows. cbn in PAL, NAL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    set (i := (p - X) / 4). set (kk := n / 4).
    assert (Ep : p = X + 4 * i) by (subst i; Z.div_mod_to_equations; lia). assert (En : n = 4 * kk) by (subst kk; Z.div_mod_to_equations; lia).
    assert (Hi : 0 <= i) by lia. assert (Hk : 0 <= kk) by lia.
    destruct (lxe_arr_win_u8 asegs m X ws (Z.to_nat i) (Z.to_nat kk) HX ltac:(lia)) as [HU LU].
    replace (X + 4 * Z.of_nat (Z.to_nat i)) with p in HU by lia. rewrite Z2Nat.id in LU by lia.
    assert (ODw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m p n) by (eapply aobj_sub; [exact OD | lia | lia]). clear OD.
    eapply evtA_cut;
    [ destruct AMS as [AE|AE];
      [ eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF p v n LO (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat i) ws))));
        rewrite ?U2; first [ left; symmetry; exact AE | eassumption | eapply lxe_cw_sub; [exact CW | lia | lia] | cbn in *; lia ]
      | eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF p v n LO (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat i) ws))));
        rewrite ?U2; first [ right; symmetry; exact AE | eassumption | eapply lxe_cw_sub; [exact CW | lia | lia] | cbn in *; lia ] ]
    | cbv beta ].
    intros ms' POST; unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH').
    apply evtA_done; rewrite U2 in MU, ST'.
    destruct (lxe_arr_upd_win asegs m m' X ws (Z.to_nat i) (Z.to_nat kk) p n LO SPu _ HX ltac:(lia) ltac:(lia) ltac:(lia) MU WM ltac:(lia) HU' ltac:(rewrite repeat_length; lia))
      as (ws' & HX' & LEN').
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end).
    all: match goal with |- ?g => idtac "SUM_amemsetWinA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOXW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_amemcpyWinA (kd ks knd : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(20.$44.$21.#=.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^3.)(15.(16.$4.$22.)(17.$4.$22.+;.^4.)(15.(16.$4.$22.)(17.$4.$22.+<.^5.)(15.(16.$4.$22.)(17.$4.$22.+2.^8.)(18.(16.$4.$22.))))))(15.(16.$22.$5.)(17.$22.$5.^1.O3.)(15.(16.$22.$5.)(17.$22.$5.^2.O2.)(15.(16.$22.$5.)(17.$22.$5.^:.#1.)(15.(16.$22.$5.)(17.$22.$5.^;.#2.)(15.(16.$22.$5.)(17.$22.$5.^<.#3.)(15.(16.$22.$5.)(17.$22.$5.^=.O1.)(18.(16.$22.$5.))))))))(23.$22.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^6.)$21.)(15.$24.(25.(26.^2.)&4.(27.^2.)(26.^7.)$45.)(18.$24.)))(28.(16.$22.$22.)(17.$22.$22.^9.^8.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^6.)))(15.$24.(29.(26.^2.)(2:.+4.(26.^7.)))(18.$24.)))(15.$2;.(2<.(26.^6.)(26.^=.))(15.$2;.(2=.(26.^1.)(26.^3.))(15.$2;.(30.(31.(26.^3.)(2:.-1.(26.^1.)))&2.)(15.$2;.(30.(26.^5.)&2.)(15.$2;.(2=.(2>.=)(26.^5.))(15.$2;.(2=.(31.(26.^3.)(26.^5.))(31.(26.^1.)(2:.+4.(26.^6.))))(15.$2;.(2=.(26.^2.)(26.^4.))(15.$2;.(30.(31.(26.^4.)(2:.-1.(26.^2.)))&2.)(15.$2;.(2=.(31.(26.^4.)(26.^5.))(31.(26.^2.)(2:.+4.(26.^7.))))(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2?.(2>.=)(26.^2.))(15.$2;.(46.(26.^1.)(2:.+4.(26.^6.))(26.^2.)(2:.+4.(26.^7.)))(15.$2;.(2=.(26.^<.)(26.^9.))(15.$2;.(2=.(26.^9.)(31.(26.^8.)(2:.-1.(26.^;.))))(15.$2;.(33.(26.^9.)(31.(26.^8.)(2:.-1.(26.^9.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^6.)))(26.^9.)(26.^8.)(26.^1.))(15.$2;.(34.(31.(26.^2.)(2:.+4.(26.^7.)))(26.^9.)(26.^8.)(26.^2.))(15.$2;.(34.(26.^5.)(2>.=)(31.(31.(26.^3.)(26.^5.))(2>.+8.))(2>.(32.+2.+2?.)))(15.$2;.(34.(26.^5.)(2>.=)(31.(31.(26.^4.)(26.^5.))(2>.+8.))(2>.(32.+2.+2?.)))(15.$2;.(2?.(26.^5.)(2>.(32.+2.+28.)))(15.$2;.(2=.(26.^8.)(26.^:.))(15.$2;.(2=.(2>.=)(26.^8.))(15.$2;.(2=.(26.^8.)(2>.(35.$36.+1.)))(18.$2;.))))))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^3.)(31.(26.^3.)(26.^5.)))(15.(16.$37.$37.)(17.$37.$37.(26.^9.)(26.^8.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+:.^>.)(15.(16.$4.$22.)(17.$4.$22.+5.^?.)(15.(16.$4.$22.)(17.$4.$22.+6.^10.)(15.(16.$4.$22.)(17.$4.$22.+7.^11.)(15.(16.$4.$22.)(17.$4.$22.+;.^12.)(15.(16.$4.$22.)(17.$4.$22.+<.^13.)(15.(16.$4.$22.)(17.$4.$22.+=.^14.)(15.(16.$4.$22.)(17.$4.$22.+>.^15.)(15.(16.$4.$22.)(17.$4.$22.+?.^16.)(15.(16.$4.$22.)(17.$4.$22.+10.^17.)(15.(16.$4.$22.)(17.$4.$22.+11.^18.)(15.(16.$4.$22.)(17.$4.$22.+1<.^19.)(15.(16.$4.$22.)(17.$4.$22.+1=.^1:.)(15.(16.$4.$22.)(17.$4.$22.+1>.^1;.)(15.(16.$4.$22.)(17.$4.$22.+1?.^1<.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^3.)(26.^6.)$21.)(15.$24.(38.(26.^9.)(26.^8.))(18.$24.)))(15.$2;.(2<.(26.^>.)(26.^3.))(18.$2;.))(15.$5.#0.(18.$5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_amemmoveWinA (k kn : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(20.$47.$21.#;.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^2.)(15.(16.$4.$22.)(17.$4.$22.+;.^3.)(15.(16.$4.$22.)(17.$4.$22.+<.^4.)(15.(16.$4.$22.)(17.$4.$22.+2.^6.)(18.(16.$4.$22.))))))(15.(16.$22.$5.)(17.$22.$5.^1.O2.)(15.(16.$22.$5.)(17.$22.$5.^8.#1.)(15.(16.$22.$5.)(17.$22.$5.^9.#2.)(15.(16.$22.$5.)(17.$22.$5.^:.#3.)(15.(16.$22.$5.)(17.$22.$5.^;.O1.)(18.(16.$22.$5.)))))))(23.$22.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^5.)$21.)(18.$24.))(28.(16.$22.$22.)(17.$22.$22.^7.^6.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^5.)))(18.$24.))(15.$2;.(2<.(26.^5.)(26.^;.))(15.$2;.(2=.(26.^1.)(26.^2.))(15.$2;.(30.(31.(26.^2.)(2:.-1.(26.^1.)))&2.)(15.$2;.(30.(26.^4.)&2.)(15.$2;.(2=.(2>.=)(26.^4.))(15.$2;.(2=.(31.(26.^2.)(26.^4.))(31.(26.^1.)(2:.+4.(26.^5.))))(15.$2;.(2=.(26.^1.)(26.^3.))(15.$2;.(30.(31.(26.^3.)(2:.-1.(26.^1.)))&2.)(15.$2;.(2=.(31.(26.^3.)(26.^4.))(31.(26.^1.)(2:.+4.(26.^5.))))(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2=.(26.^:.)(26.^7.))(15.$2;.(2=.(26.^7.)(31.(26.^6.)(2:.-1.(26.^9.))))(15.$2;.(33.(26.^7.)(31.(26.^6.)(2:.-1.(26.^7.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^5.)))(26.^7.)(26.^6.)(26.^1.))(15.$2;.(34.(26.^4.)(2>.=)(31.(31.(26.^2.)(26.^4.))(2>.+8.))(2>.(32.+2.+2?.)))(15.$2;.(34.(26.^4.)(2>.=)(31.(31.(26.^3.)(26.^4.))(2>.+8.))(2>.(32.+2.+2?.)))(15.$2;.(2?.(26.^4.)(2>.(32.+2.+28.)))(15.$2;.(2=.(26.^6.)(26.^8.))(15.$2;.(2=.(2>.=)(26.^6.))(15.$2;.(2=.(26.^6.)(2>.(35.$36.+1.)))(18.$2;.)))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^2.)(31.(26.^2.)(26.^4.)))(15.(16.$37.$37.)(17.$37.$37.(26.^7.)(26.^6.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+:.^<.)(15.(16.$4.$22.)(17.$4.$22.+5.^=.)(15.(16.$4.$22.)(17.$4.$22.+6.^>.)(15.(16.$4.$22.)(17.$4.$22.+7.^?.)(15.(16.$4.$22.)(17.$4.$22.+;.^10.)(15.(16.$4.$22.)(17.$4.$22.+<.^11.)(15.(16.$4.$22.)(17.$4.$22.+=.^12.)(15.(16.$4.$22.)(17.$4.$22.+>.^13.)(15.(16.$4.$22.)(17.$4.$22.+?.^14.)(15.(16.$4.$22.)(17.$4.$22.+10.^15.)(15.(16.$4.$22.)(17.$4.$22.+11.^16.)(15.(16.$4.$22.)(17.$4.$22.+1<.^17.)(15.(16.$4.$22.)(17.$4.$22.+1=.^18.)(15.(16.$4.$22.)(17.$4.$22.+1>.^19.)(15.(16.$4.$22.)(17.$4.$22.+1?.^1:.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^2.)(26.^5.)$21.)(15.$24.(38.(26.^7.)(26.^6.))(18.$24.)))(15.$2;.(2<.(26.^<.)(26.^2.))(18.$2;.))(15.$5.#0.(18.$5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_coreaddXXBA : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(48.$49.$21.#8.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^1.)(15.(16.$4.$22.)(17.$4.$22.+;.^1.)(15.(16.$4.$22.)(17.$4.$22.+<.^2.)(15.(16.$4.$22.)(17.$4.$22.+=.^3.)(15.(16.$4.$22.)(17.$4.$22.+2.^6.)(18.(16.$4.$22.)))))))(18.(16.$22.$5.))(28.$22.^8.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^4.)$21.)(15.$24.(25.(26.^2.)&4.(27.^2.)(26.^5.)$45.)(18.$24.)))(28.(16.$22.$22.)(17.$22.$22.^7.^6.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^3.)))(15.$24.(29.(26.^2.)(2:.+4.(26.^3.)))(15.$24.(4:.(2>.$4;.)(15.$4<.(4=.&8.(2>.$4>.))(18.$4<.)))(15.$24.(4:.(2>.$4>.)(15.$4<.(4=.&8.(26.^8.))(18.$4<.)))(18.$24.)))))(15.$2;.(2=.(2>.=)(26.^3.))(15.$2;.(2=.(26.^3.)(2>.+2710.))(15.$2;.(2=.(26.^3.)(26.^4.))(15.$2;.(2=.(26.^3.)(26.^5.))(15.$2;.(46.(26.^2.)(2:.+4.(26.^5.))(26.^1.)(2:.+4.(26.^4.)))(15.$2;.(30.(4?.^1.)&2.)(15.$2;.(30.(4?.^2.)&2.)(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2?.(2>.=)(26.^2.))(15.$2;.(2=.(26.^7.)(31.(26.^6.)(2>.(50.$51.))))(15.$2;.(30.(4?.^6.)&4.)(15.$2;.(33.(26.^7.)(31.(26.^6.)(2:.-1.(26.^7.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^4.)))(31.(26.^6.)(2>.(50.$51.)))(26.^6.)(26.^1.))(15.$2;.(34.(31.(26.^2.)(2:.+4.(26.^5.)))(31.(26.^6.)(2>.(50.$51.)))(26.^6.)(26.^2.))(15.$2;.(2=.(2>.=)(26.^6.))(15.$2;.(2=.(26.^6.)(2>.(35.$36.+1.)))(18.$2;.)))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^1.)(31.(26.^1.)(2:.+4.(26.^3.))))(15.(16.$37.$37.)(17.$37.$37.(31.(26.^6.)(2>.(50.$51.)))(26.^6.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+:.^9.)(15.(16.$4.$22.)(17.$4.$22.+5.^:.)(15.(16.$4.$22.)(17.$4.$22.+6.^;.)(15.(16.$4.$22.)(17.$4.$22.+7.^<.)(15.(16.$4.$22.)(17.$4.$22.+;.^=.)(15.(16.$4.$22.)(17.$4.$22.+<.^>.)(15.(16.$4.$22.)(17.$4.$22.+=.^?.)(15.(16.$4.$22.)(17.$4.$22.+>.^10.)(15.(16.$4.$22.)(17.$4.$22.+?.^11.)(15.(16.$4.$22.)(17.$4.$22.+10.^12.)(15.(16.$4.$22.)(17.$4.$22.+11.^13.)(15.(16.$4.$22.)(17.$4.$22.+1<.^14.)(15.(16.$4.$22.)(17.$4.$22.+1=.^15.)(15.(16.$4.$22.)(17.$4.$22.+1>.^16.)(15.(16.$4.$22.)(17.$4.$22.+1?.^17.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^3.)(26.^4.)$21.)(15.$24.(38.(26.^7.)(26.^6.))(18.$24.)))(15.$2;.(2=.(2>.=)(26.^9.))(15.$2;.(2=.(26.^9.)(2>.+1.))(18.$2;.))))")
(* [comment removed for export] *).

Eval vm_compute in (su_wf (SUM_amemcpyWinA 4 6 5), su_nl (SUM_amemcpyWinA 4 6 5), su_nrl (SUM_amemcpyWinA 4 6 5),
                    su_wf (SUM_amemmoveWinA 4 5), su_wf SUM_coreaddXXBA, su_nl SUM_coreaddXXBA, su_nrl SUM_coreaddXXBA).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SOXC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L10351776431.111L10731968645.118L14278016256.118L14280163051.118L27597014529.118L31126788864.118L31436079859.118L31833687486.118L35705592702.142L36568034874.114L36570135806.139L4233288805.113 L4233347101.118 L4233347736.116 L45272753599.112L46678497179.139L46680528933.116L50242612090.139L55807000616.118L56344577719.118L57366062101.142L5949215805.118 L63593940506.135L66584547428.136L67543993069.142L67732751320.130L695369143.139  L699099583.116  L9262013389.118 L9264158758.118 00000U01401R02002Q03C04704_05P06A07507Z08;08\09A09f0:N0;60;Y0<M0=10=\0>O0?@0?A0?h0@\0AP0B10BRS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2EdS1D1S1d1s1n2dl2sl2N03SP_1i1j2kkS1D1S1d1s1n2dl2sl2DP2N01i1j2kkS1D1S1d1s1n2dl2sl2DP2N01i1j2kkS1D1S1d1s1n2NS2dl2sl2N02SN1i1j2kkS1D1S2ND1d1s1n2NS2dl2sl2DP2N02DN2SN3SP_3SEP1i1j2kkS1D1S2ND1d1s1n3SPu2LO2dl2sl2DP2N02DN3SP_4SEPD1i1j2kkS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2Es2LRS1D1S2ND1d1s1n2dl2sl2LD2DP2N03SP_1i1j2kk3dl'4LEN'S1D1S2ND1d1s1n2dl2sl2LD2DP2N02DN3SP_1i1j2kk2Ed2EnS1D1S2ND1d1s1n2dl2sl2LD2DP2N02DN3SP_1i1j2kk2Ed2En2LRS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2EnS1D1S1d1s1n2dl2sl2N01i1j2kk2Hk2LRS1D1S1d1s1n2dl2sl2N01i1j2kk2Hk2LUS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2EsS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2EdS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2Ed2LUS1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2En2LRS1D1S1d1s1n2dl2sl2N03N471i1j2kk3S47S1D1S1d1s1n2NS3SPu2LO2dl2sl2DP2N02SN3SP_4SEPS1i1j2kkS1D1S1d1s1n2dl2sl2N01i1j2kk3dl'4LEN'S1D1S1d1s1n2dl2sl2DP2N03SP_1i1j2kk2En2LU2LRS1D1S1d1s2dl2sl2r23DAL3SP_1j2q22kk2q01r1H2H02q33H14S1D1S1d1s2dl2sl2DP2r03SAL1i2q22kk2q01r1H2H02q12H4FS1D1S1d1s1n2dl2sl2DP1r3NAL3SP_1i1j2q01HS1D1S2ND1d1s1n3SPu2LO2dl2sl2LD2DP2N03SP_4SEPD1i1j2kkS1D1S1d1s1n2NS2dl2sl2LS2DP2N02SN3SP_1i1j2kk2Es2En2LUS1D1S2ND1d1s1n2dl2sl2N02DN1i1j2kkS1D1S2ND1d1s1n2dl2sl2N02DN1i1j2kk". (* [comment removed for export] *)
  Lemma sum_amemcpyWinA_okO (kd ks knd : nat) (D S ND : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(1:.(12.$4.(52.VR,)$44.)(1:.(12.$4.(53.VR,)$44.)(12.$4.(54.VR,)$44.)))P,(12.P,$4.Sp(39.$3:.VR,VHIA,Vh,)O1.)P,(12.$4.(3;.$4.O7.VGS,=)O4.)P,(12.$4.(3;.$4.O6.VGS,=)O3.)P,(12.$4.(3;.$4.O5.VGS,=)O2.)P,(1?.(3<.VR,)(3=.$1>.VLB,(3>.VLF,))(3?.VR,)(40.$3:.VR,VHIA,Vh,)O4.(=.+4.O2.))(41.$3:.(42.VR,)VGS,VOPS,O1.(55.O7.O6.O5.))")
(* [comment removed for export] *).
  Proof.
    intros AMC ECS GD GSs GN CW. subst CS. apply apply_summary_soundO.
    unfold SUM_amemcpyWinA, q, LXE_AMEMCPY in *; lx_sum_unfold.
    intros D0 S0 d s n ND0 NS SPu LO HT NA SL NG.
    intros dl sl F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GD' GS' GHT GNA GSL GN' R10 R11 R12 R2 ST [HD LD] [HS LS] OD OSo.
    intros ENG DP DAL NAL N0 DN SP_ SAL SN D0P S0P SEP SLLO LOSP SCR SEPD SEPS N47 S47 N40 SPTOP SP0 SP1 OQ0.
    change (D0 = nth kd GS 0) in GD'; change (S0 = nth ks GS 0) in GS'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA;
    change (SL = nth 3 GS 0) in GSL; change (NG = nth knd GS 0) in GN'; change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GD in GD'; rewrite GSs in GS'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite GN in GN'; rewrite O0 in OQ0; cbv beta in OQ0.
    subst D0 S0 HT NA SL NG. rewrite !ENG in *; clear ENG ND0. lxe_pows. cbn in DAL, SAL, NAL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    set (i := (d - D) / 4). set (j := (s - S) / 4). set (kk := n / 4).
    assert (Ed : d = D + 4 * i) by (subst i; Z.div_mod_to_equations; lia).
    assert (Es : s = S + 4 * j) by (subst j; Z.div_mod_to_equations; lia).
    assert (En : n = 4 * kk) by (subst kk; Z.div_mod_to_equations; lia).
    assert (Hi : 0 <= i) by lia. assert (Hj : 0 <= j) by lia. assert (Hk : 0 <= kk) by lia.
    destruct (lxe_arr_win_u8 asegs m D dl (Z.to_nat i) (Z.to_nat kk) HD ltac:(lia)) as [HU LU].
    replace (D + 4 * Z.of_nat (Z.to_nat i)) with d in HU by lia. rewrite Z2Nat.id in LU by lia.
    destruct (lxe_ro_win_ro asegs m S sl (Z.to_nat j) (Z.to_nat kk) HS ltac:(lia)) as [HR LR].
    replace (S + 4 * Z.of_nat (Z.to_nat j)) with s in HR by lia. rewrite Z2Nat.id in LR by lia.
    assert (ODw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m d n) by (eapply aobj_sub; [exact OD | lia | lia]). clear OD.
    assert (OSw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m s n) by (eapply aobj_sub; [exact OSo | lia | lia]). clear OSo.
    eapply evtA_cut;
    [ eapply (artA_amemcpy asegs R HIA 0x67dbc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF d s n LO
                (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat i) dl))) (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat j) sl))));
      rewrite ?U2; first [ exact AMC
                         | destruct AMC as [AE|[AE|AE]]; [left | right; left | right; right]; symmetry; exact AE
                         | eassumption | eapply lxe_cw_sub; [exact CW | lia | lia] | cbn in *; lia ]
    | cbv beta ].
    intros ms' POST; unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH').
    apply evtA_done; rewrite U2 in MU, ST'.
    destruct (lxe_arr_upd_win asegs m m' D dl (Z.to_nat i) (Z.to_nat kk) d n LO SPu _ HD ltac:(lia) ltac:(lia) ltac:(lia) MU WM ltac:(lia) HU' ltac:(rewrite LR; symmetry; exact En))
      as (dl' & HD' & LEN').
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?dd ?mm => change (nth 0%nat OPS dd mm); rewrite O0; cbv beta; exact HH' end).
    all: match goal with |- ?g => idtac "SUM_amemcpyWinA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L10351776431.100L16481039092.107L16481481718.109L168181405.130  L170273881.103  L21300977506.108L21373684862.124L23447239292.105L27663054797.107L31433916442.109L33643944569.105L33645974983.130L4233288805.102 L4233347101.107 L4233347736.105 L45272753599.101L50242612090.130L52151392501.108L55607077431.109L55607520053.107L55809163969.109L55979665626.133L56342152286.109L57366062101.133L5951641300.109 L63675917349.125L67543993069.133L67732751320.119L7751425327.130 00000P00i01B02102]03703e04W05:06106T07407T08008L08l09O09k0:G0:c0;A0;m0<[0=:0=`0>L0>M0>o0?]S1X1d1s1n2ws2DP2N03SP_1i1j2kk2EdS1X1d1s1n2ws2DP2N01i1j2kkS1X1d1s1n2ws2DP2N01i1j2kkS1X2NX1d1s1n2ws2LX2DP2N03SP_2DN1i1j2kk2Ed2En2LRS1X2NX1d1s1n2ws2LX2DP2N03SP_2DN1i1j2kk2Ed2EnS1X1d1s1n2ws2N03SP_1i1j2kkS1X1d1s2ws2r23DAL3SP_1j2q22kk2q01r1H2H02q33H14S1X2NX1d1s1n2ws2LX2DP2N02SN3SP_2DN1i1j2kk2Es2En2LUS1X1d1s1n2ws2DP2N03SP_1i1j2kk2Es2LRS1X2NX1d1s1n3SPu2LO2ws2LX2DP2N03SP_2DN3SEP1i1j2kk2Ed2EnS1X1d1s1n2ws2DP2N03SP_1i1j2kk2Ed2LUS1X1d1s1n2ws2DP2N03SP_1i1j2kk2EdS1X1d1s1n2ws2DP2N03SP_1i1j2kk2EnS1X1d1s1n2ws2N01i1j2kk2Hk2LRS1X1d1s1n2ws2N01i1j2kk2Hk2LUS1X1d1s1n2ws2DP2N03SP_1i1j2kk2EsS1X1d1s1n2ws2DP2N03SP_1i1j2kk2En2LRS1X2NX1d1s1n2ws2N02SN1i1j2kkS1X2NX1d1s1n2ws2N02DN1i1j2kkS1X2NX1d1s1n2ws2N02DN1i1j2kkS1X1d1s1n2ws2N03N471i1j2kk3S47S1X2NX1d1s1n2ws2LX2DP2N03SP_1i1j2kk3ws'4LEN'S1X2NX1d1s1n3SPu2LO2ws2DP2N02SN3SP_3SEP1i1j2kkS1X1d1s1n2ws2N01i1j2kk3ws'4LEN'S1X1d1s1n2ws2DP2N03SP_1i1j2kk2En2LU2LRS1X1d1s2ws2DP2r03SAL1i2q22kk2q01r1H2H02q12H4FS1X1d1s1n2ws2DP1r3NAL3SP_1i1j2q01HS1X2NX1d1s1n3SPu2LO2ws2LX2DP2N03SP_3SEP1i1j2kk". (* [comment removed for export] *)
  Lemma sum_amemmoveWinA_okO (k kn : nat) (X NX : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(56.$3:.VR,VHIA,$47.)P,(12.P,$4.Sp(39.$3:.VR,VHIA,Vh,)O1.)P,(12.$4.(3;.$4.O5.VGS,=)O3.)P,(12.$4.(3;.$4.O4.VGS,=)O2.)P,(1?.(3<.VR,)(3=.$1>.VLB,(3>.VLF,))(3?.VR,)(40.$3:.VR,VHIA,Vh,)O3.(=.+4.O2.))(41.$3:.(42.VR,)VGS,VOPS,O1.(57.O5.O4.))")
(* [comment removed for export] *).
  Proof.
    intros AMM ECS GX GN CW. subst CS. apply apply_summary_soundO.
    unfold SUM_amemmoveWinA, q; lx_sum_unfold.
    intros X0 d s n NX0 SPu LO HT NA SL NG.
    intros ws F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GX' GHT GNA GSL GN' R10 R11 R12 R2 ST [HX LX] OD.
    intros ENG DP DAL NAL N0 DN SP_ SAL SN X0P SLLO LOSP SCR SEP N47 S47 N40 SPTOP SP0 SP1 OQ0.
    change (X0 = nth k GS 0) in GX'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL;
    change (NG = nth kn GS 0) in GN'; change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GX in GX'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite GN in GN'; rewrite O0 in OQ0; cbv beta in OQ0.
    subst X0 HT NA SL NG. rewrite !ENG in *; clear ENG NX0. lxe_pows. cbn in DAL, SAL, NAL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    set (i := (d - X) / 4). set (j := (s - X) / 4). set (kk := n / 4).
    assert (Ed : d = X + 4 * i) by (subst i; Z.div_mod_to_equations; lia).
    assert (Es : s = X + 4 * j) by (subst j; Z.div_mod_to_equations; lia).
    assert (En : n = 4 * kk) by (subst kk; Z.div_mod_to_equations; lia).
    assert (Hi : 0 <= i) by lia. assert (Hj : 0 <= j) by lia. assert (Hk : 0 <= kk) by lia.
    destruct (lxe_arr_win_u8 asegs m X ws (Z.to_nat i) (Z.to_nat kk) HX ltac:(lia)) as [HU LU].
    replace (X + 4 * Z.of_nat (Z.to_nat i)) with d in HU by lia. rewrite Z2Nat.id in LU by lia.
    destruct (lxe_arr_win_ro asegs m X ws (Z.to_nat j) (Z.to_nat kk) HX ltac:(lia)) as [HR LR].
    replace (X + 4 * Z.of_nat (Z.to_nat j)) with s in HR by lia. rewrite Z2Nat.id in LR by lia.
    assert (ODw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m d n) by (eapply aobj_sub; [exact OD | lia | lia]).
    assert (OSw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m s n) by (eapply aobj_sub; [exact OD | lia | lia]). clear OD.
    pose proof AMM as SP. unfold amemmove_stmtA in SP.
    eapply evtA_cut;
    [ eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF d s n LO
                (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat i) ws))) (u32s (firstn (Z.to_nat kk) (skipn (Z.to_nat j) ws))));
      rewrite ?U2; first [ eassumption | eapply lxe_cw_sub; [exact CW | lia | lia] | cbn in *; lia ]
    | cbv beta ].
    intros ms' POST; unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH').
    apply evtA_done; rewrite U2 in MU, ST'.
    destruct (lxe_arr_upd_win asegs m m' X ws (Z.to_nat i) (Z.to_nat kk) d n LO SPu _ HX ltac:(lia) ltac:(lia) ltac:(lia) MU WM ltac:(lia) HU' ltac:(rewrite LR; symmetry; exact En))
      as (ws' & HX' & LEN').
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?dd ?mm => change (nth 0%nat OPS dd mm); rewrite O0; cbv beta; exact HH' end).
    all: match goal with |- ?g => idtac "SUM_amemmoveWinA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOXC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SGC.
  Context {HL : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L1282180577.93  L228320730.119  L23000429473.93 L23348135916.119L38481954273.93 L55672721719.93 L58059825307.93 L60448205867.93 L63425482399.93 L68388506558.119L7522864379.93  00000X01E01F01j02S03R04I04g05d06H06IS1X1B1n2NX3SPu2xs2zs2LX3PR33PR83PR94PR15S1X1B1n2NX3SPu2xs2zs2LX3PR83PR94PR153xs'4LEN'FS1X1B1n3SPu2xs2zs4PR151c3xs'2HC4LEN'S1X1B1n2NB3SPu2xs2zs3LBz3PR43PR83PR94PR15S1X1B2NX2NB3SPu2xs2zs2LX3LBz3PR53PR63PR73PR83PR94PR134PR144PR15S1X1B2NX2NB3SPu2xs2zs2LX3LBz3PR73PR83PR94PR114PR144PR15S1X1B1n3SPu2xs2zs3PR13PR24PR15S1X1B1n2NX2NB3SPu2xs2zs2LX3PR13PR43PR63PR83PR94PR114PR134PR15S1X1B1n3SPu2xs2zs4PR151c3xs'2HC4LEN'F". (* [comment removed for export] *)
  Lemma sum_coreaddXXBA_validG : forall GS, summary_validG asegs AL GS SUM_coreaddXXBA.
  Proof.
    intros GS. unfold SUM_coreaddXXBA, q, LXE_GOT, LXE_GSB, MPI_CORE_ADD_STACK_A. lx_sum_unfold.
    intros X B n NX NB SPu lo sb.
    intros xs zs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R13 R2 ST [HX LX] [HB LBz] OX OB G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16.
    lxe_pows. cbv [Z.opp] in PR10, PR13, PR14. cbn in PR6, PR7, PR11.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB).
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    assert (ABS : abase asegs AL m) by (split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2]).
    pose proof (A_mpi_core_add_spec AL IMG) as SP. unfold mpi_core_add_stmtA, MPI_CORE_ADD_STACK_A in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                X X B n lo xs xs zs);
        rewrite ?U2; first [ eassumption | apply u32arr_ro; exact HX | left; split; reflexivity | right; lia | lia | idtac ]. }
    cbv beta. intros ms' POST. unfold mpi_core_add_postA, MPI_CORE_ADD_STACK_A in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & c & xs' & -> & MU & WM & MI' & -> & HC & HX' & LEN' & SK & LV & ST').
    apply evtA_done. rewrite U2 in MU, ST'.
    lx_sum_post.
    all: match goal with |- ?g => idtac "SUM_coreaddXXBA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sum_coreaddXXBA_okO : forall GS OPS CS, summary_okO asegs AL GS OPS CS SUM_coreaddXXBA.
  Proof. intros GS OPS CS. apply apply_summary_soundO, summary_validG_O, sum_coreaddXXBA_validG. Qed.
End SGC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_coremulA (kx knx : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(20.$58.$21.#10.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^1.)(15.(16.$4.$22.)(17.$4.$22.+;.^2.)(15.(16.$4.$22.)(17.$4.$22.+<.^3.)(15.(16.$4.$22.)(17.$4.$22.+=.^4.)(15.(16.$4.$22.)(17.$4.$22.+>.^5.)(15.(16.$4.$22.)(17.$4.$22.+2.^9.)(15.(16.$4.$22.)(17.$4.$22.+1.^;.)(18.(16.$4.$22.)))))))))(15.(16.$22.$5.)(17.$22.$5.^<.#1.)(15.(16.$22.$5.)(17.$22.$5.^=.#2.)(15.(16.$22.$5.)(17.$22.$5.^>.#3.)(15.(16.$22.$5.)(17.$22.$5.^?.O2.)(15.(16.$22.$5.)(17.$22.$5.^10.O1.)(18.(16.$22.$5.)))))))(23.$22.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^6.)$21.)(15.$24.(25.(26.^2.)&4.(27.^2.)(26.^7.)$45.)(15.$24.(25.(26.^4.)&4.(27.^3.)(26.^8.)$45.)(18.$24.))))(28.(16.$22.$22.)(17.$22.$22.^:.^9.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^6.)))(15.$24.(29.(26.^2.)(2:.+4.(26.^7.)))(15.$24.(29.(26.^4.)(2:.+4.(26.^8.)))(18.$24.))))(15.$2;.(2<.(26.^1.)(26.^?.))(15.$2;.(2<.(26.^6.)(26.^10.))(15.$2;.(2=.(2>.=)(26.^3.))(15.$2;.(2=.(2>.=)(26.^5.))(15.$2;.(2=.(31.(26.^3.)(26.^5.))(2>.+2710.))(15.$2;.(2=.(31.(26.^3.)(26.^5.))(26.^6.))(15.$2;.(2=.(26.^3.)(26.^7.))(15.$2;.(2=.(26.^5.)(26.^8.))(15.$2;.(46.(26.^2.)(2:.+4.(26.^7.))(26.^1.)(2:.+4.(26.^6.)))(15.$2;.(46.(26.^4.)(2:.+4.(26.^8.))(26.^1.)(2:.+4.(26.^6.)))(15.$2;.(30.(4?.^1.)&2.)(15.$2;.(30.(4?.^2.)&2.)(15.$2;.(30.(4?.^4.)&2.)(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(34.(26.^3.)(2>.=)(2>.+1.)(26.^2.))(15.$2;.(34.(26.^5.)(2>.=)(2>.+1.)(26.^4.))(15.$2;.(2?.(31.(26.^1.)(2:.+4.(26.^6.)))(2>.(32.+2.+40.)))(15.$2;.(2?.(31.(26.^2.)(2:.+4.(26.^7.)))(2>.(32.+2.+40.)))(15.$2;.(2?.(31.(26.^4.)(2:.+4.(26.^8.)))(2>.(32.+2.+40.)))(15.$2;.(2=.(26.^>.)(26.^:.))(15.$2;.(2=.(26.^:.)(31.(31.(26.^9.)(2>.(50.$59.)))(2:.-1.(26.^=.))))(15.$2;.(2=.(26.^9.)(26.^<.))(15.$2;.(30.(4?.^9.)&4.)(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^6.)))(26.^:.)(26.^9.)(26.^1.))(15.$2;.(34.(31.(26.^2.)(2:.+4.(26.^7.)))(26.^:.)(26.^9.)(26.^2.))(15.$2;.(34.(31.(26.^4.)(2:.+4.(26.^8.)))(26.^:.)(26.^9.)(26.^4.))(15.$2;.(33.(26.^:.)(31.(26.^9.)(2:.-1.(26.^:.))))(15.$2;.(30.(4?.^;.)&1.)(15.$2;.(2=.(2>.=)(26.^9.))(15.$2;.(2=.(26.^9.)(2>.(35.$36.+1.)))(15.$2;.(2=.(2>.=)(26.^;.))(15.$2;.(2=.(26.^;.)(2>.(35.$36.+1.)))(18.$2;.)))))))))))))))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^1.)(31.(26.^1.)(2:.+4.(31.(26.^3.)(26.^5.)))))(15.(16.$37.$37.)(17.$37.$37.(26.^:.)(26.^9.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+5.^11.)(15.(16.$4.$22.)(17.$4.$22.+6.^12.)(15.(16.$4.$22.)(17.$4.$22.+7.^13.)(15.(16.$4.$22.)(17.$4.$22.+:.^14.)(15.(16.$4.$22.)(17.$4.$22.+;.^15.)(15.(16.$4.$22.)(17.$4.$22.+<.^16.)(15.(16.$4.$22.)(17.$4.$22.+=.^17.)(15.(16.$4.$22.)(17.$4.$22.+>.^18.)(15.(16.$4.$22.)(17.$4.$22.+?.^19.)(15.(16.$4.$22.)(17.$4.$22.+10.^1:.)(15.(16.$4.$22.)(17.$4.$22.+11.^1;.)(15.(16.$4.$22.)(17.$4.$22.+1<.^1<.)(15.(16.$4.$22.)(17.$4.$22.+1=.^1=.)(15.(16.$4.$22.)(17.$4.$22.+1>.^1>.)(15.(16.$4.$22.)(17.$4.$22.+1?.^1?.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^4.)(26.^6.)$21.)(15.$24.(38.(26.^:.)(26.^9.))(18.$24.)))(18.$2;.)(15.$5.#0.(18.$5.)))")
(* [comment removed for export] *).

Eval vm_compute in (su_wf (SUM_coremulA 4 5), su_nl (SUM_coremulA 4 5), su_nrl (SUM_coremulA 4 5)).

Section SOXM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11200866206.122L15028896074.122L15199003533.122L17017932370.122L1820788193.122 L18684245632.122L19743573473.122L228404186.147  L34323550731.121L37710324985.121L379047126.122  L45542131645.122L46466657251.121L46466685504.122L5198038747.122 L53147742195.122L5485158313.121 L5485194762.122 L55672721719.122L59358596116.121L61918965667.121L67529247213.147L7753404694.122 00000\01F02002c03T04f05V06H07507T08f09R0:B0;20;_0<g0=F0=e0>d0?Q0@00@10AFS1X1A1B2NA3SPu2RA2xs2ys2zs2LA3NZX2AT3SP03RA0S1X1A2an1B3SPu2RA2xs2ys2zs3Han3NZA3SP03RA0S1X1A1B2bn3SPu2RA2xs2ys2zs3Hbn3NZB3SP03RA0S1X2NX1A2an1B2bn3SPu2RA2xs2ys2zs2LX3LXn3NZX3SP03RA0S1X1A1B2bn2NB3SPu2RA2xs2ys2zs3LBz3LBn3NZX3SP03RA0S1X2NX1A1B2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA3LBz3ALX2DB2DA3ALA3ALB3NZX3SPA2SA3SP03RA0S1X1A2an1B2NA3SPu2RA2xs2ys2zs2LA3LAn3NZX3SP03RA0S1X2NX1A1B3SPu2RA2xs2ys2zs2LX3NZX3SP03RA03xs'4LEN'S1X1A1B2bn2NB3SPu2RA2xs2ys2zs3LBn3NZX3SP03RA0S1X1A1B3SPu2RA2xs2ys2zs3SP03RA0S1X2NX1A1B2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA3LBz3ALX2DB2DA3ALA3ALB3NZX3SPA2SB3SP03RA0S1X2NX1A1B3SPu2RA2xs2ys2zs2LX3NZX2XT3SP03RA0S1X2NX1A2an1B2bn3SPu2RA2xs2ys2zs3LXn3NZX3SP03RA0S1X2NX1A2an1B2bn3SPu2RA2xs2ys2zs3LXn3NZX3SP03RA0S1X1A1B2NB3SPu2RA2xs2ys2zs3LBz3NZX2BT3SP03RA0S1X2NX1A1B2NA2NB3SPu2RA2xs2ys2zs2LX2LA3LBz3ALX2DB2DA3ALA3ALB3NZX3SP03RA0S1X1A1B3SPu2RA2xs2ys2zs3SP03RA0S1X1A1B3SPu2RA2xs2ys2zs3SP03RA0S1X2NX1A1B2NB3SPu2RA2xs2ys2zs2LX3LBz3ALX2DB3ALA3ALB3NZX3SP03RA0S1X1A2an1B2NA3SPu2RA2xs2ys2zs3LAn3NZX3SP03RA0S1X1A1B3SPu2RA2xs2ys2zs3SP03RA0FS1X2NX1A1B2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA3LBz3ALX2DB2DA3ALA3ALB3NZX3SPA2SX2SB3SP03RA0". (* [comment removed for export] *)
  Lemma sum_coremulA_okO (kx knx : nat) (X NX : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(12.P,$4.Sp(39.$3:.VR,VHIA,Vh,)O1.)P,(12.$4.(3;.$4.O5.VGS,=)O3.)P,(12.$4.(3;.$4.O4.VGS,=)O2.)P,(1?.(3<.VR,)(3=.$1>.VLB,(3>.VLF,))(3?.VR,)(40.$3:.VR,VHIA,Vh,)O3.(=.+4.O2.))(41.$3:.(42.VR,)VGS,VOPS,O1.(5:.O5.O4.))")
(* [comment removed for export] *).
  Proof.
    intros ECS GX GN CW. subst CS. apply apply_summary_soundO.
    unfold SUM_coremulA, q, MPI_CORE_MUL_STACK_A; lx_sum_unfold.
    intros X0 A an B bn NX0 NA NB SPu LO RA HT NEEDA SL XG NXG.
    intros xs ys zs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GHT GNA GSL GX' GN' R10 R11 R12 R13 R14 R2 R1 ST [HX LX] [HA LA] [HB LBz] OX OA OB.
    intros EXG ENG Han Hbn Hab LXn LAn LBn DA DB ALX ALA ALB NZX NZA NZB XT AT BT SLLO LOSP SPTOP SPA SX SA SB SCR RAE SP0 SP1 RA0 RA1 OQ0.
    change (HT = nth 1 GS 0) in GHT; change (NEEDA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL;
    change (XG = nth kx GS 0) in GX'; change (NXG = nth knx GS 0) in GN'; change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite GX in GX'; rewrite GN in GN'; rewrite O0 in OQ0; cbv beta in OQ0.
    subst HT NEEDA SL XG NXG. subst X0. rewrite !ENG in *; clear ENG NX0. lxe_pows. cbv [Z.opp] in LOSP. cbn in ALX, ALA, ALB, SPA, RAE.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxe_uw64; assumption).
    assert (OXw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m X (4 * (an + bn))) by (eapply aobj_sub; [exact OX | lia | lia]). clear OX.
    assert (OAw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m A (4 * an)) by (eapply aobj_sub; [exact OA | lia | lia]). clear OA.
    assert (OBw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m B (4 * bn)) by (eapply aobj_sub; [exact OB | lia | lia]). clear OB.
    pose proof CMUL as SP. unfold mpi_core_mul_stmtA, MPI_CORE_MUL_STACK_A in SP.
    eapply evtA_cut;
    [ eapply (SP h LB LF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                X A an B bn LO xs ys zs);
      rewrite ?U2, ?U1; first [ eassumption | eapply lxe_cw_sub; [exact CW | lia | lia] | lia | idtac ]
    | cbv beta ].
    all: try match goal with |- evtA _ _ _ _ _ => fail | |- forall _ : machine_state, _ => fail | |- ?g => idtac "SUM_coremulA-PRE-LEFT:" g end.
    intros ms' POST. unfold mpi_core_mul_postA, MPI_CORE_MUL_STACK_A in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & -> & MU & WM & MI' & HX' & LEN' & SK & ST' & HH').
    apply evtA_done. rewrite U2 in MU, ST'.
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?dd ?mm => change (nth 0%nat OPS dd mm); rewrite O0; cbv beta; exact HH' end).
    all: match goal with |- ?g => idtac "SUM_coremulA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOXM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_mlaWin1A (k kn : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(48.$5;.$21.#;.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^2.)(15.(16.$4.$22.)(17.$4.$22.+;.^3.)(15.(16.$4.$22.)(17.$4.$22.+<.^4.)(15.(16.$4.$22.)(17.$4.$22.+=.^5.)(15.(16.$4.$22.)(17.$4.$22.+2.^7.)(15.(16.$4.$22.)(17.$4.$22.+1.^9.)(18.(16.$4.$22.))))))))(15.(16.$22.$5.)(17.$22.$5.^1.O2.)(15.(16.$22.$5.)(17.$22.$5.^;.O1.)(18.(16.$22.$5.))))(28.$22.^:.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^6.)$21.)(18.$24.))(28.(16.$22.$22.)(17.$22.$22.^8.^7.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^6.)))(15.$24.(4:.(2>.$4;.)(15.$4<.(4=.&8.(2>.$4>.))(18.$4<.)))(15.$24.(4:.(2>.$4>.)(15.$4<.(4=.&8.(26.^:.))(18.$4<.)))(18.$24.))))(15.$2;.(2<.(26.^6.)(26.^;.))(15.$2;.(2=.(26.^1.)(26.^2.))(15.$2;.(30.(31.(26.^2.)(2:.-1.(26.^1.)))&2.)(15.$2;.(2=.(31.(26.^2.)(2:.+4.(26.^3.)))(31.(26.^1.)(2:.+4.(26.^6.))))(15.$2;.(2=.(26.^1.)(26.^4.))(15.$2;.(30.(31.(26.^4.)(2:.-1.(26.^1.)))&2.)(15.$2;.(2=.(31.(26.^4.)(2:.+4.(26.^5.)))(31.(26.^1.)(2:.+4.(26.^6.))))(15.$2;.(46.(26.^2.)(2:.+4.(26.^3.))(26.^4.)(2:.+4.(26.^5.)))(15.$2;.(2=.(2>.=)(26.^3.))(15.$2;.(2=.(26.^3.)(2>.+2710.))(15.$2;.(2=.(2>.=)(26.^5.))(15.$2;.(2=.(26.^5.)(2>.+2710.))(15.$2;.(30.(4?.^1.)&2.)(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2?.(31.(26.^1.)(2:.+4.(26.^6.)))(2>.(32.+2.+40.)))(15.$2;.(2=.(26.^8.)(31.(26.^7.)(2>.(50.$5<.))))(15.$2;.(30.(4?.^7.)&4.)(15.$2;.(33.(26.^8.)(31.(26.^7.)(2:.-1.(26.^8.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^6.)))(26.^8.)(26.^7.)(26.^1.))(15.$2;.(30.(4?.^9.)&1.)(15.$2;.(2=.(2>.=)(26.^7.))(15.$2;.(2=.(26.^7.)(2>.(35.$36.+1.)))(15.$2;.(2=.(2>.=)(26.^9.))(15.$2;.(2=.(26.^9.)(2>.(35.$36.+1.)))(18.$2;.)))))))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^2.)(31.(26.^2.)(2:.+4.(26.^3.))))(15.(16.$37.$37.)(17.$37.$37.(31.(26.^7.)(2>.(50.$5<.)))(26.^7.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+5.^<.)(15.(16.$4.$22.)(17.$4.$22.+6.^=.)(15.(16.$4.$22.)(17.$4.$22.+7.^>.)(15.(16.$4.$22.)(17.$4.$22.+:.^?.)(15.(16.$4.$22.)(17.$4.$22.+;.^10.)(15.(16.$4.$22.)(17.$4.$22.+<.^11.)(15.(16.$4.$22.)(17.$4.$22.+=.^12.)(15.(16.$4.$22.)(17.$4.$22.+>.^13.)(15.(16.$4.$22.)(17.$4.$22.+?.^14.)(15.(16.$4.$22.)(17.$4.$22.+10.^15.)(15.(16.$4.$22.)(17.$4.$22.+11.^16.)(15.(16.$4.$22.)(17.$4.$22.+1<.^17.)(15.(16.$4.$22.)(17.$4.$22.+1=.^18.)(15.(16.$4.$22.)(17.$4.$22.+1>.^19.)(15.(16.$4.$22.)(17.$4.$22.+1?.^1:.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^2.)(26.^6.)$21.)(15.$24.(38.(26.^8.)(26.^7.))(18.$24.)))(18.$2;.))")
(* [comment removed for export] *).

Definition SUM_coreaddWin1A (k kn : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "(48.$49.$21.#9.#?.#0.(15.(16.$4.$22.)(17.$4.$22.+:.^2.)(15.(16.$4.$22.)(17.$4.$22.+;.^2.)(15.(16.$4.$22.)(17.$4.$22.+<.^3.)(15.(16.$4.$22.)(17.$4.$22.+=.^4.)(15.(16.$4.$22.)(17.$4.$22.+2.^6.)(18.(16.$4.$22.)))))))(15.(16.$22.$5.)(17.$22.$5.^1.O2.)(15.(16.$22.$5.)(17.$22.$5.^9.O1.)(18.(16.$22.$5.))))(28.$22.^8.)(15.$24.(25.(26.^1.)&4.(27.^1.)(26.^5.)$21.)(18.$24.))(28.(16.$22.$22.)(17.$22.$22.^7.^6.))(18.(16.(16.$22.$22.)$22.))(15.$24.(29.(26.^1.)(2:.+4.(26.^5.)))(15.$24.(4:.(2>.$4;.)(15.$4<.(4=.&8.(2>.$4>.))(18.$4<.)))(15.$24.(4:.(2>.$4>.)(15.$4<.(4=.&8.(26.^8.))(18.$4<.)))(18.$24.))))(15.$2;.(2<.(26.^5.)(26.^9.))(15.$2;.(2=.(26.^1.)(26.^2.))(15.$2;.(30.(31.(26.^2.)(2:.-1.(26.^1.)))&2.)(15.$2;.(2=.(31.(26.^2.)(2:.+4.(26.^4.)))(31.(26.^1.)(2:.+4.(26.^5.))))(15.$2;.(2=.(26.^1.)(26.^3.))(15.$2;.(30.(31.(26.^3.)(2:.-1.(26.^1.)))&2.)(15.$2;.(2=.(31.(26.^3.)(2:.+4.(26.^4.)))(31.(26.^1.)(2:.+4.(26.^5.))))(15.$2;.(46.(26.^2.)(2:.+4.(26.^4.))(26.^3.)(2:.+4.(26.^4.)))(15.$2;.(2=.(2>.=)(26.^4.))(15.$2;.(2=.(26.^4.)(2>.+2710.))(15.$2;.(30.(4?.^1.)&2.)(15.$2;.(2?.(2>.=)(26.^1.))(15.$2;.(2?.(31.(26.^1.)(2:.+4.(26.^5.)))(2>.(32.+2.+40.)))(15.$2;.(2=.(26.^7.)(31.(26.^6.)(2>.(50.$51.))))(15.$2;.(30.(4?.^6.)&4.)(15.$2;.(33.(26.^7.)(31.(26.^6.)(2:.-1.(26.^7.))))(15.$2;.(34.(31.(26.^1.)(2:.+4.(26.^5.)))(26.^7.)(26.^6.)(26.^1.))(15.$2;.(2=.(2>.=)(26.^6.))(15.$2;.(2=.(26.^6.)(2>.(35.$36.+1.)))(18.$2;.))))))))))))))))))))(15.(16.$37.$37.)(17.$37.$37.(26.^2.)(31.(26.^2.)(2:.+4.(26.^4.))))(15.(16.$37.$37.)(17.$37.$37.(31.(26.^6.)(2>.(50.$51.)))(26.^6.))(18.(16.$37.$37.))))(15.(16.$4.$22.)(17.$4.$22.+:.^:.)(15.(16.$4.$22.)(17.$4.$22.+5.^;.)(15.(16.$4.$22.)(17.$4.$22.+6.^<.)(15.(16.$4.$22.)(17.$4.$22.+7.^=.)(15.(16.$4.$22.)(17.$4.$22.+;.^>.)(15.(16.$4.$22.)(17.$4.$22.+<.^?.)(15.(16.$4.$22.)(17.$4.$22.+=.^10.)(15.(16.$4.$22.)(17.$4.$22.+>.^11.)(15.(16.$4.$22.)(17.$4.$22.+?.^12.)(15.(16.$4.$22.)(17.$4.$22.+10.^13.)(15.(16.$4.$22.)(17.$4.$22.+11.^14.)(15.(16.$4.$22.)(17.$4.$22.+1<.^15.)(15.(16.$4.$22.)(17.$4.$22.+1=.^16.)(15.(16.$4.$22.)(17.$4.$22.+1>.^17.)(15.(16.$4.$22.)(17.$4.$22.+1?.^18.)(18.(16.$4.$22.)))))))))))))))))(15.$24.(25.(26.^1.)&4.(27.^2.)(26.^5.)$21.)(15.$24.(38.(26.^7.)(26.^6.))(18.$24.)))(15.$2;.(2=.(2>.=)(26.^:.))(15.$2;.(2=.(26.^:.)(2>.+1.))(18.$2;.))))")
(* [comment removed for export] *).

Eval vm_compute in (su_wf (SUM_mlaWin1A 4 5), su_nl (SUM_mlaWin1A 4 5), su_nrl (SUM_mlaWin1A 4 5),
                    su_wf (SUM_coreaddWin1A 4 5), su_nl (SUM_coreaddWin1A 4 5), su_nrl (SUM_coreaddWin1A 4 5)).

Section SGW1.
  Context {HL : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0@L10351779636.107L16291035295.110L16483135871.113L16555260348.115L19119667983.139L19976080274.115L21298880287.114L21373684990.146L22289586941.114L25331637670.139L26684492587.115L27665151046.113L28814879088.115L29278573058.115L31170598585.115L31387916055.113L31865415955.113L33645796295.139L33645974519.110L42037436654.115L42634386807.115L45272753599.108L4761353609.111 L50125367581.139L5135670297.115 L55979665626.142L56760374966.139L60958957390.115L62252288639.115L63675917477.147L63907435239.110L67363639576.115L8446413611.115 L9244284045.115 L9697440881.139 L9697623105.110 00000Z01I02303803g04N05805_06`08308d09X0:R0;C0<V0=C0=o0>k0?U0@M0AG0B10C60D30E50F=0GN0HG0IY0J@0K;0Kl0L]0MU0Nb0OXS1X1d1s3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j2EdS1X1d2dl1s3SPu2RA2ws2XS2XD4Hdl03X0P3SP03RA01i1jS1X1d2dl1s2sl3SPu2RA2ws2XD3SP03RA01i1j3LSWS1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2XD4Hsl02XT3X0P3SP03RA01i1j2Es3LSWS1X1d2dl1s2sl3SPu2RA2ws3SP03RA01i1j3LSW3ds'3LD'S1X1d2dl1s2sl3SPu2RA2ws3SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS3SP03RA01i1j3LSWS1X1d1s2ws2XS2r33DAL1j2q01r1H2H02q43H19S1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2XD3X0P3SP03RA01i1j2Es3LDW3LSWS1X2NX1d2dl1s2sl3SPu2lo2RA2ws2LX2XS2XD3X0P3ALX4LOSP3SPA3SEP3SP03RA01i1j3LSW3ds'3LD'S1X1d2dl1s2sl3SPu2RA2ws4Hdl04Hdl13SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j2Es3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD2DS3X0P3SP03RA01i1j2Ed2Es3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j3LSWS1X2NX1d2dl1s2sl3SPu2lo2RA2ws2SN2XS2XD4Hsl03X0P3ALX4LOSP3SPA3SEP3SP03RA01i1j2Es3LSWS1X2NX1d2dl1s2sl3SPu2RA2ws2DN3SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws4Hsl03SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j2Ed3LSW3ds'3LD'S1X1d1s3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j2EdS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3ALX3SP03RA01i1j2Es3LSWS1X2NX1d2dl1s2sl3SPu2RA2ws2XS2DN2XD2XT3X0P3SP03RA01i1j3LSWS1X1d1s3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j2EsS1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2DN2XD4Hsl03X0P3SP03RA01i1j2Es3LDWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j3LDW3LSW3ds'3LD'S1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2XD4Hsl03X0P3SP03RA01i1j2Es3LSWS1X2NX1d2dl1s2sl3SPu2RA2ws2LX2XS2XD3X0P3SP03RA01i1j3LSW3ds'3LD'3ws'4LEN'S1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2DN2XD4Hsl03X0P3SP03RA01i1j2Ed3LDW3LSW3ds'3LD'S1X1d2dl1s2sl3SPu2RA2ws2XS2XD4Hsl03X0P3SP03RA01i1j2Es3LSWS1X2NX1d2dl1s2sl3SPu2lo2RA2ws2XS2DN2XD3X0P3ALX4LOSP3SPA3SEP3SP03RA01i1j2Ed3LDW3LSWS1X1d1s2ws2r43SAL2XD1i2q01r1H2H02q53H24S1X2NX1d2dl1s3SPu2RA2ws2LX2XS2DN2XD4Hdl03X0P3SP03RA01i1j2EdS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws4Hsl04Hsl13SP03RA01i1j3LSWS1X1d2dl1s2sl3SPu2RA2ws2XS2XD3X0P3ALX3SP03RA01i1j2Ed3LSWS1X2NX1d2dl1s2sl3SPu2RA2ws2LX2SN2XS2DN2XD4Hsl03X0P3SP03RA01i1j2Ed3LSW3ds'3LD'S1X2NX1d2dl1s3SPu2RA2ws2LX2XS2DN2XD3X0P3SP03RA01i1j2Ed". (* [comment removed for export] *)
  Lemma sum_mlaWin1A_validG (k kn : nat) GS (X NX : Z) : nth k GS 0 = X -> nth kn GS 0 = NX -> summary_validG asegs AL GS (SUM_mlaWin1A k kn).
  Proof.
    intros GX GN. unfold SUM_mlaWin1A, q, LXE_GOT, LXE_GSB, MPI_CORE_MLA_STACK_A. lx_sum_unfold.
    intros X0 d dl s sl NX0 SPu lo RA sb NXG.
    intros ws CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GX' GN' R10 R11 R12 R13 R2 R1 ST [HX LX] OXA G1 G2.
    intros ENG XD DAL DN XS SAL SN DS Hdl0 Hdl1 Hsl0 Hsl1 ALX X0P XT LOSP SPA SCR SEP RAE SP0 SP1 RA0 RA1.
    change (X0 = nth k GS 0) in GX'; change (NXG = nth kn GS 0) in GN'. rewrite GX in GX'; rewrite GN in GN'. subst X0 NXG.
    rewrite !ENG in *; clear ENG NX0. lxe_pows. cbv [Z.opp] in LOSP, SEP. cbn in DAL, SAL, ALX, SPA, RAE.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB).
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxe_uw64; assumption).
    assert (ABS : abase asegs AL m) by (split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2]).
    set (i := (d - X) / 4). set (j := (s - X) / 4).
    assert (Ed : d = X + 4 * i) by (subst i; Z.div_mod_to_equations; lia).
    assert (Es : s = X + 4 * j) by (subst j; Z.div_mod_to_equations; lia).
    assert (Hi : 0 <= i) by lia. assert (Hj : 0 <= j) by lia.
    pose proof HX as HXw. rewrite <- (firstn_skipn (Z.to_nat i) ws) in HXw. apply u32arr_app in HXw. destruct HXw as [_ HXw].
    rewrite firstn_length_le in HXw by lia.
    rewrite <- (firstn_skipn (Z.to_nat dl) (skipn (Z.to_nat i) ws)) in HXw. apply u32arr_app in HXw. destruct HXw as [HDW _].
    replace (X + 4 * Z.of_nat (Z.to_nat i)) with d in HDW by lia.
    assert (LDW : Z.of_nat (length (firstn (Z.to_nat dl) (skipn (Z.to_nat i) ws))) = dl) by (rewrite firstn_length_le by (rewrite length_skipn; lia); lia).
    destruct (lxe_arr_win_ro asegs m X ws (Z.to_nat j) (Z.to_nat sl) HX ltac:(lia)) as [HSW LSW].
    replace (X + 4 * Z.of_nat (Z.to_nat j)) with s in HSW by lia. rewrite Z2Nat.id in LSW by lia. rewrite u32s_length in LSW.
    assert (OD : aobj asegs AL CS m d (4 * dl)) by (eapply aobj_sub; [exact OXA | lia | lia]).
    assert (OS' : aobj asegs AL CS m s (4 * Z.min dl sl)) by (eapply aobj_sub; [exact OXA | lia | lia]). clear OXA.
    pose proof (A_mpi_core_mla_spec AL IMG) as SP. unfold mpi_core_mla_stmtA, MPI_CORE_MLA_STACK_A in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                d dl s sl lo (firstn (Z.to_nat dl) (skipn (Z.to_nat i) ws)) (firstn (Z.to_nat sl) (skipn (Z.to_nat j) ws)));
        rewrite ?U2, ?U1, ?LDW; first [ eassumption | rewrite firstn_length_le by (rewrite length_skipn; lia); lia | lia | idtac ]. }
    all: try match goal with |- evtA _ _ _ _ _ => fail | |- forall _ : machine_state, _ => fail | |- ?g => idtac "SUM_mlaWin1A-PRE-LEFT:" g end.
    cbv beta. intros ms' POST. unfold mpi_core_mla_postA, MPI_CORE_MLA_STACK_A in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ds' & -> & MU & WM & MI' & HD' & LD' & SK & ST').
    apply evtA_done. rewrite U2 in MU, ST'.
    destruct (lxe_arr_upd_win32 asegs m m' X ws (Z.to_nat i) (Z.to_nat dl) d (4 * dl) _ SPu _ HX ltac:(lia) ltac:(lia) ltac:(lia) MU WM ltac:(lia) HD'
                ltac:(rewrite LD', firstn_length_le by (rewrite length_skipn; lia); lia)) as (ws' & HX' & LEN').
    lx_sum_post.
    all: match goal with |- ?g => idtac "SUM_mlaWin1A-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sum_mlaWin1A_okO (k kn : nat) GS (X NX : Z) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(12.$4.(3;.$4.O5.O3.=)O2.)P,(12.$4.(3;.$4.O4.O3.=)O1.)POPS,(0.P,P,(2.&40.)(3.(2.&8.))Sp)PCS,P,$4.Sp(41.$3:.VAL,O3.R2.R1.(5=.O5.O4.))")
(* [comment removed for export] *).
  Proof. intros GX GN OPS CS. apply apply_summary_soundO, summary_validG_O, (sum_mlaWin1A_validG k kn GS X NX GX GN). Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L10351779636.98 L11866083991.106L12711935871.132L12712310607.101L16483135871.104L21298880287.105L21373684979.130L23342320364.135L2426989001.104 L25959061471.132L26677666509.104L27665151046.104L27892142009.106L28814879088.106L29278573058.106L33452283383.105L33645796295.132L33645974519.101L3368203307.132 L3511835047.106 L35966573439.106L39078778898.106L42037436654.106L45272753599.99 L49584940744.106L51855137251.101L55979665626.135L58997403704.132L59627142355.102L60448205867.106L63423384742.132L63675917480.131L63907435239.101L68394550974.135L9244284045.106 00000S01<02=02n03M03l04S05E05e06I06k07T08a09T0::0:\0;Q0<40<f0=_0>f0?B0?o0@R0A80A^0B_0C`0DR0E60FB0Fi0G[0HM0I:S1X1d1s3SPu2ws2XS2XD3X0P3SP01i1j2EdS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j2Es3LSWS1X2NX1d1s1n3SPu2ws2LX2SN2XS2DN2XD3X0P3SP01i1j2Ed3LDW3LSW3ds'3LD'S1X2NX1d1s1n3SPu2ws2LX2SN2XS2DN2XD3X0P3SP01i1j2EdS1X1d1s1n3SPu2ws2XD3SP01i1j3LSWS1X1d1s1n3SPu2ws2XS3SP01i1j3LSWS1X1d1s2ws2XS2r23DAL1j2q01r1H2H02q33H14S1X1d1s1n3SPu2ws3SP01i1j3LSW1c3ds'2HC3LD'3ws'4LEN'S1X1d1s1n3SPu2ws3Hn03SP01i1j3LSWS1X1d1s1n3SPu2ws3SP01i1j3LSW3ds'3LD'S1X2NX1d1s1n3SPu2ws2DN3SP01i1j3LSWS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j2Es3LSWS1X2NX1d1s1n3SPu2lo2ws2SN2XS2DN2XD2DS3X0P3ALX4LOSP3SPA3SEP3SP01i1j2Es3LDW3LSWS1X1d1s1n3SPu2ws2XS2XD2DS3X0P3SP01i1j2Ed2Es3LDW3LSWS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j3LSWS1X2NX1d1s1n3SPu2ws2SN3SP01i1j3LSWS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j2Ed3LDW3LSW3ds'3LD'S1X1d1s3SPu2ws2XS2XD3X0P3SP01i1j2EdS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j3LDW3LSW3ds'3LD'S1X2NX1d1s1n3SPu2ws2LX2SN2XS2DN2XD3X0P3SP01i1j2Es3LDW3LSWS1X2NX1d1s1n3SPu2lo2ws2XS2DN2XD3X0P3ALX4LOSP3SPA3SEP3SP01i1j2Ed3LDW3LSWS1X1d1s1n3SPu2ws3SP01i1j3LSWS1X1d1s1n3SPu2ws2XS2XD3X0P3ALX3SP01i1j2Es3LSWS1X1d1s3SPu2ws2XS2XD3X0P3SP01i1j2EsS1X1d1s1n3SPu2ws2XS2XD3X0P3SP01i1j3LSWS1X1d1s1n3SPu2ws2XS2XD3Hn03X0P3SP01i1jS1X2NX1d1s1n3SPu2ws2LX2XS2XD3X0P3SP01i1j3LDW3LSW3ds'3LD'3ws'4LEN'S1X2NX1d1s1n3SPu2ws2LX2SN2XS2DN2XD3X0P3SP01i1j2Ed3LDW3LSW3ds'3LD'S1X2NX1d1s1n3SPu2ws2LX2SN2XS2XD3X0P3SP01i1j2Es3LDWS1X1d1s1n3SPu2ws3Hn03Hn13SP01i1j3LSWS1X2NX1d1s1n3SPu2lo2ws2LX2XS2XD3X0P3ALX4LOSP3SPA3SEP3SP01i1j3LDW3LSW3ds'3LD'S1X1d1s2ws2r33SAL2XD1i2q01r1H2H02q43H19S1X2NX1d1s1n3SPu2ws2LX2XS2DN2XD3Hn03X0P3SP01i1j2EdS1X1d1s1n3SPu2ws3SP01i1j3LSW1c3ds'2HC3LD'3ws'4LEN'S1X1d1s1n3SPu2ws2XS2XD3X0P3ALX3SP01i1j2Ed3LSW". (* [comment removed for export] *)
  Lemma sum_coreaddWin1A_validG (k kn : nat) GS (X NX : Z) : nth k GS 0 = X -> nth kn GS 0 = NX -> summary_validG asegs AL GS (SUM_coreaddWin1A k kn).
  Proof.
    intros GX GN. unfold SUM_coreaddWin1A, q, LXE_GOT, LXE_GSB, MPI_CORE_ADD_STACK_A. lx_sum_unfold.
    intros X0 d s n NX0 SPu lo sb NXG.
    intros ws CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GX' GN' R10 R11 R12 R13 R2 ST [HX LX] OXA G1 G2.
    intros ENG XD DAL DN XS SAL SN DS Hn0 Hn1 ALX X0P XT LOSP SPA SCR SEP SP0 SP1.
    change (X0 = nth k GS 0) in GX'; change (NXG = nth kn GS 0) in GN'. rewrite GX in GX'; rewrite GN in GN'. subst X0 NXG.
    rewrite !ENG in *; clear ENG NX0. lxe_pows. cbv [Z.opp] in LOSP, SEP. cbn in DAL, SAL, ALX, SPA.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB).
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxe_uw64; assumption).
    assert (ABS : abase asegs AL m) by (split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2]).
    set (i := (d - X) / 4). set (j := (s - X) / 4).
    assert (Ed : d = X + 4 * i) by (subst i; Z.div_mod_to_equations; lia).
    assert (Es : s = X + 4 * j) by (subst j; Z.div_mod_to_equations; lia).
    assert (Hi : 0 <= i) by lia. assert (Hj : 0 <= j) by lia.
    pose proof HX as HXw. rewrite <- (firstn_skipn (Z.to_nat i) ws) in HXw. apply u32arr_app in HXw. destruct HXw as [_ HXw].
    rewrite firstn_length_le in HXw by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) ws)) in HXw. apply u32arr_app in HXw. destruct HXw as [HDW _].
    replace (X + 4 * Z.of_nat (Z.to_nat i)) with d in HDW by lia.
    assert (LDW : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) ws))) = n) by (rewrite firstn_length_le by (rewrite length_skipn; lia); lia).
    destruct (lxe_arr_win_ro asegs m X ws (Z.to_nat j) (Z.to_nat n) HX ltac:(lia)) as [HSW LSW].
    replace (X + 4 * Z.of_nat (Z.to_nat j)) with s in HSW by lia. rewrite Z2Nat.id in LSW by lia. rewrite u32s_length in LSW.
    assert (OD : aobj asegs AL CS m d (4 * n)) by (eapply aobj_sub; [exact OXA | lia | lia]).
    assert (OS : aobj asegs AL CS m s (4 * n)) by (eapply aobj_sub; [exact OXA | lia | lia]). clear OXA.
    pose proof (A_mpi_core_add_spec AL IMG) as SP. unfold mpi_core_add_stmtA, MPI_CORE_ADD_STACK_A in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                d d s n lo (firstn (Z.to_nat n) (skipn (Z.to_nat i) ws)) (firstn (Z.to_nat n) (skipn (Z.to_nat i) ws)) (firstn (Z.to_nat n) (skipn (Z.to_nat j) ws)));
        rewrite ?U2, ?LDW; first [ eassumption | apply u32arr_ro; exact HDW | left; split; reflexivity
                                 | rewrite firstn_length_le by (rewrite length_skipn; lia); lia | lia | idtac ]. }
    all: try match goal with |- evtA _ _ _ _ _ => fail | |- forall _ : machine_state, _ => fail | |- ?g => idtac "SUM_coreaddWin1A-PRE-LEFT:" g end.
    cbv beta. intros ms' POST. unfold mpi_core_add_postA, MPI_CORE_ADD_STACK_A in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & c & ds' & -> & MU & WM & MI' & -> & HC & HD' & LD' & SK & LV & ST').
    apply evtA_done. rewrite U2 in MU, ST'.
    destruct (lxe_arr_upd_win32 asegs m m' X ws (Z.to_nat i) (Z.to_nat n) d (4 * n) _ SPu _ HX ltac:(lia) ltac:(lia) ltac:(lia) MU WM ltac:(lia) HD'
                ltac:(rewrite LD', firstn_length_le by (rewrite length_skipn; lia); lia)) as (ws' & HX' & LEN').
    lx_sum_post.
    all: match goal with |- ?g => idtac "SUM_coreaddWin1A-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sum_coreaddWin1A_okO (k kn : nat) GS (X NX : Z) : ltac2:(CDefT.buildp (gd_tbl_LxAEcpSums ()) "P,(12.$4.(3;.$4.O5.O3.=)O2.)P,(12.$4.(3;.$4.O4.O3.=)O1.)POPS,(0.P,P,(2.&40.)(3.(2.&8.))Sp)PCS,P,$4.Sp(41.$3:.VAL,O3.R2.R1.(5>.O5.O4.))")
(* [comment removed for export] *).
  Proof. intros GX GN OPS CS. apply apply_summary_soundO, summary_validG_O, (sum_coreaddWin1A_validG k kn GS X NX GX GN). Qed.
End SGW1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxe_cw :=
  try (lazymatch goal with |- client_wrange ?L ?LBs ?lo ?top ?a ?n =>
         let a' := eval cbn [List.nth] in a in let n' := eval cbn [List.nth] in n in change (client_wrange L LBs lo top a' n') end);
  first [ assumption
        | match goal with K : client_wrange ?L ?LBs ?lo ?top ?a ?n |- client_wrange ?L ?LBs ?lo ?top ?a ?n' => replace n' with n by lia; exact K end
        | match goal with |- ?g => idtac "lxe_cw: cannot show" g; fail end ].
Ltac lxe_sum1 :=
  lazymatch goal with
  | |- summary_okO _ _ _ _ _ (SUM_amemsetWinA _ _) =>
      eapply sum_amemsetWinA_okO;
      [> reflexivity | reflexivity | reflexivity | reflexivity
       | first [ left; assumption | right; assumption | left; symmetry; assumption | right; symmetry; assumption
               | left; etransitivity; [ eassumption | reflexivity ] | left; symmetry; etransitivity; [ eassumption | reflexivity ] ]
       | first [ reflexivity | assumption | symmetry; assumption ] | reflexivity | reflexivity | lxe_cw ]
  | |- summary_okO _ _ _ _ _ (SUM_amemcpyWinA _ _ _) =>
      eapply sum_amemcpyWinA_okO;
      [> reflexivity | reflexivity | reflexivity | reflexivity
       | first [ left; assumption | right; left; assumption | right; right; assumption
               | left; etransitivity; [ eassumption | reflexivity ] | right; right; etransitivity; [ eassumption | reflexivity ] ]
       | first [ reflexivity | assumption | symmetry; assumption ] | reflexivity | reflexivity | reflexivity | lxe_cw ]
  | |- summary_okO _ _ _ _ _ (SUM_amemmoveWinA _ _) =>
      eapply sum_amemmoveWinA_okO;
      [> reflexivity | reflexivity | reflexivity | reflexivity | assumption
       | first [ reflexivity | assumption | symmetry; assumption ] | reflexivity | reflexivity | lxe_cw ]
  | |- summary_okO _ _ _ _ _ SUM_coreaddXXBA => apply sum_coreaddXXBA_okO; assumption
  | |- summary_okO _ _ _ _ _ (SUM_mlaWin1A _ _) => eapply sum_mlaWin1A_okO; [ assumption | reflexivity | reflexivity ]
  | |- summary_okO _ _ _ _ _ (SUM_coreaddWin1A _ _) => eapply sum_coreaddWin1A_okO; [ assumption | reflexivity | reflexivity ]
  | |- summary_okO _ _ _ _ _ (SUM_coremulA _ _) =>
      eapply sum_coremulA_okO;
      [> reflexivity | reflexivity | reflexivity | reflexivity | assumption
       | first [ reflexivity | assumption | symmetry; assumption ] | reflexivity | reflexivity | lxe_cw ]
  | |- ?g => idtac "lxe_sum1: no ok-lemma for" g; fail
  end.
(* [comment removed for export] *)
Ltac lxe_ops_rest mx hmP acc :=
  match goal with
  | H : lx_opq _ _ _ ?P _ _ mx |- _ =>
      lazymatch P with hmP => fail | _ => lazymatch acc with context [P] => fail | _ => lxe_ops_rest mx hmP constr:(@cons (mem -> Prop) P acc) end end
  | _ => acc
  end.
Ltac lxe_sums_on segs R HIA h LB LF AL CS SUMS OBJS :=
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  let hmP := constr:(fun m => HM segs R HIA h LB LF m) in
  let rest := lxe_ops_rest mx hmP constr:(@nil (mem -> Prop)) in
  let OPS := constr:(@cons (mem -> Prop) hmP rest) in
  let GS := constr:(@cons Z (@alloc_ceiling (arl_L R)) (@cons Z (htop segs R HIA h) (@cons Z (arl_need_amem R) (@cons Z (arl_stklo R) OBJS)))) in
  let HS := fresh "LXSUMS" in
  assert (HS : List.Forall (summary_okO segs AL GS OPS CS) SUMS)
    by (repeat (apply List.Forall_cons; [ lxe_sum1 | ]); apply List.Forall_nil).
Ltac lxe_sums SUMS OBJS :=
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  lazymatch goal with
  | H : lx_opq _ _ _ (fun m => HM ?segs ?R ?HIA ?h ?LB ?LF m) _ _ mx |- evtA _ ?AL ?CS _ _ =>
      lxe_sums_on segs R HIA h LB LF AL CS SUMS OBJS
  | H : lx_opq _ _ _ (fun m => HM ?segs ?R ?HIA ?h ?LB ?LF m) _ _ mx |- aevtA _ (KF _ ?R' ?HIA' ?hc _) _ _ =>
      lxe_sums_on segs R HIA h LB LF constr:(arl_AL R) constr:(hcs segs R HIA hc) SUMS OBJS
  | |- _ => fail "lxe_sums: no lx_opq HM fact at the goal memory (run lxr_pose / lxe_pose first) / not an evtA/aevtA goal"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxe_pose_HM_on segs R HIA hc AL CS :=
  let mx := lxr_cur_mem in
  lazymatch goal with
  | HH : HM segs R HIA hc ?LB ?LF mx |- _ =>
      let L := constr:(arl_L R) in
      let TOP := constr:(htop segs R HIA hc) in
      let cands := lxr_cw_list L constr:([(arl_stklo R, htop segs R HIA hc)] : list ivl) in
      let cands := lxr_in_list cands in
      let shc := lxr_sf_list R constr:(@nil ivl) in
      let shc := lxr_crfb_list shc in
      lxr_filter cands ltac:(fun lo hi => constr:(forall a, lo <= a < hi -> hm_writable R LB LF TOP a))
        ltac:(first [ apply w_writable_of_client_wrange; solve_client_wrange | idtac ];
              try match goal with E : htop ?sg ?R' ?HIA' _ = htop ?sg ?R' ?HIA' _ |- _ => rewrite E end;
              first [ apply w_writable_of_client_wrange; solve_client_wrange
                    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; left; lxr_lia
                    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; right; right;
                      match goal with I : In (?A0, ?n0) _ |- _ => exists (A0, n0); split; [ exact I | cbn [fst snd]; lxr_lia ] end ])
        ltac:(fun ok =>
          lxr_filter shc ltac:(fun lo hi => constr:(forall c, lo <= c < hi -> arl_stklo R <= c < TOP \/ in_block LF c))
            ltac:(idtac; lxr_in_block)
            ltac:(fun sh =>
              let H := fresh "OQH" in
              assert (H : lx_opq segs AL CS (fun m => HM segs R HIA hc LB LF m) ok sh mx);
              [ apply (lx_opq_HM R HIA CS hc LB LF ok sh mx HH); [ lxr_forall_okw | lxr_forall_okw ] | ]));
      lxr_clear_okw
  end.
Ltac lxe_pose :=
  let mx := lxr_cur_mem in
  lazymatch goal with
  | |- evtA _ ?AL ?CS _ _ =>
      try (lazymatch goal with HH : HM ?segs ?R ?HIA ?h _ _ mx |- _ => lxe_pose_HM_on segs R HIA h AL CS end);
      try lxr_pose_presW; try lxr_pose_sshad
  | |- aevtA ?segs (KF _ ?R ?HIA ?hc _) _ _ =>
      try lxe_pose_HM_on segs R HIA hc constr:(arl_AL R) constr:(hcs segs R HIA hc)
  | |- aevtA ?segs (HK _ ?R ?HIA ?hc) _ _ =>
      try lxe_pose_HM_on segs R HIA hc constr:(arl_AL R) constr:(hcs segs R HIA hc)
  end.

(* [comment removed for export] *)
Ltac lxe_leaf_gc :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | u32arr _ _ _ _ => fail | rw_cells _ _ _ _ => fail | bytes_at _ _ _ _ => fail | ro_cells _ _ _ _ => fail | u8arr _ _ _ _ => fail
    | Z.of_nat (length _) = _ => fail | _ = Z.of_nat (length _) => fail
    | context [zlow _ _] => clear H | context [zswrap _ _] => clear H | context [Z.b2z _] => clear H
    end end;
  repeat match goal with
  | H : 0 <= ?v + 2147483648 |- _ => is_var v; clear H
  | H : 0 <= - ?v + 2147483647 |- _ => is_var v; clear H
  | H : 0 <= ?v, H' : 0 <= - ?v + 18446744073709551615 |- _ => is_var v; clear H H'
  | H : 0 <= - ?v + 18446744073709551615 |- _ => is_var v; clear H
  | H : 0 <= - ?v + 255 |- _ => is_var v; clear H
  end;
  repeat match goal with v : Z |- _ => clear v end.

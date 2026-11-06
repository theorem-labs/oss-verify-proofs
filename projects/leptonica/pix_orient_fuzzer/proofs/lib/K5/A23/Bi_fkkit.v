(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_gaps_iface Lept_kit Pm_gaps_iface RT_fk RT_fk_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_fkkit () := "C69OSSVerify5KrLib2K53A238Lept_kit;cps_ASTA_exC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A238Lept_kit?cps_ASTA_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53A238Lept_kit?cps_ASTA_eq_symC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Lept_kit?cps_ASTA_pure_rC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FkKit.
Variable RT : rt_sig.

Lemma cps_ASTA_ex_and : forall {X} Σ PMc (P : X -> machine_state -> Prop) (G : machine_state -> Prop) Q,
  (forall x, cps asegs (ASTA RT Σ PMc (fun ms => P x ms /\ G ms)) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => (exists x, P x ms) /\ G ms)) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_fkkit ()) ["FkKit"] "p'0h01xi001xh12msh22H0h31Gh41Hh52HGh62Hxh71Ph83PMch91Qh:1Xh;2Σp;1p;2p;4p;3p;7p;8p200R0g0000R1p4p7210p8p10010p4p7210p1001\p4p710p8g002:j18Tg0032R2j20Tg003Mj43Tg004Fj32Tg005;R3j21TP1j77Tg005Uj46Tg0060j44Tg006Jj85Tp,2RTR1#8g007Np-0R4[f2R5g008DR6P4[R7[g009KP4[f5R4g00:@P1P4f4R8P8f1R9f0R:O2f3R;P:O1R<'0X16C3;29]0P1P4P8f7R=P4P:P9O2R>P8P9O1R?'0X0='1X16P>X0=,1=/0<R<X16P9P1f6R1P4P8P4P9P:O2P8P:O1'0X16X01P9P:F7P2f8R2P1P:P5O2X02'1P?f9R?P=P:P;O2P1P;O1'0X0?'1P:f:R;P2P:P8O2X0;'1P3f;R3P?P:P4O2X03P2P4O1f=R4P3P:P=O2R8P;P=O1'0X04'1[P:P3P2O1f@R2f>P:P;O2P4P;O1'0X02P5P4P5P?O2f<P?O1P9P:C6C4W5X68X04P9P:O2n2001000000120100000W2P9P:O2n2001000000120000000X2<X16G5W4W9X37W7W8W;X:0o"). Qed.

Lemma cps_ASTA_eq_and : forall Σ PMc ms0 (G : machine_state -> Prop) Q,
  (G ms0 -> cps asegs (ASTA RT Σ PMc (eq ms0)) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => ms = ms0 /\ G ms)) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_fkkit ()) ["FkKit"] "h02msh12HGh21Eh31Gh41Hh52H0h63PMch71Qh83ms0h92Σp;1p;2p;4p;3p;6p;7p;8g002:j1<Tg00;8j2;j39Tg003Mj43Tg004Fj32Tg0032R0j21Tg00;Rj6:Tg00<Vj74Tg00=Zj25Tg005Uj46Tg001\j77Tg006Jj88Tg008DR1f1R2f0R339p=0p,2RTR4#<g007Np-0R5[P5\1g009KP5[P2f2R5O1g00:@P4f5R6f4R7f3R8,;1C3;22[P4P6P71037R9P8P7O1'1X01P8P3O1,19R:X01P2P4P6P7P9X01P5P8O1R9P2P4f6R4P6P7P5P2P3O1E:X19F4P01026P7P2O11054P6P4O1'1P3f7R4,08P4P7O1P1f9R7P7P3O1f;R4,02f:R8P4O1'1]1X01f8P7O11088P7P8O11518P3C6W1P6P2P3F7W1W2P2P3O2n2001000000120000000X5:X01G8W4W7W3X81W6W9o"). Qed.
End FkKit.

Ltac cps_open1F RT :=
  first [ apply cps_ex_l; intro
        | apply cps_and_pure_r; intro
        | apply (cps_ASTA_ex RT); intro
        | apply (cps_ASTA_pure_r RT); intro
        | apply (cps_ASTA_ex_and RT); intro
        | apply (cps_ASTA_eq_and RT); (let FK := fresh "FK" in intro FK; cbn [ms_fregs MS] in FK)
        | apply (cps_ASTA_eq_sym RT) ].
Ltac cps_open RT ::=
  unfold malloc_postF, free_postF, icpt_postF, malloc_post, free_post, icpt_post, ret_stF, ret_st; repeat (cps_open1F RT).

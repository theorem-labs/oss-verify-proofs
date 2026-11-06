(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK
Ja0DefsK Ja0PlanImagesK Ja0StartupK Ja0StartupClosedK Ja0HSK_0 Ja0HSK_1 Ja0HSK_201 Ja0HSK_202 Ja0MainTableK Ja0ResK Ja0CertK_root Ja0CertK_201 Ja0CertK_202.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0StartupFinalK () := ([""; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0CertK_201."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0CertK_root."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ResK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StartupK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."], [["1init_config"; "2LIMIT"; "2SINV0"; "2argH0"; "2inp"; "3holes_stmt"; "4itab_sound"; "5JS_as0_201"; "6JS_as0_root"; "7APH0"; "7ASAN0"; "7ASEGS0"; "8IT0"; "9HOLES"; ":srealizes"; ";init_pc"]; ["0T"; "0abrt"; "0argv"; "0brk0"; "0envp"; "0fs"; "0gid"; "0groups"; "0hw"; "0mbase"; "0net"; "0nofile"; "0rdraw"; "0scfg"; "0sigmask"; "0sp"]; ["0stdin"; "0uid"; "0urnd"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Lemma IT0_ok : ltac2:(TCodec.tc2 tcn__Ja0StartupFinalK "4&6&;&<%3221").
Proof. apply APSK.mk_itab_ranges_sound. Qed.
Section Final.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
Variables nofile sigmask : word. Variable abrt : bool. Variable urnd : InputStream.
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0.
Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
Variable T : Fs.Fs -> TSet.
Hypothesis T_nil : forall fs', T fs' [].
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation LIM := AsanInitK.LIMIT.
Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS_as0 SINV argH (HOLES T) fs.
Lemma J202_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupFinalK "G&5&;vM&:&1&7&2&9vOvLvCvBvDvQ1vH%9887654321&3%17:986543&=v@%211vE%F9EDCBA7521").
Proof.
intros h c Hh E R FULL model HC. unfold JS_as0_201 in Hh.
destruct (Nat.eqb_spec h 202) as [->|_]; [|discriminate Hh]. injection Hh as <-.
exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit IT0 IT0_ok HS_as0 T T_nil HS_sound KC0 BFUEL FUEL
planK_202 HS_202 shape_202 cert_202 eq_refl E R FULL model HC).
Qed.
Lemma J201_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupFinalK "G&5&;vM&:&1&8&2&9vOvLvCvBvDvQ1vH%9887654321&3%17:986543&=v@%211vE%F9EDCBA7521").
Proof.
intros h c Hh E R FULL model HC. unfold JS_as0_root in Hh.
destruct (Nat.eqb_spec h 201) as [->|_]; [|discriminate Hh]. injection Hh as <-.
exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit IT0 IT0_ok JS_as0_201 T T_nil J202_sound KC0 BFUEL FUEL
planK_201 HS_201 shape_201 cert_201 eq_refl E R FULL model HC).
Qed.
Theorem as0_startup_closed : ltac2:(TCodec.tc2 tcn__Ja0StartupFinalK "N'>&;vM&0&?&9vOvCvIvL&1&4vBvDvEvQ0vQ1vFvHvGvJvKvNvAvQ2%>==<;:987654321%G9IFEDCBA@1v@%11>%M4LK31").
Proof.
exact (as0_startup_hole_c scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd
Hsp Hbrk Hva Hve Hfit Huid Hhw IT0 IT0_ok JS_as0_root T T_nil J201_sound KC0 BFUEL FUEL
planK_root shape_root cert_root eq_refl).
Qed.
End Final.

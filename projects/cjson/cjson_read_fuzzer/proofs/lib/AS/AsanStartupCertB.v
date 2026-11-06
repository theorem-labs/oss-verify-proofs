(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanAcct.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanAcctImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3Sound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanCore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesIface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SumsAsanClose.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartXAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
Module AsanStartup.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.cjson.cjson_read_fuzzer.images.Asan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SpinAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcct OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcctImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3Sound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymRun3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesIface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SumsAsanClose OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartX OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartXAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma asan_maxva_code : forall i, (i < 45)%nat ->
  fetch_word ASEGS (Z_to_bv 64 (x_maxva ASAN + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva ASAN].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma asan_maxva_range : 0 < x_maxva ASAN /\ x_maxva ASAN + 180 < 2 ^ 64.
Proof. cbn [x_maxva ASAN]. lia. Qed.

(* [comment removed for export] *)
Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN nx0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 x.
  Proof.
    pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 APH sp rdraw argv envp uid hw E a = argH0 APH sp rdraw argv envp uid hw E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree APH sp rdraw argv envp uid hw). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemset nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemcpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    - apply (node_x_sound_XPnScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XPopFree nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva ASEGS ASAN nx0 AsanInit.LIMIT SINV _ FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame asan_maxva_range asan_maxva_code).
  Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN LIM HS_asan SINV argH HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN APH sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp Asan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hva Hve Hfit Huid Hhw nof sigm abt ifs urnd tmp Hfs) as HC.
    pose proof (check_sound ASEGS IT0 IT0_ok ASAN NX0 (le_n NX0) LIM HS_asan (XNS ASEGS ASAN NX0 LIM) XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF NX0 (le_n NX0) SA)
              (node_join_sound ASEGS ASAN NX0 LIM SINV argH fs)
              (XNS_sound ASEGS ASAN NX0 LIM SINV argH fs AA SA asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan asan_init startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    (* [comment removed for export] *)
    assert (EF : m_fs (model0 ASEGS sp brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp) = fs) by (rewrite Hfs; reflexivity).
    rewrite EF in R. exact R.
  Qed.
End Startup.
End AsanStartup.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHSAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertDefs.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module AsanStartupCert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges ASEGS [(0x30cb0, 20%nat); (0x37a50, 16%nat); (0x37b00, 12%nat); (0x38000, 36%nat); (0x380d0, 16%nat); (0x3d8e0, 880%nat); (0x3e6e0, 16%nat); (0x3e760, 36%nat); (0x3e810, 8%nat); (0x53130, 8%nat); (0x53810, 20%nat); (0x538e0, 24%nat); (0x53b00, 24%nat); (0x53c30, 28%nat); (0x5a580, 12%nat); (0x5ad10, 32%nat); (0x5b1d0, 48%nat); (0x5b6f0, 36%nat); (0x5bd20, 108%nat); (0x60050, 76%nat); (0x61840, 12%nat); (0x61ef0, 32%nat); (0x621a0, 44%nat); (0x63160, 88%nat); (0x635f0, 1208%nat); (0x64d70, 32%nat); (0x64e00, 32%nat); (0x64f00, 48%nat); (0x64fd0, 20%nat); (0x65080, 24%nat); (0x65160, 16%nat); (0x651c0, 68%nat); (0x65450, 20%nat); (0x654b0, 20%nat); (0x65790, 16%nat); (0x65800, 8%nat); (0x65970, 24%nat); (0x65bc0, 16%nat); (0x65c30, 36%nat); (0x66000, 20%nat); (0x662f0, 28%nat); (0x66e30, 80%nat); (0x676e0, 68%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6ef90, 8%nat); (0x7bde0, 272%nat); (0x7eca0, 12%nat); (0x81d30, 104%nat); (0x82530, 8%nat); (0x8d5c0, 32%nat); (0x8d660, 28%nat); (0x8d7c0, 96%nat); (0x8da00, 68%nat); (0x8dbe0, 100%nat); (0x8dd90, 97%nat); (0x9d864, 12%nat)]%Z.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_cert :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 HS_asanA KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
Proof. Time (vm_cert_refl constr:(COk startup_shape)). Time Qed.
End AsanStartupCert.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlan2Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHS2Asan.
Module AsanStartupCert2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Asan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHS2Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXS2 : nat := 453%nat.
Lemma NXS2_ge : (NX0 <= NXS2)%nat. Proof. unfold NX0, NXS2. lia. Qed.
(* [comment removed for export] *)
Definition startup2_shape : shape := SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (SHole 1) (SHole 2).
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup2_cert :
  check ASEGS IT2 ASAN NXS2 AsanInit.LIMIT (XNS ASEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 HS_asan2 KC0 BFUEL FUEL None HS_asanD_0 startup2_plan = COk startup2_shape.
Proof. Time (vm_cert_refl constr:(COk startup2_shape)). Time Qed.
End AsanStartupCert2.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin.
Import AsanStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlanAsan StartupHSAsan AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges ASEGS [(0x30df0, 20%nat); (0x30f90, 88%nat); (0x331b0, 16%nat); (0x33200, 12%nat); (0x332d0, 12%nat); (0x333e0, 12%nat); (0x33420, 36%nat); (0x33540, 52%nat); (0x33690, 12%nat); (0x336e0, 24%nat); (0x33780, 24%nat); (0x343c0, 28%nat); (0x344b0, 16%nat); (0x41840, 16%nat); (0x42520, 8%nat); (0x483e0, 40%nat); (0x49480, 12%nat); (0x494c0, 40%nat); (0x53050, 64%nat); (0x53810, 28%nat); (0x538a0, 20%nat); (0x539b0, 8%nat); (0x539f0, 16%nat); (0x54130, 12%nat); (0x54bd0, 8%nat); (0x55670, 44%nat); (0x557d0, 12%nat); (0x558a0, 36%nat); (0x559d0, 24%nat); (0x55b70, 32%nat); (0x55ff0, 80%nat); (0x56160, 20%nat); (0x56760, 20%nat); (0x567d0, 32%nat); (0x5b330, 48%nat); (0x5b490, 20%nat); (0x5b960, 12%nat); (0x5bf00, 40%nat); (0x5c180, 20%nat); (0x5ce50, 24%nat); (0x5d6f0, 8%nat); (0x5d880, 52%nat); (0x5d960, 44%nat); (0x5dc90, 12%nat); (0x5e130, 20%nat); (0x5e190, 16%nat); (0x5e520, 24%nat); (0x5e660, 32%nat); (0x5e770, 32%nat); (0x5f870, 48%nat); (0x5f980, 84%nat); (0x60050, 76%nat); (0x60230, 8%nat); (0x61ef0, 16%nat); (0x65790, 8%nat); (0x65d50, 8%nat); (0x66000, 20%nat); (0x66f50, 8%nat); (0x67270, 28%nat); (0x67490, 8%nat); (0x676e0, 68%nat); (0x67870, 32%nat); (0x67d30, 72%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6b2f0, 12%nat); (0x6b340, 12%nat); (0x6b3c0, 60%nat); (0x6b4c0, 12%nat); (0x6b580, 40%nat); (0x6b6a0, 24%nat); (0x6b950, 96%nat); (0x6bb20, 8%nat); (0x6bb60, 140%nat); (0x6be10, 16%nat); (0x6ca60, 52%nat); (0x6d310, 12%nat); (0x6d360, 8%nat); (0x6dc40, 40%nat); (0x6e420, 40%nat); (0x6e690, 8%nat); (0x6e6d0, 8%nat); (0x6e710, 20%nat); (0x6e810, 24%nat); (0x6ecc0, 8%nat); (0x6ef90, 120%nat); (0x6f4e0, 16%nat); (0x6f540, 8%nat); (0x6f5d0, 8%nat); (0x6f760, 44%nat); (0x6f860, 12%nat); (0x6fe70, 16%nat); (0x6fed0, 24%nat); (0x700c0, 12%nat); (0x718c0, 28%nat); (0x8d5c0, 32%nat); (0x8d660, 28%nat); (0x8d7c0, 12%nat); (0x8e0f4, 56%nat); (0x8e594, 88%nat); (0x8e704, 20%nat); (0x9b5e4, 8%nat); (0x9bb14, 8%nat); (0x9bd04, 8%nat); (0x9bd94, 12%nat); (0x9be34, 16%nat); (0x9cee4, 16%nat); (0x9d294, 60%nat); (0x9d604, 32%nat); (0x9d6a4, 24%nat); (0x9d7a4, 28%nat); (0x9d824, 20%nat)]%Z.
Lemma ITB_ok : itab_sound ASEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXB : nat := 208%nat.
Lemma NXB_ge : (NX0 <= NXB)%nat. Proof. unfold NX0, NXB. lia. Qed.
Definition startup_shapeB : shape := SHole 11.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certB :
  check ASEGS ITB ASAN NXB AsanInit.LIMIT (XNS ASEGS ASAN NXB AsanInit.LIMIT) XE0 XB0 HS_asanB KC0 BFUEL FUEL None HS_asanB1_13 startup_plan_segB1 = COk startup_shapeB.
Proof. Time (vm_cert_refl constr:(COk startup_shapeB)). Time Qed.

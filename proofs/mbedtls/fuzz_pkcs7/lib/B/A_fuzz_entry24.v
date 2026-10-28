(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib ATopContract A_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_top24 ATopContract24 A_fuzz_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_fuzz_entry24 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.P.P_pkcs7_top.pkcs7_zero"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.ATopContract.FUZZ_ENTRY"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Walk.Call.EPOST"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM5 : arl_smalloc R 5 = A_SMALLOC_5.
  Hypothesis SF5 : arl_sfree5 R = A_SFREE_5.
  Hypothesis E00 : arl_set00 R = A_SET00.
  Hypothesis EF8 : arl_setf8 R = A_SETF8.
  Hypothesis AMS : arl_amemset R = A_AMEMSET_F.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NS2 : 0 <= arl_need_setsh R.
  Hypothesis NS3 : 0 <= arl_need_amem R.
  (* [comment removed for export] *)
  Variable P7T : Type.
  Variable p7rep : P7T -> mem -> list blk -> list blk -> Z -> Prop.
  Variable SI : sinv (arl_L R).
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z) (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Variable C24p : Z.   (* [comment removed for export] *)
  Hypothesis PARSE : pkcs7_parse_der_stmtA24 asegs R HIA P7T p7rep SI PHIp FFRp CNTp STKp C24p A_PKCS7_PARSE_DER.
  Hypothesis FREE : pkcs7_free_stmtA24 asegs R HIA P7T p7rep PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis PHIp_nn : forall n, 0 <= n -> 0 <= PHIp n.
  Hypothesis FFRp_nn : forall n d, 0 <= n -> 0 <= FFRp n d.
  Hypothesis CNTp_nn : forall n, 0 <= n -> 0 <= CNTp n.
  Variable FSTK : Z.
  Hypothesis FSp : 112 + STKp <= FSTK.
  Hypothesis FSf : 112 + STKf <= FSTK.
  Hypothesis FS1 : 128 + arl_need_smalloc R <= FSTK.
  Hypothesis FS2 : 128 + arl_need_setsh R <= FSTK.
  Hypothesis FS3 : 128 + arl_need_amem R <= FSTK.

  Section Call.
  (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (DATA n lo slo : Z) (bs : list byte).
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2^26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CR : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis D47 : n = 0 \/ DATA + n + 8 <= 2 ^ 47.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - FSTK.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 32)%nat.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_5 in SM5;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Ltac call_setsh xx pclit EPC SP1 :=
    lazymatch goal with
    | SS : sshad _ _ ?mc _ _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | HHc : HM _ _ _ ?h1 ?LBc ((?FB, 2048) :: LF) mc, SP1R : 0 <= ?sp1 < 2^64, ESH : shadow_of _ (?FB + 32) = ?sv |- _ =>
        replace (Z_to_bv 64 pclit) with (Z_to_bv 64 (if Z.eqb xx 0 then arl_set00 R else if Z.eqb xx 0xf5 then arl_setf5 R else arl_setf8 R))
          by (cbn [Z.eqb Pos.eqb]; rewrite EPC; reflexivity);
        repeat match goal with P : presW _ _ _ _ _ _ _ _ _ _ mc |- _ => lazymatch type of P with ?t => change t with (hidden t) in P end end;
        let SPEC := fresh "SPEC" in
        pose proof (artA_set_shadow asegs R HIA xx) as SPEC;
        specialize SPEC with (h := h1);
        try (lazymatch goal with E : hcs _ _ _ h1 = _ |- _ => rewrite E in SPEC end);
        callrt sp1 (eapply SPEC with (LB := LBc) (LF := (FB, 2048) :: LF) (A := FB + 32) (s := sv) (n := 180) (lo := lo); clear SPEC;
                    rewrite ?(unsigned_lit sp1) by exact SP1R;
                    first [ exact HHc
                          | exact LOS
                          | reflexivity
                          | lazymatch goal with
                            | |- _ \/ _ \/ _ => first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]
                            | |- (FB + 32) mod 8 = 0 => assumption
                            | |- 0 < 180 => clear; lia
                            | |- crange _ (FB + 32) _ => match goal with C : crange _ FB 2048 |- _ => eapply crange_sub; [exact C| clear; lia| clear; lia] end
                            | |- _ = shadow_of _ _ => symmetry; exact ESH
                            | |- forall x, _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; right; exists (FB, 2048); split; [left; reflexivity| cbn; clear - Hx; lia]
                            | |- rw_cells _ mc _ _ => match goal with H : rw_cells _ mc (Z.shiftr FB 3 + al_sb _ + 4) _ |- _ =>
                                   lazymatch goal with SH4 : Z.shiftr (FB + 32) 3 = _ |- _ => rewrite SH4 end;
                                   replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) by (clear; lia); exact H end
                            | |- Z.of_nat _ = 180 => cbn; reflexivity
                            | |- stk _ mc lo _ => assumption
                            | |- lo <= _ => clear - FS2 SLO NS2 SP1; lia
                            | |- crange _ lo _ => match goal with C : crange _ lo (bv_unsigned sp - lo) |- _ => eapply crange_sub; [exact C| clear; lia| clear - SP1; lia] end
                            | |- mem_inv _ mc => assumption
                            end
                          | match goal with |- ?g => idtac "SETSH-PRE-LEFT:" g end ]);
        try clear SPEC
      end
    end.

  Ltac after_setsh SP1 :=
    lazymatch goal with
    | MU : munch [(?sv, _); (lo, ?hi)] ?ma ?mb, WM : wmono _ ?ma ?mb, ESH : shadow_of _ (?FB + 32) = ?sv |- evtA _ _ _ _ (MS _ _ _ _ _ ?mb _) =>
        let MU' := fresh "MU'" in pose proof MU as MU'; rewrite <- ESH in MU';
        repeat match goal with P : hidden (presW _ _ _ _ _ _ _ _ ?Wc ?mz ma) |- _ => unfold hidden in P;
          apply (presW_munch_sh R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) Wc mz ma mb (FB + 32) 180 lo hi) in P;
          [ | exact MU' | exact WM
            | match goal with C : crange _ FB 2048 |- _ => eapply crange_sub; [exact C| clear; lia| clear; lia] end
            | assumption
            | exact LOS | clear - SP1; lia | qlia | assumption ] end;
        lazymatch goal with SS : sshad _ _ ma _ _ |- _ =>
          apply (sshad_munch_sh R HIA h ma mb (FB + 32) 180 lo hi) in SS;
          [ | exact MU' | exact WM
            | match goal with C : crange _ (arl_stklo R) _ |- _ => eapply crange_sub; [exact C| clear - SLOS; lia| qlia] end
            | assumption
            | left; qlia
            | exact LOS ] end;
        clear MU';
        (* [comment removed for export] *)
        try (lazymatch goal with H : rw_cells _ ma (Z.shiftr FB 3 + al_sb _ + 4) _ |- _ => clear H end);
        try (lazymatch goal with H : stk _ ma lo _ |- _ => clear H end);
        transport_after_call asegs ma mb MU WM;
        try (lazymatch goal with H : mem_inv _ ma |- _ => clear H end);
        try (lazymatch goal with H : HM _ _ _ _ _ _ ma |- _ => clear H end);
        try (lazymatch goal with H : wmono _ _ mb |- _ => clear H end);
        clear MU WM;
        lazymatch goal with H : rw_cells _ mb (Z.shiftr (FB + 32) 3 + al_sb _) _ |- _ =>
          lazymatch goal with SH4 : Z.shiftr (FB + 32) 3 = _ |- _ => rewrite SH4 in H end;
          replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) in H by (clear; lia);
          change (Z.to_nat 180) with 180%nat in H; rename H into SHOBJ end;
        lazymatch goal with H : HM _ _ _ _ _ _ mb |- _ => rename H into HH1 end;
        lazymatch goal with H : stk _ mb lo _ |- _ => rename H into STC end;
        lazymatch goal with H : mem_inv _ mb |- _ => rename H into MI end
    end.


  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry24 ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La0,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)Ljw,(5.&40.)(1.(7.$8.)Lc1,(7.$8.)(1.(7.$8.)Lc3,(7.$8.)(9.(:.$0.R1:.(;.(<.(=.&40.+976<8.)(=.&40.R18.)Vgp,Vtp,R15.R14.R13.Vsp,(=.&40.R18.)R12.R11.R10.R?.R>.R=.R<.R;.(=.&40.R19.)(=.&40.Vn,)(=.&40.VDATA,)(=.&40.(>.(?.R19.+3.)(10.(11.VR,))))(=.&40.(>.R19.+20.))(=.&40.(>.(>.(?.R19.+3.)(10.(11.VR,)))+4.))(=.&40.R19.)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(=.&40.+976<8.)Vfc,(12.(5.&40.))R16.(13.$4.)))(9.(9.(14.(15.(16.&40.Vsp,)+70.)R18.)(14.R18.(15.(16.&40.Vsp,)+60.)))(9.(:.$2.(17.R18.+20.)=)(9.(18.$4.VR,VHIA,R17.VLB,(19.(1:.$2.$2.)(1;.$2.$2.R19.+800.)VLF,)R16.)(9.(:.P,$2.Sp(1<.$4.VR,VHIA,R17.)(1<.$4.VR,VHIA,Vh,))(9.(:.$2.(1=.$4.VR,VHIA,R17.)(1=.$4.VR,VHIA,Vh,))(9.(:.$2.(1>.$4.VR,VHIA,R17.)(1>.$4.VR,VHIA,Vh,))(9.(:.$2.(1?.$4.VR,VHIA,R17.)(1?.$4.VR,VHIA,Vh,))(9.(:.$2.(20.$4.VR,VHIA,R17.)(20.$4.VR,VHIA,Vh,))(9.(:.$2.(21.$4.VR,VHIA,R17.)(21.$4.VR,VHIA,Vh,))(9.Pmo,$22.(23.(24.$4.VR,VHIA,R18.R1.)(24.$4.VR,VHIA,Vh,R1.))(9.(:.$2.(17.R19.+40.)=)(9.(25.VR,VLB,VLF,R19.+800.)(9.(26.$4.R16.R19.(19.$8.(27.R6.)(19.$8.(27.R5.)(19.$8.(27.R4.)(28.$8.)))))(9.(29.$4.R16.(>.R19.+20.))(9.(26.$4.R16.(>.(?.R19.+3.)(10.(11.VR,)))R2.)(9.(:.$2:.(2;.R2.)#4.)(9.(26.$4.R16.(>.(>.(?.R19.+3.)(10.(11.VR,)))+4.)(19.$8.(2<.#;4.(2=.(5.&8.)(=.&8.=)#;4.))(28.$8.)))(9.(26.$4.R16.(>.(>.(?.R19.+3.)(10.(11.VR,)))+;8.)R1.)(9.(:.$2:.(2;.R1.)#48.)(9.(26.$4.R16.(>.(16.&40.Vsp,)-50.)(19.$8.(27.Vs8,)(19.$8.(27.Vs7,)(19.$8.(27.Vs6,)(19.$8.(27.Vs5,)(19.$8.(27.Vs4,)(19.$8.(27.Vs3,)(19.$8.(27.Vs2,)(19.$8.(27.Vs1,)(19.$8.(27.Vs0,)(19.$8.(27.Vra,)(28.$8.))))))))))))(9.(26.$4.R16.(>.R18.+8.)(19.$8.(27.R3.)(28.$8.)))(9.(2>.$4.R16.R18.(>.R18.+8.))(9.(2>.$4.R16.(>.R18.+10.)(>.(16.&40.Vsp,)-50.))(9.(2>.$4.R16.Vlo,R18.)(9.(2?.$4.R16.)(9.(30.$4.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(28.$31.)Vm,R16.)(32.$4.(11.VR,)R16.Vslo,(16.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="LOS LFB TPV SPH SPA TOP SLO SLOL SLOS bs FS3 FS2 FS1 FSTK NS3 NS2 NS1 AMS EF8 E00 SM5 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry24 ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(18.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2>.$4.Vm,Vlo,(16.&40.Vsp,))P,(32.$4.(11.VR,)Vm,Vslo,(16.&40.Vsp,))P,(2?.$4.Vm,)(33.$4.(11.VR,)(1<.$4.VR,VHIA,Vh,)$34.(;.(<.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(=.&40.VDATA,)(=.&40.Vn,)R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(=.&40.$35.)Vfc,(12.(5.&40.))Vm,(13.$4.)))")
(* [comment removed for export] *).
  Proof.
    (* [comment removed for export] *)
    exact (A_fuzz_entry.pro_walk R HIA IMG UARG SM5 E00 EF8 AMS NS1 NS2 NS3 FSTK FS1 FS2 FS3 h LB LF ra sp gp tp
             s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DATA n lo slo bs SLOS SLOL SLO TOP SPA SPH TPV LFB).
  Qed.
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LB3 : list blk) (m0 m2x : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry24 ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.(3.$4.VR,VHIA,)Lh4,(3.$4.VR,VHIA,)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(9.(:.$0.R11.(;.(<.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(=.&40.=)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(36.Vra,)Vfc,(12.(5.&40.))R10.(13.$4.)))(9.(2?.$4.R10.)(9.(2>.$4.R10.Vlo,(16.&40.Vsp,))(9.(32.$4.(11.VR,)R10.Vslo,(16.&40.Vsp,))(9.(30.$4.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(37.(38.VR,)VSI,)O2.R10.)(9.(30.$4.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(28.$31.)O1.R10.)(9.(:.P,$2.Sp(1<.$4.VR,VHIA,R?.)(1<.$4.VR,VHIA,O4.))(9.(:.$2.(1=.$4.VR,VHIA,R?.)(1=.$4.VR,VHIA,O4.))(9.(:.$2.(1>.$4.VR,VHIA,R?.)(1>.$4.VR,VHIA,O4.))(9.(:.$2.(1?.$4.VR,VHIA,R?.)(1?.$4.VR,VHIA,O4.))(9.(:.$2.(20.$4.VR,VHIA,R?.)(20.$4.VR,VHIA,O4.))(9.(:.$2.(21.$4.VR,VHIA,R?.)(21.$4.VR,VHIA,O4.))(9.Pmo,$22.(23.(24.$4.VR,VHIA,R10.R1.)(24.$4.VR,VHIA,O4.R1.))(18.$4.VR,VHIA,R?.O3.VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="LOS LFB SPH TOP SLO SLOL SLOS bs FS3 FS2 FS1 FSTK NS3 NS2 NS1 EF8 SF5 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry24 ()) "Ph3,(3.$4.VR,VHIA,)PLB3,(7.$39.)Pm0,P,(5.&40.)(6.(5.&8.))Pm2x,P,(5.&40.)(6.(5.&8.))Pmm,P,(5.&40.)(6.(5.&8.))PFB,$2.Psp1,$2.Pxra,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Pjw,(5.&40.)Pc1,(7.$8.)Pc3,(7.$8.)Posh,(7.(5.&8.))P,(18.$4.VR,VHIA,R1>.R1=.(19.(1:.$2.$2.)(1;.$2.$2.R19.+800.)VLF,)R1:.)P,Pb,$39.P,(3:.$39.R1.VLB,)(3:.$39.R2.R20.)P,Px,$2.P,(1<.$4.VR,VHIA,Vh,R1.)(1<.$4.VR,VHIA,R22.R2.)P,(:.$2.(1=.$4.VR,VHIA,R21.)(1=.$4.VR,VHIA,Vh,))P,(:.$2.(1>.$4.VR,VHIA,R22.)(1>.$4.VR,VHIA,Vh,))P,(9.(14.(15.(16.&40.Vsp,)+70.)R1=.)(14.R1=.(15.(16.&40.Vsp,)+60.)))P,(:.$2.(17.R1>.+20.)=)P,(:.$2.(17.R20.+40.)=)P,(25.VR,VLB,VLF,R21.+800.)P,(3;.(1<.$4.VR,VHIA,Vh,)R22.+800.)P,PB,$2.Pj,$2.P,(3:.(1:.$2.$2.)(1;.$2.$2.R2.R1.)VLF,)(3<.(14.(>.R26.+800.)R3.)(14.(>.R3.R2.)R26.))P,(26.$4.R25.R24.(19.$8.(27.R12.)(19.$8.(27.R11.)(19.$8.(27.R10.)(28.$8.)))))P,(26.$4.R26.(>.(?.R25.+3.)(10.(11.VR,)))R?.)P,(:.$2:.(2;.R10.)#4.)P,(26.$4.R28.(>.(>.(?.R27.+3.)(10.(11.VR,)))+4.)(19.$8.(2<.#;4.R?.)(28.$8.)))P,(26.$4.R29.(>.(>.(?.R28.+3.)(10.(11.VR,)))+;8.)R11.)P,(:.$2:.(2;.R12.)#48.)P,(26.$4.R2;.(>.(16.&40.Vsp,)-50.)(19.$8.(27.Vs8,)(19.$8.(27.Vs7,)(19.$8.(27.Vs6,)(19.$8.(27.Vs5,)(19.$8.(27.Vs4,)(19.$8.(27.Vs3,)(19.$8.(27.Vs2,)(19.$8.(27.Vs1,)(19.$8.(27.Vs0,)(19.$8.(27.Vra,)(28.$8.))))))))))))P,(26.$4.R2<.(>.R2:.+8.)(19.$8.(27.R16.)(28.$8.)))P,(2>.$4.R2=.R2;.(>.R2;.+8.))P,(2>.$4.R2>.(>.R2<.+10.)(>.(16.&40.Vsp,)-50.))P,(2>.$4.R2?.Vlo,R2=.)P,(2?.$4.R30.)P,(30.$4.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(37.(38.VR,)VSI,)R33.R31.)P,(30.$4.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(28.$31.)R33.R32.)P,(32.$4.(11.VR,)R33.Vslo,(16.&40.Vsp,))(33.$4.(11.VR,)(1<.$4.VR,VHIA,R38.)(3=.R38.R37.R36.R35.)(;.(<.R31.(=.&40.R32.)Vgp,Vtp,R30.R2?.R2>.Vsp,(=.&40.R32.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.(=.&40.R33.)(=.&40.Vn,)(=.&40.VDATA,)(=.&40.(>.(?.R33.+3.)(10.(11.VR,))))(=.&40.(>.R33.+20.))(=.&40.(>.(>.(?.R33.+3.)(10.(11.VR,)))+4.))(=.&40.R33.)Vs9,Vs10,Vs11,R25.R24.R23.R22.)VF,(=.&40.+976>0.)Vfc,(12.(5.&40.))R34.(13.$4.)))")
(* [comment removed for export] *).
  Proof.
    (* [comment removed for export] *)
    exact (A_fuzz_entry.epi_walk R HIA IMG SF5 EF8 NS1 NS2 NS3 SI FSTK FS1 FS2 FS3 h LB LF ra sp gp tp
             s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DATA n lo slo bs SLOS SLOL SLO TOP SPH LFB).
  Qed.

  End Call.

  Local Notation PHI := (A_fuzz_entry.PHI PHIp CNTp PHIf).
  Local Notation FFR := (A_fuzz_entry.FFR FFRp CNTp FFRf).

  Theorem fuzz_entryA24 : fuzz_entry_stmtA24 asegs R HIA SI PHI FSTK C24p FFR FUZZ_ENTRY.
  Proof.
    unfold fuzz_entry_stmtA24. intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo DATA n lo slo bs.
    intros HH HK0 BY LEN Hn HD CR OD DLO D47 ST SS SLOS SLOL SLO TOP SPA SPH MI TPV SIP BUD UW BUDF C24H LFB -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LOS : arl_stklo R <= lo) by (clear - SLOS SLOL; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO FS1 NS1 TOP HTOP; lia]).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (pro_walk h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DATA n lo slo bs);
        assumption. }
    intros ms1 P1. destruct P1 as (FB & sp1 & h1 & m1 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & w0 & w1 & w2 & jw & c1 & c3
                                 & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & P7Z & SHF1 & SZ1 & SHOBJ & SH3R & SZ3
                                 & SAVE & SLOT & STlo & SThi & ST1 & MI1 & PRES & SS1).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV FS1 NS1; lia).
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m1 FB 2048 HH1) as AP.
    assert (F8' : (FB + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (SH4 : Z.shiftr (FB + 32) 3 = Z.shiftr FB 3 + 4) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
    assert (INF : In (FB, 2048) ((FB, 2048) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA h1 LB _ m1 FB 2048 HH1 INF) as CFB. rewrite Ehcs in CFB.
    assert (IND : In (FB + 32, 2008) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    assert (INH : In (FB, 24) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES) as HP1.
    assert (CRsp : client_range L (LB ++ fdata LF) (bv_unsigned sp) DATA n) by (eapply client_range_raise; [exact CR| exact DLO]).
    assert (BY1 : bytes_at asegs m1 DATA bs).
    { eapply presA_bytes_at0; [exact HP1| exact BY|]. right. split; [rewrite LEN; exact CRsp| exact I]. }
    assert (OD1 : 1 <= n -> aobj asegs AL (hcs asegs R HIA h) m1 DATA n).
    { intros H1. eapply presA_aobj0; [exact CSOK| exact HP1| exact (OD H1)| intros x Hx; eapply hcs_below_top; exact Hx| right; split; [exact CRsp| clear; lia]]. }
    assert (SIP1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP1)| intros a _; exact I]. }
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) 0).
    { eapply uwc_presA; [exact HP1| exact UW| clear; lia| intros a _; exact I| clear - SPR; lia| apply hstkhi_le64].
      clear - LOS SLO SPR FS1 NS1; lia. }
    assert (UWF : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 1).
    { pose proof SAVE as SV. chunk_split SV 8%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      rewrite <- (Z_to_bv_bv_unsigned s0) in SV0.
      change 1 with (0 + 1). eapply uwc_frame; [clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| pose proof (bv_unsigned_in_range 64 s0) as XR; unfold bv_modulus in XR; cbn [Z.pow Z.of_N Pos.pow] in XR; exact XR| clear; lia| exact (proj1 SV0)| exact UW1]. }
    clear HP1 BY OD UW SIP.
    assert (OBJ1 : aobj asegs AL (hcs asegs R HIA h1) m1 (FB + 32) 1440).
    { rewrite Ehcs. change 1440 with (8 * Z.of_nat 180).
      eapply (aobj_of_zshadow asegs AL _ m1 (FB + 32) 180 CSOK); [| eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia].
      rewrite SH4. replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) by (clear; lia). exact SHOBJ. }
    assert (CW1 : client_wrange L (LB ++ fdata ((FB, 2048) :: LF)) lo (htop asegs R HIA h) (FB + 32) 1440).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    assert (CR1 : client_range L (LB ++ fdata ((FB, 2048) :: LF)) lo DATA n).
    { eapply client_range_incl; [exact CR| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    pose proof (fresh_apart_client0 R LB LF lo DATA n FB 2048 FRSH CR ltac:(clear - Hn; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APD.
    destruct (sshad_split asegs AL m1 slo sp1 (bv_unsigned sp) SS1 ltac:(clear - SP1 SLO SLOL FS1 NS1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    (* [comment removed for export] *)
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PARSE with (h := h1) (LB := LB) (LF := (FB, 2048) :: LF) (A := FB + 32) (DATA := DATA) (n := n) (bs := bs) (lo := lo) (slo := slo) (d := 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop, ?Estk, ?Evol, ?Efr; unfold PKCS7_SIZE;
        first [ exact C24H | exact HH1 | exact P7Z | exact F8' | exact OBJ1 | exact CW1 | exact BY1 | exact LEN | exact Hn | exact HD | exact CR1 | exact ST1 | exact SSlo | exact SLOS | exact MI1 | exact TPV | exact SIP1 | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- 0 < FB + 32 => clear - F0; lia
                | |- FB + 32 + _ <= arl_stklo R => clear - F1 ALO; lia
                | |- FB + 32 + _ <= hl_data_lo _ \/ _ => clear - F2; lia
                | |- 1 <= n -> _ => intros H1; rewrite Ehcs; exact (OD1 H1)
                | |- DATA + n <= lo \/ _ => clear - DLO SP1; lia
                | |- n = 0 \/ DATA + n + 8 <= _ => exact D47
                | |- n = 0 \/ _ => clear - APD; lia
                | |- slo <= lo => exact SLOL
                | |- lo <= sp1 - STKp => clear - SLO FSp SP1; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (PHIf_mono 0 (CNTp n) ltac:(split; [clear; lia| apply CNTp_nn; clear - Hn; lia])); unfold A_fuzz_entry.PHI in BUD; clear - BUD H; lia
                | |- uwc _ _ _ _ _ _ _ => exact UWF
                | |- hfr _ _ _ _ + _ <= FR_MAX => pose proof (FFRf_mono 0 (CNTp n) 0 ltac:(split; [clear; lia| apply CNTp_nn; clear - Hn; lia])); unfold A_fuzz_entry.FFR in BUDF; clear - BUDF H; lia
                | |- (length _ <= 33)%nat => cbn [length]; clear - LFB; lia
                end
              | match goal with |- ?g => idtac "PARSE-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 mo2 (mo1 & [HK1 MF1] & PO).
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & mo2' & h2 & st & LBn
                    & E2 & MI2 & ST2 & SS2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HCNT & REP2 & HH2 & SIP2 & C24n).
    injection E2 as Ems Emo. subst ms2 mo2.
    replace (ret_pc (Z_to_bv 64 620248)) with (Z_to_bv 64 620248 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, SS2, HP2 by exact SP1R.
    rewrite Ehtop in HT2. rewrite Estk in HS2, HP2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2. unfold PKCS7_SIZE in HP2.
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) (si_fp SI) m1 m2).
    { eapply (presA_drop_fresh_gen R LB LF sp1 sp1 _ (si_fp SI) FB 2048 (FB + 32) (FB + 32 + 1440) m1 m2); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO SP1 FS1 NS1; lia].
      eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (si_fp SI) m m2).
    { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]|].
      eapply presA_weaken; [exact HP2'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRES2 : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m2 m2).
    { split; [apply presA_refl| exact (proj2 PRES)]. }
    (* [comment removed for export] *)
    assert (SH184 : Z.shiftr (FB + 1472) 3 = Z.shiftr FB 3 + 184) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 2048 -> cshd R LBq ((FB, 2048) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 2048). split; [left; reflexivity| cbn; exact Hc]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 FB c1 CSOK) in SHF1;
      [| rewrite SZ1; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP2 | rewrite SZ1; intros c Hc; apply CSHD; clear - Hc; lia ].
    rewrite <- Z.add_assoc, (Z.add_comm (al_sb AL) 4), Z.add_assoc, <- SH4 in SHOBJ.
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 (FB + 32) [CB 180 (repeat (Z_to_bv 8 0) 180)] CSOK) in SHOBJ;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    rewrite <- Z.add_assoc, (Z.add_comm (al_sb AL) 184), Z.add_assoc, <- SH184 in SH3R.
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 (FB + 1472) c3 CSOK) in SH3R;
      [| rewrite SZ3; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP2 | rewrite SZ3; intros c Hc; apply CSHD; clear - Hc; lia ].
    (* [comment removed for export] *)
    apply (presA_rw_cells asegs R LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 FB _ HP2) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
       | cbn [cells_size csize Nat.add]; apply (proj2 (disjoint_from_app _ _ _ _)); split; [cbn; clear; lia| apply si_disjoint_off; clear - F2; lia] ].
    (* [comment removed for export] *)
    assert (UWF2 : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 1).
    { eapply uwc_presA; [exact HP2'| exact UWF| clear; lia| | clear - SP1R; lia| apply hstkhi_le64].
      intros a Ha. apply si_outside_above. pose proof (art_data_lo asegs R HIA). clear - Ha H ALO LOS SLO SP1 FS1 NS1. lia.
      clear - LOS SLO SPR FS1 NS1; lia. }
    clear UWF OBJ1 BY1 OD1 MI1 ST1 HH1 SSlo SS1 PRES.
    (* [comment removed for export] *)
    pose proof (art_data_lo asegs R HIA) as DLOW.
    assert (DJ : forall A k, sp1 <= A -> disjoint_from ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) A k).
    { intros A k HA. apply (proj2 (disjoint_from_app _ _ _ _)). split; [cbn; clear - HA F1 ALO LOS SLO FS1 NS1 SP1; lia|].
      apply si_disjoint_off. right. clear - HA DLOW ALO LOS SLO FS1 NS1 SP1. lia. }
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SLOT; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in STlo; [| clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SThi; [| clear; lia| apply DJ; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SShi; [| clear; lia| clear - HTOP TOP; lia].
    clear HP2 HP2' DJ.
    pose proof (sshad_merge asegs AL m2 slo sp1 (bv_unsigned sp) SS2 SShi ltac:(clear - SP1 SLOL SLO FS1 NS1; lia)) as SSm2. clear SS2 SShi.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear HK1 MF1 MF2 mo1 HK2.
    zstep. zstep.
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA h2) m2 (FB + 32) 1440).
    { change 1440 with (8 * Z.of_nat 180).
      eapply (aobj_of_zshadow asegs AL _ m2 (FB + 32) 180 (hcs_ok asegs R HIA h2)); [exact SHOBJ| | exact F8' | clear - F0; lia].
      eapply crange_mono; [exact HCS2|]. rewrite Ehcs. eapply crange_sub; [exact CFB| clear; lia| clear; lia]. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply FREE with (h := h2) (LB := LB) (LBn := LBn) (LF := (FB, 2048) :: LF) (A := FB + 32) (lo := lo) (d := 0) (st := st);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HT2, ?HS2; unfold PKCS7_SIZE;
        first [ exact HH2 | exact HK1 | exact REP2 | exact F8' | exact OBJ2 | exact CW1 | exact ST2 | exact LOS | exact MI2 | exact TPV | reflexivity
              | lazymatch goal with
                | |- 0 < FB + 32 => clear - F0; lia
                | |- FB + 32 + _ <= lo \/ _ => left; clear - F1 ALO LOS; lia
                | |- lo <= sp1 - STKf => clear - SLO FSf SP1; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX =>
                    pose proof (PHIf_mono (Z.of_nat (length LBn)) (CNTp n) ltac:(split; [clear; lia| exact HCNT])) as PM; unfold A_fuzz_entry.PHI in BUD; clear - BUD PM HV2; lia
                | |- uw_obj R _ _ _ => left; split; [clear - F1 ALO; unfold PKCS7_SIZE; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX =>
                    pose proof (FFRf_mono (Z.of_nat (length LBn)) (CNTp n) 0 ltac:(split; [clear; lia| exact HCNT])) as FM;
                    pose proof (FFRp_nn n 1 ltac:(clear - Hn; lia)) as FP; unfold A_fuzz_entry.FFR in BUDF; clear - BUDF FM FP HFR2; lia
                end
              | match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end ]. }
    cbv beta. intros ms3 mo3 (mo1 & [HK1 MF1] & PO).
    destruct PO as (u0' & u1' & u2' & va0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m3 & mo3' & h3 & LBx
                    & E3 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & ZERO3 & LENx & HH3 & C24x).
    injection E3 as Ems Emo. subst ms3 mo3.
    replace (ret_pc (Z_to_bv 64 620256)) with (Z_to_bv 64 620256 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    rewrite HT2 in HT3. rewrite HS2 in HS3, HP3. rewrite HF2 in HF3. unfold PKCS7_SIZE in HP3.
    assert (HP3' : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) [] m2 m3).
    { eapply (presA_drop_fresh_gen R LB LF sp1 (arl_stklo R) _ [] FB 2048 (FB + 32) (FB + 32 + 1440) m2 m3); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO SP1 FS1 NS1; lia].
      eapply presA_weaken; [exact HP3| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (si_fp SI) m m2 m3 LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) []) in PRESb;
      [| exact HP3' | intros b Hb; exact Hb | intros b Hb; exact Hb | clear - SP1; lia | clear - SLOS SLOL SLO FS1 NS1 LOS; lia | clear; lia | intros xo _; exact I ].
    apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m2 m2 m3 LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) []) in PRES2;
      [| exact HP3' | intros b Hb; exact Hb | intros b Hb; exact Hb | clear - SP1; lia | clear - SLOS SLOL SLO FS1 NS1 LOS; lia | clear; lia | intros xo _; exact I ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 FB c1 CSOK) in SHF1;
      [| rewrite SZ1; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | rewrite SZ1; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 (FB + 32) [CB 180 (repeat (Z_to_bv 8 0) 180)] CSOK) in SHOBJ;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 (FB + 1472) c3 CSOK) in SH3R;
      [| rewrite SZ3; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | rewrite SZ3; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 FB _ HP3) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SAVE; [| apply client_range_stack; clear - SP1; lia| exact I].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SLOT; [| apply client_range_stack; clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in STlo; [| clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SThi; [| clear; lia| exact I].
    apply (presA_sshad asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SSm2; [| exact SLOS| clear - HTOP TOP; lia].
    clear HP3 HP3' OBJ2 MI2 ST2 HH2 REP2.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    clear LAWS KINV HK1 MF1 MF3 mo1.
    rewrite SH4 in SHOBJ. replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) in SHOBJ by (clear; lia).
    rewrite SH184 in SH3R. replace (Z.shiftr FB 3 + 184 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 184) in SH3R by (clear; lia).
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3, HCS2; rewrite Ehcs; exact Hx).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo).
    { eapply (epi_walk h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DATA n lo slo bs
                SLOS SLOL SLO TOP SPH LFB h3 (LBx ++ LB) m m2 m3 FB sp1) with (c1 := c1) (c3 := c3);
        first [ exact HH3 | exact HCSh3 | exact HT3 | exact HS3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact AP | exact FHD
              | exact SHF1 | exact SZ1 | exact SHOBJ | exact SH3R | exact SZ3 | exact SAVE | exact SLOT | exact STlo | exact SThi | exact ST3 | exact MI3
              | exact PRESb | exact PRES2 | exact SSm2
              | intros b Hb; apply in_app_iff; right; exact Hb
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold fuzz_postA24.
    do 14 eexists. exists m9, mo9, h4, LBx.
    split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES9)|].
    split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
    split.
    { rewrite E4vol. pose proof (PHIf_mono (Z.of_nat (length LBn)) (CNTp n) ltac:(split; [clear; lia| exact HCNT])) as PM. unfold A_fuzz_entry.PHI. clear - HV3 HV2 PM. lia. }
    split.
    { rewrite E4fr. pose proof (FFRf_mono (Z.of_nat (length LBn)) (CNTp n) 0 ltac:(split; [clear; lia| exact HCNT])) as FM. unfold A_fuzz_entry.FFR. clear - HFR3 HFR2 FM. lia. }
    split; [exact HH4|].
    (* [comment removed for export] *)
    split; [eapply (si_heap_presx asegs L SI); [exact SIP2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES29))| intros a _; exact I]|].
    (* [comment removed for export] *)
    clear - C24x C24n. lia.
  Qed.

End Walk.

(* [comment removed for export] *)

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_montmul P_mpi_core_exp_mod_working_limbs P_mpi_core_exp_mod.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_rt_facts A_mpi_core_mla A_mpi_core_montmul A_mpi_core_exp_mod_stmtA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_core_exp_mod () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.htop"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.A.A_mpi_core_exp_mod_stmtA.mpi_core_exp_mod_postA"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "A_ASAN_MEMCPY_CE"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.A.A_mpi_core_montmul.A_ASAN_MEMSET_MM"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.mul"; "Walk.Loop.MINV"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.A.A_mpi_core_montmul.A_MPI_CORE_MONTMUL"; "Walk.Loop.NUMS"; "Walk.Loop.KBODY"; "Stdlib.ZArith.BinInt.Z.lor"; "Corelib.Lists.ListDef.skipn"; "Walk.Loop.PINV"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.P.P_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.LibA.ARt.arl_amemcpy"; "OSSVerify.KrLib.LibA.ARt.arl_need_amem"; "OSSVerify.KrLib.A.A_mpi_core_exp_mod_stmtA.mpi_core_exp_mod_stmtA"; "OSSVerify.KrLib.A.A_mpi_core_exp_mod_stmtA.A_MPI_CORE_EXP_MOD"].


Definition A_ASAN_MEMCPY_CE : Z := 0x67848.        (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Hypothesis MM : mpi_core_montmul_stmtA asegs R HIA A_MPI_CORE_MONTMUL.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A N an E en RR T lx la ln le_ lr lt lo : Z) (xs0 ys ns es rs ts0 : list word).
  Hypothesis Han : 1 <= an <= 4999.
  Hypothesis Hen : 1 <= en <= 10000.
  Hypothesis Ln : an <= lx /\ an <= la /\ an <= ln /\ en <= le_ /\ an <= lr /\ exp_mod_working_limbs an en <= lt.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LT0 : Z.of_nat (length ts0) = lt.
  Hypothesis DXT : X + 4 * lx <= T \/ T + 4 * lt <= X.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis TB : 0 < T /\ T + 4 * lt < 2^64.
  Hypothesis ALX : X mod 4 = 0. Hypothesis ALT : T mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - MPI_CORE_EXP_MOD_STACK_A - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis STT : T + 4 * lt <= lo \/ bv_unsigned sp <= T.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * an).
  Hypothesis CWT : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) T (4 * lt).
  (* [comment removed for export] *)
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LN : Z.of_nat (length ns) = ln.
  Hypothesis LE : Z.of_nat (length es) = le_.
  Hypothesis LR : Z.of_nat (length rs) = lr.
  Hypothesis DAT : locked (A + 4 * la <= T \/ T + 4 * lt <= A).
  Hypothesis DNT : locked (N + 4 * ln <= T \/ T + 4 * lt <= N).
  Hypothesis DET : locked (E + 4 * le_ <= T \/ T + 4 * lt <= E).
  Hypothesis DRT : locked (RR + 4 * lr <= T \/ T + 4 * lt <= RR).
  Hypothesis DNX : locked (N + 4 * ln <= X \/ X + 4 * lx <= N).
  Hypothesis DEX : locked (E + 4 * le_ <= X \/ X + 4 * lx <= E).
  Hypothesis ALA : A mod 4 = 0. Hypothesis ALN : N mod 4 = 0. Hypothesis ALE : E mod 4 = 0. Hypothesis ALR : RR mod 4 = 0.
  Hypothesis AB : 0 < A /\ A + 4 * la < 2^64.
  Hypothesis NB : 0 < N /\ N + 4 * ln < 2^64.
  Hypothesis EB : 0 < E /\ E + 4 * le_ < 2^64.
  Hypothesis RB : 0 < RR /\ RR + 4 * lr < 2^64.
  Hypothesis SA : locked (A + 4 * la <= lo \/ bv_unsigned sp <= A).
  Hypothesis SN : locked (N + 4 * ln <= lo \/ bv_unsigned sp <= N).
  Hypothesis SE : locked (E + 4 * le_ <= lo \/ bv_unsigned sp <= E).
  Hypothesis SRR : locked (RR + 4 * lr <= lo \/ bv_unsigned sp <= RR).
  Hypothesis HN0 : bytes_at asegs m N (u32s ns).
  Hypothesis HE0 : bytes_at asegs m E (u32s es).
  Hypothesis HR0 : bytes_at asegs m RR (u32s rs).
  Hypothesis HA0 : bytes_at asegs m A (u32s ys).
  Hypothesis OX0 : aobj asegs AL CS m X (4 * an).
  Hypothesis OA0 : aobj asegs AL CS m A (4 * an).
  Hypothesis ON0 : aobj asegs AL CS m N (4 * an).
  Hypothesis OE0 : aobj asegs AL CS m E (4 * en).
  Hypothesis OR0 : aobj asegs AL CS m RR (4 * an).
  (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_CE.
  Hypothesis T47A : A + 4 * an + 8 <= 2^47.

  Notation POST := (mpi_core_exp_mod_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X an T xs0 ts0 lo m).
  Notation W := [(X, X + 4 * an); (T, T + 4 * lt); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -176)).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L21480167967.16L29428324939.5 L30678931555.16L34239376546.16L35653441506.7 L44573860408.16L47354503799.16L59856652214.7 L60098763854.3 L7029671751.18500000<00N00T00d01<01L01\02602@036S1R2sp2lo2LOS1R2lo3LOS3ALO3ACPS1n2HnS2sp2lo3SRC1n2SSS1R3HIA1h2sp2lo3TOP4HTOPS2sp2lo3DST1n2SDS1R3HIA1h2sp3TOPS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ds2ss3RET3RRg". (* [comment removed for export] *)
    #[using="IMG NEED0 A N E RR ys ns es rs SPR LOS LO TOP AMC"] Lemma amemcpy_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PDST,$0.PSRC,$0.Pn,$0.Pds,(1.(2.&8.))Pss,(1.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PRET,$0.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys2,(2.&40.)Pys3,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(4.$5.VR,VHIA,Vh,VLB,VLF,R1;.)P,(6.$5.R1<.R21.R1>.)P,(7.$5.R1=.R21.R1>.)P,(8.$0.(9.(:.(2.&8.)R20.))R21.)P,(8.$0.(9.(:.(2.&8.)R20.))R22.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R20.R25.R23.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R21.R25.R24.)P,(>.(?.(10.R27.R25.)R26.)(?.(10.R26.R25.)R27.))P,(11.$5.R23.Vlo,(10.(12.&40.Vsp,)-;0.))P,(13.$5.R24.)P,(>.(?.(10.R2:.R28.)Vlo,)(?.(12.&40.Vsp,)R2:.))P,(>.(?.(10.R2:.R29.)Vlo,)(?.(12.&40.Vsp,)R2:.))P,(?.(10.(10.R2<.R2:.)+8.)(14.+2.+2?.))P,(?.(10.(10.R2<.R2;.)+8.)(14.+2.+2?.))P,(15.(16.=R2<.)(16.R2<.(14.+2.+28.)))P,(17.(18.VR,)(19.$1:.VLB,(1;.VLF,))(1<.VR,)(1=.$5.VR,VHIA,Vh,)R2?.R2=.)P,(8.(2.&40.)R29.(1>.&40.R2:.))P,(8.$0.(1?.R2;.+2.)=)P,(15.(?.=R2<.)(16.R2<.(14.+2.+40.)))P,Pmm',P,(2.&40.)(3.(2.&8.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(20.(21.(22.$0.$0.)(23.$0.$0.R43.(10.R43.R41.))(21.(22.$0.$0.)(23.$0.$0.Vlo,(10.(12.&40.Vsp,)-;0.))(24.(22.$0.$0.))))R3>.R10.)P,(25.$5.R3?.R11.)P,(13.$5.R12.)P,(6.$5.R13.R46.R42.)P,(11.$5.R14.Vlo,(10.(12.&40.Vsp,)-;0.))P,(4.$5.VR,VHIA,Vh,VLB,VLF,R15.)(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R42.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R15.R14.R13.R3>.R3=.R12.R11.R10.R?.R>.R=.R<.R;.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R:.R9.R8.R7.)VF,(1>.&40.R43.)Vfc,(2:.(2.&40.))R16.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R2=.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R2<.R2;.R2:.R29.R28.(1>.&40.R34.)(1>.&40.R33.)(1>.&40.R32.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)VF,(1>.&40.$2<.)Vfc,(2:.(2.&40.))R2?.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH HD HS LD LS OD OS DJ ST MI SD SS TD TS Hn CWD -> RE RRg K. rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CE) as SPC.
      eapply evtA_cut.
      { eapply SPC with (h := h) (LB := LB) (LF := LF) (DST := DST) (SRC := SRC) (n := n) (lo := lo) (ds := ds) (ss := ss);
          rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia);
          first [ exact HH | exact HD | exact HS | exact LD | exact LS | exact OD | exact OS | exact ST | exact MI | exact LOS | exact CWD | reflexivity
                | left; symmetry; exact AMC
                | right; exact DJ | right; exact TD | right; exact TS
                | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
                | clear - SD SS LO NEED0 SPR LO0 TOP Hn; lia
                | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]. }
      unfold call_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia).
      intros ms' PO.
      ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & -> & MUc & WMc & MIc & _ & HDc & STc & HHc).
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      eapply (K m2); assumption.
      all: match goal with |- ?g => idtac "MEMCPY-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L21480167967.14L29428324939.5 L30678931555.14L35653441506.7 L44573860408.14L47354503799.14L57017963659.14L59856652214.7 L60098763854.3 L7029671751.17700000<00N00T00l01<01L01M01g02102dS1R2sp2lo2LOS1R2lo3LOS3ALO3ACPS1n2HnS1R3HIA1h2sp2lo3TOP4HTOPS2sp2lo3DST1n2SDS1R3HIA1h2sp3TOPSS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ds3RET3RRg". (* [comment removed for export] *)
  #[using="IMG NEED0 A N E RR ys ns es rs SPR LOS LO TOP AMS"] Lemma amemset_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PDST,$0.Pn,$0.Pds,(1.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PRET,$0.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys2,(2.&40.)Pys3,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(4.$5.VR,VHIA,Vh,VLB,VLF,R1;.)P,(6.$5.R1<.R1?.R1=.)P,(8.$0.(9.(:.(2.&8.)R1>.))R1?.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R1>.R21.R20.)P,(11.$5.R1?.Vlo,(10.(12.&40.Vsp,)-;0.))P,(13.$5.R20.)P,(>.(?.(10.R24.R23.)Vlo,)(?.(12.&40.Vsp,)R24.))P,(?.(10.(10.R25.R24.)+8.)(14.+2.+2?.))P,(15.(16.=R25.)(16.R25.(14.+2.+28.)))P,(17.(18.VR,)(19.$1:.VLB,(1;.VLF,))(1<.VR,)(1=.$5.VR,VHIA,Vh,)R27.R26.)P,(8.(2.&40.)R23.(1>.&40.R24.))P,(8.$0.(1?.R25.+2.)=)P,(15.(?.=R26.)(16.R26.(14.+2.+40.)))P,Pmm',P,(2.&40.)(3.(2.&8.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(20.(21.(22.$0.$0.)(23.$0.$0.R3;.(10.R3;.R3:.))(21.(22.$0.$0.)(23.$0.$0.Vlo,(10.(12.&40.Vsp,)-;0.))(24.(22.$0.$0.))))R38.R10.)P,(25.$5.R39.R11.)P,(13.$5.R12.)P,(6.$5.R13.R3>.(2=.(2.&8.)(1>.&8.=)(2>.R3=.)))P,(11.$5.R14.Vlo,(10.(12.&40.Vsp,)-;0.))P,(4.$5.VR,VHIA,Vh,VLB,VLF,R15.)(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R3<.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R15.R14.R13.R38.R37.R12.R11.R10.R?.R>.R=.R<.R;.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R:.R9.R8.R7.)VF,(1>.&40.R3=.)Vfc,(2:.(2.&40.))R16.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R27.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R26.R25.R24.R23.R22.(1>.&40.R2<.)(1>.&40.=)(1>.&40.R2;.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)VF,(1>.&40.$2?.)Vfc,(2:.(2.&40.))R29.(2;.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HD LD OD ST MI SD TD Hn CWD -> RE RRg K. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_MM) as SPC.
    eapply evtA_cut.
    { eapply SPC with (h := h) (LB := LB) (LF := LF) (DST := DST) (v := 0) (n := n) (lo := lo) (ds := ds);
        rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia);
        first [ exact HH | exact HD | exact LD | exact OD | exact ST | exact MI | exact LOS | exact CWD | reflexivity
              | left; symmetry; exact AMS
              | right; exact TD
              | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
              | clear - SD LO NEED0 SPR LO0 TOP Hn; lia
              | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]. }
    unfold call_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia).
    intros ms' PO.
    ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & -> & MUc & WMc & MIc & _ & HDc & STc & HHc).
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
    eapply (K m2); assumption.
    all: match goal with |- ?g => idtac "MEMSET-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Loop.
    Variables (ws welem : Z) (wmm : word) (tl : list word).
    Hypothesis HWS : (ws = 1 /\ welem = 2) \/ (ws = 3 /\ welem = 8).
    Hypothesis HWL : welem * an + an + (2 * an + 1) <= lt.
    Hypothesis LTL : Z.of_nat (length tl) = lt - (welem * an + an + (2 * an + 1)).

    Notation SEL := (T + 4 * (welem * an)).
    Notation TMP := (T + 4 * (welem * an + an)).
    Notation TLA := (T + 4 * (welem * an + an + (2 * an + 1))).
    Notation WLN := (welem * an + an + (2 * an + 1)).
    Hypothesis OTL : aobj asegs AL CS m T (4 * WLN).
    (* [comment removed for export] *)
    Notation WT := [(X, X + 4 * an); (T, T + 4 * WLN); (lo, bv_unsigned sp)].
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L28573892092.1000000PS2sp1X2an1T2lt2lo5welem3HWL1x2Hx". (* [comment removed for export] *)
    Lemma sub_WT_W : sub_fp WT W.
    Proof using HWL. intros x Hx. cbn [outside] in *. clear - Hx HWL. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation FRAMEL mm := (rw_cells asegs mm (bv_unsigned sp + -176)
       [C8 (Z_to_bv 64 0x2a2a2a2a); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 ws);
        C8 (Z_to_bv 64 TMP); C8 (Z_to_bv 64 X); C8 wmm; C8 (Z_to_bv 64 N);
        C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    (* [comment removed for export] *)
    Definition MINV (mm : mem) (xs tab sel tmp : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "(15.(30.$5.O5.VX,O4.)(15.(8.$0.(9.(:.(2.&40.)O4.))Vlx,)(15.(31.(2.&40.)(2>.Van,)O4.Vxs0,)(15.(30.$5.O5.VT,O3.)(15.(8.$0.(9.(:.(2.&40.)O3.))(32.Vwelem,Van,))(15.(30.$5.O5.(10.VT,(32.+4.(32.Vwelem,Van,)))O2.)(15.(8.$0.(9.(:.(2.&40.)O2.))Van,)(15.(30.$5.O5.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))O1.)(15.(8.$0.(9.(:.(2.&40.)O1.))(10.(32.+2.Van,)+1.))(15.(30.$5.O5.(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))Vtl,)(15.(20.(21.(22.$0.$0.)(23.$0.$0.VX,(10.VX,(32.+4.Van,)))(21.(22.$0.$0.)(23.$0.$0.VT,(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(12.&40.Vsp,))(24.(22.$0.$0.)))))Vm,O5.)(15.(25.$5.Vm,O5.)(15.(13.$5.O5.)(15.(11.$5.O5.Vlo,(10.(12.&40.Vsp,)-;0.))(4.$5.VR,VHIA,Vh,VLB,VLF,O5.)))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L35735384464.5 L39077525840.13L53429205430.9 L57540516048.7 00000D01601X023S2an1T5welem3tab3LTBS2an2lt3ts03LT05welem2tl3LTL3tab3sel3tmp3LTB2LS2LMS2an1T5welem3tab3sel3tmp3LTB2LS2LMS2an1T5welem3tab3sel3LTB2LS". (* [comment removed for export] *)
    #[using="lt LT0 LTL"] Lemma join_T : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))P,(33.R5.R4.R3.R2.R1.)(15.(30.$5.R6.VT,(19.(2.&40.)R4.(19.(2.&40.)R3.(19.(2.&40.)R2.Vtl,))))(8.$34.(:.(2.&40.)(19.(2.&40.)R4.(19.(2.&40.)R3.(19.(2.&40.)R2.Vtl,))))(:.(2.&40.)Vts0,)))")
(* [comment removed for export] *).
    Proof.
      (intros mm xs tab sel tmp dd_H; ddestruct dd_H as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & _)).
      split.
      - apply u32arr_app. split; [exact HT|]. apply u32arr_app. split.
        { replace (T + 4 * Z.of_nat (length tab)) with SEL by (clear - LTB; lia). exact HS. }
        apply u32arr_app. split.
        { replace (T + 4 * Z.of_nat (length tab) + 4 * Z.of_nat (length sel)) with TMP by (clear - LTB LS; lia). exact HMm. }
        replace (T + 4 * Z.of_nat (length tab) + 4 * Z.of_nat (length sel) + 4 * Z.of_nat (length tmp)) with TLA by (clear - LTB LS LM; lia). exact HL.
      - rewrite !length_app. clear - LTB LS LM LTL LT0. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L13496871640.161L14401364312.161L1740955736.161 L17566313688.161L29428324939.5  L30238256600.161L31144453208.161L312739461.164  L34316152792.161L35653441506.7  L46968692952.161L49641679704.161L53719510360.161L57166284943.5  L60098763854.3  L63718073304.161L64238095896.163L66374151768.161L67937894104.161Q15641568614.164Q18364007270.164Q18376347397.164Q21877861637.164Q24387680389.164Q27583156582.164Q27904925317.164Q29503565670.164Q30413285893.164Q31269115878.164Q32653586022.164Q33915848709.164Q36423571333.164Q3832210565.164 Q39941338501.164Q41154176102.164Q44650594790.164Q4531767910.164 Q51233520870.164Q52099386854.164Q54488095749.164Q59254978790.164Q59840699110.164Q60513700229.164Q66523986693.164Q9840924165.164 00000m01j02g03d04605306007d08a0990:60;30<00<A0<K0=H0>E0?B0@?0@o0A_0BZ0CU0DP0E@0F;0Fk0Gf0HV0IF0JA0K<0L70M20Mb0NR0OB0P20Pb0Q]0RM0S=0T80U30UnS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2LO2AB2NB2EB2RB2tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2lx3xs02L02xs2LXS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LT". (* [comment removed for export] *)
    #[using="IMG NEED0 A RR la ln le_ lr lt ys ns es rs L0 LT0 XB TB SPR LOS LO TOP AB NB EB RB HWL LTL"] Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys2,(2.&40.)Pys3,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(33.R21.R20.R1?.R1>.R1=.)P,(35.$5.R22.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1>.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)VF,(1>.&40.+:6618.)Vfc,(2:.(2.&40.))R23.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros MV FR. pose proof (join_T _ _ _ _ _ MV) as [HT LT].
      ddestruct MV as (HX & LX & FX & _ & _ & _ & _ & _ & _ & _ & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      apply evtA_done. unfold mpi_core_exp_mod_postA. deexists 15. dexists mm, xs, (tab ++ sel ++ tmp ++ tl).
      split; [reflexivity|]. split; [rewrite LT0; exact (munch_weaken _ _ _ _ sub_WT_W MU)|]. split; [exact WM|]. split; [exact MI|]. split; [exact HX|].
      split; [clear - LX L0; lia|]. split; [apply same_from_skipn; [exact FX| clear - LX L0; lia]|]. split; [exact HT|]. split; [exact LT|]. split; [exact ST| exact HH].
      all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L29428324939.5L35653441506.7L37824102549.2L48155834837.3L60098763854.300000B00Z00`00l016S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1X2anS2an1T5welemS1R2lo3LOS". (* [comment removed for export] *)
    #[using="IMG LOS TOP OX0 ON0 OE0 OTL"] Lemma objs_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))P,(33.R5.R4.R3.R2.R1.)(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VX,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VN,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VE,(32.+4.Ven,))(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))))")
(* [comment removed for export] *).
    Proof.
      intros mm xs tab sel tmp MV.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (WC : w_client CS WT).
      { unfold w_client. repeat apply Forall_cons; cbn [fst snd]; [| | | apply Forall_nil].
        - replace (X + 4 * an - X) with (4 * an) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OX0).
        - replace (T + 4 * WLN - T) with (4 * WLN) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OTL).
        - exact SCS. }
      repeat split; eapply (aobj_munch asegs AL _ CSOK WT m mm); first [exact WC | exact MU | eassumption].
      all: match goal with |- ?g => idtac "OBJS-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Notation SB := (Z_to_bv 64 (al_sb AL)).
    Notation WL := (welem * an + an + (2 * an + 1)).
    (* [comment removed for export] *)
    Notation OBJT mm := (aobj asegs AL CS mm T (4 * WL)).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01;0@C33844532175.195C68255727078.194D36604751191.194D39932794823.194K11096861071.195K40484668124.194K42587433812.194K60443225391.195L10354034516.173L11102774801.5  L13043732721.173L17307733061.193L21921278833.193L23499095854.193L25607057439.170L25607152124.173L29428324939.5  L29519831493.173L35653441506.7  L40500120010.5  L42591480661.6  L44833485463.178L45272713316.181L52067443989.189L53112739003.193L59308546259.177L59308546259.180L60098763854.3  L60433113777.5  L60437718071.5  L60437798955.5  L62150255192.193L65067422056.189L65069863792.190L67221579272.191L68117358405.193L8929111654.172 L8929159528.177 L8929159528.179 P60443225391.195Q12691416109.174Q17595481517.177Q17595481517.180Q17595627449.174Q26295627581.177Q26295627581.181Q26295627581.183Q26602720822.177Q2958501345.192 Q2964842857.181 Q2964842857.183 Q30206126178.194Q3286077752.181 Q3286077752.183 Q36264016123.178Q36266672818.180Q36592349486.181Q36592349486.183Q36592448935.182Q36593012627.180Q36594532142.190Q36594546138.178Q36607027031.194Q46928622045.194Q46939464493.182Q46941546916.190Q47041869982.180Q49698585326.193Q50458135125.177Q50458135125.181Q50458135125.183Q53809516298.177Q8943722419.174 Q8944085786.180 Q8945570131.178 00000100202004105U06X0830960:E0:F0;U0><0?K0@U0B[0Da0E30F;0FS0FT0FU0IA0JH0L=0MA0P00RZ0Rd0Re0Rf0Rg0T10VD0XW0Zn0\40^70`:0b=0b>0cC0dD0eE0fF0g70gh0hY0i^0je0kl0m30nC0oC10C11C12C13D14E15F16G17H18I19M1:P1;P1<P1=U1>_1?T1@M1AF1BM1C>1Co1D`FFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42AWS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1j2xs3tab3sel3tmp2Hk2Hj2v4S1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v43LTBS1X2an1T2lx2lt3xs02ys2ns2es2rs3ts03Han3DXT5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42LX2AWS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2HiFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2HiS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1j2xs3tab3tmp2Hk2Hj3LTB3ws02LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3tmp2Hk2Hi3ws0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3tmp2Hk2Hj3ws02K1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2LS2AWS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2LS2AWS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl1k1j2xs3tab3sel3tmp2HkS1R3HIA1h2sp2lo3TOP4HTOPFFS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i1j2xs3tab3sel3tmp2Hk2Hj2Hi3LTB2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2Hk2HjS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB4T47A2tl1k1j2xs3tab3tmp2Hk2Hj3ws0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3tmp2Hk3ws0S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i1j2xs3tab3sel3tmp2Hk2Hj3LTB2LS2AW2N0S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1j2xs3tab3sel3tmp2Hk2Hj3LTB2LS2N0S1R2lo3LOSFFFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3tmp2Hk3ws0S1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3tmp2Hk3ws0S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWFS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T2lt3xs02ys2ns2es2rs3ts02TB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T2lt3xs02ys2ns2es2rs3ts02TB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T2lt3xs02ys2ns2es2rs3ts02TB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2sp1X2an1T2lo3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42AWS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42AWS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v4S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an1T2lt3xs02ys2ns2es2rs3ts03Han2TB5welem2tl3LTL1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2HkS2an1T2lt3xs02ys2ns2es2rs3ts02TB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2AWS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2Hk". (* [comment removed for export] *)
    #[using="IMG NEED0 A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB SPR LOS LO TOP SX STT CWT AB NB EB RB T47A HWS LTL"] Lemma ct_inner_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pk,$34.Pi,$0.Pj,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pys2,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwpt,(2.&40.)Pwps,(2.&40.)Pwcnt,(2.&40.)P,(8.$34.(2>.(38.Van,R1?.))R21.)P,(15.(?.=R20.)(16.R20.Van,))P,(15.(?.=R22.)(16.R22.Vwelem,))P,(8.(2.&40.)R6.(1>.&40.(10.VT,(32.+4.(10.(32.Van,R23.)R22.)))))P,(8.(2.&40.)R6.(1>.&40.(10.(10.VT,(32.+4.(32.Vwelem,Van,)))(32.+4.R23.))))P,(8.(2.&40.)R6.(1>.&40.(38.Van,R24.)))P,(33.R24.R23.R22.R21.R20.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R25.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))P,(35.$5.R26.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))P,Pmm',P,(2.&40.)(3.(2.&8.))Psel',(1.(2.&40.))Pya0,(2.&40.)Pya1,(2.&40.)Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)Pys5',(2.&40.)P,(33.R<.R32.R31.R;.R2?.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R=.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))P,(35.$5.R>.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R31.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R;.R:.R9.R2:.R29.R=.R<.R30.R2?.R2>.R2=.R2<.R2;.R28.(1>.&40.(39.(<.VR,)))R27.R4.R25.R24.R23.R22.R21.R20.R8.R7.R6.R5.)VF,(1>.&40.+:651<.)Vfc,(2:.(2.&40.))R?.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R23.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R=.R<.R;.R1<.R1;.R<.R=.R22.R21.R20.R1?.R1>.R1=.R1:.(1>.&40.(39.(<.VR,)))R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)VF,(1>.&40.+:656<.)Vfc,(2:.(2.&40.))R28.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i j mm xs tab sel tmp xra xa2 xa3 xa4 xa5 xa6 xa7 ys0 ys1 ys2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 wpt wps wcnt Hk Hj Hi -> -> -> MV OT FR KO; [lia|].
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AW : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OT (T + 4 * (an * i + j)) 4.
      (* [comment removed for export] *)
      zstep. zstep.
      prd HT (an * i + j) RDw.
      shadow_chk OT (SEL + 4 * j) 4.
      try clear RDw.
      (* [comment removed for export] *)
      rd HS j. vstep 31%positive.
      shadow_chk OT (SEL + 4 * j) 4.
      (* [comment removed for export] *)
      vstep 30%positive. vstep 31%positive. zstep. zstep. zstep. vstep 30%positive. vstep 29%positive. vstep 28%positive. vstep 28%positive.
      assert (FS : same_from (length sel) sel sel) by (apply same_from_refl).
      (* [comment removed for export] *)
      wr HS LS FS j.
      zstep. zstep.
      lazymatch goal with H6 : mem_inv asegs ?m2, H7 : stk asegs ?m2 lo _, H8 : HM _ _ _ h LB LF ?m2 |- _ =>
        lazymatch type of HS with u32arr _ _ _ ?sel2 =>
        assert (MV2 : MINV m2 xs tab sel2 tmp)
          by (refine (conj HX (conj LX (conj FX (conj HT (conj LTB (conj HS (conj LS (conj HMm (conj LM (conj HL (conj MU (conj WM (conj H6 (conj H7 H8))))))))))))))) end end.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - eapply (IH i (j + 1)); [lia | lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact MV2 | assumption | exact FR | exact KO].
      - (* [comment removed for export] *)
        zstep. eapply KO; [exact MV2 | assumption | exact FR].
      all: match goal with |- ?g => idtac "INNER-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L10354034516.168L12276447763.205L13043732721.168L16321291844.178L21920704885.178L22458920676.201L25607144757.168L28084690364.205L29428324939.5  L29519831493.168L35518900524.178L35653441506.7  L35732324389.178L3727711704.178 L48773092840.201L51989835922.167L54429812235.205L59308628179.171L59308628304.7  L60098763854.3  L62530280414.17800001:03k05506?07I09V0;Z0=60=H0>V0AA0AY0Bc0Cm0F30GA0HP0Ia0J90JC0KQS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB4sel'3LS'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW4sel'3LS'2K2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2Hi2K04sel'2K2S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB2LSS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW4sel'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk4sel'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2K0S2an1T3Han5welem1i2AW2K1S1R2lo3LOSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk". (* [comment removed for export] *)
    #[using="IMG NEED0 A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB SPR LOS LO TOP SX STT CWT AB NB EB RB T47A HWS LTL"] Lemma ct_outer_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pk,$34.Pi,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys1,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwi,(2.&40.)Pwpa,(2.&40.)P,(8.$34.(2>.(38.Vwelem,R1;.))R1<.)P,(15.(?.=R1<.)(16.R1<.Vwelem,))P,(8.(2.&40.)R4.(1>.&40.R1=.))P,(8.(2.&40.)R4.(1>.&40.(10.VT,(32.+4.(32.Van,R1>.)))))P,(33.R1>.R1=.R1<.R1;.R1:.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R1?.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))P,(35.$5.R20.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))P,Pmm',P,(2.&40.)(3.(2.&8.))Psel',(1.(2.&40.))Pya0,(2.&40.)Pya1,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)Pys5',(2.&40.)P,(33.R11.R31.R30.R10.R2>.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R12.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))P,(35.$5.R13.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R30.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R;.R:.R9.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R27.R12.R11.R2:.R10.R?.R>.R=.R<.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)R4.R25.(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R24.R23.R22.R8.R7.R6.R5.)VF,(1>.&40.+:6444.)Vfc,(2:.(2.&40.))R14.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1=.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R1<.R1;.R1:.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R14.R19.R18.R17.R:.R9.R9.R16.R15.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)R13.R12.(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R11.R10.R?.R>.R=.R<.R;.)VF,(1>.&40.+:652<.)Vfc,(2:.(2.&40.))R22.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i mm xs tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa2 xa6 xa7 ys1 ys5 ys6 ys9 ys10 ys11 xt3 xt4 xt5 xt6 wi wpa Hk Hi -> -> MV OT FR KM; [lia|].
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AW : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      (* [comment removed for export] *)
      zstep. zstep. vstep 10%positive.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [exfalso; lia|].
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; clear - K1 AW Han; lia|].
      (* [comment removed for export] *)
      vstep 11%positive. vstep 10%positive. vstep 10%positive. vstep 16%positive. vstep 10%positive. vstep 17%positive.
      zstep. zstep. zstep. zstep. zstep.
      eapply (ct_inner_walk (Z.to_nat an) i 0); [lia | lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact MV | exact OT | exact FR |].
      intros mm' sel' ya0 ya1 yt0 yt1 yt2 yt3 yt4 yt5 yt6 ys5' MV' OT' FR'.
      dpose MV' as (HX' & _ & _ & HT' & _ & HS' & LS' & HM' & _ & HL' & MU' & WM' & MI' & ST' & HH').
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      - eapply KM; [exact MV' | exact OT' | exact FR'].
      - eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | exact MV' | exact OT' | exact FR' | exact KM].
      all: match goal with |- ?g => idtac "OUTER-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "02>0@C13335976522.209C17025492443.208C40241445883.209C40241445883.210C45137625611.209C45137625611.212C45137625611.214D17582764468.212D51233741152.212D5472627854.212 D54966761497.212D60109446735.212D64311484648.212K11554254328.209K15588900467.208K19288291295.209K22393452675.209K22393452675.210K22842297120.208K34973782379.210K40247853644.208K42475897931.210K49644543183.209K49644543183.212K49644543183.214K50513409450.209K50513409450.210K52452886502.210K55676933043.211K55676933043.213K61705120587.209K61765368544.210K65354691088.209K68505827192.210L11547375246.4  L14220071842.6  L15601019926.4  L17597577141.6  L17737826157.39 L17738133748.28 L19281407145.4  L22381454459.6  L22382916926.39 L22383426215.25 L22383436283.6  L22838958405.2  L23272070152.39 L23461856521.10 L26188388139.39 L268088281.39   L27753976982.2  L28166690994.25 L29428324939.5  L3467313635.39  L34975272336.4  L35653441506.7  L36415273132.6  L37030167487.39 L3873698411.20  L40246206135.5  L42464007210.4  L42465364470.39 L43651006716.25 L47354457582.39 L49654562871.3  L49656466606.3  L50501282130.5  L50503379150.5  L50503462098.5  L50663673252.28 L50663883325.39 L52005607282.39 L52456315420.3  L53811483993.39 L53811731136.25 L54039657959.39 L54039704190.28 L55670312779.4  L55672046546.4  L59288134590.39 L59856652214.7  L60098763854.3  L60642549393.39 L60642562312.25 L61173140845.39 L61689853487.4  L61689934387.4  L61690767727.25 L61691951027.4  L61762120321.4  L61763254109.39 L65357244774.4  L65833526006.39 L65833545071.28 L68508330883.5  L68512070341.39 L7030096054.1   L7030098507.2   L7044745654.211 L7048038937.28  L7742933724.28  L7742948677.39  L9085623103.211 N44259866089.209N56949504728.209N63244352774.209N64040766665.209O10395993057.209O11831570240.209O11831570240.210O12090631900.208O13335976522.209O17025492443.208O17223163713.208O26683608823.210O28145700700.210O28775363370.209O28775363370.210O40241445883.209O40241445883.210O45137625611.209O45137625611.212O45137625611.214O4669439211.209 O49867185343.210O67018931761.210O67099258375.211O67099258375.213O6777839498.210 P22842297120.208P49644543183.209P49644543183.212P49644543183.214P55676933043.211P55676933043.213Q17582764468.212Q38248387216.212Q43879899724.212Q51233741152.212Q5472627854.212 Q59856668847.190Q8144514863.212 00000100200300400500600702<03B04E06F07R08d0:20;C0<c0>40?B0?C0@\0Aj0Ci0Cj0Ck0Cl0EK0Fn0HJ0HK0HL0ID0Jl0Ki0Ma0Mb0N20N30NJ0Nl0OK0OL0OM0Pf0QQ0QR0QS0Qa0RD0Rf0S40S;0SA0SS0Th0Ti0UA0UM0UV0VW0VX0VY0Vn0W]0Wo0X00X10X20X30X40X^0Yd0Z20Z30[?0\10\?0\H0\I0\J0\W0]10];0^\0_R0a30a40a50aA0aP0aQ0ac0ad0b20b;0b<0ce0cf0co0eF0eS0eb0f30gI0h?0i:0j=0k30k40k50k60k70k80k90k:0k;0k<0k=0k>0k?0kg0kh0ki0kj0kk0kl0km0kn0ko0l00l10l20l30l40l50l60m30m`0nP0o?0ok11611kFFFFFFFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl1B2zs2xs3tab3sel3tmp3RET3RRg3LTB3BF2S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RETS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RETS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1B2zs2xs3tab3sel3tmp3RET3RRg3BF2S1R2ra2sp1X1A1N1E2RR1T2lo3xs02ys2ns2es2rs3ts03LOS2tl1B2zs2xs3tab3sel3tmp3RETS1R3HIA1h2ra2sp1X1A1N1E2RR1T2lo3xs02ys2ns2es2rs3ts03TOP2tl1B2zs2xs3tab3sel3tmp3RETS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2SX2tl2zs2xs3tab3sel3tmpS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LSS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBFS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS1R3HIA1h2LB2LF2sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2LN5welem2tl2zs2xs3tab3sel3tmp3x144DNX'3x153x164POSTFFFS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LSS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LMS1R5NEED02sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2LO2SX2tl2zs2xs3tab3sel3tmpFFS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp2LSS1R3HIA1h2LB2LF2sp1X1N2an1T2ln2lo3xs02ys2ns2es2rs3ts02LN5welem2tl2zs2xs3tab3sel3tmp3x143SN'3x153x164POSTS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTBS1R3HIA1h2LB2LF2sp1X1N2an1T2ln2lt2lo3xs02ys2ns2es2rs3ts03Han2LN5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB3x144DNT'3x153x164POSTFS2an1T3Han5welemFS2an1T3Han2ws5welem3HWSS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS1X2an2en2lx2la2ln3le_2lr2lt2LnFFS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han2TB3STT2ws5welem3HWS3HWLFFS1R2sp1T2lo2LOS2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS2sp1N1T2ln2NBS2sp2loS2an1TS1R2lo3LOS3ALO3ACPS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln2XB2TB3SPR2LO3STT2ws5welem3HWS3HWLFS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welemS2sp2an1TS2sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo2Ln5welem3HWL4DNX'4DNT'3SN'FFS2sp1X1N1T2lx2ln4DNX'S1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO5welem3HWLS1R3HIA1h2sp1T3TOPFFFFFS1X2an1T2lx2lt3Han3DXT2XB2ws5welem3HWS3HWLS1R5NEED02sp1X2an1T2lx2lt2lo3Han3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWLS2sp1N1T2ln2NBFS1R5NEED02sp2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln2TB3SPR2LO2ws5welem3HWS3LO0S1R5NEED02sp2an1T2lt2lo3Han2TB2LO2ws5welem3HWS3LO0S2sp1X1T2lx2XBS1X2lx2XBFFS2sp2an1T3HanS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOSS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3ALT3SPR2LO2SX3STT2ws5welem3HWS3HWL3LO0S1R5NEED02sp2an1T2lt2lo3Han2TB3ALT2LO2ws5welem3HWS3LO0S1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR3SPA2LO2SX3STT2ws5welem3HWS3HWL3LO0FFS2an1T5welemS2an1T5welem2tlFS2sp1N1T2ln2lo3SN'FS2sp1X1T2lx2XBS1X2lx2XBFS1R5NEED02sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWL4DNX'4DNT'3SN'FS3RET3RRgS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RET3RRg3x153x163PC03PC3S1X2lx2XB3ALXS2sp1X2lx2lo2SXS2sp1X1T2lx2lo2SXS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RET3x153x163PC03PC3S2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmp3x171CS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp3x171CS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTB3x171CS2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmp3x171CFFFFFFFFFFFFS2an1T3Han5welem2tl2zs3tab3sel3tmp2LS2LMFFFFFFFFFFFFFFFS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTBS2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS1X2an3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS1X3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts03SPR3LOS2LO2tl2zs2xs3tab3sel3tmp3ALO3ACPS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 HWS HWL LTL OTL"] Lemma mm_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PB,$0.Pzs,(1.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))PRET,$0.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa6,(2.&40.)Pys2,(2.&40.)Pys3,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(>.(15.(8.$0.R1=.VX,)(8.(1.(2.&40.))R1<.R1:.))(15.(8.$0.R1=.(10.VT,(32.+4.(32.Vwelem,Van,))))(8.(1.(2.&40.))R1<.R18.)))P,(8.(2.&40.)R16.(1>.&40.R17.))P,(8.$0.(1?.R18.+2.)=)P,(15.(?.=R19.)(16.R19.(14.+2.+40.)))P,(33.R1?.R1>.R1=.R1<.R1;.)P,(35.$5.R20.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))P,Pmm',P,(2.&40.)(3.(2.&8.))Pxs',(1.(2.&40.))Ptmp',(1.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(33.R12.R11.R31.R30.R10.)P,(35.$5.R13.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R2?.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R11.R10.R?.R2;.R2:.R>.R=.R<.R;.R:.R9.R8.R7.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R6.R5.R4.R3.)VF,(1>.&40.R30.)Vfc,(2:.(2.&40.))R14.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1<.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R1;.R1:.R19.R18.R17.(1>.&40.VX,)(1>.&40.VX,)(1>.&40.R24.)(1>.&40.Van,)(1>.&40.VN,)(1>.&40.Van,)R16.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,))))R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(1>.&40.$3:.)Vfc,(2:.(2.&40.))R22.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HB -> RE RRg MV FR K.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      pose proof (unlock _ DNX) as DNX'. pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'.
      pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNX' DNT' SN' Ln HWL Han; lia)) as HN.
      assert (HBro : bytes_at asegs mm B (u32s zs)) by (destruct HB as [[-> ->]|[-> ->]]; apply u32arr_ro; assumption).
      assert (LZ : Z.of_nat (length zs) = lx \/ (B = SEL /\ Z.of_nat (length zs) = an)) by (destruct HB as [[-> ->]|[-> ->]]; [left; exact LX| right; split; [reflexivity| exact LS]]).
      assert (OB : aobj asegs AL CS mm B (4 * an)) by (destruct HB as [[-> _]|[-> _]]; [exact OX| eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]]).
      assert (OTM : aobj asegs AL CS mm TMP (4 * (2 * an + 1))) by (eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]).
      assert (CWM : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) TMP (4 * (2 * an + 1))) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia).
      assert (BF : B mod 4 = 0 /\ 0 < B /\ B + 4 * Z.of_nat (length zs) < 2^64 /\ an <= Z.of_nat (length zs)
                   /\ (B + 4 * Z.of_nat (length zs) <= TMP \/ TMP + 4 * Z.of_nat (length tmp) <= B)
                   /\ (B + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp + -176 <= B)).
      { rewrite LM. destruct HB as [[-> ->]|[-> ->]].
        - rewrite LX. clear - Han Ln HWL HWS DXT XB TB SPR LO NEED0 LO0 SX ALX. repeat split; try lia.
        - rewrite LS. clear - Han Ln HWL HWS TB SPR LO NEED0 LO0 STT ALT. repeat split; try lia. all: Z.div_mod_to_equations; lia. }
      ddestruct BF as (BF1 & BF2 & BF3 & BF4 & BF5 & BF6).
      pose proof (u32arr_ro _ _ _ _ HX) as HXro.
      pose proof MM as MM'. unfold mpi_core_montmul_stmtA, MPI_CORE_MONTMUL_STACK_A in MM'.
      callxA_sp (bv_unsigned sp + -176)
        (eapply MM' with (h := h) (LB := LB) (LF := LF) (X := X) (A := X) (B := B) (bn := an) (N := N) (an := an) (T := TMP) (lo := lo)
                         (xs := xs) (ys := xs) (zs := zs) (ns := ns) (ts := tmp);
         rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia);
         first [ exact HH | exact HX | exact HXro | exact HBro | exact HN | exact HMm | exact ST | exact LOS | exact MI | exact OX | exact OB | exact ON | exact OTM
               | exact CWX | exact CWM | exact Han | exact ALX | exact ALN | exact BF1 | exact BF2 | exact BF3 | exact BF4 | exact BF5 | exact BF6 | reflexivity
               | rewrite unsigned_lit by (clear - RRg; lia); exact RE
               | rewrite ?LX, ?LN, ?LM; destruct LZ as [LZ|[EB' LZ]]; rewrite ?LZ; try subst B;
                 clear - Han Ln HWL HWS DXT XB NB TB SPR SPA LO NEED0 LO0 SX STT DNX' DNT' SN' TOP ALT HTOP; first [ lia | Z.div_mod_to_equations; lia ]
               | match goal with |- ?g => idtac "MM-PRE-LEFT:" g end ]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MM-LEFT:" g end.
      try replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      lazymatch goal with H1 : u32arr asegs ?m2 X ?xs2, H2 : length ?xs2 = length xs, H3 : skipn _ ?xs2 = skipn _ xs,
                       H4 : u32arr asegs ?m2 (TMP) ?tmp2, H5 : length ?tmp2 = length tmp,
                       H6 : mem_inv asegs ?m2, H7 : stk asegs ?m2 lo _, H8 : HM _ _ _ h LB LF ?m2 |- _ =>
        eapply (K m2 xs2 tmp2); [| exact FR];
        refine (conj H1 (conj _ (conj _ (conj HT (conj LTB (conj HS (conj LS (conj H4 (conj _ (conj HL (conj MU (conj WM (conj H6 (conj H7 H8))))))))))))));
        [ rewrite H2; exact LX | eapply (same_from_of_window (Z.to_nat an)); [exact H3 | lia | exact FX] | rewrite H5; exact LM ]
      end.
      all: match goal with |- ?g => idtac "MMCALL-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Definition NUMS (limb bit wbits window : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "(15.(15.(?.=O3.)(?.O3.+1?.))(15.(15.(?.=O4.)(?.O4.Ven,))(15.(>.(16.O4.Ven,)(8.$0.O3.=))(15.(?.+1.(10.(32.+20.O4.)O3.))(15.(15.(?.=O2.)(16.O2.Vws,))(15.(?.=O1.)(16.O1.(14.+2.O2.))))))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Definition KBODY (RBd : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Plimb,$0.Pbit,$0.Pwbits,$0.Pwindow,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(3;.R1;.R1:.R19.R18.)P,(?.(10.(32.+20.R1<.)R1;.)O1.)P,(33.R19.R18.R17.R16.R15.)P,(35.$5.R1:.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R16.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R15.R14.R13.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R12.R11.R10.R?.R>.R=.R<.R;.R:.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)(1>.&40.R1<.)(1>.&40.R1?.)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.R1>.)(1>.&40.R1=.)R9.R8.R7.R6.R5.)VF,(1>.&40.+:6478.)Vfc,(2:.(2.&40.))R1;.(2;.$5.)))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L29428324939.5  L35653441506.7  L36158162381.173L56713546224.145L56713771218.168L60098763854.3  L66058234656.145L66058443266.16800000B00Z03W04Q05Z05d07Y09]S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R5NEED02ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws2tl4limb3bit5wbits6window2xs3tab3sel3tmp4Hbit5Hlimb3Hwb4Hwin3LOR2LX2K02NZS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit5wbits4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit5wbits2xs3tab3sel3tmp4HbitS1R2lo3LOSS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl4limb5wbits5Hlimb3HwbS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl4limb5wbits2xs3tab3sel3tmp5Hlimb3Hwb". (* [comment removed for export] *)
    #[using="IMG NEED0 A RR la ln le_ lr lt ys ns es rs Ln L0 LT0 DXT XB TB SPR LOS LO TOP SX STT AB NB EB RB HWL LTL"] Lemma cont_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PRBB,$0.Plimb,$0.Pbit,$0.Pwbits,$0.Pwindow,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys9,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(15.(?.=R19.)(?.R19.+1?.))P,(15.(?.=R1;.)(16.R1;.Ven,))P,(15.(?.=R1:.)(16.R1:.Vws,))P,(15.(?.=R1:.)(16.R1:.(14.+2.R1;.)))P,(?.(10.(32.+20.R1>.)R1=.)R1?.)P,(3<.R20.)P,(33.R1<.R1;.R1:.R19.R18.)P,(35.$5.R1=.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R19.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R18.R17.R16.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.(3=.R22.R21.))R15.R14.R13.R12.R11.R10.R?.R>.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)(1>.&40.R1?.)(1>.&40.R22.)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R=.(1>.&40.R20.)(1>.&40.R21.)R<.R;.R:.R9.)VF,(1>.&40.+:6470.)Vfc,(2:.(2.&40.))R1>.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb Hwb Hwin HRB KB MV FR.
      pose proof (lor_lt_pow2 limb bit 64 ltac:(lia) ltac:(lia)) as LOR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      zstep. zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      - apply Z.lor_eq_0_iff in K0. destruct K0 as [-> ->]. eapply exit_walk; [exact MV | exact FR].
      - assert (NZ : limb <> 0 \/ bit <> 0) by (destruct (Z.eq_dec limb 0) as [E0|]; [right; intros E1; apply K0; rewrite E0, E1; reflexivity | left; assumption]).
        eapply KB; [| exact HRB | exact MV | exact FR]. unfold NUMS. lia.
      all: match goal with |- ?g => idtac "CONT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L29428324939.5  L3005110713.186 L31844853592.166L35653441506.7  L36972227160.166L55430846429.0  L56711266935.168L567271841.0    L60098763854.3  L62238965067.186L64420046552.166L66056478887.168L835807704.166  L9595732537.3   Q42451520258.169Q48477206658.169Q5059450721.169 Q50851826913.169Q50970145794.169Q53365627489.169Q56995815810.169Q63330912737.16900000B01E02?02W03Q03R04U04V04`05h06b08Y09S09a0:Y0;Q0<>0<k0=c0>P0?H0@5S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit2xs3tab3sel3tmp4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit2xs3tab3sel3tmp4HbitSS1R2lo3LOSS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl4limb2xs3tab3sel3tmp5HlimbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2tl4limb2xs3tab3sel3tmp5HlimbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ws5welem3HWSS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 HWS HWL LTL OTL"] Lemma mult_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PRBB,$0.Plimb,$0.Pbit,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys5,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(15.(?.=R19.)(?.R19.+1?.))P,(15.(?.=R1;.)(16.R1;.Ven,))P,(?.(10.(32.+20.R1<.)R1;.)R1=.)P,(3<.R1>.)P,(33.R1<.R1;.R1:.R19.R18.)P,(35.$5.R1=.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R19.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R18.R17.R16.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.(3=.R20.R1?.))R15.R14.R13.R12.R11.R10.R?.R>.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)R=.(1>.&40.R20.)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R<.R;.(1>.&40.R1?.)R:.R9.R8.R7.)VF,(1>.&40.+:6444.)Vfc,(2:.(2.&40.))R1>.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb HRB KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      pose proof (lor_lt_pow2 limb bit 64 ltac:(lia) ltac:(lia)) as LOR.
      (* [comment removed for export] *)
      do 9 zstep.
      eapply (mm_call SEL sel mm xs tab sel tmp 0x0a6468); [right; split; reflexivity | reflexivity | reflexivity | clear; lia | exact MV | exact FR |].
      clear dependent mm. intros mm xs' tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MV FR.
      dpose MV as (HX2 & _ & _ & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep. zstep.
      eapply (cont_walk RBB limb bit 0 0); [lia | lia | clear - HWS; lia | clear; lia | exact HRB | exact KB | exact MV | exact FR].
      all: match goal with |- ?g => idtac "MULT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L10884122968.169L14023587864.172L2589518799.172 L29428324939.5  L34354857587.3  L34825681674.168L35205373606.168L35653441506.7  L43467180248.169L58493925670.2  L60098763854.3  L64734430706.3  L7454461363.169 Q12348970244.172Q26985410919.172Q310578692.172  Q34819445735.172Q49664522855.172Q6337902724.172 00000j02T03N03`03n03o04004H05B05H05R05`06Z07R08?09709d0:Q0;IS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl6window2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R2lo3LOS3ALO3ACPS2ws5welem3HWSFFS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2an1TS1R2lo3LOSS2ws5welem3HWSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma lookup_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pwindow,$0.PRBB,$0.Plimb,$0.Pbit,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(15.(?.=R18.)(?.R18.+1?.))P,(15.(?.=R1:.)(16.R1:.Ven,))P,(?.(10.(32.+20.R1;.)R1:.)R1<.)P,(3<.R1=.)P,(33.R1;.R1:.R19.R18.R17.)P,(35.$5.R1<.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R18.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R17.R16.R15.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.(3=.R1?.R1>.))R14.R13.R12.R11.R10.R?.R>.R=.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)(1>.&40.R21.)(1>.&40.R1?.)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R<.R;.(1>.&40.R1>.)R:.R9.R8.R7.)VF,(1>.&40.+:64?8.)Vfc,(2:.(2.&40.))R1=.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb HRB KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      eapply (ct_outer_walk (Z.to_nat welem) 0); [clear - HWS; lia | clear - HWS; lia | reflexivity | f_equal; clear; lia | exact MV | exact OT | exact FR |].
      clear dependent mm. intros mm sel' ya0 ya1 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 ys5' MV OT FR.
      eapply (mult_walk RBB limb bit); [exact Hbit | exact Hlimb | exact HRB | exact KB | exact MV | exact FR].
      all: match goal with |- ?g => idtac "LOOKUP-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L16966794342.198L16966794471.199L17468845586.192L18947339828.191L19886797616.183L20402632581.189L27625049176.186L29428324939.5  L32880766689.189L34823974375.179L35653441506.7  L37032795739.199L37032795866.198L39833942540.185L39835945900.190L39836414876.193L41415872618.178L41418083415.186L41953455944.183L42599461041.178L45710833846.180L45712880613.177L54418629900.185L54418701239.177L54420804780.190L54420876444.193L56713773925.174L59308546259.189L60098763854.3  L60200242136.178L64189350643.190L66058396085.174L67524055061.199L67524055188.198L6757073015.188 L8255261546.20  Q20999335462.189Q26295627581.189Q27348161633.191Q27348259048.189Q27350351948.186Q2870651775.191 Q38931724217.186Q44300927607.186Q44959008386.194Q48729518810.186Q50458135125.189Q54107469312.189Q5678005985.194 Q8945665283.186 00001C02S03\04f05o06007307E07F09H09`0<g0?n0AO0B[0D<0E?0FB0HD0Jn0ME0O\0R30TJ0VP0Xg0Z30]B0]L0^O0`00b70cC0dR0eU0fV0h40hd0j;0kR0li0n@0oH10_11g12]13U14l15b16RS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp2eb2B1FS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1R2lo3LOS3ALO3ACPFS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS1R3HIA1h2sp2lo3TOP4HTOPS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem3LTB2LS5limb'3Hl2S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem3LTB2LS5limb'3Hl2S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk5wbits2xs3tab3sel3tmp3Hwb3LTB2LSS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3Hl1S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk3bit5wbits2xs3tab3sel3tmp4HbitS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Hen2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2LE2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3LTB2LS2db5limb'3Hl'2N0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb5wbits2xs3tab3sel3tmp5Hlimb3HwbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp1X2an1E2en1T2lx2la2ln3le_2lr2lt2lo2Ln5welem3HWL4DEX'4DET'3SE'S1E2en3le_3xs02ys2ns2es2rs3ts02EB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1E3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN AB NB EB RB SN SE HN0 HE0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma body2_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pkk,$34.Plimb,$0.Pbit,$0.Pbit',$0.Pwbits,$0.Pwindow,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(3;.R1;.R1:.R18.R17.)P,(?.(10.(32.+20.R1<.)R1;.)(10.(9.R1=.)+1.))P,(>.(15.(8.$0.R1<.=)(8.$0.R1;.+1?.))(15.(?.+1.R1<.)(8.$0.R1;.(38.R1<.+1.))))P,(3<.(9.R1?.))P,(33.R1:.R19.R18.R17.R16.)P,(35.$5.R1;.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.+2:2:2:2:.))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(37.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))))(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R17.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R16.R15.R14.(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))R13.R12.R11.R10.R?.R>.R=.R<.R;.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)(1>.&40.R1=.)(1>.&40.R21.)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.R20.)(1>.&40.R1>.)(1>.&40.R1?.)R:.R9.R8.R7.)VF,(1>.&40.+:64:<.)Vfc,(2:.(2.&40.))R1<.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros NU Hrem Hb KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      ddestruct NU as (Hbit & Hlimb & Hle & Hrem1 & Hwb & Hwin).
      assert (PW : 2^wbits <= 4) by (change 4 with (2^2); apply Z.pow_le_mono_r; lia).
      pose proof (unlock _ DEX) as DEX'. pose proof (unlock _ DET) as DET'. pose proof (unlock _ SE) as SE'.
      pose proof (u32ro_transport _ _ _ _ _ _ HE0 MU ltac:(cbn [disjoint_from]; rewrite LE; clear - DEX' DET' SE' Ln HWL Han; lia)) as HE.
      (* [comment removed for export] *)
      zstep. zstep.
      set (db := Z.b2z (bit <? 1)) in *.
      assert (Hl' : 0 <= limb - db < en /\ 32 * (limb - db) + bit' = 32 * limb + bit - 1 /\ 0 <= bit' <= 31 /\ 0 <= db <= 1).
      { subst db. destruct (Z.ltb_spec bit 1); cbn [Z.b2z]; lia. }
      clearbody db.
      set (limb' := limb - db) in *. clearbody limb'.
      (* [comment removed for export] *)
      zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OE (E + limb' * 4) 4.
      (* [comment removed for export] *)
      rd HE limb'. clear HE.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2. try rewrite (Z.mod_small (window * 2)) by lia.
      (* [comment removed for export] *)
      vstep 10%positive.
      lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 10%positive in
        lazymatch v with Z_to_bv 64 ?z => pose proof (land_1_range z) as B1 | _ => pose proof (land_1_range (bv_unsigned v)) as B1 end end.
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 10%positive in
        lazymatch v with Z_to_bv 64 ?z => set (eb := z) in *; clearbody eb end end.
      pose proof (lor_bit_bound eb window wbits B1 ltac:(lia) Hwin) as WB.
      (* [comment removed for export] *)
      zstep. set (window' := Z.lor eb (window * 2)) in *. clearbody window'.
      pose proof (lor_lt_pow2 limb' bit' 64 ltac:(lia) ltac:(lia)) as LOR.
      (* [comment removed for export] *)
      zstep. zstep.
      ddestruct Hl' as (Hl1 & Hl2 & Hl3 & Hl4).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - (* [comment removed for export] *)
        eapply (lookup_walk window' (Z.of_nat kk) limb' bit'); [lia | lia | lia | exact KB | exact MV | exact FR].
      - (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
        + (* [comment removed for export] *)
          eapply (cont_walk (Z.of_nat kk) limb' bit' (wbits + 1) window'); [lia | lia | lia | exact WB | lia | exact KB | exact MV | exact FR].
        + (* [comment removed for export] *)
          eapply (lookup_walk window' (Z.of_nat kk) limb' bit'); [lia | lia | lia | exact KB | exact MV | exact FR].
      all: match goal with |- ?g => idtac "BODY2-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L12808385313.0  L19037020683.189L24471669126.189L29428324939.5  L31844853592.170L35653441506.7  L36972227160.170L50988289423.189L56713771218.184L59308681713.141L60098763854.3  L64420046552.170L835807704.170  Q42457880190.174Q48479233534.174Q5057284637.174 Q50866442653.174Q50984888702.174Q53355202333.174Q57006243070.174Q63320364189.17400000101G02U02g04804P05a07708J09F09P0:a0<20=H0>^0?b0@f0B<0C@0DV0EZSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4Hbit2K0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4HremS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4Hbit2K0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl4limb3bit2H14HremS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN AB NB EB RB SN SE HN0 HE0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma body_walk : forall kk : nat, KBODY (Z.of_nat kk).
    Proof.
      induction kk as [|kk IH]; unfold KBODY; intros limb bit wbits window mm xs tab sel tmp xra xt0 xt1 xt2 ys1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys11 xt3 xt4 xt5 xt6 NU Hrem MV FR.
      { exfalso. ddestruct NU as (_ & _ & _ & H1 & _). lia. }
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      dpose NU as (Hbit & Hlimb & Hle & Hrem1 & Hwb & Hwin).
      (* [comment removed for export] *)
      do 9 zstep.
      eapply (mm_call X xs mm xs tab sel tmp 0x0a649c); [left; split; reflexivity | reflexivity | reflexivity | clear; lia | exact MV | exact FR |].
      clear dependent mm. clear dependent xs. intros mm xs tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MV FR.
      dpose MV as (HX2 & _ & _ & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      - (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (bit + -1)) with (Z_to_bv 64 (bit - 1)) by (f_equal; lia).
        eapply (body2_walk kk limb bit (bit - 1) wbits window); [exact NU | lia | right; lia | exact IH | exact MV | exact FR].
      - (* [comment removed for export] *)
        zstep. zstep.
        eapply (body2_walk kk limb bit 31 wbits window); [exact NU | lia | left; lia | exact IH | exact MV | exact FR].
      all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation W0T := [(T, T + 4 * WLN); (lo, bv_unsigned sp)].
    Definition PINV (mm : mem) (tab sel tmp : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "(15.(30.$5.O4.VX,Vxs0,)(15.(30.$5.O4.VT,O3.)(15.(8.$0.(9.(:.(2.&40.)O3.))(32.Vwelem,Van,))(15.(30.$5.O4.(10.VT,(32.+4.(32.Vwelem,Van,)))O2.)(15.(8.$0.(9.(:.(2.&40.)O2.))Van,)(15.(30.$5.O4.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))O1.)(15.(8.$0.(9.(:.(2.&40.)O1.))(10.(32.+2.Van,)+1.))(15.(30.$5.O4.(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))Vtl,)(15.(20.(21.(22.$0.$0.)(23.$0.$0.VT,(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(12.&40.Vsp,))(24.(22.$0.$0.))))Vm,O4.)(15.(25.$5.Vm,O4.)(15.(13.$5.O4.)(15.(11.$5.O4.Vlo,(10.(12.&40.Vsp,)-;0.))(4.$5.VR,VHIA,Vh,VLB,VLF,O4.)))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L29428324939.5L35653441506.7L48155834837.3L60098763854.300000B00Z00f010S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welemS1R2lo3LOS". (* [comment removed for export] *)
    #[using="IMG LOS TOP OX0 OA0 ON0 OR0 OTL"] Lemma objs_pre : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))P,(4.$5.VR,VHIA,Vh,VLB,VLF,R1.)P,(20.(21.(22.$0.$0.)(23.$0.$0.VT,(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(12.&40.Vsp,))(24.(22.$0.$0.))))Vm,R2.)(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VX,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VA,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VN,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VRR,(32.+4.Van,))(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))))))")
(* [comment removed for export] *).
    Proof.
      intros mm HH MU. rt_facts.
      assert (WC : w_client CS W0T).
      { unfold w_client. repeat apply Forall_cons; cbn [fst snd]; [| | apply Forall_nil].
        - replace (T + 4 * WLN - T) with (4 * WLN) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OTL).
        - exact SCS. }
      repeat split; eapply (aobj_munch asegs AL _ CSOK W0T m mm); first [exact WC | exact MU | eassumption].
      all: match goal with |- ?g => idtac "OBJSPRE-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0150@L10351611861.177L10969596589.7  L11547683719.23 L13041178736.177L14220219354.6  L14220219356.6  L14222026245.7  L16347013912.3  L17597577141.6  L17597724619.5  L17597724621.5  L18333993997.28 L22382916926.38 L22383214332.23 L22383426215.28 L23272070152.38 L23461856521.10 L23461856521.12 L24352576421.28 L25502270292.38 L25814703959.178L26188388139.38 L268088281.38   L27163225748.3  L28573892092.15 L29127537594.28 L29428324939.5  L29519540155.178L29521865028.177L3090143128.7   L3467313635.38  L3467431546.28  L35653441506.7  L35735336831.5  L36415273132.6  L37030167487.38 L38732808811.7  L44160616706.178L47354457582.38 L49572570277.3  L50663590399.25 L51067033701.28 L51433150352.18 L51644778604.38 L52005607282.38 L53167460058.28 L53811483993.38 L54906982271.28 L5705634570.11  L59288134590.38 L59856652214.7  L60098763854.3  L60102575509.7  L60249634074.28 L60642549393.38 L60642562312.28 L60882515847.28 L60958122188.18 L61173140845.38 L61690455798.38 L61690686772.23 L61690767727.28 L61763254109.38 L65357034607.23 L68512070341.38 L7029671751.235 L7030098507.2   L7554033252.7   L7742721671.25  00001601S02:03@03W03m04G04Q04h05:05M05_06[07I08?08M09009R09\0:10;90;[0;i0<30<[0=X0=j0>l0?n0@K0AG0BH0B`0C30C?0CH0Ce0Dm0E?0EK0F80Fd0GK0Ga0Go0H=0I@0I`0JA0JN0Jh0K20KN0KX0L_0M`0NH0O10OW0PH0Ph0QP0Qb0R80SF0Te0Tn0UJ0UYS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1i3tab3sel3tmp3RET2HiS2an3Han5welem2ka3tab3LTB3AWkS2sp2an1T2lt2lo3Han3STT5welem3HWL1i3AWiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1i3tab3sel3tmp3RET2HiS2an1T3Han5welem2ka3AWkS2an1T3Han5welem1i3AWiS2an1T3Han2ws5welem3HWS2W2S2an1T3HanS2an1T3Han2ws5welem3HWSS2an1T5welem1i3AWiS2an1T5welem2ka3AWkS2sp2RR2lr2lo4SRR'S2sp2an1T2lt2lo3Han2TB3SPR3STT5welem3HWL1i3AWi2ka3AWk2ws3HWSS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWL1i3AWiS2sp2an1T2lt2lo3Han2TB3STT2ws5welem3HWS3HWL3tab2W23LTBS1R2sp1T2lo2LOS2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS2an1T2lt3Han5welem3HWL1i3AWi1a2HaS2RR2lr2RBS2sp2an1T5welem1i3AWiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl2ka3tab3sel3tmp3RET3HkaS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS2sp1N1T2ln2NBS2an1T3HanS2sp2an1T2lo3Han2ws5welem3HWS1i3AWi1x2HxS1R5NEED02sp2an1T2lt2lo3Han2TB2LO2ws5welem3HWS3tab2W23LTB3LO0S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl3tab3sel3tmp3RETS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl3tab3sel3tmp3RETS2an3Han2ws5welem3HWS3tab3LTBS1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO5welem3HWL1i2ka3AWi3AWkS1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO2ws5welem3HWS3HWL3tab2W23LTBS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welem2ka3AWkS2an1T5welemS2sp2an1TS2an3Han5welem2ka3tab3LTB3AWkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl2ka3tab3sel3tmp3RET3HkaS1R3HIA1h2sp1T3TOPS2an5welem1iS1X2an1T2lx2lt3Han3DXT5welem3HWL1i3AWi2ws3HWSS2an2RR1T2lr2lt3Han2RB2ws5welem3HWS3HWL4DRT'S2sp1N2an1T2ln2lt2lo5welem3HWL4DNT'3SN'S2sp2an1T5welem2ka3AWkS2sp1N1T2ln2NBS2RR2lr3ALR2RBS1R5NEED02sp2an1T2lt2lo2TB3SPR2LO5welem1i3LO03AWi2ka3AWk3Han2ws3HWSS2an2en2RR2lx2la2ln3le_2lr2lt2LnS2sp2an1T2lo5welem1i1a1n2D12D22D3S2sp2an1T3HanS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOSS2an3Han5welem1i3tab3LTB3AWiS2RR2lr2RBS1R5NEED02sp2an1T2lt2lo2TB3ALT3SPR2LO5welem1i3LO03AWi2ka3AWk3Han2ws3HWSS1R5NEED02sp2an1T2lt2lo3Han2TB3ALT2LO2ws5welem3HWS3tab2W23LTB3LO0S2an1T2lt3Han2TB2ws5welem3HWS3tab2W23LTBS2sp2an2RR1T2lr2lt2lo5welem3HWL4DRT'4SRR'S1R5NEED02sp1T2lt2lo2TB3SPR3SPA2LO3LO0S2sp2an1T2lt3Han2TB3SPR2ws5welem3HWS1i3AWi2ka3AWkS2an1T5welem1i3AWi2lt3Han2ws3HWSS2an1T2lt3Han2TB2ws5welem3HWS3tab2W23LTBS2sp1N1T2ln2lo3SN'S2an1T1i3Han5welem3AWiS1R5NEED02sp1N2an1T2ln2lt2lo3Han2TB3SPR2LO3STT2ws5welem3HWS3HWL1i3AWi4DNT'3SN'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs3tab3sel3tmp3RET3RRg3pre2xw2aw3xw'4tmp'3LXc3LTcS3RET3RRgS2an3Han5welem1i3tab3LTB3AWiS2sp1X2lx2lo2SX". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A E en lx la ln le_ lr lt ys ns es Han Ln L0 DXT TB ALT SPR SPA LOS LO TOP SX STT CWT LN LR DNT DRT ALN ALR NB RB SN SRR HN0 HR0 OX0 OA0 ON0 OR0 ws HWS HWL LTL OTL"] Lemma mm_call_tab : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pi,$0.Pka,$0.PB,$0.Pzs,(1.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))PRET,$0.PFRP,P,P,(2.&40.)(3.(2.&8.))SpPxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa6,(2.&40.)Pys2,(2.&40.)Pys3,(2.&40.)Pys4,(2.&40.)Pys5,(2.&40.)Pys6,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys9,(2.&40.)Pys10,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(15.(?.=R1?.)(16.R1?.Vwelem,))P,(15.(?.=R1?.)(16.R1?.Vwelem,))P,(>.(15.(8.$0.R1?.VRR,)(8.(1.(2.&40.))R1>.Vrs,))(15.(8.$0.R1?.(10.VT,(32.+4.Van,)))(15.(8.(1.(2.&40.))R1>.(3>.(2.&40.)(2>.Van,)R1<.))(?.+2.Vwelem,))))P,(8.(2.&40.)R18.(1>.&40.R1:.))P,(8.$0.(1?.R1;.+2.)=)P,(15.(?.=R1<.)(16.R1<.(14.+2.+40.)))P,Pm1,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(20.(21.(22.$0.$0.)(23.$0.$0.(10.VT,(32.+4.(32.Van,R27.)))(10.(10.VT,(32.+4.(32.Van,R27.)))(32.+4.Van,)))(21.(22.$0.$0.)(23.$0.$0.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))(10.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,)))(32.+4.(10.(32.+2.Van,)+1.))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(10.(12.&40.Vsp,)-;0.))(24.(22.$0.$0.)))))R2.R1.)P,(25.$5.R3.R2.)P,A1.R20.R4.A1.R21.R4.P,(3?.R22.R21.R20.R1?.)P,A1.R1>.R23.P,Pmm',P,(2.&40.)(3.(2.&8.))Ptab',(1.(2.&40.))Ptmp',(1.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(3?.R12.R11.R34.R10.)P,A1.R32.R13.(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R32.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R11.R10.R?.R2>.R2=.R>.R=.R<.R;.R:.R9.R8.R7.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R6.R5.R4.R3.)VF,(1>.&40.R34.)Vfc,(2:.(2.&40.))R14.(2;.$5.)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1?.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R1>.R1=.R1<.R1;.R1:.(1>.&40.(10.VT,(32.+4.(32.Van,R29.))))(1>.&40.(10.VT,(32.+4.(32.Van,R28.))))(1>.&40.R27.)(1>.&40.Van,)(1>.&40.VN,)(1>.&40.Van,)R19.(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,))))R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(1>.&40.$3:.)Vfc,(2:.(2.&40.))R25.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hi Hka HB -> RE RRg FRT PV FR K.
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_pre _ HH MU) as (OX & OA & ON & OR & OT).
      assert (AWi : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (AWk : 0 <= an * ka /\ an * ka + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'. pose proof (unlock _ DRT) as DRT'. pose proof (unlock _ SRR) as SRR'.
      pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNT' SN' Ln HWL Han; lia)) as HN.
      pose proof (u32ro_transport _ _ _ _ _ _ HR0 MU ltac:(cbn [disjoint_from]; rewrite LR; clear - DRT' SRR' Ln HWL Han; lia)) as HR.
      (* [comment removed for export] *)
      set (pre := firstn (Z.to_nat (an * i)) tab). set (xw := skipn (Z.to_nat (an * i)) tab).
      assert (LPRE : Z.of_nat (length pre) = an * i) by (subst pre; rewrite firstn_length; clear - LTB AWi Han; lia).
      assert (LXW : Z.of_nat (length xw) = welem * an - an * i) by (subst xw; rewrite skipn_length; clear - LTB AWi Han; lia).
      pose proof HT as HT2. rewrite <- (firstn_skipn (Z.to_nat (an * i)) tab) in HT2. fold pre xw in HT2.
      apply u32arr_app in HT2. destruct HT2 as [HPRE HXW]. rewrite LPRE in HXW.
      pose proof (u32ro_window _ _ _ _ (Z.to_nat (an * ka)) (u32arr_ro _ _ _ _ HT) ltac:(clear - LTB AWk Han; lia)) as HAW.
      replace (T + 4 * Z.of_nat (Z.to_nat (an * ka))) with (T + 4 * (an * ka)) in HAW by (clear - AWk; lia).
      set (aw := skipn (Z.to_nat (an * ka)) tab) in *.
      assert (LAW : Z.of_nat (length aw) = welem * an - an * ka) by (subst aw; rewrite skipn_length; clear - LTB AWk Han; lia).
      assert (HBro : bytes_at asegs mm B (u32s zs)).
      { destruct HB as [[-> ->]|(-> & -> & _)]; [exact HR|].
        pose proof (u32ro_window _ _ _ _ (Z.to_nat an) (u32arr_ro _ _ _ _ HT) ltac:(clear - LTB Han HWS; lia)) as HW1.
        replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in HW1 by (clear - Han; lia). exact HW1. }
      assert (BF : B mod 4 = 0 /\ 0 < B /\ B + 4 * Z.of_nat (length zs) < 2^64 /\ an <= Z.of_nat (length zs)
                   /\ (B + 4 * Z.of_nat (length zs) <= TMP \/ TMP + 4 * Z.of_nat (length tmp) <= B)
                   /\ (B + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp + -176 <= B)).
      { rewrite LM. destruct HB as [[-> ->]|(-> & -> & W2)].
        - rewrite LR. clear - Han Ln HWL HWS DRT' RB TB SPR LO NEED0 LO0 SRR' ALR. repeat split; try lia.
        - rewrite skipn_length. clear - Han Ln HWL HWS TB SPR LO NEED0 LO0 STT ALT LTB W2. repeat split; try lia. all: Z.div_mod_to_equations; lia. }
      ddestruct BF as (BF1 & BF2 & BF3 & BF4 & BF5 & BF6).
      assert (OB : aobj asegs AL CS mm B (4 * an)).
      { destruct HB as [[-> _]|(-> & _ & W2)]; [exact OR| eapply aobj_sub; [exact OT| clear - Han; lia| clear - Han HWS W2; lia]]. }
      assert (OXW : aobj asegs AL CS mm (T + 4 * (an * i)) (4 * an)) by (eapply aobj_sub; [exact OT| clear - AWi; lia| clear - AWi Han; lia]).
      assert (OAW : aobj asegs AL CS mm (T + 4 * (an * ka)) (4 * an)) by (eapply aobj_sub; [exact OT| clear - AWk; lia| clear - AWk Han; lia]).
      assert (OTM : aobj asegs AL CS mm TMP (4 * (2 * an + 1))) by (eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]).
      assert (CWW : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) (T + 4 * (an * i)) (4 * an)) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL AWi; lia).
      assert (CWM : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) TMP (4 * (2 * an + 1))) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia).
      pose proof MM as MM'. unfold mpi_core_montmul_stmtA, MPI_CORE_MONTMUL_STACK_A in MM'.
      eapply evtA_cut.
      { eapply MM' with (h := h) (LB := LB) (LF := LF) (X := T + 4 * (an * i)) (A := T + 4 * (an * ka)) (B := B) (bn := an) (N := N) (an := an) (T := TMP) (lo := lo)
                         (xs := xw) (ys := aw) (zs := zs) (ns := ns) (ts := tmp);
         rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia);
         first [ exact HH | exact HXW | exact HAW | exact HBro | exact HN | exact HMm | exact ST | exact LOS | exact MI | exact OXW | exact OAW | exact OB | exact ON | exact OTM
               | exact CWW | exact CWM | exact Han | exact ALN | exact BF1 | exact BF2 | exact BF3 | exact BF4 | exact BF5 | exact BF6 | reflexivity
               | rewrite unsigned_lit by (clear - RRg; lia); exact RE
               | rewrite ?LXW, ?LAW, ?LN, ?LM;
                 clear - Han Ln HWL HWS NB TB SPR SPA LO NEED0 LO0 STT DNT' SN' TOP ALT HTOP AWi AWk; first [ lia | Z.div_mod_to_equations; lia ]
               | match goal with |- ?g => idtac "MMT-PRE-LEFT:" g end ]. }
      unfold mpi_core_montmul_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by (clear - SPR LO NEED0 LO0; lia).
      intros ms' PO.
      ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & xw' & tmp' & -> & MUc & WMc & MIc & HXc & LXc & _ & HTc & LTc & _ & STc & HHc).
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      eapply (K m2 (pre ++ xw') tmp'); [| eapply FRT; [exact MUc| exact WMc| exact FR]].
      assert (DJ : forall a n, (a + n <= T + 4 * (an * i) \/ T + 4 * (an * i) + 4 * an <= a) -> (a + n <= TMP \/ TMP + 4 * (2 * an + 1) <= a) -> (a + n <= lo \/ bv_unsigned sp + -176 <= a) ->
                disjoint_from [(T + 4 * (an * i), T + 4 * (an * i) + 4 * an); (TMP, TMP + 4 * (2 * an + 1)); (lo, bv_unsigned sp + -176)] a n).
      { intros a n D1 D2 D3. cbn [disjoint_from]. clear - D1 D2 D3. lia. }
      unfold PINV.
      split; [eapply u32arr_transport; [exact HX| exact MUc| exact WMc| apply DJ; rewrite L0; clear - DXT SX Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [apply u32arr_app; split; [eapply u32arr_transport; [exact HPRE| exact MUc| exact WMc| apply DJ; rewrite LPRE; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]| rewrite LPRE; exact HXc]|].
      split; [rewrite length_app, Nat2Z.inj_add, LXc, LPRE, LXW; clear; lia|].
      split; [eapply u32arr_transport; [exact HS| exact MUc| exact WMc| apply DJ; rewrite LS; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [exact LS|]. split; [exact HTc|]. split; [rewrite LTc; exact LM|].
      split; [eapply u32arr_transport; [exact HL| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; clear - Hx AWi Han HWS LO NEED0; lia|].
      split; [eapply wmono_trans; [exact WM| exact WMc]|].
      split; [exact MIc|]. split; [exact STc| exact HHc].
      all: match goal with |- ?g => idtac "MMTAB-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation FRAMEB mm j := (rw_cells asegs mm (bv_unsigned sp + -176)
       [C8 (Z_to_bv 64 (4 * (welem * an))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 ws);
        CB 8 j; C8 (Z_to_bv 64 X); C8 wmm; C8 (Z_to_bv 64 N);
        C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D35881667587.164D35881667587.197D46522149398.197D67387923631.164K40484668124.164K40484668124.197K42587433812.164K42587433812.197K60443225391.164K60443225391.197L10828273447.12 L10884122968.158L11547569120.23 L14594643364.8  L16635876761.7  L18866009566.9  L19282129351.23 L20886524867.18 L21231429831.7  L22383361691.23 L23063600908.2  L23898603878.1  L24953833255.17 L26126682082.19 L27756594391.19 L27950918981.2  L29428324939.5  L31844853592.158L320454087.14   L35653441506.7  L39466045300.157L40269711107.190L40500120010.3  L41140355171.19 L42589383440.3  L42589383443.3  L46030209441.0  L49904321809.12 L50502792114.23 L52454524354.19 L57628700040.11 L60098763854.3  L60437718071.5  L60437798955.5  L60439896503.5  L61453626589.6  L63157168055.2  L64420046552.157L67025746339.3  L7454461363.190 L9278517154.5   L9685877192.2   Q12348823042.161Q20783692010.194Q25513505925.163Q25513505925.196Q26985558625.161Q30206126178.197Q310558744.193  Q38130921043.161Q44262837305.196Q45941463673.164Q49664603259.193Q49698585326.162Q49698585326.195Q50358700898.163Q5059829094.160 Q50969804293.160Q56993619970.161Q63333173345.16100001K02k05>07H08j0:W0<10=S0?;0@n0AV0BM0Bn0CD0C`0D@0E:0Eb0F?0Fg0Fo0G20Gl0H:0HA0HI0H[0IR0J:0JR0KI0LN0LO0MB0MC0MD0ME0Mm0Ng0OZ0P30P=0P>0P?0P@0PW0P_0QV0Q_0Rd0S90SA0T60Tn0V20W90Wc0YC0ZJ0[40\J0]Y0^Q0_E0`G0aV0b@0c50cj0dTS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP5welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR3LOS2LO2AB2NB2EB2RB2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB5welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp1X2an1T2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX5welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS1R5NEED02sp1X2an2lx2lo3xs02ys2ns2es2rs3ts03Han2LO2SX2tl3tab3sel3tmp2LP3LF13xs13LX12HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_st2LM2LSS2an2en2lx2la2ln3le_2lr2lt3xs03Han2Ln2L0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS2sp2an1T2lt2lo3Han3STT5welem3HWLS2sp1X2an2lo1a1n2D12D2S2an2lt3Han2ws5welem3HWS3HWLS2an1T2lt3Han2ws5welem3HWS3HWL1QS1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2an3Han2ws5welem3HWS3tab3LTBS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2en3HenS1TS1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS1X2an3xs03HanS2sp2loS2an3HanS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo2Ln2SXS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1FS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs03Han2Ln2L02SXFFSS2an2en2lx2la2ln3le_2lr2lt3xs03Han2Ln2L0S1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS1R5NEED02sp1X2an2en2lx2la2ln3le_2lr2lt2lo2Ln2LO2SXS2sp1X2an1T2lo5welem1x2HxS1R2lo3LOSFFFS2an1T3Han2ws5welem3HWSS2an3HanS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS2an1q2HqS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2en3Hen2ws5welem3HWSS2an3HanS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl3tab3sel3tmpS2sp2an3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HBS2sp2an1T2lo3xs02ys2ns2es2rs3ts05welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS2sp2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS1R5NEED02sp1X2an1T2lo3xs02ys2ns2es2rs3ts03Han2LO5welem2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs1S2sp3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2HBS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2sp3xs02ys2ns2es2rs3ts03SPR2tl3tab3sel3tmp2HB5Ha_stS2sp2an3xs02ys2ns2es2rs3ts03SPR2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem2tl3tab3sel3tmp2HB5Ha_st5Hl_stS2sp2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN AB NB EB RB SN SE HN0 HE0 OX0 OA0 ON0 OE0 OR0 AMC T47A HWS HWL LTL OTL"] Lemma pre_tail_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pj,(1.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys0,(2.&40.)Pys1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys5,(2.&40.)Pys11,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(3?.R18.R17.R16.R15.)P,(35.$5.R19.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.(32.+4.(32.Vwelem,Van,))))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(40.#8.R1:.)(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R16.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)R8.(1>.&40.Ven,)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.=)(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,))))R7.R6.R5.R4.R3.)VF,(1>.&40.+:63?0.)Vfc,(2:.(2.&40.))R1:.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros PV FR.
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo _, H3 : HM _ _ _ h LB LF ?m2 |- _ =>
        rename H1 into MI1; rename H2 into ST1; rename H3 into HH1; rename m2 into m1 end.
      destruct (objs_pre _ HH1 MU) as (OX & OA & ON & OR & OT).
      pose proof (firstn_skipn (Z.to_nat an) xs0) as EY. symmetry in EY.
      assert (LP : length (firstn (Z.to_nat an) xs0) = Z.to_nat an) by (rewrite firstn_length; clear - L0 Ln Han; lia).
      pose proof HX as HX2. rewrite EY in HX2. apply u32arr_app in HX2. destruct HX2 as [HXB HXC]. rewrite LP in HXC.
      apply u8arr_of_u32arr in HXB.
      pose proof (u32arr_ro _ _ _ _ HT) as HTro. rewrite <- (firstn_skipn (Z.to_nat an) tab), u32s_app in HTro.
      apply bytes_at_app in HTro. destruct HTro as [HTro _].
      assert (LF1 : length (firstn (Z.to_nat an) tab) = Z.to_nat an) by (rewrite firstn_length; clear - LTB Han HWS; lia).
      eapply (amemcpy_call X T (4 * an) _ _ m1 0x0a6408);
        [ exact HH1 | exact HXB | exact HTro | rewrite u32s_length, LP; clear - Han; lia | rewrite u32s_length, LF1; clear - Han; lia
        | exact OX | eapply aobj_sub; [exact OT| clear; lia| clear - Han HWS; lia]
        | clear - DXT Ln Han HWS HWL; lia | exact ST1 | exact MI1
        | clear - SX Ln Han; lia | clear - STT Ln Han HWS HWL; lia
        | pose proof (cw_top47 asegs R HIA h LB LF m1 _ X (4 * an) HH1 CWX ltac:(clear - Han; lia)) as Q; exact Q
        | pose proof (cw_top47 asegs R HIA h LB LF m1 _ T (4 * lt) HH1 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
        | clear - Han; lia | exact CWX | reflexivity | reflexivity | clear; lia | ].
      intros m2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MUc WMc MIc HDc STc HHc.
      apply u32arr_of_u8arr_u32s in HDc.
      assert (DJ : forall a n, (a + n <= X \/ X + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -176 <= a) ->
                disjoint_from [(X, X + 4 * an); (lo, bv_unsigned sp + -176)] a n).
      { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
      match goal with FRm : rw_cells asegs m1 (bv_unsigned sp + -176) _ |- _ =>
        apply (rw_cells_transport asegs _ m1 m2 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR2| apply DJ; simpl_sizes; clear - SX Ln Han SPR LO NEED0 LO0; lia] end.
      assert (MV : MINV m2 (firstn (Z.to_nat an) tab ++ skipn (Z.to_nat an) xs0) tab sel tmp).
      { unfold MINV.
        split; [apply u32arr_app; split; [exact HDc|]; rewrite LF1; eapply u32arr_transport; [exact HXC| exact MUc| exact WMc| apply DJ; rewrite skipn_length; clear - SX Ln Han L0 LO NEED0; lia]|].
        split; [rewrite length_app, Nat2Z.inj_add, LF1, skipn_length; clear - L0 Ln Han; lia|].
        split; [intros q Hq; rewrite nth_error_app2 by (rewrite LF1; exact Hq); rewrite LF1, nth_error_skipn; f_equal; clear - Hq; lia|].
        split; [eapply u32arr_transport; [exact HT| exact MUc| exact WMc| apply DJ; rewrite LTB; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LTB|].
        split; [eapply u32arr_transport; [exact HS| exact MUc| exact WMc| apply DJ; rewrite LS; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LS|].
        split; [eapply u32arr_transport; [exact HMm| exact MUc| exact WMc| apply DJ; rewrite LM; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LM|].
        split; [eapply u32arr_transport; [exact HL| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|].
        split; [eapply munch_trans; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; clear - Hx; tauto|];
                eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; clear - Hx LO NEED0; lia|].
        split; [eapply wmono_trans; [exact WM| exact WMc]|].
        split; [exact MIc|]. split; [exact STc| exact HHc]. }
      clear HX HT HS HMm HL MI1 ST1 HH1 HXB HXC HTro MU WM HDc MUc WMc.
      set (xs1 := firstn (Z.to_nat an) tab ++ skipn (Z.to_nat an) xs0) in *. clearbody xs1.
      (* [comment removed for export] *)
      dpose MV as (HX & LX1 & FX1 & HT & _ & HS & _ & HMm & _ & HL & MU & WM & MI & ST & HH).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with H1 : mem_inv asegs ?m3, H2 : stk asegs ?m3 lo _, H3 : HM _ _ _ h LB LF ?m3, H4 : u32arr asegs ?m3 X ?xs3, H5 : u32arr asegs ?m3 T _,
                          H6 : u32arr asegs ?m3 SEL _, H7 : u32arr asegs ?m3 TMP _, H8 : u32arr asegs ?m3 TLA _, MU3 : munch _ m ?m3, WM3 : wmono _ m ?m3,
                          FR3 : rw_cells asegs ?m3 (bv_unsigned sp + -176) _ |- _ =>
        eapply (body_walk (Z.to_nat (32 * en)) en 0 0 0 m3 xs3 tab sel tmp);
        [ unfold NUMS; clear - Hen HWS; lia | clear - Hen; lia
        | exact (conj H4 (conj LX1 (conj FX1 (conj H5 (conj LTB (conj H6 (conj LS (conj H7 (conj LM (conj H8 (conj MU3 (conj WM3 (conj H1 (conj H2 H3))))))))))))))
        | exact FR3 ] end.
      all: match goal with |- ?g => idtac "PRETAIL-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10354034516.161L12276447890.178L13043732721.161L19754568514.3  L21921318697.3  L26492581323.25 L28084711781.3  L29428324939.5  L29519831493.161L35653441506.7  L36972227160.159L48932718241.0  L52067443989.174L54429812362.178L55670780969.178L60098763854.3  L835807704.159  L8675610171.178 Q42451439483.162Q48476994811.162Q50851874968.162Q53365546520.16200001703Q04X04d05005i06506G07R07j08n08o0:i0;l0=20=<0>@0?@0@E0AJ0BA0C8S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk2HiS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2L03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB5welem2tl1k1i3sel3tmp2Hk2Hi2LS3AWiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk2HiS5welem1i2HiS5welem1i2HiS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWL1i3AWiS5welem1i2HiS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i3tab3sel3tmp2HkS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkSS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i3sel3tmp2Hk2Hi2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2Hk2Hi2K1S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2HkS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO5welem2tl1k1i3tab3sel3tmp2Hk2HiS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO5welem2tl1k1i3tab3sel3tmp2Hk2HiS2sp2lo3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS2sp2lo3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE LR DNT DET DRT DNX DEX ALN ALR AB NB EB RB SN SE SRR HN0 HE0 HR0 OX0 OA0 ON0 OE0 OR0 AMC T47A HWS HWL LTL OTL"] Lemma pre_loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pk,$34.Pi,$0.Pj,(1.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwcur,(2.&40.)Pwprev,(2.&40.)Pwcnt,(2.&40.)P,(8.$34.(2>.(38.Vwelem,R19.))R1:.)P,(15.(?.+2.R1:.)(16.R1:.Vwelem,))P,(8.(2.&40.)R5.(1>.&40.(10.VT,(32.+4.(32.Van,R1;.)))))P,(8.(2.&40.)R5.(1>.&40.(10.VT,(32.+4.(32.Van,(38.R1<.+1.))))))P,(8.(2.&40.)R5.(1>.&40.(38.Vwelem,R1=.)))P,(3?.R1<.R1;.R1:.R19.)P,(35.$5.R1=.(10.(12.&40.Vsp,)-;0.)(21.$36.(37.(1>.&40.(32.+4.(32.Vwelem,Van,))))(21.$36.(37.(1>.&40.=))(21.$36.(37.(1>.&40.VT,))(21.$36.(37.(1>.&40.VE,))(21.$36.(37.(1>.&40.Vws,))(21.$36.(40.#8.R1>.)(21.$36.(37.(1>.&40.VX,))(21.$36.(37.Vwmm,)(21.$36.(37.(1>.&40.VN,))(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.))))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1:.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R19.R18.R17.R:.(1>.&40.(10.VT,(32.+4.Van,)))R16.R15.R14.R13.R12.R11.R10.R?.(1>.&40.Vwelem,)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)R8.(1>.&40.Ven,)(1>.&40.(32.+4.Van,))(1>.&40.(10.VT,(32.+4.(32.Vwelem,Van,))))(1>.&40.=)(1>.&40.(10.VT,(32.+4.(10.(32.Vwelem,Van,)Van,))))R9.R>.R=.R<.R;.)VF,(1>.&40.+:63;<.)Vfc,(2:.(2.&40.))R1>.(2;.$5.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i j mm tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wcur wprev wcnt Hk Hi -> -> -> PV FR; [lia|].
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AWi : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      (* [comment removed for export] *)
      do 9 zstep.
      eapply (mm_call_tab i (i - 1) (T + 4 * an) (skipn (Z.to_nat an) tab) mm tab sel tmp 0x0a63e0 (fun mq => FRAMEB mq j));
        [ clear - Hi; lia | clear - Hi; lia | right; split; [reflexivity| split; [reflexivity| clear - Hi; lia]] | reflexivity | reflexivity | clear; lia
        | | exact PV | exact FR | ].
      { intros m1 m2 MUq WMq FRq. eapply rw_cells_transport; [exact FRq| exact MUq| exact WMq|].
        cbn [disjoint_from]. simpl_sizes. clear - STT Ln Han HWS HWL SPR LO NEED0 LO0 AWi. lia. }
      clear dependent mm. clear dependent tab. intros mm tab tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 PV FR.
      dpose PV as (HX2 & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact PV | exact FR].
      - eapply pre_tail_walk; [exact PV | exact FR].
      all: match goal with |- ?g => idtac "PRELOOP-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Loop.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03R0@C11386283792.209C17133037579.210D23904522630.209D35881667587.172D35881667587.174D35881667587.197D35881667587.208D35881667587.224D46522149398.197D67387923631.172D67387923631.174D67387923631.208D67387923631.224D8798035320.209 K24960274783.209K40484668124.172K40484668124.174K40484668124.197K40484668124.208K40484668124.224K42587433812.172K42587433812.174K42587433812.197K42587433812.208K42587433812.224K60443225391.172K60443225391.174K60443225391.197K60443225391.208K60443225391.224K62730101946.209K63069653654.210K67182834703.210K8081990310.172 K8081990310.174 L10362606196.198L10647043102.7  L10884122968.214L10884122968.236L11547569120.21 L11927462101.9  L11927529035.5  L12243415649.2  L12750296506.7  L14220071842.6  L14623972172.8  L15045215746.172L16078782184.2  L16342890722.2  L16347013912.3  L16384401652.164L16467615677.2  L16635876761.7  L18866009566.9  L19961711648.4  L20404769798.184L20681122052.236L20886524867.18 L21405751284.214L22383361691.21 L22760763246.174L23411732734.3  L23420628101.2  L23461856521.10 L23898603878.1  L24739615255.17 L24953049371.3  L24953833255.23 L26492728748.23 L26726870002.7  L27163225748.3  L27625049176.162L27625049176.185L27756658923.23 L2875907256.9   L29428324939.5  L29765679640.164L29765889648.161L30500770141.9  L32508069537.0  L32904787608.7  L32908981806.12 L32911014689.9  L33438479092.162L33735064744.9  L34354857587.3  L34972079987.23 L35084787414.7  L35653441506.7  L35735451399.6  L36972227160.164L36972227160.198L38062709726.2  L39172636981.0  L39188636933.0  L39220637093.0  L40269711107.187L40280805793.0  L403768116.9    L40485439768.3  L40485439770.3  L40485439771.3  L40485439773.3  L41216632490.7  L41422554759.170L42589383440.3  L43952631987.18 L465456788.9    L48038483326.18 L50663737752.23 L51433150352.18 L51632866479.149L51887855563.9  L51988059227.163L51989825952.235L51992236690.184L52418569136.185L57533285418.4  L57538479019.3  L57628700040.13 L58493925670.2  L59308546259.171L59308630497.3  L59488656116.1  L60098763854.3  L6039426548.1   L60439896503.5  L60444008939.5  L60444094443.5  L60444094446.5  L60549448800.7  L61453626589.6  L61690834259.21 L62730839678.4  L62730889342.4  L62743423010.4  L62744933058.21 L63075736182.2  L63079996654.23 L63157107674.3  L63157107803.7  L63157108714.3  L63471511624.8  L65088918924.2  L65357181960.21 L65372077406.14 L66000499105.0  L67182624712.2  L6882356298.1   L7450831556.1   L7454461363.187 L7742869216.23  L8077320871.3   L8171587126.182 L8171655512.185 L835807704.198  L926524850.0    L9685877192.2   P62730101946.209P67182834703.210Q11303243435.171Q12349038098.243Q12351150885.220Q14263382981.209Q18037037355.189Q20783692010.194Q23099095643.192Q23891856895.192Q23891870054.189Q23894295551.205Q23906540422.209Q25188298217.168Q25513505925.171Q25513505925.173Q25513505925.196Q25513505925.207Q25513505925.223Q26295627581.171Q26295627581.192Q266119562.171  Q26983366470.220Q26985478769.243Q2964607797.208 Q3008054787.192 Q311262240.193  Q32774307718.173Q32774632592.168Q32774732559.171Q38130921043.169Q38130921043.171Q38130921043.205Q38130921043.221Q39314856408.192Q39321195856.207Q42457809570.204Q44262837305.196Q44959437856.191Q44961171742.168Q45941463673.172Q45941463673.174Q45941463673.197Q45941463673.208Q45941463673.224Q48475269732.170Q48479301922.204Q49663838275.193Q49698585326.170Q49698585326.172Q49698585326.195Q49698585326.206Q49698585326.222Q50358700898.171Q50358700898.173Q50358700898.207Q50358700898.223Q50854878727.170Q50866505025.204Q53355140033.204Q54506349450.173Q5675839869.168 Q5677116483.191 Q57728971805.171Q66976989964.209Q66989661045.205Q8943687998.189 Q8943802936.168 00000100201702O03d05G06e08?0:Q0<X0>\0@i0C20E20FD0Gl0IS0K>0Lm0NX0Om0QA0Ra0T<0UU0WC0Y00Z`0\T0^E0_D0`N0`O0ae0c80d70dV0eU0f`0gH0gl0hC0hM0hk0iB0iX0jR0jX0j^0jh0kb0kl0lH0lh0m80m90o40o\10[11C12=12I12O13213514014114X15K15j16416n17m18418X18j1:Z1<J1<n1<o1=N1>51>Y1?S1@01@>1A11AP1Ah1B?1C91D81D>1D?1D@1DA1E@1EA1Ea1Eb1Ec1Ed1Ee1FC1G=1G>1Ge1HI1I11IX1J?1KI1Km1Ln1N=1OC1Q@1QP1QZ1R<1RB1TX1Tc1Tg1U11U51U61U71U81U91UX1Uo1VI1VJ1VK1VL1Vf1Vg1WZ1We1XC1XN1Xd1Xl1Y21Y[1Y\1Y]1Y`1Yd1Zc1[21[31]01^m1_l1_m1`51a@1aA1aj1c31d01e51f41ff1gT1hB1i01i^1jL1k<1l;1m91nC1oH20K21221^22M23?24=25F26E27B27k28T29=29j2:W2;I2<;2<o2=c2>`2@52A22Aj2C?2DS2Ej2GE2H\2IT2JQ2KC2L:2M12Mm2Ni2Oe2Po2R82SH2TV2UC2V52Vg2WW2XD2Y62Yf2Ze2[d2\P2]7FFS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab15Ha_stS1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP5welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB5welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB3SPR2AB2NB2EB2RB5welem4tab04sel04tmp02tl3LTB3LTL4tab15Ha_stS1X2an1T2lx2lt3xs02ys2ns2es2rs3ts03Han2L03DXT5welem4tab04sel04tmp02tl3LTB3LTL4tab1S1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel04tmp02tl3LTB3LTL2HB5Ha_st5Hl_stS1R5NEED02sp1N2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTB3LTL2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTL4tab14LTB12HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTL3v114tab24LTB22HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel02tl3LTL4tab34tmp34LTB32HB5Ha_st5Hl_stS1R5NEED02sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp1X1N2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp1X2an2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX5welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS1R5NEED02sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp1X1T2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel04tmp02tl3LTB3LTL2HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp1N2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTB3LTL2HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTB3LTL4tab12HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel04tmp02tl3LTB3LTL3v114tab22HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem4tab04sel02tl3LTB3LTL4tab34tmp32HB5Ha_st5Hl_st3LM32LSS2an1T3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S1R5NEED02sp1T2lt2lo3xs02ys2ns2es2rs3ts03LT02LO3STT4tab04sel04tmp02tl4tab1FS1R5NEED02sp1N2ln2lo3xs02ys2ns2es2rs3ts02LO2LN2ws4tab04sel04tmp02tl3SN'2HB5Ha_st5Hl_stS1R5NEED02sp1N2ln2lo3xs02ys2ns2es2rs3ts02LO2LN4tab04sel04tmp02tl3SN'2HB5Ha_st5Hl_stS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab2S2an3Han2ws5welem3HWS4tab14LTB1S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel02tl4tab34tmp3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel02tl4tmp32q02q12q24tab4S2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2an3Han5welem4tabr3LTRS2an5welemS2an3Han2ws5welem3HWS4tab03LTBS2an1T3Han2ws5welem3HWSS2sp2an1T2lo1a1n2D12D2S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2an1TS2an1TS2an1T3HanS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2an5welemS2an2lt3Han2ws5welem3HWS3HWLS2an1T2lt3Han2ws5welem3HWS3HWL1QS2en2ws5welem2HWFS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RB4tab04sel02tl4tmp32q02q12q24tab4S2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel02tl4tab34tmp3S2sp2an1T2lt2lo3Han3STT5welem3HWL2ws3HWSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2an1T5welemS2an1TS2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS1TS1A2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln2ws5welem3HWS3HWL4DAT'FS1X2an1T2lx2lt3Han3DXT2ws5welem3HWS3HWLS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2an3Han2ws5welem3HWS4tab34LTB3S2an1T3HanS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S2sp2loS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln2XB2TB3SPR2AB2NB2EB2RB4tab04sel04tmp02tlS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln2XB2TB3SPR2AB2NB2EB2RB4tab04sel04tmp02tlS2an2lt3ts03Han3LT02ws5welem3HWS3HWLSS2an3Han2ws5welem3HWS4tab34LTB3S2an2en2lx2la2ln3le_2lr2lt2ys3Han2Ln2LAS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2an2lt3ts03Han3LT05welem3HWLS2ws5welem3HWSS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2an3Han2ws5welem3HWS4tab34LTB3S1R3HIA1h2sp2lo3TOP4HTOPS2an1T3Han2ws5welem3HWSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab2S2an1TSSSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1SS2an1T2lt3Han2ws5welem3HWS3HWL1QFFFFS2an3Han2ws5welem3HWS4tab03LTBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlFS2sp1A2an1T2la2lt2lo5welem3HWL4DAT'3SA'S2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS1X2an1T2lx2lt3Han3DXT2ws5welem3HWS3HWLS2sp1N2an1T2ln2lt2lo5welem3HWL4DNT'3SN'S2ra2sp1X1A1N2an1E2en2RR1T2lt3xs02ys2ns2es2rs3ts02H01H2lx2la2ln3le_2lr3Ln'S2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han4tab04sel04tmp02tlS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han4tab04sel02tl4tmp32q02q12q24tab4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han4tab04sel04tmp02tl4tab1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem4tab04sel04tmp02tl3LTB3LTL4tab1S2an1T3Han5welemS2an1T3HanS2sp2an1T2lo2ws5welem3HWS1x2Hx3HanS2an1TS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln2L03LT03DXT2XB2TB3SPR2LO2SX3STT2LN2AB2NB2EB2RB4tab04sel04tmp02tl2N0S2en3H792KBS2anS1R2lo3LOSS2anFFFFS2an3Han2ws5welem3HWS4tab34LTB3S2an1T3Han2ws5welem3HWSS2an1T5welem2ws3HWS3Han2ltFFFS2an1T5welem3Han2ws3HWS2ltFS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2an2ys3LYAS2an3Han2ws5welem3HWS4tab03LTBS2an2q13LQ1S2sp2an1T2lo1a1n2D12D2S2an3HanS2an1TS2sp1A2an2en2lx2la2ln3le_2lr2lt2lo2Ln3SA'SFS1TS2anS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S2sp1X2lx2lo2SXFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem4tab04sel04tmp02tl3LTB3LTL4tab1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem4tab04sel04tmp02tl3LTB3LTL4tab1S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab2SS2an3HanS2an2en1T3xs02ys2ns2es2rs3ts03Han2ws5welem2HW3HWS4tab04sel04tmp02tl2LS4tab1FS1N3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts02LO4tab04sel02tl4tmp32q02q12q24tab4S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel02tl4tab34tmp3S2sp2an1T2lo3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S2an1T3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S2sp3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab12HBS1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1N2an3xs02ys2ns2es2rs3ts03Han4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl2HB5Ha_st5Hl_stS2sp1N2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl2HB5Ha_st5Hl_stS2sp2an2lo3xs02ys2ns2es2rs3ts05welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS2sp1T2lo3xs02ys2ns2es2rs3ts04tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1N2ln3xs02ys2ns2es2rs3ts02NB4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel02tl4tab34tmp3S2sp2an2lo3xs02ys2ns2es2rs3ts04tab04sel02tl4tmp32q02q12q24tab4S2an1T2lt3xs02ys2ns2es2rs3ts03Han2TB5welem4tab04sel04tmp02tl3LTB3LTL4tab1S2an1T3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl4tab1S1N3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS1N3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS1N3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2sp3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl2HBS2sp3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl2HBS2sp3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab22HBS2sp3xs02ys2ns2es2rs3ts04tab04sel02tl4tab34tmp32HBS1T2lt3xs02ys2ns2es2rs3ts02TB4tab04sel04tmp02tl4tab1S1T2lt3xs02ys2ns2es2rs3ts02TB4tab04sel04tmp02tl4tab1S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl4tab2S1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts02LO5welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl4tab1S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tlS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp1N2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem4tab04sel04tmp02tl4tab12HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl4tab2S2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S2sp3xs02ys2ns2es2rs3ts03SPR4tab04sel04tmp02tl2HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR4tab04sel04tmp02tl2HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR4tab04sel04tmp02tl4tab12HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR4tab04sel04tmp02tl4tab22HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR4tab04sel02tl4tab34tmp32HB5Ha_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp1N2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl2HB5Ha_st5Hl_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp1T2lo3xs02ys2ns2es2rs3ts02LO4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab2S2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab2S1N2an3xs02ys2ns2es2rs3ts03Han4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S1N2an3xs02ys2ns2es2rs3ts03Han4tab04sel04tmp02tlS2an1T3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S2an1T3xs02ys2ns2es2rs3ts03Han5welem4tab04sel04tmp02tl3LTB4tab1S3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl4tab1S3xs02ys2ns2es2rs3ts04tab04sel04tmp02tl". (* [comment removed for export] *)
  #[using="IMG NEED0 MM lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LA LN LE LR DAT DNT DET DRT DNX DEX ALN ALR AB NB EB RB SA SN SE SRR HN0 HE0 HR0 HA0 OX0 OA0 ON0 OE0 OR0 AMS AMC T47A"] Lemma setup_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pws,$0.Pwelem,$0.Pmm,P,(2.&40.)(3.(2.&8.))Pj0,(1.(2.&8.))Pj16,(1.(2.&8.))Pj32,(1.(2.&8.))Pj64,(1.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pys1,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pys7,(2.&40.)Pys8,(2.&40.)Pys10,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(>.(15.(8.$0.R19.+1.)(15.(8.$0.R18.+2.)(?.(32.Ven,+20.)+4?.)))(15.(8.$0.R19.+3.)(15.(8.$0.R18.+8.)(?.+50.(32.Ven,+20.)))))P,(30.$5.R18.VX,Vxs0,)P,(30.$5.R19.VT,Vts0,)P,(20.(21.(22.$0.$0.)(23.$0.$0.VT,(10.VT,(32.+4.(10.(10.(32.R1;.Van,)Van,)(10.(32.+2.Van,)+1.)))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(12.&40.Vsp,))(24.(22.$0.$0.))))Vm,R1:.)P,(25.$5.Vm,R1;.)P,(13.$5.R1<.)P,(11.$5.R1=.Vlo,(10.(12.&40.Vsp,)-;0.))P,(4.$5.VR,VHIA,Vh,VLB,VLF,R1>.)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)Vm,VT,(32.+4.(10.(10.(32.R20.Van,)Van,)(10.(32.+2.Van,)+1.))))P,(35.$5.R20.(10.(12.&40.Vsp,)-;0.)(21.$36.(40.#8.R1?.)(21.$36.(37.(1>.&40.=))(21.$36.(40.#8.R1>.)(21.$36.(37.(1>.&40.VE,))(21.$36.(40.#10.R1=.)(21.$36.(37.(1>.&40.VX,))(21.$36.(37.(1>.&40.VRR,))(21.$36.(40.#8.R1<.)(21.$36.(37.Vs11,)(21.$36.(37.Vs10,)(21.$36.(37.Vs9,)(21.$36.(37.Vs8,)(21.$36.(37.Vs7,)(21.$36.(37.Vs6,)(21.$36.(37.Vs5,)(21.$36.(37.Vs4,)(21.$36.(37.Vs3,)(21.$36.(37.Vs2,)(21.$36.(37.Vs1,)(21.$36.(37.Vs0,)(21.$36.(37.Vra,)(24.$36.)))))))))))))))))))))))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.R1<.(1>.&40.(10.(12.&40.Vsp,)-;0.))Vgp,Vtp,R1;.R1:.R19.(1>.&40.(32.Ven,+20.))R18.(1>.&40.R23.)R17.R16.R15.R14.(1>.&40.VN,)R13.R12.(1>.&40.+1.)(1>.&40.(39.(<.VR,)))(1>.&40.Van,)(1>.&40.VT,)(1>.&40.Ven,)R11.R10.(1>.&40.=)R?.(1>.&40.VA,)R>.R=.R<.R;.)VF,(1>.&40.+:62<8.)Vfc,(2:.(2.&40.))R21.(2;.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HW HX HT MU WM MI ST HH OTL FR. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    assert (HWS : (ws = 1 /\ welem = 2) \/ (ws = 3 /\ welem = 8)) by (clear - HW; lia).
    assert (HWL : welem * an + an + (2 * an + 1) <= lt).
    { pose proof Ln as Ln'. unfold exp_mod_working_limbs, exp_mod_welem in Ln'. destruct (Z.ltb_spec 79 (32 * en)); destruct HW as [(_ & -> & ?)|(_ & -> & ?)]; lia. }
    (* [comment removed for export] *)
    destruct (u32arr_take _ _ _ _ (Z.to_nat (welem * an)) HT ltac:(clear - LT0 HWL HWS Han; lia)) as [HTAB HR1].
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HR1 ltac:(clear - LT0 HWL HWS Han; rewrite skipn_length; lia)) as [HS HR2]. clear HR1.
    destruct (u32arr_take _ _ _ _ (Z.to_nat (2 * an + 1)) HR2 ltac:(clear - LT0 HWL HWS Han; rewrite !skipn_length; lia)) as [HMm HL]. clear HR2.
    rewrite !skipn_skipn in HL. rewrite skipn_skipn in HMm.
    replace (T + 4 * Z.of_nat (Z.to_nat (welem * an))) with (T + 4 * (welem * an)) in HS, HMm, HL by (clear - HWS Han; lia).
    replace (T + 4 * (welem * an) + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * (welem * an + an)) in HMm, HL by (clear - Han; lia).
    replace (T + 4 * (welem * an + an) + 4 * Z.of_nat (Z.to_nat (2 * an + 1))) with (T + 4 * (welem * an + an + (2 * an + 1))) in HL by (clear - Han; lia).
    lazymatch type of HTAB with u32arr _ _ _ ?l => set (tab0 := l) in HTAB end.
    lazymatch type of HS with u32arr _ _ _ ?l => set (sel0 := l) in HS end.
    lazymatch type of HMm with u32arr _ _ _ ?l => set (tmp0 := l) in HMm end.
    lazymatch type of HL with u32arr _ _ _ ?l => set (tl := l) in HL end.
    assert (LTB : Z.of_nat (length tab0) = welem * an) by (subst tab0; clear - LT0 HWL HWS Han; rewrite firstn_length; lia).
    assert (LS : Z.of_nat (length sel0) = an) by (subst sel0; clear - LT0 HWL HWS Han; rewrite firstn_length, skipn_length; lia).
    assert (LM : Z.of_nat (length tmp0) = 2 * an + 1) by (subst tmp0; clear - LT0 HWL HWS Han; rewrite firstn_length, skipn_length; lia).
    assert (LTL : Z.of_nat (length tl) = lt - (welem * an + an + (2 * an + 1))) by (subst tl; clear - LT0 HWL HWS Han; rewrite skipn_length; lia).
    clearbody tab0 sel0 tmp0 tl. clear HT.
    destruct (objs_pre welem OTL _ HH MU) as (OX & OA & ON & OR & OT).
    pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'.
    pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNT' SN' Ln HWL Han; lia)) as HN.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk ON N 4.
    (* [comment removed for export] *)
    zstep. rd HN 0. clear HN.
    (* [comment removed for export] *)
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. replace (an * 4) with (4 * an) by (clear; lia).
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HTAB ltac:(clear - LTB HWS Han; lia)) as [HT0 HT1].
    apply u8arr_of_u32arr in HT0.
    lazymatch type of HT1 with u32arr _ _ _ ?l => set (tabr := l) in HT1 end.
    assert (LTR : Z.of_nat (length tabr) = welem * an - an) by (subst tabr; rewrite skipn_length; clear - LTB HWS Han; lia). clearbody tabr.
    replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in HT1 by (clear - Han; lia). clear HTAB.
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo _, H3 : HM _ _ _ h LB LF ?m2 |- _ =>
      rename H1 into MI1; rename H2 into ST1; rename H3 into HH1; rename m2 into m1 end.
    eapply (amemset_call T (4 * an) _ m1 0x0a62f8);
      [ exact HH1 | exact HT0 | rewrite u32s_length, firstn_length; clear - LTB HWS Han; lia
      | eapply aobj_sub; [exact OT| clear; lia| clear - Han HWS; lia] | exact ST1 | exact MI1
      | clear - STT Ln Han HWS HWL; lia
      | pose proof (cw_top47 asegs R HIA h LB LF m1 _ T (4 * lt) HH1 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
      | clear - Han; lia | intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia | reflexivity | reflexivity | clear; lia | ].
    intros m2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MUc WMc MIc HDc STc HHc.
    apply (rw_cells_of_u8arr asegs) in HDc. rewrite repeat_length in HDc.
    apply (u32arr_of_cells asegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat an))) in HDc; [| rewrite u32s_repeat0; f_equal; clear - Han; lia].
    assert (DJ : forall a n, (a + n <= T \/ T + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -176 <= a) ->
              disjoint_from [(T, T + 4 * an); (lo, bv_unsigned sp + -176)] a n).
    { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
    eapply u32arr_transport in HX; [| exact MUc| exact WMc| apply DJ; rewrite L0; clear - DXT SX Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HT1; [| exact MUc| exact WMc| apply DJ; rewrite LTR; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HS; [| exact MUc| exact WMc| apply DJ; rewrite LS; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HMm; [| exact MUc| exact WMc| apply DJ; rewrite LM; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HL; [| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - STT Ln Han HWS HWL LO NEED0; lia].
    match goal with FRm : rw_cells asegs m1 (bv_unsigned sp + -176) _ |- _ =>
      apply (rw_cells_transport asegs _ m1 m2 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR2| apply DJ; simpl_sizes; clear - STT Ln Han HWS HWL SPR LO NEED0 LO0; lia] end.
    assert (MU2 : munch [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x Hx; cbn [outside] in *; clear - Hx Han HWS LO NEED0; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM2. clear MU WM. rename MU2 into MU. rename WM2 into WM.
    assert (HTAB : u32arr asegs m2 T (repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr)).
    { apply u32arr_app. split; [exact HDc|]. rewrite repeat_length. replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) by (clear - Han; lia). exact HT1. }
    assert (LTB1 : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr)) = welem * an) by (rewrite length_app, repeat_length; clear - LTR Han; lia).
    set (tab1 := repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr) in *. clearbody tab1. clear HDc HT1 LTR HT0 MUc WMc MI1 ST1 HH1 OX OA ON OR OT. clear tabr.
    destruct (objs_pre welem OTL _ HHc MU) as (OX & OA & ON & OR & OT).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OT T 4.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    assert (EW1 : Z.shiftl 1 ((ws mod 18446744073709551616) mod 64) = welem) by (destruct HWS as [[-> ->]|[-> ->]]; reflexivity).
    assert (EW2 : Z.shiftl an ((ws mod 18446744073709551616) mod 64) = welem * an).
    { destruct HWS as [[-> ->]|[-> ->]]; [change ((1 mod 18446744073709551616) mod 64) with 1| change ((3 mod 18446744073709551616) mod 64) with 3];
        rewrite Z.shiftl_mul_pow2 by (clear; lia); [change (2^1) with 2| change (2^3) with 8]; clear; lia. }
    rewrite EW1, EW2. clear EW1 EW2.
    (* [comment removed for export] *)
    vstep 11%positive. zstep. zstep.
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2^2) with 4. replace (welem * an * 4) with (4 * (welem * an)) by (clear; lia).
    vstep 11%positive. zstep. zstep.
    (* [comment removed for export] *)
    vstep 11%positive. vstep 11%positive. vstep 10%positive. vstep 10%positive. vstep 10%positive. vstep 11%positive. vstep 12%positive.
    zstep. replace (T + 4 * (welem * an) + 4 * an) with (T + 4 * (welem * an + an)) by (clear; lia).
    vstep 10%positive. vstep 11%positive. vstep 11%positive. vstep 16%positive.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok asegs _ T tab1 0 _ HTAB ltac:(clear - LTB1 Han HWS; lia) ltac:(f_equal; clear; lia)) as SOK.
    replace (T + 4 * 0) with T in SOK by (clear; lia).
    zstep.
    lazymatch goal with |- context [write_to_mem ?mq _ (le4 ?v)] =>
      pose proof (u32arr_write asegs mq T tab1 0 v HTAB ltac:(clear - LTB1 Han HWS; lia)) as HX';
      replace (T + 4 * 0) with T in HX' by (clear; lia);
      store_done; try clear HTAB; rename HX' into HTAB;
      assert (LTB2 : Z.of_nat (length (upd tab1 (Z.to_nat 0) v)) = welem * an) by (rewrite upd_length; exact LTB1);
      set (tab2 := upd tab1 (Z.to_nat 0) v) in *; clearbody tab2; clear LTB1; try clear tab1
    end.
    (* [comment removed for export] *)
    do 9 zstep.
    replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 4 * (an * 0))) by (f_equal; clear; lia).
    lazymatch goal with FRq : rw_cells asegs ?mq (bv_unsigned sp + -176) ?cells, H1 : mem_inv asegs ?mq, H2 : stk asegs ?mq lo _, H3 : HM _ _ _ h LB LF ?mq |- _ =>
      eapply (mm_call_tab ws welem tl HWS HWL LTL OTL 0 0 RR rs mq tab2 sel0 tmp0 0x0a6388 (fun mz => rw_cells asegs mz (bv_unsigned sp + -176) cells));
        [ clear - HWS; lia | clear - HWS; lia | left; split; reflexivity | reflexivity | reflexivity | clear; lia
        | | exact (conj HX (conj HTAB (conj LTB2 (conj HS (conj LS (conj HMm (conj LM (conj HL (conj MU (conj WM (conj H1 (conj H2 H3)))))))))))) | exact FRq | ] end.
    { intros mz1 mz2 MUq WMq FRq. eapply rw_cells_transport; [exact FRq| exact MUq| exact WMq|].
      cbn [disjoint_from]. simpl_sizes. clear - STT Ln Han HWS HWL SPR LO NEED0 LO0. lia. }
    clear HX HTAB LTB2 HS HMm HL MU WM OX OA ON OR OT. clear dependent tab2. clear dependent tmp0.
    lazymatch goal with |- forall _, _ => idtac end.
    intros m3 tab3 tmp3 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 PV FR3.
    replace (T + 4 * (an * 0)) with T by (clear; lia).
    dpose PV as (HX & HTAB & LTB3 & HS & _ & HMm & LM3 & HL & MU & WM & MI3 & ST3 & HH3).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    clear PV. try clear FR2.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    lazymatch goal with H1 : mem_inv asegs m4, H2 : stk asegs m4 lo _, H3 : HM _ _ _ h LB LF m4 |- _ => rename H1 into MI4; rename H2 into ST4; rename H3 into HH4 end.
    destruct (objs_pre welem OTL _ HH4 MU) as (OX & OA & ON & OR & OT).
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HTAB ltac:(clear - LTB3 HWS Han; lia)) as [Q0 QR].
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) QR ltac:(rewrite skipn_length; clear - LTB3 HWS Han; lia)) as [Q1 Q2]. clear QR.
    apply u8arr_of_u32arr in Q1.
    replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in Q1, Q2 by (clear - Han; lia).
    replace (T + 4 * an + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * (an + an)) in Q2 by (clear - Han; lia).
    lazymatch type of Q0 with u32arr _ _ _ ?l => set (q0 := l) in Q0; assert (LQ0 : Z.of_nat (length q0) = an) by (subst q0; rewrite firstn_length; clear - LTB3 HWS Han; lia); clearbody q0 end.
    lazymatch type of Q2 with u32arr _ _ _ ?l => set (q2 := l) in Q2; assert (LQ2 : Z.of_nat (length q2) = welem * an - an - an) by (subst q2; rewrite !skipn_length; clear - LTB3 HWS Han; lia); clearbody q2 end.
    lazymatch type of Q1 with u8arr _ _ _ (u32s ?l) => set (q1 := l) in Q1; assert (LQ1 : Z.of_nat (length q1) = an) by (subst q1; rewrite firstn_length, skipn_length; clear - LTB3 HWS Han; lia); clearbody q1 end.
    clear HTAB LTB3.
    pose proof (unlock _ DAT) as DAT'. pose proof (unlock _ SA) as SA'.
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; clear - DAT' SA' Ln HWL Han; lia)) as HA.
    rewrite <- (firstn_skipn (Z.to_nat an) ys), u32s_app in HA. apply bytes_at_app in HA. destruct HA as [HA _].
    assert (LYA : Z.of_nat (length (firstn (Z.to_nat an) ys)) = an) by (rewrite firstn_length; clear - LA Ln Han; lia).
    eapply (amemcpy_call (T + 4 * an) A (4 * an) _ _ m4 0x0a63a0);
      [ exact HH4 | exact Q1 | exact HA | rewrite u32s_length; clear - LQ1; lia | rewrite u32s_length; clear - LYA; lia
      | eapply aobj_sub; [exact OT| clear - Han; lia| clear - Han HWS; lia] | exact OA
      | clear - DAT' Ln Han HWS HWL; lia | exact ST4 | exact MI4
      | clear - STT Ln Han HWS HWL; lia | clear - SA' Ln Han; lia
      | pose proof (cw_top47 asegs R HIA h LB LF m4 _ T (4 * lt) HH4 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
      | exact T47A
      | clear - Han; lia | intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia | reflexivity | reflexivity | clear; lia | ].
    try clear MIc STc HHc.
    intros m5 yt0' yt1' yt2' ya0' ya1' ya2' ya3' ya4' ya5' ya6' ya7' yt3' yt4' yt5' yt6' MUc WMc MIc HDc STc HHc.
    apply u32arr_of_u8arr_u32s in HDc.
    assert (DJ2 : forall a n, (a + n <= T + 4 * an \/ T + 4 * an + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -176 <= a) ->
              disjoint_from [(T + 4 * an, T + 4 * an + 4 * an); (lo, bv_unsigned sp + -176)] a n).
    { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
    eapply u32arr_transport in HX; [| exact MUc| exact WMc| apply DJ2; rewrite L0; clear - DXT SX Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in Q0; [| exact MUc| exact WMc| apply DJ2; rewrite LQ0; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in Q2; [| exact MUc| exact WMc| apply DJ2; rewrite LQ2; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HS; [| exact MUc| exact WMc| apply DJ2; rewrite LS; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HMm; [| exact MUc| exact WMc| apply DJ2; rewrite LM3; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HL; [| exact MUc| exact WMc| apply DJ2; rewrite LTL; clear - STT Ln Han HWS HWL LO NEED0; lia].
    match goal with FRm : rw_cells asegs m4 (bv_unsigned sp + -176) _ |- _ =>
      apply (rw_cells_transport asegs _ m4 m5 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR5| apply DJ2; simpl_sizes; clear - STT Ln Han HWS HWL SPR LO NEED0 LO0; lia] end.
    assert (MU5 : munch [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m m5).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x Hx; cbn [outside] in *; clear - Hx Han HWS LO NEED0; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM5. clear MU WM.
    assert (HTAB : u32arr asegs m5 T (q0 ++ firstn (Z.to_nat an) ys ++ q2)).
    { apply u32arr_app. split; [exact Q0|]. apply u32arr_app. split.
      - rewrite LQ0. exact HDc.
      - rewrite LQ0, LYA. replace (T + 4 * an + 4 * an) with (T + 4 * (an + an)) by (clear; lia). exact Q2. }
    assert (LTB4 : Z.of_nat (length (q0 ++ firstn (Z.to_nat an) ys ++ q2)) = welem * an) by (rewrite !length_app, !Nat2Z.inj_add, LQ0, LYA, LQ2; clear; lia).
    set (tab4 := q0 ++ firstn (Z.to_nat an) ys ++ q2) in *. clearbody tab4.
    assert (PV5 : PINV welem tl m5 tab4 sel0 tmp3) by (exact (conj HX (conj HTAB (conj LTB4 (conj HS (conj LS (conj HMm (conj LM3 (conj HL (conj MU5 (conj WM5 (conj MIc (conj STc HHc))))))))))))).
    clear HDc Q0 Q1 Q2 HA MUc WMc MI4 ST4 HH4 OX OA ON OR OT.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear - Hen; lia).
    - (* [comment removed for export] *)
      destruct HW as [(-> & -> & H79)|(-> & -> & H79)]; [| exfalso; clear - KB H79; lia].
      eapply (pre_tail_walk 1 2 _ tl ltac:(left; split; reflexivity) HWL LTL OTL); [exact PV5 | exact FR5].
    - (* [comment removed for export] *)
      destruct HW as [(-> & -> & H79)|(-> & -> & H79)]; [exfalso; clear - KB H79; lia|].
      zstep. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2^3) with 8. zstep. zstep. zstep. zstep.
      eapply (pre_loop_walk 3 8 _ tl ltac:(right; split; reflexivity) HWL LTL OTL 6 2); [reflexivity | clear; lia | f_equal; clear; lia | f_equal; clear; lia | f_equal; clear; lia | exact PV5 | exact FR5].
    all: match goal with |- ?g => idtac "SETUP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01d0@D35881667587.137D67387923631.137K40484668124.137K42587433812.137L10362606196.130L13496871640.130L14401364312.130L15380150644.130L1685717371.0   L1740955736.130 L17566313688.130L17777983920.129L20681125023.130L22412115316.130L27417060468.130L28081971108.4  L28422376436.130L29428324939.5  L30238256600.130L30930650740.130L31144453208.130L3174820682.4   L31844853592.130L34316152792.130L34447988852.130L35653441506.7  L36957836532.130L39284637285.0  L40458843892.130L40500118168.3  L40834179097.132L42589383440.3  L42966524276.130L43061724204.131L43467180248.130L45476453876.130L46489027444.130L46968692952.130L47816909591.126L48994238452.130L49641679704.130L52271955174.133L52499960308.130L53719510360.130L55007644788.130L60098763854.3  L60200242136.130L61035354868.130L63718073304.130L66374151768.130L6660460841.126 L67045685108.130L67937894104.130L835807704.130  Q1067133538.135 Q15643324129.133Q18235909853.135Q18365925601.133Q18378753154.133Q18694146040.135Q21384638156.135Q21798041355.135Q21879645826.133Q21962771306.135Q24389563138.133Q25157988860.135Q25513505925.136Q25662358575.135Q27584944865.133Q27907200258.133Q29505479905.133Q30415036802.133Q31228709292.135Q31271525473.133Q31394594844.135Q32655500769.133Q33918256002.133Q34800357606.135Q34819330273.133Q35014437530.135Q35717497884.135Q36425882626.133Q38130921043.134Q3830427394.133 Q38933719170.133Q39939554818.133Q41152393185.133Q4143427880.135 Q42453453442.133Q44648843873.133Q45217673672.135Q4533518817.133 Q45941463673.137Q47797448393.135Q48731712993.133Q49698585326.135Q50358700898.136Q51235796833.133Q51371168465.135Q52101170785.133Q53367561185.133Q53969758199.135Q54057591853.135Q54485784450.133Q56993619970.133Q59256763233.133Q59843137889.133Q60511257090.133Q61802139820.135Q63333173345.133Q6338050946.133 Q6416456232.135 Q64255486968.135Q66277404438.135Q66522067074.133Q9843367298.133 00001Y04105c07Q08908a09I0:10:20:Z0;B0<10=I0>10>Y0>j0?R0?d0@L0A40A\0Am0BU0C=0Ce0D=0De0Df0EN0EO0F90F:0Fb0HA0Hi0IQ0J90Ja0KN0L60L^0MF0Mn0NV0O>0OH0P00PX0Q@0Qh0RU0S=0Se0TM0TN0Ti0Tj0UE0Uk0VG0VH0VI0Vo0W00WV0X20YL0YM0Yh0ZN0Zi0[O0[l0\G0\\0]70]]0]^0^90^V0^W0_=0_X0`>0`d0aJ0ae0af0bL0bg0bh0cC0e30e40eO0f40gY0h40h50hP0hk0iH0iI0io0jU0k00kK0l10l20lM0m30mO0mP0mQ0n70n]S1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp1T2lt2lo3xs02ys2ns2es2rs3ts03LT02LO3STT2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1E2RRS1R5NEED02ra2sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111E2RRS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0SS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts03HenS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2en5welem3HWE2KWS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2en5welem3HWE2KWS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0SS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0FS1R2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0FS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2LO2AB2NB2EB2RBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts01HS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts01HS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0FS2sp2lo3xs02ys2ns2es2rs3ts0FS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R3xs02ys2ns2es2rs3ts04IMG'FFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R3xs02ys2ns2es2rs3ts04IMG'S2ra2sp2lo3xs02ys2ns2es2rs3ts02HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1E2RRFS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R3xs02ys2ns2es2rs3ts05ALWF'S2sp2lo3xs02ys2ns2es2rs3ts0S3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS2sp2lo3xs02ys2ns2es2rs3ts0S1R3xs02ys2ns2es2rs3ts05ALWF'FS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp3xs02ys2ns2es2rs3ts02HBS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0FS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0FS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02ra2sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1E2RRFS2sp2lo3xs02ys2ns2es2rs3ts0S2sp3xs02ys2ns2es2rs3ts03SPR2HB5Ha_stS1R5NEED02ra2sp2lo3xs02ys2ns2es2rs3ts02LO2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1E2RRS2sp2lo3xs02ys2ns2es2rs3ts0FS2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R3xs02ys2ns2es2rs3ts05ALWF'FS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R3xs02ys2ns2es2rs3ts04IMG'FFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO". (* [comment removed for export] *)
  #[using="IMG NEED0 MM lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LA LN LE LR DAT DNT DET DRT DNX DEX ALN ALR AB NB EB RB SA SN SE SRR HN0 HE0 HR0 HA0 OX0 OA0 ON0 OE0 OR0 AMS AMC T47A"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(30.$5.Vm,VX,Vxs0,)P,(30.$5.Vm,VT,Vts0,)P,(13.$5.Vm,)P,(11.$5.Vm,Vlo,(12.&40.Vsp,))P,(4.$5.VR,VHIA,Vh,VLB,VLF,Vm,)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)Vm,VT,(32.+4.(41.Van,Ven,)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(1>.&40.VX,)(1>.&40.VA,)(1>.&40.VN,)(1>.&40.Van,)(1>.&40.VE,)(1>.&40.Ven,)(1>.&40.VRR,)(1>.&40.VT,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(1>.&40.+:6128.)Vfc,(2:.(2.&40.))Vm,(2;.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX HT MI ST HH OT0. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    set (welem := exp_mod_welem en).
    assert (HWE : (welem = 2 /\ en * 32 <= 79) \/ (welem = 8 /\ 80 <= en * 32)).
    { subst welem. unfold exp_mod_welem. destruct (Z.ltb_spec 79 (32 * en)); [right| left]; split; try reflexivity; lia. }
    assert (OTL : aobj asegs AL CS m T (4 * (welem * an + an + (2 * an + 1)))) by exact OT0.
    clearbody welem. clear OT0.
    pose proof (munch_refl [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lazymatch goal with |- evtA ?sg ?al ?cs ?P (MS ?Rg ?FF ?pc ?fcc ?rv m ?ro) =>
      enough (G : forall mm, mm = m -> evtA sg al cs P (MS Rg FF pc fcc rv mm ro)) by exact (G m eq_refl) end.
    intros mm Emm. rewrite <- Emm in HX, HT, MI, ST, HH. rewrite <- Emm in MU at 2. rewrite <- Emm in WM at 2. clear Emm.
    pose proof (hm_abase asegs R HIA h LB LF mm HH) as ABS.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    carve_frame 176%nat ST.
    (* [comment removed for export] *)
    do 14 zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (abase_got _ _ _ ABS) as GOT. pose proof (abase_gsb _ _ _ ABS) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2^5) with 32.
    zstep. zstep.
    zstep. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by (clear - Hen; lia);
      [ (* [comment removed for export] *) zstep | (* [comment removed for export] *) zstep; zstep ].
    - lazymatch goal with FR' : rw_cells asegs ?m2 (bv_unsigned sp + -176) _ |- _ =>
        eapply (setup_walk 3 welem m2); [right; clear - HWE KW; lia | | | exact MU | exact WM | | | | exact OTL | exact FR'] end;
        assumption.
    - lazymatch goal with FR' : rw_cells asegs ?m2 (bv_unsigned sp + -176) _ |- _ =>
        eapply (setup_walk 1 welem m2); [left; clear - HWE KW; lia | | | exact MU | exact WM | | | | exact OTL | exact FR'] end;
        assumption.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L11401030561.115L1316427937.115 L27951960317.115L3229129457.115 L56527267681.115L63432074286.115L64599781253.11500000a01R02C03403e04g05XS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZE2ET3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZT2TT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZN2NT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZA2AT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZX2XT3SPRS2ra2sp1X1A1N2an1E2en2RR1T2xs2ys2ns2es2rs2ts2LX2LA2LN2LE2LR2LT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZR2RT3SPR". (* [comment removed for export] *)
Theorem A_mpi_core_exp_mod_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PR,$42.PHIA,(43.$5.R1.)P,(44.(<.R2.))P,(8.$0.(45.R3.)$2?.)P,(8.$0.(46.R4.)$2<.)P,(?.=(47.R5.))(48.$5.R6.R5.$49.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS AMC NEED0. pose proof (A_mpi_core_montmul_spec R HIA IMG AMS NEED0) as MM.
  unfold mpi_core_exp_mod_stmtA, A_MPI_CORE_EXP_MOD.
  intros until ts. intros HH PRE LOS SLO TOP CWX CWT OX OA ON OE OR OT T47 -> -> -> -> -> -> -> ->.
  unfold mpi_core_exp_mod_pre, MPI_CORE_EXP_MOD_STACK in PRE. expmod_pre PRE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  eapply main_walk with (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (ln := Z.of_nat (length ns)) (le_ := Z.of_nat (length es))
                         (lr := Z.of_nat (length rs)) (lt := Z.of_nat (length ts)) (ys := ys) (ns := ns) (es := es) (rs := rs);
    try eassumption; try reflexivity; try (apply lock; assumption); try lia.
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

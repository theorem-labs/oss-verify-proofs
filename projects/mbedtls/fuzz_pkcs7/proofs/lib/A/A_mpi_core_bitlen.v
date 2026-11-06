(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_bitlen.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_core_bitlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_BITLEN_STACK_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "mpi_core_bitlen_postA"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.log2"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Mem.sx32"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen_rec"; "OSSVerify.KrLib.LibA.ALazy.al_sb"].


Definition A_MPI_CORE_BITLEN : Z := 0x0a3ee4.
Definition MPI_CORE_BITLEN_STACK_A : Z := 16.

Definition mpi_core_bitlen_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O17.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O15.)$12.)(11.&40.O15.))(13.(=.$>.$>.)))O1.R1.)(4.(14.O17.O1.R1.)(4.(15.O17.R1.)(4.(5.(2.&40.)R=.(16.&40.(17.O4.O3.)))(18.O17.R1.O2.(11.&40.O15.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_bitlen_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Pn,$>.Plo,$>.Pxs,(1:.(2.&40.))P,(1;.O3.R5.R4.(1<.R1.))P,(4.(1=.=R4.)(1=.R4.+2710.))P,(1=.R5.(1>.(1?.(2.&40.)R3.)))P,(5.$>.(20.R7.+4.)=)P,(21.=R8.)P,(15.O3.R:.)P,(22.O2.)P,(23.O2.R2>.)P,(24.O3.O2.R=.)P,(25.O3.O2.R30.R>.R=.(26.+4.R<.))P,(18.O3.R?.R<.(11.&40.R2?.))P,(1=.R=.(10.(11.&40.R30.)$12.))P,(5.$>.(20.(11.&40.R31.)+10.)=)P,(27.R34.R?.(10.(11.&40.R32.)R?.))P,(28.(1=.(29.R12.(26.+4.(1>.(1?.(2.&40.)R?.))))(10.(11.&40.R33.)$12.))(1=.(11.&40.R33.)R12.))P,(5.(2.&40.)R2<.(16.&40.R13.))P,(5.(2.&40.)R2<.(16.&40.R13.))(2:.O3.O2.R38.(2;.O3.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R12.R14.R13.R16.)(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(16.&40.O1.)R17.(9.(2.&40.))R16.(:.O3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_core_bitlen_z_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Plo,$>.P,(15.O3.R3.)P,(4.(1=.=R3.)(21.R3.(2<.+2.+40.)))P,(22.O2.)P,(23.O2.R28.)P,(24.O3.O2.R7.)P,(18.O3.R8.R6.(11.&40.R28.))P,(1=.R7.(10.(11.&40.R29.)$12.))P,(5.$>.(20.(11.&40.R2:.)+10.)=)P,(27.R2=.R9.(10.(11.&40.R2;.)R9.))P,(5.(2.&40.)R24.(16.&40.R;.))P,(5.(2.&40.)R24.(16.&40.=))(2:.O3.O2.R30.(2;.O3.R2?.R2>.R2=.R2<.R28.R27.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R10.R?.(13.(2.&40.))=R<.R>.)(6.(7.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(16.&40.O1.)R?.(9.(2.&40.))R>.(:.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n lo : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SA : A + 4 * Z.of_nat (length xs) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_bitlen_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L14935779467.66L15475369355.68L31399144472.68L32049487064.69L3830364018.69 L46933721732.69L59589536811.66Q15643391633.69Q9843295730.69 00000100=00H00S00e01:01B01L01ZFS1A2xs1w1r1bS2sp1A2xs1wS2sp1A2xs1wS2sp1A2lo2xs3SLO1wS1A1n2xs2Hn2XB1w1r2HrS1A2xs1wS2sp2lo2xsS2sp2lo2xs3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK A Hn XB LO0 SLO SCS SPR"] Lemma clz_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "Pw,(2.&40.)Px,$>.Pr,$>.Px10,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pw11,(2.&40.)Pjunk,(1:.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(5.$>.R;.(20.(11.&40.R<.)(2<.+2.+20.)))P,(2=.(5.$>.R<.=))P,(4.(1=.+1.R<.)(1=.R<.Vn,))P,(5.$>.(17.Vxs,Vn,)(29.(29.(26.+20.(10.R=.+1.))(2>.R>.))+1.))P,(5.(2.&40.)R7.(16.&40.(26.+20.R>.)))P,(2?.$30.R6.(29.(11.&40.Vsp,)-10.)(<.$31.(32.#8.R7.)(<.$31.(33.Vra,)(13.$31.))))P,(18.$30.R7.Vlo,(29.(11.&40.Vsp,)-10.))P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+10.)(11.&40.Vsp,))(13.(=.$>.$>.)))Vm,R8.)P,(14.$30.Vm,R9.)P,(15.$30.R:.)(2:.$30.VAL,VCS,(2;.$30.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vlo,Vm,)(6.(7.Vra,(16.&40.(29.(11.&40.Vsp,)-10.))Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,R13.R=.R12.R11.R10.(34.R16.)R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+:3?60.)Vfc,(9.(2.&40.))R;.(:.$30.)))")
(* [comment removed for export] *).
  Proof.
    intros w x r x10 x12 x13 x14 x16 x17 w11 junk mm Hx Hnz Hr HBL -> FR ST MU WM MI. al_facts.
    do 12 zstep.
    destruct (smear_chain w x (Z.log2 x) Hx Hnz eq_refl) as [SM Bb]. cbv zeta in SM.
    rewrite SM. clear SM.
    set (b := Z.log2 x) in *. clearbody b.
    do 19 step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch get_x10 R with Z_to_bv 64 (_ - bv_unsigned ?raw) =>
        assert (HR : bv_unsigned raw = 31 - b)
          by (clear -b Bb; pattern b;
              lazymatch goal with |- ?P b =>
                unshelve refine (enum32 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b Bb) end;
              cbv beta; vm_compute; reflexivity)
      end end.
    rewrite HR. clear HR. rewrite (unsigned_lit (32 * r)) by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish. f_equal. rewrite HBL. lia.
    all: match goal with |- ?g => idtac "CLZ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0?L20378331621.74L23917391152.74L26773890077.72L29010565666.65L31399144472.61L31889232343.74L32049487064.62L35909905322.69L37798226539.68L37801064254.72L3834405561.62 L42468625771.72L44663269934.70L54425554183.69L55310445663.65L56834433586.74L58496276083.65L58829635818.75L59164244479.75L59308628179.66L66138855315.63L8658395247.64 Q10827307447.72Q15647499098.62Q23447478054.70Q25485674942.72Q25486628167.73Q25488363986.70Q26295627581.73Q26463039879.73Q45164787272.73Q50458135125.73Q8945570098.70 Q9839185977.62 00000?00T00i01A01M01d02002K04O04j05=05L05Y05i06A06P06]07807S08508H08`09509B09W09g0:70:G0:R0:e0;:0;G0;R0;cS1A2xs1k1r2Hk1wS1A2xs2XB1k1r2Hk1w2K1S1A2xs2XB1k1r2Hk2K11wS1A1n2xs2Ln2XB1k1r2Hk2HrS2sp1A2xs2HkS1A1n2xs1k1r2Hk2Hr1w2K1S2sp1A2xs2HkS1A1n2xs2Ln2XB1k1r2Hk2Hr2K1S2AL2CS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1A1n2lo2xs2Ln2XB1k1r3x153x163x172mm2Hk2Hr2K12NXS1A1n2xs2Ln2XB1k1r2Hk2Hr2K1S2sp1A2lo2xs3SLO2HkS1A2xs1k1r2Hk1wS1A2xs1k1r2HkS1A2xs1k1r2Hk2K1S1A1n2xs2Hn2XB1k1r2Hk2HrS1A2xs1k1r2Hk1wS1A2xs1k1r2HkS1A1n2xs2XB1k1r2Hk1w3HBL2K1S1A1n2xs1k1r2Hk2Hr1w3HBL2K1S2sp1A1n2xs2Ln2XB3SPR1k1r2Hk2Hr2K0S1A1n2xs2XB1r2Hk2HrS1A1n2xs2Ln2XB1k1r2Hk2HrS1A1n2xs1k1r2Hk2Hr2K1S2sp2lo2xs2HkS1A1n2xs1k1r2Hk2Hr2K1S1A2xs1k1r2Hk2K1S1A2xs1k1r2Hk2K1S1A2xs1k1r2Hk2K1S2xs1k1r2HkS1A2xs2XB1k1r2Hk2K1S1A1n2xs1k1r2Hk2Hr2K1S1A2xs1k1r2HkS2xs1k1r2HkS2sp2lo2xs3SLO2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK Hn Ln XB LO0 SLO SCS SPR"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "Pk,$35.Pr,$>.Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pw11,(2.&40.)Pw12,(2.&40.)Pw13,(2.&40.)Pjunk,(1:.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(5.$35.(36.R9.)R:.)P,(4.(1=.=R:.)(1=.R:.Vn,))P,(5.$>.(17.Vxs,Vn,)(37.Vxs,(36.R;.)))P,(5.(2.&40.)R8.(16.&40.(29.(26.+20.R<.)+20.)))P,(5.(2.&40.)R8.(16.&40.(29.R=.+1.)))P,(5.(2.&40.)R8.(16.&40.(10.(29.VA,(26.+4.R>.))+4.)))P,(1;.$30.R7.VA,(1<.Vxs,))P,(25.$30.VAL,VCS,R8.VA,(26.+4.Vn,))P,(2?.$30.R9.(29.(11.&40.Vsp,)-10.)(<.$31.(32.#8.R:.)(<.$31.(33.Vra,)(13.$31.))))P,(18.$30.R:.Vlo,(29.(11.&40.Vsp,)-10.))P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+10.)(11.&40.Vsp,))(13.(=.$>.$>.)))Vm,R;.)P,(14.$30.Vm,R<.)P,(15.$30.R=.)(2:.$30.VAL,VCS,(2;.$30.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vlo,Vm,)(6.(7.Vra,(16.&40.(29.(11.&40.Vsp,)-10.))Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,R10.R12.R11.(16.&40.(38.VAL,))R10.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+:3?18.)Vfc,(9.(2.&40.))R>.(:.$30.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r x15 x16 x17 w11 w12 w13 junk mm Hk Hr HBL -> -> -> HA OA FR ST MU WM MI; al_facts.
    - assert (r = 0) by lia. subst r.
      zstep. change (bv_swrap 32 (0 + 1 + -1)) with 0.
      (* [comment removed for export] *)
      zstep. try (if_cases K0; zify_cond K0; [| exfalso; lia]).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      finish. f_equal. rewrite HBL. reflexivity.
    - zstep. replace (bv_swrap 32 (r + 1 + -1)) with r by (rewrite swrap32_of_small; lia).
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in * by lia; lia|].
      destruct (nth_error xs (Z.to_nat (r - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
      pose proof (u32ro_read asegs mm A xs (r - 1) w _ HA NX ltac:(lia) eq_refl) as RDX.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (A + 4 * r - 4) with (A + 4 * (r - 1)) in * by lia.
      shadow_chk OA (A + 4 * (r - 1)) 4.
      (* [comment removed for export] *)
      zstep. clear RDX. zstep. zstep. zstep.
      assert (L32 : limb32 xs (Z.to_nat (r - 1)) = bv_unsigned w mod 2^32).
      { unfold limb32. rewrite (nth_error_nth _ _ _ NX). reflexivity. }
      replace (Z.to_nat r) with (S (Z.to_nat (r - 1))) in HBL by lia. cbn [core_bitlen_rec] in HBL. rewrite L32 in HBL.
      pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as Rw.
      zstep. if_cases Kz; zify_cond Kz; rewrite ?bv_unsigned_sx32 in Kz.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ Rw)) in Kz. rewrite Kz, Z.eqb_refl in HBL.
        eapply (IH (r - 1)); [lia | lia | exact HBL | f_equal; lia | f_equal; lia | f_equal; lia | | | | | | | ]; try eassumption.
        all: match goal with |- ?g => idtac "IH-LEFT:" g end.
      + assert (NZ : bv_unsigned w mod 2^32 <> 0) by (intros E; apply Kz; rewrite E; reflexivity).
        rewrite (proj2 (Z.eqb_neq _ _) NZ) in HBL.
        (* [comment removed for export] *)
        zstep.
        eapply (clz_walk w (bv_unsigned w mod 2^32) r); [reflexivity | exact NZ | lia | rewrite HBL; lia | f_equal; lia | | | | | ]; try eassumption.
        all: match goal with |- ?g => idtac "TOCLZ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00[0?K49615311099.68L11616173489.65L1167583876.66 L1169664276.64 L1685717371.0  L17912843979.65L18873397548.65L18926591958.65L20433961190.64L22331926039.65L25960813796.65L32049487064.64L3227376625.65 L41872764395.67L43061775753.62L44015132812.65L44301797884.65L46748113268.64L47039734445.65L49618833658.3 L53395299452.65L58304640849.65L58796926075.65L60194088209.65L61931962912.66Q11801279589.68Q1219017780.67 Q15643324129.64Q21798041355.67Q23150033886.67Q25513505925.67Q31394594844.67Q40688494363.67Q41126203749.67Q44034257392.67Q45914037331.65Q49698585326.66Q53519952433.67Q54057591853.67Q58146298210.67Q63037100374.67Q66715549212.67Q9843367298.64 00000N00O00P00Q00R00S00\00e00n00o01:01C01S01_01n02702802A02W02X02a02l03:03E03S03l04904C04D04Q04m05105205305?05I05]05j05k06J06V06b06oS2ra2sp1A2xs2SA2HB5Ha_st5Hl_stFFFSFS2sp1A2xsS2sp1A2xsS2sp1A2xsFS2sp1A1n2xsS2sp1A2xsS2sp1A2xs3NZA2XBS2AL2sp1A2xsS2sp1A2lo2xs2LOS2sp1A2xsFS2sp1A2xsS2sp1A1n2xs2Hn3NZA3SPRFS2sp1A2xsS2sp1A1n2xsS2sp1A1n2xs2HnS2sp1A1n2xsS2sp1A1n2xs2HnS2ra2sp2xs2HB5Ha_st5Hl_stS2AL2xs5ALWF'S2sp2lo2xsFS2AL2xs5ALWF'S2ra2sp2lo2xs2HB5Ha_st5Hl_stS2xsFFS2AL2xs4IMG'S2sp2xs2HBS2sp2xs3SPR2HB5Ha_stS2AL2xs5ALWF'FS2ra2sp2lo2xs2LO2HB5Ha_st5Hl_stS2AL2xs4IMG'S2AL2xs4IMG'S2sp2lo2xs2LO". (* [comment removed for export] *)
Lemma A_mpi_core_bitlen_spec : forall AL, asan_img_ok AL -> mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
Proof.
  intros AL IMG. unfold mpi_core_bitlen_stmtA, A_MPI_CORE_BITLEN.
  intros until xs. intros HA Hn LX ALA NZA MI ALWF CSOK ABS OA ST LO SPA SCS SA -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_BITLEN_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB. pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  pose proof (abase_got _ _ _ ABS) as GOT. pose proof (abase_gsb _ _ _ ABS) as GSB. rewrite (proj1 IMG) in GOT.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. clear GOT GSB. zstep. zstep. zstep. zstep. zstep.
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^27) with 134217728. change (2^30) with 1073741824.
  rewrite ?(Z.mod_small (n * 4294967296)) by lia.
  replace (n * 4294967296 / 134217728) with (32 * n)
    by (replace (n * 4294967296) with (32 * n * 134217728) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace (n * 4294967296 / 1073741824) with (4 * n)
    by (replace (n * 4294967296) with (4 * n * 1073741824) by lia; rewrite Z.div_mul by lia; reflexivity).
  eapply (loop_walk AL IMG ALWF CS CSOK) with (n := n) (xs := xs) (k := Z.to_nat n) (r := n); try eassumption; try lia; try (f_equal; lia).
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L1685717371.0  L20433961190.55L31399144472.55L32049487064.56L32049487064.57L3830427394.56 L41872764395.59L43061775753.53L46748113268.56Q11801279589.59Q1219017780.58 Q15643324129.55Q15643324129.56Q21798041355.58Q23150033886.58Q25513505925.58Q31394594844.58Q41126203749.58Q44034257392.58Q45914037331.56Q49698585326.57Q53519952433.58Q58146298210.58Q63037100374.58Q66715549212.58Q9843367298.55 Q9843367298.56 00000100500900=00A00K00R00\00`01601@01G01N01O01Y02202302402=02D02U02_03;03D03M03W03aSS2spS2spS2spS2spS2sp2lo2LOS2AL2spS2sp2lo2LOS2spS2ra2sp2HB5Ha_st5Hl_stS2AL5ALWF'S2sp2loS2sp2loFS2AL5ALWF'S2ra2sp2lo2HB5Ha_st5Hl_stSFS2AL4IMG'S2sp2HBS2sp3SPR2HB5Ha_stS2AL5ALWF'S2ra2sp2lo2LO2HB5Ha_st5Hl_stS2AL4IMG'S2AL4IMG'S2sp2lo2LOS2sp2lo2LO". (* [comment removed for export] *)
Lemma A_mpi_core_bitlen_z_spec : forall AL, asan_img_ok AL -> mpi_core_bitlen_z_stmtA asegs AL A_MPI_CORE_BITLEN.
Proof.
  intros AL IMG. unfold mpi_core_bitlen_z_stmtA, A_MPI_CORE_BITLEN.
  intros until lo. intros MI HA ALWF CSOK ABS ST LO SPA SCS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_BITLEN_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  zstep. zstep.
  pose proof (abase_got _ _ _ ABS) as GOT. pose proof (abase_gsb _ _ _ ABS) as GSB. rewrite (proj1 IMG) in GOT.
  zstep. zstep. zstep. zstep. zstep. zstep. clear GOT GSB. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. try change (bv_swrap 32 (0 + 1 + -1)) with 0.
  zstep. try (if_cases K0; zify_cond K0; [| exfalso; clear - K0; rewrite ?unsigned_lit in K0 by lia; cbn in K0; lia]).
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
  all: match goal with |- ?g => idtac "Z-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

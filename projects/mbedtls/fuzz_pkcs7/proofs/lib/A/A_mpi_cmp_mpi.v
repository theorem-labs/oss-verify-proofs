(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_cmp_mpi () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "mpi_cmp_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "Corelib.Init.Logic.not"].


Definition A_MPI_CMP_MPI_E : Z := 0x09d5b4.   (* [comment removed for export] *)
Notation MPI_CMP_MPI_STACK_A := 16 (only parsing).

Definition mpi_cmp_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O15.O14.O13.O12.R?.R>.R=.O11.O10.(8.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(9.O15.)O4.(:.(2.&40.))R1.(;.O16.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.O2.(11.&40.O14.))(12.(>.$?.$?.)))O1.R1.)(4.(13.O16.O1.R1.)(4.(14.O16.R1.)(15.O16.R1.O2.(11.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_cmp_mpi_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "PCS,P,$?.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(16.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(17.$18.)PdX,$19.PdY,$19.Plo,$?.P,(1:.O3.R5.R4.R3.)P,(1:.O3.R6.R5.R3.)P,P,(5.$1;.(1<.R5.)$1=.)(1>.=(1?.R6.))P,P,(5.$1;.(1<.R5.)$1=.)(1>.=(1?.R6.))P,(14.O3.R9.)P,(20.O2.)P,(21.O2.R2=.)P,(22.O3.O2.R<.)P,(23.O3.O2.R2?.R=.(24.R;.)+10.)P,(23.O3.O2.R30.R>.(24.R;.)+10.)P,P,(25.+1.(26.R=.))(23.O3.O2.R32.R10.(1?.R>.)(27.+4.(26.R>.)))P,P,(25.+1.(26.R=.))(23.O3.O2.R33.R11.(1?.R>.)(27.+4.(26.R>.)))P,(15.O3.R11.R=.(11.&40.R31.))P,(25.=R>.)P,(25.R?.(28.(11.&40.R33.)+10.))P,(5.$?.(29.(11.&40.R34.)+10.)=)P,(2:.R37.R11.(28.(11.&40.R35.)R11.))P,(2;.(25.(2<.(24.R14.)+10.)R12.)(25.(11.&40.R36.)(24.R14.)))P,(2;.(25.(2<.(24.R14.)+10.)R13.)(25.(11.&40.R37.)(24.R14.)))P,P,(25.+1.(26.R16.))(2;.(25.(2<.(1?.R17.)(27.+4.(26.R17.)))R15.)(25.(11.&40.R39.)(1?.R17.)))P,P,(25.+1.(26.R16.))(2;.(25.(2<.(1?.R17.)(27.+4.(26.R17.)))R16.)(25.(11.&40.R3:.)(1?.R17.)))P,(5.(2.&40.)R32.(8.&40.(24.R18.)))P,(5.(2.&40.)R32.(8.&40.(24.R18.)))(2=.O3.O2.R3>.(2>.O3.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.(2?.(28.(30.R1:.)(30.R19.)))R18.R1<.)(6.(7.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(8.&40.O1.)R1=.(:.(2.&40.))R1<.(;.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (m mm : mem) (lo : Z) (junk : list byte).
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells asegs mm X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at asegs mm P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis CY : rw_cells asegs mm Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at asegs mm Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis SG' : sg' = 1 \/ sg' = -1.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis MI : mem_inv asegs mm.
  Hypothesis ALX : X mod 8 = 0.
  Hypothesis ALY : Y mod 8 = 0.
  Hypothesis OX : aobj asegs AL CS mm X 16.
  Hypothesis OY : aobj asegs AL CS mm Y 16.
  Hypothesis OP : 1 <= n -> aobj asegs AL CS mm P (4 * n).
  Hypothesis OQ : 1 <= n' -> aobj asegs AL CS mm Q (4 * n').
  Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk asegs mm lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(lo, bv_unsigned sp)] m mm.
  Hypothesis WM : wmono asegs m mm.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis PBB : 0 <= P /\ P + 4 * n <= 2^64.
  Hypothesis QBB : 0 <= Q /\ Q + 4 * n' <= 2^64.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3 + al_sb AL)).
  Let POST (T : Z) := mpi_cmp_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L31399144472.91L32049487064.89L3832275385.92 Q15641501786.92Q9840988985.92 00000B00P00i01601GS2sp1X1P2xs1Y1Q2ysS2sp1X2xs1Y2ysS2sp2lo1X1P2xs1Y1Q2ys3SLOS2sp2lo2xs2ysS2sp2lo2xs2ys3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk X P xs Y Q ys MI FR ST MU WM LO0 SLO SCS SPR"] Lemma a_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "PT,$?.Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)(2=.$31.VAL,VCS,A1.VPOST,R?.(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(8.&40.R?.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(8.&40.+9=720.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros. al_facts. pose proof FR as FR'. pose proof MU as MU'. pose proof WM as WM'.
    zstep. zstep. release_frame FR' ST (bv_unsigned sp). zstep.
    apply evtA_done. subst POST. unfold mpi_cmp_postA. deexists 15. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI| assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@L11014201954.11 L11014201954.12 L11014202083.11 L1120085281.101 L13987405769.2  L16475699316.101L16477430914.98 L21743477688.1  L22553357965.11 L23100341967.99 L23917405863.3  L28574840970.2  L29010565666.87 L29971744258.5  L30436581548.108L3508006412.11  L36259467494.5  L36571201320.0  L41773732473.3  L44654450861.3  L45380526330.2  L47013807010.12 L4812051346.2   L49844187461.1  L54425655282.3  L54425655405.4  L56840611386.1  L58196651164.101L58198864894.104L59308546259.3  L59308551419.8  L59308551544.8  L59308628179.4  L66151418440.3  Q10125995177.108Q12370813529.103Q14485421028.105Q17205367401.102Q24363994560.105Q24364461956.104Q24415828206.107Q26295627581.105Q26295627581.108Q29651637810.103Q36157561789.105Q37623064971.102Q39944472214.105Q40948640061.105Q41750243048.105Q42426514348.105Q45132659991.103Q50107086626.105Q50458135125.105Q50458135125.108Q54201986939.104Q5483128726.102 Q5485174314.103 Q57547218494.102Q57549166911.105Q57549166911.107Q612084707.107  Q6143569392.103 Q62561324959.103Q63569342106.102Q67028169811.108Q67375772307.104Q6761749716.105 Q6761749719.107 Q6764271681.108 Q8945554086.102 Q8945570098.105 00000>00L00Z01001401c02R02U03403J03R03W04=04J04K04j05905:05D05L05Q06306706;06C06K06N07>07n08>08T08l09709@09Z0::0:W0:g0;70;G0;\0;j0<80<90<:0<J0<b0=90=:0=S0=T0=d0>40>D0>T0>d0?40?D0?T0?d0@;0@K0@L0@a0A<0AL0A\0Al0B<0BJ0BXS1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS1X1P2xs1Y1Q2ys1k1r2HkS2sgS1X1P1n2xs1Y1Q2n'2ys2XB2YB3PBB3QBB1k1r2Hk2Rn2PPS1X1P1n2xs1Y1Q2n'2ys2XB2YB3PBB3QBB1k1r2Hk2Rn2PPS1rS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K1S1X1P2xs1Y1Q2ys1k1r2HkS1k1r2HkS1Q1rS1X1P1n2xs1Y2ys2XB2YB3PBB1k1r2Hk2Hr2RnS1n1k1r2Hk2RnFS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K2S2n'1k1r2Hk3Rn'SS2n'1r3Rn'S1n1r2RnS1P1rS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K12K2S2sgS2sgS1k1r2HkS1k1r2HkS1rS1X1P1n2xs1Y1Q2n'2ys2XB2YB3PBB3QBB1k1r2Hk3Rn'2QPS1X1P1n2xs1Y1Q2n'2ys2XB2YB3PBB3QBB1k1r2Hk3Rn'2QPS1n2N12N02n'3N1'S1n2xs2LX1k1r2Hk2Rn2NXS2n'2ys2LY1k1r2Hk3Rn'2NYS1k1r2Hk2K0S1r2Hk2HrS2xs1Q2n'2ys3QBB1k1r2Hk2QPS1X1P2xs1Y1Q2ys2XB2YB3ALX1k1r2HkS1X1P2xs1Y1Q2ys2YB3ALY1k1r2HkS1X2xs2ys1k1r2HkS2xs1Y2ys1k1r2HkS2xs1Y2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2RnS2xs2ys1k1r2HkS2xs2ys1k1r2HkFFS1X2xs2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2Rn2N1S2xs1Q2n'2ys1k1r2Hk3Rn'FS1P1n2xs2ys3PBB1k1r2Hk2PPFS2xs1Y2ys1k1r2HkS1P2xs2ys1k1r2HkS2xs1Q2ys1k1r2HkS2xs1Y2ys1k1r2HkS1X2xs2ys1k1r2HkS1X2xs2ys1k1r2HkS1P2xs2ys1k1r2HkS1P2xs2ys1k1r2HkS1P2xs2ys1k1r2HkS2xs1Q2n'2ys1k1r2Hk3Rn'S1X2xs2ys1k1r2HkFS1P1n2xs2ys1k1r2Hk2RnS2xs1Q2n'2ys1k1r2Hk3Rn'3N1'S2xs1Y2ys1k1r2HkS2xs1Q2ys1k1r2HkS2xs1Q2ys1k1r2HkS2xs1Q2ys1k1r2HkS2xs2ys1k1r2HkS2xs2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad Q sg' pad' CX HX LX XB PB CY HY LY YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_loop3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pk,$32.Pr,$?.PT,$?.Pw15,(2.&40.)Pw17,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(5.$32.(33.R;.)R<.)P,(25.=R<.)P,(25.R=.Vn,)P,(25.R>.Vn',)P,(5.$?.R>.(27.Vsg,(2?.(28.(34.Vxs,R?.)(34.Vys,R?.)))))P,(5.(2.&40.)R>.(8.&40.(2<.R10.+1.)))P,(5.(2.&40.)R>.(8.&40.(28.(27.+4.R11.)+4.)))(2=.$31.VAL,VCS,A1.VPOST,R11.(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,(8.&40.(2<.(35.VX,+3.)(36.VAL,)))(8.&40.(2<.(35.VY,+3.)(36.VAL,)))R>.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R=.R<.(8.&40.(36.VAL,))R10.(8.&40.Vsg,)R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(8.&40.+9=780.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r T w15 w17 xt2 xa2 xa3 xt3 xt4 xt5 xt6 Hk Hr Rn Rn' HT -> ->; al_facts.
    - assert (r = 0) as -> by (clear - Hk Hr; lia).
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 T) by (f_equal; rewrite HT, !lval_0; cbn; clear; lia). apply a_ret.
    - zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - Hk Hr Rn Hn; lia); clear - K0 Hk; lia|]. clear K0.
      destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Rn LX Hk; lia].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Rn' LY Hk; lia].
      assert (N1 : 1 <= n) by (clear - Hk Rn; lia). assert (N1' : 1 <= n') by (clear - Hk Rn'; lia).
      pose proof (OP N1) as OPn. pose proof (OQ N1') as OQn.
      destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|]. destruct QB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs mm P xs (r - 1) wx _ HX NX ltac:(clear - Hk Hr; lia) eq_refl) as RDX.
      replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
      zstep. zstep. shadow_chk OQn (Q + (4 * r - 4)) 4.
      clear RDX.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs mm Q ys (r - 1) wy _ HY NY ltac:(clear - Hk Hr; lia) eq_refl) as RDY.
      replace (Q + 4 * (r - 1)) with (Q + (4 * r - 4)) in RDY by (clear; lia).
      zstep. clear RDY.
      pose proof (limb32_of_read xs r wx NX) as LXr. pose proof (limb32_of_read ys r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      + apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
        (* [comment removed for export] *)
        zstep. zstep. replace (Z_to_bv 64 sg) with (Z_to_bv 64 T) by (f_equal; rewrite HT, (cmp_step_gt xs ys r) by (clear - K1 LXr LYr Hk Hr; lia); clear - SG; lia). apply a_ret.
      + apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
        (* [comment removed for export] *)
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
        * apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
          eapply (IH (r - 1) T); [clear - Hk; lia| clear - Hk; lia| clear - Rn; lia| clear - Rn'; lia| rewrite HT, (cmp_step_eq xs ys r) by (clear - K1 K2 LXr LYr Hk Hr; lia); reflexivity| f_equal; clear; lia| f_equal; clear; lia].
        * apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
          (* [comment removed for export] *)
          zstep. zstep. zstep.
          replace (Z_to_bv 64 (0 - sg mod 18446744073709551616)) with (Z_to_bv 64 T); [apply a_ret|].
          apply Z_to_bv_eqm. rewrite HT, (cmp_step_lt xs ys r) by (clear - K2 LXr LYr Hk Hr; lia). change 18446744073709551616 with (2^64).
          rewrite Zminus_mod_idemp_r. f_equal. clear - SG; lia.
    all: match goal with |- ?g => idtac "LOOP3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@L10116397382.6  L10351590514.3  L10907032063.4  L2424960062.2   L27147534220.6  L27601760771.4  L29074168500.95 L29074168500.99 L29074177661.92 L29074214878.96 L29969580679.4  L32954672704.93 L32954672833.92 L36259533860.4  L37314927368.93 L37314936640.101L37314936640.96 L37315409998.98 L39172636981.0  L39973646689.2  L39973646689.4  L41247890161.4  L42989026026.2  L44872450572.3  L45272779239.3  L48521138956.6  L51196083649.1  L5126932107.6   L5260085936.103 L53768759474.3  L55487647722.95 L57415930929.3  L58874375798.2  L66182251873.4  L66184348993.2  L66253547196.103L66253710909.92 L66253711036.93 L9327607964.103 Q12046551387.103Q12046608925.99 Q22285569813.101Q22285598390.98 Q22285631880.101Q22285631880.104Q22285631880.105Q22286196081.100Q39212284437.101Q39212284437.102Q39212284437.104Q39212284437.106Q39424119965.102Q39424119965.106Q49046334496.102Q49046334496.106Q4926406185.101 Q4926406185.104 Q4958620598.101 Q4960717810.105 Q54253781473.105Q54253886744.100Q56761401107.101Q56761401107.104Q60511567613.101Q60511567613.102Q60511567613.104Q60511567613.106Q61417400191.101Q61417400191.103Q61417997369.99 Q61418027910.102Q61418027910.106Q61419497275.105Q63231421641.101Q63231434090.98 Q9538243134.103 Q9538410586.101 Q9538464120.99  Q9538464249.98  00000C00K00S00Y00j01501G01W01i02902E02f03G03T03f04604H04X04Y04b04k05705?05G05P05c05f06706G06O06P06Y06^06e06l07J07j08J08Z08e09209=09J09W09b09m0::0:G0:T0:_0:j0;70;B0;R0;`0;m0<80<E0<P0<[0<h0=80=F0=Q0=\0=e0=n0>;0>F0>S0>`0>k0?60?A0?N0?W0?`0?k0@6S2xs2ys1i2I32PP3RY'S1n1i2I1S1i1j2K2S1n2HnS1n2xs2n'2ys1H2H0S1i1j2K12K2S1X2xs1Y2ys2XB1i1jS1X2xs1Y2ys2XB1iS1X2xs1Y2ys2XB1i1jS1X2xs1Y2ys2XB1iS1n1i2I13NeiS1X2xs1Y1Q2n'2ys2XB2YB3QBB1i1j2J1S1X2xs1Y1Q2n'2ys2XB2YB3QBB1i1j2J1S2n'1i2J13NeiS1X2xs1Y2ys2YB1i1jS1X2xs1Y2ys2YB1iS1X2xs1Y2ys2YB1i1jS1X2xs1Y2ys2YB1iSS3sg'3SG'S3sg'3SG'S1n1i2I13NeiS2n'3Hn'S1i1j2K1S2n'1j2J1S2xs2ys1i2I32PP3RY'S1iS1n2xs2n'2ys1H2H0S1X2xs1Y2ys2XB1iS1n1i2I1FS2n'1i2J1S3sg'S2sg2SGS2sg2SGS1X1P1n2xs1Y2ys2XB2YB3PBB1i2I1S1X1P1n2xs1Y2ys2XB2YB3PBB1i1j2I1S1X1P1n2xs1Y2ys2XB2YB3PBB1i1j2I1S1X2xs1Y2ys2YB1iS2xs1Y2ys1iS2xs1Y2ys1i1jS1X2xs2ys1iS1X2xs2ys1i1jS1X2xs2ys1i1jS1X2xs2ys1iS1X2xs2ys1iS1X2xs2ys1i1jS1X2xs2ys1i1jS2xs1Y2ys1i1jS1X2xs2ys1iS2xs1Y2ys1iS2xs1Y2ys1i1jS2xs1Y2ys1iS2xs1Y2ys2YB1i1jS2xs1Y2ys2YB1iS1X2xs2ys1i1jS1X2xs2ys1iS2xs1Y2ys1i1jS2xs1Y2ys1iS1X2xs2ys1iS1X2xs2ys1i1jS1X2xs2ys2XB1i1jS1X2xs2ys2XB1iS2xs2ys1i1jS2xs2ys1i1jS2xs2ys1iS2xs2ys1iS2xs1Y2ys1i1jS2xs1Y2ys1iS2xs1Y2ys1i1jS2xs1Y2ys1i1jS2xs1Y2ys1iS2xs1Y2ys1iS1X2xs2ys1iS1X2xs2ys1i1jS2xs2ys1iS2xs2ys1iS2xs2ys1i1jS2xs2ys1i1j". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad Q pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_decide : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pi,$?.Pj,$?.Pxf,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(37.Vxs,Vn,R<.)P,(37.Vys,Vn',R<.)P,(38.(4.(5.$?.R>.=)(5.$?.R=.=)))(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R9.R=.(8.&40.(36.VAL,))(8.&40.R?.)(8.&40.R>.)R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(8.&40.+9=6>0.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros i j xf xt0 xt1 xt2 xa2 xa7 xt3 xt4 xt5 xt6 SX SY NZ. al_facts.
    dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (lval_range xs i ltac:(clear - I1; lia)) as RX. pose proof (lval_range ys j ltac:(clear - J1; lia)) as RY.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - I1 J1 Hn Hn'; lia).
    2: { (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX (X + 8) 2. zstep. rewrite sx16_small by (clear - SG; lia). zstep.
      replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))); [apply a_ret|].
      f_equal. apply sgn_of_lt; [exact SG| exact SG'|]. pose proof (lval_range ys n' ltac:(clear - Hn'; lia)). pose proof (SIGF_lt xs n i ys n' j SX SY ltac:(clear - K1; lia)). clear - H H0. lia. }
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - I1 J1 Hn Hn'; lia).
    2: { (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OY (Y + 8) 2. zstep. rewrite sx16_small by (clear - SG'; lia). zstep.
      replace (Z_to_bv 64 (0 - sg' mod 18446744073709551616)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))); [apply a_ret|].
      apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_r. f_equal.
      rewrite (sgn_of_gt sg sg'); [clear - SG'; lia| exact SG| exact SG'|].
      pose proof (lval_range xs n ltac:(clear - Hn; lia)). pose proof (SIGF_lt ys n' j xs n i SY SX ltac:(clear - K1 K2; lia)). clear - H H0. lia. }
    (* [comment removed for export] *)
    assert (j = i) as -> by (clear - K1 K2; lia). assert (Nei : i <> 0) by (intros E; apply NZ; split; exact E). clear K1 K2 NZ.
    destruct I3 as [I3|I3]; [exfalso; exact (Nei I3)|]. pose proof (pow32_pos (i - 1) ltac:(clear - I1 Nei; lia)) as PP.
    pose proof (lval_range ys i ltac:(clear - I1; lia)) as RY'.
    assert (N1 : 1 <= n) by (clear - I1 Nei; lia). assert (N1' : 1 <= n') by (clear - J1 Nei; lia).
    assert (LP : forall s xt2' xa2' xa3' xa7' xt3', s = 1 \/ s = -1 -> sg = s -> sg' = s ->
      evtA asegs AL CS (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
        (MS (mkR ra SP' gp tp xt0 xt1 xt2' s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa2' xa3' SB (Z_to_bv 64 i) (Z_to_bv 64 s) xa7'
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3' xt4 xt5 xt6) F (Z_to_bv 64 0x09d764) fc None mm (seg_rom asegs))).
    { intros s xt2' xa2' xa3' xa7' xt3' Hs E1 E2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      rewrite <- E1.
      eapply (a_loop3 (Z.to_nat i) i); [reflexivity| clear - I1; lia| clear - I1; lia| clear - J1; lia| | f_equal; clear; lia| f_equal; clear; lia].
      rewrite I2, J2, E2, <- E1. apply sgn_same_sign. exact SG. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OY (Y + 8) 2.
    rewrite !sx16_small by (clear - SG SG'; lia).
    (* [comment removed for export] *)
    zstep. rewrite !sx16_small by (clear - SG SG'; lia).
    destruct SG as [Es|Es]; rewrite Es in *; zstep; destruct SG' as [Es'|Es']; rewrite Es' in *; zstep.
    - (* [comment removed for export] *) apply LP; [left; reflexivity| reflexivity| reflexivity].
    - (* [comment removed for export] *)
      zstep. zstep. replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.sgn (1 * lval xs n - -1 * lval ys n'))) by (f_equal; rewrite I2, J2; apply Z.sgn_pos; clear - I3 PP RY'; lia). apply a_ret.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (Z.sgn (-1 * lval xs n - 1 * lval ys n'))) by (f_equal; rewrite I2, J2; apply Z.sgn_neg; clear - I3 PP RY'; lia). apply a_ret.
    - (* [comment removed for export] *) zstep. apply LP; [right; reflexivity| reflexivity| reflexivity].
    all: match goal with |- ?g => idtac "DECIDE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11430973886.2000008S2sg3sg'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad Q pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_zero_j : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pi,$?.Pxf,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(37.Vxs,Vn,R<.)P,(37.Vys,Vn',=)P,P,(5.$?.(11.&40.R=.)=)(38.(5.$?.R?.=))P,P,(38.(5.$?.(11.&40.R>.)=))(5.$?.R10.=)(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R;.R?.(8.&40.(36.VAL,))(8.&40.R10.)R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(8.&40.+9=6=0.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros i xf xt0 xt1 xt2 xa2 xa6 xa7 xt3 xt4 xt5 xt6 SX SY XF0 XF1. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply a_decide; [exact SX| exact SY|]. intros [Ei _]. exact (XF0 K Ei).
    - (* [comment removed for export] *)
      pose proof (XF1 K) as Ei. zstep. zstep.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))); [apply a_ret|].
      f_equal. ddestruct SX as (I1 & I2 & I3). ddestruct SY as (J1 & J2 & J3). rewrite I2, J2, Ei, !lval_0. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L11014210082.3  L1137720866.4   L1962756882.4   L21411420601.2  L23917405863.3  L23970764156.100L28574840970.2  L31326834835.4  L36257472189.3  L36571201320.0  L43921905810.3  L47910126524.2  L54425655405.3  L58198864894.97 L58198942495.94 L59308546259.3  L59308551544.6  L59308587409.4  L59314955108.4  Q10125995177.101Q26295627581.101Q40946738878.98 Q50458135125.101Q612084707.101  Q67028169811.101Q6761749719.101 Q6764271681.101 Q6764303191.98  Q8943673009.98  00000900E00F00N00V01@01E01Q01Z01[01d01i02202V03:03E03W03c03n04H04V04l05<05R05h06>06T06j078S2n'1r2HrS2n'1r2Hr2K2FS2n'3Hn'S1k1r2HkS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2Hr2QP2wyS1Q1rS2n'1r2Hr2K2S2n'1r2HrSS2n'1r2HrS1Q1rS2n'1r2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS2n'3N1'2N0S2n'2ys2LY1r2Hr2NYS2n'1r2Hk2HrS2n'1r2Hr1ES2xs1Q2n'2ys3QBB1k1r2Hk2HrS2xs2ys1k1r2HkS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2ys1k1r2HkS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_loop2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pk,$32.Pi,$?.Pr,$?.Pxf,(2.&40.)Pw12,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(5.$32.(33.R:.)R<.)P,(4.(25.+1.R;.)(25.R;.Vn',))P,(37.Vxs,Vn,R=.)P,(5.$?.(34.Vys,Vn',)(34.Vys,R=.))P,P,(5.$?.(11.&40.R=.)=)(38.(5.$?.R10.=))P,P,(38.(5.$?.(11.&40.R>.)=))(5.$?.R11.=)P,(5.(2.&40.)R>.(8.&40.(2<.VQ,(28.(27.+4.R10.)+4.))))(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R?.R10.(8.&40.(36.VAL,))(8.&40.R12.)(8.&40.R11.)R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(8.&40.+9=690.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i r xf w12 xt0 xt1 xt2 xt3 xt4 xt5 xt6 Hk Hr SX INV XF0 XF1 ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1' : 1 <= n') by (clear - Hr; lia). pose proof (OQ N1') as OQn.
    destruct QB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Hr LY; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OQn (Q + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs mm Q ys (r - 1) wy _ HY NY ltac:(clear - Hr; lia) eq_refl) as RDY.
    replace (Q + 4 * (r - 1)) with (Q + (4 * r - 4)) in RDY by (clear; lia).
    zstep. clear RDY. pose proof (limb32_of_read ys r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
      apply a_decide; [exact SX| | intros [_ E]; clear - E Hr; lia]. split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ By)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn'; lia).
      + eapply (IH i (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| exact SX| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LYr; exact K1]| exact XF0| exact XF1| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. apply a_zero_j; [exact SX| | exact XF0| exact XF1]. split; [clear - Hn'; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero ys r) by (first [clear - Hr; lia | rewrite LYr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
    all: match goal with |- ?g => idtac "LOOP2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L1120085281.91 L14972936856.3 L21411420601.2 L39172636981.0 L47548442835.85L47560995072.88L47912431207.2 L50704676279.2 L54258658734.88L54261175314.90L9325852706.90 Q14485421028.95Q20233606338.89Q20246173414.92Q20246661663.91Q24361956476.94Q24363994560.95Q35030107133.92Q39212284437.92Q42349454934.91Q48520856102.89Q50107086626.95Q54200464515.94Q60511567613.92Q67373197675.94Q7748271680.92 Q9534297315.89 00000=00H00P00Q00_00m01301;01M01a02102E02N02W02`02i03203;03D03M03V03_03h03o04804D04KS1X2xs1Y1Q2ysS2n'3Hn'2K0S2n'3Hn'SS1X2xs1Y2ys2YBS1X2xs1Y2ys2YBS1Q2n'S2n'3Hn'S1X2xs1Y2n'2ys3Hn'S1X2xs1Y1Q2n'2ys3Hn'S1X2xs1Y1Q2ys2YBS1X2xs1Y1Q2ys2YB3ALYS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs2ysS2xs1Y2ysS2xs1Y2ys2YBS2xs2ys". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad Q pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_stage2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pi,$?.Pxf,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(37.Vxs,Vn,R<.)P,P,(5.$?.(11.&40.R<.)=)(38.(5.$?.R>.=))P,P,(38.(5.$?.(11.&40.R=.)=))(5.$?.R?.=)(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R:.R>.(8.&40.(36.VAL,))(8.&40.R?.)R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(8.&40.+9=650.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros i xf xt0 xt1 xt2 xa2 xa6 xa7 xt3 xt4 xt5 xt6 SX XF0 XF1. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OY (Y + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - Hn'; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn'; lia).
    - (* [comment removed for export] *) apply a_zero_j; [exact SX| | exact XF0| exact XF1]. split; [clear - Hn'; lia|]. split; [rewrite K0; reflexivity| left; reflexivity].
    - destruct QB as [N0|[QP QAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (a_loop2 (Z.to_nat n') i n'); [reflexivity| clear - K0 Hn'; lia| exact SX| reflexivity| exact XF0| exact XF1| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "STAGE2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L11014210082.3 L1546378976.3  L16475646230.91L16475699316.94L21007906567.2 L23917405863.3 L23970764156.97L29971580958.3 L31326834835.4 L33397803794.4 L36571201320.0 L42164753195.3 L45380526330.2 L54425655405.3 L55166369148.2 L56393850587.4 L58127621921.0 L59308546259.3 L59308551419.6 L59308586639.4 L59308587409.4 L59355849605.0 L64930767917.4 Q24418024571.98Q26295627581.98Q39944472214.98Q42426514348.98Q50458135125.98Q57547169194.98Q57549166911.98Q57549198250.95Q63571026702.95Q8943673138.95 00000800@00c01F01L01T02=02E02P02Q02R02Z02_02g02l03703803A03R03_03j03k04604K04Y04n05G05W05l06A06V06k079S1n1r2HrS1n1r2HrS1X1P1n2xs1Y2ys2XB2YB3PBB1k1r2Hk2HrS1X1P1n2xs1Y2ys2XB2YB3PBB1k1r2Hk2HrS1n2HnS1k1r2HkS1X1P1n2xs1Y2ys2XB2YB3PBB1k1r2Hk2Hr2PP2wxS1n1r2HrS1n1r2Hr2K2FSS1n1r2HrS1P1rS1n1r2HrS1P1rS1n1r2Hr2K2SS1n2N12N0S1n2xs2LX1r2Hr2NXS2wx2Bx2K12HlS1n1r2Hk2HrSS1n1r2Hr2K2S1P1n2xs2ys1k1r2Hk2HrS2xs2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys3PBB1k1r2Hk2HrS1P2xs2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS2xs2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk pad Q pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_loop1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pk,$32.Pr,$?.Pw12,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa3,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(5.$32.(33.R;.)R<.)P,(4.(25.+1.R<.)(25.R<.Vn,))P,(5.$?.(34.Vxs,Vn,)(34.Vxs,R=.))P,(5.(2.&40.)R=.(8.&40.(2<.VP,(28.(27.+4.R>.)+4.))))(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R>.R:.(8.&40.(36.VAL,))(8.&40.R?.)R>.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(8.&40.+9=608.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w12 xt0 xt1 xt2 xa3 xa7 xt3 xt4 xt5 xt6 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= n) by (clear - Hr; lia). pose proof (OP N1) as OPn.
    destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hr LX; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs mm P xs (r - 1) wx _ HX NX ltac:(clear - Hr; lia) eq_refl) as RDX.
    replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply a_stage2.
      + split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
      + intros _. clear - Hr; lia.
      + intros KF. exfalso. apply KF. cbn. rewrite bv_unsigned_sx32.
        destruct (Z.ltb_spec (sxz (bv_unsigned wx mod 2 ^ 32)) 1) as [Hl|Hl]; [exfalso; pose proof (proj2 (sxz_zero_iff _ Bx)); unfold sxz in *; destruct (bv_unsigned wx mod 2 ^ 32 <? 2 ^ 31); clear - K1 Hl Bx; lia| reflexivity].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LXr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        apply a_stage2.
        * split; [clear - Hn; lia|]. split; [| left; reflexivity]. rewrite INV, (lval_drop_zero xs r) by (first [clear - Hr; lia | rewrite LXr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
        * intros KF. exfalso. revert KF. cbn. rewrite bv_unsigned_sx32. rewrite (proj2 (sxz_zero_iff _ Bx) K1). cbn. rewrite ?unsigned_lit by (clear; lia). clear. lia.
        * intros _; reflexivity.
    all: match goal with |- ?g => idtac "LOOP1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L23100341967.90L33087595724.2 L39172636981.0 L41872764395.87L44822653989.3 L46160487540.87L46164721063.84L5262012942.89 L55166432096.2 L58127621921.0 L58796964359.2 L59308631013.1 L61929812114.87L61931718958.89Q1219017780.90 Q12370813529.94Q17205383785.93Q21798041355.90Q23150033886.90Q26207421841.90Q26207721832.91Q26220321612.88Q31394594844.90Q31654082872.90Q37138808053.90Q37623048587.93Q39212284437.91Q41126203749.90Q4143427880.90 Q43925228937.91Q44034257392.90Q45132659991.94Q53519952433.90Q5483112342.93 Q5485174314.94 Q59531472556.90Q60511567613.91Q60697995187.91Q6143569392.94 Q63037100374.90Q66715549212.90Q67536506979.90Q8884992016.88 Q9534297315.88 00000=00C00D00R00[00i01701G01L01M01S01W01g02902I02`02i02j03:03C03L03U03\03e03f03o04804904:04C04R04S04c04l05505605=05I05R05a06006106:06AS1X1P2xs1Y2ysS1n2HnSS2AL1X2xs1Y2ysS1n2Hn2K0S1X2xs1Y2ys2XBS1X2xs1Y2ys2XBS1X1P2xs1Y2ys2XBS1P1nSS1n2HnS2KFS1X1n2xs1Y2ys2HnS1X1P1n2xs1Y2ys2HnS2AL2xs2ys5ALWF'S1X1P2xs1Y2ys2XB2YB3ALXS1X2xs2ysFS2AL2xs2ys5ALWF'S1X2xs2ysS1X2xs2ysS1X2xs2ysS2xs2ysS1X2xs2ysFS1X2xs2ysS1X2xs2ysFFS1X2xs2ysS2AL2xs2ys4IMG'FS2AL2xs2ys5ALWF'S1X2xs2ysS1X2xs2ysFS2xs2ysS1X2xs2ys2XBS1X2xs2ysS2AL2xs2ys4IMG'S2AL2xs2ys4IMG'FS1X2xs2ysS2xs2ys". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad Q pad' CX HX LX Hn SG XB PB CY HY LY Hn' SG' YB QB MI ALX ALY OX OY OP OQ FR ST MU WM LO0 SLO SCS SPR PBB QBB"] Lemma a_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(22.$31.VAL,Vmm,)(2=.$31.VAL,VCS,A1.VPOST,(2?.(28.(27.Vsg,(34.Vxs,Vn,))(27.Vsg',(34.Vys,Vn',))))(6.(7.Vra,(8.&40.(2<.(11.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(8.&40.VX,)(8.&40.VY,)R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(8.&40.+9=5;<.)Vfc,(:.(2.&40.))Vmm,(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros AB. al_facts.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - Hn; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn; lia).
    - (* [comment removed for export] *)
      zstep. apply (a_stage2 n); [| intros KF; exfalso; rewrite unsigned_lit in KF by (clear; lia); clear - KF; lia| intros _; exact K0].
      split; [clear - Hn; lia|]. split; [reflexivity| left; exact K0].
    - destruct PB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (a_loop1 (Z.to_nat n) n); [reflexivity| clear - K0 Hn; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "AMAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?K12690573793.90K8159284910.90 L12694265486.2 L13742250448.9 L13742266832.8 L1685717371.0  L19945316590.2 L20433961190.86L23515373696.2 L23515373827.2 L32049487064.81L41042576636.5 L41042593020.6 L43059266230.84L46748113268.81L57394205001.9 L57394221385.8 L8164022338.2  L9164419877.5  P23511823980.90Q15643324129.86Q25513505925.89Q45914037331.87Q49698585326.88Q58146298210.89Q67528989526.90Q9843367298.86 00000^01L01M01N01O01P01W01i01j01k02=02H02I02b03403503603703B04904N05505J05i06T07?07XS2ra2sp2dX2dY2lo3SLO2YS3PBB3QBB2HB5Ha_st5Hl_stS2ra2sp2dX2dY2lo3SLO2XS3PBB3QBB2HB5Ha_st5Hl_stFFFSS2sp2loS2sp2dX2dY3PBB3QBBFFS2sp2dX2dY3PBB3QBBS2dY2LY3QBBFS2sp2dX2dY2lo3SLO3PBB3QBBS2sp2dX2dY3PBB3QBBFFFS2dX2LX3PBBS2ra2sp2dX2dY2lo3SLO2QS2LY3PBB3QBB2HB5Ha_st5Hl_st2PS2LXS2sp2dX2dY2lo3PBB3QBBS2ra2sp2dX2dY2lo3PBB3QBB2HB5Ha_st5Hl_stS2sp2dX2dY3PBB3QBB2HBS2sp2dX2dY3SPR3PBB3QBB2HB5Ha_stS2ra2sp2dX2dY2lo3SLO3PBB3QBB2HB5Ha_st5Hl_stS2ra2sp2dX2dY2lo3SLO3PBB3QBB2HB5Ha_st5Hl_stS2sp2dX2dY2lo3SLO3PBB3QBB". (* [comment removed for export] *)
Theorem A_mpi_cmp_mpi_spec : forall AL, asan_img_ok AL -> mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.
Proof.
  intros AL IMG. unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E. intros until lo. intros HX HY PX PY MI ALWF CSOK AB OX OY OP OQ ST LO0 SLO SPA SCS XS YS PS QS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (mpd_raw _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  pose proof (proj1 (proj2 (proj1 HX))) as ALX. pose proof (proj1 (proj2 (proj1 HY))) as ALY.
  pose proof (bytes_at_bound _ _ _ _ BX) as PBB. rewrite u32s_length in PBB.
  pose proof (bytes_at_bound _ _ _ _ BY) as QBB. rewrite u32s_length in QBB.
  unfold mpd_val. fold (mpd_abs dX) (mpd_abs dY). rewrite !mpd_abs_lval by assumption.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply a_main; try eassumption; try reflexivity.
  all: try (clear - NX LX PBB PBX; lia).
  all: try (clear - NY LY QBB PBY; lia).
  all: try (intros N1; destruct (PS N1); [left| right]; assumption).
  all: try (intros N1; destruct (QS N1); [left| right]; assumption).
  all: try (intros N1; eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m);
            [unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]
            | exact MU | first [exact (OP N1) | exact (OQ N1)]]).
  all: match goal with |- ?g => idtac "CMP-TOP-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

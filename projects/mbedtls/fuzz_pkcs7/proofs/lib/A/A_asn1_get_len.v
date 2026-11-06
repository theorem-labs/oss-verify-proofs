(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len.
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
Ltac2 gd_tbl_A_asn1_get_len () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "asn1_get_len_postA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"].


Definition A_ASN1_GET_LEN : Z := 0x098f28.
Notation GETLEN_STACK := 16 (only parsing).

(* [comment removed for export] *)
Definition A_GOT_SHADOW : Z := 0x0f2a90.

Definition asn1_get_len_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+10.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-7?.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1;.R1.)(13.$1:.)))(5.(5.(18.O4.R2.)(18.R2.O3.))(5.P,(6.$4.R3.=)(5.(18.(10.O4.+1.)R3.)(18.(12.&40.R2.)(11.O3.R3.)))(1<.O19.R4.O2.(12.&40.O17.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_len_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Plo,$4.Pbs,(1>.(2.&8.))Plenv,(2.&40.)P,(19.O3.R9.R8.(=.$1:.(1;.(16.&40.R6.))(13.$1:.)))P,(19.O3.R:.R8.(=.$1:.(1;.R2.)(13.$1:.)))P,(1?.O3.R;.R6.R4.)P,(18.R7.R9.)P,(18.R:.R9.)P,(18.R:.(10.R9.(20.(21.(2.&8.)R7.))))P,(17.(10.R:.(20.(21.(2.&8.)R8.)))(22.+2.+3?.))P,(23.(18.(10.R?.+8.)R>.)(18.(10.R>.+8.)R?.))P,(23.(6.$4.(20.(21.(2.&8.)R:.))=)(23.(18.(10.R10.+8.)R<.)(18.(10.R<.(20.(21.(2.&8.)R:.)))R10.)))P,(23.(6.$4.(20.(21.(2.&8.)R;.))=)(23.(18.(10.R10.+8.)R=.)(18.(10.R=.(20.(21.(2.&8.)R;.)))R10.)))P,(6.$4.(24.R12.+8.)=)P,(6.$4.(24.R12.+8.)=)P,(17.=R14.)P,(17.=R14.)P,(17.=R12.)P,(15.O3.R18.)P,(25.O2.)P,(26.O2.R3<.)P,(27.O3.O2.R1;.)P,(28.O3.O2.R3>.R1<.R1;.+8.)P,(28.O3.O2.R3?.R1=.R1;.+8.)P,(28.O3.O2.R40.R1>.R19.(20.(21.(2.&8.)R17.)))P,(1<.O3.R1?.R19.(12.&40.R3?.))P,(18.R1:.(11.(12.&40.R40.)+10.))P,(6.$4.(24.(12.&40.R41.)+10.)=)P,(29.R44.R1<.(11.(12.&40.R42.)R1<.))P,(23.(18.(10.R22.+8.)(11.(12.&40.R43.)+10.))(18.(12.&40.R43.)R22.))P,(23.(18.(10.R22.+8.)(11.(12.&40.R44.)+10.))(18.(12.&40.R44.)R22.))P,(23.(6.$4.(20.(21.(2.&8.)R1>.))=)(23.(18.(10.R20.(20.(21.(2.&8.)R1>.)))(11.(12.&40.R45.)+10.))(18.(12.&40.R45.)R20.)))P,(6.(2.&40.)R3>.(16.&40.R25.))P,(6.(2.&40.)R3>.(16.&40.R23.))P,(6.(2.&40.)R3>.(16.&40.R26.))(2:.O3.O2.R4;.(2;.O3.R4:.R49.R48.R47.R43.R42.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2;.R2:.R28.R27.R26.R25.R23.R29.)(7.(8.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.)R2;.(16.&40.O1.)R2:.(:.(2.&40.))R29.(;.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : LENP mod 8 = 0.
  Hypothesis SPL : lo <= bv_unsigned sp - 16.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : LENP + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= LENP.
  Hypothesis DS3 : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "(23.(6.$4.(20.(21.(2.&8.)Vbs,))=)(23.(18.(10.VBUF,(20.(21.(2.&8.)Vbs,)))(11.(12.&40.Vsp,)+10.))(18.(12.&40.Vsp,)VBUF,)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation POST := (asn1_get_len_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L13952552502.87L20628580025.87L22370308963.87L31399144472.87L32049487064.83L3832212994.88 L61492657120.87L61543885275.87Q15641571297.88Q9840925826.88 00000D00_01:01I01X01n02B02C02M02[S2sp2PP4LENP2bs1r2HrS2sp2PP4LENP1P3END2bs2p'2HpS2sp2PP4LENP1P3END2bs2p'2HpS2sp2PP4LENP2bsS2sp2PP4LENP2bsS2sp2PP4LENP2lo2bs3SPLS2sp2PP4LENP2bs1r2HrFS2sp2lo2bsS2sp2lo2bs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK bs SPL LO0 SCS"] Lemma ret_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Pr,$4.Pp',$4.PL,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(5.(17.-7?.R11.)(18.R11.=))P,(5.(18.VP,R11.)(18.R11.VEND,))P,P,(6.$4.R13.=)(5.(18.(10.VP,+1.)R13.)(18.(12.&40.R12.)(11.VEND,R13.)))P,(19.$2<.R5.VPP,(=.$1:.(1;.(16.&40.R13.))(13.$1:.)))P,(19.$2<.R6.VLENP,(=.$1:.(1;.R13.)(13.$1:.)))P,(19.$2<.R7.(10.(12.&40.Vsp,)-10.)(=.$1:.(2=.#8.R6.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1<.$2<.R8.Vlo,(10.(12.&40.Vsp,)-10.))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R9.)P,(14.$2<.Vm,R:.)P,(15.$2<.R;.)(2:.$2<.VAL,VCS,(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R18.R17.R16.Vs0,Vs1,R15.R14.R13.R12.(16.&40.R1;.)R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.Vt5,Vt6,)VF,(16.&40.+9907<.)Vfc,(:.(2.&40.))R<.(;.$2<.)))")
(* [comment removed for export] *).
  Proof.
    intros r p' L x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 x29 mm junk Hr Hp Hr0 HPP HLEN FR ST MU WM MI. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish; try eassumption; try lia; try reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L29036584927.79L34758834082.85L38386304944.85L41202929119.79L42609056908.78L42814994432.85L50365010712.85L53987760896.78L67688727892.78L8073614032.78 L9817085104.78 Q10649498890.85Q10649715752.84Q13735272213.84Q14060997130.85Q15861160855.84Q17701933584.85Q23545509642.85Q23545529896.84Q39676986896.85Q45355799959.84Q60529804337.85Q61847600945.85Q66916223253.8400000D00d01801L02K02_03B04A04B04[05Z05f06206>06?06M06Y06g07507C07O08008U08cS2sp2PP4LENP2bs1L2LRS2sp2PP4LENP1P3END2bs2p'1L2Hp2LRS2sp2PP4LENP2bs1L2LRS2sp2PP4LENP2bs1L2LRS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF02p'1L2Hp3SPR2LRS2sp2PP4LENP2bs1L2LRS2sp2PP4LENP1P3END2bs2p'1L2LR2Hp2KCS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF02p'1L2Hp3SPR2LRFS2sp2PP4LENP2bs4LENB1L2LRS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF02p'1L2Hp3SPR2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRFS4LENP2bs1L2LRS2PP2bs1L2LRS4LENP2bs1L2LRS4LENP2bs1L2LRS4LENP2bs1L2LRS2PP2bs1L2LRS2sp2PP4LENP2bs4LENB3AL21L3SPR2LRS2sp2PP4LENP2bs3PPB4LENB3AL11L3SPR2LRS4LENP2bs1L2LR". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK BUF bs B1 B3 B4 PPB LENB BUF0 AL1 AL2 SPL LO0 SCS"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Pp',$4.PL,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(5.(18.(10.VP,+1.)R<.)(18.R<.VEND,))P,(19.$2<.R3.VPP,(=.$1:.(1;.(16.&40.R=.))(13.$1:.)))P,(19.$2<.R4.VLENP,(=.$1:.(1;.R=.)(13.$1:.)))P,(19.$2<.R5.(10.(12.&40.Vsp,)-10.)(=.$1:.(2=.#8.R4.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1<.$2<.R6.Vlo,(10.(12.&40.Vsp,)-10.))P,(28.$2<.VAL,VCS,R7.VPP,+8.)P,(28.$2<.VAL,VCS,R8.VLENP,+8.)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R9.)P,(14.$2<.Vm,R:.)P,(15.$2<.R;.)(2:.$2<.VAL,VCS,(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VLENP,)R11.R10.(16.&40.(10.(2>.VPP,+3.)(2?.VAL,)))(16.&40.(2?.VAL,))R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.Vt5,Vt6,)VF,(16.&40.+98?:4.)Vfc,(:.(2.&40.))R<.(;.$2<.)))")
(* [comment removed for export] *).
  Proof.
    intros p' L x5 x6 x7 x13 x14 x17 x28 x29 mm junk Hp HPP HLEN FR ST OPP OLEN MU WM MI. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (bv_unsigned_in_range 64 L) as LR. unfold bv_modulus in LR.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [Z.b2z ?c] => destruct c eqn:KC end.
    - (* [comment removed for export] *)
      apply Z.ltb_lt in KC.
      zstep.
      match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] =>
        replace (Z_to_bv 64 (Z.land x y)) with (Z_to_bv 64 (-96)) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply ret_walk with (r := -96); try eassumption; try lia.
    - apply Z.ltb_ge in KC.
      zstep.
      match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] =>
        replace (Z_to_bv 64 (Z.land x y)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply ret_walk with (r := 0); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0140?K26917854431.92K27714971988.92K44164039966.92K46559006175.92K57066140244.92L22923653376.78L22925878376.81L26921733691.2 L27715122352.2 L29036584927.83L30599044641.78L41202929119.83L43935938480.82L44168742175.3 L45790398623.83L46558990395.2 L47909761398.90L49515715386.89L52067441322.83L53007606158.89L53271535775.83L53812888462.89L54273804052.89L56957661856.89L57066385328.2 L65169320714.80L68515083543.82L68515999329.80L68635998774.88L8468002760.82 L9573028719.89 Q10637070004.88Q10649498890.89Q13671303185.91Q13731009929.88Q14060997130.89Q15861191559.88Q15930096381.87Q17701933584.89Q23544911182.86Q23545509642.87Q23545564728.88Q24201931769.89Q27441842022.87Q27968400810.89Q27968497955.87Q27970480060.84Q28496781288.91Q36438862312.91Q37216054521.89Q39600066516.89Q39676986896.87Q40968284040.84Q43610544776.84Q4453582353.91 Q45360062219.88Q5840558608.90 Q58791244926.87Q58791407863.89Q60030975100.87Q60529804337.87Q61556549392.90Q61847600945.89Q66288959700.87Q66916588147.86Q7174379670.87 Q8188910703.89 Q9487243258.92 00000`01Q02M03C04805@06H06I06J06l08c09E09F09G09i09j0:P0;90;[0<=0<_0>70>^0?@0?A0@70A40B10BS0C50CW0D10DK0E:0ET0EU0F10FH0Fb0G>0GZ0H60HZ0I10IV0J;0J`0KI0L80LY0LZ0M60MT0Mk0NT0Nn0OX0OY0OZ0P80Pg0QN0RA0RB0R^0SH0Sf0T[S2sp2PP3END2bs3DS11j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2PP4LENP3END2bs2D11j3cur2Hj5Hstop2HB5Ha_st5Hl_stS4LENP3END3BUF2bs2D31j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_st2PP2D2S2sp4LENP3END2bs3DS21j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_stS2PP4LENP3END2bs2D11j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_stS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF01j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF01j3cur2Hj4Hcur5Hstop3SPRFFS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t52t61F2fc1m2PP4LENP1P3END2lo2bs3cur1L2x73x283x292mm2Hj5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopFFS2sp2PP4LENP3END2bs1j3cur2Hj5HstopFS2sp2PP4LENP3END3BUF2bs1j3cur2Hj5HstopS2sp2PP4LENP1P3END2bs1j3cur2Hj4Hcur5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2sp2PP4LENP1P3END3BUF2bs2B12B32D12D22D33PPB4LENB3DS13DS23DS31j3cur2Hj4Hcur5Hstop3SPR2KLS2sp2PP4LENP3END2bs1j3cur1L2Hj5Hstop2KLS2sp2PP4LENP3END2bs1j3cur2Hj5HstopFS2sp2PP4LENP3END3BUF2bs2B33PPB4LENB1j3cur2Hj5Hstop3SPRS2sp2PP4LENP1P3END3BUF2bs2B13PPB4LENB1j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4LENP1P3END3BUF2bs2B13PPB4LENB1j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2sp2PP4LENP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS4LENP3END2bs1j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_stS2PP3END2bs1j3cur2Hj5HstopFS4LENP3END2bs1j3cur2Hj5HstopS3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS4LENP3END2bs1j3cur2Hj5HstopS4LENP3END2bs1j3cur2Hj5HstopS4LENP3END2bs1j3cur2Hj5HstopS4LENP3END2bs4LENB1j3cur2Hj5Hstop2HBS3END2bs1j3cur2Hj5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS2PP3END2bs1j3cur2Hj5Hstop2HB5Ha_st5Hl_stS4LENP3END2bs1j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_stS2PP3END2bs3PPB1j3cur2Hj5Hstop2HBFS4LENP3END2bs1j3cur2Hj5HstopS3END3BUF2bs2B31j3cur2Hj5HstopS3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2PP3END2bs1j3cur2Hj5HstopS4LENP3END2bs4LENB1j3cur2Hj5Hstop2HB5Ha_stFFS3END3BUF2bs2B31j3cur2Hj5HstopS2sp2PP4LENP3END2bs4LENB3AL21j3cur2Hj5Hstop3SPRS2PP3END2bs3PPB1j3cur2Hj5Hstop2HB5Ha_stS2sp2PP4LENP3END2bs3PPB4LENB3AL11j3cur2Hj5Hstop3SPRFS4LENP3END2bs1j3cur2Hj5HstopS1P3END3BUF2bs2B14BUF01j3cur2Hj4Hcur5HstopS3END3BUF2bs2B31j3cur2Hj5HstopS2sp2PP4LENP3END2bs1j3cur1L2Hj5Hstop1b2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB LENB BUF0 AL1 AL2 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Pj,$30.Pcur,$4.PL,(2.&40.)Px7,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(5.(31.#1.R8.)(31.R8.#4.))P,(18.(10.VP,+1.)R8.)P,(18.(10.R9.(20.R:.))VEND,)P,(19.$2<.R5.VPP,(=.$1:.(1;.(16.&40.R:.))(13.$1:.)))P,(19.$2<.R6.VLENP,(=.$1:.(1;.R:.)(13.$1:.)))P,(1?.$2<.R7.VBUF,Vbs,)P,(19.$2<.R8.(10.(12.&40.Vsp,)-10.)(=.$1:.(2=.#8.R7.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1<.$2<.R9.Vlo,(10.(12.&40.Vsp,)-10.))P,(28.$2<.VAL,VCS,R:.VPP,+8.)P,(28.$2<.VAL,VCS,R;.VLENP,+8.)P,(28.$2<.VAL,VCS,R<.VBUF,(20.(21.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R=.)P,(14.$2<.Vm,R>.)P,(15.$2<.R?.)(2:.$2<.VAL,VCS,(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(2>.VLENP,+3.)(2?.VAL,)))R14.R13.Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VLENP,)(16.&40.(10.R15.+1.))(16.&40.R15.)(16.&40.(10.(2>.VPP,+3.)(2?.VAL,)))(16.&40.(2?.VAL,))(16.&40.(20.R16.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.Vt5,Vt6,)VF,(16.&40.+99024.)Vfc,(:.(2.&40.))R10.(;.$2<.)))")
(* [comment removed for export] *).
  Proof.
    induction j as [|j IH]; intros cur L x7 x28 x29 mm junk Hj Hcur Hstop HPP HLEN HBUF FR ST OPP OLEN OBUF MU WM MI; [lia|].
    al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk1 OBUF cur.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    get_byte bs (cur - BUF) b NB. read_at HBUF NB (cur - BUF) RD.
    zstep. clear RD. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite (swrap32_id (Z.of_nat (S j) + -1)) by lia.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 (Z.of_nat (S j) + -1)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; lia).
      replace (Z_to_bv 64 (cur + 2)) with (Z_to_bv 64 (cur + 1 + 1)) by (f_equal; lia).
      eapply (IH (cur + 1)); try eassumption; try lia.
    - (* [comment removed for export] *)
      zstep. eapply tail_walk with (p' := cur + 1); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L21856780372.76L27081563761.76L47217930967.76L5548736291.76 L7612225195.76 00000A01R02h04>04OS2sp2PP4LENP1P2bsS2sp2PP4LENP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4LENB3SPL3LO03DS13DS23DS32nn2HN2HES2sp2PP4LENP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4LENB4BUF03SPL3LO03DS13DS23DS32nn2HN2HES2sp2PP4LENP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4LENB4BUF03SPL3LO03DS13DS23DS32nn2HN2HES2sp2PP4LENP1P2bs". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB LENB BUF0 AL1 AL2 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop_entry : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Pnn,$4.Pjw,(2.&40.)Px7,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(5.(18.+1.R7.)(18.R7.+4.))P,(18.(10.(10.VP,+1.)R8.)VEND,)P,(6.(2.&40.)R8.(16.&40.R9.))P,(19.$2<.R5.VPP,(=.$1:.(1;.(16.&40.(10.VP,+1.)))(13.$1:.)))P,(19.$2<.R6.VLENP,(=.$1:.(1;.(16.&40.=))(13.$1:.)))P,(1?.$2<.R7.VBUF,Vbs,)P,(19.$2<.R8.(10.(12.&40.Vsp,)-10.)(=.$1:.(2=.#8.R7.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1<.$2<.R9.Vlo,(10.(12.&40.Vsp,)-10.))P,(28.$2<.VAL,VCS,R:.VPP,+8.)P,(28.$2<.VAL,VCS,R;.VLENP,+8.)P,(28.$2<.VAL,VCS,R<.VBUF,(20.(21.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R=.)P,(14.$2<.Vm,R>.)P,(15.$2<.R?.)(2:.$2<.VAL,VCS,(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(2>.VLENP,+3.)(2?.VAL,)))(16.&40.=)R13.Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VLENP,)(16.&40.(10.VP,+2.))(16.&40.(10.VP,+1.))(16.&40.(10.(2>.VPP,+3.)(2?.VAL,)))(16.&40.(2?.VAL,))R14.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.Vt5,Vt6,)VF,(16.&40.+99024.)Vfc,(:.(2.&40.))R10.(;.$2<.)))")
(* [comment removed for export] *).
  Proof.
    intros nn jw x7 x28 x29 mm junk HN HE -> HPP HLEN HBUF FR ST OPP OLEN OBUF MU WM MI.
    replace (Z_to_bv 64 nn) with (Z_to_bv 64 (Z.of_nat (Z.to_nat nn))) by (f_equal; lia).
    replace (Z_to_bv 64 (P + 2)) with (Z_to_bv 64 (P + 1 + 1)) by (f_equal; lia).
    eapply (loop_walk (Z.to_nat nn) (P + 1)); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02[0?K12226132804.84K26917854431.91K26917854431.96K27714971988.91K27714971988.96K44164039966.84K44164039966.91K44164039966.93K44164039966.96K46559006175.93K46559006175.96K52368581444.84K57066140244.93K57066140244.96L11668900560.75L11668954808.79L11668954808.84L11668962290.76L12222146976.2 L15821664843.92L15823597244.83L15823761858.88L16601122297.86L16605321107.76L1685717371.0  L1804587928.78 L20433961190.80L20736186812.89L21348076663.92L21991189007.78L21993286219.83L21993419083.80L26921733691.2 L27715122352.2 L29036584927.84L29036584927.87L30803094856.82L32049487064.75L35347804779.81L41202929119.76L41202929119.82L41202929119.87L41872764395.78L42812894818.92L42815156885.83L43061431595.78L44168742175.3 L45790398623.84L45790398623.87L46558990395.2 L46748113268.75L46859111120.75L47832358507.88L49490490120.92L508980326.88  L508980326.91  L52368703136.2 L52753443773.88L52753478851.83L52755540020.92L53271535775.82L53271535775.87L57066385328.2 L63152446533.86L64438461917.82L8071348722.83 L8071434021.86 L9817183408.75 Q10637070004.92Q10649498890.82Q10649498890.88Q10649498890.93Q10649814056.81Q10651703251.87Q10732447889.87Q10732447890.90Q1219017780.83 Q13671303185.92Q13671303185.95Q13731009929.92Q13733088494.87Q13735108373.81Q14060997130.82Q14060997130.88Q14060997130.93Q15643324129.80Q15859172962.92Q15859222709.89Q15930096381.85Q15930096381.90Q17701933584.82Q17701933584.88Q17701933584.93Q1954359180.85 Q1954359180.90 Q20568046174.83Q21798041355.83Q2215932912.82 Q2218034128.87 Q23150033886.83Q23542813962.89Q23543520221.92Q23545509642.90Q23545509642.93Q23733024212.87Q23733024215.90Q23733452788.87Q23735521236.82Q23735546217.85Q23735546217.90Q24201931769.90Q24201931769.93Q25457592038.83Q25513505925.83Q26611046992.83Q28496781288.90Q28496781288.95Q31394594844.83Q36438862312.92Q36438862312.95Q37216054521.88Q37216054521.93Q37343932385.87Q37343932386.90Q37345667932.85Q37345667932.90Q39600066516.82Q39600066516.88Q39600066516.93Q39676986896.90Q39676986896.93Q41126203749.83Q43608320682.82Q43610462858.87Q44034257392.83Q4453582353.90 Q4453582353.95 Q4470399284.83 Q45353748076.87Q45355636119.81Q45360062219.92Q45914037331.81Q47120844340.83Q49698585326.82Q53519952433.83Q57351519894.85Q57351519894.90Q58146298210.83Q5840558608.91 Q5840558608.94 Q60529804337.90Q60529804337.93Q61556549392.89Q61556549392.94Q61847600945.82Q61847600945.88Q61847600945.93Q62641111670.85Q62641111670.90Q63037100374.83Q66288959700.90Q66288959700.93Q66715549212.83Q66918372576.92Q66918685239.89Q8204118352.83 Q9487243258.84 Q9487243258.91 Q9487243258.93 Q9487243258.96 Q9843367298.80 00000P00o01Q02102T03503T04604`05B05d06F06g07H08?09609m0:d0:e0;B0;\0<90=30=j0=k0>W0>f0?>0??0?W0?o0@G0@H0@I0@X0@j0@k0A:0AI0AX0Ag0B90BK0B]0Bl0CB0CC0CR0Cd0Ce0D40DG0DY0E50EJ0E_0E`0F;0FS0Fn0G=0GO0GP0Ge0I>0IR0Ii0J`0Jj0K10K80KB0KI0KP0Kd0L80LE0L`0M;0ME0ML0MS0MT0MU0MV0M`0Ml0N50N90N=0ND0NK0NU0Ng0O90O:0O;0OO0Oc0P00P90PE0PN0PZ0Pg0Q40QA0QN0Q[0Qh0R90RM0RN0Rj0Rk0SC0S^0Sb0T=0TX0Tf0U70U80U90U:0U;0U<0U=0U>0UG0US0UT0UX0U\0Uh0V@0V[0V\0Vc0Vj0W40W>0W?0WS0W`0X40XH0Xh0Y?0YY0Z50ZT0Zh0[?0[_0\?0\b0\h0\n0]:0];0]<0]H0]T0]]0]^0^?0^_0_@0_c0`1S2ra2sp2PP2bs3DS12HB5Ha_st5Hl_stS2sp2PP1P2bs3DS12HB5Ha_st5Hl_stS2sp2PP1P2bs3DS12nn2HB5Ha_st5Hl_stS2PP4LENP1P2bs2D12HB5Ha_st5Hl_stS2PP4LENP1P2bs2D12nn2HB5Ha_st5Hl_stS2ra2sp3BUF2bs3DS32HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stS4LENP3BUF2bs2D32b02HB5Ha_st5Hl_stS4LENP3BUF2bs2D32nn2HB5Ha_st5Hl_st2PP1P2D2S2sp4LENP2bs3DS22b02HB5Ha_st5Hl_stS2sp4LENP2bs3DS22nn2HB5Ha_st5Hl_stS2ra2sp4LENP2bs3DS22HB5Ha_st5Hl_stS2PP4LENP2bs2D12b02HB5Ha_st5Hl_stS2PP4LENP2bs2D12nn2HB5Ha_st5Hl_stS2sp2PP4LENP1P3END3BUF2bs2B12B22B32B43PPB4LENB4BUF03SPRS2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF03SPR2K0S2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF03SPR2K0S2sp2PP4LENP1P3END3BUF2bs2B12B32B43PPB4LENB4BUF03SPR2K0FS2sp2PP4LENP1P3END2bs4lenv2nnS2sp2PP4LENP1P3END2bs4lenvS2sp2PP4LENP1P3END2bs4lenv2b0S2sp2PP4LENP1P3END3BUF2bs2B12B22B32B43PPB4LENB4BUF03SPR2nnS2sp2PP4LENP1P3END3BUF2bs2B12B22B32B43PPB4LENB4BUF03SPRSS2sp2PP4LENP1P3END3BUF2bs2B33PPB4LENB3SPR2K0S2sp2PP4LENP2bsS2sp2PP4LENP1P3END2bs2K0FS2sp2PP4LENP1P3BUF2bs2B1S2sp2PP4LENP1P3BUF2bs2B1S2sp2PP4LENP1P3BUF2bs2B1FFS2sp2PP4LENP2bsS2sp2PP4LENP2bs2nnFS2sp2PP4LENP2bsS2sp2PP4LENP2bsS2sp2PP4LENP2bsS2sp2PP4LENP2bsS2sp2PP4LENP2bs2nnS2AL2sp2PP4LENP2bsS2sp2PP4LENP2bs2nnS2sp2PP4LENP2bsS2sp2PP4LENP2lo2bs3SPLFS2sp2PP4LENP2bsS2sp2PP4LENP2bs2nnFS2sp2PP4LENP2bsS2sp2PP4LENP2bs3PPBS2sp2PP4LENP2bs2b0S2sp2PP4LENP1P3END2bs2nn3KgeS2sp2PP4LENP1P3BUF2bsS2sp2PP4LENP1P3BUF2bsFS2sp2PP4LENP1P3END2bs2B22b0S2sp2PP4LENP1P3END2bs2B2S2sp2PP4LENP1P3END2bs2B22nnS2sp2PP4LENP2bsS2sp2PP4LENP2bs2nnFS2sp2PP4LENP2bs2nn2NRS2sp2PP4LENP1P3END2bs2B21K3BUF2lo2B12B32B42D12D22D33PPB4LENB4BUF03SPL3LO03DS13DS23DS33SPRS2sp2PP4LENP2bs4LENBS2sp2PP4LENP2bs4LENB2nnS2sp2PP4LENP1P3END3BUF2bs2B12B22B32B43PPB4LENB4BUF03SPRS2PP2bs2nnS2PP2bsS2PP2bsS2PP2bs2nnS2PP2bsS2PP2bsS1P3END3BUF2bs2B32K0S1P3END3BUF2bs2B32K0S2AL2bs5ALWF'S4LENP2bs2b02HB5Ha_st5Hl_stS4LENP2bs2nn2HB5Ha_st5Hl_stS2PP2bs2nnS2PP2bsS2PP2bsFFFS2sp2lo2bsS4LENP2bs2nnS4LENP2bsS2bsS2bsS2PP2bsS2PP2bsS2PP2bs2nnS1P3BUF2bs2B14BUF0S1P3BUF2bs2B14BUF0FFS1P3END3BUF2bs2B32K0S1P3END3BUF2bs2B32K0S2AL2bs5ALWF'S4LENP2bsS4LENP2bs2nnS4LENP2bsS4LENP2bs2nnS1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S4LENP2bs4LENB2HBS4LENP2bs4LENB2nn2HBFS2ra2sp2lo2bs2HB5Ha_st5Hl_stFS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2nn2HB5Ha_st5Hl_stS2bsS4LENP2bs2b02HB5Ha_st5Hl_stS4LENP2bs2nn2HB5Ha_st5Hl_stS2PP2bs3PPB2HBS2PP2bs3PPB2nn2HBFFFFFFFS4LENP2bsS4LENP2bs2nnFS2bsS2bsS2AL2bs4IMG'S2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2nn2HB5Ha_st5Hl_stFS2PP2bsS2PP2bsS2PP2bs2nnS2sp2bs2HBFS2sp2bs3SPR2HB5Ha_stS2AL2bs5ALWF'S1P3END3BUF2bs2B32K0S1P3END3BUF2bs2B32K0S2ra2sp2lo2bs3SPL2HB5Ha_st5Hl_stS4LENP2bs4LENB2HB5Ha_stS4LENP2bs4LENB2nn2HB5Ha_stS2sp2PP4LENP2bs4LENB3AL23SPRS2sp2PP4LENP2bs4LENB3AL23SPR2nnS2PP2bs3PPB2HB5Ha_stS2PP2bs3PPB2nn2HB5Ha_stS2sp2PP4LENP2bs3PPB4LENB3AL13SPRS2sp2PP4LENP2bs3PPB4LENB3AL13SPRS2sp2PP4LENP2bs3PPB4LENB3AL13SPR2nnS1P2bsS1P2bsS2AL2bs4IMG'FFS2AL2bs4IMG'S4LENP2bs2nnS4LENP2bsFS2ra2sp2PP4LENP2bs2HB5Ha_st5Hl_stS2sp2PP4LENP1P2bs2HB5Ha_st5Hl_stS2sp2PP4LENP2bs2b02HB5Ha_st5Hl_stS2sp2PP4LENP2bs2nn2HB5Ha_st5Hl_st1PS2sp2lo2bs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B2 B3 B4 D1 D2 D3 PPB LENB BUF0 AL1 AL2 SPL LO0 SCS DS1 DS2 DS3"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Plenv,(2.&40.)P,(19.$2<.Vm,VPP,(=.$1:.(1;.(16.&40.VP,))(13.$1:.)))P,(19.$2<.Vm,VLENP,(=.$1:.(1;.R2.)(13.$1:.)))P,(1?.$2<.Vm,VBUF,Vbs,)P,(15.$2<.Vm,)P,(27.$2<.VAL,Vm,)P,(28.$2<.VAL,VCS,Vm,VPP,+8.)P,(28.$2<.VAL,VCS,Vm,VLENP,+8.)P,(28.$2<.VAL,VCS,Vm,VBUF,(20.(21.(2.&8.)Vbs,)))P,(1<.$2<.Vm,Vlo,(12.&40.Vsp,))(2:.$2<.VAL,VCS,(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VLENP,)R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+98?28.)Vfc,(:.(2.&40.))Vm,(;.$2<.)))")
(* [comment removed for export] *).
  Proof.
    intros a3 a4 a5 a6 a7 lenv HPP HLEN HBUF MI AB OPP OLEN OBUF ST. al_facts.
    pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB.
    rewrite (proj1 IMG) in GOT.
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      assert (EP : END = P) by (apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia).
      eapply ret_walk with (r := -96) (p' := P); try eassumption; try lia. }
    clear K1.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF P.
    (* [comment removed for export] *)
    get_byte bs (P - BUF) b0 NB0. read_at HBUF NB0 (P - BUF) RD0.
    zstep. clear RD0. zstep. if_cases Ksg; zify_cond Ksg.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      { (* [comment removed for export] *)
        pose proof (land_127_range (bv_unsigned (sxb b0))) as NR.
        set (nn := Z.land (Z.land (bv_unsigned (sxb b0)) 255) 127) in *.
        pose proof (longform_n nn NR Kn) as HN. clearbody nn.
        zstep. if_cases Kge; zify_cond Kge.
        { (* [comment removed for export] *)
          eapply ret_walk with (r := -96) (p' := P); try eassumption; try lia. }
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        eapply loop_entry with (nn := nn); try eassumption; try lia; try reflexivity. }
      (* [comment removed for export] *)
      zstep. zstep. eapply ret_walk with (r := -100) (p' := P); try eassumption; try lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk1 OBUF P.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    read_at HBUF NB0 (P - BUF) RD1. zstep. clear RD1. zstep.
    eapply tail_walk with (p' := P + 1); try eassumption; try lia.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_asn1_get_len_spec : forall AL, asan_img_ok AL -> asn1_get_len_stmtA asegs AL A_ASN1_GET_LEN.
Proof.
  intros AL IMG. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN.
  intros until lenv. intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI ALWF CSOK AB OPP OLEN OBUF ST SPL SPA SCS DS1 DS2 DS3 -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.

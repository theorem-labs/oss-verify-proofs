(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_asn1_get_int_loops.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
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
Ltac2 gd_tbl_A_asn1_get_int () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.A.A_asn1_get_int_loops.asn1_get_int_postA"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.LibA.AShadow.abase"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : VALP mod 4 = 0.
  Hypothesis SPL : lo <= bv_unsigned sp - 16.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : VALP + 4 <= lo \/ bv_unsigned sp <= VALP.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - 16, bv_unsigned sp)].
  Notation POST := (asn1_get_int_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHPP := (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00m0?L24111420455.87L24111426329.92L24111427218.86L3196084676.92 L32465650701.83L39864816189.87L39864821896.86L39864823043.92L41202929119.80L41202929119.82L41202929119.87L42814994432.86L43363777942.92L44074763222.93L44372709270.85L44373628128.83L47832354315.92L47832363317.87L52423106317.92L61565324574.81L61565331540.84L61565418556.79L64180445855.80L64517196828.92L9817085104.79 Q10532772112.92Q10649498890.86Q10649498890.88Q10649498890.93Q10649602612.92Q10649613578.87Q10649715752.85Q11325740407.92Q11326156611.87Q11326165502.90Q13735186697.92Q13735194167.87Q13735272213.85Q14732311517.87Q15930096381.90Q17701933584.86Q17701933584.88Q17701933584.93Q38758237731.90Q39600066516.86Q39600066516.88Q39600066516.93Q41746550691.90Q41746909994.92Q43608320682.87Q45355799959.85Q45355850635.92Q45355852981.87Q55366643217.90Q57202208522.86Q57202208522.88Q57202208522.93Q61847600945.86Q61847600945.88Q61847600945.93Q66664606784.9000000P01001P01Q02F02_03803Q03e04904M04a05A05\06P07D07X07l08C09B0:A0;@0<?0<]0=\0>90>E0>Q0>]0>i0?50?A0?]0@90@U0@a0@m0A90AV0A_0Ak0B70BC0Bd0Be0Bf0Bg0Bh0Bi0C20C>0CJ0CV0D30D40D50D60D[0E@0Ee0F1S2sp2PP4VALP1P3END2bs2p11L2Hp2LRS2sp2PP4VALP1P3END2bs2p11L2Hp2LRS2sp2PP4VALP1P3END2bs2p11L2Hp2LRFS2sp2PP4VALP3END3BUF2bs2B33PPB4VALB2p11L3SPR2LR2KC2K0S2sp2PP4VALP1P2bs2p11L2LRS2sp2PP4VALP1P2bs2p11L2LRS2sp2PP4VALP1P2bs2p11L2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP1P3END2bs2p11L2Hp2LRS2sp2PP4VALP3BUF2bs2p11L2LRS2sp2PP4VALP1P3END3BUF2bs2B13PPB4VALB2p11L2Hp3SPR2LRS2sp2PP4VALP1P3END3BUF2bs2B13PPB4VALB2p11L2Hp3SPR2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP2bs1L2LRS2sp2PP4VALP2bs1L2LR2K0S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF02p11L2Hp3SPR2LRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF02p11L2Hp3SPR2LRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF02p11L2Hp3SPR2LRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF02p11L2Hp3SPR2LRS2sp2PP4VALP3END2bs2p11L2LR2KCS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF02p11L2Hp3SPR2LRS3END3BUF2bs2B32p11L2LR2KC2K0S2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS1P3END3BUF2bs2B12p11L2Hp2LRS1P3END3BUF2bs2B12p11L2Hp2LRS1P3END3BUF2bs2B12p11L2Hp2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS3END3BUF2bs2B32p11L2LR2KC2K0S2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS1P3END3BUF2bs2B14BUF02p11L2Hp2LRFFFFFS2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS2PP2bs1L2LRS3END3BUF2bs2B32p11L2LR2KC2K0FFFS2sp2PP4VALP2bs3PPB4VALB3AL11L3SPR2LRS2sp2PP4VALP2bs3PPB4VALB3AL11L3SPR2LRS2sp2PP4VALP2bs3PPB4VALB3AL11L3SPR2LRS2bs2p11L2LR". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma j1_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int ()) "Pp1,$0.PL,(1.&40.)Pv,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Px14,(1.&40.)Px15,(1.&40.)Px28,(1.&40.)Px29,(1.&40.)Pmm,P,(1.&40.)(2.(1.&8.))Pjunk,(3.(1.&8.))P,(4.(5.(6.VP,+2.)R;.)(5.R;.VEND,))P,(7.$8.R3.VPP,(9.$:.(;.(<.&40.R<.))(=.$:.)))P,(7.$8.R4.VVALP,(9.$:.(>.R;.)(=.$:.)))P,(?.$8.R5.VBUF,Vbs,)P,(7.$8.R6.(6.(10.&40.Vsp,)-10.)(9.$:.(11.#8.R5.)(9.$:.(;.Vra,)(=.$:.))))P,(12.$8.R7.Vlo,(6.(10.&40.Vsp,)-10.))P,(13.$8.VAL,VCS,R8.VPP,+8.)P,(13.$8.VAL,VCS,R9.VVALP,+4.)P,(13.$8.VAL,VCS,R:.VBUF,(14.(15.(1.&8.)Vbs,)))P,(16.(9.(17.$0.$0.)(18.$0.$0.VPP,(6.VPP,+8.))(9.(17.$0.$0.)(18.$0.$0.VVALP,(6.VVALP,+4.))(9.(17.$0.$0.)(18.$0.$0.(19.(10.&40.Vsp,)+10.)(10.&40.Vsp,))(=.(17.$0.$0.)))))Vm,R;.)P,(1:.$8.Vm,R<.)P,(1;.$8.R=.)(1<.$8.VAL,VCS,(1=.$8.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(1>.(1?.Vra,(<.&40.(6.(10.&40.Vsp,)-10.))Vgp,Vtp,(<.&40.(6.(20.VPP,+3.)(21.VAL,)))R14.R13.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)R16.(<.&40.VVALP,)R12.R11.(<.&40.-60.)(<.&40.(21.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.Vt5,Vt6,)VF,(<.&40.+9958<.)Vfc,(22.(1.&40.))R>.(23.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros p1 L v x6 x7 x14 x15 x28 x29 mm junk Hp HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (bv_unsigned_in_range 64 L) as LR. unfold bv_modulus in LR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC.
    { rewrite ?unsigned_lit in KC by lia. eapply ret_walk with (r := -96) (p' := p1); try eassumption; try lia. }
    rewrite ?unsigned_lit in KC by lia.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0.
    { rewrite ?unsigned_lit in K0 by lia. eapply ret_walk with (r := -100) (p' := p1); try eassumption; try lia. }
    rewrite ?unsigned_lit in K0 by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    shadow_chk1 OBUF p1.
    (* [comment removed for export] *)
    get_byte bs (p1 - BUF) b NB. read_at HBUF NB (p1 - BUF) RD.
    zstep. clear RD. zstep. if_cases KN; zify_cond KN.
    { eapply ret_walk with (r := -100) (p' := p1); try eassumption; try lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply loop2_walk with (cur := p1) (rem := bv_unsigned L); try eassumption; try lia.
    reflexivity. symmetry; apply Z_to_bv_bv_unsigned.
    all: match goal with |- ?g => idtac "J1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?K24753660756.93K26917854431.93K44164039966.93L22923653376.79L22925878376.82L24753455024.2 L26701802538.90L26921733691.2 L41202929119.84L43938004642.83L44168742175.3 L47909761398.91L52067441322.84L53007606158.90L53271535775.84L54273804052.90L56957661856.90L58902353609.79L65169320714.81L68515083543.83L68515999329.81L68648805324.87L8463380018.81 L8517161022.90 L9573028719.90 Q10649498890.88Q10649685048.89Q10650081102.87Q13734317171.87Q15930096381.88Q17701933584.88Q27441842022.88Q27968400810.90Q27968497955.88Q27970480060.85Q28496781288.92Q37216054521.90Q39600066516.88Q40968284040.85Q43610544776.85Q4453582353.92 Q45355769223.89Q57202208522.88Q58791244926.88Q58791407863.90Q60030975100.88Q61556549392.91Q61847600945.88Q7174379670.88 Q8188910703.90 Q9487243258.93 00000a01X02H03P04X04Y05B05C05e05f05g06M06o07Q08308X09:0;10;g0<d0=a0>C0>e0@D0@f0A@0AZ0B40BN0Be0C?0CV0D;0D`0EE0En0FO0FP0Fn0GE0Gn0HH0HI0HJ0HK0Hi0IP0JC0Jm0KK0L<S2PP4VALP3END2bs2D11j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2sp2PP3END2lo2bs3SPL3DS11j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2PP3END3BUF2bs2D21j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01j3cur2Hj4Hcur5Hstop3SPRFS2sp2PP4VALP1P3END2bs1j3cur2Hj4Hcur5HstopFS2sp2PP4VALP3END2bs1j3cur2Hj5HstopFFS2sp2PP4VALP3END3BUF2bs1j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5Hstop2KLS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t52t61F2fc1m2PP4VALP1P3END2lo2bs3cur1L2x73x283x292mm2Hj5HstopS2sp2PP4VALP3END3BUF2bs2B33PPB4VALB1j3cur2Hj5Hstop3SPRS2sp2PP4VALP1P3END3BUF2bs2B13PPB4VALB1j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4VALP1P3END3BUF2bs2B13PPB4VALB1j3cur2Hj4Hcur5Hstop3SPRS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31j3cur2Hj4Hcur5Hstop3SPR2KLS2sp2PP4VALP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5HstopS3END2bs1j3cur2Hj5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS1P3END3BUF2bs2B11j3cur2Hj4Hcur5HstopS2PP3END2bs1j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2PP3END2bs3PPB1j3cur2Hj5Hstop2HBFS3END3BUF2bs2B31j3cur2Hj5HstopS3END2bs1j3cur2Hj5HstopS2PP3END2bs1j3cur2Hj5Hstop2HB5Ha_st5Hl_stS2PP3END2bs1j3cur2Hj5HstopFFFS3END3BUF2bs2B31j3cur2Hj5HstopS2PP3END2bs3PPB1j3cur2Hj5Hstop2HB5Ha_stS2sp2PP4VALP3END2bs3PPB4VALB3AL11j3cur2Hj5Hstop3SPRS1P3END3BUF2bs2B14BUF01j3cur2Hj4Hcur5HstopS3END3BUF2bs2B31j3cur2Hj5HstopS2sp2PP4VALP3END2bs1j3cur2Hj5Hstop2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int ()) "Pj,$24.Pcur,$0.PL,(1.&40.)Pv,(1.&40.)Px7,(1.&40.)Px28,(1.&40.)Px29,(1.&40.)Pmm,P,(1.&40.)(2.(1.&8.))Pjunk,(3.(1.&8.))P,(4.(25.#1.R9.)(25.R9.#4.))P,(5.(6.VP,+2.)R9.)P,(5.(6.R:.(14.R;.))VEND,)P,(7.$8.R5.VPP,(9.$:.(;.(<.&40.R;.))(=.$:.)))P,(7.$8.R6.VVALP,(9.$:.(>.R:.)(=.$:.)))P,(?.$8.R7.VBUF,Vbs,)P,(7.$8.R8.(6.(10.&40.Vsp,)-10.)(9.$:.(11.#8.R7.)(9.$:.(;.Vra,)(=.$:.))))P,(12.$8.R9.Vlo,(6.(10.&40.Vsp,)-10.))P,(13.$8.VAL,VCS,R:.VPP,+8.)P,(13.$8.VAL,VCS,R;.VVALP,+4.)P,(13.$8.VAL,VCS,R<.VBUF,(14.(15.(1.&8.)Vbs,)))P,(16.(9.(17.$0.$0.)(18.$0.$0.VPP,(6.VPP,+8.))(9.(17.$0.$0.)(18.$0.$0.VVALP,(6.VVALP,+4.))(9.(17.$0.$0.)(18.$0.$0.(19.(10.&40.Vsp,)+10.)(10.&40.Vsp,))(=.(17.$0.$0.)))))Vm,R=.)P,(1:.$8.Vm,R>.)P,(1;.$8.R?.)(1<.$8.VAL,VCS,(1=.$8.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(1>.(1?.Vra,(<.&40.(6.(10.&40.Vsp,)-10.))Vgp,Vtp,(<.&40.(6.(20.VPP,+3.)(21.VAL,)))(<.&40.(14.R17.))R13.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)R15.(<.&40.VVALP,)(<.&40.(6.R16.+1.))(<.&40.R16.)(<.&40.-60.)(<.&40.(21.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.Vt5,Vt6,)VF,(<.&40.+9966<.)Vfc,(22.(1.&40.))R10.(23.$8.)))")
(* [comment removed for export] *).
  Proof.
    induction j as [|j IH]; intros cur L v x7 x28 x29 mm junk Hj Hcur Hstop HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI; [lia|].
    al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk1 OBUF cur.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite (swrap32_id (Z.of_nat (S j) + -1)) by lia.
    (* [comment removed for export] *)
    get_byte bs (cur - BUF) b NB. read_at HBUF NB (cur - BUF) RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 (Z.of_nat (S j) + -1)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; lia).
      replace (Z_to_bv 64 (cur + 2)) with (Z_to_bv 64 (cur + 1 + 1)) by (f_equal; lia).
      eapply (IH (cur + 1)); try eassumption; try lia.
    - (* [comment removed for export] *)
      zstep. eapply j1_walk with (p1 := cur + 1); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L27081563761.77L39931892532.77L4345593543.77 L47940853355.77L5548736291.77 00001A01R02h03904OS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3LO03DS13DS23DS32nn2HN2HES2sp2PP4VALP1P2bsS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB4BUF03SPL3LO03DS13DS23DS32nn2HN2HES2sp2PP4VALP1P2bsS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB4BUF03SPL3LO03DS13DS23DS32nn2HN2HE". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop1_entry : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int ()) "Pnn,$0.Pjw,(1.&40.)Pv,(1.&40.)Px7,(1.&40.)Px28,(1.&40.)Px29,(1.&40.)Pmm,P,(1.&40.)(2.(1.&8.))Pjunk,(3.(1.&8.))P,(4.(5.+1.R8.)(5.R8.+4.))P,(5.(6.(6.VP,+2.)R9.)VEND,)P,(26.(1.&40.)R9.(<.&40.R:.))P,(7.$8.R5.VPP,(9.$:.(;.(<.&40.(6.VP,+2.)))(=.$:.)))P,(7.$8.R6.VVALP,(9.$:.(>.R:.)(=.$:.)))P,(?.$8.R7.VBUF,Vbs,)P,(7.$8.R8.(6.(10.&40.Vsp,)-10.)(9.$:.(11.#8.R7.)(9.$:.(;.Vra,)(=.$:.))))P,(12.$8.R9.Vlo,(6.(10.&40.Vsp,)-10.))P,(13.$8.VAL,VCS,R:.VPP,+8.)P,(13.$8.VAL,VCS,R;.VVALP,+4.)P,(13.$8.VAL,VCS,R<.VBUF,(14.(15.(1.&8.)Vbs,)))P,(16.(9.(17.$0.$0.)(18.$0.$0.VPP,(6.VPP,+8.))(9.(17.$0.$0.)(18.$0.$0.VVALP,(6.VVALP,+4.))(9.(17.$0.$0.)(18.$0.$0.(19.(10.&40.Vsp,)+10.)(10.&40.Vsp,))(=.(17.$0.$0.)))))Vm,R=.)P,(1:.$8.Vm,R>.)P,(1;.$8.R?.)(1<.$8.VAL,VCS,(1=.$8.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(1>.(1?.Vra,(<.&40.(6.(10.&40.Vsp,)-10.))Vgp,Vtp,(<.&40.(6.(20.VPP,+3.)(21.VAL,)))R15.R13.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.=)(<.&40.VVALP,)(<.&40.(6.VP,+3.))(<.&40.(6.VP,+2.))(<.&40.-60.)(<.&40.(21.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.Vt5,Vt6,)VF,(<.&40.+9966<.)Vfc,(22.(1.&40.))R10.(23.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros nn jw v x7 x28 x29 mm junk HN HE -> HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI.
    replace (Z_to_bv 64 nn) with (Z_to_bv 64 (Z.of_nat (Z.to_nat nn))) by (f_equal; lia).
    replace (Z_to_bv 64 (P + 3)) with (Z_to_bv 64 (P + 2 + 1)) by (f_equal; lia).
    eapply (loop1_walk (Z.to_nat nn) (P + 2)); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02e0@K11417993028.84 K12226132804.84 K24753660756.102K24753660756.91 K24753660756.97 K26917854431.102K26917854431.91 K26917854431.97 K44164039966.102K44164039966.84 K44164039966.91 K44164039966.97 L11418330016.2  L11668900560.75 L11668954808.79 L11668962290.76 L12222146976.2  L12550742471.86 L12551142084.84 L12551142087.89 L14400193759.89 L14400236163.94 L14402332938.98 L16070426553.94 L16070426553.97 L16108054177.92 L16110144372.82 L16605321107.76 L1685717371.0   L1804587928.78  L20433961190.80 L21348076663.98 L21991189007.78 L21993419083.80 L24150417681.84 L24753455024.2  L24782519217.95 L26921733691.2  L30803094856.88 L32049487064.75 L35347804779.87 L37917973656.98 L41202929119.76 L41202929119.82 L41202929119.88 L41202929119.93 L41872764395.78 L42812894818.98 L42815144887.89 L42815156885.83 L43061431595.78 L44168742175.3  L46748113268.75 L46859111120.75 L47832358507.94 L49921682489.94 L49921901157.89 L49923780528.98 L50091493243.82 L50091499700.85 L50091499700.90 L50091501498.81 L508980326.88   L52753442471.87 L52753478851.83 L53271535775.82 L53271535775.88 L53271535775.93 L60929927345.87 L63152446533.92 L64438461917.82 L6958177821.88  L8326768114.83  L8327002006.87  L9817098198.81  L9817183408.75  Q10649498890.82 Q10649498890.88 Q10649498890.94 Q10649498890.99 Q10649605966.87 Q10649814056.81 Q10651703251.93 Q10651703773.98 Q10732447889.87 Q1219017780.83  Q13074342371.93 Q13074443200.93 Q13074443201.96 Q13076419398.88 Q13076443006.91 Q13076443006.96 Q13733085920.98 Q13733088494.93 Q13735108373.81 Q13735185523.87 Q15063504633.91 Q15063504633.96 Q15643324129.80 Q15930096381.85 Q15930096381.91 Q15930096381.96 Q17701933584.82 Q17701933584.88 Q17701933584.94 Q17701933584.99 Q1954359180.85  Q20568046174.83 Q21027042243.91 Q21027042243.96 Q21028779900.96 Q21028779901.93 Q21798041355.83 Q2215932912.82  Q23150033886.83 Q23733024212.87 Q23735521236.82 Q23735546217.85 Q25457592038.83 Q25513505925.83 Q26611046992.83 Q28496781288.101Q28496781288.90 Q28496781288.96 Q30485177150.96 Q30485177151.93 Q31394594844.83 Q31407341477.93 Q31409376512.88 Q32871135979.91 Q32871135979.96 Q37216054521.88 Q37216054521.94 Q37216054521.99 Q37343932385.87 Q37345667932.85 Q39600066516.82 Q39600066516.88 Q39600066516.94 Q39600066516.99 Q41126203749.83 Q43608320047.88 Q43608320682.82 Q43610462858.93 Q44034257392.83 Q4453582353.101 Q4453582353.90  Q4453582353.96  Q45353748076.93 Q45353748578.98 Q45355636119.81 Q45355845361.87 Q45914037331.81 Q47120844340.83 Q49698585326.82 Q5257172243.91  Q5257172243.96  Q53519952433.83 Q57202208522.82 Q57202208522.88 Q57202208522.94 Q57202208522.99 Q57351519894.85 Q58146298210.83 Q61556549392.100Q61556549392.89 Q61556549392.95 Q61847600945.82 Q61847600945.88 Q61847600945.94 Q61847600945.99 Q62641111670.85 Q6268859444.83  Q63037100374.83 Q66715549212.83 Q8416710736.83  Q9487243258.102 Q9487243258.84  Q9487243258.91  Q9487243258.97  Q9843367298.80  00000Y01@01c02C02c03L04204X05:05b06A06`06a07X08O09F09G09_0:70:O0:`0;40;H0;]0<20<P0=G0>>0>?0>k0?:0?;0?S0?k0@W0@X0A00A10A20AA0AP0Al0B;0BJ0BY0Bk0C=0CO0C^0Cm0DC0DD0DS0Df0E80ES0Ek0FF0G=0H40Hk0Ib0J70JO0Jg0K60KE0KW0Kf0L;0MT0Nn0O?0OP0PG0Q>0QE0QL0QS0Q]0Qd0Qk0R20R<0RP0R]0Rj0S70SD0SQ0S^0Sk0T50T<0TC0TJ0T^0U20U<0U@0UD0UH0UO0UV0U]0Ug0V90V:0V;0V<0V=0V>0V?0VS0V`0Vm0W:0WG0WH0Wd0We0X@0XX0Y00YD0YX0Y\0Z00ZD0ZV0Zh0[60[D0[U0[V0[W0[X0[Y0[Z0[[0[\0[`0[d0[h0\40\O0\g0]?0]F0]P0]W0]^0]h0]i0^=0^C0^I0^V0^W0^X0^Y0^Z0^n0_N0_e0`90`M0`m0aM0am0bP0bV0bW0bc0bo0c00cS0d40dT0e40eBS2ra2sp4VALP2lo2bs3SPL3DS22HB5Ha_st5Hl_stS2ra2sp2PP2lo2bs3SPL3DS12HB5Ha_st5Hl_stS2PP4VALP1P2bs2D12nn2HB5Ha_st5Hl_stS2PP4VALP1P2bs2D12HB5Ha_st5Hl_stS2PP4VALP1P2bs2D12HB5Ha_st5Hl_stS2sp2PP1P2lo2bs3SPL3DS12nn2HB5Ha_st5Hl_stS2sp2PP1P2lo2bs3SPL3DS12HB5Ha_st5Hl_stS2sp2PP1P2lo2bs3SPL3DS12HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22nn2HB5Ha_st5Hl_stS2ra2sp3BUF2lo2bs3SPL3DS32HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stFS2sp2PP4VALP1P3END3BUF2bs2B12B22B32B43PPB4VALB4BUF03SPRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K0S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K0FS2sp2PP4VALP1P3BUF2bs2B1S2sp2PP4VALP1P3BUF2bs2B1S2sp2PP4VALP1P3BUF2bs2B1S2sp2PP4VALP1P2bsS2sp2PP4VALP1P2bs2b1S2sp2PP4VALP1P2bs2nnS2sp2PP4VALP1P3BUF2bsS2sp2PP4VALP1P3BUF2bsS2sp2PP4VALP1P3END2bs2K12K32nnS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K0S2sp2PP4VALP1P3END3BUF2bs2B12B22B32B43PPB4VALB4BUF03SPRSS2sp2PP4VALP1P3END3BUF2bs2B33PPB4VALB3SPR2K0S2sp2PP4VALP2bsFS2sp2PP4VALP1P3BUF2bs2B1S2sp2PP4VALP1P3BUF2bs2B1S2sp2PP4VALP1P3END3BUF2bs2B33PPB4VALB3SPR2K1FS2sp2PP4VALP1P3END2bs2K1FFS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP1P3END2bs2nn3KgeS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2bs2nnS2AL2sp2PP4VALP2bsS2sp2PP4VALP2bs2nnS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2lo2bs3SPLFS2sp2PP4VALP2bsS2sp2PP4VALP2bs3PPBS2sp2PP4VALP2bs2b1S2sp2PP4VALP1P3END2bs2K12b1S2sp2PP4VALP1P3END2bs2K0S2sp2PP4VALP1P3END2bs2K12nnS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K1S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K1S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K1S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K0S2sp2PP4VALP1P3BUF2bsS2sp2PP4VALP1P3END2bs2B2S2sp2PP4VALP1P3END2bs2B2S2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2bs2nnS2sp2PP4VALP2bsS2sp2PP4VALP2bs2nn2NRS2sp2PP4VALP1P3END2bs2B21K3BUF2lo2B12B32B42D12D22D33PPB4VALB4BUF03SPL3LO03DS13DS23DS33SPRS2sp2PP4VALP1P3END2bs2K02K23BUF2lo2B12B32B42D12D22D33PPB4VALB4BUF03SPL3LO03DS13DS23DS33SPRS2sp2PP4VALP1P2bsS2sp2PP4VALP1P2bsS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03SPR2K0S2sp2PP4VALP1P3END3BUF2bs2B12B22B32B43PPB4VALB4BUF03SPRS2PP2bsS2PP2bsS2PP2bsS2PP2bs2nnS2PP2bsS2PP2bsS2PP2bsS2PP2bs2nnS1P3END3BUF2bs2B32K0S2AL2bs5ALWF'S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S2PP2bs2nnS2PP2bsS2PP2bsS2PP2bsS1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S2sp2lo2bsS2bsS2bsS2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bs2nnS1P3BUF2bs2B14BUF0FFFFFFS1P3END3BUF2bs2B32K0S2AL2bs5ALWF'S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1FS2ra2sp2lo2bs2HB5Ha_st5Hl_stFS2PP1P2bs2nn2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S2bsS1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S1P3BUF2bs2B14BUF0S1P3BUF2bs2B14BUF0S2PP2bs3PPB2HBS2PP2bs3PPB2HBS2PP2bs3PPB2nn2HBFFFFFFFS2bsS2bsS2bsS2AL2bs4IMG'S2PP1P2bs2nn2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP2bsS2PP2bs2nnS2PP2bsS2PP2bsS2sp2bs2HBFS2sp2bs3SPR2HB5Ha_stS1P2bsS1P2bsS2AL2bs5ALWF'FFFFS1P3END3BUF2bs2B32K0S2ra2sp2lo2bs3SPL2HB5Ha_st5Hl_stS2PP2bs3PPB2nn2HB5Ha_stS2PP2bs3PPB2HB5Ha_stS2PP2bs3PPB2HB5Ha_stS2sp2PP4VALP2bs3PPB4VALB3AL13SPRS2sp2PP4VALP2bs3PPB4VALB3AL13SPRS2sp2PP4VALP2bs3PPB4VALB3AL13SPRS2sp2PP4VALP2bs3PPB4VALB3AL13SPR2nnS1P2bsFS2AL2bs4IMG'S2AL2bs4IMG'FS2sp2PP4VALP1P2bs2nn2HB5Ha_st5Hl_stS2ra2sp2PP4VALP2bs2HB5Ha_st5Hl_stS2sp2PP4VALP1P2bs2HB5Ha_st5Hl_stS2sp2PP4VALP1P2bs2HB5Ha_st5Hl_stS2sp2lo2bs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B2 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int ()) "Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pvalv,(1.&40.)P,(7.$8.Vm,VPP,(9.$:.(;.(<.&40.VP,))(=.$:.)))P,(7.$8.Vm,VVALP,(9.$:.(>.R2.)(=.$:.)))P,(?.$8.Vm,VBUF,Vbs,)P,(1;.$8.Vm,)P,(27.$8.VAL,Vm,)P,(13.$8.VAL,VCS,Vm,VPP,+8.)P,(13.$8.VAL,VCS,Vm,VVALP,+4.)P,(13.$8.VAL,VCS,Vm,VBUF,(14.(15.(1.&8.)Vbs,)))P,(12.$8.Vm,Vlo,(10.&40.Vsp,))(1<.$8.VAL,VCS,(1=.$8.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(1>.(1?.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VVALP,)R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(<.&40.+994>8.)Vfc,(22.(1.&40.))Vm,(23.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros a3 a4 a5 a6 a7 valv HPP HVAL HBUF MI AB OPP OVAL OBUF ST. al_facts.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
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
    zstep. clear RD0. zstep. if_cases Kt; zify_cond Kt.
    { (* [comment removed for export] *)
      zstep. eapply ret_walk with (r := -98) (p' := P); try eassumption; try lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      assert (E2 : END = P + 1) by (apply Bool.andb_false_iff in K2; destruct K2 as [K2|K2]; apply Z.ltb_ge in K2; lia).
      eapply ret_walk with (r := -96) (p' := P + 1); try eassumption; try lia. }
    clear K0.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF (P + 1).
    (* [comment removed for export] *)
    get_byte bs (P + 1 - BUF) b1 NB1. read_at HBUF NB1 (P + 1 - BUF) RD1.
    zstep. clear RD1. zstep. if_cases Ksg; zify_cond Ksg.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      { (* [comment removed for export] *)
        pose proof (land_127_range (bv_unsigned (sxb b1))) as NR.
        set (nn := Z.land (Z.land (bv_unsigned (sxb b1)) 255) 127) in *.
        pose proof (longform_n nn NR Kn) as HN. clearbody nn.
        zstep. if_cases Kge; zify_cond Kge.
        { (* [comment removed for export] *)
          eapply ret_walk with (r := -96) (p' := P + 1); try eassumption; try lia. }
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        eapply loop1_entry with (nn := nn); try eassumption; try lia; try reflexivity. }
      (* [comment removed for export] *)
      zstep. zstep. eapply ret_walk with (r := -100) (p' := P + 1); try eassumption; try lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk1 OBUF (P + 1).
    (* [comment removed for export] *)
    read_at HBUF NB1 (P + 1 - BUF) RD2. zstep. clear RD2.
    eapply j1_walk with (p1 := P + 2); try eassumption; try lia.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_asn1_get_int_spec {L : heap_layout} : forall AL, asan_img_ok AL -> asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
Proof.
  intros AL IMG. unfold asn1_get_int_stmtA, A_ASN1_GET_INT.
  intros until valv. intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OVAL OBUF SCS -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.

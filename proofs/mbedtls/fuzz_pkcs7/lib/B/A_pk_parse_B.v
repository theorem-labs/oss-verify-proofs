(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pk_parse_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P003f19d21a008c7f 0 3 0 1 33 1 127 1P0074945a510adf75 0 7 0 1 22 1 128 1 129 1 131 1 134 1 135 1P045d0e197883b772 0 3 0 1 33 1 127 1P053213fb16bd54da 0 5 0 1 128 1 129 1 130 1 131 1P078b0ae9291fea29 0 5 0 1 128 1 129 1 130 1 131 1P0ac58d340e2c8ed2 0 5 0 1 128 1 129 1 130 1 131 1P0f715ee119f69c3d 1 1 64 2 107 1 123 1 3 0 1 122 1 124 64P10e17e460a072937 0 5 0 1 128 1 129 1 130 1 131 1P12bc847d3ebe3aa9 0 5 0 1 128 1 129 1 130 1 131 1P150b063442f4fcee 0 5 0 1 128 1 129 1 130 1 131 1P1800c5c7714ff778 1 1 64 2 0 1 122 1 3 2 1 123 1 124 64P185e2eaea5c0830d 0 3 0 1 33 1 127 1P18739e051f081f4b 0 5 0 1 128 1 129 1 130 1 131 1P1a8a78f55195de95 0 5 0 1 116 1 117 1 118 1 119 1P1c5c63e67681546b 0 3 0 1 33 1 115 1P1d87ac4f4b9fd8b1 1 1 64 2 1 1 122 1 3 0 1 123 1 124 64P1ff20ecc295234b4 0 5 0 1 128 1 129 1 130 1 131 1P219c91c78334499b 0 3 0 1 33 1 127 1P223b4d33619f63ce 0 5 0 1 128 1 129 1 130 1 131 1P2308f1234de45c01 0 3 0 1 33 1 127 1P23bd0f53c61365a3 0 4 0 1 21 1 134 1 135 1P267e95cf798f392d 0 3 0 1 33 1 127 1P2710fd05d6815c16 0 3 0 1 33 1 127 1P28a5da5df11d59ea 0 3 0 1 33 1 127 1P29e8d88b55d9a1a3 0 5 0 1 128 1 129 1 130 1 131 1P2a59de691c9bcba4 0 5 0 1 128 1 129 1 130 1 131 1P2a7b8a2c9135f6a3 0 3 0 1 33 1 127 1P2c05a75c63fb7833 0 4 0 1 21 1 134 1 135 1P30d35c22a2955f2c 0 3 0 1 33 1 127 1P30ff3e0154c4ca0f 0 3 0 1 33 1 127 1P374d210a838b50e6 0 5 0 1 128 1 129 1 130 1 131 1P3b920b9da0e39132 0 3 0 1 33 1 127 1P3d8daf7ad9629553 0 5 0 1 128 1 129 1 130 1 131 1P3eb45cd5867241d1 0 9 0 1 107 1 111 1 117 1 118 1 119 1 120 1 123 1 124 1P3fbc977f2aafbbe7 0 3 0 1 33 1 127 1N013ad01727034a1bN0292a8b67db6f931N0326de0fa27850d2N09c5c02d5b00b23fN0a08519c1e60fb41N0a9445c537cb1c6cN0bf9ef804bd7fc9aN0cc03207fcad2f88N0cc220d0523f517cN0d8b27924e6e7b4bN0e0f0eb256dafc99N0f7e305267bd2ed8N0febba434482dd2bN103e532db6ef759eN1074777207852832N17f6c6a7e565779dN18a485f08ff37bdbN196f570d91ea58b5N1a52cf8c09b7c2b6N1b1bc8026fb2c473N1babcc4360a4c437N1ec8340fd22c229bN1fa304e58f49a8c3N203f5f6f3fec323eN20a37ae278c1fd52N234113a105d126cbN257a8429f48dac09N2a8f6d226a1da815N2c55eade1c1707dcN302578c055803b70N30df2077a6915275N3c8ddfba90114f71N3f093ca3ff4b2bedN3f1dfaea092a1c70"%lxh.
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
Ltac2 gd_tbl_A_pk_parse_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkPKB.Call.EPOST"; "stdpp.bitvector.definitions.Z_to_bv"].


Section WalkPKB.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_PK.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_PK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP END PKA lo STKk : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis STK0 : 176 + arl_need_smalloc R <= STKk.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.
  Hypothesis ENDB : 0 <= END < 2^64.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_PK in UARG; unfold A_SMALLOC_2_PK in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation F1 := (C1 (Z_to_bv 8 241)). Local Notation F2 := (C1 (Z_to_bv 8 242)). Local Notation F3 := (C1 (Z_to_bv 8 243)).
  Local Notation F8 := (C1 (Z_to_bv 8 248)). Local Notation Z0 := (C1 (Z_to_bv 8 0)). Local Notation P4 := (C1 (Z_to_bv 8 4)).
  Local Notation FSH0 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  F8; F8; F8; F2;  F2; F2; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (a0v : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,O1.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(:.Vra,)Vfc,(;.(2.&40.))R10.(<.$5.)))(6.(=.$5.R10.)(6.(>.$5.R10.Vlo,(?.&40.Vsp,))(6.(10.$5.VR,VHIA,O8.O7.VLF,(?.&40.Vsp,)(11.VR,)O3.O5.R10.)(6.(10.$5.VR,VHIA,O8.O6.VLF,(?.&40.Vsp,)(11.VR,)O2.O4.R10.)(6.(7.P,$12.Sp(13.$5.VR,VHIA,R?.)(13.$5.VR,VHIA,O8.))(6.(7.$12.(14.$5.VR,VHIA,R?.)(14.$5.VR,VHIA,O8.))(6.(7.$12.(15.$5.VR,VHIA,R?.)(15.$5.VR,VHIA,O8.))(6.(7.$12.(16.$5.VR,VHIA,R?.)(16.$5.VR,VHIA,O8.))(6.(7.$12.(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O8.))(6.(7.$12.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O8.))(6.Pmo,$19.(1:.(1;.$5.VR,VHIA,R10.R1.)(1;.$5.VR,VHIA,O8.R1.))(1<.$5.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 ENDB; try lx_pin1 PKB; try lx_pin1 PPB; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 PKA; try lx_pin1 END; try lx_pin1 PP; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LFB TOP SLO STK0 LOS STKk NS1 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_B ()) "Ph3,(4.$5.VR,VHIA,)PLBa,(1=.$1>.)PLBb,(1=.$1>.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(1=.$1?.)PWB,(1=.$1?.)PFB,$12.Psp1,$12.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0v,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pb0,(2.&8.)Pb1,(2.&8.)Pb2,(2.&8.)Pb3,(2.&8.)Pb4,(2.&8.)Pb5,(2.&8.)Pb6,(2.&8.)Pb7,(2.&8.)Pb8,(2.&8.)Pb9,(2.&8.)Pb10,(2.&8.)Pb11,(2.&8.)Pb12,(2.&8.)Pb13,(2.&8.)Pb14,(2.&8.)Pb15,(2.&8.)Pb16,(2.&8.)Pb17,(2.&8.)Pb18,(2.&8.)Pb19,(2.&8.)Pb20,(2.&8.)Pb21,(2.&8.)Pb22,(2.&8.)Pb23,(2.&8.)Pb24,(2.&8.)Pb25,(2.&8.)Pb26,(2.&8.)Pb27,(2.&8.)Pb28,(2.&8.)Pb29,(2.&8.)Pb30,(2.&8.)Pb31,(2.&8.)P,(1<.$5.VR,VHIA,R44.R42.(20.(21.$12.$12.)(22.$12.$12.R3<.+100.)VLF,)R3?.)P,Px,$12.P,(13.$5.VR,VHIA,Vh,R1.)(13.$5.VR,VHIA,R47.R2.)P,(7.$12.(14.$5.VR,VHIA,R46.)(14.$5.VR,VHIA,Vh,))P,(7.$12.(15.$5.VR,VHIA,R47.)(15.$5.VR,VHIA,Vh,))P,(6.(23.(24.(?.&40.Vsp,)+;0.)R3?.)(23.R3?.(24.(?.&40.Vsp,)+:0.)))P,(7.$12.(25.R40.+20.)=)P,(7.$12.(25.R42.+40.)=)P,(26.VR,R4:.VLF,R43.+100.)P,(26.VR,R4:.VLF,R44.+100.)P,(27.(13.$5.VR,VHIA,Vh,)R45.+100.)P,PB,$12.Pj,$12.P,(28.(21.$12.$12.)(22.$12.$12.R2.R1.)VLF,)(29.(23.(2:.R49.+100.)R3.)(23.(2:.R3.R2.)R49.))P,Pb',$1>.P,(28.$1>.R1.R4?.)(28.$1>.R2.R4?.)P,(2;.$5.R4;.R48.(20.$2<.(2=.R2?.)(20.$2<.(2=.R2>.)(20.$2<.(2=.R2=.)(2>.$2<.)))))P,(2;.$5.R4<.(2:.(2?.R49.+3.)(30.(31.VR,)))(20.$2<.(32.R2=.)(20.$2<.(32.R2<.)(20.$2<.(32.R2;.)(20.$2<.(32.R2:.)(20.$2<.(32.R29.)(20.$2<.(32.R28.)(20.$2<.(32.R27.)(20.$2<.(32.R26.)(20.$2<.(32.R25.)(20.$2<.(32.R24.)(20.$2<.(32.R23.)(20.$2<.(32.R22.)(20.$2<.(32.R21.)(20.$2<.(32.R20.)(20.$2<.(32.R1?.)(20.$2<.(32.R1>.)(20.$2<.(32.R1=.)(20.$2<.(32.R1<.)(20.$2<.(32.R1;.)(20.$2<.(32.R1:.)(20.$2<.(32.R19.)(20.$2<.(32.R18.)(20.$2<.(32.R17.)(20.$2<.(32.R16.)(20.$2<.(32.R15.)(20.$2<.(32.R14.)(20.$2<.(32.R13.)(20.$2<.(32.R12.)(20.$2<.(32.R11.)(20.$2<.(32.R10.)(20.$2<.(32.R?.)(20.$2<.(32.R>.)(2>.$2<.))))))))))))))))))))))))))))))))))P,(2;.$5.R4=.(2:.(?.&40.Vsp,)-68.)(20.$2<.(2=.Vs11,)(20.$2<.(2=.Vs10,)(20.$2<.(2=.Vs9,)(20.$2<.(2=.Vs8,)(20.$2<.(2=.Vs7,)(20.$2<.(2=.Vs6,)(20.$2<.(2=.Vs5,)(20.$2<.(2=.Vs4,)(20.$2<.(2=.Vs3,)(20.$2<.(2=.Vs2,)(20.$2<.(2=.Vs1,)(20.$2<.(2=.Vs0,)(20.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))P,(>.$5.R4>.R4:.(2:.(?.&40.Vsp,)-68.))P,(>.$5.R4?.Vlo,R4;.)P,(=.$5.R50.)P,(10.$5.VR,VHIA,R56.R55.VLF,(?.&40.Vsp,)(11.VR,)R50.R53.R51.)P,(10.$5.VR,VHIA,R57.R55.VLF,(?.&40.Vsp,)(11.VR,)R50.R53.R52.)(33.$5.(31.VR,)(13.$5.VR,VHIA,R58.)(34.R58.R57.R56.R55.R54.R52.R51.R4:.)(8.(9.R4>.(35.&40.R4?.)Vgp,Vtp,R4=.R4<.R4;.Vsp,(35.&40.R4?.)R4:.R49.R48.R47.R46.R45.R44.R43.(35.&40.R50.)R3>.R3=.R3<.R3;.R3:.R39.R38.(35.&40.(2:.(2?.R50.+3.)(30.(31.VR,))))(35.&40.R50.)R42.R41.R40.R3?.)VF,(35.&40.+;035<.)Vfc,(;.(2.&40.))R53.(<.$5.)))")
(* [comment removed for export] *).
  Proof.
  intros until b31.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE ST1 STbelow MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO STK0 NS1 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xb040c] [] 442%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 256) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 256) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO STK0 NS1 LOS; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO STK0 NS1; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO STK0 NS1; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
  }
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.

  (* [comment removed for export] *)
  Definition EPIQ (hq hp : HST asegs R HIA) (LBa LBq : list blk) (m0 : mem) (WA : list ivl) (FB sp1 : Z) (a0v : word)
      (XQ : mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lxra,(2.&40.)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)Ls4v,(2.&40.)(1.(2.&40.)Ls5v,(2.&40.)(1.(2.&40.)Ls6v,(2.&40.)(1.(2.&40.)Ls7v,(2.&40.)(1.(2.&40.)Ls8v,(2.&40.)(1.(2.&40.)Ls9v,(2.&40.)(1.(2.&40.)Ls10v,(2.&40.)(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(1.(2.&8.)Lb0,(2.&8.)(1.(2.&8.)Lb1,(2.&8.)(1.(2.&8.)Lb2,(2.&8.)(1.(2.&8.)Lb3,(2.&8.)(1.(2.&8.)Lb4,(2.&8.)(1.(2.&8.)Lb5,(2.&8.)(1.(2.&8.)Lb6,(2.&8.)(1.(2.&8.)Lb7,(2.&8.)(1.(2.&8.)Lb8,(2.&8.)(1.(2.&8.)Lb9,(2.&8.)(1.(2.&8.)Lb10,(2.&8.)(1.(2.&8.)Lb11,(2.&8.)(1.(2.&8.)Lb12,(2.&8.)(1.(2.&8.)Lb13,(2.&8.)(1.(2.&8.)Lb14,(2.&8.)(1.(2.&8.)Lb15,(2.&8.)(1.(2.&8.)Lb16,(2.&8.)(1.(2.&8.)Lb17,(2.&8.)(1.(2.&8.)Lb18,(2.&8.)(1.(2.&8.)Lb19,(2.&8.)(1.(2.&8.)Lb20,(2.&8.)(1.(2.&8.)Lb21,(2.&8.)(1.(2.&8.)Lb22,(2.&8.)(1.(2.&8.)Lb23,(2.&8.)(1.(2.&8.)Lb24,(2.&8.)(1.(2.&8.)Lb25,(2.&8.)(1.(2.&8.)Lb26,(2.&8.)(1.(2.&8.)Lb27,(2.&8.)(1.(2.&8.)Lb28,(2.&8.)(1.(2.&8.)Lb29,(2.&8.)(1.(2.&8.)Lb30,(2.&8.)(1.(2.&8.)Lb31,(2.&8.)(6.(7.$0.R3;.(8.(9.R39.(35.&40.O3.)Vgp,Vtp,R38.R37.R36.Vsp,(35.&40.O3.)O2.R35.R34.R33.R32.R31.R30.R2?.(35.&40.O4.)R2:.R29.R28.R27.R26.R25.R24.(35.&40.(2:.(2?.O4.+3.)(30.(31.VR,))))(35.&40.O4.)R2>.R2=.R2<.R2;.)VF,(35.&40.+;035<.)Vfc,(;.(2.&40.))R3:.(<.$5.)))(6.(1<.$5.VR,VHIA,O:.O7.(20.(21.$12.$12.)(22.$12.$12.O4.+100.)VLF,)R3:.)(6.(2;.$5.R3:.O4.(20.$2<.(2=.R23.)(20.$2<.(2=.R22.)(20.$2<.(2=.R21.)(2>.$2<.)))))(6.(2;.$5.R3:.(2:.(2?.O4.+3.)(30.(31.VR,)))(20.$2<.(32.R20.)(20.$2<.(32.R1?.)(20.$2<.(32.R1>.)(20.$2<.(32.R1=.)(20.$2<.(32.R1<.)(20.$2<.(32.R1;.)(20.$2<.(32.R1:.)(20.$2<.(32.R19.)(20.$2<.(32.R18.)(20.$2<.(32.R17.)(20.$2<.(32.R16.)(20.$2<.(32.R15.)(20.$2<.(32.R14.)(20.$2<.(32.R13.)(20.$2<.(32.R12.)(20.$2<.(32.R11.)(20.$2<.(32.R10.)(20.$2<.(32.R?.)(20.$2<.(32.R>.)(20.$2<.(32.R=.)(20.$2<.(32.R<.)(20.$2<.(32.R;.)(20.$2<.(32.R:.)(20.$2<.(32.R9.)(20.$2<.(32.R8.)(20.$2<.(32.R7.)(20.$2<.(32.R6.)(20.$2<.(32.R5.)(20.$2<.(32.R4.)(20.$2<.(32.R3.)(20.$2<.(32.R2.)(20.$2<.(32.R1.)(2>.$2<.))))))))))))))))))))))))))))))))))(6.(2;.$5.R3:.(2:.(?.&40.Vsp,)-68.)(20.$2<.(2=.Vs11,)(20.$2<.(2=.Vs10,)(20.$2<.(2=.Vs9,)(20.$2<.(2=.Vs8,)(20.$2<.(2=.Vs7,)(20.$2<.(2=.Vs6,)(20.$2<.(2=.Vs5,)(20.$2<.(2=.Vs4,)(20.$2<.(2=.Vs3,)(20.$2<.(2=.Vs2,)(20.$2<.(2=.Vs1,)(20.$2<.(2=.Vs0,)(20.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))(6.(>.$5.R3:.O3.(2:.(?.&40.Vsp,)-68.))(6.(>.$5.R3:.Vlo,O3.)(6.(=.$5.R3:.)(6.(10.$5.VR,VHIA,O9.O8.VLF,(?.&40.Vsp,)(11.VR,)O5.O6.R3:.)A1.O1.R3:.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
  End Call.
End WalkPKB.

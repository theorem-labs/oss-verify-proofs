(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_get_len () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "asn1_get_len_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"].


Definition A_ASN1_GET_LEN : Z := 0x099724.
Notation GETLEN_STACK := 16 (only parsing).

(* [comment removed for export] *)
Definition A_GOT_SHADOW : Z := 0x0f5e50.

Definition asn1_get_len_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+10.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-7?.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1;.R1.)(13.$1:.)))(5.(5.(18.O4.R2.)(18.R2.O3.))(5.P,(6.$4.R3.=)(5.(18.(10.O4.+1.)R3.)(18.(12.&40.R2.)(11.O3.R3.)))(1<.O19.R4.O2.(12.&40.O17.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_len_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_len ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Plo,$4.Pbs,(1>.(2.&8.))Plenv,(2.&40.)P,(19.O3.R9.R8.(=.$1:.(1;.(16.&40.R6.))(13.$1:.)))P,(19.O3.R:.R8.(=.$1:.(1;.R2.)(13.$1:.)))P,(1?.O3.R;.R6.R4.)P,(18.R7.R9.)P,(18.R:.R9.)P,(18.R:.(10.R9.(20.(21.(2.&8.)R7.))))P,(17.(10.R:.(20.(21.(2.&8.)R8.)))(22.+2.+3?.))P,(23.(18.(10.R?.+8.)R>.)(18.(10.R>.+8.)R?.))P,(23.(6.$4.(20.(21.(2.&8.)R:.))=)(23.(18.(10.R10.+8.)R<.)(18.(10.R<.(20.(21.(2.&8.)R:.)))R10.)))P,(23.(6.$4.(20.(21.(2.&8.)R;.))=)(23.(18.(10.R10.+8.)R=.)(18.(10.R=.(20.(21.(2.&8.)R;.)))R10.)))P,(6.$4.(24.R12.+8.)=)P,(6.$4.(24.R12.+8.)=)P,(17.=R14.)P,(17.=R14.)P,(17.=R12.)P,(15.O3.R18.)P,(25.O2.)P,(26.O2.R3<.)P,(27.O3.O2.R1;.)P,(28.O3.O2.R3>.R1<.R1;.+8.)P,(28.O3.O2.R3?.R1=.R1;.+8.)P,(28.O3.O2.R40.R1>.R19.(20.(21.(2.&8.)R17.)))P,(1<.O3.R1?.R19.(12.&40.R3?.))P,(18.R1:.(11.(12.&40.R40.)+10.))P,(6.$4.(24.(12.&40.R41.)+10.)=)P,(29.R44.R1<.(11.(12.&40.R42.)R1<.))P,(23.(18.(10.R22.+8.)(11.(12.&40.R43.)+10.))(18.(12.&40.R43.)R22.))P,(23.(18.(10.R22.+8.)(11.(12.&40.R44.)+10.))(18.(12.&40.R44.)R22.))P,(23.(6.$4.(20.(21.(2.&8.)R1>.))=)(23.(18.(10.R20.(20.(21.(2.&8.)R1>.)))(11.(12.&40.R45.)+10.))(18.(12.&40.R45.)R20.)))P,(6.(2.&40.)R3>.(16.&40.R25.))P,(6.(2.&40.)R3>.(16.&40.R23.))P,(6.(2.&40.)R3>.(16.&40.R26.))(2:.O3.O2.R4;.(2;.O3.R4:.R49.R48.R47.R43.R42.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2;.R2:.R28.R27.R26.R25.R23.R29.)(7.(8.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.)R2;.(16.&40.O1.)R2:.(:.(2.&40.))R29.(;.O3.)))")
(* [comment removed for export] *).

Tactic Notation "lxc_apply" uconstr(L) :=
  first [ (eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac])
        | (eapply evtA_eq; [ apply lx_MS_regs | eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac] ]) ];
  try lx_regs_eq; try lx_app.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
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
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < LENP.
  Hypothesis NZ3 : 0 < BUF.
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

  Notation W := [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - 16, bv_unsigned sp)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@L10526144419.67 L13111027312.66 L15047214981.106L1589942203.68  L1590122298.67  L16364863445.2  L214452351.116  L214452351.117  L214452351.78   L23020998485.106L2315928060.78  L26543632511.116L29775382283.105L29777478279.66 L29971666151.91 L31059860602.74 L34922826621.106L37896807997.106L3815032347.78  L4308504021.2   L43887727410.68 L43887776691.106L46054712944.116L46054712944.117L46054712944.78 L47127224865.68 L47127437984.106L47500120783.67 L49517696420.78 L50039458051.117L52534297420.66 L53259778579.78 L59308580059.66 L59310614641.78 L59314873579.2  L59314873579.3  L59314873579.4  L59314988138.4  L59314988138.67 L62524583283.68 L64164876829.78 L65706827985.78 L67402872395.106L67534559879.66 L67536658187.105L6972793115.106 00000V01=01]01^01_01`03A03B03C03n04Q04l04m04n06U08M08m09Z0:;0:<0:=0:>0;_0;`0;a0;b0;c0<J0<k0=H0=h0>A0>B0>C0>D0>E0>F0>G0>H0?30?i0@C0@c0@d0@e0AES2sp2PP4LENP3END2bs3cur1L2Hn2HE3HL02H8S2sp2PP4LENP1P3END2bs3cur2Hn4Hcur2HE2H8S2sp2PP4LENP3END2bs3cur2Hn2HE2H8FFFS2sp2PP4LENP1P3END3BUF2bs2B12B32D12D22D33PPB4LENB3DS13DS23DS31k3cur1L2Hk4Hcur2HE4Hinv3SPR4lxv12H9FFS2sp2PP4LENP3END2bs3cur1L2Hn2HE3HL04HL322H8S2sp2PP4LENP2bs3PPB4LENB1k1n2Hk3SPRS2sp2PP4LENP2bs4lxv12H93H10FFS2sp2PP4LENP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4LENB3NZ13NZ23NZ33SPL3LO03DS13DS23DS31k3cur1n2Hk4Hcur2HES2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t52t61F2fc1m2PP4LENP1P3END2lo2bs3cur1L2Hn2HE4lxv04lxv13lxm3H11S2sp2PP4LENP3END2bs3cur2Hn2HE2H8S2sp2PP4LENP1P3END2bs3cur1L2Hn2HE2H84Hcur3H15S2sp2PP4LENP3END2bs1k3cur1n2Hk2HEFFFS2sp2PP4LENP1P3END3BUF2bs2B12B32D12D22D33PPB4LENB3DS13DS23DS31k3cur1L2Hk4Hcur2HE4Hinv3SPR4lxv12H9FFFFS2sp2PP4LENP3END2bs3cur1L2Hn2HE4HL322H8S2sp2PP4LENP1P2bs1k3cur1n2Hk4HcurS2sp2PP4LENP2bs1k1n2Hk2Hn3Hn1S2sp2PP4LENP3END2bs3cur2Hn2HE2H8S2sp2PP4LENP2bs1k1n2Hk2HnFFFFFFFS2sp2PP4LENP3END2bs3cur1L2Hn2HE3HL04HL322H8S2sp2PP4LENP2bs3PPB4LENB1k1n1L2Hk3HL03SPR4lxv13H103LORS2sp2PP4LENP2bs1k1n2Hk3Hn1S2sp2PP4LENP3END2bs3cur2Hn2HE2H8FFS2sp2PP4LENP3END2bs3cur2Hn2HE2H8".
  Lemma loop_walk : forall (k : nat) (cur n L : Z) (rt2 rt3 rt4 pw : word) (j8 : list byte) (mm : mem),
    Z.of_nat k = n -> 0 <= n <= 4 -> P + 1 <= cur -> cur + n <= END ->
    0 <= L -> L * 2 ^ (8 * n) < 2 ^ 32 -> L < 2 ^ 32 ->
    rw_cells asegs mm LENP [C8 (Z_to_bv 64 L)] ->
    rw_cells asegs mm PP [C8 pw] ->
    rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -16) ->
    ro_cells asegs mm 0x1099f8 [C8 (Z_to_bv 64 (al_sb AL))] ->
    ro_cells asegs mm 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)] ->
    aobj asegs AL CS mm BUF (Z.of_nat (length bs)) -> aobj asegs AL CS mm LENP 8 -> aobj asegs AL CS mm PP 8 ->
    bytes_at asegs mm BUF bs ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 cur) (Z_to_bv 64 2) rt2 s0 s1
               (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 LENP) (Z_to_bv 64 cur)
               (Z_to_bv 64 (al_sb AL + Z.shiftr LENP 3)) (Z_to_bv 64 (al_sb AL + Z.shiftr PP 3))
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 n) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rt3 rt4 t5 t6)
          F (Z_to_bv 64 0x099848) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros cur n L rt2 rt3 rt4 pw j8 mm Hk Hn Hcur HE HL0 Hinv HL32 HLEN HPPc HFR ST GSB GOT OBUF OLEN OPP
      HBUF MU WM MI.
    - cbn [Z.of_nat] in Hk; subst n.
      pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
      lx_hide1 Hinv.
      lx_run_tac (PLAN [0x099848] [(0x099870, DJoin)] 200%N).
      lx_tree.
      all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
      all: try lxc_b2z.
      all: try lx_arith.
    - assert (Hn1 : 1 <= n) by lia.
      pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
      lx_hide1 Hinv. lx_hide1 Hk.
      lx_run_tac (PLAN [0x099848] [(0x099870, DJoin)] 200%N).
      lx_tree.
      all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
      all: try lxc_b2z.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x099848) _ _ ?mm _] =>
               lazymatch goal with |- context [Z_to_bv 64 (Z.lor (256 * ?L0) ?b)] =>
                 pose proof (lor_256_byte L0 b HL0 ltac:(lia)) as LOR;
                 unfold lx_hidden in Hinv, Hk;
                 lxc_apply (IH (cur + 1) (n - 1) (Z.lor (256 * L0) b))
               end
           | |- _ => idtac
           end.
      all: try lxc_cells_conv.
      all: try (rewrite LOR; assert (In4 : n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia;
                destruct In4 as [-> | [-> | [-> | ->]]]; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *; lia).
      all: try lx_arith.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@L15047214853.115L16364863445.2  L20433961190.80 L20729452516.70 L29775382411.114L29775382412.75 L31182537301.115L34922826749.115L41620534259.77 L4295607933.115 L43061431595.78 L4308504021.2   L44157706741.72 L44179736208.75 L45860560208.77 L45860740561.76 L50362652068.115L50362766629.77 L51613865239.76 L52199099879.72 L52636350339.72 L54548996694.75 L57140130203.72 L59310676432.75 L59314873579.2  L59314873579.3  L59314873579.4  L59314988138.1  L59314988138.4  L59314988138.76 L60855970958.77 L60856183823.115L60888157259.76 L67402872523.115L67536658315.114L67536658316.75 L6972793243.115 L6974891287.60  L6976986276.71  00000?00@00O00^00_00`01;01J01e02C02Y02Z03103J03K03L03M03N03e04C04k05<05`05a05b05c05d05g05h05i05j05k06C06R06S06T06c07207AS2sp2PP4LENP2bsFS2sp2PP4LENP2bsS2sp2PP4LENP2bsFFS2sp2PP4LENP2bs4lxv42H93H10S2sp2PP4LENP2bsS2sp2PP4LENP2bs4lxv42H93H10S2sp2PP4LENP1P3END2bs4lxv43H25S2sp2PP4LENP2lo2bs3SPLFS2sp2PP4LENP2bs4lxv12NRS2sp2PP4LENP1P3END2bs3H14FFFFS2sp2PP4LENP2bs4lxv42H9S2sp2PP4LENP1P3END2bs4lxv13H10S2sp2PP4LENP2bs3PPB4LENB3SPR4lxv13H112NRS2sp2PP4LENP1P2bsS2sp2PP4LENP2bs3PPB4LENB3SPR4lxv12NRFFFFS1GFFFFS2sp2PP4LENP2bs4lxv43H10S2sp2PP4LENP2bsFFS2sp2PP4LENP2bsS2sp2PP4LENP2bsS2sp2PP4LENP2bs".
  Lemma main_walk : forall (a3 a4 a5 a6 a7 lenv : word),
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m LENP [C8 lenv] -> bytes_at asegs m BUF bs ->
    mem_inv asegs m -> abase asegs AL m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m LENP 8 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    stk asegs m lo (bv_unsigned sp) ->
    evtA asegs AL CS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 LENP) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x099724) fc None m (seg_rom asegs)).
  Proof.
    intros a3 a4 a5 a6 a7 lenv HPP HLEN HBUF MI AB OPP OLEN OBUF ST.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    carve_frame 16%nat ST.
    lx_pre.
    lx_run_tac (PLAN [0x099848] [(0x099774, DJoin); (0x0997a8, DJoin)] 300%N).
    lx_tree.
    all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: try lxc_b2z.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x099848) _ _ ?mm _] =>
             match goal with HFR : rw_cells _ mm (bv_unsigned sp + -16) [CB 8 ?j; C8 ra] |- _ =>
               lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.land ?v 255) 127)] =>
                 pose proof (land_127_range v) as NR;
                 lxc_apply (loop_walk (Z.to_nat (Z.land (Z.land v 255) 127)) (P + 1) (Z.land (Z.land v 255) 127) 0
                              _ t3 t4 _ j mm)
               end end
         | |- _ => idtac
         end.
    all: try lxc_cells_conv.
    all: try lx_arith.
  Qed.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

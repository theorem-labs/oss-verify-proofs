(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_oid A_oid_pk_alg A_oid_ec_grp_algid A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_parse_B A_pk_parse_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pk_parse_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0c36045ca9996a7e 0 7 0 1 57 1 91 1 92 1 97 1 103 1 104 1P0d9951800e6bf8f3 1 1 32 3 0 1 103 1 106 1 10 57 2 80 2 83 2 91 2 92 2 97 2 99 2 104 2 105 2 107 64P166ea0bcf3fb17ec 0 4 0 1 56 1 103 1 104 1P21d2712f42822093 0 9 0 1 80 1 83 1 91 1 92 1 97 1 99 1 103 1 104 1P2a523030713a109a 0 4 0 1 56 1 103 1 104 1P2f8c7a1af1eaee10 1 1 32 3 0 1 103 1 106 1 10 57 2 80 2 83 2 91 2 92 2 97 2 99 2 104 2 105 2 107 64P32af4ca7252ce6fe 0 7 0 1 57 1 91 1 92 1 97 1 103 1 104 1P3f6d77b13af56e28 0 4 0 1 91 1 92 1 97 1N030855e31388da20N092b1311254ca9f2N1eacd26455254ffcN2abfd2a514352a47"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_pk_parse_D () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "WalkPKD.Call.DINV"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_B.EPIQ"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_C.XE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "A_PK_SETUP_PK"; "RocqVerifyHarness.AgentSubmission.P.P_pk_info.pk_info_of"; "RocqVerifyHarness.AgentSubmission.B.A_pk_info.A_PK_INFOS"; "WalkPKD.Call.TVAL"; "Stdlib.Lists.List.In"; "WalkPKD.Call.CALLQ_SETUP"].


Definition A_PK_SETUP_PK : Z := 0x0b1858.   (* [comment removed for export] *)


Section WalkPKD.
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
            (PP END PKA lo STKk : Z) (P BUF : Z) (bs : list byte).
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

  Local Notation BLEN := (Z.of_nat (length bs)).
  Local Notation X00 := [(PP, PP + 8); (PKA, PKA + 16)].
  Hypothesis HBS0 : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, BLEN) LB.
  Hypothesis BP : BUF <= P. Hypothesis PE : P <= END. Hypothesis EB : END <= BUF + BLEN.
  Hypothesis B47 : BUF + BLEN < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BL30 : BLEN < 2^30.
  Hypothesis PPAL : PP mod 8 = 0. Hypothesis PP0 : 0 < PP. Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PKAL : PKA mod 8 = 0. Hypothesis PK0 : 0 < PKA. Hypothesis PKLO : PKA + 16 <= lo.
  Hypothesis CWK : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PKA 16.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + BLEN <= PP.
  Hypothesis DKB : PKA + 16 <= BUF \/ BUF + BLEN <= PKA.

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
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis STK2 : 176 + 32 + arl_need_bcmp R <= STKk.
  Hypothesis STK5 : 176 + 64 <= STKk.
  Hypothesis RTCL : forall mx, arl_rtc R mx -> asan_rtc mx.
  Hypothesis OIDPK : oid_lookup1_stmtA asegs R HIA A_OID_GET_PK_ALG OID_PK_ALG_STACK_A.
  Hypothesis OIDGA : oid_lookup1_stmtA asegs R HIA A_OID_GET_EC_GRP_ALGID OID_EC_GRP_ALGID_STACK_A.
  Hypothesis GETBSN : asn1_get_bitstring_null_stmtA asegs AL A_ASN1_GET_BITSTRING_NULL.

  Local Notation EPIQ' := (A_pk_parse_B.EPIQ R HIA LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).
  Local Notation XE' := (A_pk_parse_C.XE PP END PKA P).
  Local Notation MIDQ1' := (A_pk_parse_C.MIDQ1 R HIA LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP END PKA lo P BUF bs).

  (* [comment removed for export] *)
  Ltac merge_stk :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with SL : rw_cells _ mx (?q + 8) [C8 _; C8 _; C8 _], S48 : rw_cells _ mx (?q + 48) [C8 _],
                          STA : stk _ mx ?q (?q + 8), STB : stk _ mx (?q + 32) (?q + 48), STC : stk _ mx (?q + 56) _ |- _ =>
        chunk_to_stk SL; chunk_to_stk S48;
        stk_merge_into STA SL; stk_merge_into STA STB; stk_merge_into STA S48; stk_merge_into STA STC end end.
  (* [comment removed for export] *)
  Ltac fin_epiq :=
    merge_stk;
    lazymatch goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb AL) _ |- _ => norm_b8 H end;
    apply evtA_done; left; eexists; unfold A_pk_parse_B.EPIQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    do 25 eexists; do 32 eexists; split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | idtac ].





  (* [comment removed for export] *)
  Definition DINV (FB sp1 : Z) (h1 : HST asegs R HIA) (sh : list cell) (kv : word) (p2 e1 : Z) (mm : mem) : Prop :=
    exists (w0 w1 w2 pc0 pc1 Lw kpad gv gpad : word) (pp p1v : Z) (ptag ppad plen : word),
      HM asegs R HIA h1 LB ((FB, 256) :: LF) mm
      /\ rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs mm (FB + 32) [C8 pc0; C8 pc1]
      /\ rw_cells asegs mm (FB + 64) [C8 Lw]
      /\ rw_cells asegs mm (FB + 96) [C4 ptag; C4 ppad; C8 plen; C8 (Z_to_bv 64 pp)]
      /\ rw_cells asegs mm (FB + 160) [C4 kv]
      /\ rw_cells asegs mm (FB + 160 + 4) [C4 kpad]
      /\ rw_cells asegs mm (FB + 176) [C4 gv]
      /\ rw_cells asegs mm (FB + 176 + 4) [C4 gpad]
      /\ rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) sh
      /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs mm (sp1 + 8)
           [C8 (Z_to_bv 64 p1v); C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL))]
      /\ rw_cells asegs mm (sp1 + 48) [C8 (Z_to_bv 64 FB)]
      /\ stk asegs mm sp1 (sp1 + 8)
      /\ stk asegs mm (sp1 + 32) (sp1 + 48)
      /\ stk asegs mm (sp1 + 56) (bv_unsigned sp + -104)
      /\ stk asegs mm lo sp1
      /\ mem_inv asegs mm
      /\ rw_cells asegs mm PP [C8 (Z_to_bv 64 p2)]
      /\ aobj asegs AL (hcs asegs R HIA h1) mm PP 8
      /\ rw_cells asegs mm PKA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      /\ aobj asegs AL (hcs asegs R HIA h1) mm PKA 16
      /\ bytes_at asegs mm BUF bs
      /\ aobj asegs AL (hcs asegs R HIA h1) mm BUF BLEN
      /\ P <= p2 /\ p2 <= e1 /\ e1 <= END
      /\ P + 2 <= p1v /\ p1v <= p2
      /\ ((pp = 0 /\ bv_unsigned plen = 0 /\ ptag = Z_to_bv 64 0) \/ (BUF <= pp /\ P <= pp /\ pp + bv_unsigned plen <= e1))
      /\ presW asegs R HIA h1 LB LF (bv_unsigned sp) (arl_stklo R) X00 m mm
(* [comment removed for export] *).


  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 GETBSN; try lx_pin1 OIDGA; try lx_pin1 OIDPK; try lx_pin1 RTCL; try lx_pin1 DPK; try lx_pin1 PKLO; try lx_pin1 PK0; try lx_pin1 PKAL; try lx_pin1 PPLO; try lx_pin1 PP0; try lx_pin1 PPAL; try lx_pin1 BUF0; try lx_pin1 PE; try lx_pin1 BP; try lx_pin1 ENDB; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 bs; try lx_pin1 BUF; try lx_pin1 P; try lx_pin1 lo; try lx_pin1 PKA; try lx_pin1 END; try lx_pin1 PP; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TVAL (kv : word) : Z := bv_unsigned (sx32 kv) mod 2^32.
  Definition CALLQ_SETUP (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := fun ms =>
    exists (mm : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 kv : word) (p5 e1 info : Z),
      ms = MS (mkR (Z_to_bv 64 0xb052c) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1)
                 (Z_to_bv 64 PKA) (Z_to_bv 64 info) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (-16384))
                 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160))
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
              F (Z_to_bv 64 A_PK_SETUP_PK) fc None mm (seg_rom asegs)
      /\ DINV FB sp1 h1
           [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
             F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p5 e1 mm
      /\ info = pk_info_of A_PK_INFOS (TVAL kv) /\ In info A_PK_INFOS
(* [comment removed for export] *).


  Ltac epi_close :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      repeat match goal with Hx : context [mx] |- _ => lazymatch type of Hx with mx = _ => fail | _ => clear Hx end end;
      subst mx end;
    try (match goal with Hx : ?b = ?b |- _ => clear Hx end);
    rewrite ?(Z.add_comm (al_sb AL) (Z.shiftr _ 3));
    fin_epiq;
    first [ solve [ eexists; eexists; split; [reflexivity|]; split; [lia|]; split; [eassumption|]; split; [lia| eassumption] ]
          | match goal with |- ?g => idtac "EPI-LEFT:" g end ].

  Lemma seg_A2 : forall (FB sp1 : Z) (h1 : HST asegs R HIA) (ms : machine_state),
    (bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) ->
    sp1 mod 32 = 0 ->
    hcs asegs R HIA h1 = hcs asegs R HIA h ->
    htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    MIDQ1' FB sp1 h1 ms ->
    evtA asegs AL (hcs asegs R HIA h1)
      (fun ms' => (exists a0v, EPIQ' h1 h1 LB LB m X00 FB sp1 a0v (XE' a0v) ms') \/ CALLQ_SETUP FB sp1 h1 ms')
      ms.
  Proof.
    intros FB sp1 h1 ms SP1 SP1M Ehcs Ehtop Estk F64 FRSH MQ. clear NB1 STK2.
    unfold A_pk_parse_C.MIDQ1 in MQ.
    destruct MQ as (mm & xra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & w0 & w1 & w2 & pc0 & pc1 & Lw
                    & kv & kpad & gv & gpad & p1 & p2 & pp & ptag & ppad & plen & -> & HH1 & HW & HPC & HLW & HPAR & HKV & HKP & HGV & HGP
                    & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MI1 & HPP & OPP & HPKA & OPKA & HBS & OBUF
                    & Hp1a & Hp12 & Hp2e & HeE & PPC & PRES).
    rt_facts. rewrite <- Ehcs in CSOK, SCS0.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 LB LF mm FB 256 lo HH1 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; exact BIN).
    destruct (hm_apart asegs R HIA h1 LB _ mm HH1) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC.
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8).
    { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCPP : wcover R LB LF (bv_unsigned sp) X00 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    set (e1 := p1 + bv_unsigned Lw) in *.
    assert (Hp2a : P <= p2) by (clear - Hp1a Hp12; lia).
    pose proof FSHX as FSH2. norm_b8 FSH2.
    frame_aobj FSH2 (FB + 64) 1%nat as OLEN. clear FSH2.
    pose proof (hm_abase asegs R HIA h1 LB _ mm HH1) as AB2.
    pose proof (art_alwf asegs R HIA) as ALWF.
    lx_run_tac (PLAN [A_ASN1_GET_BITSTRING_NULL] [] 20%N). lx_tree.
    repeat match goal with Hx : context [lxm] |- _ => lazymatch type of Hx with lxm = _ => fail | _ => clear Hx end end.
    subst lxm. clear LXlen.
    pose proof GETBSN as GB'. unfold asn1_get_bitstring_null_stmtA, A_ASN1_GET_BITSTRING_NULL in GB'.
    callxA_sp sp1 (eapply GB' with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 64) (P := p2) (END := e1) (BUF := BUF) (bs := bs) (lo := lo); clear GB';
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 STK0 STK5 F0 F1' F8' F64 ALO LOS ACP ACV PP0 BUF0 PPAL APP APB DPB BUFC PPLO BP PE EB Hp2a Hp2e HeE FBLO;
                                    first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "BSN-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "BSN-LEFT:" g end.
    clear OLEN AB2.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 64) [C8 ?lw] |- _ => rename H into HL5; rename lw into L5 end.
    match goal with H : rw_cells _ m5 PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP5; rename qq into p5 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r5 end.
    match goal with H : r5 = 0 -> _ |- _ => rename H into HOK5 end.
    match goal with H : _ < r5 <= 0 |- _ => rename H into RR5 end.
    match goal with H : p2 <= p5 <= e1 |- _ => rename H into Hp5 end.
    pose proof (bv_unsigned_in_range 64 L5) as LR5. unfold bv_modulus in LR5. cbn [Z.pow Z.of_N Pos.pow] in LR5.
    destruct (Z.eq_dec r5 0) as [R50|R5N].
    2:{ assert (R5L : r5 < 0) by (clear - RR5 R5N; lia). clear HOK5 R5N.
        lx_run_tac (PLAN [0xb035c; 0xb0730] [] 60%N). lx_tree.
        all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xb035c) _ _ _ (seg_rom _)] => epi_close | |- _ => idtac end.
        }
    subst r5. destruct (HOK5 eq_refl) as [Hp5a HL5b]. clear HOK5.
    lx_run_tac (PLAN [0xb035c; 0xb0730; A_PK_INFO_FROM_TYPE] [] 80%N). lx_tree.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xb035c) _ _ _ (seg_rom _)] => epi_close | |- _ => idtac end.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
           repeat match goal with Hx : context [mx] |- _ => lazymatch type of Hx with mx = _ => fail | _ => clear Hx end end;
           subst mx end.
    try (match goal with Hx : ?b = ?b |- _ => clear Hx end).
    assert (SXK : Z_to_bv 64 (zswrap 32 (zlow 32 (bv_unsigned kv))) = sx32 kv).
    { unfold sx32. f_equal. unfold zswrap, zlow, bv_swrap, bv_wrap.
      change (2 ^ (32 - 1)) with 2147483648. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
      change (2 ^ 32) with 4294967296. rewrite Zplus_mod_idemp_l. reflexivity. }
    rewrite SXK. clear SXK.
    pose proof (hm_abase asegs R HIA h1 LB _ m5 HH1) as AB3. pose proof (RTCL m5 (hm_rtc asegs R HIA h1 _ _ m5 HH1)) as RT3.
    pose proof (hm_img_shadow asegs R HIA h1 _ _ m5 HH1) as ISH3.
    pose proof (hcs_img_cs R HIA h1 IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
    assert (OTBL : aobj asegs AL (hcs asegs R HIA h1) m5 A_PK_INFO_TBL 32) by (eapply aobj_img; [exact ICS| exact ISH3| vm_compute; reflexivity]).
    pose proof (A_pk_info_from_type_spec AL IMG L) as PI'. unfold pk_info_from_type_stmtA, A_PK_INFO_FROM_TYPE in PI'.
    callxA_sp sp1 (eapply PI' with (CS := hcs asegs R HIA h1) (lo := lo); clear PI';
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NS1 STK0 STK5 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "INFO-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "INFO-LEFT:" g end.
    clear AB3 RT3 ISH3 OTBL.
    match goal with H : ?x = Z_to_bv 64 (pk_info_of _ _) |- _ => subst x end.
    fold (TVAL kv). remember (pk_info_of A_PK_INFOS (TVAL kv)) as info eqn:EINFO.
    assert (INFOB : info = 0 \/ In info A_PK_INFOS).
    { rewrite EINFO. unfold pk_info_of. destruct ((1 <=? TVAL kv) && (TVAL kv <=? 4)) eqn:EB4; [| left; reflexivity]. right.
      apply andb_true_iff in EB4. destruct EB4 as [E1 E4]. apply Z.leb_le in E1, E4.
      assert (CASES : TVAL kv = 1 \/ TVAL kv = 2 \/ TVAL kv = 3 \/ TVAL kv = 4) by (clear - E1 E4; revert E1 E4; generalize (TVAL kv); intros tv E1 E4; lia).
      destruct CASES as [E | [E | [E | E]]]; rewrite E; clear; cbn; tauto. }
    assert (INFOR : 0 <= info < 2^47).
    { destruct INFOB as [E0|HIN]; [rewrite E0; clear; lia|]. unfold A_PK_INFOS, A_RSA_INFO, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in HIN. cbn [In] in HIN. clear - HIN. lia. }
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    lx_run_tac (PLAN [0xb035c; 0xb0730; A_PK_SETUP_PK] [] 40%N). lx_tree.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xb035c) _ _ _ (seg_rom _)] => epi_close | |- _ => idtac end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      repeat match goal with Hx : context [mx] |- _ => lazymatch type of Hx with mx = _ => fail | _ => clear Hx end end;
      subst mx end.
    try (match goal with Hx : ?b = ?b |- _ => clear Hx end).
    assert (INFO1 : In info A_PK_INFOS) by (destruct INFOB as [E0|HIN]; [exfalso; lia| exact HIN]).
    rewrite ?(Z.add_comm (al_sb AL) (Z.shiftr _ 3)).
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?k) _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
      replace (Z_to_bv 64 k) with (Z_to_bv 64 (k - 2^64))
        by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity) end.
    apply evtA_done. right. unfold CALLQ_SETUP.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    do 13 eexists. exists kv, p5, e1, info.
    split; [reflexivity|]. split; [| split; [exact EINFO| exact INFO1]].
    unfold DINV. exists w0, w1, w2, pc0, pc1, L5, kpad, gv, gpad, pp, p1, ptag, ppad, plen.
    repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].
    all: first [ lia | exact PPC | match goal with |- ?g => idtac "CQS-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKD.

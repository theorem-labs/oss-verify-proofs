(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_seq_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_parse_A A_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_bud.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0140ab2d3c3a5934 0 3 0 1 33 1 67 1P03146a932136ad13 0 3 0 1 33 1 67 1P057d8b2d3e8b8628 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P084e448132c74b5f 0 3 0 1 33 1 67 1P0955f7926a587d03 0 9 0 1 22 1 57 1 68 1 73 1 74 1 75 1 78 1 79 1P0a51125d3e9427cb 1 1 64 2 0 1 66 1 3 2 1 67 1 68 64P0fdeeba686cdb97e 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P13499749f664cbb1 0 3 0 1 33 1 67 1P1349a6da612ef00a 0 3 0 1 33 1 67 1P1506d561ed7b47c2 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P17231791bedfd744 1 1 64 2 1 1 66 1 3 0 1 67 1 68 64P18062912b08b9165 0 8 0 1 45 1 56 1 57 1 58 1 61 1 62 1 63 1P18e73c365dd3937f 0 4 0 1 21 1 78 1 79 1P1ba22b661b8647e1 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P1bed91d180570f04 0 3 0 1 33 1 67 1P1c76164ebe76744b 0 3 0 1 33 1 67 1P1da595fc7be45994 0 3 0 1 33 1 55 1P1f1d83fc7044cb3a 0 3 0 1 33 1 67 1P1f1eb5597373a3dd 1 1 64 2 43 1 67 1 3 0 1 66 1 68 64P1ff02c6cfda3da09 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P24cd9d933ea5aa60 0 3 0 1 33 1 67 1P282e1d05af0bf177 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P29f703d122269463 0 3 0 1 33 1 67 1P2a126c5a1cd1497d 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P2d777bcbcc2f54aa 0 3 0 1 33 1 67 1P30cc5ba046fd2e35 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P323c702f156cce55 0 3 0 1 33 1 67 1P335c0029777ec7f5 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P33ca54fa2721735c 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P34369bdc25234eaa 0 4 0 1 21 1 78 1 79 1P3441e7f7d6bd9e49 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P3762ae0727eba336 0 3 0 1 33 1 67 1P37cf1309891aa21c 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1P3bf5dd7f9800f622 0 12 0 1 43 1 46 1 50 1 57 1 58 1 59 1 62 1 63 1 64 1 67 1 68 1P3fee17d08d0f05e4 0 8 0 1 57 1 68 1 69 1 70 1 73 1 74 1 75 1N0162d3c86b31378bN0343e2cde13b97c8N0494aa4c4d349fb6N0700471e2cfefc01N082ce051d257eb6fN09f6176917de8972N0a8379155c26b060N0ab7e305bf945dddN0dafe5e33837d56fN0e7548d31fb04b32N110badb072e3222aN11c0eadfc1b92611N145c4b7135b9460fN151a7525279f1126N17e657ec0a435839N17f7feb1e3a0d33cN1a523b35f192d3faN1a90e35a4d0809f6N1ccfd6f9713c6bc9N1d22fb4dddfee27eN21f02a554ecfc528N23f8c1a9e667c74cN244b3d4426160c9fN2538af0740fcce28N25e3d09ef14c04b9N2bc957b44014bc2dN2c0cb91dc9fefa0dN2c0ec325dbd040d8N2db61631207e84acN2ed39d85d41b4a90N3102b6af2a37752fN311c374f93e4ec35N31ea7e8ec6acb5c6N33532a5b30c3a1d7N3842fea8e6f3d27eN39029cc34041ce23N3b346bb448dc44c9N3b694c2d74e4a7e9N3ef386db7f81381c"%lxh.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.

  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m2x : mem) (WA WB : list ivl) (r : Z) : machine_state -> Prop := fun ms =>
    exists (m' : mem) (h4 : HST asegs R HIA) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ sshad asegs AL m' slo (bv_unsigned sp)
      /\ presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m m'
      /\ presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x m'
      /\ hcs asegs R HIA h4 = hcs asegs R HIA h3 /\ htop asegs R HIA h4 = htop asegs R HIA h3
      /\ hstkhi asegs R HIA h4 = hstkhi asegs R HIA h3 /\ hflag asegs R HIA h4 = hflag asegs R HIA h3
      /\ havol asegs R HIA h4 = havol asegs R HIA h3 /\ hfr asegs R HIA h4 = hfr asegs R HIA h3
      /\ (forall mo, HK asegs R HIA h4 mo <-> HK asegs R HIA h3 mo)
      /\ HM asegs R HIA h4 (LBc ++ LB) LF m'.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 DCB; try lx_pin1 CURLO; try lx_pin1 CWC; try lx_pin1 ALC; try lx_pin1 HCUR; try lx_pin1 DPB; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 HBY; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 HPP; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 d; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 CNTp_add; try lx_pin1 FFRp_add; try lx_pin1 PHIp_add; try lx_pin1 CNTp_mono; try lx_pin1 FFRp_mono; try lx_pin1 PHIp_mono; try lx_pin1 SEQFREE; try lx_pin1 FREEL; try lx_pin1 PSAN; try lx_pin1 CNTp; try lx_pin1 FFRp; try lx_pin1 PHIp; try lx_pin1 HMND; try lx_pin1 CALLOC; try lx_pin1 AMC; try lx_pin1 AMS; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS CUR0 PP0 LFB bs CUR PP NRT STKp0 STKp NA1 NS1 IMG"]
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (LBc : list blk) (m2x mm : mem) (WA WB : list ivl) (FB sp1 : Z)
      (xra t0 t1 t2 a0 a3 a4 a5 a6 a7 s3v s4v s5v s6v s7v s8v s9v s10v t3 t4 t5 t6 w0 w1 w2 : word) (r : Z),
    HM asegs R HIA h3 (LBc ++ LB) ((FB, 256) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h -> hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 256 -> fresh_apart R (LBc ++ LB) LF FB 256 -> crange CS FB 256 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) (FSHb (Z_to_bv 8 248)) ->
    rw_cells asegs mm (bv_unsigned sp + -104) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -104) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm ->
    presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm ->
    sshad asegs AL mm slo (bv_unsigned sp) ->
    evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 LBc m2x WA WB r)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 (Z_to_bv 64 FB) (Z_to_bv 64 FB) a3 a4 a5 a6 a7
               (Z_to_bv 64 r) s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae96c) fc None mm (seg_rom asegs)).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE STK2 STlo MI PRES PRES2 SS.
  rt_facts.
  unfold A_x509_san_ext_A.FSHb in FSH.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaea08] [] 377%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 NA1 NRTa STKp0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ]]).
  clear HHe NCp NSp.
  repeat match goal with H : rw_cells _ me FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  idtac "EPI-DONE".
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _ |- _ =>
          pose proof (stk_merge asegs mf lo sp1 _ ST0 STA ltac:(first [ clear - SP1 SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ])) as ST3;
          release_frame SV ST3 (bv_unsigned sp); exact ST3 end).
  }
  split; [assumption|].
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
  End Call.
End Walk.

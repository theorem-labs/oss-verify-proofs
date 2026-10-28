(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_parse_san_A A_x509_seq_stmts A_x509_seq_stmtsE A_x509_seq_stmtsE_w.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F A_x509_san_ext_G A_x509_san_ext_H A_x509_san_ext_I A_x509_san_ext_J A_x509_san_ext_K A_x509_san_ext_L.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43150339301.25000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).
  Local Notation sfr := (A_x509_san_ext_C.sfr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs).
  Local Notation svA := (A_x509_san_ext_C.svA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs).
  Local Notation Wc := (A_x509_san_ext_C.Wc PP).
  Local Notation nLB := (A_x509_san_ext_C.nLB LB).
  Local Notation nfreshA := (A_x509_san_ext_C.nfreshA R LB LF PP CUR).
  Local Notation curFA := (A_x509_san_ext_C.curFA CUR).
  Local Notation headrep := (A_x509_san_ext_C.headrep CUR END BUF).
  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).
  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).
  (* [comment removed for export] *)
  Ltac fin_sfr t :=
    unfold A_x509_san_ext_C.sfr;
    spine; first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (unfold A_x509_san_ext_A.rsl; eassumption)
                 | (repeat split; eassumption) | reflexivity | solve [t] | match goal with |- ?g => idtac "SFR-LEFT:" g end ].
  Local Notation ERRQ := (A_x509_san_ext_D.ERRQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation CALLQ1 := (A_x509_san_ext_D.CALLQ1 R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation EXITP := (A_x509_san_ext_E.EXITP R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).

  (* [comment removed for export] *)
  Hypothesis BUD : havol asegs R HIA h + PHIx NB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRx NB d <= FR_MAX.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Local Notation KSL := (Z_to_bv 64 CUR) (only parsing).

  Local Notation K0 := (Z_to_bv 64 CUR) (only parsing).
  Local Notation K8 := (Z_to_bv 64 (-9578)) (only parsing).
  Local Notation K16 := (Z_to_bv 64 (-9472)) (only parsing).
  Local Notation K24 := (Z_to_bv 64 (-9570)) (only parsing).
  Local Notation K48 := (Z_to_bv 64 (-8320)) (only parsing).
  Local Notation LoopOb := (A_x509_san_ext_K.LoopOb R HIA PHIp FFRp CNTp h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP CUR P END BUF lo slo d bs).
  Local Notation PHIy := (A_x509_san_ext_K.PHIy PHIp CNTp).
  Local Notation FFRy := (A_x509_san_ext_K.FFRy FFRp CNTp d).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01K0@D3953997537.232 D3953997537.233 D50244182904.233D60189065437.232D60189065437.233L11668947013.216L12126572370.2  L1685717371.0   L27111942217.1  L28632618922.2  L31145622673.2  L34452444106.2  L35653441506.13 L38235734261.1  L38259954321.2  L38692635477.0  L39332637397.0  L43300649301.0  L44166924249.3  L46367748665.10 L48937103345.219L50797055232.13 L51578300575.1  L56009798182.1  L56380991837.10 L56468645943.219L57698627611.2  L60098763854.6  L64850595401.0  L9080220944.4   L9347146865.10  L9356559676.18  L9817103909.216 P12115299733.232P12115299733.233P28627113325.232P28627113325.233P31146933846.232P31146933846.233P34450608397.232P34450608397.233P38261788758.232P38261788758.233P44164039966.232P44164039966.233P57713046236.232P57713046236.233Q10048410502.228Q10160764996.233Q16057206942.229Q18826805037.229Q19243646445.232Q19243646445.233Q24809784940.233Q25952160488.231Q25952160488.232Q26119743870.233Q26481470270.229Q26863663622.233Q28465177121.229Q28465177121.230Q32681824661.232Q32681824661.233Q37149073081.232Q37149073081.233Q39180574961.232Q39180574961.233Q42439443119.232Q42439443119.233Q45257319447.232Q45257319447.233Q47387919910.228Q50246429048.232Q5265442331.230 Q5265442331.231 Q53915156798.229Q55415036769.232Q55415036769.233Q56854244147.232Q56854244147.233Q60191312605.231Q60191312605.232Q60546513284.230Q60703360670.229Q64132804025.232Q64132804025.233Q64683667846.232Q64683667846.233Q66730946590.229Q67028250965.229Q67877090750.22900001G02^04G06007Y09L09M09N09R09S09T09U09m0:10:20:30:40:50:60:C0:_0;H0;M0;R0;k0<G0<H0<R0<S0<b0<o0=l0?_0@m0B?0CS0E00F>0GP0H^0Il0K@0L]0Mm0OA0Of0PO0QJ0R\0SW0T>0T?0T@0UR0VH0WB0XP0Y70Y80YO0Yf0Yg0Yh0[60\D0]R0^`0_I0`60aD0bR0c90dG0d_0e70e^0fC0fl0fm0fn0h80iB0iY0jT0jU0jV0kL0lF0mA0n<0ncS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2hc2FB3sp13HTc3SP13SPR4SP1R2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2hc2FB3sp13HTc3SP13SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP14NRTa3SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP14NRTa3SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP14NRTa3SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp13Hpc4NRTa3SPR4SP1R2F05BUFLOFSS2PPFFFS1R3HIA1h2sp2lo3TOP4HTOPS2loFSSSFS1P3END2bs2KES2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS3CURS3sp1S1R3BUF2lo2bs3LOS3ALO3BCES2LF2sp2PP3CUR2bs3LFB2FB3sp1FS1R2lo3LOSSS2sp2lo3sp13SP1S1P3END2bs2KES1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp13Hpc4NRTa3SPR4SP1R2F05BUFLOS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP14NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP14NRTa2HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO4NRTa2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO4NRTa2F12HB5Ha_st5Hl_st3CUR4FBLOS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14NRTa4FBLO2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14NRTa4FBLO2HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO4NRTa2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO4NRTa2F12HB5Ha_st5Hl_st4FBLO3CURS1R3NS13NA14STKp5STKp02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP14NRTa5BUFLO2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP14NRTa5BUFLO2HB5Ha_st5Hl_st3CURS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3LOS3sp13SP13ALO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFFS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB4PPLO3SLO3sp13SP14NRTa2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS2LF2bs3LFB3sp14SP1R2HBS2LF2bs3LFB3sp14SP1R2HBFFS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP14NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP14NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALO4NRTa2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS3sp12HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS3sp12HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3LOS3sp13SP14NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB3sp12HB5Ha_stS2LF2bs3LFB3sp12HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_st3CURFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB3sp14SP1R2HBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaFFS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp14HTOP2HB5Ha_st5Hl_st3CURS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOP". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP PPLO BIN B1 B3 B5 CUR0 CWC SLOS SLOL SLO TOP SPH LOS"] Lemma pre_walk : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (ctc cpc : word) (clc cpp cnx : Z) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s2v s7v s8v s9v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 248) k0 k8 k16 k24 k48 j64 tg pd ln pv jn P CUR ctc cpc clc cpp cnx mm ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms => exists (mm' : mem) (j64' : list byte) (a0' a1' s2' s7' s8' : word) (pc' : Z),
         ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0' a1' a2 a3 (Z_to_bv 64 FB) a5 a6 a7
                      s2' (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) s7' s8'
                      (Z_to_bv 64 CUR) (Z_to_bv 64 P) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 pc') fc None mm' (seg_rom asegs)
         /\ presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc CUR) mm mm'
         /\ ((pc' = 0xae878 /\ END <= P
              /\ sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 248) k0 k8 k16 k24 k48 j64' tg pd ln pv jn P CUR ctc cpc clc cpp cnx mm')
             \/ (pc' = 0xae6b0 /\ P < END /\ s2' = Z_to_bv 64 (-8) /\ s7' = Z_to_bv 64 (FB + 32) /\ s8' = Z_to_bv 64 (FB + 64)
                 /\ sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 248) k0 K8 K16 K24 K48 j64' tg pd ln pv jn P CUR ctc cpc clc cpp cnx mm')))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 (Z_to_bv 64 FB) a5 a6 a7
               s2v (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) s7v s8v
               s9v (Z_to_bv 64 P) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae674) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D. sfr_open D.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE.
    { idtac "PRE-SKIP".
      assert (PGE : END <= P) by (clear - KE Hpc B1 B5 B3 B47; kland KE; rewrite ?Z.mod_small in KE by lia; lia).
      zstep. apply evtA_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [eassumption|]. left. split; [reflexivity|]. split; [exact PGE|].
      fin_sfr ltac:(idtac). }
    assert (PLT : P < END) by (clear - KE Hpc B1 B5 B3 B47; kland KE; rewrite ?Z.mod_small in KE by lia; lia).
    (* [comment removed for export] *)
    do 14 zstep.
    idtac "PRE-HEAD".
    apply evtA_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [eassumption|]. right. split; [reflexivity|]. split; [exact PLT|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold A_x509_san_ext_C.sfr. spine;
      first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (repeat split; eassumption) | reflexivity
            | (unfold A_x509_san_ext_A.rsl;
               lazymatch goal with H : rw_cells _ ?mx sp1 ?cs |- rw_cells _ ?mx sp1 ?cs' => replace cs' with cs; [exact H|] end;
               repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity)))
            | match goal with |- ?g => idtac "PRE-SFR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L10717539247.2 L15280432730.4 L18570614261.8 L31154747521.4 L32352139684.10L33370412135.4 L34233982622.4 L34967395327.9 L39172636981.0 L49255527545.8 L56281978260.2 L57777299826.2 L61810296239.8 L63486584942.4 L63924389993.5 L65110696054.4 00000700C00c00n01L01X01e02G02H02d02k03203N03Z03g043S1d3D0'S1P3END1p2C1S4PHIp4CNTp1P3END1p4PHIa3PHI3BT1S1P1p2p12LwS1P3END1p3Hpq2p12Lw3HP13HLE2LRS1P3END1p2C1S1p2p12Lw3HP1S4FFRp4CNTp1P3END1d1p4FFRa3FFR3BT2SS1P1p5nodes3CNT2p12Lw3HP12LRS2Lw2LRS2Lw2LRS1P1p5nodes3CNT2p12Lw3HP12LRS1P3END1p2C1S1P3END1p3HpqS1P3END1p2C1". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 AMS AMC CALLOC HMND STKp STKp0 PSAN FREEL SEQFREE PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV BUD BUDF UW"] Lemma iter : forall p, (forall p', p < p' -> LoopOb p') -> LoopOb p.
  Proof.
    intros p IH. unfold A_x509_san_ext_K.LoopOb. intros until t6. intros D PLT PHI FFR CNT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    dpose D as (SFR & HKq & _ & _ & _ & _ & _ & NDq & _ & _ & _ & _ & CBq).
    dpose SFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpq & _).
    assert (C1 : 0 <= p - P <= NB) by (clear - Hpq B2; lia).
    destruct (A_x509_san_ext_K.bud_top PHIp FFRp CNTp PHIp_mono FFRp_mono CNTp_mono P END d (p - P) 0 C1 ltac:(clear - C1; lia) D0') as [BT1 BT2].
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKq (mo_frame_refl moc))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply A_x509_san_ext_D.seg1 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact SFR | exact PLT | eassumption | match goal with |- ?g => idtac "IT-S1-PRE-LEFT:" g end ]. }
    cbv beta. intros ms1 [CQ | EQ].
    2:{ idtac "IT-ERR1".
        eapply A_x509_san_ext_H.err_fin with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
          first [ exact D | exact EQ | exact CBq | eassumption
                | lazymatch goal with
                  | |- Z.of_nat (length _) <= _ => unfold A_x509_san_ext_bud.CNTx; apply (A_x509_san_ext_bud.cnt2_div _ (p - P)); [exact CNT| clear - C1; lia]
                  | |- PHIa <= _ => clear - PHI BT1; lia
                  | |- FFRa <= _ => clear - FFR BT2; lia
                  end
                | match goal with |- ?g => idtac "IT-ERR1-LEFT:" g end ]. }
    ddestruct CQ as (mm & p1 & w0' & w1' & w2' & tg' & pd' & Lw & j64' & xra' & u0 & u1 & u2 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & us10 & u3 & u4 & u5 & u6
                    & -> & HP1 & HLE & S1 & PW).
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof D as DS.
    eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S1| exact PW| exact CBq].
    (* [comment removed for export] *)
    assert (C2 : 0 <= p1 + bv_unsigned Lw - P <= NB) by (clear - Hpq HP1 HLE LR B2; lia).
    destruct (A_x509_san_ext_K.bud_iter PHIp FFRp CNTp PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add d (p - P) (bv_unsigned Lw) (p1 + bv_unsigned Lw - p)
                ltac:(clear - C1; lia) ltac:(clear - LR; lia) ltac:(clear - HP1; lia) D0') as [BI1 BI2].
    replace (p - P + (p1 + bv_unsigned Lw - p)) with (p1 + bv_unsigned Lw - P) in BI1, BI2 by (clear; lia).
    assert (KN : 0 <= Z.of_nat (length nodes) /\ 2 * Z.of_nat (length nodes) <= p1 + bv_unsigned Lw - P) by (clear - CNT HP1 LR; lia).
    destruct (A_x509_san_ext_K.bud_top PHIp FFRp CNTp PHIp_mono FFRp_mono CNTp_mono P END d (p1 + bv_unsigned Lw - P) (Z.of_nat (length nodes)) C2 KN D0') as [BU1 BU2].
    pose proof (CNTp_mono 0 (bv_unsigned Lw) ltac:(clear - LR; lia)) as CN0.
    assert (FC3 : fr_charge 0 = 3) by reflexivity. assert (AV0 : AVOL_CALL = 0) by reflexivity.
    assert (FC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0'; lia).
    (* [comment removed for export] *)
    idtac "IT-PSAN".
    eapply A_x509_san_ext_I.psan_step with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
      first [ exact DS | exact HLE | eassumption
            | lazymatch goal with
              | |- havol _ _ _ _ + _ + _ <= AVOL_MAX => clear - BUD PHI BI1 BU1 CN0 AV0 KN; nia
              | |- hfr _ _ _ _ + _ + _ <= FR_MAX => clear - BUDF FFR BI2 BU2 CN0 FC3 FC0 KN; nia
              | |- forall _, _ => idtac
              end
            | match goal with |- ?g => idtac "IT-PSAN-PRE-LEFT:" g end ].
    intros m1 mo1 h1 nn r t dn rest jn' y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 DP SANc TR T4 NC TN RN NDn CNTn Hr.
    pose proof DP as (SFRp & _).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
    { eapply A_x509_san_ext_G.seg2 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (r := r) (t := t) (dn := dn) (rest := rest);
        first [ exact SFRp | exact SANc | exact TR | exact T4 | exact Hr | reflexivity | eassumption | match goal with |- ?g => idtac "IT-S2-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 [(R0 & R1 & a1' & ->) | (RC & [(E4 & a1' & ->) | (TN4 & a0' & a1' & ->)])].
    - (* [comment removed for export] *)
      idtac "IT-FATAL".
      pose proof (RN R0) as ENN. subst nn. cbn [rev SNAME map app] in DP, SFRp.
      pose proof DP as DP'. svA_open DP'. pose proof SFR0 as SFR0'. sfr_open SFR0'.
      destruct (A_x509_san_ext_C.close_nodes R LB LF PP CUR END BUF FB (nLB nodes) nodes cur m1 _ _ _ _ HFR HCF HHD SUBN HLS CURc CBUF)
        as [(ht & hpd & hl & hp & HHEAD & HHB) HLF].
      pose proof (seq_lseg_chain asegs _ _ BUF END nodes HLF) as CHN.
      assert (HB' : (hp = 0 /\ hl = 0) \/ (BUF <= hp /\ 0 <= hl /\ hp + hl <= END)) by (clear - HHB; destruct HHB as [(X1 & X2 & _)|X]; [left; split; assumption| right; exact X]).
      eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
      { eapply A_x509_san_ext_G.fatal1 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (r := r) (hnx := hd 0 nodes);
          first [ exact SFR0 | exact HHEAD | eassumption | match goal with |- ?g => idtac "IT-F1-PRE-LEFT:" g end ]. }
      cbv beta. intros ms3 (a1'' & ->).
      pose proof (A_x509_san_ext_J.svA_rehead R HIA IMG h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs ALC CUR0 CWC CURLO DCB D1 SLOS SLOL
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht hpd hl hp (hd 0 nodes) DP HHEAD HB') as DR.
      eapply A_x509_san_ext_J.seqfree_step with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact DR | exact CHN | exact HND | eassumption
              | lazymatch goal with
                | |- havol _ _ _ _ + _ + _ <= AVOL_MAX => clear - BUD PHI BI1 BU1 CN0 AV0 KN; nia
                | |- hfr _ _ _ _ + _ + _ <= FR_MAX => clear - BUDF FFR BI2 BU2 CN0 FC3 FC0 KN; nia
                | |- forall _, _ => idtac
                end
              | match goal with |- ?g => idtac "IT-SEQF-PRE-LEFT:" g end ].
      intros m2 mo2 h2 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 DQ.
      pose proof DQ as (SFRq & _).
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo2).
      { eapply A_x509_san_ext_G.fatal2 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (r := r);
          first [ exact SFRq | exact Hr | eassumption | (intros E0; exfalso; first [exact (R0 E0) | exact (R1 E0) | (clear - E0 R0 R1; lia)]) | match goal with |- ?g => idtac "IT-F2-PRE-LEFT:" g end ]. }
      cbv beta. intros ms4 EX.
      eapply A_x509_san_ext_H.exitp_fin with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (nodes := @nil Z);
        first [ exact DQ | exact EX | eassumption
              | lazymatch goal with
                | |- _ \/ _ => clear - HB'; destruct HB' as [(X1 & X2)|X]; [left; repeat split; assumption| right; exact X]
                | |- Z.of_nat (length _) <= _ => unfold A_x509_san_ext_bud.CNTx; cbn [length Z.of_nat]; apply Z.div_pos; [clear - C1; lia| clear; lia]
                | |- _ <= A_x509_san_ext_bud.PHIx _ _ _ => clear - PHI BI1 BU1 CN0 AV0 KN; nia
                | |- _ <= A_x509_san_ext_bud.FFRx _ _ _ _ => clear - FFR BI2 BU2 CN0 FC3 FC0 KN; nia
                end
              | match goal with |- ?g => idtac "IT-FATAL-FIN-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "IT-FREE".
      eapply A_x509_san_ext_J.freel_step with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact DP | exact (NC E4) | exact NDn | eassumption
              | lazymatch goal with
                | |- havol _ _ _ _ + _ + _ <= AVOL_MAX => clear - BUD PHI BI1 BU1 CN0 AV0 KN CNTn; nia
                | |- hfr _ _ _ _ + _ + _ <= FR_MAX => clear - BUDF FFR BI2 BU2 CN0 FC3 FC0 KN CNTn; nia
                | |- forall _, _ => idtac
                end
              | match goal with |- ?g => idtac "IT-FREEL-PRE-LEFT:" g end ].
      intros m2 mo2 h2 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 DQ.
      eapply (A_x509_san_ext_L.append_part) with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (p0 := p);
        first [ exact IH | exact DQ | exact HP1 | exact HLE | eassumption
              | lazymatch goal with
                | |- _ <= A_x509_san_ext_K.PHIy _ _ _ => clear - PHI BI1 CN0 AV0 CNTn; nia
                | |- _ <= A_x509_san_ext_K.FFRy _ _ _ _ => clear - FFR BI2 CN0 FC3 FC0 CNTn; nia
                | |- 2 * (Z.of_nat (length _) + 1) <= _ => clear - CNT HP1 LR; lia
                end
              | match goal with |- ?g => idtac "IT-APP1-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "IT-APPEND".
      pose proof (TN TN4) as ENN. subst nn. cbn [rev SNAME map app] in DP.
      eapply (A_x509_san_ext_L.append_part) with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (p0 := p);
        first [ exact IH | exact DP | exact HP1 | exact HLE | eassumption
              | lazymatch goal with
                | |- _ <= A_x509_san_ext_K.PHIy _ _ _ => clear - PHI BI1 CN0 AV0; nia
                | |- _ <= A_x509_san_ext_K.FFRy _ _ _ _ => clear - FFR BI2 CN0 FC3 FC0; nia
                | |- 2 * (Z.of_nat (length _) + 1) <= _ => clear - CNT HP1 LR; lia
                end
              | match goal with |- ?g => idtac "IT-APP2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L26728691728.6L59308579027.400000C00PS3END1k1p2Hk2p'3Hp'S3END1p2Hk2H0". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 AMS AMC CALLOC HMND STKp STKp0 PSAN FREEL SEQFREE PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV BUD BUDF UW"] Lemma loops : forall (k : nat) (p : Z), END - p < Z.of_nat k -> LoopOb p.
  Proof.
    induction k as [|k IHk]; intros p Hk.
    - unfold A_x509_san_ext_K.LoopOb. intros. exfalso. clear - Hk H0. lia.
    - apply iter. intros p' Hp'. apply IHk. clear - Hk Hp'. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L11033178002.3L26892418956.1L27735870085.5L39172636981.0L40281191306.3L44921588402.0L49493397620.3L51578300575.1L52753581537.5L54765347722.1L57374658089.4L58872464727.1L64630569949.3L64850595401.0L65110679799.300000;00?00R00S00\00]00g00l01601901G01J01S01T01^S1P3END3PLTS2spS4FFRp4CNTp1d2M22M3SS1R3HIA1hSS1P3END2B2S3CURS1P3END2B2S1PS4PHIp4CNTp2M1S1PS1R3HIA1hSS1P3END2B2". (* [comment removed for export] *)
  #[using="IMG UARG SM2 NS1 NA1 AMS AMC CALLOC HMND STKp STKp0 PSAN FREEL SEQFREE PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add NRT bs ct cpad LFB HPP ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB HCUR ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS BUD BUDF UW"] Lemma main_call : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m CUR 32 ->
    aevtS asegs POST
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 CUR) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_X509_SAN_EXT) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST SS MI OPP OCUR.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_san_ext_A.pro_walk with (STKp := STKp) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (ct := ct) (cpad := cpad);
        first [ exact HH | exact ST | exact SS | exact MI | exact OPP | exact OCUR | exact OBUF | eassumption | match goal with |- ?g => idtac "MAIN-PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    ddestruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6
                   & w0 & w1 & w2 & tl & k0 & k8 & k16 & k24 & k48 & j64 & jt & jn
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & TLc & TSN & FSH & SAVE & RSL & TSBraw
                   & STb & STlo & MI1 & HPP1 & HCUR1 & HB1 & OPP1 & OCUR1 & OBUF1 & APP & APC & APB & PRES0 & SS1).
    intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo1) _ _ mo1 (conj (proj2 (HKI mo1) HK1) (mo_frame_refl mo1))).
    rt_facts.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m1 (sp1 + 96) [] 24 jt [] [4; 4; 8; 8]%nat) in TSBraw; [| reflexivity]. cbn [mk_CB_cells app] in TSBraw.
    cb4_to_c4 TSBraw (@nil cell).
    lazymatch type of TSBraw with rw_cells _ _ _ (?c1 :: _) => cb4_to_c4 TSBraw [c1] end.
    lazymatch type of TSBraw with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 TSBraw [c1; c2] end.
    lazymatch type of TSBraw with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 TSBraw [c1; c2; c3] end.
    (* [comment removed for export] *)
    assert (PRESx : presW asegs R HIA h1 LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m1).
    { eapply (presW_hmono R HIA h h1); [| intros x Hx; rewrite Ehcs; exact Hx| exact Estk].
      ddestruct PRES0 as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
    unfold seq_cells in HCUR1.
    lazymatch type of TSBraw with rw_cells _ _ _ [C4 ?tgv; C4 ?pdv; C8 ?lnv; C8 ?pvv] =>
      assert (D : svA (nLB []) FB sp1 0 0 w0 w1 w2 tl (Z_to_bv 8 248) k0 k8 k16 k24 k48 j64 tgv pdv lnv pvv jn P [] CUR ct cpad 0 0 0 m1 mo1 h1) end.
    { split.
      { unfold A_x509_san_ext_C.sfr.
        spine; first [ exact HH1 | exact PRESx | exact TSBraw | exact HCUR1 | eassumption | (rewrite Ehcs; eassumption) | reflexivity | idtac ].
        - intros x Hx. rewrite Ehcs. exact Hx.
        - intros b' Hb. exact Hb.
        - clear - B1 B2. lia.
        - split; [exact ALC|]. split; [exact CUR0|]. split; [exact CURLO|]. split; [exact D1|]. split; [exact DCB|]. split; [exact APC|].
          split; [| apply wcover_inside; cbn [inside]; right; left; clear; lia].
          eapply client_wrange_mono; [exact CWC|]. intros b' Hb. apply fdata_cons_sub. exact Hb. }
      split; [apply (proj2 (HKI mo1)); exact HK1|]. split; [exact MF1|]. split; [exact Eflag|].
      split; [rewrite Evol; clear; lia|]. split; [rewrite Efr; clear; lia|].
      split; [intros x []|]. split; [constructor|]. split; [intros x []|]. split; [left; split; reflexivity|]. split; [left; reflexivity|].
      split; [exact I|]. left. repeat split; reflexivity. }
    dpose D as (SFR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CBq).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
    { eapply pre_walk; first [ exact SFR | match goal with |- ?g => idtac "MAIN-PRE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (mm' & j64' & a0' & a1' & s2' & s7' & s8' & pc' & -> & PW & [(-> & PGE & S2) | (-> & PLT & -> & -> & -> & S2)])).
    - (* [comment removed for export] *)
      idtac "MAIN-SKIP".
      pose proof D as DS.
      eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S2| exact PW| exact CBq].
      eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
      { eapply A_x509_san_ext_E.exit_walk with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
          first [ exact S2 | eassumption | match goal with |- ?g => idtac "MAIN-X-PRE-LEFT:" g end ]. }
      cbv beta. intros ms3 EX.
      pose proof (PHIp_mono 0 NB ltac:(clear - B2; lia)) as M1. pose proof (FFRp_mono 0 NB (d + 1) ltac:(clear - B2; lia)) as M2. pose proof (CNTp_mono 0 NB ltac:(clear - B2; lia)) as M3.
      eapply A_x509_san_ext_H.exitp_fin with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (nodes := @nil Z);
        first [ exact DS | exact EX | exact CBq | eassumption
              | lazymatch goal with
                | |- Z.of_nat (length _) <= _ => unfold A_x509_san_ext_bud.CNTx; cbn [length Z.of_nat]; apply Z.div_pos; [clear - B2; lia| clear; lia]
                | |- 0 <= A_x509_san_ext_bud.PHIx _ _ _ => unfold A_x509_san_ext_bud.PHIx, AVOL_CALL; clear - M1 M3 B2; nia
                | |- 0 <= A_x509_san_ext_bud.FFRx _ _ _ _ => unfold A_x509_san_ext_bud.FFRx, fr_charge; pose proof (Z.div_pos NB 2 ltac:(clear - B2; lia) ltac:(clear; lia)) as DP2; pose proof (Z.le_max_l 0 (d + 1 + 3)) as MX; clear - M2 M3 B2 D0' DP2 MX; nia
                end
              | match goal with |- ?g => idtac "MAIN-SKIP-FIN-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "MAIN-LOOP".
      pose proof D as DS.
      eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S2| exact PW| exact CBq].
      pose proof (PHIp_mono 0 0 ltac:(clear; lia)) as M1. pose proof (FFRp_mono 0 0 (d + 1) ltac:(clear; lia)) as M2. pose proof (CNTp_mono 0 0 ltac:(clear; lia)) as M3.
      intros mo2 [HK2 MF2].
      eapply (loops (S (Z.to_nat (END - P))) P ltac:(clear - PLT; lia));
        [ eapply A_x509_san_ext_H.svA_mo; [exact DS| exact HK2| exact MF2] | exact PLT | | | ].
      + replace (P - P) with 0 by (clear; lia). unfold A_x509_san_ext_K.PHIy, AVOL_CALL. clear - M1 M3. lia.
      + replace (P - P) with 0 by (clear; lia). unfold A_x509_san_ext_K.FFRy, fr_charge. change (0 / 2) with 0. clear - M2 M3. lia.
      + cbn [length Z.of_nat]. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  #[using="IMG UARG SM2 NS1 NA1 AMS AMC CALLOC HMND STKp0 PSAN FREEL SEQFREE PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add NRT"] Theorem A_x509_san_ext_specE :
    seq_parser_stmtE asegs R HIA PHIx FFRx CNTx STKx (LFMAX_CRT + 5) (fun _ => True) (fun r => r = 0) A_X509_SAN_EXT.
  Proof.
    unfold seq_parser_stmtE. intros until cpad. intros; subst.
    eapply main_call with (bs := bs) (ct := ct) (cpad := cpad); first [eassumption | reflexivity].
  Qed.
  #[using="IMG UARG SM2 NS1 NA1 AMS AMC CALLOC HMND STKp0 PSAN FREEL SEQFREE PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add NRT"] Theorem A_x509_san_ext_spec : seq_parser_stmtA asegs R HIA PHIx FFRx CNTx STKx (LFMAX_CRT + 5) (fun _ => True) A_X509_SAN_EXT.
  Proof. exact (seq_parser_stmtE_A _ _ _ _ _ _ _ _ _ _ _ A_x509_san_ext_specE). Qed.
End Walk.

(* [comment removed for export] *)

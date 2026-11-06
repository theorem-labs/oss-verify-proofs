(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int
     A_asn1_get_alg_null_A A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_pkcs7_top24 A_pkcs7_getcerts_stmt24 A_pkcs7_parse_A A_pkcs7_parse_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pkcs7_parse_D24 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "OSSVerify.KrLib.Spec.RepCrt.pkcs7_at"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.A_pkcs7_free.p7small"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.A.A_pkcs7_parse_C.CNTp"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.A.A_pkcs7_parse_C.PHIp"; "OSSVerify.KrLib.A.A_pkcs7_parse_C.FFRp"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.Frame.outside"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.SInv.si_fp"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Cells.cell"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.Spec.RepCrt.p7_own"; "OSSVerify.KrLib.Spec.RepCrt.p7_junk"; "OSSVerify.KrLib.A.A_pkcs7_parse_C24.dvA"; "OSSVerify.KrLib.Lib.Cells.C1"; "Walk.Call.tailP"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_pkcs7_top24.pkcs7_parse_der_postA24"; "OSSVerify.KrLib.A.A_pkcs7_free.p7repA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.land"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable PK : pk_class asegs.
  Variable SI : sinv (arl_L R).
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIg : Z -> Z) (FFRg : Z -> Z -> Z) (CNTg : Z -> Z) (STKg : Z).
  Variable C24c : Z.   (* [comment removed for export] *)
  Hypothesis C24c0 : 0 <= C24c.
  Hypothesis GETCERTS : pkcs7_get_certs_stmtA24 asegs R HIA PK SI PHIg FFRg CNTg STKg C24c A_PKCS7_GETCERTS.
  Variables (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z) (STKs : Z).
  Hypothesis GETSIGNERS : pkcs7_getsigners_stmtA asegs R HIA PHIs FFRs CNTs STKs A_PKCS7_GETSIGNERS.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Variables (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PKFREE : pkcs7_free_stmtA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIg_mono : forall n n', 0 <= n <= n' -> 0 <= PHIg n <= PHIg n'.
  Hypothesis FFRg_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRg n d <= FFRg n' d.
  Hypothesis CNTg_mono : forall n n', 0 <= n <= n' -> 0 <= CNTg n <= CNTg n'.
  Hypothesis PHIs_mono : forall n n', 0 <= n <= n' -> 0 <= PHIs n <= PHIs n'.
  Hypothesis FFRs_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRs n d <= FFRs n' d.
  Hypothesis CNTs_mono : forall n n', 0 <= n <= n' -> 0 <= CNTs n <= CNTs n'.
  Hypothesis PHIj_mono : forall n n', 0 <= n <= n' -> 0 <= PHIj n <= PHIj n'.
  Hypothesis FFRj_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRj n d <= FFRj n' d.
  Hypothesis CNTj_mono : forall n n', 0 <= n <= n' -> 0 <= CNTj n <= CNTj n'.
  Hypothesis PHIj_joint : forall a b, 0 <= a -> 0 <= b -> PHIg a + PHIs b <= PHIj (a + b).
  Hypothesis FFRj_joint : forall a b d, 0 <= a -> 0 <= b -> FFRg a d + FFRs b d <= FFRj (a + b) d.
  Hypothesis CNTj_joint : forall a b, 0 <= a -> 0 <= b -> CNTg a + CNTs b <= CNTj (a + b).
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis STKg0 : 0 <= STKg. Hypothesis STKs0 : 0 <= STKs. Hypothesis STKf0 : 0 <= STKf.
  (* [comment removed for export] *)
  Local Notation STKp := (STKp R STKg STKs STKf).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (A DATA n lo slo d : Z) (bs : list byte).
  Hypothesis P7Z : pkcs7_zero asegs m A.
  Hypothesis AAL : A mod 8 = 0.
  Hypothesis A0 : 0 < A.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A PKCS7_SIZE.
  Hypothesis ASTK : A + PKCS7_SIZE <= arl_stklo R.
  Hypothesis AOD : A + PKCS7_SIZE <= hl_data_lo L \/ hl_data_hi L <= A.
  Hypothesis HBY : bytes_at asegs m DATA bs.
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2 ^ 26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CRD : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis DA : n = 0 \/ A + PKCS7_SIZE <= DATA \/ DATA + n <= A.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKp.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 33)%nat.
  Hypothesis C24H : cnt24 LB + 1 + 2 * (n / 5889) + C24c <= C24MAX.     (* [comment removed for export] *)
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.10200000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
  Let ALO1 : A + PKCS7_SIZE <= lo. Proof. pose proof LOS. pose proof ASTK. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2 in SM2; unfold A_pkcs7_parse_A.STKp in SLO; unfold PKCS7_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].



  Local Notation CNTp := (CNTp CNTj).
  Local Notation PHIp := (PHIp PHIj CNTj PHIf).
  Local Notation FFRp := (FFRp FFRj CNTj FFRf).
  Local Notation POST := (pkcs7_parse_der_postA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) SI PHIp FFRp CNTp
                            h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n lo slo d m mo0).
  Local Notation X0 := [(A, A + 1440)].
  Local Notation dvA := (dvA R HIA SI h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 A n lo slo).
  Local Notation C1x32 := (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte =>
    [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
     C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]).

  (* [comment removed for export] *)
  Definition tailP (W : list ivl) (PHIa FFRa : Z) (Lc : list blk) (mc : mem) (st : option (p7_own * p7_junk)) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "(0.(1.$2.VPK,O1.O2.O3.VLB,VA,)(0.(3.O1.)(0.(4.(5.(6.$7.O3.))(8.VCNTj,Vn,))(0.(4.(9.O5.A1.VPHIf,(5.(6.$7.O3.)))(:.VPHIj,VCNTj,VPHIf,Vn,))(0.(4.(9.O4.A2.VFFRf,(5.(6.$7.O3.))=)(;.VFFRj,VCNTj,VFFRf,Vn,Vd,))(0.Px,$<.P,(=.(>.(?.$<.$<.)(10.(?.$<.$<.)(11.$<.$<.VA,(9.VA,+5:0.))(12.(?.$<.$<.)))(13.(14.VR,)VSI,))R1.)(=.O6.R2.)(0.Px,$<.P,(=.O6.R1.)(=.(10.(?.$<.$<.)(11.$<.$<.VA,(9.VA,+5:0.))(12.(?.$<.$<.)))R2.)(0.(4.(9.(15.$2.VR,VHIA,Vh,)(:.VPHIj,VCNTj,VPHIf,Vn,))$16.)(4.(9.(17.$2.VR,VHIA,Vh,)(;.VFFRj,VCNTj,VFFRf,Vn,Vd,))$18.)))))))))")
(* [comment removed for export] *).

  Ltac dvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SIc & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & G8 & G12 & G16 & G18 & G22 & FSH & SAVE & RSL
                   & STa & STb & STlo & CELLS & SZC & OBJA & MIc & SSc & C24i).
  Ltac dvA_build :=
    cbv delta [A_pkcs7_parse_C24.dvA] beta;
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity
          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA-LEFT:" g end ] ].

  (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB"] Lemma tail_9755c : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv16,(1;.&40.)Pv24,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps3v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R42.R41.R40.R3?.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R48.R47.R3>.R46.R3=.R45.R3<.R1;.R1:.R19.R18.)P,(24.R4?.R4>.R4=.R1<.R1;.R18.)P,(0.(4.(25.(26.+2.+1?.))R18.)(27.R18.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R18.(2>.&40.R52.)Vgp,Vtp,R17.R16.R15.Vsp,(2>.&40.R52.)R14.R13.R12.R11.R10.R?.R>.R=.R8.R7.(2>.&40.R19.)R6.R5.R4.(2>.&40.R53.)(2>.&40.VA,)(2>.&40.(9.(2?.R53.+3.)(30.(31.VR,))))(2>.&40.R53.)R<.R;.R:.R9.)VF,(2>.&40.+9752<.)Vfc,(32.(1;.&40.))R1=.(33.$2.))R1<.))")
(* [comment removed for export] *).
  Proof.
    intros until s7v. intros D TP Hr. cbv beta in D. pose proof D as D0. dvA_open D. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    zstep.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
      first [exact HW | exact HWX | eassumption | dvA_build ].
  Qed.

  (* [comment removed for export] *)
  Ltac tail_prep :=
    rt_facts;
    lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) ((?FB, 256) :: LF) ?mc |- _ =>
      pose proof (hcs_ok asegs R HIA hc) as CSOKc;
      pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT;
      lazymatch goal with HTc : htop _ _ _ hc = _, HSc : hstkhi _ _ _ hc = _, HCSc : forall x, CS x -> hcs _ _ _ hc x, CFB : crange CS FB 256, OBJA : aobj _ _ CS mc A 1440, FRSH : fresh_apart R LB LF FB 256, F64 : FB mod 64 = 0, SCS0 : crange CS (arl_stklo R) _ |- _ =>
        rewrite HTc, HSc in HT;
        pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc;
        pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c;
        pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJA) as OBJc;
        pose proof OBJA as CRA; apply aobj_crange in CRA;
        pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 256 FRSH HHc) as FRSH3;
        destruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 256 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
          as (_ & INF & INH & IND & AP & _ & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
        pose proof FRSH as FRSH'; unfold fresh_apart in FRSH'; destruct FRSH' as (F0 & F1 & F2 & F3);
        pose proof (frame_apart_obj R HIA LB LF lo _ A 1440 FB 256 FRSH CWA ltac:(clear; lia) ltac:(clear; lia) LOS) as APPA;
        pose proof (art_stk_high asegs R HIA) as STKH;
        assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKg0 STKs0 STKf0 TOP HT; lia]);
        pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc
      end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30163642507.30L40228640085.0 00000g00hS1r2Hr1q2r02r21H2H02q02r12H42H52q12r32H93H102q23H143H15S". (* [comment removed for export] *)
  #[using="Type"] Lemma sext_small : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "Pr,$<.P,(0.(4.(25.(26.+2.+1?.))R1.)(27.R1.(26.+2.+1?.)))(34.(1;.&40.)(2>.&40.(35.&20.(9.(36.R2.+????????????????.)=)))(2>.&40.R2.))")
(* [comment removed for export] *).
  Proof.
    intros r Hr. apply bv_eq. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). rewrite Z.add_0_r.
    rewrite ?Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. change (2 ^ Z.of_N 64) with 18446744073709551616.
    clear - Hr. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L16467427964.257L35666023782.15 L36961436047.257L43300649301.0  L57124690773.0  L60098763854.6  L64850595401.0  Q21925682067.262Q27942899219.262Q35288190350.262Q7522361358.262 00000d01I02=02>02?02I02J03G04D05:060S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS1R2lo3LOSSS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_97558 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps3v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)Ps8v,(1;.&40.)Ps9v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R46.R45.R44.R43.R42.R41.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(2>.&40.VA,)(2>.&40.R50.)R40.R48.R3?.R47.R3>.R1=.R1<.R1;.R1:.)P,(24.R4?.R4>.R4=.R1>.R1=.R1:.)P,(0.(4.(25.(26.+2.+1?.))R1:.)(27.R1:.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R1:.(2>.&40.R52.)Vgp,Vtp,R19.R18.R17.Vsp,(2>.&40.R52.)R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.(2>.&40.R1;.)R8.R7.R6.R5.R4.(2>.&40.(9.(2?.R53.+3.)(30.(31.VR,))))(2>.&40.R53.)R>.R=.R<.R;.)VF,(2>.&40.+97524.)Vfc,(32.(1;.&40.))R1?.(33.$2.))R1>.))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    zstep. zstep.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    eapply (tail_9755c FB sp1 W PHIa FFRa w0 w1 w2 (Z_to_bv 64 A) (Z_to_bv 64 FB) v48 v80 g4 g8 g12 g16 g18 g22 j32 alg cs
              b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 Lc mc mo9 hc st r);
      [cbv beta; dvA_build | exact TP0 | exact Hr].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L10642845640.1  L16467427964.256L24756857590.8  L29010568859.256L29023151364.255L32381388445.9  L35666023782.15 L36961436047.256L40228640085.0  L43300649301.0  L5367509977.10  L57124690773.0  L60098763854.6  L64850595401.0  Q21925682067.261Q27942899219.261Q35288190350.261Q7522361358.261 00000400h01H01I01J01l02Q03E03F03G03Z03[03e03f04c05`06V07LS2LcS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCS4PHIj4CNTj4PHIf1n4PHIa2Lc3PHI1HFFS4FFRj4CNTj4FFRf1n1d4FFRa2Lc3FFR1HS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS1r2Hr2r02KG1q1H2H0SS1R2lo3LOSSS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_97460 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)Ps8v,(1;.&40.)Ps9v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R45.R44.R43.R42.R41.R40.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(2>.&40.VA,)(2>.&40.R4?.)R3?.R47.R3>.R46.R3=.R1<.R1;.R1:.R19.)P,(24.R4>.R4=.R4<.R1=.R1<.R19.)P,(0.(4.(25.(26.+2.+1?.))R19.)(27.R19.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R19.(2>.&40.R51.)Vgp,Vtp,R18.R17.R16.Vsp,(2>.&40.R51.)R15.R14.R13.R12.R11.R10.R?.R>.R9.(2>.&40.-8.)(2>.&40.R1:.)R8.R7.R6.R5.R4.(2>.&40.(9.(2?.R52.+3.)(30.(31.VR,))))(2>.&40.R52.)R=.R<.R;.R:.)VF,(2>.&40.+9742<.)Vfc,(32.(1;.&40.))R1>.(33.$2.))R1=.))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try rewrite (sext_small r Hr).
    (* [comment removed for export] *)
    zstep. if_cases KG; zify_cond KG.
    - (* [comment removed for export] *)
      assert (R0 : 0 <= r).
      { change 18446744073709551615 with (Z.ones 64) in KG. rewrite Z.land_ones in KG by (clear; lia). clear - KG Hr. Z.div_mod_to_equations. lia. }
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      eapply (ret_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
        first [ exact HW | eassumption
              | lazymatch goal with
                | |- PHIa <= _ => pose proof (PHIf_mono 0 (Z.of_nat (length Lc)) ltac:(clear; lia)); clear - PHI H; lia
                | |- FFRa <= _ => pose proof (FFRf_mono 0 (Z.of_nat (length Lc)) 0 ltac:(clear; lia)); clear - FFR H; lia
                end
              | dvA_build ].
    - (* [comment removed for export] *)
      zstep.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
        first [ exact HW | exact HWX | eassumption | dvA_build ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L16467427964.256L35666023782.15 L36961436047.256L43300649301.0  L57124690773.0  L60098763854.6  L64850595401.0  Q21925682067.261Q27942899219.261Q35288190350.261Q7522361358.261 00000d01I02=02>02?02I02J03G04D05:060S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS1R2lo3LOSSS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_97768 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)Ps8v,(1;.&40.)Ps9v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R45.R44.R43.R42.R41.R40.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(2>.&40.VA,)(2>.&40.R4?.)R3?.R47.R3>.R46.R3=.R1<.R1;.R1:.R19.)P,(24.R4>.R4=.R4<.R1=.R1<.R19.)P,(0.(4.(25.(26.+2.+1?.))R19.)(27.R19.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R19.(2>.&40.R51.)Vgp,Vtp,R18.R17.R16.Vsp,(2>.&40.R51.)R15.R14.R13.R12.R11.R10.R?.R>.R9.(2>.&40.-8.)(2>.&40.R1:.)R8.R7.R6.R5.R4.(2>.&40.(9.(2?.R52.+3.)(30.(31.VR,))))(2>.&40.R52.)R=.R<.R;.R:.)VF,(2>.&40.+97758.)Vfc,(32.(1;.&40.))R1>.(33.$2.))R1=.))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
      first [ exact HW | exact HWX | eassumption | dvA_build ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@L16467427964.259L1685717371.0   L24023900370.0  L27817441514.276L27817441514.277L35666023782.15 L36961436047.259L42411609006.0  L43300649301.0  L50790731766.15 L57124690773.0  L60098763854.6  L64850595401.0  L8171953640.276 L8171953640.277 P32557674715.280P32557674715.281P53346601986.280P53346601986.281Q10592318623.276Q125584537.274  Q15605646235.272Q18089490443.275Q18099926587.275Q18708020747.275Q18861529033.275Q21925682067.264Q26314584654.280Q26314584654.281Q26316671538.265Q27663034012.273Q27940667404.269Q27942899219.264Q29743073578.264Q34357517860.270Q35288190350.264Q36940995257.275Q37706020980.268Q38802716827.276Q39285966488.273Q3933900710.269 Q39682685338.271Q40599399476.275Q42441548847.280Q42441548847.281Q44298944140.265Q44301027056.280Q44301027056.281Q45819994683.275Q45834628107.275Q48119910507.280Q48119910507.281Q49770149321.275Q50231601566.271Q51604307871.272Q54481541664.270Q5596578838.280 Q5596578838.281 Q57210883017.275Q58653566660.275Q58744150173.274Q58972088541.277Q59617553652.275Q59619599044.275Q59698924043.275Q59705132091.275Q59867425008.280Q59867425008.281Q62639683769.275Q64228675114.279Q64228675114.280Q64681563910.280Q64681563910.281Q6575031993.275 Q67140783850.264Q67837027513.275Q67893080934.268Q6912043747.277 Q7522361358.264 00000d00e00f02:03N04304g04h04i05W05X05b05c05d05e06l08309I0:_0;Y0<S0=M0=N0=O0>:0>e0?b0@b0Ab0BP0CJ0DY0EV0FA0GA0H70Hb0I^0JX0KR0LZ0MT0N?0OH0PQ0Q?0R?0S?0Sj0Sk0UJ0Vi0WT0XN0YH0ZO0ZP0ZQ0[<0[g0\a0][0]\0]]0]^0]_0]`0]a0^L0`Q0bV0cm0eD0eo0fZ0gE0hA0i;0j1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSSS1R2lo3LOSSFFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB2cs2Lc3SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB2cs2Lc3SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCFS1R4STKg4STKs4STKf2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB2cs2Lc3SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB2cs2Lc3SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf5STKg02LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp12cs2Lc3SP14SP1M3SZC3ALO3ACV3SPR2F82F02HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf5STKg02LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp12cs2Lc3SP14SP1M3SZC3ALO3ACV3SPR2F82F02HB5Ha_st5Hl_st5SAEstS1R3HIA4STKg4STKs4STKf1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB2cs2Lc3SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA4STKg4STKs4STKf1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB2cs2Lc3SZC2HT2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp12cs2Lc3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_977a0 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps3v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)Ps8v,(1;.&40.)Ps9v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R46.R45.R44.R43.R42.R41.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(2>.&40.VA,)(2>.&40.R50.)R40.R48.R3?.R47.R3>.R1=.R1<.R1;.R1:.)P,(24.R4?.R4>.R4=.R1>.R1=.R1:.)P,(0.(4.(25.(26.+2.+1?.))R1:.)(27.R1:.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R1:.(2>.&40.R52.)Vgp,Vtp,R19.R18.R17.Vsp,(2>.&40.R52.)R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.(2>.&40.R1;.)R8.R7.R6.R5.R4.(2>.&40.(9.(2?.R53.+3.)(30.(31.VR,))))(2>.&40.R53.)R>.R=.R<.R;.)VF,(2>.&40.+9777<.)Vfc,(32.(1;.&40.))R1?.(33.$2.))R1>.))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA hc _ _ (Lc ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    (* [comment removed for export] *)
    pose proof (conj HHc I) as HHbox. apply rw_cells_blob in CELLS. rewrite SZC in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
      assert (REPx : pkcs7_at asegs PK st mx Lc LB A);
      [ eapply (pkcs7_at_presx0 R HIA) with (bs := bs) (slo := slo) (lo := lo) (n := n) (h := h) (A := A) (sp := sp) (hq := hc) (LFq := (FB, 256) :: LF);
        first [ exact REP | exact (proj1 HHbox) | exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2)) | eassumption
              | match goal with |- ?g => idtac "REPX-LEFT:" g end ] |];
      assert (SIx : si_P SI mx);
      [ eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))| intros a _; exact I] |];
      clear SIc end.
    eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
      first [ exact HW | exact HWX | exact REPx | eassumption | dvA_build
            | match goal with |- ?g => idtac "T97494-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0@L10642845640.1  L13812385959.0  L16467427964.272L1685717371.0   L24023900370.0  L24756857590.8  L27817441514.276L27817441514.277L29010571016.271L29023151364.258L32381388445.9  L35666023782.15 L42411609006.0  L43300649301.0  L50790731766.15 L57124690773.0  L60098763854.6  L64850595401.0  L8171953640.276 L8171953640.277 P32557674715.280P32557674715.281P53346601986.280P53346601986.281Q10592318623.276Q125584537.274  Q15605646235.272Q18089490443.275Q18099926587.275Q18708020747.275Q18861529033.275Q20375131383.277Q25615717736.277Q26314584654.280Q26314584654.281Q26316671538.265Q27663034012.273Q27940667404.269Q29743073578.264Q34357517860.270Q36940995257.275Q37706020980.268Q38802716827.276Q39285966488.273Q3933900710.269 Q39682685338.271Q40599399476.275Q42441548847.280Q42441548847.281Q44298944140.265Q44301027056.280Q44301027056.281Q45819994683.275Q45834628107.275Q48119910507.280Q48119910507.281Q49770149321.275Q50231601566.271Q51604307871.272Q54481541664.270Q5596578838.280 Q5596578838.281 Q57210883017.275Q58653566660.275Q58744150173.274Q58972088541.277Q59617553652.275Q59619599044.275Q59698924043.275Q59705132091.275Q59867425008.280Q59867425008.281Q62639683769.275Q64228675114.279Q64228675114.280Q64681563910.280Q64681563910.281Q6575031993.275 Q67140783850.264Q67837027513.275Q67893080934.268Q6912043747.277 00000400500i00j00k01K02_04304404504W05<05=05>05l05m06706806906:07A08H09^0;40;n0<h0=b0=c0=d0>O0?:0?f0@R0AR0BR0C@0D:0EI0F40G40G_0H[0IU0JO0KW0LQ0M<0NE0ON0P<0Q<0R<0Rg0Rh0TG0Uf0VQ0WK0XE0YL0YM0YN0Z90Zd0[^0\X0\Y0\Z0\[0\\0\]0\^0]I0_N0aS0bj0dA0dl0eW0fB0g>0h8S2LcSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZCSSS4PHIj4CNTj4PHIf1n4PHIa2Lc3PHI1HS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFFS4FFRj4CNTj4FFRf1n1d4FFRa2Lc3FFR1HS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTSSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSSS1R2lo3LOSSFFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB2cs2Lc3SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB2cs2Lc3SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp12cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp12cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCFS1R4STKg4STKs4STKf2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB2cs2Lc3SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB2cs2Lc3SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs2Hn3SLO3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf5STKg02LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp12cs2Lc3SP14SP1M3SZC3ALO3ACV3SPR2F82F02HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf5STKg02LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp12cs2Lc3SP14SP1M3SZC3ALO3ACV3SPR2F82F02HB5Ha_st5Hl_st5SAEstS1R3HIA4STKg4STKs4STKf1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB2cs2Lc3SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA4STKg4STKs4STKf1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB2cs2Lc3SZC2HT2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_97504 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_parse_D24 ()) "PFB,$<.Psp1,$<.PW,(19.$1:.)PPHIa,$<.PFFRa,$<.Pw0,(1;.&40.)Pw1,(1;.&40.)Pw2,(1;.&40.)Pv48,(1;.&40.)Pv80,(1;.&40.)Pg4,(19.(1;.&8.))Pg8,(19.(1;.&8.))Pg12,(19.(1;.&8.))Pg16,(19.(1;.&8.))Pg18,(19.(1;.&8.))Pg22,(19.(1;.&8.))Pj32,(19.(1;.&8.))Palg,(19.(1;.&8.))Pcs,(19.$1<.)Pb0,(1;.&8.)Pb1,(1;.&8.)Pb2,(1;.&8.)Pb3,(1;.&8.)Pb4,(1;.&8.)Pb5,(1;.&8.)Pb6,(1;.&8.)Pb7,(1;.&8.)Pb8,(1;.&8.)Pb9,(1;.&8.)Pb10,(1;.&8.)Pb11,(1;.&8.)Pb12,(1;.&8.)Pb13,(1;.&8.)Pb14,(1;.&8.)Pb15,(1;.&8.)Pb16,(1;.&8.)Pb17,(1;.&8.)Pb18,(1;.&8.)Pb19,(1;.&8.)Pb20,(1;.&8.)Pb21,(1;.&8.)Pb22,(1;.&8.)Pb23,(1;.&8.)Pb24,(1;.&8.)Pb25,(1;.&8.)Pb26,(1;.&8.)Pb27,(1;.&8.)Pb28,(1;.&8.)Pb29,(1;.&8.)Pb30,(1;.&8.)Pb31,(1;.&8.)PLc,(19.$7.)Pmc,P,(1;.&40.)(1=.(1;.&8.))Pmoc,$1>.Phc,(1?.$2.VR,VHIA,)Pst,(1=.(?.$20.$21.))Pr,$<.Pxra,(1;.&40.)Pt0,(1;.&40.)Pt1,(1;.&40.)Pt2,(1;.&40.)Pa0,(1;.&40.)Pa1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pt3,(1;.&40.)Pt4,(1;.&40.)Pt5,(1;.&40.)Pt6,(1;.&40.)Ps2v,(1;.&40.)Ps3v,(1;.&40.)Ps5v,(1;.&40.)Ps6v,(1;.&40.)Ps7v,(1;.&40.)Ps8v,(1;.&40.)Ps9v,(1;.&40.)P,(22.VR,VHIA,VSI,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VA,Vn,Vlo,Vslo,R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R46.R45.R44.R43.R42.R41.A20.Lb0,(1;.&8.)Lb1,(1;.&8.)Lb2,(1;.&8.)Lb3,(1;.&8.)Lb4,(1;.&8.)Lb5,(1;.&8.)Lb6,(1;.&8.)Lb7,(1;.&8.)Lb8,(1;.&8.)Lb9,(1;.&8.)Lb10,(1;.&8.)Lb11,(1;.&8.)Lb12,(1;.&8.)Lb13,(1;.&8.)Lb14,(1;.&8.)Lb15,(1;.&8.)Lb16,(1;.&8.)Lb17,(1;.&8.)Lb18,(1;.&8.)Lb19,(1;.&8.)Lb20,(1;.&8.)Lb21,(1;.&8.)Lb22,(1;.&8.)Lb23,(1;.&8.)Lb24,(1;.&8.)Lb25,(1;.&8.)Lb26,(1;.&8.)Lb27,(1;.&8.)Lb28,(1;.&8.)Lb29,(1;.&8.)Lb30,(1;.&8.)Lb31,(1;.&8.)(10.$1<.(23.R20.)(10.$1<.(23.R1?.)(10.$1<.(23.R1>.)(10.$1<.(23.R1=.)(10.$1<.(23.R1<.)(10.$1<.(23.R1;.)(10.$1<.(23.R1:.)(10.$1<.(23.R19.)(10.$1<.(23.R18.)(10.$1<.(23.R17.)(10.$1<.(23.R16.)(10.$1<.(23.R15.)(10.$1<.(23.R14.)(10.$1<.(23.R13.)(10.$1<.(23.R12.)(10.$1<.(23.R11.)(10.$1<.(23.R10.)(10.$1<.(23.R?.)(10.$1<.(23.R>.)(10.$1<.(23.R=.)(10.$1<.(23.R<.)(10.$1<.(23.R;.)(10.$1<.(23.R:.)(10.$1<.(23.R9.)(10.$1<.(23.R8.)(10.$1<.(23.R7.)(10.$1<.(23.R6.)(10.$1<.(23.R5.)(10.$1<.(23.R4.)(10.$1<.(23.R3.)(10.$1<.(23.R2.)(10.$1<.(23.R1.)(12.$1<.)))))))))))))))))))))))))))))))))R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(2>.&40.VA,)(2>.&40.R50.)R40.R48.R3?.R47.R3>.R1=.R1<.R1;.R1:.)P,(24.R4?.R4>.R4=.R1>.R1=.R1:.)P,(0.(4.(25.(26.+2.+1?.))R1:.)(27.R1:.(26.+2.+1?.)))(28.$2.(29.$2.VR,VHIA,(1=.(?.$20.$21.))(2:.VPK,)VSI,(:.VPHIj,VCNTj,VPHIf,)(;.VFFRj,VCNTj,VFFRf,)(8.VCNTj,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VA,Vn,Vlo,Vslo,Vd,Vm,Vmo0,)(2;.(2<.(2=.R1:.(2>.&40.R52.)Vgp,Vtp,R19.R18.R17.Vsp,(2>.&40.R52.)R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.(2>.&40.R1;.)R8.R7.R6.R5.R4.(2>.&40.(9.(2?.R53.+3.)(30.(31.VR,))))(2>.&40.R53.)R>.R=.R<.R;.)VF,(2>.&40.+974?4.)Vfc,(32.(1;.&40.))R1?.(33.$2.))R1>.))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    pose proof (presW_init_at R HIA hc _ _ (Lc ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    pose proof (conj HHc I) as HHbox. apply rw_cells_blob in CELLS. rewrite SZC in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    try rewrite (sext_small r Hr).
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (REPx : pkcs7_at asegs PK st mx Lc LB A);
      [ eapply (pkcs7_at_presx0 R HIA) with (bs := bs) (slo := slo) (lo := lo) (n := n) (h := h) (A := A) (sp := sp) (hq := hc) (LFq := (FB, 256) :: LF);
        first [ exact REP | exact (proj1 HHbox) | exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2)) | eassumption
              | match goal with |- ?g => idtac "REPX-LEFT:" g end ] |];
      assert (SIx : si_P SI mx);
      [ eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))| intros a _; exact I] |];
      clear SIc REP end.
    assert (TPx : forall mq, pkcs7_at asegs PK st mq Lc LB A -> tailP W PHIa FFRa Lc mq st).
    { intros mq Rq. exact (conj Rq (conj SM (conj CNT (conj PHI (conj FFR (conj HW (conj HWX (conj BUD BUDF)))))))). }
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      eapply (tail_97460 FB sp1 W PHIa FFRa w0 w1 w2 v48 v80 g4 g8 g12 g16 g18 g22 j32 alg _
                b0 b1 b2 b3 b4 b5 b6 b7 _ b9 b10 b11 _ b13 b14 b15 _ b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 Lc _ mo9 hc st r);
        [cbv beta; dvA_build | exact (TPx _ REPx) | exact Hr].
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      eapply (ret_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
        first [ exact HW | exact REPx | eassumption
              | lazymatch goal with
                | |- PHIa <= _ => pose proof (PHIf_mono 0 (Z.of_nat (length Lc)) ltac:(clear; lia)); clear - PHI H; lia
                | |- FFRa <= _ => pose proof (FFRf_mono 0 (Z.of_nat (length Lc)) 0 ltac:(clear; lia)); clear - FFR H; lia
                | |- - 2 ^ 31 <= 2 < 2 ^ 31 => clear; lia
                end
              | dvA_build ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_x509_seq_stmts A_x509_seq_stmtsE A_x509_seq_stmtsE_w A_x509_akid_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_get_san_A A_x509_akid_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02f7efa6dbce44a5 0 3 0 1 33 1 65 1P038321d8257caf53 0 7 0 1 46 1 55 1 60 1 61 1 64 1 65 1P04b6f241726c9d18 1 1 64 2 44 1 64 1 3 0 1 63 1 65 64P056d1578a7fa5245 0 3 0 1 33 1 65 1P05ab35cfc1468593 0 3 0 1 33 1 65 1P0629493319f7b3c7 0 3 0 1 33 1 65 1P09441621b3ba8a4d 0 3 0 1 33 1 65 1P0d5b31814530e4ad 0 3 0 1 33 1 65 1P0e3622c7aadeec6b 0 6 0 1 66 1 67 1 68 1 71 1 72 1P0f9724a0ed1ef94f 0 7 0 1 22 1 66 1 71 1 72 1 75 1 76 1P15c21548b06bc56d 0 3 0 1 33 1 65 1P179e96a26dd9b259 0 6 0 1 66 1 67 1 68 1 71 1 72 1P17b6c7ec09d639e9 0 6 0 1 66 1 67 1 68 1 71 1 72 1P1946d14ea1f5034d 0 6 0 1 54 1 55 1 56 1 59 1 60 1P19b36d4d695be605 0 3 0 1 33 1 65 1P1afe338cc19b112e 0 4 0 1 21 1 75 1 76 1P1c210618be546a6d 1 1 64 2 1 1 63 1 3 0 1 64 1 65 64P213ee2d66a2d10c4 0 6 0 1 66 1 67 1 68 1 71 1 72 1P27800c6d7c9f330c 0 3 0 1 33 1 65 1P29d2690622abcd0e 0 6 0 1 66 1 67 1 68 1 71 1 72 1P2cc5871c67cbcb89 0 6 0 1 66 1 67 1 68 1 71 1 72 1P2dbd12e44196d983 0 6 0 1 66 1 67 1 68 1 71 1 72 1P3071e23bb356afc9 0 3 0 1 33 1 65 1P32d9ff4d0f654323 1 1 64 2 0 1 63 1 3 2 1 64 1 65 64P3330e0c9c2a78e0b 0 3 0 1 33 1 53 1P353be4b04322e5ff 0 6 0 1 66 1 67 1 68 1 71 1 72 1P358f27fa833b91a0 0 3 0 1 33 1 65 1P373dede076cae5aa 0 3 0 1 33 1 65 1P3a82b3c20dfec035 0 6 0 1 66 1 67 1 68 1 71 1 72 1P3cd4356886e8fc1b 0 6 0 1 66 1 67 1 68 1 71 1 72 1P3d31ce0d83a0ce49 0 4 0 1 21 1 75 1 76 1P3e8a12b1ebc6ac4b 0 6 0 1 66 1 67 1 68 1 71 1 72 1P3eca478af5f30dda 0 6 0 1 66 1 67 1 68 1 71 1 72 1N01c9d50081719ba6N0ed800f44c5f06dbN0f9e68ab95bdd485N0fb27d0e5420f5caN182f91d6a64c5182N1b820f89fcc7421fN200d544e41400677N201881a0d70ab440N2b9ef5ad2c33e37bN320e9c972beec597N333f67b9125b38deN34a5a29895a99eb4N3755336887a87540N39636e18c547b7e7N3d085e9a5233c8c6N3d42252992167090N3dcb75b8544d09cdN3e1f43e6e27044b5"%lxh.
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
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0G.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.   (* [comment removed for export] *)
  Variables (PHIe : Z -> Z) (FFRe : Z -> Z -> Z) (CNTe : Z -> Z) (STKe : Z).
  Hypothesis STKe0 : 0 <= STKe.
  Hypothesis SANEXT : seq_parser_stmtE asegs R HIA PHIe FFRe CNTe STKe (LFMAX_CRT + 5) (fun _ => True) (fun r => r = 0) A_X509_SAN_EXT.
  Hypothesis PHIe_mono : forall n n', 0 <= n <= n' -> 0 <= PHIe n <= PHIe n'.
  Hypothesis FFRe_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRe n d <= FFRe n' d.
  Hypothesis CNTe_mono : forall n n', 0 <= n <= n' -> 0 <= CNTe n <= CNTe n'.

  Local Notation STKk := (A_x509_akid_A.STKk R STKe).
  Definition FFRk (n d : Z) : Z := FFRe n (d + 1).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP AK P END BUF lo slo d : Z) (bs : list byte) (ct cpad r1 r2 r3 r4 : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 4)%nat.
  Hypothesis B30 : n < 2^30.
  Hypothesis NDL : List.NoDup (map fst LB).
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALA : AK mod 8 = 0.
  Hypothesis AK0 : 0 < AK.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) AK 80.
  Hypothesis AKLO : AK + 80 <= lo.
  Hypothesis DAB : AK + 80 <= BUF \/ BUF + n <= AK.
  Hypothesis D1 : PP + 8 <= AK \/ AK + 80 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Let LFB' : (length LF < 511)%nat.
  Proof. clear - LFB. unfold LFMAX_CRT in LFB. lia. Qed.
  Let CWA0 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) AK 24.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.
  Let CWHD : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (AK + 24) 32.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.
  Let CWA56 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (AK + 56) 24.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold A_x509_akid_A.STKk in SLO; unfold SEQ_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (AK, AK + 80)].
  Local Notation SAVEL := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation HEADC := (seq_cells ct cpad 0 0 0).
  Local Notation AK56C := [C4 r1; C4 r2; C8 r3; C8 r4].

  Local Notation POST := (x509_akid_postE asegs R HIA PHIe FFRk CNTe h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP AK P END BUF (END - P) lo slo d m mo0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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

  #[local] Ltac lx_pins_hook ::= try lx_pin1 CWA56; try lx_pin1 CWHD; try lx_pin1 CWA0; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 DAB; try lx_pin1 AKLO; try lx_pin1 CWA; try lx_pin1 ALA; try lx_pin1 DPB; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 NDL; try lx_pin1 B30; try lx_pin1 r4; try lx_pin1 r3; try lx_pin1 r2; try lx_pin1 r1; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 d; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 CNTe_mono; try lx_pin1 FFRe_mono; try lx_pin1 PHIe_mono; try lx_pin1 SANEXT; try lx_pin1 CNTe; try lx_pin1 FFRe; try lx_pin1 PHIe; try lx_pin1 DIMG; try lx_pin1 GT; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LFB' LOS SPH TOP SLO SLOL SLOS AK0 PP0 LFB bs AK PP STKe0 STKe NS1 IMG"]
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (LBc : list blk) (m2x mm : mem) (WA WB : list ivl) (FB sp1 : Z)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s9v s10v x28 x29 x30 x31 w0 w1 w2 : word) (r : Z),
    HM asegs R HIA h3 (LBc ++ LB) ((FB, 64) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h -> hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 64 -> fresh_apart R (LBc ++ LB) LF FB 64 -> crange CS FB 64 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHG ->
    rw_cells asegs mm (bv_unsigned sp + -96) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -96) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm ->
    presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm ->
    sshad asegs AL mm slo (bv_unsigned sp) ->
    evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 LBc m2x WA WB r)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s9v s10v s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x0ab6e4) fc None mm (seg_rom asegs)).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE STK2 STlo MI PRES PRES2 SS.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKe0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xab720] [] 266%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 64) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -96 + 96 <= p \/ p + 1 <= bv_unsigned sp + -96).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 STKe0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 STKe0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 STKe0; lia | lx_side_lia ]]).
  clear HHe NCp NSp.
  repeat match goal with H : rw_cells _ me FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
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
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (bv_unsigned sp + -96), SV : rw_cells _ mf (bv_unsigned sp + -96) _ |- _ =>
          pose proof (stk_merge asegs mf lo sp1 _ ST0 STA ltac:(first [ clear - SP1 SLO NS1 STKe0; lia | lx_side_lia ])) as ST3;
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ak_fin : forall (hq : HST asegs R HIA) (nodes : list Z) (FB sp1 : Z) (mm : mem) (r p' : Z) (k1 k2 k3 k4 hct hcpad q1 q2 q3 q4 : word) (hcl hcp : Z) (w0 w1 w2 : word)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s9v s10v x28 x29 x30 x31 : word),
    HM asegs R HIA hq (SSEQ (rev nodes) ++ LB) ((FB, 64) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h -> hstkhi asegs R HIA hq = hstkhi asegs R HIA h -> hflag asegs R HIA hq = hflag asegs R HIA h ->
    havol asegs R HIA hq <= havol asegs R HIA h + PHIe (END - P) -> hfr asegs R HIA hq <= hfr asegs R HIA h + FFRk (END - P) d ->
    Z.of_nat (length nodes) <= CNTe (END - P) ->
    bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 64 -> crange CS FB 64 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHG ->
    rw_cells asegs mm (bv_unsigned sp + -96) SAVEL -> rw_cells asegs mm (sp1 + 24) [C8 (Z_to_bv 64 FB)] ->
    stk asegs mm (sp1 + 32) (bv_unsigned sp + -96) -> stk asegs mm sp1 (sp1 + 24) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA hq LB LF (bv_unsigned sp) (bv_unsigned sp) W m mm ->
    sshad asegs AL mm slo sp1 -> sshad asegs AL mm sp1 (bv_unsigned sp) ->
    rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    rw_cells asegs mm AK [C4 k1; C4 k2; C8 k3; C8 k4] -> rw_cells asegs mm (AK + 24) (seq_cells hct hcpad hcl hcp (hd 0 nodes)) ->
    rw_cells asegs mm (AK + 56) [C4 q1; C4 q2; C8 q3; C8 q4] ->
    ((hcp = 0 /\ hcl = 0 /\ nodes = []) \/ (BUF <= hcp /\ 0 <= hcl /\ hcp + hcl <= END)) ->
    seq_chain asegs (fun _ => True) mm (SSEQ (rev nodes) ++ LB) (hd 0 nodes) nodes ->
    List.NoDup nodes -> (forall x, In x nodes -> forall B k, In (B, k) LB -> x + SEQ_SIZE <= B \/ B + k <= x) ->
    -0x3000 < r <= 0 -> (r = 0 -> p' = END) ->
    aevtA asegs (KF asegs R HIA hq mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s9v s10v s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x0ab6e4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE SLOT SThi STmid STlo MI PRESq SS1 SS2 HPPx Hp' HA0x HHDx HA56x HCB NC ND APN RR HENDq.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq (SSEQ (rev nodes)) LB LF mm FB 64 FRSH HHq) as FRSHq.
    pose proof (presW_init_at R HIA hq _ _ (SSEQ (rev nodes) ++ LB) LF mm (bv_unsigned sp) (bv_unsigned sp) [] hq HHq
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 STKe0; lia)) as PRES2.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 STKe0; lia)) as SSm.
    chunk_to_stk SLOT.
    lazymatch type of SLOT with stk _ _ _ ?hi => replace hi with (sp1 + 32) in SLOT by (clear; lia) end.
    pose proof (stk_merge _ _ _ _ _ STmid SLOT ltac:(clear; lia)) as STK1.
    pose proof (stk_merge _ _ _ _ _ STK1 SThi ltac:(clear - SP1; lia)) as STK2.
    (* [comment removed for export] *)
    replace (AK + 56) with (AK + 24 + 32) in HA56x by (clear; lia).
    pose proof (rw_cells_join3 asegs mm AK _ _ _ HA0x HHDx HA56x) as HAKx.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := SSEQ (rev nodes)) (WA := W) (WB := @nil ivl) (m2x := mm);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact SSm | exact STK2
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29) as HP29.
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' ((SSEQ (rev nodes) ++ LB) ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((SSEQ (rev nodes) ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    unfold x509_akid_postE.
    do 15 eexists. exists m9, mo9, h4, r, p', k1, k2, k3, k4, hct, hcpad, hcl, hcp, (hd 0 nodes), q1, q2, q3, q4, nodes.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES9) as HPF; rewrite ESq in HPF; exact HPF|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact ECNT|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HPPx| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hp'|].
    split; [unfold CrtExtStmts.akid_cells; eapply (presA_rw_cells asegs R); [exact HP29| exact HAKx| cbn [cells_size csize Nat.add length seq_cells app]; apply CRo; [exact AKLO| exact (client_range_of_w L _ _ _ _ _ CWA)]| exact I]|].
    split; [exact HCB|]. split; [reflexivity|].
    split.
    { eapply chain_presx with (L2 := SSEQ (rev nodes) ++ LB) (X := @nil ivl) (SP := bv_unsigned sp);
        [exact NC| | | unfold SEQ_SIZE; clear; lia| intros x Hx; exact I].
      - intros x Hx. apply in_app_iff. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    split; [exact ND|]. split; [exact APN|]. split; [exact HH4|]. exact HENDq.
  Qed.

  (* [comment removed for export] *)
  Lemma exq_fin : forall (FB sp1 : Z) (h1 : HST asegs R HIA) (ms : machine_state),
    A_x509_akid_A.EXQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP AK P END lo slo ct cpad r1 r2 r3 r4 FB sp1 h1 ms ->
    hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA h ->
    hflag asegs R HIA h1 = hflag asegs R HIA h -> havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 64 -> crange CS FB 64 ->
    0 <= PHIe (END - P) -> 0 <= FFRe (END - P) (d + 1) -> 0 <= CNTe (END - P) ->
    aevtA asegs (KF asegs R HIA h1 mo0) POST ms.
  Proof.
    intros FB sp1 h1 ms EQ Ehcs Ehtop Estk Eflag Evol Efr SP1 SP1M F64 FRSH CFB PH0 FF0 CN0.
    destruct EQ as (m2 & r & p' & v0 & v1 & v2 & j1 & j2 & j3 & j4 & xra & u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & s3v & s4v & s5v & s6v & s9v & s10v & u28 & u29 & u30 & u31
                    & -> & Hr & Hp' & HH2 & MI2 & FH2 & FSH2 & SAVE2 & SLOT2 & SThi2 & STmid2 & STlo2 & HPP2 & HA02 & HHD2 & HA562 & PRES & SS12 & SS22 & HEQ).
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m2 PRES HCS1 Estk) as PRES1.
    eapply ak_fin with (hq := h1) (nodes := @nil Z) (p' := p') (hct := ct) (hcpad := cpad) (hcl := 0) (hcp := 0);
      first [ exact HEQ | exact HH2 | exact PRES1 | exact HPP2 | exact HA02 | exact HHD2 | exact HA562 | exact Hp' | exact CFB | exact HCS1 | exact Hr | eassumption | reflexivity
            | lazymatch goal with
              | |- havol _ _ _ _ <= _ => rewrite Evol; clear - PH0; lia
              | |- hfr _ _ _ _ <= _ => rewrite Efr; unfold FFRk; clear - FF0; lia
              | |- Z.of_nat (length _) <= _ => cbn [length Z.of_nat]; clear - CN0; lia
              | |- _ \/ _ => left; repeat split; reflexivity
              | |- seq_chain _ _ _ _ _ _ => apply chain_nil
              | |- List.NoDup [] => constructor
              | |- forall x, In x [] -> _ => intros x []
              end
            | match goal with |- ?g => idtac "EXQ-FIN-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_call : forall (k1 k2 k3 k4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m AK (CrtExtStmts.akid_cells k1 k2 k3 k4 ct cpad 0 0 0 r1 r2 r3 r4) -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m AK 80 ->
    havol asegs R HIA h + PHIe (END - P) <= AVOL_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    hfr asegs R HIA h + FFRk (END - P) d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 AK) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_X509_AKID) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros k1 k2 k3 k4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 HPP HAK HBUF ST SS MI OPP OAK BUD UW BUDF.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof SLO as SLO'.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO' STKe0 NS1 TOP HTOP; lia]).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    pose proof (PHIe_mono 0 (END - P) ltac:(clear - B2; lia)) as PH0.
    pose proof (FFRe_mono 0 (END - P) (d + 1) ltac:(clear - B2; lia)) as FF0.
    pose proof (CNTe_mono 0 (END - P) ltac:(clear - B2; lia)) as CN0.
    (* [comment removed for export] *)
    unfold CrtExtStmts.akid_cells in HAK. destruct (rw_cells_split3 asegs m AK _ _ _ HAK) as (HA0 & HHD & HA56). clear HAK.
    change (AK + Z.of_nat (cells_size [C4 k1; C4 k2; C8 k3; C8 k4])) with (AK + 24) in HHD, HA56.
    change (AK + 24 + Z.of_nat (cells_size (seq_cells ct cpad 0 0 0))) with (AK + 24 + 32) in HA56.
    replace (AK + 24 + 32) with (AK + 56) in HA56 by (clear; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_akid_A.pro_walk with (STKe := STKe) (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact HH | exact HPP | exact HA0 | exact HHD | exact HA56 | exact HBUF | exact ST | exact SS | exact MI | exact OPP | exact OAK | exact OBUF | eassumption
              | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & w0 & w1 & w2 & lenj
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & HLEN & FSH & SAVE & SLOT & SThi & STmid & STlo & MI1
                   & HPP1 & HA01 & HHD1 & HA561 & HB1 & OPP1 & OAK1 & OBUF1 & APP & APC & PRES0 & SS1 & SS2).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 STKe0; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & _ & _).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_akid_A.mid_walk1 with (STKe := STKe) (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (h1 := h1);
        first [ eassumption | match goal with |- ?g => idtac "MID1-PRE-LEFT:" g end ]. }
    clear FHD HLEN FSH SAVE SLOT SThi STmid STlo MI1 HPP1 HA01 HHD1 HA561 HB1 OPP1 OAK1 OBUF1 PRES0 SS1 SS2 HH1. intros ms2 P2.
    destruct P2 as [EQ | MQ].
    { intros mo1 [HK1 MF1].
      apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
      eapply exq_fin with (FB := FB) (sp1 := sp1); first [ exact EQ | exact CFB | eassumption | clear - PH0 FF0 CN0; lia | match goal with |- ?g => idtac "EXQ1-LEFT:" g end ]. }
    destruct MQ as (m2 & q0 & v0 & v1 & v2 & Lw0 & j1 & j2 & j3 & j4 & xra0 & u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31
                    & -> & Hq0 & HH2 & MI2 & FH2 & HLEN2 & FSH2 & SAVE2 & SLOT2 & SThi2 & STmid2 & STlo2 & HPP2 & HA02 & HHD2 & HA562 & HB2 & OPP2 & OAK2 & OBUF2 & PRES2 & SS12 & SS22).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_akid_B.mid_walk2 with (STKe := STKe) (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (h1 := h1) (q := q0);
        first [ eassumption | match goal with |- ?g => idtac "MID2-PRE-LEFT:" g end ]. }
    clear FH2 HLEN2 FSH2 SAVE2 SLOT2 SThi2 STmid2 STlo2 MI2 HPP2 HA02 HHD2 HA562 HB2 OPP2 OAK2 OBUF2 PRES2 SS12 SS22 HH2. intros ms3 P3.
    destruct P3 as [EQ | CQ].
    { intros mo1 [HK1 MF1].
      apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
      eapply exq_fin with (FB := FB) (sp1 := sp1); first [ exact EQ | exact CFB | eassumption | clear - PH0 FF0 CN0; lia | match goal with |- ?g => idtac "EXQ2-LEFT:" g end ]. }
    idtac "CQ".
    (* [comment removed for export] *)
    destruct CQ as (m3 & q & v0' & v1' & v2' & Lw & i1 & i2 & i3 & i4 & xra & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31
                    & -> & Hq & HqE & HH3 & MI3 & FH3 & HLEN3 & FSH3 & SAVE3 & SLOT3 & SThi3 & STmid3 & STlo3 & HPP3 & HA03 & HHD3 & HA563 & HB3 & OPP3 & OAK3 & OBUF3 & PRES & SSlo & SShi).
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    assert (QS : 0 <= q + bv_unsigned Lw - q <= END - P) by (clear - Hq HqE LR; lia).
    pose proof (PHIe_mono _ (END - P) QS) as PHL.
    pose proof (FFRe_mono _ (END - P) (d + 1) QS) as FFL.
    pose proof (CNTe_mono _ (END - P) QS) as CNL.
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
    assert (CWH1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) (AK + 24) 32)
      by (eapply client_wrange_mono; [exact CWHD| intros b Hb; apply fdata_cons_sub; exact Hb]).
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m3 PRES) as HP13.
    assert (UW3 : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply uwc_presA; [exact HP13| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO' SPR NS1 STKe0; lia].
      intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO AKLO SLO' NS1 STKe0; lia. }
    assert (UWF : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { pose proof SAVE3 as SV. chunk_split SV 10%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -96 + 80) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW3| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    clear HP13 UW3.
    assert (OHD3 : aobj asegs AL CS m3 (AK + 24) 32) by (eapply aobj_sub; [exact OAK3| clear; lia| clear; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    (* [comment removed for export] *)
    zstep.
    idtac "SANEXT-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SANEXT with (h := h1) (LB := LB) (LF := (FB, 64) :: LF) (PP := PP) (CUR := AK + 24) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                         (ct := ct) (cpad := cpad);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr; unfold SEQ_SIZE;
        first [ exact HH3 | exact HB3 | exact BIN | exact HPP3 | exact HHD3 | exact OPP3 | exact OHD3 | exact CWP1 | exact CWH1 | exact STlo3 | exact SSlo | exact SLOS | exact SLOL | exact MI3 | exact TPV
              | exact NDL | exact UWF | exact B47 | exact B5 | exact B30 | exact ALP | exact PP0 | exact PPLO | exact DPB | exact I | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                | |- lo <= sp1 - STKe => clear - SLO' SP1 NS1 STKe0; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD PHL; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRk in BUDF; clear - BUDF FFL; lia
                | |- _ mod 8 = 0 => clear - ALA; Z.div_mod_to_equations; lia
                | |- _ \/ _ => clear - DAB D1; lia
                | |- _ => clear - B1 B3 Hq HqE LR AKLO AK0; lia
                end
              | match goal with |- ?g => idtac "SANEXT-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    idtac "SANEXT-POST".
    destruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & h3 & rc & p4 & hct & hcpad & hcl & hcp & hcn & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HHD4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & _).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn.
    replace (ret_pc (Z_to_bv 64 0xab890)) with (Z_to_bv 64 0xab890 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
    rewrite Ehtop in HT3. rewrite Estk in HS3, HP4. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3. unfold SEQ_SIZE in HP4.
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
    (* [comment removed for export] *)
    assert (HP4' : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) W m3 m4).
    { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m4).
    { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [exact P0|].
      eapply presA_weaken; [exact HP4'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia| intros x Hx; exact Hx]. }
    pose proof (presW_hmono R HIA h h3 LB LF _ _ _ m m4 PRESb HCSh3 HS3) as PRES3.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 64 -> cshd R LBq ((FB, 64) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(PP, PP + 8); (AK + 24, AK + 24 + 32)] m3 m4 FB _ CSOK) in FSH3;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(PP, PP + 8); (AK + 24, AK + 24 + 32)] m3 m4 FB _ HP4) in FH3;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - APP APC; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(PP, PP + 8); (AK + 24, AK + 24 + 32)] m3 m4 (FB + 32) _ HP4) in HLEN3;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - APP APC; lia ].
    assert (DJ : forall A k, sp1 <= A -> disjoint_from [(PP, PP + 8); (AK + 24, AK + 24 + 32)] A k).
    { intros A k HA. cbn [disjoint_from]. clear - HA PPLO AKLO SLO' NS1 STKe0 SP1. lia. }
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SAVE3; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SLOT3; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SThi3; [| clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in STmid3; [| clear; lia| apply DJ; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SShi; [| clear; lia| clear - HTOP TOP; lia].
    assert (SUBf : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
    assert (CRl : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (LB ++ fdata ((FB, 64) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBf]. }
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in HA03;
      [| cbn [cells_size csize Nat.add]; apply CRl; [clear - AKLO; lia| exact (client_range_of_w L _ _ _ _ _ CWA0)]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - D1; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in HA563;
      [| cbn [cells_size csize Nat.add]; apply CRl; [clear - AKLO; lia| exact (client_range_of_w L _ _ _ _ _ CWA56)]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - D1; lia ].
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (OPP4 : aobj asegs AL (hcs asegs R HIA h3) m4 PP 8).
    { eapply aobj_cs_mono; [exact HCSh3|]. eapply (presA_aobj asegs R); [exact CSOK| exact HP4| exact OPP3| apply CRl; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear; lia| exact TOPCS]. }
    assert (OAK4 : aobj asegs AL (hcs asegs R HIA h3) m4 AK 80).
    { eapply aobj_cs_mono; [exact HCSh3|]. eapply (presA_aobj asegs R); [exact CSOK| exact HP4| exact OAK3| apply CRl; [exact AKLO| exact (client_range_of_w L _ _ _ _ _ CWA)]| clear; lia| exact TOPCS]. }
    assert (BIN3 : In (BUF, n) (SSEQ (rev nodes) ++ LB)) by (apply in_app_iff; right; exact BIN).
    pose proof (hm_aobj_block asegs R HIA h3 _ _ m4 BUF n HH4 BIN3) as OBUF4.
    assert (HB4 : bytes_at asegs m4 BUF bs).
    { eapply (presA_bytes_at asegs R); [exact HP4| exact HB3| eapply client_range_block; [apply in_app_iff; left; exact BIN| clear; lia| clear; lia]|].
      cbn [disjoint_from]. clear - DPB DAB. lia. }
    pose proof (fresh_apart_grow R HIA h3 (SSEQ (rev nodes)) LB LF m4 FB 64 FRSH HH4) as FRSH3.
    clear HP4 HP4' DJ OPP3 OAK3 OBUF3 OHD3 HB3 MI3 STlo3 SSlo PRES HH3 HPP3 HHD3 PRESb CRl.
    idtac "TRANSPORTED".
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply A_x509_akid_B.post_walk with (STKe := STKe) (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (h3 := h3) (LBc := SSEQ (rev nodes)) (rc := rc) (p4 := p4)
                                          (hct := hct) (hcpad := hcpad) (hcl := hcl) (hcp := hcp) (hcn := hd 0 nodes);
        first [ exact HH4 | exact HCSh3 | exact HT3 | exact HS3 | exact FRSH | exact FRSH3 | exact CFB | exact Hr3 | exact PRES3 | exact HPP4 | exact HHD4 | exact HA03 | exact HA563
              | exact OPP4 | exact OAK4 | exact OBUF4 | exact HB4 | exact ST4 | exact SS4 | exact MI4 | eassumption
              | lazymatch goal with |- P <= p4 <= END => clear - Hp4 Hq HqE; lia end
              | match goal with |- ?g => idtac "POST-PRE-LEFT:" g end ]. }
    idtac "POST-WALKED".
    cbv beta. intros ms5 X3.
    destruct X3 as (m5 & r5 & p5 & f0 & f1 & f2 & g1 & g2 & g3 & g4 & e1 & e2 & e3 & e4
                    & yra & c5 & c6 & c7 & c11 & c12 & c13 & c14 & c15 & c16 & c17 & d3v & d4v & d5v & d6v & d9v & d10v & c28 & c29 & c30 & c31
                    & -> & Hr5 & Hp5 & HH5 & MI5 & FH5 & FSH5 & SAVE5 & SLOT5 & SThi5 & STmid5 & STlo5 & HPP5 & HA05 & HHD5 & HA565 & PRES5 & PRES25 & SS15 & SS25 & HEQ5).
    (* [comment removed for export] *)
    assert (NC5 : seq_chain asegs (fun _ => True) m5 (SSEQ (rev nodes) ++ LB) (hd 0 nodes) nodes).
    { pose proof (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES25) as HP25.
      eapply chain_presx with (L2 := SSEQ (rev nodes) ++ LB) (X := W) (SP := bv_unsigned sp);
        [exact NC4| | | unfold SEQ_SIZE; clear; lia| ].
      - intros x Hx. apply in_app_iff. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP25)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
      - intros x Hx.
        assert (XIN : In (x, 32) (SSEQ (rev nodes))) by (unfold SSEQ; apply (in_map (fun a => (a, SEQ_SIZE))); apply -> in_rev; exact Hx).
        pose proof (obj_apart_new R HIA h3 (SSEQ (rev nodes)) LB LF ((FB, 64) :: LF) m4 lo (htop asegs R HIA h) PP 8 x 32 DIMG HH4 ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) XIN ltac:(clear; lia)) as AP1.
        pose proof (obj_apart_new R HIA h3 (SSEQ (rev nodes)) LB LF ((FB, 64) :: LF) m4 lo (htop asegs R HIA h) AK 80 x 32 DIMG HH4 ltac:(intros fb Hfb; right; exact Hfb) CWA ltac:(clear - ALO LOS; lia) ltac:(clear; lia) XIN ltac:(clear; lia)) as AP2.
        cbn [disjoint_from]. unfold SEQ_SIZE. clear - AP1 AP2. lia. }
    idtac "CHAIN".
    eapply ak_fin with (hq := h3) (nodes := nodes) (r := r5) (p' := p5) (hct := hct) (hcpad := hcpad) (hcl := hcl) (hcp := hcp);
      first [ exact HEQ5 | exact HH5 | exact HCSh3 | exact HT3 | exact HS3 | exact HF3 | exact PRES5 | exact CFB | exact HPP5 | exact HA05 | exact HHD5 | exact HA565 | exact NC5 | exact ND4 | exact APN4 | exact Hr5 | exact Hp5
            | eassumption | reflexivity
            | lazymatch goal with
              | |- havol _ _ _ _ <= _ => clear - HV3 PHL; lia
              | |- hfr _ _ _ _ <= _ => unfold FFRk; clear - HFR3 FFL; lia
              | |- Z.of_nat (length _) <= _ => clear - HCNT3 CNL; lia
              | |- _ \/ _ => clear - HCB4 HqE; destruct HCB4 as [HC|HC]; [left; exact HC| right; lia]
              end
            | match goal with |- ?g => idtac "FIN-B-PRE-LEFT:" g end ].
  Qed.
  End Call.

  Theorem A_x509_akid_specE : x509_akid_stmtE asegs R HIA PHIe FFRk CNTe STKk (LFMAX_CRT + 4) A_X509_AKID.
  Proof.
    unfold x509_akid_stmtE. intros until r4. intros; subst.
    eapply main_call with (bs := bs) (ct := ct) (cpad := cpad) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4); first [eassumption | reflexivity].
  Qed.
  Theorem A_x509_akid_spec : x509_akid_stmtA asegs R HIA PHIe FFRk CNTe STKk (LFMAX_CRT + 4) A_X509_AKID.
  Proof. exact (x509_akid_stmtE_A _ _ _ _ _ _ _ _ _ A_x509_akid_specE). Qed.
End Walk.

(* [comment removed for export] *)

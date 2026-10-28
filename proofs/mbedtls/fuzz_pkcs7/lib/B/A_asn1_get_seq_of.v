(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_seq_cb A_x509_seq_stmts A_x509_seq_stmtsE A_x509_seq_stmtsE_w A_asn1_trav.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A A_asn1_get_seq_of_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P04038dd8416e80f3 0 3 0 1 33 1 65 1P0549685597508dd4 0 3 0 1 33 1 65 1P0661f26de3b34098 0 8 0 1 46 1 55 1 60 1 61 1 62 1 65 1 66 1P0760806393f3bfc1 0 3 0 1 33 1 65 1P09c5625c46bbe08d 0 3 0 1 33 1 65 1P112f041861cdabea 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P1238d8c26736bf83 0 4 0 1 21 1 76 1 77 1P1522ac577cafa333 1 1 64 2 1 1 64 1 3 0 1 65 1 66 64P161b2556aeabb1e2 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P191244b358b2f903 0 3 0 1 33 1 53 1P195f5a812378e705 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P19d5e49b705727dd 0 3 0 1 33 1 65 1P1cc4f390c4ae1a7e 0 3 0 1 33 1 65 1P1e276c0fe7e732ad 0 3 0 1 33 1 65 1P1ef3d073b50d5666 0 4 0 1 21 1 76 1 77 1P21c353a9989a9186 0 3 0 1 33 1 65 1P222a5ac274206b41 1 1 64 2 44 1 65 1 3 0 1 64 1 66 64P22617d7c4b34346e 0 3 0 1 33 1 65 1P26e01d4675bd0321 0 3 0 1 33 1 65 1P2c09e4eaf1bc24b1 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P2da2f936205a9850 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P308416b393d15fb3 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P3149b0445e04b285 0 7 0 1 54 1 55 1 56 1 59 1 60 1 61 1P31ea354d7736a94c 0 3 0 1 33 1 65 1P32e009d1e5e0a812 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P33b955e718829567 1 1 64 2 0 1 64 1 3 2 1 65 1 66 64P33e3f54163a3de1c 0 8 0 1 22 1 66 1 71 1 72 1 73 1 76 1 77 1P340a3c9e19bfe440 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P37fa283df9e4fbc1 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P38aaadae0e1735dc 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1P3d7e5bcf83046432 0 7 0 1 66 1 67 1 68 1 71 1 72 1 73 1N056ea7e8ea88d078N06484932a91cb92aN0b5b68380c572508N0e027452d367e62cN1c261826ba8c033fN278a7b71da4e8308N28d8208a7c73fde9N2ce5bf951805b33aN30e11b1ae14ffe30N31daa9852c86190dN3338df24e2aeb3fcN35b33172b5e1be4fN369158c5eecd9c78N36fee2bad380ce57N38fbb36e4fd246d5N3bf46dd17d338166N3ea7d286d93a089b"%lxh.
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
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.

  Hypothesis TRAV : asn1_trav_stmtA asegs R HIA A_ASN1_TRAV.
  Local Notation STKq := (A_asn1_get_seq_of_A.STKq R).
  Definition FFRq (n d : Z) : Z := TRAV_FFR n.
  Definition CNTq (n : Z) : Z := n / 2.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 4)%nat.
  Hypothesis NDL : List.NoDup (map fst LB).
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKq.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Let LFB' : (length LF < 511)%nat.
  Proof. clear - LFB. unfold LFMAX_CRT in LFB. lia. Qed.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold A_asn1_get_seq_of_A.STKq, TRAV_STK in SLO; unfold SEQ_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHQ := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation ZHEAD := (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0).


  Local Notation POST := (seq_parser_postE asegs R HIA TRAV_PHI FFRq CNTq (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF (END - P) lo slo d m mo0).

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

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 DCB; try lx_pin1 CURLO; try lx_pin1 CWC; try lx_pin1 ALC; try lx_pin1 DPB; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 NDL; try lx_pin1 d; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 TRAV; try lx_pin1 AMS; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LFB' LOS SPH TOP SLO SLOL SLOS CUR0 PP0 LFB bs CUR PP NEED0 NA1 NS1 IMG"]
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (LBc : list blk) (m2x mm : mem) (WA WB : list ivl) (FB sp1 : Z)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v x28 x29 x30 x31 w0 w1 w2 : word) (r : Z),
    HM asegs R HIA h3 (LBc ++ LB) ((FB, 64) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h -> hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 64 -> fresh_apart R (LBc ++ LB) LF FB 64 -> crange CS FB 64 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHQ ->
    rw_cells asegs mm (bv_unsigned sp + -88) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -88) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm ->
    presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm ->
    sshad asegs AL mm slo (bv_unsigned sp) ->
    evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 LBc m2x WA WB r)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x09a7a4) fc None mm (seg_rom asegs)).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE STK2 STlo MI PRES PRES2 SS.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NEED0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 NA1 NEED0 TOP HTOP3; lia | lx_side_lia ]]).
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
  lx_pre. lx_run_tac (PLAN [0x9a7e4] [] 144%N). lx_tree.
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
  assert (NP5 : bv_unsigned sp + -88 + 88 <= p \/ p + 1 <= bv_unsigned sp + -88).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 NA1 NEED0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 NA1 NEED0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 NA1 NEED0; lia | lx_side_lia ]]).
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
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (bv_unsigned sp + -88), SV : rw_cells _ mf (bv_unsigned sp + -88) _ |- _ =>
          pose proof (stk_merge asegs mf lo sp1 _ ST0 STA ltac:(first [ clear - SP1 SLO NS1 NA1 NEED0; lia | lx_side_lia ])) as ST3;
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
  Lemma gq_fin : forall (hq : HST asegs R HIA) (nodes : list Z) (FB sp1 : Z) (m2x mm : mem) (r p' : Z) (hct hcpad : word) (hcl hcp : Z) (w0 w1 w2 : word)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v x28 x29 x30 x31 : word),
    HM asegs R HIA hq (SSEQ (rev nodes) ++ LB) ((FB, 64) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h -> hstkhi asegs R HIA hq = hstkhi asegs R HIA h -> hflag asegs R HIA hq = hflag asegs R HIA h ->
    havol asegs R HIA hq <= havol asegs R HIA h + TRAV_PHI (END - P) -> hfr asegs R HIA hq <= hfr asegs R HIA h + FFRq (END - P) d ->
    Z.of_nat (length nodes) <= CNTq (END - P) ->
    bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 64 -> crange CS FB 64 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHQ ->
    rw_cells asegs mm (bv_unsigned sp + -88) SAVEL -> rw_cells asegs mm sp1 [C8 (Z_to_bv 64 FB)] ->
    stk asegs mm (sp1 + 8) (bv_unsigned sp + -88) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m mm ->
    presW asegs R HIA hq (SSEQ (rev nodes) ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) [] m2x mm ->
    sshad asegs AL mm slo sp1 -> sshad asegs AL mm sp1 (bv_unsigned sp) ->
    rw_cells asegs m2x PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    rw_cells asegs m2x CUR (seq_cells hct hcpad hcl hcp (hd 0 nodes)) ->
    ((hcp = 0 /\ hcl = 0 /\ nodes = []) \/ (BUF <= hcp /\ 0 <= hcl /\ hcp + hcl <= END)) ->
    seq_chain asegs (fun _ => True) m2x (SSEQ (rev nodes) ++ LB) (hd 0 nodes) nodes ->
    List.NoDup nodes -> (forall x, In x nodes -> forall B k, In (B, k) LB -> x + SEQ_SIZE <= B \/ B + k <= x) ->
    -0x3000 < r <= 0 -> (r = 0 -> p' = END) ->
    aevtA asegs (KF asegs R HIA hq mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x09a7a4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE SLOT SThi STlo MI PRES PRES2 SS1 SS2 HPPx Hp' HCURx HCB NC ND APN RR HENDq.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq (SSEQ (rev nodes)) LB LF mm FB 64 FRSH HHq) as FRSHq.
    pose proof (presW_hmono R HIA h hq LB LF _ _ _ m mm PRES HCSq ESq) as PRESq.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 NA1 NEED0; lia)) as SSm.
    chunk_to_stk SLOT.
    lazymatch type of SLOT with stk _ _ _ ?hi => replace hi with (sp1 + 8) in SLOT by (clear; lia) end.
    pose proof (stk_merge _ _ _ _ _ SLOT SThi ltac:(clear - SP1; lia)) as STK2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := SSEQ (rev nodes)) (WA := W) (WB := @nil ivl) (m2x := m2x);
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
    unfold seq_parser_postE.
    do 15 eexists. exists m9, mo9, h4, r, p', hct, hcpad, hcl, hcp, (hd 0 nodes), nodes.
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
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HCURx| cbn [cells_size csize Nat.add length seq_cells]; apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]|].
    split; [exact HCB|]. split; [reflexivity|].
    split.
    { eapply chain_presx with (L2 := SSEQ (rev nodes) ++ LB) (X := @nil ivl) (SP := bv_unsigned sp);
        [exact NC| | | unfold SEQ_SIZE; clear; lia| intros x Hx; exact I].
      - intros x Hx. apply in_app_iff. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    split; [exact ND|]. split; [exact APN|]. split; [exact HH4|]. exact HENDq.
  Qed.

  #[using="CUR LF LFB LFB' PP R bs sp"] Lemma aobj_of_sshad_q : forall (CSx : Z -> Prop) mX slo' shi B (k : nat),
    cs_ok AL CSx -> sshad asegs AL mX slo' shi -> slo' <= B -> B + 8 * Z.of_nat (S k) <= shi -> B mod 8 = 0 -> 0 <= B ->
    crange CSx B (8 * Z.of_nat (S k)) -> aobj asegs AL CSx mX B (8 * Z.of_nat (S k)).
  Proof.
    intros CSx mX slo' shi B k OK SS H1 H2 HB H0 HC.
    pose proof (sshad_chunk asegs AL mX slo' shi k B SS H1 H2 HB) as SH.
    match type of SH with rw_cells _ _ ?x _ =>
      replace x with (Z.shiftr B 3 + al_sb AL) in SH by (unfold OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
    eapply (aobj_of_zero_shadow_sh asegs AL CSx mX B (zcells (S k)) B 0 (S k) OK SH HC HB H0 ltac:(lia)).
    intros i Hi. apply cell_at_zcells. exact Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_call : forall (ct cpad t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m CUR (seq_cells ct cpad 0 0 0) -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m CUR 32 ->
    havol asegs R HIA h + TRAV_PHI (END - P) <= AVOL_MAX ->
    hfr asegs R HIA h + FFRq (END - P) d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 CUR) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_ASN1_GET_SEQ_OF) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros until t6. intros HH HK0 HPP HCUR HBUF ST SS MI OPP OCUR BUD BUDF.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof SLO as SLO'.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_asn1_get_seq_of_A.pro_walk with (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (ct := ct) (cpad := cpad);
        first [ exact HH | exact HPP | exact HCUR | exact HBUF | exact ST | exact SS | exact MI | exact OPP | exact OCUR | exact OBUF | eassumption
              | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m3 & y5 & y6 & y7 & a3v & y28 & y29 & y30 & y31 & w0 & w1 & w2 & tagw
                   & -> & SP1 & SP1M & HH3 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FH3 & HCTX3 & FSH3 & SAVE3 & SLOT3 & SThi3 & STlo3 & MI3
                   & HPP3 & HCUR3 & HB3 & OPP3 & OCUR3 & APP & APC & PRES & SSlo & SShi).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 NA1 NEED0; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH3 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & _ & _).
    assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
    assert (CWC1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) CUR 32)
      by (eapply client_wrange_mono; [exact CWC| intros b Hb; apply fdata_cons_sub; exact Hb]).
    assert (CWX1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) (FB + 32 + 8) 8)
      by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    frame_aobj FSH3 (FB + 40) 1%nat as OCTX.
    replace (FB + 40) with (FB + 32 + 8) in OCTX by (clear; lia).
    pose proof HCTX3 as HCX. chunk_split HCX 2%nat HCXa HCXb. clear HCXa.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    (* [comment removed for export] *)
    zstep.
    idtac "TRAV-CALL".
    assert (OTS : aobj asegs AL (hcs asegs R HIA h) m3 (sp1 - 112) 8).
    { apply (aobj_of_sshad_q (hcs asegs R HIA h) m3 slo sp1 (sp1 - 112) 0 CSOK SSlo);
        [clear - SP1 SLOL SLO' NS1 NA1 NEED0; lia| clear; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1 SLOL SLO' LOS ALO ACP NS1 NA1 NEED0; lia|].
      eapply crange_sub; [exact SCS0| clear - SP1 SLO' LOS NS1 NA1 NEED0; lia| clear - SP1 TOP HTOP; lia]. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      pose proof TRAV as SPT. unfold asn1_trav_stmtA in SPT.
      eapply SPT with (h := h1) (LB := LB) (LF := (FB, 64) :: LF) (PP := PP) (CTX := FB + 32) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (bs := bs) (lo := lo)
                      (ct := Z_to_bv 64 0) (cpad := Z_to_bv 64 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr;
        first [ exact HH3 | exact HB3 | exact BIN | exact HPP3 | exact HCUR3 | exact HCXb | exact OPP3 | exact OCUR3 | exact OCTX | exact OTS | exact CWP1 | exact CWC1 | exact CWX1 | exact STlo3 | exact LOS | exact MI3 | exact TPV
              | exact B47 | exact B5 | exact B1 | exact B2 | exact B3 | exact ALP | exact PP0 | exact PPLO | exact DPB | exact ALC | exact CUR0 | exact CURLO | exact DCB | exact D1 | exact BUD | exact BUDF | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- lo <= sp1 - TRAV_STK R => unfold TRAV_STK; clear - SLO' SP1 NS1 NA1 NEED0; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- _ mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- _ \/ _ => clear - APP APC APB; lia
                | |- _ => clear - F0 F1 ALO; lia
                end
              | match goal with |- ?g => idtac "TRAV-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    idtac "TRAV-POST".
    destruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo4' & h3 & r3 & p4 & hct & hcpad & hcl & hcp & hcn & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HCUR4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & HENDt).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn.
    replace (ret_pc (Z_to_bv 64 0x9a7a4)) with (Z_to_bv 64 0x9a7a4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, HP4 by exact SP1R.
    rewrite Ehtop in HT3. rewrite Estk in HS3, HP4. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3.
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
    (* [comment removed for export] *)
    assert (HP4' : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) W m3 m4).
    { assert (HPa : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) ((FB + 32 + 8, FB + 32 + 16) :: W) m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
      eapply (presA_drop_fresh_gen R LB LF _ _ _ W FB 64 (FB + 32 + 8) (FB + 32 + 16)); [exact HPa| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO' SP1 NS1 NA1 NEED0; lia]. }
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m4).
    { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [exact P0|].
      eapply presA_weaken; [exact HP4'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - LOS SLO' NS1 NA1 NEED0; lia| clear; lia| intros x Hx; exact Hx]. }
    pose proof (presW_init_at R HIA h3 _ _ (SSEQ (rev nodes) ++ LB) LF m4 (bv_unsigned sp) (bv_unsigned sp) [] h HH4
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSh3 HS3 ltac:(clear - LOS SLO' NS1 NA1 NEED0; lia)) as PRES2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 64 -> cshd R LBq ((FB, 64) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(PP, PP + 8); (CUR, CUR + 32); (FB + 32 + 8, FB + 32 + 16)] m3 m4 FB _ CSOK) in FSH3;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(PP, PP + 8); (CUR, CUR + 32); (FB + 32 + 8, FB + 32 + 16)] m3 m4 FB _ HP4) in FH3;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - APP APC; lia ].
    assert (DJ : forall A k, sp1 <= A -> disjoint_from [(PP, PP + 8); (CUR, CUR + 32); (FB + 32 + 8, FB + 32 + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. clear - HA PPLO CURLO FBLO SLO' NS1 NA1 NEED0 SP1. lia. }
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SAVE3; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SLOT3; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SThi3; [| clear; lia| apply DJ; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SShi; [| clear - LOS SLO' SP1 NS1 NA1 NEED0; lia| clear - HTOP TOP; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SSlo; [| exact SLOS| clear - HTOP TOP SP1; lia].
    clear HP4 HP4' DJ OPP3 OCUR3 HB3 MI3 STlo3 PRES HH3 HPP3 HCUR3 HCTX3 HCXb OCTX.
    idtac "TRANSPORTED".
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    eapply gq_fin with (hq := h3) (nodes := nodes) (m2x := m4) (r := r3) (p' := p4) (hct := hct) (hcpad := hcpad) (hcl := hcl) (hcp := hcp);
      first [ exact HH4 | exact HCSh3 | exact HT3 | exact HS3 | exact HF3 | exact PRESb | exact PRES2 | exact CFB | exact HPP4 | exact HCUR4 | exact HCB4 | exact NC4 | exact ND4 | exact APN4 | exact Hr3 | exact Hp4
            | exact HV3 | exact HCNT3 | exact HFR3 | exact HENDt | eassumption | reflexivity
            | match goal with |- ?g => idtac "FIN-PRE-LEFT:" g end ].
  Qed.
  End Call.

  (* [comment removed for export] *)
  Theorem A_asn1_get_seq_of_specE : seq_parser_stmtE asegs R HIA TRAV_PHI FFRq CNTq STKq (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0) A_ASN1_GET_SEQ_OF.
  Proof.
    unfold seq_parser_stmtE. intros until cpad. intros; subst. eapply main_call with (bs := bs) (ct := ct) (cpad := cpad); first [eassumption | reflexivity].
  Qed.
  Theorem A_asn1_get_seq_of_spec : seq_parser_stmtA asegs R HIA TRAV_PHI FFRq CNTq STKq (LFMAX_CRT + 4) (fun _ => True) A_ASN1_GET_SEQ_OF.
  Proof. exact (seq_parser_stmtE_A _ _ _ _ _ _ _ _ _ _ _ A_asn1_get_seq_of_specE). Qed.
End Walk.

(* [comment removed for export] *)

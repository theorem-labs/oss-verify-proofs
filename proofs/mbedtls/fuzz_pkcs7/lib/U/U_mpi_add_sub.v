(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_cmp_abs U_mpi_sub_abs U_mpi_add_abs_W U_mpi_add_abs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_add_sub () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sgn"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Main.as_frame"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Main.Body.after"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.USpec.MpiOpnd.opnd_at"; "Main.Body.at1"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.add_sub_mpi_R"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"].


Local Ltac cond_decide :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  repeat match goal with
    | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
    | |- context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
    | |- context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
    | |- context [Z.b2z ?b] => progress cbn [Z.b2z]
    | |- context [negb ?b] => progress cbn [negb]
  end; reflexivity.
Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in assert (E : c = false) by cond_decide; rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_zero_any :=
  repeat match goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  end.
Local Ltac if_vm :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv_concl_iota
  end.
Local Ltac bv_eqz := first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24059859474.3000009S2d12d21D". (* [comment removed for export] *)
Lemma mpd_sep_sym : forall d1 d2, mpd_sep d1 d2 -> mpd_sep d2 d1.
Proof. intros d1 d2 [E|D]; [left; symmetry; exact E| right; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Definition U_ADD_SUB_MPI' : Z := 0x20a04.

(* [comment removed for export] *)
Section Main.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Variable MSF : Z.
  Hypothesis HADD : mpi_add_abs_stmt' usegs L HI U_MPI_ADD_ABS MSF.
  Hypothesis HSUB : mpi_sub_abs_stmt' usegs L HI U_MPI_SUB_ABS MSF.

  (* [comment removed for export] *)
  Definition as_frame (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (lo : Z) (flip : Z)
              (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
              (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own)
              (Ba sB nB pB : Z) (zs : list word) (padB : word) (ownB : limb_own).
    Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
    Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
    Local Notation dB := (mkMPD Ba sB nB pB zs padB ownB).
    Hypothesis FLIP : flip = 1 \/ flip = -1.
    Hypothesis HH : HEAP usegs L HI h LB m mo.
    Hypothesis MX : mpd_at usegs m LB dX.
    Hypothesis MA : mpd_at usegs m LB dA.
    Hypothesis MB : opnd_at usegs m LB (bv_unsigned sp) dB.
    Hypothesis SXA : mpd_sep dX dA.
    Hypothesis SXB : mpd_sep dX dB.
    Hypothesis SAB : mpd_sep dA dB.
    Hypothesis NST : ownX <> LStatic.
    Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
    Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
    Hypothesis CRA : client_range L LB lo Aa 16.
    Hypothesis CRAL : ownA = LHeap -> client_range L LB lo pA (4 * nA).
    Hypothesis CRB : client_range L LB lo Ba 16.
    Hypothesis CRBL : ownB = LHeap -> client_range L LB lo pB (4 * nB).
    Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
    Hypothesis XLS : ownX <> LNull -> pX + 4 * nX <= lo \/ bv_unsigned sp <= pX.
    Hypothesis SLO : lo <= bv_unsigned sp - 224 - hl_stack L.
    Hypothesis ACL : alloc_ceiling <= lo.
    Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis SPA : bv_unsigned sp mod 16 = 0.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SOK : statics_ok usegs L m.
    Hypothesis CA : const_at L MSF 8.
    Hypothesis MI0 : mem_inv usegs m.
    Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).

    Let POST := mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (add_sub_mpi_R flip LB dX dA dB) lo m mo.
    Let VAL := mpd_val dA + flip * mpd_val dB.

    (* [comment removed for export] *)
    Definition after (m1 m' : mem) (mo' : Model) (h' : HST usegs L HI) (LB' : list blk) (dX' : mpd) : Prop :=
      mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp - 48) /\ mo_frame mo mo' /\ heap_top usegs L HI h' = heap_top usegs L HI h /\
      HEAP usegs L HI h' LB' m' mo' /\ mpd_at usegs m' LB' dX' /\ mpd_out LB dX LB' dX' /\
      heap_presx usegs L LB (bv_unsigned sp - 48) (mpd_ivs dX) m1 m' /\ statics_ok usegs L m' /\ binop_keep LB dX dX' /\
      rw_cells usegs m' (bv_unsigned sp - 48) (as_frame ra s0 s1 s2 s3 s4) /\
      munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono usegs m m1.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L22219771718.1 L26825553190.4 L32436940338.1 L38948636245.0 L39409930731.3 L41560720338.7 L46602796124.7 L48076008077.6 L52437843788.6 L54398102733.9 L59314873579.11L59656785403.11L59696753857.1 L774765788.5   00000400?00C00D00L00]01301H01[02502R02l03003AS2spS1X2n'2p'1HS2spSS1X1a2NOS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo1X3SLO2XSS1L3HLS2sp2lo3SLO3ACLS1X2nX2pX4ownX1a2HoS1L2HI3HLS2sp1h2lo3SLO1a1CS1X2nX2pX1a3Ha'1q1k1R2E12E21HS1L2HI3HLS2sp1h2lo3SLO1a1CS2spS1L3HLS2sp2lo3SLO". (* [comment removed for export] *)
    Lemma as_FIN : forall (t0 t1 t2 raj x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (m1 m' : mem) (mo' : Model)
        (h' : HST usegs L HI) (LB' : list blk) (dX' : mpd) (w sg : Z),
      after m1 m' mo' h' LB' dX' -> x20 = Z_to_bv 64 w -> w mod 2 ^ 16 = sg mod 2 ^ 16 -> (sg = 1 \/ sg = -1) ->
      sg * mpd_abs dX' = VAL ->
      aevtM usegs mo' POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 X) x9 a0 a1 a2 a3 a4 a5 a6 a7
        x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133744) fc None m' (seg_rom usegs)).
    Proof.
      intros until sg. intros AF -> WS SG HV.
      ddestruct AF as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & BK2 & FR2 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      ddestruct XW as (XCW & XDW & XP). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in XCW, XDW, XP.
      pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
      destruct dX' as [X' sg' n' p' xs' pad' own']. ddestruct BK2 as (EA & EP & FRS & NMO). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in EA, EP, NMO. subst X' pad'.
      pose proof MX2 as [(CX2 & XAL & X0 & LEN2 & NR2 & OWN2) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      dpose OUT2 as (_ & NS2 & O3 & O4 & O5). cbn [md_addr md_own] in NS2.
      pose proof (conj HH2 I) as HH2c. clear HH2. pose proof (conj SOK2 I) as SOK2c. clear SOK2. pose proof (conj FR2 I) as FR2c. clear FR2.
      pose proof (munch_refl [(X, X + 16)] m') as MU. pose proof (wmono_refl usegs m') as WM.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m'' end.
      (* [comment removed for export] *)
      match goal with CX : rw_cells usegs m'' X [C8 _; C2 (Z_to_bv 64 ?v); _; _] |- _ =>
        pose proof (rw_cells_C2_congr usegs m'' X [C8 (Z_to_bv 64 p')] v sg [C2 (Z_to_bv 64 n'); C4 padX] CX) as CX3 end.
      cbn [app] in CX3.
      match goal with MI3 : mem_inv usegs m'' |- _ => rename MI3 into MIq end.
      destruct HH2c as [HH2 _]. destruct SOK2c as [SOK2 _]. destruct FR2c as [FR2 _].
      assert (FR3 : rw_cells usegs m'' (bv_unsigned sp - 48) (as_frame ra s0 s1 s2 s3 s4)).
      { eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. unfold as_frame. cbn. clear - XS SLO HLS. lia. }
      unfold as_frame in FR3.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      zstep.
      apply aevtM_done. unfold POST, mpi_binop_post. deexists 14. dexists m'', mo', h', LB', (mkMPD X sg n' p' xs' padX own'), 0.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [reflexivity|]. split; [exact MIq|].
      split; [eapply stk_release in FR3; [| exact ST2| clear - SLO HLS ACL ACP; lia];
              cbn [cells_size csize Nat.add] in FR3; replace (bv_unsigned sp - 48 + Z.of_nat 48) with (bv_unsigned sp) in FR3 by (clear; lia); exact FR3|].
      split; [exact MF2|]. split; [exact HT2|].
      split. { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact MU| exact WM| exact ACL|].
               intros a Ha NO. cbn in NO. rewrite HT2. assert (Ha' : X <= a < X + 16) by (clear - NO; lia).
               destruct (XCW a Ha') as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO HLS; lia| right; left; exact C| right; right].
               exists (q, k). split; [| exact R]. apply O4; [exact Hq|]. cbn in R. unfold mpd_blk; cbn [md_own md_p md_n].
               destruct ownX; try (intros []; fail). intros [E|[]]. injection E as E1 E2. pose proof (XP eq_refl). clear - H Ha' R E1 E2. lia. }
      split. { split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [apply CX3; rewrite WS; reflexivity|].
               split; [exact XAL|]. split; [exact X0|]. split; [exact LEN2|]. split; [exact NR2|].
               destruct own'; [exact OWN2| | exfalso; exact (NS2 eq_refl)]. ddestruct OWN2 as (Q1 & Q2 & Q3 & Q4).
               split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. eapply u32arr_transport; [exact Q4| exact MU| exact WM|]. cbn.
               pose proof (new_limbs_apart_range usegs L HI h' LB LB' m' m' mo' lo dX (mkMPD X sg' n' p' xs' padX LHeap) X 16 HH2 MX2 OUT2 FRS ACL (proj1 DIMG) (proj2 DIMG)) as NL.
               cbn [md_addr md_own md_p md_n] in NL. rewrite LEN2.
               destruct (NL ltac:(intros a Ha; destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C HTOP SLO HLS ACL; lia| right; left; exact C| right; right; exact C]) ltac:(clear; lia) XP eq_refl);
                 clear - H; lia. }
      split; [eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; exact NS2| reflexivity]|].
      split. { eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU1| exact WM1| exact HBR| exact DHI| clear - ACL SLO HLS; lia]|].
               eapply heap_presx_trans; [eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho]|].
               eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn in Ho |- *. split; [| exact I]. clear - Ho. lia. }
      split; [eapply statics_ok_munch; [exact SOK2| exact MU|]; intros a Hd NW; cbn; split; [| exact I]; intros C; exact (NW (XDW a C Hd))|].
      split; [| split; [reflexivity| split; [reflexivity| split; [exact FRS| cbn [md_n]; exact NMO]]]].
      left. split; [reflexivity|]. unfold mpd_val, mpd_abs in *. cbn [md_sg md_limbs] in *. exact HV.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L22219771718.1L32436940338.1L41560720338.7L48076008077.6L59696753857.100000400800I00^00bS2spS2spS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo3SLO3ACLS2sp". (* [comment removed for export] *)
    Lemma as_ERR : forall (t0 t1 t2 raj x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (m1 m' : mem) (mo' : Model)
        (h' : HST usegs L HI) (LB' : list blk) (dX' : mpd),
      after m1 m' mo' h' LB' dX' ->
      aevtM usegs mo' POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 x8 x9
        (Z_to_bv 64 MBEDTLS_ERR_MPI_ALLOC_FAILED) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 133836) fc None m' (seg_rom usegs)).
    Proof.
      intros until dX'. intros AF.
      ddestruct AF as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & BK2 & FR2 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      unfold as_frame in FR2.
      pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl usegs m') as WM.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      zstep.
      apply aevtM_done. unfold POST, mpi_binop_post. deexists 14. dexists m', mo', h', LB', dX', MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [exact MI2|].
      split; [eapply stk_release in FR2; [| exact ST2| clear - SLO HLS ACL ACP; lia]; cbn [cells_size csize Nat.add] in FR2;
              replace (bv_unsigned sp - 48 + Z.of_nat 48) with (bv_unsigned sp) in FR2 by (clear; lia); exact FR2|].
      split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MX2|]. split; [exact OUT2|].
      split. { eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU1| exact WM1| exact HBR| exact DHI| clear - ACL SLO HLS; lia]|].
               eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho]. }
      split; [exact SOK2|]. split; [right; reflexivity| exact BK2].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition at1 (m1 : mem) : Prop :=
      mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp - 48) /\ rw_cells usegs m1 (bv_unsigned sp - 48) (as_frame ra s0 s1 s2 s3 s4) /\
      HEAP usegs L HI h LB m1 mo /\ statics_ok usegs L m1 /\ mpd_at usegs m1 LB dX /\ mpd_at usegs m1 LB dA /\
      opnd_at usegs m1 LB (bv_unsigned sp) dB /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono usegs m m1.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L38948636245.0L45871104164.8L51809538089.7L55595827568.1L774765788.5  00000100J00`00d015SS1L3HLS2sp2lo2nX2pX3SLO1HS1L3HLS2sp2lo1X3SLO2XSS2spS1L3HLS2sp2lo3SLO". (* [comment removed for export] *)
    Lemma after_of_post : forall (m1 m' : mem) (mo' : Model) (h' : HST usegs L HI) (LB' : list blk) (dX' : mpd),
      at1 m1 -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp - 48) -> mo_frame mo mo' ->
      heap_top usegs L HI h' = heap_top usegs L HI h -> HEAP usegs L HI h' LB' m' mo' -> mpd_at usegs m' LB' dX' ->
      mpd_out LB dX LB' dX' -> heap_presx usegs L LB (bv_unsigned sp - 48) (mpd_ivs dX) m1 m' -> statics_ok usegs L m' ->
      binop_keep LB dX dX' -> after m1 m' mo' h' LB' dX'.
    Proof.
      (intros m1 m' mo' h' LB' dX' dd_H; ddestruct dd_H as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1); intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK2).
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _]. ddestruct XW as (XCW & XDW & XP). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in XCW, XP.
      pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MX2|]. split; [exact OUT2|].
      split; [exact HPX2|]. split; [exact SOK2|]. split; [exact BK2|]. split; [| split; [exact MU1| exact WM1]].
      eapply heap_presx_rw_cells; [exact HPX2| exact FR1| apply client_range_stack; clear; lia|].
      unfold as_frame, mpd_ivs. cbn. split; [clear - XS SLO HLS; lia|]. destruct ownX; [exact I| |]; (split; [| exact I]); destruct (XLS ltac:(discriminate)); clear - H SLO HLS; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac pre_call MX1 MA1 MB1 :=
      try exact MX1; try exact MA1; try exact MB1;
      try (eapply (opnd_at_SP_le _ _ _ (bv_unsigned sp)); [first [exact MB1| apply opnd_at_mpd; first [exact MA1| exact MB1]]| clear; lia]);
      try assumption; try (apply mpd_sep_sym; assumption);
      try (clear - SLO SPA HLS ACL HTOP; rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by lia; lia).

    Local Ltac x_facts :=
      pose proof MX as [(CXa & XAL & X0 & _) _]; cbn [md_addr md_sg md_n md_p md_pad] in CXa, XAL, X0; unfold mpi_cells in CXa;
      pose proof (rw_cells_bound _ _ _ _ CXa) as XB; cbn [cells_size csize Nat.add] in XB; clear CXa.
    Local Ltac x_checks := zstep; if_false_x; zstep; land_zero_any; zstep; if_false.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11552774173.10 L12523502953.3  L17808963163.5  L18971972328.10 L22135776033.0  L22219771718.1  L29010569984.163L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L43480590174.4  L43592699947.6  L45445358076.3  L58354988821.5  L59308632561.1  L61386272733.16 L6186700885.5   L63060358698.24 L63509712077.24 L7358958502.18  L8574640155.5   00000800A00H00U00V00Z00[00\00j01G01W01`01n02=02F02M02Q03J03Q03R03S03T03[S2sp3SPAS2sp2pB1HS2ys2zsS1L2sp2lo3SLOSS2spFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2ys2zsS2KRS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2NA2NBS2ys2zsFFFS2ys2zs". (* [comment removed for export] *)
    Lemma as_KADD : forall (t0 t1 t2 raj a0 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m1 : mem) (w : Z),
      at1 m1 -> x20 = Z_to_bv 64 w -> w mod 2 ^ 16 = sA mod 2 ^ 16 -> flip * sB = sA ->
      aevtM usegs mo POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 X) s1 a0 (Z_to_bv 64 Aa)
        (Z_to_bv 64 Ba) a3 a4 a5 a6 a7 s2 s3 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133720) fc None m1 (seg_rom usegs)).
    Proof.
      intros until w. intros AT -> WS SGN. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      x_facts.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep.
      pose proof HADD as SPc. unfold mpi_add_abs_stmt', mpi_binop_stmtB', U_MPI_ADD_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 133728)) with (Z_to_bv 64 133728) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl usegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & _ & _)|Er]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity|]. eapply as_ERR. exact AF.
      - destruct CR1 as [(Er & CV & CS)|Er]; rewrite Er in KR |- *; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
        x_checks.
        eapply as_FIN; [exact AF| reflexivity| exact WS| exact SGA|].
        unfold VAL. pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA.
        pose proof (mpd_abs_nonneg dA) as NA. pose proof (mpd_abs_nonneg dB) as NB. rewrite Z.abs_eq in VA by (clear - NA NB; lia).
        rewrite <- VA. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. rewrite <- SGN. clear - SGA SGB FLIP. destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L11552774173.10 L12523502953.3  L21175842280.10 L22219771718.1  L29010569984.166L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L40015233486.6  L43480590174.4  L43592699947.6  L45445358076.3  L59308518135.16 L59308632561.1  L61171887184.6  L61386304856.15 L63060358698.24 L63509712077.24 L66000499105.0  L7358958502.18  00000800A00N00R00S00T00b01?01O01X01f02402C02L03E03I03W04M04N04O04P04QS2sp3SPAS2sp2pB1HS1L2sp2lo3SLOS2spFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sA2ys2zs3SGNS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LE2LTS2KRS2sA2ys2zs3SGNS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LEFFSF". (* [comment removed for export] *)
    Lemma as_KSUBAB : forall (t0 t1 t2 raj x9 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m1 : mem) (c w : Z),
      at1 m1 -> x20 = Z_to_bv 64 w -> w mod 2 ^ 16 = sA mod 2 ^ 16 -> flip * sB = - sA ->
      (c = 0 /\ mpd_abs dA = mpd_abs dB \/ c = 1 /\ mpd_abs dB < mpd_abs dA) ->
      aevtM usegs mo POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 X) x9 (Z_to_bv 64 c) a1 a2 a3 a4
        a5 a6 a7 (Z_to_bv 64 Aa) (Z_to_bv 64 Ba) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133780) fc None m1 (seg_rom usegs)).
    Proof.
      intros until w. intros AT -> WS SGN HC. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      assert (LE : mpd_abs dB <= mpd_abs dA) by (clear - HC; lia).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      x_facts.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep. zstep. zstep. zstep.
      pose proof HSUB as SPc. unfold mpi_sub_abs_stmt', mpi_binop_stmt', U_MPI_SUB_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 133800)) with (Z_to_bv 64 133800) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl usegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & _ & _)|[Er|[Er LT]]]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity| eapply as_ERR; exact AF| exfalso; clear - LT LE; lia].
      - destruct CR1 as [(Er & CV & CS)|[Er|[Er LT]]]; rewrite Er in KR |- *;
          [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LE; lia].
        pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA. rewrite Z.abs_eq in VA by (clear - LE; lia).
        destruct HC as [(-> & EQ)|(-> & GT)].
        + zstep. if_vm. zstep. zstep. x_checks.
          eapply as_FIN with (w := 1) (sg := 1); [exact AF| bv_eqz| reflexivity| left; reflexivity|].
          unfold VAL. rewrite <- VA. revert EQ. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. intros EQ.
          clear - SGA SGB FLIP SGN EQ. destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
        + zstep. if_vm. x_checks.
          eapply as_FIN with (w := w) (sg := sA); [exact AF| reflexivity| exact WS| exact SGA|].
          unfold VAL. rewrite <- VA. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs].
          clear - SGA SGB FLIP SGN. destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L11552774173.10 L12523502953.3  L21175842280.10 L22219771718.1  L28893959834.6  L29010569984.165L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L43480590174.4  L43592699947.6  L45445358076.3  L48709637724.2  L5231095820.168 L52331515492.6  L59308632561.1  L59310615242.16 L61386302667.15 L63060358698.24 L63509712077.24 L7021056161.0   L7358958502.18  00000800A00N00R00`00a00b01001M01]01f02402C02L02T02`02n03203l04b04c04d04e04fS2sp3SPAS2sp2pB1HS1L2sp2lo3SLOS2spS2sA2ys2zs3SGNFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2sA3SGAS2sp2sA1w2WBS2sA2ys2zs3SGNS2KRS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LT3LT'S2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LTFFSF". (* [comment removed for export] *)
    Lemma as_KSUBBA : forall (t0 t1 t2 raj x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m1 : mem) (w : Z),
      at1 m1 -> x20 = Z_to_bv 64 w -> w mod 2 ^ 16 = sA mod 2 ^ 16 -> 0 <= w < 2 ^ 16 -> flip * sB = - sA ->
      mpd_abs dA < mpd_abs dB ->
      aevtM usegs mo POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 X) x9 a0 a1 a2 a3 a4
        a5 a6 a7 (Z_to_bv 64 Aa) (Z_to_bv 64 Ba) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133816) fc None m1 (seg_rom usegs)).
    Proof.
      intros until w. intros AT -> WS WB SGN LT. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      x_facts.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep. zstep. zstep.
      pose proof HSUB as SPc. unfold mpi_sub_abs_stmt', mpi_binop_stmt', U_MPI_SUB_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dB) (dB := dA) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 133832)) with (Z_to_bv 64 133832) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl usegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & CV & CS)|[Er|[Er LT']]]; rewrite Er in KR |- *;
          [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LT'; lia].
        x_checks. zstep. zstep.
        eapply as_FIN with (w := 0 - w) (sg := - sA); [exact AF| bv_eqz| | clear - SGA; lia|].
        + rewrite Zminus_mod, WS, <- Zminus_mod. reflexivity.
        + unfold VAL. pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA. rewrite Z.abs_eq in VA by (clear - LT; lia).
          rewrite <- VA. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. clear - SGA SGB FLIP SGN.
          destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
      - destruct CR1 as [(Er & _ & _)|[Er|[Er LT']]]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity| eapply as_ERR; exact AF| exfalso; clear - LT LT'; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Lemma as_KCMP : forall (t0 t1 t2 raj a0 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m1 : mem) (w : Z),
      at1 m1 -> x20 = Z_to_bv 64 w -> w mod 2 ^ 16 = sA mod 2 ^ 16 -> 0 <= w < 2 ^ 16 -> flip * sB = - sA ->
      aevtM usegs mo POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 X) s1 a0 (Z_to_bv 64 Aa)
        (Z_to_bv 64 Ba) a3 a4 a5 a6 a7 s2 s3 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133756) fc None m1 (seg_rom usegs)).
    Proof.
      intros until w. intros AT -> WS WB SGN. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      assert (PA0 : ownA = LHeap -> 0 < pA).
      { intros EO. pose proof MA as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_own md_p md_n] in OW. rewrite EO in OW. ddestruct OW as (_ & IN & _).
        exact (proj1 (proj1 (Forall_forall _ _) HBR _ IN)). }
      assert (PB0 : ownB = LHeap -> 0 < pB).
      { intros EO. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_own md_p md_n] in OW. rewrite EO in OW. ddestruct OW as (_ & IN & _).
        exact (proj1 (proj1 (Forall_forall _ _) HBR _ IN)). }
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep. zstep. zstep. zstep.
      pose proof U_mpi_cmp_abs_spec_o as CMP. unfold mpi_cmp_abs_stmt_o, U_MPI_CMP_ABS in CMP.
      eapply aevtM_cut_evt; [exact MK1| eapply CMP with (LB := LB) (dX := dA) (dY := dB)|].
      - rewrite unsigned_lit by (clear - SPB SLO HLS ACL ACP; lia). apply opnd_at_mpd. exact MA1.
      - rewrite unsigned_lit by (clear - SPB SLO HLS ACL ACP; lia). eapply opnd_at_SP_le; [exact MB1| clear; lia].
      - exact PA0.
      - exact PB0.
      - exact MI1.
      - reflexivity.
      - reflexivity.
      - intros ms' PO. unfold mpi_cmp_post in PO.
        destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & -> & _ & _ & MI2).
        rewrite (ret_pc_even 133776) by lia.
        pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS.
        destruct (Z.lt_ge_cases (mpd_abs dA) (mpd_abs dB)) as [LT|GE]; [| destruct (Z.eq_dec (mpd_abs dA) (mpd_abs dB)) as [EQ|NE]].
        + replace (Z.sgn (mpd_abs dA - mpd_abs dB)) with (-1) by (clear - LT SS; lia).
          zstep. if_vm.
          eapply as_KSUBBA; [exact AT| reflexivity| exact WS| exact WB| exact SGN| exact LT].
        + replace (Z.sgn (mpd_abs dA - mpd_abs dB)) with 0 by (clear - EQ SS; lia).
          zstep. if_vm.
          eapply as_KSUBAB with (c := 0); [exact AT| reflexivity| exact WS| exact SGN| left; split; [reflexivity| exact EQ]].
        + replace (Z.sgn (mpd_abs dA - mpd_abs dB)) with 1 by (clear - GE NE SS; lia).
          zstep. if_vm.
          eapply as_KSUBAB with (c := 1); [exact AT| reflexivity| exact WS| exact SGN| right; split; [reflexivity| clear - GE NE; lia]].
    Qed.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L136446722.6  L14622494633.2L22366621351.0L24962925985.0L25523630113.0L32223618336.4L43315511802.6L5212562720.4 L59308628179.1L59663971895.5L635310052.2  L6419290535.0 L7688565214.2 00000E00M00N00O00P00Z00o01<01@01M01U01V01]S4flip2sA2sB2EA2EB2EFS2nB3NRBSSSS2ys2zs2CmS4flip2sA2sB2EA2EB2EFS2ys2zs2C02C1S2K0S2sA2ys2zs2C0S2nA3NRASS2sA2EA". (* [comment removed for export] *)
    Lemma as_body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem),
      at1 m1 ->
      aevtM usegs mo POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Aa)
        (Z_to_bv 64 Ba) (Z_to_bv 64 flip) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 133664) fc None m1 (seg_rom usegs)).
    Proof.
      intros until m1. intros AT. dpose AT as (MI & ST & FR & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct (mpd_raw _ _ _ _ MA1 ltac:(cbn [md_own md_p]; intros EO; rewrite EO in MA; pose proof MA as [(_ & _ & _ & _ & _ & OW) _]; ddestruct OW as (_ & IN & _);
                 pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CEA & ABY & LENA & NRA & _ & ABD & PAB).
      destruct (opnd_raw _ _ _ _ _ MB1 ltac:(cbn [md_own md_p]; intros EO; pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]; cbn [md_own] in OW; rewrite EO in OW; ddestruct OW as (_ & IN & _);
                 pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CEB & BBY & LENB & NRB & _ & BBD & PBB).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA, ABY, LENA, NRA, ABD, PAB, CEB, BBY, LENB, NRB, BBD, PBB.
      pose proof MA as [(_ & AAL & AP0 & _) _]. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & BAL & BP0 & _) _].
      cbn [md_addr] in AAL, AP0, BAL, BP0.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep; if_false_x. zstep. zstep. land_zero_any. zstep. if_false.
      zstep; if_false_x. zstep. land_zero_any. zstep. if_false.
      pose proof FLIP as FL. destruct SGA as [EA|EA]; rewrite EA in CEA; destruct SGB as [EB|EB]; rewrite EB in CEB; (destruct FL as [EF|EF];
        [replace (Z_to_bv 64 flip) with (Z_to_bv 64 1) by (rewrite EF; reflexivity) | replace (Z_to_bv 64 flip) with (Z_to_bv 64 (-1)) by (rewrite EF; reflexivity)]).
      all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; if_vm.
      all: lazymatch goal with
           | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 133720) _ _ _ _) =>
               eapply as_KADD with (w := sA mod 2 ^ 16); [exact AT| rewrite EA; bv_eqz| apply Zmod_mod| clear - EA EB EF; lia]
           | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 133756) _ _ _ _) =>
               eapply as_KCMP with (w := sA mod 2 ^ 16); [exact AT| rewrite EA; bv_eqz| apply Zmod_mod| apply Z.mod_pos_bound; lia| clear - EA EB EF; lia]
           end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.
  (* [comment removed for export] *)
  #[using="Type"] Lemma binop_post_mono : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PR1,P,$3.P,$32.SpPR2,P,$3.P,$32.SpPlo,$3.Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Pc,$3>.P,Pr,$3.Pd,$32.P,A2.R8.R2.R1.A2.R8.R3.R2.P,(3?.$;.VL,VHI,R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R5.R4.R3.R2.)(3?.$;.VL,VHI,R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros until c. intros HR P. unfold mpi_binop_post in *.
    ddestruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & P).
    dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', mo', h', LB', dX', r.
    ddestruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    repeat (split; [assumption|]). apply HR. exact P10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@D10463954377.125D10463954377.126D27668705378.125D27668705378.126L15962907669.8  L21765854580.118L21887662552.117L27775132660.118L33160662877.7  L33510041944.118L34290115814.117L34496295996.7  L35312475779.7  L35754698159.125L35754698159.126L38948636245.0  L43061432074.115L44622288685.125L44622288685.126L49698585326.125L49698585326.126L53028994992.1  L66083662040.118L774765788.5    L9716869748.117 00000R01701^02H02a02e02i02m03B03F03J03`04804N04g04h05=05l06^07807U07Y07]07n082S1L2HI2ra2sp1h4HTOP2HB5Ha_st5Hl_stS1L2HI2sp2s01h4HTOP2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp2lo3SLO3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02lo3SLO3SPB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2nB2pB2lo3SLO1HS2spS2spS2spS1L3HLS2sp2lo3SLO1d1HS2spS2spS1L3HLS2sp2lo3SLO1d2D1S1L3HLS2sp2Ba2lo3SLO3OB4S2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s1SS1L3HLS2sp2lo3SLO3SPBS1L3HLS2ra2sp2lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_st2s1S2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s1S2spS2spS1L3HLS2sp2lo3SLOS2sp". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Lemma U_add_sub_mpi_spec : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pflip,$3.P,(11.(5.$3.R1.+1.)(5.$3.R1.-1.))Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PdA,$32.PdB,$32.Plo,$3.P,(20.$;.VL,VHI,R6.R5.R8.R7.)P,(21.$;.R9.R6.R5.)P,(21.$;.R:.R7.R5.)P,(39.$;.R;.R8.(1=.&40.R2:.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(41.(5.$42.(43.R;.)$44.))P,(45.R<.R;.R9.(1=.&40.R2?.))P,(45.R=.R;.R:.(1=.&40.R30.))P,(46.VL,R?.R;.(47.R=.)+10.)P,P,(5.$42.(43.R>.)$48.)(46.VL,R11.R=.(49.R?.)(19.+4.(4:.R?.)))P,(46.VL,R11.R=.(47.R>.)+10.)P,P,(5.$42.(43.R?.)$48.)(46.VL,R13.R?.(49.R10.)(19.+4.(4:.R10.)))P,(4;.VL,R13.(1=.&40.R35.)(1?.$;.VL,VHI,R14.)R12.)P,P,(41.(5.$42.(43.R13.)$4<.))(11.(14.(18.(49.R14.)(19.+4.(4:.R14.)))R11.)(14.(1=.&40.R37.)(49.R14.)))P,(1<.$;.R18.R11.(1=.&40.R37.))P,(14.R12.(16.(16.(1=.&40.R38.)+>0.)(4=.VL,)))P,(14.(4>.VL,)R13.)P,(14.(1=.&40.R3:.)(1?.$;.VL,VHI,R19.))P,(5.$3.(34.(1=.&40.R3;.)+10.)=)P,(14.(4?.VL,)(4>.VL,))P,(5.(2.&40.)R3;.(8.&40.(50.VL,)))P,(10.$;.R1?.)P,(26.$;.VL,R20.)P,(51.VL,VMSF,+8.)P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))(37.$;.R24.(3?.$;.VL,VHI,R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(52.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(6.(7.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(8.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(8.&40.+20:04.)R26.(9.(2.&40.))R25.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros flip FLIP. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA]. destruct dB as [Ba sB nB pB zs padB ownB].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5). dpose XW as (XCW & XDW & XP).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OA4, OA5, OB4, OB5, XCW.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
    pose proof ST as ST1. carve_frame 48%nat ST1.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HHc. pose proof (conj SOK I) as SOKc. pose proof MI as MI1.
    do 7 zstep.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct HHc as [HH0 _]. destruct SOKc as [SOK0 _].
    assert (OPM : forall d, mpd_at usegs m LB d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> mpd_at usegs m1 LB d).
    { intros d Md D1 D2. eapply mpd_at_munch_any; [exact Md| exact MU| exact WM| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    eapply (as_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB lo flip X sX nX pX xs0 padX ownX Aa sA nA pA ys padA ownA Ba sB nB pB zs padB ownB);
      try assumption.
    split; [exact MI1|]. split; [exact ST1|]. split; [exact FR|].
    split; [first [exact HH| eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH0| exact MU| exact WM| exact ACL|]; intros a Ha NO; cbn in NO; left; clear - NO HTOP SLO HLS; lia]|].
    split; [first [exact SOK| eapply statics_ok_munch; [exact SOK0| exact MU|]; intros a Hd NW; cbn; split; [clear - Hd DHI ACL SLO HLS; lia| exact I]]|].
    split; [exact (OPM _ MX XS XLS)|]. split; [exact (OPM _ MA OA4 OA5)|].
    split. { eapply opnd_at_munch_any; [exact MB| exact MU| exact WM| cbn; split; [clear - OB4 SLO HLS; lia| exact I]|].
             intros ON. cbn. split; [destruct (OB5 ON); clear - H SLO HLS; lia| exact I]. }
    split; [exact MU| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L65106939752.8300000:S2sp2dA2dB". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Theorem U_mpi_add_mpi_spec' : mpi_add_mpi_stmt usegs L HI U_MPI_ADD_MPI MSF.
  Proof.
    unfold mpi_add_mpi_stmt, mpi_binop_stmt, U_MPI_ADD_MPI. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep.
    eapply aevtM_mono; [eapply (U_add_sub_mpi_spec 1 ltac:(left; reflexivity)) with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); try eassumption; try reflexivity; apply opnd_at_mpd; assumption|].
    cbv beta. intros c. apply binop_post_mono. intros r d [V K]. split; [| exact K].
    destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L52849495742.8300000:S2sp2dA2dB". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Theorem U_mpi_sub_mpi_spec' : mpi_sub_mpi_stmt usegs L HI U_MPI_SUB_MPI MSF.
  Proof.
    unfold mpi_sub_mpi_stmt, mpi_binop_stmt, U_MPI_SUB_MPI. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep.
    eapply aevtM_mono; [eapply (U_add_sub_mpi_spec (-1) ltac:(right; reflexivity)) with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); try eassumption; try reflexivity; apply opnd_at_mpd; assumption|].
    cbv beta. intros c. apply binop_post_mono. intros r d [V K]. split; [| exact K].
    destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_add_mpi_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_add_mpi_stmt usegs L HI U_MPI_ADD_MPI MSF.
  Proof.
    intros MSF E. apply U_mpi_add_mpi_spec'; try assumption.
    - apply U_mpi_add_abs_spec_o; assumption.
    - apply U_mpi_sub_abs_spec_o; assumption.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_sub_mpi_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_sub_mpi_stmt usegs L HI U_MPI_SUB_MPI MSF.
  Proof.
    intros MSF E. apply U_mpi_sub_mpi_spec'; try assumption.
    - apply U_mpi_add_abs_spec_o; assumption.
    - apply U_mpi_sub_abs_spec_o; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_add_sub_mpi_spec_o : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "PMSF,$3.P,(5.$3.R1.$53.)Pflip,$3.P,(11.(5.$3.R1.+1.)(5.$3.R1.-1.))Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PdA,$32.PdB,$32.Plo,$3.P,(20.$;.VL,VHI,R6.R5.R8.R7.)P,(21.$;.R9.R6.R5.)P,(21.$;.R:.R7.R5.)P,(39.$;.R;.R8.(1=.&40.R2:.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(41.(5.$42.(43.R;.)$44.))P,(45.R<.R;.R9.(1=.&40.R2?.))P,(45.R=.R;.R:.(1=.&40.R30.))P,(46.VL,R?.R;.(47.R=.)+10.)P,P,(5.$42.(43.R>.)$48.)(46.VL,R11.R=.(49.R?.)(19.+4.(4:.R?.)))P,(46.VL,R11.R=.(47.R>.)+10.)P,P,(5.$42.(43.R?.)$48.)(46.VL,R13.R?.(49.R10.)(19.+4.(4:.R10.)))P,(4;.VL,R13.(1=.&40.R35.)(1?.$;.VL,VHI,R14.)R12.)P,P,(41.(5.$42.(43.R13.)$4<.))(11.(14.(18.(49.R14.)(19.+4.(4:.R14.)))R11.)(14.(1=.&40.R37.)(49.R14.)))P,(1<.$;.R18.R11.(1=.&40.R37.))P,(14.R12.(16.(16.(1=.&40.R38.)+>0.)(4=.VL,)))P,(14.(4>.VL,)R13.)P,(14.(1=.&40.R3:.)(1?.$;.VL,VHI,R19.))P,(5.$3.(34.(1=.&40.R3;.)+10.)=)P,(14.(4?.VL,)(4>.VL,))P,(5.(2.&40.)R3;.(8.&40.(50.VL,)))P,(10.$;.R1?.)P,(26.$;.VL,R20.)P,(51.VL,R45.+8.)P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))(37.$;.R24.(3?.$;.VL,VHI,R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(52.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(6.(7.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(8.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(8.&40.+20:04.)R26.(9.(2.&40.))R25.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros MSF E. apply U_add_sub_mpi_spec; try assumption.
    - apply U_mpi_add_abs_spec_o; assumption.
    - apply U_mpi_sub_abs_spec_o; assumption.
  Qed.
End Spec.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W1_misc Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_j0lem Fz_W3_j0r Fz_W3_j0n.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | apply wa_of_var; lia ].

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.
(* [comment removed for export] *)
Ltac enred := cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_s e_LBall e_LB0 e_LBL e_L e_f e_m e_lo e_B
                   e_K e_pe e_BI e_meth e_blen e_bmax e_boff e_flags e_E e_Enm].

(* [comment removed for export] *)
Lemma mbio_rep_ids `{CE__ : Ceiling} `{RN__ : RunRnd} : forall (m : mem) LBall L K BI meth len max off q,
  mbio_rep m LBall L K BI meth len max off -> mbio_T K q -> In q (map blk_id LBall).
Proof.
  intros m LBall L K BI meth len max off q [BM MB] Tq.
  destruct MB as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DOPT).
  destruct Tq as [->|[->|[->|[->|KD]]]].
  - apply in_map_iff. exists (k_bi K, BI, 128). split; [reflexivity| exact (proj1 OWNB)].
  - apply in_map_iff. exists (k_bb K, BB, 16). split; [reflexivity| exact (proj1 OWNbb)].
  - apply in_map_iff. exists (k_bm K, BM, 32). split; [reflexivity| exact (proj1 OWNbm)].
  - apply in_map_iff. exists (k_rp K, RP, 32). split; [reflexivity| exact (proj1 OWNrp)].
  - rewrite KD in DOPT. destruct DOPT as (D & nm & junk & OWND & _). apply in_map_iff. exists (q, D, max). split; [reflexivity| exact (proj1 OWND)].
Qed.

Lemma mbio_rep_off `{CE__ : Ceiling} `{RN__ : RunRnd} : forall (m : mem) LBall L K BI meth len max off,
  mbio_rep m LBall L K BI meth len max off -> 0 <= off <= len /\ List.NoDup (mbio_blocks K).
Proof.
  intros m LBall L K BI meth len max off [BM MB].
  destruct MB as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & _). split; [exact OFF| exact NDK].
Qed.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation libenv_munchI := (libenv_munch libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  Theorem J0_proof :
    RAISE0_stmt libenv errst_at_rest errst_live -> J0N_stmt libenv errst_at_rest errst_live -> pem_read_bio_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros R0P J0NP. unfold RAISE0_stmt, J_RAISE0 in R0P. unfold J0N_stmt, J_J0N in J0NP. unfold pem_read_bio_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 LBL L f K pe BI meth blen bmax boff PL flags E enm lo B
           on oh od ol.
    intros FUEL ROOM CST SLO LE INCL NTL OWNE NPE ER0 MB BLEN EPL PLB AL16 OUT -> -> -> -> -> -> FLR. subst PL.
    set (en := PEMENT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 LBL L f m lo B K pe BI meth blen bmax boff flags E enm).
    lazymatch goal with |- climpl _ _ _ _ ?P => change P with (pem_post libenv errst_live en) end.
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold PEMR_STACK, BPUTS_STACK, WRITE_STACK, GROW_STACK, FZ_PEM_READ_BIO, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (mbio_rep_off _ _ _ _ _ _ _ _ _ MB) as [OFF NDK].
    assert (NDR : List.NoDup (e_pe en :: mbio_blocks (e_K en))) by (constructor; [exact NPE| exact NDK]).
    assert (INE : In (pe, E, 904) LBall) by exact (proj1 OWNE).
    assert (EPE : In (e_pe en) (map blk_id (e_LBall en))) by (apply in_map_iff; exists (pe, E, 904); split; [reflexivity| exact INE]).
    assert (EK : forall q, mbio_T (e_K en) q -> In q (map blk_id (e_LBall en))) by (intros q Tq; exact (mbio_rep_ids _ _ _ _ _ _ _ _ _ _ MB Tq)).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -224, bv_unsigned sp + 32)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (HWo : Forall (wfree LBall lo (bv_unsigned sp + 32) (fun _ => True)) [(bv_unsigned sp + -224, bv_unsigned sp + 32)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    assert (ENTRY : forall mX, munch [(bv_unsigned sp + -224, bv_unsigned sp + 32)] m mX -> wmono usegs m mX -> mem_inv usegs mX -> stk usegs mX lo (bv_unsigned sp + -208) ->
              rw_cells usegs mX (bv_unsigned sp + -104) (pem_saved en) ->
              pem_com libenv en s LBall L f mX boff (pem_EV en) 16 8 (pem_BIG en) /\ errst_at_rest E [] mX).
    { intros mX MUX WMX MIX STX SAVEDX. unfold pem_com, pem_T, pem_EV, pem_BIG, e_PL, incl_blocks. unfold en. enred. split.
      - split. { eapply (cstate_seg _ _ _ _ _ m mX sp _ tp lo B (bv_unsigned sp + 32)); [exact CST| exact MUX| exact WMX| exact MIX| | clear - SLO; lia| exact PLB| | rewrite unsigned_lit by lia; exact STX| rewrite unsigned_lit by lia; clear - PLB; lia].
          + apply Forall_cons; [apply cwin_stack; clear - SLO; lia| apply Forall_nil].
          + cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO LO GLO; lia. }
        split. { eapply cframe_seg; [apply cframe_refl| exact MUX| exact WMX| exact HP| clear - SLO LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
        split; [eapply libenv_munchI; [exact LE| exact MUX| exact WMX| exact CST| exact INCL| exact HWo| intros b _; exact I]|].
        split; [exact INCL|]. split; [exact INCL|]. split; [exact NTL|]. split; [exact OWNE|].
        split; [eapply mbio_rep_agree; [exact MB| eapply mbio_fp_munch; [exact CST| exact MUX| exact WMX| exact HWo| intros q _; exact I]]|].
        split; [clear - OFF; lia|]. split; [exact FUEL|]. split; [clear - FUEL; lia|].
        split; [exact ROOM|]. split; [clear; unfold cgrow; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear - OFF; lia|].
        split; [intros b X; exact X|]. split; [intros q nm X; exact X|]. split; [exact SAVEDX|].
        split; [unfold BPUTS_STACK, WRITE_STACK, GROW_STACK; rewrite WSP; clear - SLO; lia|]. split; [exact PLB|]. split; [exact FLR|]. split; [exact AL16|]. split; [exact EPE| exact EK].
      - eapply (er0_segI _ en); [exact ER0| exact MUX| exact WMX| exact CST| exact INE| exact HWo| exact I]. }
    (* [comment removed for export] *)
    assert (JOIN : forall mc (meth0 : Z) (junk104 : list byte) (xra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word),
      (meth0 = M_MEM \/ meth0 = M_SECMEM) ->
      munch [(bv_unsigned sp + -224, bv_unsigned sp + 32)] m mc -> wmono usegs m mc -> mem_inv usegs mc -> stk usegs mc lo (bv_unsigned sp + -208) ->
      rw_cells usegs mc (bv_unsigned sp + -104) (pem_saved en) -> rw_cells usegs mc (bv_unsigned sp + -208) [CB 104 junk104] ->
      rw_cells usegs mc (bv_unsigned sp) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
      climpl f L s (MS (mkR xra (wz (bv_unsigned sp + -208)) gp tp y0 y1 y2 sp s1 (wz meth0) y3 y4 y5 y6 y7 y8 y9
                         s2 (wz (bv_unsigned sp + 8)) (wz (bv_unsigned sp + 16)) (wz flags) s6 sp (wz (bv_unsigned sp + 24)) (wz BI) s10 s11 y10 y11 y12 y13)
                   F (wz 0x188050) fc None mc (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros mc meth0 junk104 xra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 METH MUc WMc MIc STc SAVEDc LOCc OUTc.
      destruct (ENTRY mc MUc WMc MIc STc SAVEDc) as [COMc ERc].
      destruct (rw_cells_junk_pem_loc mc _ _ LOCc) as (l0 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & ta & tb & PLOC).
      pose proof (munch_refl ([] : list (Z * Z)) mc) as MU0. pose proof (wmono_refl usegs mc) as WM0.
      cprefix. ths. chere.
      (* [comment removed for export] *)
      pose proof (J0NP en) as X. unfold e_PL in X. rewrite ?Z_to_bv_bv_unsigned in X.
      eapply (X s LBall L f mc boff (pem_EV en) 16 8 (pem_BIG en)); unfold pem_EV, pem_BIG; unfold en; enred;
        [exact COMc| exact ERc| clear - OFF; lia| clear - OFF; lia| exact BLEN
        | clear; lia| clear; lia| clear - OFF; lia| intros b Y; exact Y| exact NDR| exact METH| exact PLOC| exact OUTc]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ OUT) as OUTB. cbn [cells_size csize Nat.add] in OUTB.
    cprefix. step. th_frame 208%nat [104; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 13 ths.
    ths. ths. ubs_if. ths. ths. ths. ths. ubs_if.
    ths. ths. ths. ubs_if. ths. ths. ubs_if.
    ths. ths. ths. ubs_if. ths. ths. ubs_if.
    ths. ths. ths. ubs_if. ths. ths. ubs_if.
    ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : stk usegs m1 lo _ |- _ => rename H into ST1 end. lazymatch goal with H : mem_inv usegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : munch _ m m1 |- _ => rename H into MU1 end. lazymatch goal with H : wmono usegs m m1 |- _ => rename H into WM1 end.
    lazymatch goal with H : rw_cells usegs m1 (bv_unsigned sp + -208) (CB 104 ?jk :: _) |- _ => rename H into FR1; set (junk104 := jk) in FR1 end.
    lazymatch goal with H : rw_cells usegs m1 (bv_unsigned sp) _ |- _ => rename H into OUT1 end.
    (* [comment removed for export] *)
    pose proof FR1 as FR1'.
    change (rw_cells usegs m1 (bv_unsigned sp + -208) ([CB 104 junk104] ++ pem_saved en)) in FR1'.
    apply (proj1 (rw_cells_app usegs m1 _ _ _)) in FR1'. destruct FR1' as [LOC1 SAVED1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SAVED1.
    replace (bv_unsigned sp + -208 + 104) with (bv_unsigned sp + -104) in SAVED1 by (clear; lia).
    ths. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      ths. ths. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        ths. tcall (W1_BIO_s_secmem_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
        all: try first [eassumption | clear - LO SLO SPR GLO; lia].
        cbv beta delta [mkR]. chere.
        eapply (JOIN _ M_SECMEM junk104); [right; reflexivity| eassumption| eassumption| eassumption| eassumption| exact SAVED1| exact LOC1| exact OUT1].
      + ths. tcall (W1_BIO_s_mem_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
        all: try first [eassumption | clear - LO SLO SPR GLO; lia].
        cbv beta delta [mkR]. ths. chere.
        eapply (JOIN _ M_MEM junk104); [left; reflexivity| eassumption| eassumption| eassumption| eassumption| exact SAVED1| exact LOC1| exact OUT1].
    - (* [comment removed for export] *)
      chere. destruct (ENTRY m1 MU1 WM1 MI1 ST1 SAVED1) as [COM1 ER1].
      eapply (R0P en s LBall L f m1 boff (pem_EV en) 16 8 (pem_BIG en) [CB 104%nat junk104]);
        [exact COM1| exact ER1| unfold pem_EV; unfold en; enred; clear - OFF; lia| clear; lia| intros b X; exact X| exact NDR| exact LOC1| reflexivity| exact OUT1].
  Qed.
End W3.

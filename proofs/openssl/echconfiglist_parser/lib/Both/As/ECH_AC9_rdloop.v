(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC8_blockA ECH_AC9_kit ECH_AC9_rdseg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64 ECH_C9_rdfacts.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ubal_any :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch R with
      | context [Z.land ?x 7] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | idtac ]
      | context [Z.land ?x 3] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                | idtac ]
      | _ => idtac
      end
  | _ => idtac
  end.


Section HC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  (* [comment removed for export] *)
  Lemma ENCCTX_CB92 : forall LB m a d p, ENCCTX H LB m a d p ->
    (exists old, rw_cells asegs m a [CB 92 old]) /\ In (p, a, ENCCTX_SIZE) LB /\ ablock_range H a ENCCTX_SIZE /\ (length d < 64)%nat.
  Proof.
    intros LB m a d p (raw & line & L & MD & RC & LN & IN & RB & DI).
    split; [| split; [exact IN| split; [exact RB| apply DI]]].
    exists (cells_bytes [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]).
    eapply arw_cells_recut; [exact RC| | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
    cbn -[cells_bytes]. split; [| exact I]. pose proof (cells_bytes_length [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]) as E.
    cbn [cells_size csize Nat.add] in E. apply E. cbn. repeat split; auto.
  Qed.

  Lemma ENCCTX_transport : forall W m m' LB a d p,
    munch W m m' -> wmono asegs m m' -> disjoint_from W a 92 -> ENCCTX H LB m a d p -> ENCCTX H LB m' a d p.
  Proof.
    intros W m m' LB a d p MU WM DJ (raw & line & L & MD & RC & LN & IN & RB & DI).
    exists raw, line. split; [exact L|]. split; [exact MD|]. split; [| exact (conj LN (conj IN (conj RB DI)))].
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact DJ.
  Qed.

  Lemma MEMBIO_transport : forall W m m' LB a M,
    munch W m m' -> wmono asegs m m' ->
    disjoint_from W a BIO_SIZE -> disjoint_from W (mb_bb M) BIOBUFMEM_SIZE ->
    disjoint_from W (mb_bm M) BUFMEM_SIZE -> disjoint_from W (mb_rp M) BUFMEM_SIZE ->
    MEMBIO H LB m a M -> MEMBIO H LB m' a M.
  Proof.
    intros W m m' LB a M MU WM D1 D2 D3 D4 (H1 & H2 & H3 & H4 & REST).
    split; [| split; [| split; [| split; [| exact REST]]]].
    - eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D1].
    - eapply rw_cells_transport; [exact H2| exact MU| exact WM| exact D2].
    - eapply rw_cells_transport; [exact H3| exact MU| exact WM| exact D3].
    - eapply rw_cells_transport; [exact H4| exact MU| exact WM| exact D4].
  Qed.

  Lemma decode_final_rv_cases : forall d, decode_final_rv d = 1 \/ decode_final_rv d = -1.
  Proof.
    intros d. unfold decode_final_rv. destruct (Nat.eqb (length d) 0); [left; reflexivity|].
    destruct (decodeblock_ret d (-1) <? 0); [right| left]; reflexivity.
  Qed.
End HC.

(* [comment removed for export] *)
Ltac mbnum MB :=
  let T := fresh "MBt" in
  pose proof MB as T; unfold MEMBIO in T;
  cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset] in T;
  let MBP := fresh "MBP" in let MBL := fresh "MBL" in let MBB0 := fresh "MBB0" in let MBBH := fresh "MBBH" in
  let MBF := fresh "MBF" in let MBN := fresh "MBN" in let MBN2 := fresh "MBN2" in
  destruct T as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MBP & MBL & MBB0 & MBBH & MBF & _ & _ & _ & MBN & MBN2 & _ & _).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zapZ := repeat match goal with x := _ : Z |- _ => subst x end.
(* [comment removed for export] *)
Ltac base_of t := match t with | ?b + _ + _ => b | ?b + _ => b | ?b - _ => b | _ => t end.
Ltac unhide_for_goal :=
    repeat match goal with
    | H : hidden (_ <= ?y \/ _ <= ?x) |- ?G =>
        let by0 := base_of y in let bx0 := base_of x in
        match G with context [by0] => match G with context [bx0] => unhide H end end
    end.
(* [comment removed for export] *)
Ltac unhide_fsb_for ffv :=
    match goal with
    | |- context [ffv] =>
        repeat match goal with
        | Hh : hidden (?u + _ + _ <= _ \/ _ + _ <= ?u - _) |- ?G => match G with context [u] => unhide Hh end
        end
    | _ => idtac
    end.
Ltac lia_clean :=
    repeat match goal with H : hidden _ |- _ => clear H end;
    repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H | H : MEMBIO _ _ _ _ _ |- _ => clear H
                         | H : ENCCTX _ _ _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H
                         | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
                         | H : @eq nat _ _ |- _ => clear H | H : (_ <= _)%nat |- _ => clear H | H : (_ < _)%nat |- _ => clear H
                         | H : @eq (list _) _ _ |- _ => clear H | H : In _ _ |- _ => clear H
                         | H : accessible _ _ _ |- _ => clear H | H : addressable _ _ _ |- _ => clear H | H : shvis _ _ _ |- _ => clear H
                         | H : ACONST _ |- _ => clear H | H : as_RFS _ _ _ |- _ => clear H | H : as_RHEAP _ _ _ _ |- _ => clear H
                         | H : arelro_lib _ |- _ => clear H | H : fsobj _ _ _ _ |- _ => clear H end;
    Zify.zify; xlia zchecker.
Ltac djak := zapZ; unhide_for_goal; lia_clean.
Ltac djsk := cbn [disjoint_from cells_size csize length map app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ rdhdr ardslots bio_cells buf_cells];
    unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE, B64CTX_SIZE, ENCCTX_SIZE;
    repeat lazymatch goal with |- _ /\ _ => split end; try exact I; djak.
Ltac dja := zapZ; repeat match goal with H : ?A \/ ?B |- _ => hide H end; unhide_for_goal;
    match goal with Hf : aframe_range _ 0 ?ffv _ |- _ => unhide_fsb_for ffv | _ => idtac end;
    lia_clean.
Ltac djs := cbn [disjoint_from cells_size csize length map app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ rdhdr ardslots bio_cells buf_cells];
    unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE, B64CTX_SIZE, ENCCTX_SIZE;
    repeat lazymatch goal with |- _ /\ _ => split end; try exact I; dja.
(* [comment removed for export] *)
Ltac carryh MU WM :=
    lazymatch type of MU with
    | munch ?W ?ma ?mb =>
        repeat match goal with
        | H : rw_cells ?segs ma ?A ?cs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by djs;
                    apply (fun HH => @rw_cells_transport segs W ma mb A cs HH MU WM D) in H; clear D
                  | change (ECH_AKit.stale (rw_cells segs ma A cs)) in H ]
        | H : bytes_at ?segs ma ?A ?bs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (length bs))) by djs;
                    apply (fun HH => @bytes_at_transport segs W ma mb A bs HH MU D) in H; clear D
                  | change (ECH_AKit.stale (bytes_at segs ma A bs)) in H ]
        | H : stk ?segs ma ?l ?h |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W l (h - l)) by djs;
                    apply (fun HH => @stk_transport_disjoint segs W ma mb l h HH MU WM D) in H; clear D
                  | change (ECH_AKit.stale (stk segs ma l h)) in H ]
        | H : ENCCTX ?HI ?LBx ma ?A ?d ?p |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A 92) by djs;
                    apply (fun HH => @ENCCTX_transport _ HI W ma mb LBx A d p MU WM D HH) in H; clear D
                  | change (ECH_AKit.stale (ENCCTX HI LBx ma A d p)) in H ]
        | H : MEMBIO ?HI ?LBx ma ?A ?M |- _ =>
            first [ let D1 := fresh in let D2 := fresh in let D3 := fresh in let D4 := fresh in
                    assert (D1 : disjoint_from W A BIO_SIZE) by (unfold BIO_SIZE; djs);
                    assert (D2 : disjoint_from W (mb_bb M) BIOBUFMEM_SIZE) by (cbn [mb_bb mset]; unfold BIOBUFMEM_SIZE; djs);
                    assert (D3 : disjoint_from W (mb_bm M) BUFMEM_SIZE) by (cbn [mb_bm mset]; unfold BUFMEM_SIZE; djs);
                    assert (D4 : disjoint_from W (mb_rp M) BUFMEM_SIZE) by (cbn [mb_rp mset]; unfold BUFMEM_SIZE; djs);
                    apply (fun HH => @MEMBIO_transport _ HI W ma mb LBx A M MU WM D1 D2 D3 D4 HH) in H; clear D1 D2 D3 D4
                  | change (ECH_AKit.stale (MEMBIO HI LBx ma A M)) in H ]
        | H : B64TAB ma |- _ => clear H
        | H : mem_inv _ ma |- _ => clear H
        end;
        repeat match goal with H : ECH_AKit.stale _ |- _ => clear H end
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Hypothesis BRMS : bioread_mem_stmt H.
  Hypothesis TFS : biotestflags_stmt H.
  Hypothesis DUS : decupdate_stmt H.
  Hypothesis DFS : decfinal_stmt H.
  Hypothesis DIS : decinit_stmt H.
  (* [comment removed for export] *)
  Variables (sp0 fb : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (j136 j152 : word) (j256 : list byte).
  Variables (m0 : mem) (s : as_St H) (LB : list block) (LF : list fframe) (ff fp : Z).
  Variables (a mb lo out0 outl0 : Z) (R : b64frep) (M0 : membio) (txt : list byte).
  Local Notation ctx := (bf_ctx R).
  Local Notation enc := (bf_enc R).
  Local Notation TXT := (map bv_unsigned txt).
  Local Notation LFb := ((0, ff, fp) :: LF).
  (* [comment removed for export] *)
  Definition WL' : list (Z * Z) :=
    [(out0, out0 + outl0); (ctx, ctx + 2566); (enc, enc + 92); (mb, mb + 128); (mb_bm M0, mb_bm M0 + 32); (ff + 32, ff + 36)].
  Definition FP (XS : list (Z * Z)) : list (Z * Z) := (lo, fb + 280) :: XS ++ WL'.

  (* [comment removed for export] *)
  Hypothesis APB : B64F_apart a R.
  Hypothesis BLW : B64F_below a R lo.
  Hypothesis RBa : ablock_range H a BIO_SIZE.
  Hypothesis RBc : ablock_range H ctx B64CTX_SIZE.
  Hypothesis RBe : ablock_range H enc 92.
  Hypothesis FLR : 0 <= bf_flags R < 2^31.
  Hypothesis NONL : Z.land (bf_flags R) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL.
  Hypothesis INe : In (bf_eid R, enc, ENCCTX_SIZE) LB.
  Hypothesis MBW : MEMBIO_below mb M0 lo.
  Hypothesis MSP : MEMBIO_sep mb M0.
  Hypothesis MRB : ablock_range H mb BIO_SIZE /\ ablock_range H (mb_bb M0) BIOBUFMEM_SIZE /\ ablock_range H (mb_bm M0) BUFMEM_SIZE /\ ablock_range H (mb_rp M0) BUFMEM_SIZE.
  Hypothesis MLEN : 0 <= mb_len M0 < 2^31.
  Hypothesis TL : zlength txt = mb_len M0.
  Hypothesis X1 : Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M0)) (blocks_B64F a R).
  Hypothesis X2 : Forall (fun b => mb_buf M0 + mb_len M0 <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M0) (blocks_B64F a R).
  Hypothesis X3 : Forall (fun b => out0 + outl0 <= blk_addr b \/ blk_addr b + blk_size b <= out0) (blocks_MEMBIO mb M0).
  Hypothesis X4 : mb_buf M0 + mb_len M0 <= out0 \/ out0 + outl0 <= mb_buf M0.
  Hypothesis X5 : out0 + outl0 <= A_mem_buf_method + O_METH_BREAD \/ A_mem_buf_method + O_METH_BREAD + 64 <= out0.
  Hypothesis X6 : Forall (fun b => out0 + outl0 <= blk_addr b \/ blk_addr b + blk_size b <= out0) (blocks_B64F a R).
  Hypothesis OUTW : out0 + outl0 <= lo \/ sp0 <= out0.
  Hypothesis OUT0 : 0 < out0.
  Hypothesis OUTE : out0 + outl0 <= 2^64.
  Hypothesis OUTTOP : AIMG_TOP <= out0.
  Hypothesis OUTL0 : 0 < outl0 < 2^31.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LOS : lo <= fb - Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK (Z.max DECFINAL_STACK (Z.max DECINIT_STACK AINTRIN_STACK))).
  Hypothesis FBT : fb + 280 <= sp0 - 104.
  Hypothesis SPT : sp0 < 2^64.
  Hypothesis FB16 : fb mod 16 = 0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis METH0 : METH_mem m0.
  (* [comment removed for export] *)
  Variable B0 : biorep.
  Hypothesis AH0 : rw_cells asegs m0 a (bio_cells B0).
  Hypothesis BOK0 : bio_ok B0.
  Hypothesis BNL : Z.land (bio_flags B0) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL.
  (* [comment removed for export] *)
  Hypothesis FFR : aframe_range H 0 ff fp.
  Hypothesis FSBOK : afsb_ok H.
  Hypothesis LFLEN : (length LFb < AFS_MAXLIVE)%nat.
  Hypothesis SHP0 : rw_cells asegs m0 (sh ff) b64rd_shpat.
  Hypothesis BSH0 : B64F_shad m0 a R.
  Hypothesis MBSH0 : MEMBIO_shad m0 mb M0.
  Hypothesis PAY0 : PAYLOAD_shad m0 M0.
  Hypothesis OSH0 : OUT_shad m0 out0 outl0.
  Hypothesis CSV0 : shvis m0 ctx (ctx + B64CTX_SIZE).
  Hypothesis CAPP : in_app_mem ctx (ctx + B64CTX_SIZE).
  Hypothesis OBout : fsobj H LFb out0 outl0.
  Hypothesis OBpay : fsobj H LFb (mb_buf M0) (mb_len M0).
  (* [comment removed for export] *)
  Hypothesis PAYFF : mb_buf M0 + mb_len M0 <= ff \/ ff + 64 <= mb_buf M0.
  Hypothesis OUTFF : out0 + outl0 <= ff \/ ff + 64 <= out0.
  Hypothesis AWout : afs_write_ok H LF (out0, out0 + outl0).
  Hypothesis ACWout : aclient_write_ok H LB (out0, out0 + outl0).
  Hypothesis INc : In (bf_cid R, ctx, B64CTX_SIZE) LB.
  Hypothesis INa : In (bf_id R, a, BIO_SIZE) LB.
  Hypothesis INmb : In (mb_id M0, mb, BIO_SIZE) LB /\ In (mb_bmid M0, mb_bm M0, BUFMEM_SIZE) LB.

  (* [comment removed for export] *)
  Local Ltac facts :=
    let T := fresh in
    pose proof X1 as T; unfold blocks_B64F, blocks_MEMBIO in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T;
    destruct T as ((hA_M & hA_BB & hA_BM & hA_RP & _) & (hC_M & hC_BB & hC_BM & hC_RP & _) & (hE_M & hE_BB & hE_BM & hE_RP & _) & _);
    pose proof X2 as T; unfold blocks_B64F in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hP_A & hP_C & hP_E & _);
    pose proof X3 as T; unfold blocks_MEMBIO in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hO_M & hO_BB & hO_BM & hO_RP & _);
    pose proof X6 as T; unfold blocks_B64F in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hO_A & hO_C & hO_E & _);
    pose proof APB as T; unfold B64F_apart in T; destruct T as (hAC & hAE & hCE);
    pose proof MSP as T; unfold MEMBIO_sep, MEMBIO_apart in T;
    destruct T as ((hM_BB & hM_BM & hM_RP & hBB_BM & hBB_RP & hBM_RP) & hP_M & hP_BB & hP_BM & hP_RP);
    pose proof X4 as hX4; pose proof X5 as hX5; pose proof OUTW as hOUTW;
    assert (hOUTW2 : out0 + outl0 <= fb \/ fb + 384 <= out0) by (pose proof LOS; pose proof FBT; lia);
    cbn [blk_addr blk_size fst snd] in hA_M, hA_BB, hA_BM, hA_RP, hC_M, hC_BB, hC_BM, hC_RP, hE_M, hE_BB, hE_BM, hE_RP, hP_A, hP_C, hP_E,
      hO_M, hO_BB, hO_BM, hO_RP, hO_A, hO_C, hO_E;
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, O_METH_BREAD, A_mem_buf_method in
      hA_M, hA_BB, hA_BM, hA_RP, hC_M, hC_BB, hC_BM, hC_RP, hE_M, hE_BB, hE_BM, hE_RP, hP_A, hP_C, hP_E,
      hO_M, hO_BB, hO_BM, hO_RP, hO_A, hO_C, hO_E, hAC, hAE, hCE, hM_BB, hM_BM, hM_RP, hBB_BM, hBB_RP, hBM_RP, hP_M, hP_BB, hP_BM, hP_RP, hX5;
    repeat match goal with H : _ \/ _ |- _ => hide H end.
  (* [comment removed for export] *)
  Local Ltac nums :=
    acb;
    pose proof BLW as hBLW; unfold B64F_below, BIO_SIZE, B64CTX_SIZE in hBLW;
    pose proof MBW as hMBW; unfold MEMBIO_below, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in hMBW;
    pose proof RBc as hRBc; unfold ablock_range, B64CTX_SIZE, AFS_SIZE, AIMG_TOP in hRBc; destruct hRBc as (hRBc1 & hRBc2 & _ & hRBc3 & hRBc4 & hRBc5 & hRBc6);
    pose proof RBe as hRBe; unfold ablock_range, AFS_SIZE, AIMG_TOP in hRBe; destruct hRBe as (hRBe1 & hRBe2 & _ & hRBe3 & hRBe4 & hRBe5 & hRBe6);
    pose proof RBa as hRBa; unfold ablock_range, BIO_SIZE, AFS_SIZE, AIMG_TOP in hRBa; destruct hRBa as (hRBa1 & hRBa2 & _ & hRBa3 & hRBa4 & hRBa5 & hRBa6);
    pose proof MRB as hMRB; unfold ablock_range, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, AFS_SIZE, AIMG_TOP in hMRB;
    destruct hMRB as ((hM1 & _ & _ & hM3 & hM4 & hM5 & hM6) & (hBB1 & _ & _ & hBB3 & hBB4 & hBB5 & hBB6) & (hBM1 & _ & _ & hBM3 & hBM4 & hBM5 & hBM6) & (hRP1 & _ & _ & hRP3 & hRP4 & hRP5 & hRP6));
    hide hRBc4; hide hRBe4; hide hRBa4; hide hM4; hide hBB4; hide hBM4; hide hRP4;
    hide hRBc5; hide hRBe5; hide hRBa5; hide hM5; hide hBB5; hide hBM5; hide hRP5;
    pose proof LOS as hLOS;
    assert (hLOSr : lo <= fb - BIOREAD_STACK) by (clear - hLOS; lia);
    assert (hLOSu : lo <= fb - DECUPDATE_STACK) by (clear - hLOS; lia);
    assert (hLOSf : lo <= fb - DECFINAL_STACK) by (clear - hLOS; lia);
    assert (hLOSi : lo <= fb - DECINIT_STACK) by (clear - hLOS; lia);
    assert (hLOSm : lo <= fb - 4096) by (clear - hLOS; unfold AINTRIN_STACK in hLOS; lia);
    assert (hLOS0 : lo <= fb) by (clear - hLOSm; lia);
    clear hLOS;
    pose proof aceil_range as hACR; assert (LO0 : 0 <= lo) by (clear - CEIL hACR; lia);
    pose proof (fresh_frame_facts H [] 0 ff fp (conj FFR (conj FSBOK (fun f (Hf : In f []) => match Hf with end)))) as hFF;
    change (fsz 0) with 64 in hFF; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AFS_FLAGS in hFF;
    destruct hFF as (_ & hFF1 & hFF2 & hFF64 & hFF8 & _ & _ & _ & _ & hFSB1 & hFSB2 & _ & _ & hAPF);
    pose proof TL as hTL; unfold zlength in hTL.
  (* [comment removed for export] *)
  Local Ltac covtac :=
    unfold WL', ENCCTX_foot, MEMBIO_foot, ENCCTX_SIZE, BIO_SIZE, BUFMEM_SIZE; cbn [mb_bm mset app];
    repeat (apply Forall_cons); try apply Forall_nil; unfold covered; cbn [fst snd];
    first [ left; match goal with HL : lo <= fb |- _ => clear - HL FBT end; lia
          | left; match goal with HM : lo <= fb - 4096 |- _ => clear - HM FBT end; lia
          | right; repeat (first [ apply Exists_cons_hd; cbn [fst snd]; djak | apply Exists_cons_tl ]) ].

  (* [comment removed for export] *)
  Local Ltac extc MU WM MUc WMc XSc :=
    lazymatch type of MU with munch (FP ?XS) ?mz ?ma =>
    lazymatch type of MUc with munch ((?loc, ?hic) :: XSc ++ ?Wc) ma ?mb =>
      let T := fresh "MUx" in
      assert (T : munch (FP (XSc ++ XS)) mz mb)
        by (unfold FP in MU |- *; eapply (munch_join _ _ _ _ _ _ MU MUc); [apply sub_fp_grow| apply sub_fp_callee; [clear - LOS FBT; lia| covtac]]);
      clear MU MUc; rename T into MU;
      let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM WMc; rename T2 into WM
    end end.
  (* [comment removed for export] *)
  Local Ltac extw MU WM MUc WMc :=
    lazymatch type of MU with munch (FP ?XS) ?mz ?ma =>
    lazymatch type of MUc with munch ?Wc ma ?mb =>
      let T := fresh "MUx" in
      assert (T : munch (FP XS) mz mb)
        by (unfold FP in MU |- *; eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc]; apply sub_fp_covered; covtac);
      clear MU MUc; rename T into MU;
      let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM WMc; rename T2 into WM
    end end.

  (* [comment removed for export] *)
  Definition HINV (m : mem) (used : nat) (d acc : list Z) (fl nr c vnum : Z) (XS : list (Z * Z)) (w216 w224 : word)
      (jb jt jo : list byte) : Prop :=
       rw_cells asegs m (fb + 8) (ardslots ctx ff ff (zlength acc) mb a (ff + 32) (Z_to_bv 64 (out0 + zlength acc)) (Z_to_bv 64 (outl0 - zlength acc))
                                          j136 j152 w216 w224 (Z_to_bv 64 0) j256)
    /\ rw_cells asegs m ctx (rdhdr 0 0 0 c enc)
    /\ rw_cells asegs m (ctx + 40) [CB 1502 jb] /\ rw_cells asegs m (ctx + 1542) [CB 1024 jt]
    /\ ENCCTX H LB m enc d (bf_eid R)
    /\ MEMBIO H LB m mb (mset M0 (Z.of_nat used) fl nr)
    /\ bytes_at asegs m (mb_buf M0) txt
    /\ rw_cells asegs m out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
    /\ rw_cells asegs m (ff + 32) [C4 (wz vnum)]
    /\ B64TAB m /\ mem_inv asegs m /\ stk asegs m lo fb
    /\ ACONST m /\ as_RFS H LFb m /\ arelro_lib m /\ as_RHEAP H s LB m
    /\ Forall (fs_scratch H LFb) XS /\ munch (FP XS) m0 m /\ wmono asegs m0 m.

  (* [comment removed for export] *)
  Definition HEADMS (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
    MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20))
             s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
       F (Z_to_bv 64 ARD_HEAD) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition EXITQ (res : b64r_res) : machine_state -> Prop := fun ms' =>
    exists m' (rcf c' fl' nr' bl' bo' vnum : Z) (d' : list Z) (XS : list (Z * Z)) (w104 w128 w216 w224 : word) (jb' jt' jo' : list byte)
           (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
         ms' = MS (mkR ra' (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ARD_EXIT) fc None m' (seg_rom asegs)
      /\ br_rv res = (if zlength (br_out res) =? 0 then rcf else zlength (br_out res))
      /\ (rcf = 0 \/ rcf = -1) /\ (c' <= 0 \/ 0 < zlength (br_out res)) /\ - 2^31 <= c' < 2^31
      /\ zlength (br_out res) <= outl0 /\ (br_used res <= length txt)%nat /\ 0 <= fl' < 2^31
      /\ rw_cells asegs m' (fb + 8) (ardslots ctx ff ff (zlength (br_out res)) mb a (ff + 32) w104 w128 j136 j152 w216 w224 (Z_to_bv 64 rcf) j256)
      /\ rw_cells asegs m' ctx (rdhdr bl' bo' 0 c' enc)
      /\ rw_cells asegs m' (ctx + 40) [CB 1502 jb'] /\ rw_cells asegs m' (ctx + 1542) [CB 1024 jt']
      /\ ENCCTX H LB m' enc d' (bf_eid R)
      /\ MEMBIO H LB m' mb (mset M0 (Z.of_nat (br_used res)) fl' nr')
      /\ bytes_at asegs m' (mb_buf M0) txt
      /\ rw_cells asegs m' out0 [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl0 - length (br_out res)) jo']
      /\ rw_cells asegs m' (ff + 32) [C4 (wz vnum)]
      /\ B64TAB m' /\ mem_inv asegs m' /\ stk asegs m' lo fb
      /\ ACONST m' /\ as_RFS H LFb m' /\ arelro_lib m' /\ as_RHEAP H s LB m'
      /\ Forall (fs_scratch H LFb) XS /\ munch (FP XS) m0 m' /\ wmono asegs m0 m'.

  (* [comment removed for export] *)
  Definition READQ (used : nat) (d acc : list Z) (c : Z) (n : Z) : machine_state -> Prop := fun ms' =>
    exists m1 (fl nr vnum : Z) (XS : list (Z * Z)) (w216 w224 : word) (jb jt jo : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 t3 t4 t5 t6 : word),
         ms' = MS (mkR (Z_to_bv 64 ARD_RA_READ) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                  F (Z_to_bv 64 ARD_RA_READ) fc None m1 (seg_rom asegs)
      /\ n = Z.min 1024 (zlength txt - Z.of_nat used) /\ 0 <= fl < 2^31 /\ Z.land fl 8 = 0
      /\ rw_cells asegs m1 (fb + 8) (ardslots ctx ff ff (zlength acc) mb a (ff + 32) (Z_to_bv 64 (out0 + zlength acc)) (Z_to_bv 64 (outl0 - zlength acc))
                                         j136 j152 w216 w224 (Z_to_bv 64 0) j256)
      /\ rw_cells asegs m1 ctx (rdhdr 0 0 0 c enc)
      /\ rw_cells asegs m1 (ctx + 40) [CB 1502 jb]
      /\ rw_cells asegs m1 (ctx + 1542) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn used txt)); CB (1024 - Z.to_nat n) jt]
      /\ ENCCTX H LB m1 enc d (bf_eid R)
      /\ MEMBIO H LB m1 mb (mset M0 (Z.of_nat used + n) fl nr)
      /\ bytes_at asegs m1 (mb_buf M0) txt
      /\ rw_cells asegs m1 out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
      /\ rw_cells asegs m1 (ff + 32) [C4 (wz vnum)]
      /\ B64TAB m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo fb
      /\ ACONST m1 /\ as_RFS H LFb m1 /\ arelro_lib m1 /\ as_RHEAP H s LB m1
      /\ Forall (fs_scratch H LFb) XS /\ munch (FP XS) m0 m1 /\ wmono asegs m0 m1.

  (* [comment removed for export] *)
  Definition DUQ (used : nat) (d acc : list Z) (c : Z) (n : Z) : machine_state -> Prop := fun ms' =>
    let data := firstn (Z.to_nat n) (skipn used txt) in
    let r := decode_update d (map bv_unsigned data) in
    exists m3 (fl nr vnum : Z) (XS : list (Z * Z)) (w216 w224 : word) (jb jt jo : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
         ms' = MS (mkR (Z_to_bv 64 ARD_RA_DU) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 (dr_rv r)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n)
                       (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                  F (Z_to_bv 64 ARD_RA_DU) fc None m3 (seg_rom asegs)
      /\ n = Z.min 1024 (zlength txt - Z.of_nat used) /\ length data = Z.to_nat n /\ 0 <= fl < 2^31 /\ (length (dr_out r) <= 1502)%nat
      /\ rw_cells asegs m3 (fb + 8) (ardslots ctx ff ff (zlength acc) mb a (ff + 32) (Z_to_bv 64 (out0 + zlength acc)) (Z_to_bv 64 (outl0 - zlength acc))
                                         j136 j152 w216 w224 (Z_to_bv 64 0) j256)
      /\ rw_cells asegs m3 ctx (rdhdr (zlength (dr_out r)) 0 0 c enc)
      /\ rw_cells asegs m3 (ctx + 40) [CB (length (dr_out r)) (map b8 (dr_out r)); CB (1502 - length (dr_out r)) jb]
      /\ rw_cells asegs m3 (ctx + 1542) [CB (Z.to_nat n) data] /\ rw_cells asegs m3 (ctx + 1542 + n) [CB (1024 - Z.to_nat n) jt]
      /\ ENCCTX H LB m3 enc (dr_d r) (bf_eid R)
      /\ MEMBIO H LB m3 mb (mset M0 (Z.of_nat used + n) fl nr)
      /\ bytes_at asegs m3 (mb_buf M0) txt
      /\ rw_cells asegs m3 out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
      /\ rw_cells asegs m3 (ff + 32) [C4 (wz vnum)]
      /\ B64TAB m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo fb
      /\ ACONST m3 /\ as_RFS H LFb m3 /\ arelro_lib m3 /\ as_RHEAP H s LB m3
      /\ Forall (fs_scratch H LFb) XS /\ munch (FP XS) m0 m3 /\ wmono asegs m0 m3.

  (* [comment removed for export] *)
  Definition TRIPQ (used : nat) (d acc : list Z) (n : Z) : machine_state -> Prop := fun ms' =>
    let chunk := firstn 1024 (skipn used TXT) in
    let r := decode_update d chunk in
    let used' := (used + length chunk)%nat in
    let i := Z.min (zlength (dr_out r)) (outl0 - zlength acc) in
    let acc' := acc ++ firstn (Z.to_nat i) (dr_out r) in
       (dr_rv r < 0 /\ EXITQ (mkBR (if zlength acc =? 0 then 0 else zlength acc) acc used') ms')
    \/ (0 <= dr_rv r /\ i = outl0 - zlength acc /\ EXITQ (mkBR (zlength acc + i) acc' used') ms')
    \/ (0 <= dr_rv r /\ i < outl0 - zlength acc
        /\ (length (dr_d r) = 0%nat \/ Nat.modulo (length (dr_d r)) 4 <> 0%nat)
        /\ exists m' (fl' nr' vnum' : Z) (XS' : list (Z * Z)) (w216 w224 : word) (jb' jt' jo' : list byte)
                  (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word),
             ms' = HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 m'
          /\ HINV m' used' (dr_d r) acc' fl' nr' (dr_rv r) vnum' XS' w216 w224 jb' jt' jo').

  (* [comment removed for export] *)
  Hypothesis RFS0 : as_RFS H LFb m0.

  (* [comment removed for export] *)
  Lemma appwin_WL' : Forall appwin WL'.
  Proof.
    nums. unfold WL', appwin.
    pose proof OSH0 as (_ & _ & IAo & _).
    unhide hRBc5. unhide hRBe5. unhide hM5. unhide hBM5.
    pose proof (aapp_not_shadowland _ _ hRBc6) as N1. pose proof (aapp_not_shadowland _ _ hRBe6) as N2.
    pose proof (aapp_not_shadowland _ _ hM6) as N3. pose proof (aapp_not_shadowland _ _ hBM6) as N4.
    pose proof (fresh_frame_facts H [] 0 ff fp (conj FFR (conj FSBOK (fun f (Hf : In f []) => match Hf with end)))) as hFF.
    change (fsz 0) with 64 in hFF. destruct hFF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q1 & Q2 & _ & _ & APF).
    pose proof (aapp_not_shadowland _ _ APF) as N5.
    unfold ALOWSH_LO, AFS_SIZE, AFS_HDR in *. rewrite ASHADOW_BASE_val.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - revert IAo. unfold in_app_mem. rewrite ASHADOW_BASE_val. clear. intros. lia.
    - clear - N1. lia.
    - clear - N2. lia.
    - clear - N3. lia.
    - clear - N4. lia.
    - clear - N5 Q1 Q2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma disjoint_img_scratch : forall XS O n, O + n <= AIMG_TOP -> Forall (fs_scratch H LFb) XS -> disjoint_from XS O n.
  Proof.
    intros XS O n HO FX. eapply disjoint_from_Forall; [exact FX|]. intros iv [->|(k & ff' & fp' & FF & E)]; cbn [fst snd].
    - left. pose proof FSBOK as (F1 & _). exact (Z.le_trans _ _ _ HO F1).
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & _ & _ & P1 & _).
      pose proof (fsz_pos k ltac:(lia)).
      destruct E as [->|[->| ->]]; cbn [fst snd]; left; unfold AFS_HDR, AFS_FLAGS in *; try lia.
      unfold sh. rewrite ASHADOW_BASE_val. unfold AIMG_TOP in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma shad_now : forall m XS,
    Forall (fs_scratch H LFb) XS -> munch (FP XS) m0 m -> wmono asegs m0 m ->
       B64F_shad m a R /\ MEMBIO_shad m mb M0 /\ PAYLOAD_shad m M0 /\ OUT_shad m out0 outl0 /\ shvis m ctx (ctx + B64CTX_SIZE)
    /\ rw_cells asegs m (sh ff) b64rd_shpat /\ METH_mem m /\ rw_cells asegs m a (bio_cells B0).
  Proof.
    intros m XS FX MU WM. nums. facts. unfold FP in MU. pose proof appwin_WL' as AW.
    destruct BSH0 as (Sa & Sc & Se). destruct MBSH0 as (Sm & Sbb & Sbm & Srp). destruct PAY0 as (Pa & Pv & Pi). destruct OSH0 as (Oa & Ov & Oi & Ok).
    (* [comment removed for export] *)
    unhide hRBa5. unhide hRBc5. unhide hRBe5. unhide hM5. unhide hBB5. unhide hBM5. unhide hRP5.
    assert (Fa : fsobj H LFb a 128) by (apply fsobj_outside; unfold AFS_SIZE; clear - hRBa5; lia).
    assert (Fc : fsobj H LFb ctx 2584) by (apply fsobj_outside; unfold AFS_SIZE; clear - hRBc5; lia).
    assert (Fe : fsobj H LFb enc 92) by (apply fsobj_outside; unfold AFS_SIZE; clear - hRBe5; lia).
    assert (Fm : fsobj H LFb mb 128) by (apply fsobj_outside; unfold AFS_SIZE; clear - hM5; lia).
    assert (Fbb : fsobj H LFb (mb_bb M0) 16) by (apply fsobj_outside; unfold AFS_SIZE; clear - hBB5; lia).
    assert (Fbm : fsobj H LFb (mb_bm M0) 32) by (apply fsobj_outside; unfold AFS_SIZE; clear - hBM5; lia).
    assert (Frp : fsobj H LFb (mb_rp M0) 32) by (apply fsobj_outside; unfold AFS_SIZE; clear - hRP5; lia).
    pose proof (aapp_bounds _ _ hRBa6 ltac:(lia)) as (_ & _ & Ta & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
    pose proof (aapp_bounds _ _ hRBe6 ltac:(lia)) as (_ & _ & Te & _). pose proof (aapp_bounds _ _ hM6 ltac:(lia)) as (_ & _ & Tm & _).
    pose proof (aapp_bounds _ _ hBB6 ltac:(lia)) as (_ & _ & Tbb & _). pose proof (aapp_bounds _ _ hBM6 ltac:(lia)) as (_ & _ & Tbm & _).
    pose proof (aapp_bounds _ _ hRP6 ltac:(lia)) as (_ & _ & Trp & _).
    assert (To : 0 <= out0 /\ out0 + outl0 <= AAPP_HI) by (destruct Oa as (? & ? & _); lia).
    assert (Tp : 0 <= mb_buf M0 /\ mb_buf M0 + mb_len M0 <= AAPP_HI) by (destruct Pa as (? & ? & _); lia).
    unfold B64F_shad, MEMBIO_shad, PAYLOAD_shad, OUT_shad, BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
    repeat lazymatch goal with |- _ /\ _ => split end.
    - eapply (addressable_across3 H HH); [exact Sa| exact RFS0| exact Fa| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Sc| exact RFS0| exact Fc| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Se| exact RFS0| exact Fe| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Sm| exact RFS0| exact Fm| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Sbb| exact RFS0| exact Fbb| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Sbm| exact RFS0| exact Fbm| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (addressable_across3 H HH); [exact Srp| exact RFS0| exact Frp| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (accessible_across3 H HH); [exact Pa| exact RFS0| exact OBpay| lia| exact MU| exact CEIL| exact FX| exact AW].
    - eapply (shvis_across3 H HH); [exact Pv| exact RFS0| exact OBpay| lia| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - exact Pi.
    - eapply (accessible_across3 H HH); [exact Oa| exact RFS0| exact OBout| lia| exact MU| exact CEIL| exact FX| exact AW].
    - eapply (shvis_across3 H HH); [exact Ov| exact RFS0| exact OBout| lia| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - exact Oi.
    - exact Ok.
    - eapply (shvis_across3 H HH LFb ctx 2584); [exact CSV0| exact RFS0| exact Fc| lia| lia| lia| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - eapply (shpat_across3 H HH); [exact SHP0| exact RFS0| left; reflexivity| exact MU| exact WM| exact CEIL| exact FX| exact AW].
    - unfold METH_mem in METH0 |- *. eapply rw_cells_transport; [exact METH0| exact MU| exact WM|].
      cbn [cells_size csize Nat.add]. split; [unfold A_mem_buf_method, O_METH_BREAD; cbn; lia|]. apply disjoint_from_app. split.
      + apply disjoint_img_scratch; [unfold A_mem_buf_method, O_METH_BREAD, AIMG_TOP; cbn; lia| exact FX].
      + unhide hX5. unfold WL', A_mem_buf_method, O_METH_BREAD in *. cbn. unfold AIMG_TOP, AFS_HDR in *. clear - hX5 hRBc3 hRBe3 hM3 hBM3 hFF1. lia.
    - eapply (rw_cells_across3 H HH); [exact AH0| exact RFS0| | clear - hRBa1; lia| | | | exact MU| exact WM| exact FX|];
        cbn [cells_size csize Nat.add bio_cells Z.of_nat Pos.of_succ_nat Pos.succ]; [exact Fa| clear - Ta; lia| exact hRBa6| clear - hBLW; lia|].
      unfold WL'. unhide hO_A. unhide hAC. unhide hAE. unhide hA_M. unhide hA_BM. cbn. unfold AFS_HDR, AFS_SIZE in *. clear - hO_A hAC hAE hA_M hA_BM hRBa5 FFR.
      destruct FFR as (_ & G1 & G2 & _). change (fsz 0) with 64 in G2. unfold AFS_HDR, AFS_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FOBJ : fsobj H LFb a 128 /\ fsobj H LFb ctx 2584 /\ fsobj H LFb enc 92 /\ fsobj H LFb mb 128
            /\ fsobj H LFb (mb_bb M0) 16 /\ fsobj H LFb (mb_bm M0) 32 /\ fsobj H LFb (mb_rp M0) 32 /\ fsobj H LFb ff 64.
  Proof.
    nums. unhide hRBa5. unhide hRBc5. unhide hRBe5. unhide hM5. unhide hBB5. unhide hBM5. unhide hRP5.
    split; [apply fsobj_outside; unfold AFS_SIZE; clear - hRBa5; lia|]. split; [apply fsobj_outside; unfold AFS_SIZE; clear - hRBc5; lia|].
    split; [apply fsobj_outside; unfold AFS_SIZE; clear - hRBe5; lia|]. split; [apply fsobj_outside; unfold AFS_SIZE; clear - hM5; lia|].
    split; [apply fsobj_outside; unfold AFS_SIZE; clear - hBB5; lia|]. split; [apply fsobj_outside; unfold AFS_SIZE; clear - hBM5; lia|].
    split; [apply fsobj_outside; unfold AFS_SIZE; clear - hRP5; lia|].
    eapply fsobj_inframe; [left; reflexivity| cbn; clear; lia| cbn; change (fsz 0) with 64; clear; lia].
  Qed.

  (* [comment removed for export] *)
  Definition okw (iv : Z * Z) : Prop := covered (aceil, 2^64) WL' iv.
  Lemma okw_laws : forall iv, okw iv -> aconst_ok iv /\ afs_write_ok H LFb iv /\ (snd iv <= 0x571000 \/ 0x5ea000 <= fst iv) /\ aclient_write_ok H LB iv.
  Proof.
    intros [l h] OK. nums. destruct OSH0 as (_ & _ & _ & Ok). destruct INmb as [INm INbm].
    pose proof (fresh_frame_facts H [] 0 ff fp (conj FFR (conj FSBOK (fun f (Hf : In f []) => match Hf with end)))) as hFF.
    change (fsz 0) with 64 in hFF. destruct hFF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q1 & Q2 & Q3 & Q4 & APF).
    unhide hRBc5. unhide hRBe5. unhide hM5. unhide hBM5.
    unfold okw, covered, WL' in OK. cbn [fst snd] in OK.
    assert (CASES : aceil <= l \/ (out0 <= l /\ h <= out0 + outl0) \/ (ctx <= l /\ h <= ctx + 2566) \/ (enc <= l /\ h <= enc + 92)
                    \/ (mb <= l /\ h <= mb + 128) \/ (mb_bm M0 <= l /\ h <= mb_bm M0 + 32) \/ (ff + 32 <= l /\ h <= ff + 36)).
    { destruct OK as [OK|OK]; [left; clear - OK; lia| right].
      repeat (apply Exists_cons in OK; destruct OK as [OK|OK]; [cbn [fst snd] in OK; first [left; exact OK| exact OK] | first [right| idtac]]).
      inversion OK. }
    clear OK. cbn [fst snd]. unfold afs_write_ok, aclient_write_ok. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP, AFS_SIZE, AFS_HDR in *.
    destruct CASES as [K|[K|[K|[K|[K|[K|K]]]]]].
    - split; [apply aconst_ok_high; cbn; [| right; left]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear - K hACR; lia.. |].
      split; [left; clear - K Q4 hACR; lia|]. split; [right; clear - K hACR; lia|]. left. exact K.
    - split; [intros x Hx; apply Ok; cbn in Hx |- *; clear - K Hx; lia|].
      split; [destruct AWout as [AW|(f & INf & AW1 & AW2)]; [left; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in AW; cbn in AW |- *; clear - K AW; lia| right; exists f; split; [right; exact INf| cbn in *; clear - K AW1 AW2; lia]]|].
      split; [right; clear - K OUTTOP; lia|].
      destruct ACWout as [C|[C|[C|[C|C]]]]; [left; cbn in *; clear - K C; lia| right; left; revert C; unfold aimg_client_w; cbn; clear - K; intros; lia
        | right; right; left; destruct C as (b & INb & C1 & C2); exists b; split; [exact INb| cbn in *; clear - K C1 C2; lia]
        | right; right; right; left; destruct C as (b & INb & C1 & C2); exists b; split; [exact INb| cbn in *; clear - K C1 C2; lia]
        | right; right; right; right; unfold AFS_SIZE, AHI_LO in *; cbn in *; clear - K C; lia].
    - split; [eapply aconst_ok_aapp; [exact hRBc6| clear - K; lia| clear - K; lia]|].
      split; [left; clear - K hRBc3 hRBc5; lia|]. split; [right; clear - K hRBc3; lia|].
      right; right; left. exists (bf_cid R, ctx, B64CTX_SIZE). split; [exact INc| cbn; unfold B64CTX_SIZE; clear - K; lia].
    - split; [eapply aconst_ok_aapp; [exact hRBe6| clear - K; lia| clear - K; lia]|].
      split; [left; clear - K hRBe3 hRBe5; lia|]. split; [right; clear - K hRBe3; lia|].
      right; right; left. exists (bf_eid R, enc, ENCCTX_SIZE). split; [exact INe| cbn; unfold ENCCTX_SIZE; clear - K; lia].
    - split; [eapply aconst_ok_aapp; [exact hM6| clear - K; lia| clear - K; lia]|].
      split; [left; clear - K hM3 hM5; lia|]. split; [right; clear - K hM3; lia|].
      right; right; left. exists (mb_id M0, mb, BIO_SIZE). split; [exact INm| cbn; unfold BIO_SIZE; clear - K; lia].
    - split; [eapply aconst_ok_aapp; [exact hBM6| clear - K; lia| clear - K; lia]|].
      split; [left; clear - K hBM3 hBM5; lia|]. split; [right; clear - K hBM3; lia|].
      right; right; left. exists (mb_bmid M0, mb_bm M0, BUFMEM_SIZE). split; [exact INbm| cbn; unfold BUFMEM_SIZE; clear - K; lia].
    - split; [eapply aconst_ok_aapp; [exact APF| clear - K Q1 Q2; lia| clear - K Q1 Q2; lia]|].
      split; [right; exists (0, ff, fp); split; [left; reflexivity| cbn; change (fsz 0) with 64; clear - K; lia]|].
      split; [right; clear - K hFF1; lia|].
      right; right; right; right; left. clear - K Q1 Q2. lia.
  Qed.

  Lemma rt_frame : forall W m m', ACONST m -> as_RFS H LFb m -> arelro_lib m -> as_RHEAP H s LB m ->
    munch W m m' -> wmono asegs m m' -> Forall okw W ->
    ACONST m' /\ as_RFS H LFb m' /\ arelro_lib m' /\ as_RHEAP H s LB m'.
  Proof.
    intros W m m' AC RFS RL RH MU WM FW.
    split; [| split; [| split]].
    - eapply ACONST_frame; [exact AC| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj1 (okw_laws iv Hiv)).
    - eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj1 (proj2 (okw_laws iv Hiv))).
    - eapply arelro_across7; [exact RL| exact MU|]. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj1 (proj2 (proj2 (okw_laws iv Hiv)))).
    - eapply (ah_RHEAP_frame H HH); [exact RH| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj2 (proj2 (proj2 (okw_laws iv Hiv)))).
  Qed.
  Lemma okw_acw : forall W, Forall okw W -> Forall (aclient_write_ok H LB) W.
  Proof. intros W FW. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj2 (proj2 (proj2 (okw_laws iv Hiv)))). Qed.
  Lemma okw_afs : forall W, Forall okw W -> Forall (afs_write_ok H LFb) W.
  Proof. intros W FW. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj1 (proj2 (okw_laws iv Hiv))). Qed.
  Lemma okw_aconst : forall W, Forall okw W -> Forall aconst_ok W.
  Proof. intros W FW. eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (proj1 (okw_laws iv Hiv)). Qed.
  (* [comment removed for export] *)
  Local Ltac okwtac :=
    unfold ENCCTX_foot, MEMBIO_foot, ENCCTX_SIZE, BIO_SIZE, BUFMEM_SIZE; cbn [mb_bm mset app];
    repeat (apply Forall_cons); try apply Forall_nil; unfold okw, covered, WL'; cbn [fst snd];
    first [ left; match goal with HL : lo <= fb |- _ => clear - CEIL HL FBT SPT end; lia
          | left; match goal with HM : lo <= fb - 4096 |- _ => clear - CEIL HM FBT SPT end; lia
          | right; repeat (first [ apply Exists_cons_hd; cbn [fst snd]; djak | apply Exists_cons_tl ]) ].

  (* [comment removed for export] *)
  Local Ltac solve_fsobj Fa Fc Fe Fm Fbb Fbm Frp Fff :=
    lazymatch goal with |- fsobj _ _ ?O _ =>
      match O with
      | context [bf_ctx R] => eapply fsobj_sub; [exact Fc| djak| djak]
      | context [bf_enc R] => eapply fsobj_sub; [exact Fe| djak| djak]
      | context [mb_bb M0] => eapply fsobj_sub; [exact Fbb| djak| djak]
      | context [mb_bm M0] => eapply fsobj_sub; [exact Fbm| djak| djak]
      | context [mb_rp M0] => eapply fsobj_sub; [exact Frp| djak| djak]
      | context [mb_buf M0] => eapply fsobj_sub; [exact OBpay| djak| djak]
      | context [out0] => eapply fsobj_sub; [exact OBout| djak| djak]
      | context [ff] => eapply fsobj_sub; [exact Fff| djak| djak]
      | context [mb] => eapply fsobj_sub; [exact Fm| djak| djak]
      | context [a] => eapply fsobj_sub; [exact Fa| djak| djak]
      end end.
  Local Ltac solve_aapp :=
    lazymatch goal with |- aapp ?O _ =>
      match O with
      | context [bf_ctx R] => eapply aapp_sub; [match goal with Hx : aapp (bf_ctx R) _ |- _ => exact Hx end| djak| djak]
      | context [bf_enc R] => eapply aapp_sub; [match goal with Hx : aapp (bf_enc R) _ |- _ => exact Hx end| djak| djak]
      | context [mb_bb M0] => eapply aapp_sub; [match goal with Hx : aapp (mb_bb M0) _ |- _ => exact Hx end| djak| djak]
      | context [mb_bm M0] => eapply aapp_sub; [match goal with Hx : aapp (mb_bm M0) _ |- _ => exact Hx end| djak| djak]
      | context [mb_rp M0] => eapply aapp_sub; [match goal with Hx : aapp (mb_rp M0) _ |- _ => exact Hx end| djak| djak]
      | context [ff] => eapply aapp_sub; [match goal with Hx : aapp (as_FSB H) _ |- _ => exact Hx end| unfold AFS_HDR, AFS_SIZE in *; djak| unfold AFS_HDR, AFS_SIZE in *; djak]
      | context [mb] => eapply aapp_sub; [match goal with Hx : aapp mb _ |- _ => exact Hx end| djak| djak]
      | context [a] => eapply aapp_sub; [match goal with Hx : aapp a _ |- _ => exact Hx end| djak| djak]
      end end.
  Local Ltac unhide_tops := repeat match goal with Ht : hidden (_ <= aceil) |- _ => unhide Ht end; pose proof aceil_range.
  (* [comment removed for export] *)
  Local Ltac djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff :=
    cbn [cells_size csize length map app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ rdhdr ardslots bio_cells buf_cells mb_bb mb_bm mb_rp mb_buf mb_len mset];
    lazymatch goal with |- disjoint_from ((_, _) :: ?XSc ++ _) ?A ?n =>
      apply disjoint_from_callee;
      [ dja
      | first [ eapply (disjoint_of_scratch H HH); [exact RFSsrc| solve_fsobj Fa Fc Fe Fm Fbb Fbm Frp Fff| djak| djak| unhide_tops; unfold AAPP_HI; djak| solve_aapp| exact FXc]
              | eapply (disjoint_of_scratch_inapp H HH); [exact RFSsrc| solve_fsobj Fa Fc Fe Fm Fbb Fbm Frp Fff| djak| djak| | | exact FXc];
                [ match goal with Ho : OUT_shad _ out0 outl0 |- _ => destruct Ho as ((? & ? & _) & _ & _); unfold AAPP_HI in *; djak end
                | match goal with Ho : OUT_shad _ out0 outl0 |- _ => destruct Ho as (_ & _ & Hia & _); eapply in_app_mem_sub; [exact Hia| djak| djak] end ]
              | eapply disjoint_from_Forall; [exact FXc|]; let iv := fresh "iv" in let Hiv := fresh "Hiv" in intros iv Hiv;
                pose proof (fs_scratch_below_ceil H HH _ _ _ RFSsrc Hiv); destruct iv; cbn [fst snd] in *; dja
              | apply disjoint_img_scratch; [cbn; djak| exact FXc] ]
      | djs ]
    end.
  Local Ltac carryc MU WM RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff :=
    lazymatch type of MU with
    | munch ?W ?ma ?mb =>
        repeat match goal with
        | H : rw_cells ?segs ma ?A ?cs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff;
                    apply (fun HH => @rw_cells_transport segs W ma mb A cs HH MU WM D) in H; clear D
                  | change (ECH_AKit.stale (rw_cells segs ma A cs)) in H ]
        | H : bytes_at ?segs ma ?A ?bs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (length bs))) by djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff;
                    apply (fun HH => @bytes_at_transport segs W ma mb A bs HH MU D) in H; clear D
                  | change (ECH_AKit.stale (bytes_at segs ma A bs)) in H ]
        | H : ENCCTX ?HI ?LBx ma ?A ?d ?p |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A 92) by djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff;
                    apply (fun HH => @ENCCTX_transport _ HI W ma mb LBx A d p MU WM D HH) in H; clear D
                  | change (ECH_AKit.stale (ENCCTX HI LBx ma A d p)) in H ]
        | H : MEMBIO ?HI ?LBx ma ?A ?M |- _ =>
            first [ let D1 := fresh in let D2 := fresh in let D3 := fresh in let D4 := fresh in
                    assert (D1 : disjoint_from W A BIO_SIZE) by (unfold BIO_SIZE; djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff);
                    assert (D2 : disjoint_from W (mb_bb M) BIOBUFMEM_SIZE) by (unfold BIOBUFMEM_SIZE; djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff);
                    assert (D3 : disjoint_from W (mb_bm M) BUFMEM_SIZE) by (unfold BUFMEM_SIZE; djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff);
                    assert (D4 : disjoint_from W (mb_rp M) BUFMEM_SIZE) by (unfold BUFMEM_SIZE; djc RFSsrc FXc Fa Fc Fe Fm Fbb Fbm Frp Fff);
                    apply (fun HH => @MEMBIO_transport _ HI W ma mb LBx A M MU WM D1 D2 D3 D4 HH) in H; clear D1 D2 D3 D4
                  | change (ECH_AKit.stale (MEMBIO HI LBx ma A M)) in H ]
        | H : B64TAB ma |- _ => clear H
        | H : mem_inv _ ma |- _ => clear H
        end;
        repeat match goal with H : ECH_AKit.stale _ |- _ => clear H end
    end.

  (* [comment removed for export] *)
  Lemma MEMBIO_rehdr : forall W m m' M,
    MEMBIO H LB m mb M -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (mb_bb M) BIOBUFMEM_SIZE -> disjoint_from W (mb_bm M) BUFMEM_SIZE -> disjoint_from W (mb_rp M) BUFMEM_SIZE ->
    rw_cells asegs m' mb (bio_cells (membio_bio M)) -> MEMBIO H LB m' mb M.
  Proof.
    intros W m m' M (H1 & H2 & H3 & H4 & REST) MU WM D2 D3 D4 HDR.
    split; [exact HDR| split; [| split; [| split; [| exact REST]]]].
    - eapply rw_cells_transport; [exact H2| exact MU| exact WM| exact D2].
    - eapply rw_cells_transport; [exact H3| exact MU| exact WM| exact D3].
    - eapply rw_cells_transport; [exact H4| exact MU| exact WM| exact D4].
  Qed.
  Lemma membio_bio_ok : forall m M, MEMBIO H LB m mb M -> bio_ok (membio_bio M).
  Proof.
    intros m M MB. mbnum MB.
    pose proof MB as T; unfold MEMBIO in T;
    cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset] in T.
    destruct T as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RBB & _ & _ & _ & _ & _ & _ & _ & _ & _ & MNF & _ & _ & MNX & MPV).
    destruct RBB as (BB1 & _ & _ & _ & BB4 & _). unfold BIOBUFMEM_SIZE in BB4. pose proof aceil_range as ACR.
    unfold bio_ok, membio_bio; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
    unfold A_mem_buf_method. rewrite MNF. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_pre : forall (used : nat) (d acc : list Z) (m : mem) (fl nr c vnum : Z) (XS : list (Z * Z)) (w216 w224 : word)
      (jb jt jo : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word),
    (used <= length txt)%nat -> zlength acc < outl0 -> 0 < c < 2^31 ->
    HINV m used d acc fl nr c vnum XS w216 w224 jb jt jo ->
    evt asegs (READQ used d acc c (Z.min 1024 (zlength txt - Z.of_nat used)))
      (HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 m).
  Proof.
    intros until t6. intros USED ACC C HI.
    destruct HI as (SL & HD & BUF & TMP & ENC & MB & TXTB & OUTB & NUM & TAB & MI & ST & AC & RFS & ARL & RH & FX & MU & WM).
    nums. facts. mbnum MB. unfold HEADMS. unfold zlength in *.
    destruct FOBJ as (Fa & Fc & Fe & Fm & Fbb & Fbm & Frp & Fff).
    destruct (shad_now _ _ FX MU WM) as (BSH & MBSH & PAY & OSH & CSV & SHP & METH & AHb).
    assert (ACCc : accessible m ctx 2584).
    { destruct BSH as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply ard_head; try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact ACCc.
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - C ACC OUTL0 OUT0 OUTE hRBc1 hRBc2 hBLW hLOS0 SPT FBT CEIL LO0; try lia.
      all: match goal with |- ?G => idtac "HEADPRE:" G end. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & SL1 & HD1).
    carryh MU1 WM1.
    destruct (rt_frame _ _ _ AC RFS ARL RH MU1 WM1 ltac:(okwtac)) as (AC1 & RFS1 & ARL1 & RH1). clear AC RFS ARL RH.
    extw MU WM MU1 WM1.
    (* [comment removed for export] *)
    pose proof BRMS as BRM. unfold bioread_mem_stmt in BRM.
    try clear BSH; try clear MBSH; try clear PAY; try clear OSH; try clear CSV; try clear SHP; try clear METH; try clear AHb; try clear ACCc.
    destruct (shad_now _ _ FX MU WM) as (BSH1 & MBSH1 & PAY1 & OSH1 & CSV1 & SHP1 & METH1 & AHb1).
    assert (OKW1 : okw (ctx + 1542, ctx + 2566)) by (unfold okw, covered, WL'; cbn [fst snd]; right; apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; clear; lia).
    pose proof (okw_laws _ OKW1) as (AOKt & AFSt & _ & ACWt). clear OKW1.
    assert (OSHt : OUT_shad m1 (ctx + 1542) 1024).
    { destruct BSH1 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      split; [eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia|].
      split; [eapply shvis_sub; [exact CSV1| | | | |]; unfold B64CTX_SIZE; clear - hRBc1; lia|].
      split; [eapply aapp_in_app_mem; [exact hRBc6| clear; lia| clear; lia]| replace (ctx + 1542 + 1024) with (ctx + 2566) by (clear; lia); exact AOKt]. }
    eapply evt_cut.
    { eapply BRM with (a := mb) (out := ctx + 1542) (outl := 1024) (R := mset M0 (Z.of_nat used) fl nr) (ds := txt) (junk := jt) (lo := lo) (LB := LB) (LF := LFb);
        clear BRM; try reflexivity; try exact MB; try exact ST1; try exact MI1; try exact METH1; try exact TXTB; try exact TMP; try exact MBW; try exact MSP; try exact CEIL;
        try exact MBSH1; try exact PAY1; try exact OSHt; try exact AC1; try exact RFS1; try exact LFLEN; try exact TP; try (replace (ctx + 1542 + 1024) with (ctx + 2566) by (clear; lia); exact AFSt); try exact OBpay; try exact FB16; try exact ARL1.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_READ; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST1; try exact hLOSr; try exact FB16; try (cbn [mb_buf mb_len mset]; first [exact TXTB | exact hTL]).
      all: lazymatch goal with
           | |- 0 < 1024 < _ => clear; lia
           | |- _ mod 2 = 0 => unfold ARD_RA_READ; clear; reflexivity
           | |- _ <= bf_ctx R + 1542 => unfold AIMG_TOP in *; clear - hRBc3; lia
           | |- athr_cells _ => eapply (ah_thr H HH); exact RH1
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      unfold memrd_out. cbn [mb_buf mb_len mset]. unfold blocks_MEMBIO. cbn [mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset].
      split; [clear - hBLW; lia|]. split; [clear - hRBc1; lia|]. split; [clear -hBLW SPT FBT hLOS0; lia|].
      split. { unhide hC_M. unhide hC_BB. unhide hC_BM. unhide hC_RP. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
               apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
               cbn [blk_addr blk_size fst snd]; clear - hC_M hC_BB hC_BM hC_RP; lia. }
      split; [unhide hP_C; clear - hP_C; lia|].
      unfold A_mem_buf_method, O_METH_BREAD. unfold AIMG_TOP in hRBc3. clear - hRBc3. lia. }
    all: match goal with |- ?G => idtac "BRM-LEFT:" G end.
    cbv beta. intros ms2 (XS2 & FX2 & PO & RFS2 & ARL2). unfold memrd_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & jt' & -> & MU2 & WM2 & MI2 & AC2 & ST2 & MB2 & TXTB2 & TMP2 & _).
    cbn [ms_mem] in RFS2, ARL2.
    rewrite ?unsigned_lit in MU2 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST2 by (clear - SPT FBT hLOS0 LO0; lia).
    cbn [mb_buf mset] in TXTB2. unfold MEMBIO_foot in MU2. cbn [mb_bm mset] in MU2.
    assert (RH2 : as_RHEAP H s LB m2).
    { eapply (RHEAP_after_scratch H HH); [exact RH1| exact MU2| exact WM2| exact CEIL| exact FX2|]. apply okw_acw. okwtac. }
    clear TXTB MI1 METH1 TMP MB.
    carryc MU2 WM2 RFS1 FX2 Fa Fc Fe Fm Fbb Fbm Frp Fff.
    extc MU WM MU2 WM2 XS2.
    pose proof (Forall_app_scratch _ _ _ FX2 FX) as FX'.
    set (n := mb_rdn (mset M0 (Z.of_nat used) fl nr) 1024) in *.
    assert (EN : n = Z.min 1024 (Z.of_nat (length txt) - Z.of_nat used)).
    { subst n. unfold mb_rdn, mb_avail. cbn [mb_len mb_pos mset]. clear - hTL. lia. }
    clearbody n. subst n.
    rewrite mb_after_read_mset in MB2. unfold mb_take in TMP2. cbn [mb_pos mset] in TMP2. rewrite Nat2Z.id in TMP2.
    assert (NB : 0 <= Z.min 1024 (Z.of_nat (length txt) - Z.of_nat used) <= Z.of_nat (length txt) - Z.of_nat used) by (clear - USED; lia).
    rewrite length_firstn, length_skipn, Nat.min_l in TMP2 by (clear - NB USED; lia).
    change (Z.to_nat 1024) with 1024%nat in TMP2.
    mbnum MB2.
    replace (ret_pc (Z_to_bv 64 ARD_RA_READ)) with (Z_to_bv 64 ARD_RA_READ) by (symmetry; apply ret_pc_even; [unfold ARD_RA_READ; clear; lia| reflexivity]).
    apply evt_done. unfold READQ.
    eexists m2, _, _, vnum, (XS2 ++ XS), w216, w224, jb, _, jo. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MBF0|]. split; [apply land_lnot15_8|].
    split; [exact SL1|]. split; [exact HD1|]. split; [exact BUF|]. split; [exact TMP2|]. split; [exact ENC|].
    split; [exact MB2|]. split; [exact TXTB2|]. split; [exact OUTB|]. split; [exact NUM|].
    split; [exact (B64TAB_of_mem_inv _ MI2)|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact AC2|]. split; [exact RFS2|]. split; [exact ARL2|]. split; [exact RH2|].
    split; [exact FX'|]. split; [exact MU| exact WM].
    all: match goal with |- ?G => idtac "RDPRE-LEFT:" G end.
  Qed.

  Lemma rd_trip_eof : forall (used : nat) (d acc : list Z) (c : Z) ms,
    (used = length txt)%nat -> zlength acc < outl0 -> (length d = 0%nat \/ Nat.modulo (length d) 4 <> 0%nat) ->
    READQ used d acc c 0 ms ->
    evt asegs (EXITQ (mkBR (if zlength acc =? 0 then (if decode_final_rv d <? 0 then -1 else 0) else zlength acc) acc used)) ms.
  Proof.
    intros used d acc c ms USED ACC DMOD RQ. unfold READQ in RQ.
    destruct RQ as (m1 & fl & nr & vnum & XS & w216 & w224 & jb & jt & jo & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s8 & s9 & s10 & t3 & t4 & t5 & t6
                    & -> & EN & FLR1 & FL8 & SL & HD & BUF & TMP & ENC & MB & TXTB & OUTB & NUM & TAB & MI & ST & AC & RFS & ARL & RH & FX & MU & WM).
    nums. facts. rewrite Z.add_0_r in MB. mbnum MB. unfold zlength in *.
    destruct FOBJ as (Fa & Fc & Fe & Fm & Fbb & Fbm & Frp & Fff).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply ard_eof1; try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL.
      all: unfold B64CTX_SIZE; clear - hRBc1 hBLW hLOS0 SPT FBT LO0; try lia.
      all: match goal with |- ?G => idtac "EOF1PRE:" G end. }
    cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ST2 & SL2 & HD2). clear SL HD ST.
    carryh MU2 WM2.
    destruct (rt_frame _ _ _ AC RFS ARL RH MU2 WM2 ltac:(okwtac)) as (AC2 & RFS2 & ARL2 & RH2). clear AC RFS ARL RH.
    extw MU WM MU2 WM2.
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (_ & MBSH2 & _ & _ & _ & _ & _ & _).
    pose proof MB as MBc. destruct MBc as (NBC & _). pose proof (membio_bio_ok _ _ MB) as NBOK.
    pose proof TFS as TF. unfold biotestflags_stmt, bioacc_stmt_at in TF.
    eapply evt_cut.
    { eapply TF with (a := mb) (x := 8) (B := membio_bio (mset M0 (Z.of_nat used) fl nr)) (lo := lo); clear TF;
        try reflexivity; try exact NBC; try exact NBOK; try exact AC2; try exact CEIL; try exact MI2.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_TF2; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST2.
      all: lazymatch goal with
           | |- 0 <= 8 < _ => clear; lia
           | |- mb + BIO_SIZE <= lo => unfold BIO_SIZE; clear - hMBW; lia
           | |- addressable _ mb BIO_SIZE => destruct MBSH2 as (Sm & _); exact Sm
           | |- BIO_ranges H mb => exact (proj1 MRB)
           | |- lo <= fb - BIOACC_STACK => unfold BIOACC_STACK, FR_BIO_set_data; clear - hLOSr; unfold BIOREAD_STACK, FR_BIO_read, AFS_STACK in hLOSr; lia
           | |- _ mod 2 = 0 => unfold ARD_RA_TF2; clear; reflexivity
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "TFPRE:" G end. }
    cbv beta. intros ms3 PO. unfold bioacc_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & AC3 & ST3 & NBC3).
    rewrite ?unsigned_lit in MU3 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST3 by (clear - SPT FBT hLOS0 LO0; lia).
    cbn [bio_flags membio_bio mb_flags mset] in NBC3 |- *.
    assert (MB3 : MEMBIO H LB m3 mb (mset M0 (Z.of_nat used) fl nr)).
    { eapply MEMBIO_rehdr; [exact MB| exact MU3| exact WM3| | | | exact NBC3]; cbn [mb_bb mb_bm mb_rp mset]; unhide hM_BB; unhide hM_BM; unhide hM_RP; djs. }
    clear MB NBC NBC3 MI2.
    carryh MU3 WM3.
    destruct (rt_frame _ _ _ AC2 RFS2 ARL2 RH2 MU3 WM3 ltac:(okwtac)) as (AC3' & RFS3 & ARL3 & RH3). clear AC2 RFS2 ARL2 RH2 AC3'.
    extw MU WM MU3 WM3.
    rewrite FL8.
    replace (ret_pc (Z_to_bv 64 ARD_RA_TF2)) with (Z_to_bv 64 ARD_RA_TF2) by (symmetry; apply ret_pc_even; [unfold ARD_RA_TF2; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH3 & _ & _ & _ & _ & SHP3 & _ & _).
    assert (ACCc3 : accessible m3 ctx 2584).
    { destruct BSH3 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    eapply evt_cut.
    { eapply ard_eof1b; try exact SL2; try exact HD2; try exact ST3; try exact MI3; try exact CEIL; try exact ACCc3.
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
      all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
      all: match goal with |- ?G => idtac "EOF1BPRE:" G end. }
    cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & SL4 & HD4). clear SL2 HD2 ST3 ACCc3.
    carryh MU4 WM4.
    destruct (rt_frame _ _ _ AC3 RFS3 ARL3 RH3 MU4 WM4 ltac:(okwtac)) as (AC4 & RFS4 & ARL4 & RH4). clear AC3 RFS3 ARL3 RH3. try clear MI3.
    extw MU WM MU4 WM4.
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH4 & _ & _ & _ & _ & SHP4 & _ & _).
    assert (ACCe4 : accessible m4 enc 92).
    { destruct BSH4 as (_ & _ & Se). pose proof (aapp_bounds _ _ hRBe6 ltac:(lia)) as (_ & _ & Te & _).
      eapply addressable_accessible; [exact Se| clear; lia| clear; lia| clear - Te; lia]. }
    assert (ACCn4 : accessible m4 (ff + 32) 4).
    { apply acc4_of_shpat; [exact SHP4| clear - hFF1; lia| exact hFF8|]. pose proof aceil_range. unfold AAPP_HI. clear - hFF2 H0. lia. }
    pose proof DFS as DF. unfold decfinal_stmt in DF.
    eapply evt_cut.
    { eapply DF with (a := bf_enc R) (outlp := ff + 32) (d := d) (p := bf_eid R) (lo := lo) (LB := LB) (ov := vnum); clear DF;
        try reflexivity; try exact ENC; try exact NUM; try exact DMOD; try exact CEIL; try exact ACCe4; try exact ACCn4; try exact AC4.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_DF; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST4; try exact MI4; try exact hLOSf; try exact (B64TAB_of_mem_inv _ MI4).
      all: lazymatch goal with
           | |- _ mod 2 = 0 => unfold ARD_RA_DF; clear; reflexivity
           | |- (ff + 32) mod 4 = 0 => clear - hFF8; Z.div_mod_to_equations; lia
           | |- ff + 32 + 4 <= lo \/ _ => left; clear - hFF2 CEIL; lia
           | |- ff + 32 + 4 <= bf_enc R \/ _ => unhide hRBe5; unfold ENCCTX_SIZE; clear - hRBe5 hFSB1 hFSB2; lia
           | |- aapp (ff + 32) 4 \/ _ => left; eapply aapp_sub; [exact hAPF| clear - hFSB1; lia| clear - hFSB2; lia]
           | |- bf_enc R + ENCCTX_SIZE <= lo => unfold ENCCTX_SIZE; clear - hBLW; lia
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "DFPRE:" G end. }
    cbv beta. intros ms5 PO. unfold c8_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m5 & -> & -> & MU5 & WM5 & MI5 & AC5 & ST5 & ENC5 & NUM5 & _).
    rewrite ?unsigned_lit in MU5 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST5 by (clear - SPT FBT hLOS0 LO0; lia).
    clear ENC NUM MI4 ACCe4 ACCn4 SHP4 BSH4.
    carryh MU5 WM5.
    destruct (rt_frame _ _ _ AC4 RFS4 ARL4 RH4 MU5 WM5 ltac:(okwtac)) as (AC5' & RFS5 & ARL5 & RH5). clear AC4 RFS4 ARL4 RH4 AC5'.
    extw MU WM MU5 WM5.
    replace (ret_pc (Z_to_bv 64 ARD_RA_DF)) with (Z_to_bv 64 ARD_RA_DF) by (symmetry; apply ret_pc_even; [unfold ARD_RA_DF; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (decode_final_rv_cases d) as RVC.
    destruct (shad_now _ _ FX MU WM) as (BSH5 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCc5 : accessible m5 ctx 2584).
    { destruct BSH5 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    eapply evt_cut.
    { eapply ard_eof2; try exact SL4; try exact HD4; try exact ST5; try exact MI5; try exact CEIL; try exact ACCc5.
      all: try (clear - RVC; lia).
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
      all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
      all: match goal with |- ?G => idtac "EOF2PRE:" G end. }
    cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & ST6 & SL6 & HD6). clear SL4 HD4 ST5 ACCc5 BSH5.
    carryh MU6 WM6.
    destruct (rt_frame _ _ _ AC5 RFS5 ARL5 RH5 MU6 WM6 ltac:(okwtac)) as (AC6 & RFS6 & ARL6 & RH6). clear AC5 RFS5 ARL5 RH5. try clear MI5.
    extw MU WM MU6 WM6.
    (* [comment removed for export] *)
    destruct (ENCCTX_CB92 _ _ _ _ _ _ ENC5) as ((old & ENCB) & _ & _ & _).
    destruct (shad_now _ _ FX MU WM) as (BSH6 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCe6 : accessible m6 enc 92).
    { destruct BSH6 as (_ & _ & Se). pose proof (aapp_bounds _ _ hRBe6 ltac:(lia)) as (_ & _ & Te & _).
      eapply addressable_accessible; [exact Se| clear; lia| clear; lia| clear - Te; lia]. }
    pose proof DIS as DI. unfold decinit_stmt in DI.
    eapply evt_cut.
    { eapply DI with (a := bf_enc R) (p := bf_eid R) (lo := lo) (LB := LB); clear DI;
        try reflexivity; try exact ENCB; try exact INe; try exact RBe; try exact CEIL; try exact ACCe6; try exact AC6.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_DI2; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST6; try exact MI6; try exact hLOSi.
      all: lazymatch goal with
           | |- _ mod 2 = 0 => unfold ARD_RA_DI2; clear; reflexivity
           | |- bf_enc R + ENCCTX_SIZE <= lo => unfold ENCCTX_SIZE; clear - hBLW; lia
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "DIPRE:" G end. }
    cbv beta. intros ms7 PO. unfold c8_post in PO.
    destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m7 & -> & -> & MU7 & WM7 & MI7 & AC7 & ST7 & ENC7 & _).
    rewrite ?unsigned_lit in MU7 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST7 by (clear - SPT FBT hLOS0 LO0; lia).
    clear ENC5 ENCB MI6 ACCe6 BSH6. unfold ENCCTX_foot in MU7.
    carryh MU7 WM7.
    destruct (rt_frame _ _ _ AC6 RFS6 ARL6 RH6 MU7 WM7 ltac:(okwtac)) as (AC7' & RFS7 & ARL7 & RH7). clear AC6 RFS6 ARL6 RH6 AC7'.
    extw MU WM MU7 WM7.
    replace (ret_pc (Z_to_bv 64 ARD_RA_DI2)) with (Z_to_bv 64 ARD_RA_DI2) by (symmetry; apply ret_pc_even; [unfold ARD_RA_DI2; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    set (rc := if decode_final_rv d <? 0 then -1 else 0) in *.
    assert (RC : rc = -1 \/ rc = 0) by (subst rc; destruct (decode_final_rv d <? 0); [left|right]; reflexivity).
    destruct (shad_now _ _ FX MU WM) as (BSH7 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCc7 : accessible m7 ctx 2584).
    { destruct BSH7 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    eapply evt_cut.
    { eapply ard_eof3; try exact SL6; try exact HD6; try exact ST7; try exact MI7; try exact CEIL; try exact ACCc7.
      all: try exact RC.
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
      all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
      all: match goal with |- ?G => idtac "EOF3PRE:" G end. }
    cbv beta. intros ms8 (m8 & -> & MU8 & WM8 & MI8 & ST8 & SL8 & HD8). clear SL6 HD6 ST7 ACCc7 BSH7.
    carryh MU8 WM8.
    destruct (rt_frame _ _ _ AC7 RFS7 ARL7 RH7 MU8 WM8 ltac:(okwtac)) as (AC8 & RFS8 & ARL8 & RH8). clear AC7 RFS7 ARL7 RH7. try clear MI7.
    extw MU WM MU8 WM8.
    assert (TMP' : rw_cells asegs m8 (bf_ctx R + 1542) [CB 1024 jt]).
    { eapply arw_cells_recut; [exact TMP| | cbn; rewrite app_nil_r; reflexivity].
      destruct TMP as [[WF _] _]. cbn in WF |- *. tauto. }
    clear TMP.
    apply evt_done. unfold EXITQ. cbn [br_rv br_out br_used].
    exists m8, rc, rc, fl, nr, 0, 0, 0, (@nil Z), XS. exists (Z_to_bv 64 (out0 + Z.of_nat (length acc))), (Z_to_bv 64 (outl0 - Z.of_nat (length acc))), w216, w224, jb, jt, jo.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [clear - RC; lia|]. split; [left; clear - RC; lia|]. split; [clear - RC; lia|].
    split; [unfold zlength; clear - ACC; lia|]. split; [clear - USED; lia|]. split; [exact FLR1|].
    split; [exact SL8|]. split; [exact HD8|]. split; [exact BUF|]. split; [exact TMP'|]. split; [exact ENC7|].
    split; [exact MB3|]. split; [exact TXTB|]. split; [exact OUTB|]. split; [exact NUM5|].
    split; [exact (B64TAB_of_mem_inv _ MI8)|]. split; [exact MI8|]. split; [exact ST8|].
    split; [exact AC8|]. split; [exact RFS8|]. split; [exact ARL8|]. split; [exact RH8|].
    split; [exact FX|]. split; [exact MU| exact WM].
    all: match goal with |- ?G => idtac "EOF-LEFT:" G end.
  Qed.

  Lemma rd_trip_du : forall (used : nat) (d acc : list Z) (c n : Z) ms,
    (used < length txt)%nat -> zlength acc < outl0 -> 0 < n -> 0 < c < 2^31 ->
    READQ used d acc c n ms ->
    evt asegs (DUQ used d acc c n) ms.
  Proof.
    intros used d acc c n ms USED ACC NPOS C RQ. unfold READQ in RQ.
    destruct RQ as (m1 & fl & nr & vnum & XS & w216 & w224 & jb & jt & jo & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s8 & s9 & s10 & t3 & t4 & t5 & t6
                    & -> & EN & FLR1 & FL8 & SL & HD & BUF & TMP & ENC & MB & TXTB & OUTB & NUM & TAB & MI & ST & AC & RFS & ARL & RH & FX & MU & WM).
    nums. facts. mbnum MB. unfold zlength in *.
    destruct FOBJ as (Fa & Fc & Fe & Fm & Fbb & Fbm & Frp & Fff).
    set (data := firstn (Z.to_nat n) (skipn used txt)) in *.
    assert (NB : 0 < n <= 1024 /\ n <= Z.of_nat (length txt) - Z.of_nat used) by (clear - EN NPOS USED; lia).
    assert (LD : length data = Z.to_nat n) by (subst data; rewrite length_firstn, length_skipn; clear - NB; lia).
    hide EN.
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH1 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCc1 : accessible m1 ctx 2584).
    { destruct BSH1 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    eapply evt_cut.
    { eapply ard_data1 with (n := n); try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact ACCc1.
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - NB hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
      all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
      all: match goal with |- ?G => idtac "D1PRE:" G end. }
    cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ST2 & SL2 & HD2). clear SL HD ST ACCc1 BSH1.
    carryh MU2 WM2.
    destruct (rt_frame _ _ _ AC RFS ARL RH MU2 WM2 ltac:(okwtac)) as (AC2 & RFS2 & ARL2 & RH2). clear AC RFS ARL RH.
    extw MU WM MU2 WM2.
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH2 & _ & _ & _ & _ & _ & _ & AHb2).
    first [ pose proof (abiogetflags_rd_spec H HH) as TF | pose proof (abiogetflags_rd_spec H) as TF | pose proof (@abiogetflags_rd_spec _ H HH) as TF ].
    eapply evt_cut.
    { eapply TF with (a := a) (B := B0) (lo := lo); clear TF;
        try reflexivity; try exact AHb2; try exact BOK0; try exact AC2; try exact CEIL; try exact MI2; try exact RBa.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_TF1; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST2.
      all: lazymatch goal with
           | |- a + BIO_SIZE <= lo => unfold BIO_SIZE; clear - hBLW; lia
           | |- addressable _ a BIO_SIZE => destruct BSH2 as (Sa & _); exact Sa
           | |- BIO_ranges H a => exact RBa
           | |- lo <= fb - BIOACC_STACK => unfold BIOACC_STACK, FR_BIO_set_data; clear - hLOSr; unfold BIOREAD_STACK, FR_BIO_read, AFS_STACK in hLOSr; lia
           | |- _ mod 2 = 0 => unfold ARD_RA_TF1; clear; reflexivity
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "TF1PRE:" G end. }
    cbv beta. intros ms3 PO. unfold bioget_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & AC3 & ST3 & AHb3).
    rewrite ?unsigned_lit in MU3 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST3 by (clear - SPT FBT hLOS0 LO0; lia).
    clear MI2 AHb2 BSH2.
    carryh MU3 WM3.
    destruct (rt_frame _ _ _ AC2 RFS2 ARL2 RH2 MU3 WM3 ltac:(okwtac)) as (AC3' & RFS3 & ARL3 & RH3). clear AC2 RFS2 ARL2 RH2 AC3'.
    extw MU WM MU3 WM3.
    replace (ret_pc (Z_to_bv 64 ARD_RA_TF1)) with (Z_to_bv 64 ARD_RA_TF1) by (symmetry; apply ret_pc_even; [unfold ARD_RA_TF1; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH3 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCc3 : accessible m3 ctx 2584).
    { destruct BSH3 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    pose proof BOK0 as BOKf. unfold bio_ok in BOKf. destruct BOKf as (_ & _ & _ & FLB & _).
    eapply evt_cut.
    { eapply ard_data2 with (fl := bio_flags B0); try exact SL2; try exact HD2; try exact ST3; try exact MI3; try exact CEIL; try exact ACCc3; try exact BNL; try exact FLB.
      all: unfold B64CTX_SIZE; try exact hRBc6.
      all: clear - NB hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
      all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
      all: match goal with |- ?G => idtac "D2PRE:" G end. }
    cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & SL4 & HD4). clear SL2 HD2 ST3 ACCc3 BSH3.
    carryh MU4 WM4.
    destruct (rt_frame _ _ _ AC3 RFS3 ARL3 RH3 MU4 WM4 ltac:(okwtac)) as (AC4 & RFS4 & ARL4 & RH4). clear AC3 RFS3 ARL3 RH3. try clear MI3.
    extw MU WM MU4 WM4.
    (* [comment removed for export] *)
    unfold rdhdr in HD4. change (rw_cells asegs m4 ctx ([C4 (wz 0)] ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz enc)])) in HD4.
    apply (proj1 (rw_cells_app asegs m4 ctx _ _)) in HD4. destruct HD4 as [HD0 HDR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDR.
    change (rw_cells asegs m4 (ctx + 1542) ([CB (Z.to_nat n) data] ++ [CB (1024 - Z.to_nat n) jt])) in TMP.
    apply (proj1 (rw_cells_app asegs m4 _ _ _)) in TMP. destruct TMP as [TMPd TMPj]. cbn [cells_size csize Nat.add] in TMPj.
    replace (bf_ctx R + 1542 + Z.of_nat (Z.to_nat n + 0)) with (bf_ctx R + 1542 + n) in TMPj by (clear - NB; lia).
    destruct (rw_cells_CB_bytes_at _ _ _ _ _ TMPd) as [DATAB _].
    destruct (ENCCTX_CB92 _ _ _ _ _ _ ENC) as (_ & _ & _ & DL).
    (* [comment removed for export] *)
    destruct (shad_now _ _ FX MU WM) as (BSH4 & _ & _ & _ & _ & _ & _ & _).
    assert (ACCe4 : accessible m4 enc 92).
    { destruct BSH4 as (_ & _ & Se). pose proof (aapp_bounds _ _ hRBe6 ltac:(lia)) as (_ & _ & Te & _).
      eapply addressable_accessible; [exact Se| clear; lia| clear; lia| clear - Te; lia]. }
    assert (ACCc4 : accessible m4 ctx 2584).
    { destruct BSH4 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
      eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
    pose proof DUS as DU. unfold decupdate_stmt in DU.
    eapply evt_cut.
    { eapply DU with (a := bf_enc R) (out := bf_ctx R + 40) (outlp := bf_ctx R) (inp_a := bf_ctx R + 1542) (inl := n) (outsz := 1502) (ov := 0)
                     (d := d) (inp := data) (junk := jb) (p := bf_eid R) (lo := lo) (LB := LB); clear DU;
        try reflexivity; try exact ENC; try exact DATAB; try exact BUF; try exact HD0; try exact CEIL; try exact ACCe4; try exact AC4.
      all: rewrite ?unsigned_lit by (unfold ARD_RA_DU; clear - SPT FBT hLOS0 LO0; lia).
      all: try exact ST4; try exact MI4; try exact hLOSu; try exact (B64TAB_of_mem_inv _ MI4).
      all: lazymatch goal with
           | |- _ mod 2 = 0 => unfold ARD_RA_DU; clear; reflexivity
           | |- (bf_ctx R) mod 4 = 0 => clear - hRBc2; Z.div_mod_to_equations; lia
           | |- accessible _ (bf_ctx R + 40) 1502 => eapply accessible_sub; [exact ACCc4| clear; lia| clear; lia| clear; lia]
           | |- accessible _ (bf_ctx R) 4 => eapply accessible_sub; [exact ACCc4| clear; lia| clear; lia| clear; lia]
           | |- accessible _ (bf_ctx R + 1542) _ => eapply accessible_sub; [exact ACCc4| clear; lia| clear - NB; lia| clear - NB; lia]
           | |- aapp (bf_ctx R + 40) 1502 \/ _ => left; eapply aapp_sub; [exact hRBc6| clear; lia| clear; lia]
           | |- aapp (bf_ctx R) 4 \/ _ => left; eapply aapp_sub; [exact hRBc6| clear; lia| clear; lia]
           | |- aapp (bf_ctx R + 1542) _ \/ _ => left; eapply aapp_sub; [exact hRBc6| clear; lia| clear - NB; lia]
           | |- _ => idtac
           end.
      all: try (unfold ENCCTX_SIZE, du_outcap, zlength; unhide hCE; clear - hCE NB LD DL hRBc1 hBLW hLOS0 SPT FBT LO0; lia).
      all: match goal with |- ?G => idtac "DUPRE:" G end. }
    cbv beta. intros ms5 PO. unfold c8_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m5 & -> & -> & MU5 & WM5 & MI5 & AC5 & ST5 & ENC5
                    & (jb' & BUF5 & HD05 & DATAB5 & _ & LEN5)).
    rewrite ?unsigned_lit in MU5 by (clear - SPT FBT hLOS0 LO0; lia). rewrite ?unsigned_lit in ST5 by (clear - SPT FBT hLOS0 LO0; lia).
    clear ENC BUF HD0 DATAB MI4 ACCe4 ACCc4 BSH4.
    carryh MU5 WM5.
    destruct (rt_frame _ _ _ AC4 RFS4 ARL4 RH4 MU5 WM5 ltac:(okwtac)) as (AC5' & RFS5 & ARL5 & RH5). clear AC4 RFS4 ARL4 RH4 AC5'.
    extw MU WM MU5 WM5.
    set (r := decode_update d (map bv_unsigned data)) in *.
    assert (HD5 : rw_cells asegs m5 (bf_ctx R) (rdhdr (zlength (dr_out r)) 0 0 c (bf_enc R))).
    { unfold rdhdr. change (rw_cells asegs m5 (bf_ctx R) ([C4 (wz (zlength (dr_out r)))] ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz (bf_enc R))])).
      apply (proj2 (rw_cells_app asegs m5 _ _ _)). split; [exact HD05|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact HDR. }
    clear HD05 HDR.
    replace (ret_pc (Z_to_bv 64 ARD_RA_DU)) with (Z_to_bv 64 ARD_RA_DU) by (symmetry; apply ret_pc_even; [unfold ARD_RA_DU; clear; lia| reflexivity]).
    apply evt_done. unfold DUQ. cbv zeta. fold data. fold r.
    exists m5, fl, nr, vnum, XS. eexists _, _. exists jb', jt, jo. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|]. split; [unhide EN; exact EN|]. split; [exact LD|]. split; [exact FLR1|]. split; [clear - LEN5; exact LEN5|].
    split; [exact SL4|]. split; [exact HD5|]. split; [exact BUF5|]. split; [exact TMPd|]. split; [exact TMPj|].
    split; [exact ENC5|]. split; [exact MB|]. split; [exact TXTB|]. split; [exact OUTB|]. split; [exact NUM|].
    split; [exact (B64TAB_of_mem_inv _ MI5)|]. split; [exact MI5|]. split; [exact ST5|].
    split; [exact AC5|]. split; [exact RFS5|]. split; [exact ARL5|]. split; [exact RH5|].
    split; [exact FX|]. split; [exact MU| exact WM].
    all: match goal with |- ?G => idtac "DU-LEFT:" G end.
  Qed.

  Lemma rd_trip_data : forall (used : nat) (d acc : list Z) (c n : Z) ms,
    (used < length txt)%nat -> zlength acc < outl0 -> 0 < n -> 0 < c < 2^31 ->
    READQ used d acc c n ms ->
    evt asegs (TRIPQ used d acc n) ms.
  Proof.
    intros used d acc c n ms USED ACC NPOS C RQ.
    eapply evt_cut; [eapply rd_trip_du; eauto|]. cbv beta. intros ms3 DQ. unfold DUQ in DQ. cbv zeta in DQ.
    destruct DQ as (m3 & fl & nr & vnum & XS & w216 & w224 & jb & jt & jo & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6
                    & -> & EN & LD & FLR1 & LEN3 & SL & HD & BUF & TMPd & TMPj & ENC & MB & TXTB & OUTB & NUM & TAB & MI & ST & AC & RFS & ARL & RH & FX & MU & WM).
    nums. facts. mbnum MB. unfold zlength in *.
    destruct FOBJ as (Fa & Fc & Fe & Fm & Fbb & Fbm & Frp & Fff).
    set (data := firstn (Z.to_nat n) (skipn used txt)) in *. set (r := decode_update d (map bv_unsigned data)) in *.
    assert (NB : 0 < n <= 1024 /\ n <= Z.of_nat (length txt) - Z.of_nat used) by (clear - EN NPOS USED; lia).
    assert (CH : firstn 1024 (skipn used TXT) = map bv_unsigned data).
    { subst data. rewrite skipn_map, firstn_map. f_equal.
      destruct (Nat.le_gt_cases 1024 (length txt - used)) as [GE|LT].
      - f_equal. clear - GE EN. lia.
      - rewrite firstn_all2 by (rewrite length_skipn; clear - LT; lia).
        replace (Z.to_nat n) with (length (skipn used txt)) by (rewrite length_skipn; clear - LT EN; lia). symmetry. apply firstn_all. }
    clear EN. unfold TRIPQ. cbv zeta. rewrite !CH. fold r. rewrite length_map, LD. unfold zlength.
    pose proof (decode_update_rv d (map bv_unsigned data)) as KRV. fold r in KRV.
    destruct (Z.lt_ge_cases (dr_rv r) 0) as [KN|KP].
    - (* [comment removed for export] *)
      destruct (shad_now _ _ FX MU WM) as (BSH3 & _ & _ & _ & _ & _ & _ & _).
      assert (ACCc3 : accessible m3 ctx 2584).
      { destruct BSH3 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
        eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
      eapply evt_cut.
      { eapply ard_du_neg; try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact ACCc3.
        all: unfold B64CTX_SIZE; try exact hRBc6.
        all: clear - KN KRV hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
        all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
        all: match goal with |- ?G => idtac "DNPRE:" G end. }
      cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & SL4 & HD4). clear SL HD ST ACCc3 BSH3.
      (* [comment removed for export] *)
      assert (BUF' : rw_cells asegs m3 (bf_ctx R + 40) [CB 1502 (map b8 (dr_out r) ++ jb)]).
      { eapply arw_cells_recut; [exact BUF| | cbn; rewrite !app_nil_r, ?app_assoc; reflexivity].
        destruct BUF as [[WF _] _]. cbn in WF |- *. rewrite length_app, length_map. split; [| exact I]. clear - WF LEN3. lia. }
      clear BUF.
      carryh MU4 WM4.
      destruct (rt_frame _ _ _ AC RFS ARL RH MU4 WM4 ltac:(okwtac)) as (AC4 & RFS4 & ARL4 & RH4). clear AC RFS ARL RH.
      extw MU WM MU4 WM4.
      apply evt_done. left. split; [exact KN|].
      pose proof (rw_cells_CB_join _ _ _ _ _ _ _ TMPd ltac:(rewrite Z2Nat.id by (clear - NB; lia); exact TMPj)) as TMP'.
      replace (Z.to_nat n + (1024 - Z.to_nat n))%nat with 1024%nat in TMP' by (clear - NB; lia).
      unfold EXITQ. cbn [br_rv br_out br_used].
      exists m4, 0, (dr_rv r), fl, nr, 0, 0, vnum, (dr_d r), XS.
      exists (Z_to_bv 64 (out0 + Z.of_nat (length acc))), (Z_to_bv 64 (outl0 - Z.of_nat (length acc))), w216, w224,
             (map b8 (dr_out r) ++ jb), (data ++ jt), jo.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|].
      split; [unfold zlength; reflexivity|].
      split; [left; reflexivity|]. split; [left; clear - KN; lia|]. split; [clear - KN KRV; lia|].
      split; [unfold zlength; clear - ACC; lia|]. split; [clear - NB USED; lia|]. split; [exact FLR1|].
      split; [exact SL4|]. split; [exact HD4|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
      split; [replace (Z.of_nat (used + Z.to_nat n)) with (Z.of_nat used + n) by (clear - NB; lia); exact MB|].
      split; [exact TXTB|]. split; [exact OUTB|]. split; [exact NUM|].
      split; [exact (B64TAB_of_mem_inv _ MI4)|]. split; [exact MI4|]. split; [exact ST4|].
      split; [exact AC4|]. split; [exact RFS4|]. split; [exact ARL4|]. split; [exact RH4|].
      split; [exact FX|]. split; [exact MU| exact WM].
      all: match goal with |- ?G => idtac "DN-LEFT:" G end.
    - (* [comment removed for export] *)
      set (bl := Z.of_nat (length (dr_out r))) in *.
      set (outc := out0 + Z.of_nat (length acc)) in *. set (outlc := outl0 - Z.of_nat (length acc)) in *.
      assert (BLB : 0 <= bl <= 1502) by (clear - LEN3; lia).
      destruct (shad_now _ _ FX MU WM) as (BSH3 & _ & _ & _ & _ & _ & _ & _).
      assert (ACCc3 : accessible m3 ctx 2584).
      { destruct BSH3 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
        eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
      eapply evt_cut.
      { eapply ard_du_pos; try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact ACCc3.
        all: unfold B64CTX_SIZE; try exact hRBc6.
        all: zapZ; clear - KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; try lia.
        all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
        all: match goal with |- ?G => idtac "DPPRE:" G end. }
      cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & SL4 & HD4). clear SL HD ST ACCc3 BSH3.
      carryh MU4 WM4.
      destruct (rt_frame _ _ _ AC RFS ARL RH MU4 WM4 ltac:(okwtac)) as (AC4 & RFS4 & ARL4 & RH4). clear AC RFS ARL RH.
      extw MU WM MU4 WM4.
      set (i := Z.min bl outlc) in *.
      assert (IB : 0 <= i <= bl /\ i <= outlc /\ 0 < outlc) by (zapZ; clear - LEN3 ACC; lia).
      assert (Ei1 : bl < outlc -> i = bl) by (zapZ; clear; lia). assert (Ei2 : outlc <= bl -> i = outlc) by (zapZ; clear; lia).
      clearbody i.
      (* [comment removed for export] *)
      pose proof BUF as BUFc. change (rw_cells asegs m4 (bf_ctx R + 40) ([CB (length (dr_out r)) (map b8 (dr_out r))] ++ [CB (1502 - length (dr_out r)) jb])) in BUFc.
      apply (proj1 (rw_cells_app asegs m4 _ _ _)) in BUFc. destruct BUFc as [BUFo _].
      destruct (rw_cells_CB_split _ _ _ _ (Z.to_nat i) _ BUFo ltac:(clear - IB; zapZ; lia)) as [SRCc _]. clear BUFo.
      destruct (rw_cells_CB_bytes_at _ _ _ _ _ SRCc) as [SRC LS]. clear SRCc.
      pose proof OUTB as OUTc. change (rw_cells asegs m4 out0 ([CB (length acc) (map b8 acc)] ++ [CB (Z.to_nat outl0 - length acc) jo])) in OUTc.
      apply (proj1 (rw_cells_app asegs m4 _ _ _)) in OUTc. destruct OUTc as [OUTa OUTr]. cbn [cells_size csize Nat.add] in OUTr.
      replace (out0 + Z.of_nat (length acc + 0)) with outc in OUTr by (zapZ; clear; lia).
      destruct (rw_cells_CB_split _ _ _ _ (Z.to_nat i) _ OUTr ltac:(clear - IB ACC; zapZ; lia)) as [DST OUTz]. clear OUTr OUTB.
      rewrite Z2Nat.id in OUTz by (clear - IB; lia).
      (* [comment removed for export] *)
      destruct (shad_now _ _ FX MU WM) as (BSH4 & _ & _ & OSH4 & CSV4 & _ & _ & _).
      assert (ACCc4 : accessible m4 ctx 2584).
      { destruct BSH4 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
        eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
      destruct OSH4 as (Oa & Ov & Oi & Ok).
      eapply evt_cut.
      { eapply (asan_memcpy_specZ H HH) with (src := firstn (Z.to_nat i) (map b8 (dr_out r))) (junk := firstn (Z.to_nat i) jo) (lo := lo);
          try exact SRC; try exact DST; try exact MI4; try exact AC4; try exact ST4; try exact CEIL; try exact hLOSm.
        all: lazymatch goal with
             | |- length _ = Z.to_nat _ => exact LS
             | |- accessible _ (bf_ctx R + 40) _ => eapply accessible_sub; [exact ACCc4| clear; lia| clear - IB BLB; lia| clear - IB; lia]
             | |- accessible _ _ _ => eapply accessible_sub; [exact Oa| zapZ; clear - ACC; lia| zapZ; clear - IB ACC; lia| clear - IB; lia]
             | |- shvis _ (bf_ctx R + 40) _ => eapply shvis_sub; [exact CSV4| | | | |]; unfold B64CTX_SIZE; clear - IB BLB hRBc1; lia
             | |- shvis _ _ _ => eapply shvis_sub; [exact Ov| | | | |]; zapZ; clear - IB ACC OUT0 OUTE; lia
             | |- in_app_mem (bf_ctx R + 40) _ => eapply in_app_mem_sub; [exact CAPP| clear; lia| unfold B64CTX_SIZE; clear - IB BLB; lia]
             | |- in_app_mem _ _ => eapply in_app_mem_sub; [exact Oi| zapZ; clear - ACC; lia| zapZ; clear - IB ACC; lia]
             | |- aconst_ok (_, _) => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply (Ok x); cbn [fst snd] in Hx |- *; zapZ; clear - Hx IB ACC; lia
             | |- bf_ctx R + 40 + _ <= lo \/ _ => clear - hBLW IB BLB; lia
             | |- bf_ctx R + 40 + _ <= _ \/ _ => unhide hO_C; zapZ; clear - hO_C IB ACC BLB; lia
             | |- _ + _ <= lo \/ _ => unhide hOUTW; zapZ; clear - hOUTW IB ACC FBT; lia
             | |- _ => idtac
             end.
        all: try (zapZ; clear - IB BLB OUT0 OUTE ACC OUTL0 hRBc1 hBLW hLOS0 SPT FBT LO0; lia).
        all: match goal with |- ?G => idtac "MCPRE:" G end. }
      cbv beta. intros ms5 PO. unfold amove_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> & MU5 & WM5 & MI5 & ST5 & DST5 & SRC5 & AC5).
      clear SRC DST MI4 Oa Ov Oi Ok ACCc4 BSH4 CSV4.
      (* [comment removed for export] *)
      assert (MU5' : munch [(outc, outc + i); (lo, fb)] m4 m5).
      { eapply munch_weaken; [| exact MU5]. intros x Hx. cbn [outside fst snd] in Hx |- *. clear - Hx hLOSm. lia. }
      clear MU5. rename MU5' into MU5.
      carryh MU5 WM5.
      destruct (rt_frame _ _ _ AC4 RFS4 ARL4 RH4 MU5 WM5 ltac:(okwtac)) as (AC5' & RFS5 & ARL5 & RH5). clear AC4 RFS4 ARL4 RH4 AC5'.
      extw MU WM MU5 WM5.
      replace (ret_pc (Z_to_bv 64 ARD_RA_MC)) with (Z_to_bv 64 ARD_RA_MC) by (symmetry; apply ret_pc_even; [unfold ARD_RA_MC; clear; lia| reflexivity]).
      (* [comment removed for export] *)
      set (acc' := acc ++ firstn (Z.to_nat i) (dr_out r)) in *.
      assert (LA : length acc' = (length acc + Z.to_nat i)%nat).
      { subst acc'. rewrite length_app, length_firstn. clear - IB. zapZ. lia. }
      assert (OUTacc : rw_cells asegs m5 out0 [CB (length acc') (map b8 acc')]).
      { subst acc'. rewrite map_app, <- firstn_map. replace (length (acc ++ firstn (Z.to_nat i) (dr_out r))) with (length acc + Z.to_nat i)%nat.
        eapply rw_cells_CB_join; [exact OUTa|]. replace (out0 + Z.of_nat (length acc)) with outc by (zapZ; clear; lia). exact DST5. }
      clear OUTa DST5 SRC5. rewrite LA in OUTacc.
      (* [comment removed for export] *)
      replace (Z.of_nat used + n) with (Z.of_nat (used + Z.to_nat n)) in MB by (clear - NB; lia).
      (* [comment removed for export] *)
      assert (BUF' : rw_cells asegs m5 (bf_ctx R + 40) [CB 1502 (map b8 (dr_out r) ++ jb)]).
      { eapply arw_cells_recut; [exact BUF| | cbn; rewrite !app_nil_r, ?app_assoc; reflexivity].
        destruct BUF as [[WF _] _]. cbn in WF |- *. rewrite length_app, length_map. split; [| exact I]. clear - WF LEN3. lia. }
      pose proof (rw_cells_CB_join _ _ _ _ _ _ _ TMPd ltac:(rewrite Z2Nat.id by (clear - NB; lia); exact TMPj)) as TMP'.
      replace (Z.to_nat n + (1024 - Z.to_nat n))%nat with 1024%nat in TMP' by (clear - NB; lia).
      clear BUF TMPd TMPj.
      destruct (Z.lt_ge_cases bl outlc) as [PART|FULL].
      + (* [comment removed for export] *)
        pose proof (Ei1 PART) as Ei. clear Ei1 Ei2.
        destruct (shad_now _ _ FX MU WM) as (BSH5 & _ & _ & _ & _ & _ & _ & _).
        assert (ACCc5 : accessible m5 ctx 2584).
        { destruct BSH5 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
          eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
        eapply evt_cut.
        { rewrite Ei. eapply ard_mc_loop with (bl := bl) (out := outc) (outl := outlc) (ret := Z.of_nat (length acc)); try exact SL4; try exact ST5; try exact MI5; try exact CEIL; try exact ACCc5; try exact HD4.
          all: unfold B64CTX_SIZE; try exact hRBc6.
          all: try (generalize Ei; zapZ; clear - PART KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; intros Ei; lia).
          all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
          all: match goal with |- ?G => idtac "MLPRE:" G end. }
        cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & ST6 & SL6 & HD6). clear SL4 HD4 ST5 ACCc5 BSH5.
        carryh MU6 WM6.
        destruct (rt_frame _ _ _ AC5 RFS5 ARL5 RH5 MU6 WM6 ltac:(okwtac)) as (AC6 & RFS6 & ARL6 & RH6). clear AC5 RFS5 ARL5 RH5. try clear MI5.
        extw MU WM MU6 WM6.
        apply evt_done. right. right.
        split; [exact KP|]. split; [clear - PART Ei; zapZ; lia|].
        split. { subst r. apply decode_update_d; [| exact KP]. intros E. apply (f_equal (@length Z)) in E. rewrite length_map, LD in E. cbn in E. clear - E NB. lia. }
        exists m6, fl, nr, vnum, XS, w216, w224.
        exists (map b8 (dr_out r) ++ jb), (data ++ jt), (skipn (Z.to_nat i) jo).
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
        split; [unfold HEADMS; reflexivity|].
        unfold HINV. unfold zlength. rewrite LA, Nat2Z.inj_add, Z2Nat.id by (clear - IB; lia).
        split.
        { rewrite Ei in SL6 |- *. replace (out0 + (Z.of_nat (length acc) + bl)) with (bl + outc) by (zapZ; clear; lia).
          replace (outl0 - (Z.of_nat (length acc) + bl)) with (outlc - bl) by (zapZ; clear; lia). exact SL6. }
        split; [exact HD6|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
        split. { replace (used + length (map bv_unsigned data))%nat with (used + Z.to_nat n)%nat by (rewrite length_map, LD; reflexivity). exact MB. }
        split; [exact TXTB|].
        split. { change (rw_cells asegs m6 out0 ([CB (length acc + Z.to_nat i) (map b8 acc')] ++ [CB (Z.to_nat outl0 - (length acc + Z.to_nat i)) (skipn (Z.to_nat i) jo)])).
                 apply (proj2 (rw_cells_app asegs m6 out0 _ _)). split; [exact OUTacc|]. cbn [cells_size csize Nat.add].
                 replace (out0 + Z.of_nat (length acc + Z.to_nat i + 0)) with (outc + i) by (zapZ; clear - IB; lia).
                 replace (Z.to_nat outl0 - (length acc + Z.to_nat i))%nat with (Z.to_nat outl0 - length acc - Z.to_nat i)%nat by (clear; lia). exact OUTz. }
        split; [exact NUM|].
        split; [exact (B64TAB_of_mem_inv _ MI6)|]. split; [exact MI6|]. split; [exact ST6|].
        split; [exact AC6|]. split; [exact RFS6|]. split; [exact ARL6|]. split; [exact RH6|].
        split; [exact FX|]. split; [exact MU| exact WM].
        all: match goal with |- ?G => idtac "ML-LEFT:" G end.
      + (* [comment removed for export] *)
        pose proof (Ei2 FULL) as Ei. clear Ei1 Ei2.
        clearbody acc'. subst i.
        destruct (shad_now _ _ FX MU WM) as (BSH5 & _ & _ & OSH5 & _ & _ & _ & _).
        assert (OUTLT : outc + outlc < 2^64).
        { destruct OSH5 as (_ & _ & OIa & _). unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI in OIa.
          subst outc outlc. clear - OIa. lia. }
        clear OSH5.
        assert (ACCc5 : accessible m5 ctx 2584).
        { destruct BSH5 as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
          eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
        eapply evt_cut.
        { eapply ard_mc_done with (bl := bl) (out := outc) (outl := outlc) (ret := Z.of_nat (length acc)); try exact SL4; try exact ST5; try exact MI5; try exact HD4; try exact CEIL; try exact ACCc5.
          all: unfold B64CTX_SIZE; try exact hRBc6.
          all: try exact OUTLT.
          all: try (zapZ; clear - FULL KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; lia).
          all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
          all: match goal with |- ?G => idtac "MDPRE:" G end. }
        cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & ST6 & SL6 & HD6). clear SL4 HD4 ST5 ACCc5 BSH5.
        carryh MU6 WM6.
        destruct (rt_frame _ _ _ AC5 RFS5 ARL5 RH5 MU6 WM6 ltac:(okwtac)) as (AC6 & RFS6 & ARL6 & RH6). clear AC5 RFS5 ARL5 RH5. try clear MI5.
        extw MU WM MU6 WM6.
        apply evt_done. right. left.
        split; [exact KP|]. split; [clear - FULL; zapZ; lia|].
        unfold EXITQ. cbn [br_rv br_out br_used]. unfold zlength.
        rewrite !LA, !Nat2Z.inj_add, !(Z2Nat.id outlc) by (clear - IB; lia).
        exists m6, 0, (dr_rv r), fl, nr, (if bl =? outlc then 0 else bl), (if bl =? outlc then 0 else outlc), vnum, (dr_d r), XS.
        exists (Z_to_bv 64 (outlc + outc)), (Z_to_bv 64 0), w216, w224,
               (map b8 (dr_out r) ++ jb), (data ++ jt), (skipn (Z.to_nat outlc) jo).
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
        split; [reflexivity|].
        split. { replace (Z.of_nat (length acc) + outlc =? 0) with false by (symmetry; apply Z.eqb_neq; clear - IB; zapZ; lia). reflexivity. }
        split; [left; reflexivity|]. split; [right; clear - IB; zapZ; lia|]. split; [clear - KP KRV; lia|].
        split; [clear - IB ACC; zapZ; lia|]. split; [clear - NB USED; lia|]. split; [exact FLR1|].
        split; [exact SL6|]. split; [exact HD6|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
        split; [rewrite <- Nat2Z.inj_add; exact MB|]. split; [exact TXTB|].
        split. { change (rw_cells asegs m6 out0 ([CB (length acc + Z.to_nat outlc) (map b8 acc')] ++ [CB (Z.to_nat outl0 - (length acc + Z.to_nat outlc)) (skipn (Z.to_nat outlc) jo)])).
                 apply (proj2 (rw_cells_app asegs m6 out0 _ _)). split; [exact OUTacc|]. cbn [cells_size csize Nat.add].
                 replace (out0 + Z.of_nat (length acc + Z.to_nat outlc + 0)) with (outc + outlc) by (zapZ; clear - IB; lia).
                 replace (Z.to_nat outl0 - (length acc + Z.to_nat outlc))%nat with (Z.to_nat outl0 - length acc - Z.to_nat outlc)%nat by (clear; lia). exact OUTz. }
        split; [exact NUM|].
        split; [exact (B64TAB_of_mem_inv _ MI6)|]. split; [exact MI6|]. split; [exact ST6|].
        split; [exact AC6|]. split; [exact RFS6|]. split; [exact ARL6|]. split; [exact RH6|].
        split; [exact FX|]. split; [exact MU| exact WM].
        all: match goal with |- ?G => idtac "MD-LEFT:" G end.
  Qed.

  Lemma rd_loop : forall (fuel used : nat) (d acc : list Z) (m : mem) (fl nr c vnum : Z) (XS : list (Z * Z)) (w216 w224 : word)
      (jb jt jo : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word),
    (S (length txt - used) <= fuel)%nat -> (used <= length txt)%nat ->
    zlength acc < outl0 -> (length d = 0%nat \/ Nat.modulo (length d) 4 <> 0%nat) -> 0 < c < 2^31 ->
    HINV m used d acc fl nr c vnum XS w216 w224 jb jt jo ->
    evt asegs (EXITQ (b64r_loop fuel (skipn used TXT) d (zlength acc) (outl0 - zlength acc) acc used))
      (HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 m).
  Proof.
    induction fuel as [|fuel IH]; intros until t6; intros FUEL USED ACC DMOD C HI; [lia|].
    assert (LT : length TXT = length txt) by (apply length_map).
    destruct (Nat.eq_dec used (length txt)) as [EOFc|DATAc].
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply rd_pre; eauto|]. cbv beta. intros ms' RQ.
      replace (Z.min 1024 (zlength txt - Z.of_nat used)) with 0 in RQ by (unfold zlength; lia).
      replace (skipn used TXT) with (@nil Z) by (symmetry; apply skipn_all2; lia).
      rewrite b64r_loop_eof by lia.
      eapply rd_trip_eof; eauto.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply rd_pre; eauto|]. cbv beta. intros ms' RQ.
      eapply evt_cut; [eapply rd_trip_data; [| | | | exact RQ]; unfold zlength in *; lia|]. cbv beta. intros ms2 TQ.
      assert (NE : skipn used TXT <> []).
      { intros E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. clear - E LT DATAc USED. lia. }
      rewrite b64r_loop_trip by first [lia| exact NE].
      unfold TRIPQ in TQ. cbv zeta in TQ |- *. unfold zlength in TQ |- *.
      set (chunk := firstn 1024 (skipn used TXT)) in *. set (r := decode_update d chunk) in *.
      pose proof (decode_update_rv d chunk) as KRV. fold r in KRV.
      destruct TQ as [(NEG & EX)|[(POS & FULL & EX)|(POS & PART & DMOD' & m' & fl' & nr' & vnum' & XS' & w216' & w224' & jb' & jt' & jo'
                       & ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s8' & s9' & s10' & t3' & t4' & t5' & t6' & -> & HI')]].
      + replace (dr_rv r <? 0) with true by (symmetry; apply Z.ltb_lt; exact NEG). apply evt_done. exact EX.
      + replace (dr_rv r <? 0) with false by (symmetry; apply Z.ltb_ge; exact POS).
        rewrite FULL. rewrite FULL in EX.
        destruct (dr_rv r =? 0).
        * replace (Z.of_nat (length acc) + (outl0 - Z.of_nat (length acc)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          apply evt_done. exact EX.
        * rewrite b64r_loop_outl_le0 by (clear - FUEL USED DATAc; lia). apply evt_done. exact EX.
      + replace (dr_rv r <? 0) with false by (symmetry; apply Z.ltb_ge; exact POS).
        set (i := Z.min (Z.of_nat (length (dr_out r))) (outl0 - Z.of_nat (length acc))) in *.
        set (acc' := acc ++ firstn (Z.to_nat i) (dr_out r)) in *.
        assert (IB : 0 <= i <= Z.of_nat (length (dr_out r))) by (unfold i in *; lia).
        assert (LA : Z.of_nat (length acc') = Z.of_nat (length acc) + i).
        { unfold acc'. rewrite length_app, length_firstn. clear - IB. lia. }
        rewrite <- !LA. replace (outl0 - Z.of_nat (length acc) - i) with (outl0 - Z.of_nat (length acc')) by lia.
        clearbody i acc'.
        destruct (Z.eq_dec (dr_rv r) 0) as [K0|K1].
        * (* [comment removed for export] *)
          rewrite K0, Z.eqb_refl. rewrite K0 in HI'.
          destruct HI' as (SL & HD & BUF & TMP & ENC & MB & TXTB & OUTB & NUM & TAB & MI & ST & AC & RFS & ARL & RH & FX & MU & WM).
          nums. facts. mbnum MB. unfold HEADMS. unfold zlength in *.
          destruct FOBJ as (Fa & Fc & Fe & Fm & Fbb & Fbm & Frp & Fff).
          destruct (shad_now _ _ FX MU WM) as (BSHx & _ & _ & _ & _ & _ & _ & _).
          assert (ACCcx : accessible m' ctx 2584).
          { destruct BSHx as (_ & Sc & _). pose proof (aapp_bounds _ _ hRBc6 ltac:(lia)) as (_ & _ & Tc & _).
            eapply addressable_accessible; [exact Sc| | |]; unfold B64CTX_SIZE; clear - Tc; lia. }
          assert (ACC' : Z.of_nat (length acc') < outl0) by (clear - PART IB LA ACC; lia).
          eapply evt_cut.
          { eapply ard_head_exit; try exact SL; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact ACCcx.
            all: unfold B64CTX_SIZE; try exact hRBc6.
            all: try (clear - ACC' OUTL0 OUT0 OUTE hRBc1 hRBc2 hBLW hLOS0 SPT FBT LO0; lia).
            all: try lazymatch goal with |- word => exact (Z_to_bv 64 0) end. all: try lazymatch goal with |- Z => exact 0 end.
            all: match goal with |- ?G => idtac "HXPRE:" G end. }
          cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3 & SL3 & HD3). clear SL HD ST ACCcx BSHx.
          carryh MU3 WM3.
          destruct (rt_frame _ _ _ AC RFS ARL RH MU3 WM3 ltac:(okwtac)) as (AC3 & RFS3 & ARL3 & RH3). clear AC RFS ARL RH.
          extw MU WM MU3 WM3.
          apply evt_done. unfold EXITQ. cbn [br_rv br_out br_used].
          exists m3, 0, 0, fl', nr', 0, 0, vnum', (dr_d r), XS'.
          exists (Z_to_bv 64 (out0 + zlength acc')), (Z_to_bv 64 (outl0 - zlength acc')), w216', w224', jb', jt', jo'.
          eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
          split; [reflexivity|].
          split; [unfold zlength; destruct (Z.of_nat (length acc') =? 0); reflexivity|].
          split; [left; reflexivity|]. split; [left; clear; lia|]. split; [clear; lia|].
          split; [unfold zlength; clear - ACC'; lia|].
          split. { unfold chunk. rewrite length_firstn, length_skipn, LT. clear - USED DATAc; lia. }
          assert (FLR' : 0 <= fl' < 2^31) by exact MBF.
          split; [exact FLR'|].
          split; [exact SL3|]. split; [exact HD3|]. split; [exact BUF|]. split; [exact TMP|]. split; [exact ENC|].
          split. { replace (used + length chunk)%nat with (used + length (firstn 1024 (skipn used TXT)))%nat by reflexivity. exact MB. }
          split; [exact TXTB|]. split; [exact OUTB|]. split; [exact NUM|].
          split; [exact (B64TAB_of_mem_inv _ MI3)|]. split; [exact MI3|]. split; [exact ST3|].
          split; [exact AC3|]. split; [exact RFS3|]. split; [exact ARL3|]. split; [exact RH3|].
          split; [exact FX|]. split; [exact MU| exact WM].
          all: match goal with |- ?G => idtac "HX-LEFT:" G end.
        * (* [comment removed for export] *)
          assert (K1' : dr_rv r = 1) by lia. rewrite K1'. change (1 =? 0) with false. cbv iota.
          assert (USED' : (used + length chunk <= length txt)%nat).
          { unfold chunk. rewrite length_firstn, length_skipn, LT. lia. }
          replace (skipn 1024 (skipn used TXT)) with (skipn (used + length chunk) TXT).
          2:{ rewrite skipn_skipn. unfold chunk. rewrite length_firstn, length_skipn.
              destruct (Nat.le_gt_cases (length TXT - used) 1024) as [LE|GT].
              - rewrite Nat.min_r by lia. rewrite !skipn_all2 by lia. reflexivity.
              - rewrite Nat.min_l by lia. f_equal. lia. }
          eapply IH; [ | | | exact DMOD' | | exact HI']; [ | exact USED' | unfold zlength; lia | lia].
          unfold chunk. rewrite length_firstn, length_skipn, LT. clear - FUEL DATAc USED. lia.
  Qed.

End RD.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegVCx SegDig SegDigOk.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPCU_sum PFFCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok S2SumH S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require PU2_entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import S2TabU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require U2N_defs U2N_cert U2N_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_t0 PU2_t0n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SG := U2N_defs.SG.
Local Notation u_rng' := PU2_entry.u_rng'.

(* [comment removed for export] *)
Lemma T0N_regs_list : map (fun k => sr_get U2N_defs.T0_regs (Z_to_bv 5 k)) rkeys =
  [EVar 30; EAlu ALU_ADD (EVar 1) (ELit (-368)); EVar 2; EVar 3; EVar 31; EVar 32; EVar 33; EVar 19; EVar 34; EVar 29;
   EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EAlu ALU_ADD (EVar 18) (EVar 28); EVar 20; EVar 42; EVar 18;
   EVar 43; EVar 44; EVar 45; EVar 46; EVar 22; EVar 47; EVar 48; EVar 49; EVar 50; EVar 51].
Proof. vm_compute. reflexivity. Qed.

Lemma t0n_regs : forall (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  368 <= zsp < M64 -> 0 <= zgp < M64 -> 0 <= ztp < M64 -> 0 <= LEN < M64 -> 0 <= COPY < M64 -> 0 <= IDX < M64 ->
  0 <= BUF -> 0 <= V -> BUF + V < M64 -> 0 <= TBASE < M64 ->
  regs_ok (mkEZ (ZLN zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                     THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY
                     [u x1; u x5; u x6; u x7; u x9; u x11; u x12; u x13; u x14; u x15; u x16; u x17;
                      u x20; u x22; u x23; u x24; u x25; u x27; u x28; u x29; u x30; u x31]))
    U2N_defs.T0_regs
    (mkR x1 (Z_to_bv 64 (zsp - 368)) (Z_to_bv 64 zgp) (Z_to_bv 64 ztp) x5 x6 x7 (Z_to_bv 64 LEN) x9
         (Z_to_bv 64 COPY) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (BUF + V)) (Z_to_bv 64 IDX) x20 (Z_to_bv 64 BUF)
         x22 x23 x24 x25 (Z_to_bv 64 TBASE) x27 x28 x29 x30 x31).
Proof.
  intros. apply regs_ok_mkR.
  rewrite <- (map_map (fun k => sr_get U2N_defs.T0_regs (Z_to_bv 5 k)) (edenot _)), T0N_regs_list. cbn [map].
  repeat f_equal;
    first [ (cbn [edenot ev mkEZ nth ZLN app]; apply Z_to_bv_bv_unsigned)
          | (cbn [edenot ev mkEZ nth ZLN app]; reflexivity)
          | (rewrite zden_ok by reflexivity; cbn [zden nth ZLN app]; apply Z_to_bv_congr; f_equal; lia) ].
Qed.

Section R.
  Hypothesis SFPCSU_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPCSU.
  Hypothesis PFFCSU_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFCSU.

  Lemma u2n_run : forall (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
      THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
      (gpw tpw : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d idx : list Z),
    let ZL := ZLN zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS
                  OCB IAB V COPY
                  [u x1; u x5; u x6; u x7; u x9; u x11; u x12; u x13; u x14; u x15; u x16; u x17;
                   u x20; u x22; u x23; u x24; u x25; u x27; u x28; u x29; u x30; u x31] in
    zgp = u gpw -> ztp = u tpw ->
    368 <= zsp < M64 -> 0 <= LEN < M64 -> 0 <= COPY < M64 -> 0 <= IDX < M64 -> 0 <= BUF -> 0 <= V -> BUF + V < M64 ->
    0 <= TBASE < M64 ->
    know_ok usegs (mkEZ ZL) m U2N_defs.T0_kn ->
    LEN = zlength d -> N = zlength idx -> Forall (fun c => 0 <= c < 256) d -> scan d = (true, idx) ->
    bytes_at usegs m BUF (s1buf d) -> DJ 0x10000 0xa3000 BUF (LEN + 64) -> BUF + LEN + 64 < M64 ->
    rw_cells usegs m IDX [CB (4 * (length idx + 3)) (SjS1Bytes.u32bytes (idx ++ [LEN; LEN; 0]))] ->
    DJ 0x10000 0xa3000 IDX (4 * N + 12) -> IDX + 4 * N + 12 < M64 ->
    mem_inv usegs m -> frm0 fc ->
    ExecF.evtF SG (SX.fp_of (SP.p_A U2N_defs.U2N) (mkEZ ZL))
      (SLib.xpostH SG (U2N_sound.gpu2n d (idx ++ [LEN; LEN; 0])) MMU.hmH MMU.hmA U2N_defs.U2N (mkEZ ZL) m (seg_rom usegs))
      (MS (mkR x1 (Z_to_bv 64 (zsp - 368)) gpw tpw x5 x6 x7 (Z_to_bv 64 LEN) x9
               (Z_to_bv 64 COPY) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (BUF + V)) (Z_to_bv 64 IDX) x20 (Z_to_bv 64 BUF)
               x22 x23 x24 x25 (Z_to_bv 64 TBASE) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x29e0c) fc None m (seg_rom usegs)).
  Proof.
    intros until idx. intros ZL Hgp Htp Hsp HL HCP HI HB1 HV HB2 HTB HK HLEN HN Hd Hscan HBUF UB HBE HIDX UI HIE HMI HZ.
    subst LEN N. pose proof (scan_S1OUT d idx Hscan) as S1. pose proof (s1_n _ _ _ S1) as Sn.
    pose proof (u_rng' gpw) as Rgp. pose proof (u_rng' tpw) as Rtp.
    assert (EGP : gpw = Z_to_bv 64 zgp) by (subst zgp; symmetry; apply Z_to_bv_bv_unsigned).
    assert (ETP : tpw = Z_to_bv 64 ztp) by (subst ztp; symmetry; apply Z_to_bv_bv_unsigned).
    rewrite EGP, ETP.
    apply (SLib.prog_evtH SG (U2N_sound.gpu2n d (idx ++ [zlength d; zlength d; 0])) (SDG.gfpx gfp2)
             (SVX.gvc_enrich SVX.bc_enrich (SDG.gsplit SG (wvc_ok SG 1048512 0x13768)))
             (SDG.gpx_frame SG (gp2 SG d _) gfp2 (gp2_frame SG d _))
             (SVX.gvc_enrich_ok SG (U2N_sound.gpu2n d _) SVX.bc_enrich _ (SVX.bc_enrich_ok SG)
                (SDGok.gsplit_ok SG (gp2 SG d _) _ (wvc_ok_sound SG d _ 1048512 ltac:(lia) 0x13768 ltac:(lia) d2v_img_ubsan)))
             MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF U2N_defs.U2N U2N_defs.U2N_IT 4000 true U2N_cert.U2N_hints
             U2N_defs.T0 (fun _ => True)
             (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ U2N_cert.u2n_cert) (SP.itab_ranges_sound SG _) ltac:(intros TA [])
             ltac:(intros Sm HSm; cbn [SP.p_cs U2N_defs.U2N] in HSm;
                   destruct HSm as [<-|[<-|[<-|[<-|[]]]]];
                   [ apply MMU.mcpu_ok; lia | apply MMU.msp_ok; lia | apply SFPCSU_ok | apply PFFCSU_ok ])
             ltac:(intros; exact I) ltac:(intros; unfold SP.wins_client; apply Forall_forall; intros; exact I)
             ltac:(intros E0 _ w Hw; destruct Hw) ltac:(intros; constructor) ltac:(left; reflexivity)).
    - reflexivity.
    - exact I.
    - exact I.
    - exact HMI.
    - apply rfull_mkR.
    - apply t0n_regs; lia.
    - exact HK.
    - (* [comment removed for export] *)
      unfold SG.gholds. cbn [ST.t_ghost U2N_defs.T0]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold U2N_sound.gpu2n;
        cbn [SDG.gpx Nat.leb ST.g_id ST.g_args map gp2 edenot mkEZ ev U2N_defs.vBUF U2N_defs.vLEN U2N_defs.vIDX U2N_defs.vN U2N_defs.V nth ZL ZLN app];
        rewrite !u_Z_to_bv, !Z.mod_small by lia.
      + split; [reflexivity|]. split; [lia|]. split; [exact Hd|]. rewrite PU2_entry.bufbytes_eq.
        apply PU2_entry.mbytes_of_bytes_at_heap; [exact HBUF|]. intros i Hi. rewrite PU2_entry.s1buf_length in Hi.
        rewrite u_Z_to_bv, Z.mod_small by lia. clear - UB Hi. unfold DJ in UB. lia.
      + assert (ZL3 : zlength (idx ++ [zlength d; zlength d; 0]) = zlength idx + 3) by (rewrite zlength_app; reflexivity).
        rewrite ZL3. replace (zlength idx + 3 - 3) with (zlength idx) by lia.
        split; [reflexivity|]. split; [exact S1|]. split; [lia|]. rewrite PU2_entry.u32bytes_eq.
        destruct (cb_bytes m _ _ _ HIDX) as [BI LI].
        apply PU2_entry.mbytes_of_bytes_at_heap; [exact BI|]. intros i Hi. rewrite LI in Hi.
        rewrite u_Z_to_bv, Z.mod_small by (unfold zlength in *; lia). clear - UI Hi. unfold DJ in UI. unfold zlength in *. lia.
    - exact HMI.
    - exact HZ.
  Qed.
End R.

(* [comment removed for export] *)
Lemma u2n_munch : forall (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY (rest : list Z) (m m' : word -> option byte),
  (forall x : word, SP.outside_wins (mkEZ (ZLN zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                                              THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY rest))
                       (SP.p_W U2N_defs.U2N) (u x) -> m' x = m x) ->
  2976 <= zsp < M64 -> 0 <= TBASE -> 0 <= CAPT -> TBASE + 8 * CAPT < M64 -> 0 <= COPY -> 0 <= V <= LEN ->
  COPY + (LEN - V + 64) < M64 -> LEN < M64 ->
  munch [(zsp - 368, zsp); (zsp - 2976, zsp - 368); (TBASE, TBASE + 8 * CAPT); (COPY, COPY + (LEN - V + 64))] m m'.
Proof.
  intros until m'. intros FR. intros. intros x Hx. apply FR. unfold SP.outside_wins. cbn [SP.p_W U2N_defs.U2N].
  pose proof (u_rng' x).
  cbn [outside] in Hx.
  repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity;
    cbn [zden nth ZLN app U2N_defs.vSP U2N_defs.vTBASE U2N_defs.vCAPT U2N_defs.vCOPY U2N_defs.vLEN U2N_defs.vV U2N_defs.V
         U2N_defs.mul U2N_defs.add U2N_defs.sub];
    rewrite ?(Z.mod_small _ M64) by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma xdel_regsA : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  length ZL = 30%nat -> SP.gagree 30 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs U2N_defs.XDELA) R' ->
  exists x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    R' = mkR x1 (Z_to_bv 64 (nth 1 ZL 0 - 368)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0)) x5 x6 x7
             x8 (Z_to_bv 64 (nth 29 ZL 0)) (Z_to_bv 64 (nth 29 ZL 0))
             x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros ZL E' R' HL Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (E2 : edenot E' (EAlu ALU_ADD (EVar 1) (ELit (-368))) = Z_to_bv 64 (nth 1 ZL 0 - 368))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EAlu ALU_ADD (EVar 1) (ELit (-368))) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E3 : edenot E' (EVar 2) = Z_to_bv 64 (nth 2 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 2) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E4 : edenot E' (EVar 3) = Z_to_bv 64 (nth 3 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 3) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E29 : edenot E' (EVar 29) = Z_to_bv 64 (nth 29 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 29) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  change (sr_get (ST.t_regs _) 2) with (EAlu ALU_ADD (EVar 1) (ELit (-368))); change (sr_get (ST.t_regs _) 3) with (EVar 2);
  change (sr_get (ST.t_regs _) 4) with (EVar 3); change (sr_get (ST.t_regs _) 9) with (EVar 29);
  change (sr_get (ST.t_regs _) 10) with (EVar 29).
  rewrite E2, E3, E4, E29; cbn [edenot]; do 26 eexists; reflexivity.
Qed.

Lemma xdel_regsBC : forall (X : ST.tmpl) (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  X = U2N_defs.XDELB \/ X = U2N_defs.XDELC ->
  length ZL = 30%nat -> SP.gagree 30 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs X) R' ->
  exists x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    R' = mkR x1 (Z_to_bv 64 (nth 1 ZL 0 - 368)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0)) x5 x6 x7
             (ev E' 30) (Z_to_bv 64 (nth 29 ZL 0)) (Z_to_bv 64 (nth 29 ZL 0))
             x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros X ZL E' R' HX HL Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (E2 : edenot E' (EAlu ALU_ADD (EVar 1) (ELit (-368))) = Z_to_bv 64 (nth 1 ZL 0 - 368))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EAlu ALU_ADD (EVar 1) (ELit (-368))) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E3 : edenot E' (EVar 2) = Z_to_bv 64 (nth 2 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 2) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E4 : edenot E' (EVar 3) = Z_to_bv 64 (nth 3 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 3) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  assert (E29 : edenot E' (EVar 29) = Z_to_bv 64 (nth 29 ZL 0))
    by (rewrite <- (SP.edenot_gagree 30 _ _ (EVar 29) Hg Hb eq_refl), zden_ok by reflexivity; reflexivity).
  destruct HX as [->| ->];
    change (sr_get (ST.t_regs _) 2) with (EAlu ALU_ADD (EVar 1) (ELit (-368))); change (sr_get (ST.t_regs _) 3) with (EVar 2);
    change (sr_get (ST.t_regs _) 4) with (EVar 3); change (sr_get (ST.t_regs _) 8) with (EVar 30);
    change (sr_get (ST.t_regs _) 9) with (EVar 29); change (sr_get (ST.t_regs _) 10) with (EVar 29);
    rewrite E2, E3, E4, E29; cbn [edenot]; do 25 eexists; reflexivity.
Qed.

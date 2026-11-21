(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ENTRYG.
Variables (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_entryg : forall (Q : machine_state -> Prop) (d : deflate_state) (flush : Z)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  DREP me L d -> dout me L rest0 (ds_strm d) -> Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat ->
  stk usegs me lo (bv_unsigned (r_sp r)) -> mem_inv usegs me ->
  (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) -> 0 <= flush <= 5 ->
  0 <= cs_avail_in (ds_strm d) < 2^31 -> 0 <= cs_next_in (ds_strm d) <= zlength inp ->
  (* [comment removed for export] *)
  (ds_status d = 666 /\ flush <> 4 ->
   forall (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me (fst (err_return d Z_STREAM_ERROR)) m' ->
     evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 (wz (-2)) y13 y14 y15 y16 y17 y18
                          (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_DEFL_EPI) fc None m' (seg_rom usegs))) ->
  (* [comment removed for export] *)
  (~ (ds_status d = 666 /\ flush <> 4) ->
   forall (y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me d m' ->
     evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                          (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x17328) fc None m' (seg_rom usegs))) ->
  evt usegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom usegs)).
Proof.
  intros until t6. intros DR DOUT ROOM STK MI HST HFL RAI RNI KERR KOK.
  pose proof DR as DR0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_S _ LAY) as BKS.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold Z_DEFLATE_PC. unfold Z_ZCALLOC, Z_ZCFREE in ZS. unfold Z_DEFL_EPI in KERR.
  pose proof (munch_refl (defl_W L rest0 lo r) me) as MU. unfold defl_W in MU. pose proof (wmono_refl usegs me) as WM.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r))] me) as MUf. pose proof (wmono_refl usegs me) as WMf.
  (* [comment removed for export] *)
  carve_frame 64%nat STK.
  do 8 zs. name_mem mP.
  assert (RST : 0 <= ds_status d < 1000) by lia.
  assert (RLP : relro_clean mP) by (apply (defl_relro L inp rest0 lo r me CTX); unfold defl_W; exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  assert (DRP : DREP mP L d).
  { apply (DREP_agree me mP L d DR0).
    - eapply ag_blocks_munch; [exact LAY1| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
    - apply (agree_on_of_munch [(lo, bv_unsigned (r_sp r))]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
  assert (DOUTP : dout mP L rest0 (ds_strm d)) by (apply (dout_munch _ me mP L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
  (* [comment removed for export] *)
  zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|].
  zstep. al8 (dl_S L). gT.
  zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].
  zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zs. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia; [exfalso; lia|].
  zstep. al8 (dl_As L). gT.
  zs. zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia; [exfalso; lia|].
  zs.
  (* [comment removed for export] *)
  assert (C_DD4 : forall a14 a15 : word,
    evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (r_s1 r) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) a14 a15 a6 a7
                     (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x172c0) fc None mP (seg_rom usegs))).
  { intros a14 a15. pose proof (unbox _ ROOM) as RM0.
    zstep. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia; [exfalso; lia|].
    zs. zstep. zstep. if_cases KNO; zify_cond KNO; rewrite ?unsigned_lit in KNO by lia; [exfalso; lia|].
    zs. zstep.
    (* [comment removed for export] *)
    assert (C_DF8 : forall a15' : word,
      evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) a15' a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x172e4) fc None mP (seg_rom usegs))).
    { intros a15'. zstep. zstep.
      assert (SIP : DINV L rest0 lo r me d mP).
      { split; [exact DRP|]. split; [exact DOUTP|]. split; [exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      if_cases KF4; zify_cond KF4; rewrite ?unsigned_lit in KF4 by lia.
      - eapply (KOK ltac:(lia)). exact SIP.
      - zstep. zstep. if_cases KS6; zify_cond KS6; rewrite ?unsigned_lit in KS6 by lia.
        + eapply (KOK ltac:(lia)). exact SIP.
        + (* [comment removed for export] *)
          clear MUf WMf ZS GA. destruct DRP as [ZSP STP]. open_zs ZSP.
          pose proof (munch_refl [(dl_S L, dl_S L + 112)] mP) as MUg. pose proof (wmono_refl usegs mP) as WMg.
          zstep. zs. zstep. gT. zs. zs. name_mem mE. zstep.
          eapply (KERR ltac:(lia)).
          split; [split|].
          { unfold err_return, Z_STREAM_ERROR, MSG_ERR. cbn [fst]. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
            do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZSP. }
          { apply DST_set_strm; [intros HB; exact HB|].
            apply (DST_agree mP mE L d STP). eapply ag_blocks_munch; [exact LAY1| exact MUg| exact WMg| | | | |]; cbn [disjoint_from]; slia. }
          { split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ mP mE L rest0 _ DOUTP ROOM MUg WMg); cbn [disjoint_from]; slia|].
            split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
            split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. } }
    if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
    - apply C_DF8.
    - zs. zstep. if_cases KNI; zify_cond KNI; rewrite ?unsigned_lit in KNI by lia; [exfalso; lia|]. apply C_DF8. }
  clear KERR KOK.
  zstep. zstep. zstep.
  destruct HST as [E|[E|E]]; rewrite E in *.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zstep. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [exfalso; lia|].
    zstep. zstep. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia; [|exfalso; lia].
    apply C_DD4.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [exfalso; revert KS; vm_compute; intros KS; discriminate KS|].
    zstep. zs. zstep. zstep. zstep.
    if_cases KM; zify_cond KM; [exfalso; revert KM; vm_compute; intros KM; discriminate KM|].
    apply C_DD4.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zstep. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [|exfalso; lia].
    apply C_DD4.
Qed.
End ENTRYG.

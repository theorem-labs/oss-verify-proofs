(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC7_rd ECH_AC7_read ECH_AC7_rd2 ECH_AC7_bioread
  ECH_AKitS ECH_AC9_kit ECH_AC9_ctrl ECH_AC9_push ECH_AC9_rdseg ECH_AC9_rdloop ECH_AC9_read.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64 ECH_C9_rdfacts.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma clr128_facts9 : forall x, 0 <= x < 2^31 -> 0 <= Z.land x 18446744073709551487 < 2^31 /\ Z.land (Z.land x 18446744073709551487) 128 = 0.
Proof.
  intros x Hx. split; [apply land_lt_pow2; lia|]. rewrite <- Z.land_assoc. change (Z.land 18446744073709551487 128) with 0. apply Z.land_0_r.
Qed.

Definition ard_conv (rv : Z) : Z := if 0 <? rv then 1 else rv.
Definition ard_rbv (rv : Z) : Z := if 0 <? rv then rv else 0.
Definition ABREADCONV_B64_STACK : Z := FR_bread_conv + Z.max B64READ_STACK BIOCTRL_B64_STACK.
Definition AREADINTERN_B64_STACK : Z := FR_bio_read_intern + ABREADCONV_B64_STACK.

(* [comment removed for export] *)
Lemma munch_grow9 : forall (lo hi hi' : Z) (XS W Wc : list (Z * Z)) m0 m1 m2,
  munch ((lo, hi) :: W) m0 m1 -> munch ((lo, hi') :: XS ++ Wc) m1 m2 -> hi' <= hi ->
  (forall x, outside W x -> outside Wc x) -> munch ((lo, hi) :: XS ++ W) m0 m2.
Proof.
  intros lo hi hi' XS W Wc m0 m1 m2 M1 M2 LE SUB. eapply munch_trans.
  - eapply munch_weaken; [| exact M1]. intros x Hx. cbn in Hx |- *. destruct Hx as [H1 H2]. apply outside_app in H2. destruct H2 as [_ H2]. split; [exact H1| exact H2].
  - eapply munch_weaken; [| exact M2]. intros x Hx. cbn in Hx |- *. destruct Hx as [H1 H2]. apply outside_app in H2. destruct H2 as [H2 H3].
    split; [lia|]. apply outside_app. split; [exact H2| exact (SUB _ H3)].
Qed.
Lemma munch_absorb9 : forall (lo hi : Z) (XS W Wl : list (Z * Z)) m0 m1 m2,
  munch ((lo, hi) :: XS ++ W) m0 m1 -> munch Wl m1 m2 -> (forall x, outside ((lo, hi) :: W) x -> outside Wl x) -> munch ((lo, hi) :: XS ++ W) m0 m2.
Proof.
  intros lo hi XS W Wl m0 m1 m2 M1 M2 SUB. eapply munch_trans; [exact M1|]. eapply munch_weaken; [| exact M2].
  intros x Hx. apply SUB. cbn in Hx |- *. destruct Hx as [H1 H2]. apply outside_app in H2. destruct H2 as [_ H2]. split; [exact H1| exact H2].
Qed.

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



Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HX.
  (* [comment removed for export] *)
  Hypothesis BRMS : bioread_mem_stmt H.
  Hypothesis GDS : biogetdata_stmt H.
  Hypothesis NXS : bionext_stmt H.
  Hypothesis CFS : bioclearflags_stmt H.
  Hypothesis TFS : biotestflags_stmt H.
  Hypothesis DUS : decupdate_stmt H.
  Hypothesis DFS : decfinal_stmt H.
  Hypothesis DIS : decinit_stmt H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac nzal X := rewrite ?v_sltu_b2z, ?v_sltiu_b2z; rewrite ?(unsigned_lit 0) by lia; rewrite ?(unsigned_lit X) by lia; rewrite (proj2 (Z.ltb_lt 0 X)) by lia; if_lit.
  Local Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => hide H end.
  Local Ltac hlia := first [lia | unfold hidden in *; lia].
  (* [comment removed for export] *)
  Local Ltac aconst_of AC MU WM :=
    eapply ACONST_frame; [exact AC| exact MU| exact WM|];
    repeat (apply Forall_cons;
            [cbn [fst snd]; first [ assumption
                                  | apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia
                                  | match goal with X : aapp ?A ?n |- _ => eapply (aconst_ok_aapp A n _ _ X); cbn; lia end
                                  | match goal with X : hidden (aapp ?A ?n) |- _ => eapply (aconst_ok_aapp A n _ _ X); cbn; lia end ] |]);
    apply Forall_nil.
  Local Ltac bio_unf X := unfold bio_cells, b64f_bio, membio_bio, bf_with_hdr, wz in X;
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
         bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset] in X;
    unfold A_b64_method, A_mem_buf_method in X.
  Local Ltac bio_unf_goal := unfold bio_cells, b64f_bio, membio_bio, bf_with_hdr, wz;
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
         bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset];
    unfold A_b64_method, A_mem_buf_method.

  Definition ABRB_RA1 : Z := 0x23970c.   (* [comment removed for export] *)
  Definition ABRB_RA2 : Z := 0x23977c.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma abreadconv_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (sA : as_St H)
           (a mb out outl rbp rbv lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX H LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at asegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      rbp mod 8 = 0 -> rw_cells asegs m rbp [C8 (wz rbv)] -> memrd_out mb M rbp 8 lo (bv_unsigned sp) ->
      (rbp + 8 <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= rbp) ->
      Forall (fun b => rbp + 8 <= blk_addr b \/ blk_addr b + blk_size b <= rbp) (blocks_B64F a R) ->
      (rbp + 8 <= out \/ out + outl <= rbp) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> PAYLOAD_shad m M -> OUT_shad m out outl -> RB_shad m rbp ->                                    (* [comment removed for export] *)
      aapp rbp 8 -> fsobj H LF rbp 8 -> afs_write_ok H LF (rbp, rbp + 8) -> aclient_write_ok H LB (rbp, rbp + 8) ->              (* [comment removed for export] *)
      shvis m (bf_ctx R) (bf_ctx R + B64CTX_SIZE) -> in_app_mem (bf_ctx R) (bf_ctx R + B64CTX_SIZE) ->
      ACONST m -> arelro_lib m ->
      as_RFS H LF m -> (S (length LF) < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> as_RHEAP H sA LB m -> bv_unsigned sp mod 16 = 0 ->
      fsobj H LF out outl -> fsobj H LF (mb_buf M) (mb_len M) ->
      afs_write_ok H LF (out, out + outl) -> aclient_write_ok H LB (out, out + outl) -> AIMG_TOP <= out ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ABREADCONV_B64_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      let res := b64_read_spec (map bv_unsigned txt) outl in
      evt asegs (b64rd_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF sA (ard_conv (br_rv res)) a R (bf_nread R) mb M txt
                   out (br_out res) outl (br_used res) (Some (rbp, ard_rbv (br_rv res)))
                   ((out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bread_conv) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros A0 A1 A2 A3 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT RBAL RBC MORB RBMB RBF RBO METHB METHM
      BSH MSH PAY OSH RSH RAP RFO ARW RCW CVIS CIA AC RL RFS LFB TP HP SPA FOO FOP AFW ACW OTOP ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3.
    unfold P_bread_conv in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOS : lo <= bv_unsigned sp + -64 - B64READ_STACK /\ lo <= bv_unsigned sp + -64 - BIOCTRL_B64_STACK).
    { revert LO. unfold ABREADCONV_B64_STACK, FR_bread_conv. clear. intros; lia. }
    destruct LOS as [LOSr LOSc].
    assert (LO64 : lo <= bv_unsigned sp + -64).
    { revert LOSc. unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & ACE & AFS & AAP). pose proof RB2 as (CP & _ & _ & CH & CCE & CFSB & CAP). pose proof RB3 as (EP & _ & _ & EH & ECE & EFSB & EAP).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MORB as (RBR & RBP & RBH & RBFM & RBB & RBM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MCE & MFSB & MAP). pose proof RM2 as (BBP & _ & _ & BBH & BBCE & _ & BBAP).
    pose proof RM3 as (BMP & _ & _ & BMH & BMCE & _ & BMAP). pose proof RM4 as (RPP & _ & _ & RPH & RPCE & _ & RPAP).
    pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof (Forall_inv RBFM) as RF1. pose proof (Forall_inv (Forall_inv_tail RBFM)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBFM))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBFM)))) as RF4.
    cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4.
    pose proof (Forall_inv RBF) as RA1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RA3.
    cbn [blk_addr blk_size fst snd] in RA1, RA2, RA3.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE, AIMG_TOP in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      ACE, CCE, ECE, MCE, BBCE, BMCE, RPCE, AAP, CAP, EAP, MAP, BBAP, BMAP, RPAP, AFS, CFSB, EFSB, MFSB, I1, I2, I3, J1, J2, J3, J4,
      OF1, OF2, OF3, OF4, RF1, RF2, RF3, RF4, RA1, RA2, RA3, SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4, BBH, BMH, RPH.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM, RBM. unfold A_b64_method, O_METH_BREAD in OUTMB, RBMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    destruct BSH as (ADA & ADC & ADE). destruct PAY as (PACC & PVIS & PAPP). pose proof OSH as (OACC & OVIS & OAPP & OAOK). destruct RSH as (RACC & RAPP & RAOK).
    unfold BIO_SIZE, B64CTX_SIZE in ADA, ADC, CVIS, CIA.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX. unfold wz in RBC.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    pose proof METHB as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in MT. norm_addr MT.
    pose proof METHM as MTM. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MTM. norm_addr MTM.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & EIN & EBR & DINV).
    assert (IN : In (A_b64_method, 112, 112) aglobals) by (unfold A_b64_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(clear; lia)) as ADmt. unfold A_b64_method in ADmt.
    unfold zlength in TLEN, TLE.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_not_shadowland _ _ EAP) as NSe.
    pose proof (aapp_not_shadowland _ _ MAP) as NSm. pose proof (aapp_not_shadowland _ _ BMAP) as NSbm. pose proof (aapp_not_shadowland _ _ RAP) as NSr.
    hide_ors.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
             [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]).
    { unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; unhide NSr. clear - CEIL ACEILB OAPP RAPP NSa NSc NSe NSm NSbm NSr SPR. nsw_tac. }
    assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact ADA| clear; lia| clear; lia| clear - AH ACE ACEILB; unfold AAPP_HI; lia]).
    pose proof RACC as RACC0. change (id (accessible m rbp 8)) in RACC0. hide RACC0.
    assert (ACCmt : id (accessible m 0x5e75e0 112)) by (eapply addressable_accessible; [exact ADmt| clear; lia| clear; lia| clear; unfold AAPP_HI; lia]).
    hide AAP; hide CAP; hide EAP; hide MAP; hide BBAP; hide BMAP; hide RPAP; hide RAP.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    unhide OUTR; unhide RBR. do 9 step. hide RBR. hide OUTR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : id (accessible mx a 128)) by (unfold id in ACCa |- *; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]);
      assert (ACC2 : id (accessible mx 0x5e75e0 112)) by (unfold id in ACCmt |- *; eapply accessible_across2; [exact ACCmt| exact MU| exact NSW0]) end.
    clear ACCa ACCmt. unfold id in ACC1, ACC2.
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    step. step. zstep.
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { step. if_cases K1; zify_cond K1.
      - apply evt_done; subst TGT; reflexivity.
      - step. apply evt_done. subst TGT. repeat f_equal. lia. }
    subst TGT. cbv beta. intros ms' ->.
    (* [comment removed for export] *)
    step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check ACC1 (a + 8). st1.
    (* [comment removed for export] *)
    step. ub_dead. step. step. if_lit.
    zstep. zstep. zstep. ck8_check_lit ACC2 (0x5e75e0 + 40). st1. step. unfold P_b64_read. step.
    (* [comment removed for export] *)
    pose proof (b64read_spec H) as B64R.
    repeat first [ specialize (B64R HX) | specialize (B64R BRMS) | specialize (B64R GDS) | specialize (B64R NXS) | specialize (B64R CFS)
                 | specialize (B64R TFS) | specialize (B64R DUS) | specialize (B64R DFS) | specialize (B64R DIS) ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ADA1 : addressable mx a 128) by (eapply addressable_across2; [exact ADA| exact AAP| exact MU| exact WM| exact NSW0]);
      assert (ADC1 : addressable mx (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC| exact CAP| exact MU| exact WM| exact NSW0]);
      assert (ADE1 : addressable mx (bf_enc R) 92) by (eapply addressable_across2; [exact ADE| exact EAP| exact MU| exact WM| exact NSW0]) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RFS1 : as_RFS H LF mx) end.
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|]. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
      unhide AFS; unhide CFSB; unhide EFSB; unhide MFSB. pose proof RM3 as (_ & _ & _ & _ & _ & BMFS & _). unfold BUFMEM_SIZE in BMFS.
      clear - F1 F2 F3 F4 AFS CFSB EFSB MFSB BMFS AFW ARW CEIL LO64 SPR AH CH EH MH BMH ACEILB.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [ exact AFW | exact ARW | left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; split; lia ].
      all: fail. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (HP1 : as_RHEAP H sA LB mx) end.
    { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
      repeat apply Forall_cons; try apply Forall_nil;
        first [ exact ACW | exact RCW | left; cbn [fst snd]; lia
              | right; right; left; cbn [fst snd]; first [ exists (bf_id R, a, 128); split; [exact I1| cbn; lia] | exists (bf_cid R, bf_ctx R, 2584); split; [exact I2| cbn; lia]
                                          | exists (bf_eid R, bf_enc R, 92); split; [exact I3| cbn; lia] | exists (mb_id M, mb, 128); split; [exact J1| cbn; lia]
                                          | exists (mb_bmid M, mb_bm M, 32); split; [exact J3| cbn; lia] ]
              ].
      all: fail. }
    eapply evt_cut.
    { eapply B64R with (lo := lo) (R := R) (LB := LB) (LF := LF) (sA := sA) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl);
        rewrite ?unsigned_lit by (clear - SPR LO64 LO0; lia); try reflexivity.
      all: lazymatch goal with
           | |- B64F_fresh _ _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| exact BX]|];
                                        exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact EIN|]; split; [exact EBR| exact DINV]
           | |- MEMBIO _ _ _ _ _ => membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; split; [clear - OUTR; lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - OUTM; lia
           | |- Forall _ _ => first [exact APO | exact APM | exact APT]
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact MT
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact MTM
           | |- B64F_shad _ _ _ => exact (conj ADA1 (conj ADC1 ADE1))
           | |- MEMBIO_shad _ _ _ => exact (MEMBIO_shad_across2 H LB _ m _ _ mb M MB MSH MU WM NSW0)
           | |- PAYLOAD_shad _ _ => split; [| split]; [eapply accessible_across2; [exact PACC| exact MU| exact NSW0]| eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| exact PAPP]
           | |- OUT_shad _ _ _ => pose proof OACC as (_ & OHI & _); split; [| split; [| split]]; [eapply accessible_across2; [exact OACC| exact MU| exact NSW0]| eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| lia| exact NSW0]| exact OAPP| exact OAOK]
           | |- shvis _ _ _ => unfold B64CTX_SIZE; eapply shvis_across2; [exact CVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia| exact NSW0]
           | |- in_app_mem _ _ => exact CIA
           | |- ACONST _ => aconst_of AC MU WM
           | |- arelro_lib _ => eapply arelro_across7; [exact RL| exact MU|]; clear - AH CH EH MH BMH OTOP LO64 CEIL ACEILB RAP; unfold hidden, aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in RAP, OTOP;
                               repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia
           | |- as_RFS _ _ _ => exact RFS1
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- _ = Z_to_bv 64 ATP => exact TP
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- fsobj _ _ _ _ => first [exact FOO| exact FOP]
           | |- afs_write_ok _ _ _ => exact AFW
           | |- aclient_write_ok _ _ _ => exact ACW
           | |- AIMG_TOP <= _ => exact OTOP
           | |- stk _ _ _ _ => exact ST
           | |- aceil <= _ => exact CEIL
           | |- _ <= _ - B64READ_STACK => exact LOSr
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
          end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk' & XS
                    & -> & FX & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & _ & ACp & RFSp & RLp & HPp).
    rewrite ?unsigned_lit in MUc by (clear - SPR LO64 LO0; lia). rewrite ?unsigned_lit in STc by (clear - SPR LO64 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    replace (ret_pc (Z_to_bv 64 2332428)) with (Z_to_bv 64 2332428) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    assert (APW : Forall appwin [(out, out + outl); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]).
    { unfold appwin. unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm. clear - OAPP NSa NSc NSe NSm NSbm ACEILB. nsw_tac. }
    assert (FSa : fsobj H LF a 128) by (eapply (fsobj_block H HH); [exact HP| exact I1]).
    assert (FSc : fsobj H LF (bf_ctx R) 2584) by (eapply (fsobj_block H HH); [exact HP| exact I2]).
    assert (FSe : fsobj H LF (bf_enc R) 92) by (eapply (fsobj_block H HH); [exact HP| exact I3]).
    (* [comment removed for export] *)
    lazymatch type of MUc with munch ?Wc ?ma ?mb0 =>
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FR;
        [| apply disjoint_from_callee; [right; cbn; clear; lia
                                       | eapply disjoint_from_Forall; [exact FX|]; intros iv Hiv; pose proof (fs_scratch_below_ceil H HH _ _ _ RFS Hiv); cbn; clear - H0 CEIL LO64; lia
                                       | cbn; unhide OUTR; clear - OUTR BL1 BL2 BL3 ML1 ML3 SPR LO64; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in RBC;
        [| apply disjoint_from_callee; [unhide RBR; cbn; clear - RBR; lia
                                       | unhide RAP; pose proof RACC as (_ & RHI & _); eapply (disjoint_of_scratch H HH); [exact RFS1| exact RFO| clear - RBP; lia| clear; lia| exact RHI| exact RAP| exact FX]
                                       | cbn; unhide RBO; unhide RA1; unhide RA2; unhide RA3; unhide RF1; unhide RF3; clear - RBO RA1 RA2 RA3 RF1 RF3; lia]]
    end.
    lazymatch type of MUc with munch _ ?ma ?mb0 =>
      assert (ACCa2 : id (accessible mb0 a 128)) by (unfold id; eapply (accessible_across3 H HH); [exact ACC1| exact RFS1| exact FSa| clear; lia| exact MUc| exact CEIL| exact FX| exact APW]);
      assert (RACC1 : accessible ma rbp 8) by (pose proof RACC0 as K; unfold hidden, id in K; eapply accessible_across2; [exact K| exact MU| exact NSW0]);
      assert (RACC2 : id (accessible mb0 rbp 8)) by (unfold id; eapply (accessible_across3 H HH); [exact RACC1| exact RFS1| exact RFO| clear; lia| exact MUc| exact CEIL| exact FX| exact APW]);
      assert (ADA2 : addressable mb0 a 128) by (eapply (addressable_across3 H HH); [exact ADA1| exact RFS1| exact FSa| clear - AP; lia| clear - AH ACE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW]);
      assert (ADC2 : addressable mb0 (bf_ctx R) 2584) by (eapply (addressable_across3 H HH); [exact ADC1| exact RFS1| exact FSc| clear - CP; lia| clear - CH CCE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW]);
      assert (ADE2 : addressable mb0 (bf_enc R) 92) by (eapply (addressable_across3 H HH); [exact ADE1| exact RFS1| exact FSe| clear - EP; lia| clear - EH ECE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW])
    end.
    clear ACC1 ACC2 RACC1 ADA1 ADC1 ADE1 RFS1 HP1.
    (* [comment removed for export] *)
    pose proof (munch_grow9 _ _ _ XS _ _ _ _ _ MU MUc ltac:(clear - SPR; lia) ltac:(clear; intros x Hx; cbn in Hx |- *; tauto)) as MUX.
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMX. clear MU WM MUc WMc. hide MUX. hide WMX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)] m') as MU. pose proof (wmono_refl asegs m') as WM.
    assert (NSWl : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)]).
    { unhide NSa; unhide NSr. clear - CEIL ACEILB NSa NSr. nsw_tac. }
    clear ST MI. rename STc into ST. rename MIc into MI. clear BC BX EC MC MBB MBM MRP TXT OUTC MT MTM.
    (* [comment removed for export] *)
    bio_unf BCp. unfold b64ctx_used_cells, wz in CTXp.
    destruct ENCp as (raw2 & line2 & RAWL2 & RAWP2 & ECp & LINE2 & _ & _ & DINV2).
    pose proof MBp as MBp0. destruct MBp0 as (MCp & MBBp & MBMp & MRPp & MBpure). clear MBp. bio_unf MCp. unfold buf_cells, wz in MBMp, MRPp. cbn [bm_len bm_data bm_max bm_flags] in MBMp, MRPp. unfold wz in MBBp.
    pose proof METHBp as METHB1. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB1. norm_addr METHB1.
    pose proof METHMp as METHM1. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM1. norm_addr METHM1.
    clear METHBp METHMp.
    cbn [mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mb_flags mb_nread mset] in MCp, MBBp, MBMp, MRPp.
    unfold id in ACCa2, RACC2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_load ACCa2 (a + 48). step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1. rewrite ?zx32_lit by (clear - FLp; lia). zstep.
    pose proof (clr128_facts9 fl FLp) as [FL2 FL3]. set (fl2 := Z.land fl 18446744073709551487) in *.
    unfold zlength in ZLE.
    assert (DJo : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) a 128).
    { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide OA1. clear - OA1 ZLE OUTL. lia. }
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm.
    pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp. clear APM1.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp.
    pose proof (Forall_inv APT) as PT1'. cbn [blk_addr blk_size fst snd] in PT1'. unfold BIO_SIZE in PT1'.
    (* [comment removed for export] *)
    assert (DK1 : chunk_disj (bf_ctx R) 2584 a 128) by (unhide BA1; clear - BA1; unfold chunk_disj; lia).
    assert (DK2 : chunk_disj (bf_enc R) 92 a 128) by (unhide BA2; clear - BA2; unfold chunk_disj; lia).
    assert (DK3 : chunk_disj mb 128 a 128) by (clear - DJ_a_mb; unfold chunk_disj; lia).
    assert (DK4 : chunk_disj (mb_bb M) 16 a 128) by (clear - DJ_a_bb; unfold chunk_disj; lia).
    assert (DK5 : chunk_disj (mb_bm M) 32 a 128) by (clear - DJ_a_bm; unfold chunk_disj; lia).
    assert (DK6 : chunk_disj (mb_rp M) 32 a 128) by (clear - DJ_a_rp; unfold chunk_disj; lia).
    assert (DK7 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) a 128) by (clear - PT1' TLEN; unfold chunk_disj; lia).
    assert (DK8 : chunk_disj rbp 8 a 128) by (unhide RA1; clear - RA1; unfold chunk_disj; lia).
    hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp; hide PT1'.
    st1.
    change (Z_to_bv 64 fl2) with (wz fl2) in *.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DR1 : chunk_disj a 128 rbp 8) by (unhide RA1; clear - RA1; unfold chunk_disj; lia).
    assert (DR2 : chunk_disj (bf_ctx R) 2584 rbp 8) by (unhide RA2; clear - RA2; unfold chunk_disj; lia).
    assert (DR3 : chunk_disj (bf_enc R) 92 rbp 8) by (unhide RA3; clear - RA3; unfold chunk_disj; lia).
    assert (DR4 : chunk_disj mb 128 rbp 8) by (unhide RF1; clear - RF1; unfold chunk_disj; lia).
    assert (DR5 : chunk_disj (mb_bb M) 16 rbp 8) by (unhide RF2; clear - RF2; unfold chunk_disj; lia).
    assert (DR6 : chunk_disj (mb_bm M) 32 rbp 8) by (unhide RF3; clear - RF3; unfold chunk_disj; lia).
    assert (DR7 : chunk_disj (mb_rp M) 32 rbp 8) by (unhide RF4; clear - RF4; unfold chunk_disj; lia).
    assert (DR8 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) rbp 8) by (unhide RBB; clear - RBB TLEN; unfold chunk_disj; lia).
    assert (DR9 : chunk_disj (bv_unsigned sp + -64) 64 rbp 8) by (unhide RBR; clear - RBR LO64; unfold chunk_disj; lia).
    assert (DR10 : chunk_disj 6190592 64 rbp 8) by (unhide RBMB; clear - RBMB; unfold chunk_disj; lia).
    assert (DR11 : chunk_disj 5957056 64 rbp 8) by (unhide RBM; clear - RBM; unfold chunk_disj; lia).
    assert (DR12 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) rbp 8).
    { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide RBO. clear - RBO ZLE OUTL. lia. }
    (* [comment removed for export] *)
    assert (FIN : forall mf, munch [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)] m' mf -> wmono asegs m' mf ->
              ACONST mf /\ as_RFS H LF mf /\ arelro_lib mf /\ as_RHEAP H sA LB mf /\ munch ((lo, bv_unsigned sp) :: XS ++ [(out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]) m mf /\ wmono asegs m mf).
    { intros mf MUl WMl. split; [| split; [| split; [| split; [| split]]]].
      - aconst_of ACp MUl WMl.
      - eapply (ah_RFS_frame H HH); [exact RFSp| exact MUl| exact WMl|]. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
        unhide AFS. clear - F1 F2 F3 F4 AFS ARW CEIL LO64 SPR AH ACEILB.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; first [ exact ARW | left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; split; lia ].
      - eapply arelro_across7; [exact RLp| exact MUl|]. unhide RAP. clear - AH LO64 CEIL ACEILB RAP. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in RAP.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
      - eapply (ah_RHEAP_frame H HH); [exact HPp| exact MUl| exact WMl|].
        repeat apply Forall_cons; try apply Forall_nil; first [ exact RCW | left; cbn [fst snd]; lia | right; right; left; cbn [fst snd]; exists (bf_id R, a, 128); split; [exact I1| cbn; lia] ].
      - unhide MUX. eapply munch_absorb9; [exact MUX| exact MUl|]. clear. intros x Hx. cbn in Hx |- *. tauto.
      - unhide WMX. exact (wmono_trans _ _ _ _ WMX WMl). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (br_rv res) 0) as [RZ|RNZ].
    - (* [comment removed for export] *)
      rewrite RZ in *. specialize (CZ eq_refl).
      step. if_true. step. step. step. step. unfold P_BIO_ctrl. step.
      pose proof (abioctrl_b64_spec H) as BCS. unfold bioctrl_b64_stmt in BCS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (ADA3 : addressable mx a 128) by (eapply addressable_across2; [exact ADA2| unhide AAP; exact AAP| exact MU| exact WM| exact NSWl]);
        assert (ADC3 : addressable mx (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC2| unhide CAP; exact CAP| exact MU| exact WM| exact NSWl]);
        assert (ADE3 : addressable mx (bf_enc R) 92) by (eapply addressable_across2; [exact ADE2| unhide EAP; exact EAP| exact MU| exact WM| exact NSWl]) end.
      eapply evt_cut.
      { eapply BCS with (lo := lo) (LB := LB) (a := a) (mb := mb) (cmd := BIO_CTRL_EOF) (parg := 0) (R := bf_with_hdr R fl2 rt (bf_nread R) mb (bf_prev R)) (M := M)
                        (hdr := hdr) (junk := cjunk) (elen := 0) (cont := c);
          cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by (clear - SPR LO64 LO0; lia); try reflexivity.
        all: lazymatch goal with
             | |- 0 <= 0 < _ => clear; lia
             | |- rw_cells _ _ _ (bio_cells _) => bio_unf_goal; exact BCp
             | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTXp
             | |- B64F_blocks _ _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr];
                                          split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FL2|]; split; [exact RTp|]; split; [exact NRR|]; split; [clear - MP MH ACEILB MCE; lia| exact PVR]
             | |- B64F_below _ _ _ => exact BEL
             | |- length _ = _ => exact LH
             | |- map _ _ = _ => exact CONT
             | |- _ \/ _ => right; split; [reflexivity| clear - CR CZ; lia]
             | |- B64F_apart _ _ => exact BAP
             | |- B64F_shad _ _ _ => exact (conj ADA3 (conj ADC3 ADE3))
             | |- ACONST _ => aconst_of ACp MU WM
             | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1
             | |- stk _ _ _ _ => exact ST
             | |- aceil <= _ => exact CEIL
             | |- _ <= _ - BIOCTRL_B64_STACK => exact LOSc
             | |- mem_inv _ _ => assumption
             | |- _ mod 2 = 0 => reflexivity
            end. }
      cbv beta. clear BCS. unfold BIO_SIZE.
      aland_open MU.
      carry1 MUc WMc FR. carry1 MUc WMc RBC using RBR RA1. carry1 MUc WMc CTXp using BA1. carry1 MUc WMc ECp using BA2.
      unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp; unhide PT1'.
      carry1 MUc WMc MCp. carry1 MUc WMc MBBp. carry1 MUc WMc MBMp. carry1 MUc WMc MRPp. carry1 MUc WMc TXTp.
      hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp; hide PT1'.
      carry1k MUc WMc OUTp by (unhide OUTR; unhide OA1; clear - OUTp MUc WMc OUTR OA1 ZLE OUTL LO64 SPR).
      carry1 MUc WMc METHB1. carry1 MUc WMc METHM1.
      aland_close MU WM MUc WMc.
      match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC3; bio_unf BC3 end.
      (* [comment removed for export] *)
      step. if_lit.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (RACC3 : accessible mx rbp 8) by (eapply accessible_across2; [exact RACC2| exact MU| exact NSWl]) end.
      step. ub_dead. step. ubal_by RBAL. step. if_lit. step. zstep. zstep. ck8_check RACC3 rbp.
      change (Z_to_bv 64 0 : word) with (wz 0) at 2.
      st1.
      do 7 st1. step. step. release_frame FR ST (bv_unsigned sp).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
      apply evt_done. change (ard_conv 0) with 0. change (ard_rbv 0) with 0. unfold b64rd_post.
      do 15 eexists. exists fl2, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
      split; [reflexivity|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
      split; [assumption|]. split; [exact ST|].
      split; [bio_unf_goal; exact BC3|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
      split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros _; exact CZ|].
      split; [clear - RVR OUTL; lia|]. split; [unfold zlength; exact ZLE|].
      split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
      split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
               split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
               split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
      split; [exact TXTp|]. split; [exact OUTp|].
      split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
      split. { match goal with X : rw_cells asegs _ rbp _ |- _ => unfold wz; split; [exact X| clear - OUTL; lia] end. }
      exact (conj ACf (conj RFSf (conj RLf HPf))).
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (br_rv res) 0) as [NEG|NNEG].
      + assert (RM : br_rv res = -1) by (clear - NEG RVR; lia). rewrite RM in *.
        (* [comment removed for export] *)
        step. if_cases K1; zify_cond K1; [clear - K1; lia|]. clear K1.
        do 4 step. step. if_cases K2; zify_cond K2; [| exfalso; clear - K2; lia]. clear K2.
        go. ubal_by RBAL. nzal rbp. go.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (RACC3 : accessible mx rbp 8) by (eapply accessible_across2; [exact RACC2| exact MU| exact NSWl]) end.
        ck8_check RACC3 rbp.
        change (Z_to_bv 64 0 : word) with (wz 0) at 1.
        st1.
        do 7 st1. step. step. release_frame FR ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
        apply evt_done. change (ard_conv (-1)) with (-1). change (ard_rbv (-1)) with 0. unfold b64rd_post.
        do 15 eexists. exists fl2, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
        split; [reflexivity|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
        split; [assumption|]. split; [exact ST|].
        split; [bio_unf_goal; exact BCp|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E; cbn in E; lia|].
        split; [clear - RVR OUTL; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split. { match goal with X : rw_cells asegs _ rbp _ |- _ => unfold wz; split; [exact X| clear - OUTL; lia] end. }
        exact (conj ACf (conj RFSf (conj RLf HPf))).
      + assert (POS : 0 < br_rv res < 2^31) by (clear - RNZ NNEG RVR OUTL; lia). clear RNZ NNEG.
        (* [comment removed for export] *)
        step. if_cases K1; zify_cond K1; [exfalso; clear - K1 POS; lia|]. clear K1.
        do 4 step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit, ?signed_lit in K2 by (clear - POS; lia); [exfalso; clear - K2 POS; lia|]. clear K2.
        ubal_by RBAL. step. nzal rbp. step. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (RACC3 : accessible mx rbp 8) by (eapply accessible_across2; [exact RACC2| exact MU| exact NSWl]) end.
        zstep. zstep. ck8_check RACC3 rbp.
        st1.
        do 7 st1. step. step. release_frame FR ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
        apply evt_done. unfold b64rd_post, ard_conv, ard_rbv. replace (0 <? br_rv res) with true by (symmetry; apply Z.ltb_lt; clear - POS; lia). cbv iota.
        do 15 eexists. exists fl2, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
        split; [reflexivity|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
        split; [assumption|]. split; [exact ST|].
        split; [bio_unf_goal; exact BCp|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E POS; lia|].
        split; [clear - RVR OUTL POS; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split. { match goal with X : rw_cells asegs _ rbp _ |- _ => unfold wz; split; [exact X| clear - OUTL RVR POS; lia] end. }
        exact (conj ACf (conj RFSf (conj RLf HPf))).
  Qed.

  Lemma abioeof_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb lo : Z) (R : b64frep) (M : membio)
           (hdr junk : list byte) (cont : Z),
      a0 = Z_to_bv 64 a ->
      rw_cells asegs m a (bio_cells (b64f_bio R)) -> bf_next R = mb -> B64F_blocks H LB a R -> B64F_below a R lo ->
      rw_cells asegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk 0) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [cont; cont / 256; cont / 65536; cont / 16777216] ->
      - 2^31 <= cont <= 0 ->
      B64F_apart a R -> B64F_shad m a R -> ACONST m -> METH_b64 m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - (FR_BIO_eof + BIOCTRL_B64_STACK) -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m'
                   /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' a (bio_cells (b64f_bio R)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs)).
  Proof.
    intros until cont. intros A0 BC NX BLK BEL CTX LH CONT CR APT BSH AC MT ST CEIL LO MI RAE. subst a0.
    unfold P_BIO_eof in *. acb.
    assert (LOc : lo <= bv_unsigned sp + -16 - BIOCTRL_B64_STACK) by (revert LO; unfold FR_BIO_eof; clear; intros; lia). clear LO.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO16 : lo <= bv_unsigned sp + -16).
    { revert LOc. unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & _ & _ & AAP).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BSH as (SHa & SHc & SHe).
    unfold BIO_SIZE, B64CTX_SIZE, AIMG_TOP in BL1, BL2, BL3, AH, SHa, SHc, AAP.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _). unfold AAPP_HI in AHIa.
    assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SHa| lia| lia| unfold AAPP_HI; lia]).
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128)]) by nsw_tac.
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold b64ctx_used_cells, wz in CTX.
    carve_frame 16%nat ST.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCa1 : accessible mx a 128) by (unfold id in ACCa; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]) end.
    step. ub_dead. step. ubal_by AAL. step. if_lit. step. step. step. zstep. zstep. zstep. ck8_check ACCa1 (a + 48).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (BCx : rw_cells asegs mc a (bio_cells (b64f_bio R)))
        by (unfold bio_cells, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact BC) end.
    pose proof (bio_flags_byte _ _ _ BCx) as RD. cbn [bio_flags b64f_bio] in RD. clear BCx.
    st1. clear RD. zstep. rewrite wz_unsigned by (clear - FLR; pose proof (Z.mod_pos_bound (bf_flags R) 256); lia).
    rewrite land_mod256_128 by (clear - FLR; lia).
    step. if_cases K2; zify_cond K2.
    - go. step. release_frame FR ST (bv_unsigned sp). finish.
      all: first [ eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
                 | unfold bio_cells, b64f_bio, wz;
                   cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact BC ].
    - step. step. step. unfold P_BIO_ctrl. step.
      pose proof (abioctrl_b64_spec H) as BCS. unfold bioctrl_b64_stmt in BCS.
      eapply evt_cut.
      { eapply BCS with (lo := lo) (LB := LB) (a := a) (mb := mb) (cmd := BIO_CTRL_EOF) (parg := 0) (R := R) (M := M)
                        (hdr := hdr) (junk := junk) (elen := 0) (cont := cont);
          rewrite ?unsigned_lit by lia; try reflexivity.
        all: lazymatch goal with
             | |- 0 <= 0 < _ => clear; lia
             | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz;
                                                 cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact BC
             | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTX
             | |- bf_next _ = _ => exact NX
             | |- B64F_blocks _ _ _ _ => exact BLK
             | |- B64F_below _ _ _ => exact BEL
             | |- length _ = _ => exact LH
             | |- map _ _ = _ => exact CONT
             | |- _ \/ _ => right; split; [reflexivity| exact CR]
             | |- B64F_apart _ _ => exact APT
             | |- B64F_shad _ _ _ => split; [| split]; (eapply addressable_across2; [eassumption| | exact MU| exact WM| exact NSW0]);
                                     [exact AAP| destruct RB2 as (_ & _ & _ & _ & _ & _ & K); exact K| destruct RB3 as (_ & _ & _ & _ & _ & _ & K); exact K]
             | |- ACONST _ => eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
             | |- METH_b64 _ => unfold METH_b64 in MT |- *; eapply rw_cells_transport; [exact MT| exact MU| exact WM|
                                 unfold A_b64_method, O_METH_BREAD; cbn; first [lia | pose proof aceil_range; unfold AIMG_TOP in *; lia]]
             | |- stk _ _ _ _ => exact ST
             | |- aceil <= _ => exact CEIL
             | |- _ <= _ - BIOCTRL_B64_STACK => exact LOc
             | |- mem_inv _ _ => assumption
             | |- _ mod 2 = 0 => reflexivity
             end. }
      clear BCS. cbv beta. unfold BIO_SIZE. alandx MU WM. change (b64ctrl_rv BIO_CTRL_EOF) with 1.
      go. step. release_frame FR ST (bv_unsigned sp). finish.
      all: first [ eapply ACONST_stack_obj6; [eassumption| exact MU| exact WM| exact CEIL| exact AAP| lia] | assumption ].
  Qed.

  Definition ARIB_RA1 : Z := 0x237910.   (* [comment removed for export] *)
  Definition ARIB_RA2 : Z := 0x2379f0.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma areadintern_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (sA : as_St H)
           (a mb out outl rbp rbv lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX H LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at asegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      rbp mod 8 = 0 -> rw_cells asegs m rbp [C8 (wz rbv)] -> memrd_out mb M rbp 8 lo (bv_unsigned sp) ->
      (rbp + 8 <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= rbp) ->
      Forall (fun b => rbp + 8 <= blk_addr b \/ blk_addr b + blk_size b <= rbp) (blocks_B64F a R) ->
      (rbp + 8 <= out \/ out + outl <= rbp) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> PAYLOAD_shad m M -> OUT_shad m out outl -> RB_shad m rbp ->                                    (* [comment removed for export] *)
      aapp rbp 8 -> fsobj H LF rbp 8 -> afs_write_ok H LF (rbp, rbp + 8) -> aclient_write_ok H LB (rbp, rbp + 8) ->              (* [comment removed for export] *)
      shvis m (bf_ctx R) (bf_ctx R + B64CTX_SIZE) -> in_app_mem (bf_ctx R) (bf_ctx R + B64CTX_SIZE) ->
      ACONST m -> arelro_lib m ->
      as_RFS H LF m -> (S (length LF) < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> as_RHEAP H sA LB m -> bv_unsigned sp mod 16 = 0 ->
      fsobj H LF out outl -> fsobj H LF (mb_buf M) (mb_len M) ->
      afs_write_ok H LF (out, out + outl) -> aclient_write_ok H LB (out, out + outl) -> AIMG_TOP <= out ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AREADINTERN_B64_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      let res := b64_read_spec (map bv_unsigned txt) outl in
      evt asegs (b64rd_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF sA (ard_conv (br_rv res)) a R (bf_nread R + ard_rbv (br_rv res)) mb M txt
                   out (br_out res) outl (br_used res) (Some (rbp, ard_rbv (br_rv res)))
                   ((out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bio_read_intern) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros A0 A1 A2 A3 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT RBAL RBC MORB RBMB RBF RBO METHB METHM
      BSH MSH PAY OSH RSH RAP RFO ARW RCW CVIS CIA AC RL RFS LFB TP HP SPA FOO FOP AFW ACW OTOP ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3.
    unfold P_bio_read_intern in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOS : lo <= bv_unsigned sp + -96 - ABREADCONV_B64_STACK /\ lo <= bv_unsigned sp + -96 - BIOCTRL_B64_STACK).
    { revert LO. unfold AREADINTERN_B64_STACK, ABREADCONV_B64_STACK, FR_bio_read_intern, FR_bread_conv. clear. intros; lia. }
    destruct LOS as [LOSr LOSc].
    assert (LO96 : lo <= bv_unsigned sp + -96).
    { revert LOSc. unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & ACE & AFS & AAP). pose proof RB2 as (CP & _ & _ & CH & CCE & CFSB & CAP). pose proof RB3 as (EP & _ & _ & EH & ECE & EFSB & EAP).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MORB as (RBR & RBP & RBH & RBFM & RBB & RBM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MCE & MFSB & MAP). pose proof RM2 as (BBP & _ & _ & BBH & BBCE & _ & BBAP).
    pose proof RM3 as (BMP & _ & _ & BMH & BMCE & _ & BMAP). pose proof RM4 as (RPP & _ & _ & RPH & RPCE & _ & RPAP).
    pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof (Forall_inv RBFM) as RF1. pose proof (Forall_inv (Forall_inv_tail RBFM)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBFM))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBFM)))) as RF4.
    cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4.
    pose proof (Forall_inv RBF) as RA1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RA3.
    cbn [blk_addr blk_size fst snd] in RA1, RA2, RA3.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE, AIMG_TOP in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      ACE, CCE, ECE, MCE, BBCE, BMCE, RPCE, AAP, CAP, EAP, MAP, BBAP, BMAP, RPAP, AFS, CFSB, EFSB, MFSB, I1, I2, I3, J1, J2, J3, J4,
      OF1, OF2, OF3, OF4, RF1, RF2, RF3, RF4, RA1, RA2, RA3, SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4, BBH, BMH, RPH.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM, RBM. unfold A_b64_method, O_METH_BREAD in OUTMB, RBMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    destruct BSH as (ADA & ADC & ADE). pose proof PAY as (PACC & PVIS & PAPP). pose proof OSH as (OACC & OVIS & OAPP & OAOK). pose proof RSH as (RACC & RAPP & RAOK).
    unfold BIO_SIZE, B64CTX_SIZE in ADA, ADC, CVIS, CIA.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX. unfold wz in RBC.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    pose proof METHB as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in MT. norm_addr MT.
    pose proof METHM as MTM. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MTM. norm_addr MTM.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & EIN & EBR & DINV).
    assert (IN : In (A_b64_method, 112, 112) aglobals) by (unfold A_b64_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(clear; lia)) as ADmt. unfold A_b64_method in ADmt.
    unfold zlength in TLEN, TLE.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_not_shadowland _ _ EAP) as NSe.
    pose proof (aapp_not_shadowland _ _ MAP) as NSm. pose proof (aapp_not_shadowland _ _ BMAP) as NSbm. pose proof (aapp_not_shadowland _ _ RAP) as NSr.
    hide_ors.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
             [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]).
    { unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; unhide NSr. clear - CEIL ACEILB OAPP RAPP NSa NSc NSe NSm NSbm NSr SPR. nsw_tac. }
    assert (NSWl : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)]).
    { unhide NSa; unhide NSr. clear - CEIL ACEILB NSa NSr. nsw_tac. }
    assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact ADA| clear; lia| clear; lia| clear - AH ACE ACEILB; unfold AAPP_HI; lia]).
    pose proof RACC as RACC0. change (id (accessible m rbp 8)) in RACC0. hide RACC0. pose proof ACCa as ACCa0. hide ACCa0.
    assert (ACCmt : id (accessible m 0x5e75e0 112)) by (eapply addressable_accessible; [exact ADmt| clear; lia| clear; lia| clear; unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    carve_frame 96%nat ST.
    unhide OUTR; unhide RBR. do 14 step. hide RBR. hide OUTR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : id (accessible mx a 128)) by (unfold id in ACCa |- *; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]);
      assert (ACC2 : id (accessible mx 0x5e75e0 112)) by (unfold id in ACCmt |- *; eapply accessible_across2; [exact ACCmt| exact MU| exact NSW0]) end.
    clear ACCa ACCmt. unfold id in ACC1, ACC2.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step. ubal_any. step. if_lit. step. step. step.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC1 (a + 8). st1. step. step. step. step. if_false.
    (* [comment removed for export] *)
    step. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACC2 (0x5e75e0 + 32). st1. step. if_false.
    (* [comment removed for export] *)
    do 2 step. zstep. ck8_check ACC1 (a + 16). step. step. do 2 step. if_false.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC1 (a + 24). st1. step. if_true.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC1 (a + 40). st1. rewrite sx32_lit by (clear; lia). step. if_false.
    (* [comment removed for export] *)
    ck8_check ACC1 (a + 8). st1. step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACC2 (0x5e75e0 + 32). st1.
    (* [comment removed for export] *)
    step. step. step. step. unfold P_bread_conv. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ADA1 : addressable mx a 128) by (eapply addressable_across2; [exact ADA| exact AAP| exact MU| exact WM| exact NSW0]);
      assert (ADC1 : addressable mx (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC| exact CAP| exact MU| exact WM| exact NSW0]);
      assert (ADE1 : addressable mx (bf_enc R) 92) by (eapply addressable_across2; [exact ADE| exact EAP| exact MU| exact WM| exact NSW0]) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RFS1 : as_RFS H LF mx) end.
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|]. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
      unhide AFS; unhide CFSB; unhide EFSB; unhide MFSB. pose proof RM3 as (_ & _ & _ & _ & _ & BMFS & _). unfold BUFMEM_SIZE in BMFS.
      clear - F1 F2 F3 F4 AFS CFSB EFSB MFSB BMFS AFW ARW CEIL LO96 SPR AH CH EH MH BMH ACEILB.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [ exact AFW | exact ARW | left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; split; lia ]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (HP1 : as_RHEAP H sA LB mx) end.
    { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
      repeat apply Forall_cons; try apply Forall_nil;
        first [ exact ACW | exact RCW | left; cbn [fst snd]; lia
              | right; right; left; cbn [fst snd]; first [ exists (bf_id R, a, 128); split; [exact I1| cbn; lia] | exists (bf_cid R, bf_ctx R, 2584); split; [exact I2| cbn; lia]
                                          | exists (bf_eid R, bf_enc R, 92); split; [exact I3| cbn; lia] | exists (mb_id M, mb, 128); split; [exact J1| cbn; lia]
                                          | exists (mb_bmid M, mb_bm M, 32); split; [exact J3| cbn; lia] ] ]. }
    eapply evt_cut.
    { eapply abreadconv_b64_spec with (lo := lo) (R := R) (LB := LB) (LF := LF) (sA := sA) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl) (rbp := rbp) (rbv := rbv);
        rewrite ?unsigned_lit by (clear - SPR LO96 LO0; lia); try reflexivity.
      all: lazymatch goal with
           | |- B64F_fresh _ _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| exact BX]|];
                                        exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact EIN|]; split; [exact EBR| exact DINV]
           | |- MEMBIO _ _ _ _ _ => membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- rw_cells _ _ _ [C8 _] => unfold wz; exact RBC
           | |- _ mod 8 = 0 => exact RBAL
           | |- memrd_out _ _ _ 8 _ _ => unfold memrd_out; unhide RBR; unhide RBB; unhide RBM; split; [clear - RBR; lia|]; split; [exact RBP|]; split; [exact RBH|]; split; [exact RBFM|]; split; [exact RBB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - RBM; lia
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; split; [clear - OUTR; lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - OUTM; lia
           | |- _ + 8 <= A_b64_method + _ \/ _ => exact RBMB
           | |- _ + _ <= A_b64_method + _ \/ _ => exact OUTMB
           | |- _ + 8 <= _ \/ _ => exact RBO
           | |- Forall _ _ => first [exact APO | exact APM | exact APT | exact RBF]
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact MT
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact MTM
           | |- B64F_shad _ _ _ => exact (conj ADA1 (conj ADC1 ADE1))
           | |- MEMBIO_shad _ _ _ => exact (MEMBIO_shad_across2 H LB _ m _ _ mb M MB MSH MU WM NSW0)
           | |- PAYLOAD_shad _ _ => split; [| split]; [eapply accessible_across2; [exact PACC| exact MU| exact NSW0]| eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| exact PAPP]
           | |- OUT_shad _ _ _ => pose proof OACC as (_ & OHI & _); split; [| split; [| split]]; [eapply accessible_across2; [exact OACC| exact MU| exact NSW0]| eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| lia| exact NSW0]| exact OAPP| exact OAOK]
           | |- RB_shad _ _ => split; [| split]; [eapply accessible_across2; [exact RACC| exact MU| exact NSW0]| exact RAPP| exact RAOK]
           | |- aapp _ _ => exact RAP
           | |- shvis _ _ _ => unfold B64CTX_SIZE; eapply shvis_across2; [exact CVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia| exact NSW0]
           | |- in_app_mem _ _ => exact CIA
           | |- ACONST _ => aconst_of AC MU WM
           | |- arelro_lib _ => eapply arelro_across7; [exact RL| exact MU|]; clear - AH CH EH MH BMH OTOP LO96 CEIL ACEILB RAP; unfold hidden, aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in RAP, OTOP;
                                repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia
           | |- as_RFS _ _ _ => exact RFS1
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- _ = Z_to_bv 64 ATP => exact TP
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- fsobj _ _ _ _ => first [exact RFO| exact FOO| exact FOP]
           | |- afs_write_ok _ _ _ => first [exact ARW| exact AFW]
           | |- aclient_write_ok _ _ _ => first [exact RCW| exact ACW]
           | |- AIMG_TOP <= _ => exact OTOP
           | |- stk _ _ _ _ => exact ST
           | |- aceil <= _ => exact CEIL
           | |- _ <= _ - ABREADCONV_B64_STACK => exact LOSr
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
          end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk' & XS
                    & -> & FX & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & [RBCp RBV] & ACp & RFSp & RLp & HPp).
    rewrite ?unsigned_lit in MUc by (clear - SPR LO96 LO0; lia). rewrite ?unsigned_lit in STc by (clear - SPR LO96 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    replace (ret_pc (Z_to_bv 64 2324752)) with (Z_to_bv 64 2324752) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    assert (APW : Forall appwin [(out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]).
    { unfold appwin. unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; unhide NSr. clear - OAPP NSa NSc NSe NSm NSbm NSr ACEILB. nsw_tac. }
    assert (FSa : fsobj H LF a 128) by (eapply (fsobj_block H HH); [exact HP| exact I1]).
    (* [comment removed for export] *)
    lazymatch type of MUc with munch ?Wc ?ma ?mb0 =>
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FR;
        [| apply disjoint_from_callee; [right; cbn; clear; lia
                                       | eapply disjoint_from_Forall; [exact FX|]; intros iv Hiv; pose proof (fs_scratch_below_ceil H HH _ _ _ RFS Hiv); cbn; clear - H0 CEIL LO96; lia
                                       | cbn; unhide OUTR; unhide RBR; clear - OUTR RBR BL1 BL2 BL3 ML1 ML3 SPR LO96; lia]]
    end.
    lazymatch type of MUc with munch _ ?ma ?mb0 =>
      assert (ACCa2 : id (accessible mb0 a 128)) by (unfold id; eapply (accessible_across3 H HH); [exact ACC1| exact RFS1| exact FSa| clear; lia| exact MUc| exact CEIL| exact FX| exact APW]);
      assert (RACC1 : accessible ma rbp 8) by (pose proof RACC0 as K; unfold hidden, id in K; eapply accessible_across2; [exact K| exact MU| exact NSW0]);
      assert (RACC2 : id (accessible mb0 rbp 8)) by (unfold id; eapply (accessible_across3 H HH); [exact RACC1| exact RFS1| exact RFO| clear; lia| exact MUc| exact CEIL| exact FX| exact APW]);
      assert (ADA2 : addressable mb0 a 128) by (eapply (addressable_across3 H HH); [exact ADA1| exact RFS1| exact FSa| clear - AP; lia| clear - AH ACE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW]);
      assert (ADC2 : addressable mb0 (bf_ctx R) 2584) by (eapply (addressable_across3 H HH); [exact ADC1| exact RFS1| eapply (fsobj_block H HH); [exact HP| exact I2]| clear - CP; lia| clear - CH CCE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW]);
      assert (ADE2 : addressable mb0 (bf_enc R) 92) by (eapply (addressable_across3 H HH); [exact ADE1| exact RFS1| eapply (fsobj_block H HH); [exact HP| exact I3]| clear - EP; lia| clear - EH ECE ACEILB; unfold AAPP_HI; lia| exact MUc| exact WMc| exact CEIL| exact FX| exact APW])
    end.
    clear ACC1 ACC2 RACC1 ADA1 ADC1 ADE1 RFS1 HP1.
    pose proof (munch_grow9 _ _ _ XS _ _ _ _ _ MU MUc ltac:(clear - SPR; lia) ltac:(clear; intros x Hx; exact Hx)) as MUX.
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMX. clear MU WM MUc WMc. hide MUX. hide WMX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)] m') as MU. pose proof (wmono_refl asegs m') as WM.
    clear ST MI. rename STc into ST. rename MIc into MI. clear BC BX EC MC MBB MBM MRP TXT OUTC MT MTM RBC.
    pose proof BCp as BCf. bio_unf BCp. unfold b64ctx_used_cells, wz in CTXp.
    destruct ENCp as (raw2 & line2 & RAWL2 & RAWP2 & ECp & LINE2 & _ & _ & DINV2).
    pose proof MBp as MBp0. destruct MBp0 as (MCp & MBBp & MBMp & MRPp & MBpure). clear MBp. bio_unf MCp. unfold buf_cells, wz in MBMp, MRPp. cbn [bm_len bm_data bm_max bm_flags] in MBMp, MRPp. unfold wz in MBBp.
    pose proof METHBp as METHB1. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB1. norm_addr METHB1.
    pose proof METHMp as METHM1. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM1. norm_addr METHM1.
    clear METHBp METHMp. unfold wz in RBCp. unfold zlength in ZLE.
    cbn [mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mb_flags mb_nread mset] in MCp, MBBp, MBMp, MRPp.
    unfold id in ACCa2, RACC2.
    (* [comment removed for export] *)
    assert (FIN : forall mf, munch [(lo, bv_unsigned sp); (rbp, rbp + 8); (a, a + 128)] m' mf -> wmono asegs m' mf ->
              ACONST mf /\ as_RFS H LF mf /\ arelro_lib mf /\ as_RHEAP H sA LB mf /\ munch ((lo, bv_unsigned sp) :: XS ++ [(out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]) m mf /\ wmono asegs m mf).
    { intros mf MUl WMl. split; [| split; [| split; [| split; [| split]]]].
      - aconst_of ACp MUl WMl.
      - eapply (ah_RFS_frame H HH); [exact RFSp| exact MUl| exact WMl|]. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
        unhide AFS. clear - F1 F2 F3 F4 AFS ARW CEIL LO96 SPR AH ACEILB.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; first [ exact ARW | left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; split; lia ].
      - eapply arelro_across7; [exact RLp| exact MUl|]. unhide RAP. clear - AH LO96 CEIL ACEILB RAP. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in RAP.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
      - eapply (ah_RHEAP_frame H HH); [exact HPp| exact MUl| exact WMl|].
        repeat apply Forall_cons; try apply Forall_nil; first [ exact RCW | left; cbn [fst snd]; lia | right; right; left; cbn [fst snd]; exists (bf_id R, a, 128); split; [exact I1| cbn; lia] ].
      - unhide MUX. eapply munch_absorb9; [exact MUX| exact MUl|]. clear. intros x Hx. cbn in Hx |- *. tauto.
      - unhide WMX. exact (wmono_trans _ _ _ _ WMX WMl). }
    (* [comment removed for export] *)
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm.
    pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp. clear APM1.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp.
    pose proof (Forall_inv APT) as PT1'. cbn [blk_addr blk_size fst snd] in PT1'. unfold BIO_SIZE in PT1'.
    assert (DK1 : chunk_disj (bf_ctx R) 2584 a 128) by (unhide BA1; clear - BA1; unfold chunk_disj; lia).
    assert (DK2 : chunk_disj (bf_enc R) 92 a 128) by (unhide BA2; clear - BA2; unfold chunk_disj; lia).
    assert (DK3 : chunk_disj mb 128 a 128) by (clear - DJ_a_mb; unfold chunk_disj; lia).
    assert (DK4 : chunk_disj (mb_bb M) 16 a 128) by (clear - DJ_a_bb; unfold chunk_disj; lia).
    assert (DK5 : chunk_disj (mb_bm M) 32 a 128) by (clear - DJ_a_bm; unfold chunk_disj; lia).
    assert (DK6 : chunk_disj (mb_rp M) 32 a 128) by (clear - DJ_a_rp; unfold chunk_disj; lia).
    assert (DK7 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) a 128) by (clear - PT1' TLEN; unfold chunk_disj; lia).
    assert (DK8 : chunk_disj rbp 8 a 128) by (unhide RA1; clear - RA1; unfold chunk_disj; lia).
    assert (DK9 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) a 128).
    { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide OA1. clear - OA1 ZLE OUTL. lia. }
    rename DJ_a_mb into DJ_a_mb0. rename DJ_a_bb into DJ_a_bb0. rename DJ_a_bm into DJ_a_bm0. rename DJ_a_rp into DJ_a_rp0. rename PT1' into PT10.
    hide DJ_a_mb0; hide DJ_a_bb0; hide DJ_a_bm0; hide DJ_a_rp0; hide PT10.
    (* [comment removed for export] *)
    step. step. step.
    destruct (Z.eq_dec (br_rv res) 0) as [RZ|RNZ].
    - (* [comment removed for export] *)
      rewrite RZ in *. change (ard_conv 0) with 0 in *. change (ard_rbv 0) with 0 in *. rewrite Z.add_0_r. specialize (CZ eq_refl).
      step. if_lit.
      (* [comment removed for export] *)
      step. if_lit. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
        step. unfold P_BIO_eof. step.
        pose proof abioeof_b64_spec as BES.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ADA3 : addressable mx a 128) by (eapply addressable_across2; [exact ADA2| unhide AAP; exact AAP| exact MU| exact WM| exact NSWl]);
          assert (ADC3 : addressable mx (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC2| unhide CAP; exact CAP| exact MU| exact WM| exact NSWl]);
          assert (ADE3 : addressable mx (bf_enc R) 92) by (eapply addressable_across2; [exact ADE2| unhide EAP; exact EAP| exact MU| exact WM| exact NSWl]) end.
        eapply evt_cut.
        { eapply BES with (lo := lo) (LB := LB) (a := a) (mb := mb) (R := bf_with_hdr R fl rt (bf_nread R) mb (bf_prev R)) (M := M)
                          (hdr := hdr) (junk := cjunk) (cont := c);
            cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by (clear - SPR LO96 LO0; lia); try reflexivity.
          all: lazymatch goal with
               | |- - 2^31 <= _ <= 0 => clear - CR CZ; lia
               | |- rw_cells _ _ _ (bio_cells _) => exact BCf
               | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTXp
               | |- B64F_blocks _ _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr];
                                            split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FLp|]; split; [exact RTp|]; split; [exact NRR|]; split; [clear - MP MH ACEILB MCE; lia| exact PVR]
               | |- B64F_below _ _ _ => exact BEL
               | |- length _ = _ => exact LH
               | |- map _ _ = _ => exact CONT
               | |- B64F_apart _ _ => exact BAP
               | |- B64F_shad _ _ _ => exact (conj ADA3 (conj ADC3 ADE3))
               | |- ACONST _ => aconst_of ACp MU WM
               | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1
               | |- stk _ _ _ _ => exact ST
               | |- aceil <= _ => exact CEIL
               | |- _ <= _ - (FR_BIO_eof + BIOCTRL_B64_STACK) => revert LOSr; unfold ABREADCONV_B64_STACK, FR_bread_conv, FR_BIO_eof; clear; intros; lia
               | |- mem_inv _ _ => assumption
               | |- _ mod 2 = 0 => reflexivity
               end. }
        cbv beta. clear BES. unfold BIO_SIZE.
        aland_open MU.
        carry1 MUc WMc FR. carry1 MUc WMc RBCp using RBR RA1. carry1 MUc WMc CTXp using BA1. carry1 MUc WMc ECp using BA2.
        unhide DJ_a_mb0; unhide DJ_a_bb0; unhide DJ_a_bm0; unhide DJ_a_rp0; unhide PT10.
        carry1 MUc WMc MCp. carry1 MUc WMc MBBp. carry1 MUc WMc MBMp. carry1 MUc WMc MRPp. carry1 MUc WMc TXTp.
        hide DJ_a_mb0; hide DJ_a_bb0; hide DJ_a_bm0; hide DJ_a_rp0; hide PT10.
        carry1k MUc WMc OUTp by (unhide OUTR; unhide OA1; clear - OUTp MUc WMc OUTR OA1 ZLE OUTL LO96 SPR).
        carry1 MUc WMc METHB1. carry1 MUc WMc METHM1.
        aland_close MU WM MUc WMc.
        match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC3 end. pose proof BC3 as BC3f. bio_unf BC3.
        (* [comment removed for export] *)
        zstep. step. step.
        change (Z.b2z (0 <? 1) + -1) with 0.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACCa3 : accessible mx a 128) by (eapply accessible_across2; [exact ACCa2| exact MU| exact NSWl]) end.
        ck8_check ACCa3 (a + 16). do 2 step. if_false. zstep. zstep. zstep. ck8_check ACCa3 (a + 24). st1. step. if_true.
        do 2 step. if_true. step. do 12 st1. step. step. release_frame FR ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
        apply evt_done. unfold b64rd_post.
        do 15 eexists. exists fl, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
        split; [reflexivity|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
        split; [assumption|]. split; [exact ST|].
        split; [exact BC3f|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros _; exact CZ|].
        split; [clear - OUTL; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [unfold wz; split; [exact RBCp| clear - OUTL; lia]|].
        exact (conj ACf (conj RFSf (conj RLf HPf))).
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (br_rv res) 0) as [NEG|NNEG].
      + assert (POS : br_rv res = -1). { revert RVR NEG. unfold ard_conv. destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; clear - E; intros; lia. }
        rewrite POS in *. change (ard_conv (-1)) with (-1) in *. change (ard_rbv (-1)) with 0 in *. rewrite Z.add_0_r.
        (* [comment removed for export] *)
        step. if_lit.
        step. if_lit.
        ck8_check ACCa2 (a + 16). do 2 step. if_false. zstep. zstep. zstep. ck8_check ACCa2 (a + 24). st1. step. if_true.
        do 2 step. if_true. step. do 12 st1. step. step. release_frame FR ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
        apply evt_done. unfold b64rd_post.
        do 15 eexists. exists fl, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
        split; [first [reflexivity | f_equal; f_equal; apply bv_eq; vm_compute; reflexivity]|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
        split; [assumption|]. split; [exact ST|].
        split; [exact BCf|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E POS; cbn in E; lia|].
        split; [clear - OUTL RVR POS; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [unfold wz; split; [exact RBCp| clear - OUTL RVR POS; lia]|].
        exact (conj ACf (conj RFSf (conj RLf HPf))).
      + assert (POS : 0 < br_rv res <= outl).
        { revert RVR NNEG RNZ RBV. unfold ard_conv, ard_rbv. destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; clear - E; intros; lia. }
        clear RNZ NNEG. unfold ard_conv, ard_rbv in *. replace (0 <? br_rv res) with true in * by (symmetry; apply Z.ltb_lt; clear - POS; lia). cbv iota in RBCp, RBV, RVR, CZ. cbv iota.
        clear BCf.
        (* [comment removed for export] *)
        step. if_false.
        step. ub_dead. step. ubal_by RBAL. if_lit. zstep. ck8_check RACC2 rbp. zstep. zstep. zstep. ck8_check ACCa2 (a + 96). st1. st1. zstep.
        change (Z_to_bv 64 (bf_nread R + br_rv res)) with (wz (bf_nread R + br_rv res)).
        st1. step.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACCa4 : accessible mx a 128) by (eapply accessible_across2; [exact ACCa2| exact MU| exact NSWl]);
          assert (RACC4 : accessible mx rbp 8) by (eapply accessible_across2; [exact RACC2| exact MU| exact NSWl]) end.
        ck8_check ACCa4 (a + 16). do 2 step. if_false. zstep. zstep. zstep. ck8_check ACCa4 (a + 24). st1. step. if_true.
        do 2 step. if_false. step. ub_dead. step. ub_dead. zstep. ck8_check RACC4 rbp. st1. step. if_cases K5; zify_cond K5; [clear K5| kill K5].
        step. do 12 st1. step. step. release_frame FR ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (FIN mf MU WM) as (ACf & RFSf & RLf & HPf & MUf & WMf) end.
        apply evt_done. unfold b64rd_post.
        do 15 eexists. exists fl, rt, c, fl', nr', d', hdr, cjunk, junk', XS.
        split; [reflexivity|]. split; [exact FX|]. split; [unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [app]; exact MUf|]. split; [exact WMf|].
        split; [assumption|]. split; [exact ST|].
        split; [bio_unf_goal; exact BCp|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E POS; cbn in E; lia|].
        split; [clear - OUTL RVR POS; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [unfold wz; split; [exact RBCp| clear - OUTL RVR POS; lia]|].
        exact (conj ACf (conj RFSf (conj RLf HPf))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma munch_reshape9 : forall (lohi wout : Z * Z) (S4 XSc Wr : list (Z * Z)) m0 m1,
    munch (lohi :: XSc ++ (S4 ++ (wout :: Wr))) m0 m1 -> munch (lohi :: wout :: (S4 ++ XSc) ++ Wr) m0 m1.
  Proof.
    intros [lo hi] wout S4 XSc Wr m0 m1 M. eapply munch_weaken; [| exact M]. intros x Hx. cbn in Hx |- *.
    destruct wout as [wl wh]. cbn in Hx. destruct Hx as [H1 [H2 H3]].
    apply (proj1 (outside_app _ _ _)) in H3. destruct H3 as [H34 H5]. apply (proj1 (outside_app _ _ _)) in H34. destruct H34 as [H3 H4].
    split; [exact H1|]. apply (proj2 (outside_app _ _ _)). split; [exact H4|]. apply (proj2 (outside_app _ _ _)). split; [exact H3|]. cbn. split; [exact H2| exact H5].
  Qed.

  Definition ABRD_SM : Z := 0x237620.    (* [comment removed for export] *)
  Definition ABRD_RI : Z := 0x2376c4.    (* [comment removed for export] *)
  Let HSM0 : stack_malloc_0_stmt H := proj1 (proj2 (proj2 HX)).

  (* [comment removed for export] *)
  Lemma abioread_b64_spec : bioread_b64_stmt H.
  Proof.
    unfold bioread_b64_stmt. intros until junk.
    intros A0 A1 A2 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT METHB METHM BSH MSH PAY OSH AC RL RFS LFB TP HP SPA FOO FOP AFW ACW OTOP ST CEIL LO MI RAE.
    subst a0 a1 a2.
    unfold P_BIO_read in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOS : lo <= bv_unsigned sp - 112 - 1024 /\ lo <= bv_unsigned sp - 112 - AREADINTERN_B64_STACK).
    { revert LO. unfold BIOREAD_B64_STACK, AREADINTERN_B64_STACK, ABREADCONV_B64_STACK, AFS_STACK, FR_BIO_read, FR_bio_read_intern, FR_bread_conv. clear. intros; lia. }
    destruct LOS as [LOSm LOSr].
    assert (LO112 : lo <= bv_unsigned sp - 112 - 96).
    { revert LOSr. unfold AREADINTERN_B64_STACK, ABREADCONV_B64_STACK, FR_bio_read_intern, FR_bread_conv, BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & ACE & AFSa & AAP). pose proof RB2 as (CP & _ & _ & CH & CCE & AFSc & CAP). pose proof RB3 as (EP & _ & _ & EH & ECE & AFSe & EAP).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MCE & AFSm & MAP). pose proof RM2 as (BBP & _ & _ & BBH & BBCE & AFSbb & BBAP).
    pose proof RM3 as (BMP & _ & _ & BMH & BMCE & AFSbm & BMAP). pose proof RM4 as (RPP & _ & _ & RPH & RPCE & AFSrp & RPAP).
    pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof (Forall_inv APT) as PT1. cbn [blk_addr blk_size fst snd] in PT1.
    pose proof MSEP as ((SP1 & SP2_ & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE, AIMG_TOP in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      ACE, CCE, ECE, MCE, BBCE, BMCE, RPCE, AAP, CAP, EAP, MAP, BBAP, BMAP, RPAP, AFSa, AFSc, AFSe, AFSm, AFSbb, AFSbm, AFSrp, I1, I2, I3, J1, J2, J3, J4,
      OF1, OF2, OF3, OF4, PT1, SP1, SP2_, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4, BBH, BMH, RPH.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. unfold A_b64_method, O_METH_BREAD in OUTMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    destruct BSH as (ADA & ADC & ADE). pose proof MSH as (ADM & ADBB & ADBM & ADRP). pose proof PAY as (PACC & PVIS & PAPP). pose proof OSH as (OACC & OVIS & OAPP & OAOK).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in ADA, ADC, ADM, ADBB, ADBM, ADRP.
    pose proof OACC as (_ & OHI & _). unfold AAPP_HI in OHI.
    unfold zlength in TLEN, TLE.
    (* [comment removed for export] *)
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (out, out + outl); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_not_shadowland _ _ EAP) as NSe.
    pose proof (aapp_not_shadowland _ _ MAP) as NSm. pose proof (aapp_not_shadowland _ _ BBAP) as NSbb. pose proof (aapp_not_shadowland _ _ BMAP) as NSbm. pose proof (aapp_not_shadowland _ _ RPAP) as NSrp.
    unfold ALOWSH_LO, AHI_LO in NSa, NSc, NSe, NSm, NSbb, NSbm, NSrp.
    (* [comment removed for export] *)
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof (ACONST_uar _ AC) as [GUA UAR]. unfold AGOT_UAR, AUAR_CELL, wz in GUA, UAR.
    assert (GFD : rw_cells asegs m 0x5e8630 [C8 (wz 0x2375b4)]).
    { apply relro_cell7; [exact RL| lia| cbn; lia| cbn; repeat split; try exact I; try lia| vm_compute; reflexivity]. }
    unfold wz in GFD.
    pose proof METHB as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in MT. norm_addr MT.
    pose proof METHM as MTM. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MTM. norm_addr MTM.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & EIN & EBR & DINV).
    unfold in_app_mem, AHI_LO, AAPP_HI in OAPP, PAPP. rewrite ASHADOW_BASE_val in OAPP, PAPP.
    hide_ors.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]).
    { unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; unhide OAPP. clear - HH CEIL ACEILB OAPP NSa NSc NSe NSm NSbm SPR. nsw_tac. }
    (* [comment removed for export] *)
    carve_frame 80%nat ST. carve_frame 16%nat ST.
    unhide OUTR. step. st1. do 10 step. step.
    (* [comment removed for export] *)
    zstep.
    rewrite land_m32 by lia.
    remember (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) as sp2 eqn:Hsp2.
    assert (SP2 : bv_unsigned sp - 112 <= sp2 <= bv_unsigned sp - 96 /\ sp2 mod 16 = 0).
    { subst sp2. split; [Z.div_mod_to_equations; lia|]. rewrite <- Zminus_mod_idemp_r. Z.div_mod_to_equations. lia. }
    clear Hsp2. destruct SP2 as [SP2 SP2A]. hide OUTR.
    release_frame FR0 ST (bv_unsigned sp + -80).
    destruct (stk_split asegs _ lo sp2 _ ST ltac:(lia)) as [STc STm]. clear ST.
    destruct (stk_split asegs _ sp2 (sp2 + 16) _ STm ltac:(lia)) as [ST2 ST3]. clear STm.
    carve_frame 16%nat ST2. clear ST2. rename STc into ST. rewrite ?Z.add_0_r in FR0.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. st1. rewrite sx32_lit by lia. step. step. step. if_false.
    (* [comment removed for export] *)
    step. step.
    assert (FWS : Forall (afs_write_ok H LF) [(lo, bv_unsigned sp)]).
    { constructor; [| constructor]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. split; lia. }
    assert (RFS1 : as_RFS H LF m0) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU0| exact WM| exact FWS]).
    assert (AC1 : ACONST m0) by (eapply ACONST_stack_frame7; [exact AC| exact MU0| exact WM| exact CEIL]).
    assert (HP1 : as_RHEAP H sA LB m0) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU0| exact WM| constructor; [left; cbn [fst snd]; lia| constructor]]).
    assert (THR1 : athr_cells m0) by (exact (ah_thr H HH _ _ _ HP1)).
    pose proof HSM0 as SM. unfold stack_malloc_0_stmt, stack_malloc_stmt, AFS_MALLOC_0, AFS_STACK in SM.
    eapply evt_cut.
    { eapply SM with (lo := lo) (LF := LF); clear SM; rewrite ?unsigned_lit by lia;
        [exact RFS1| clear - HH LFB; lia| exact ST| exact CEIL| lia| assumption| exact TP| exact AC1| exact THR1]. }
    clear SM. unfold stack_malloc_post.
    intros ms' PO. change (fsz 0) with 64 in PO. change (fshn 0) with 8 in PO. unfold AFS_STACK, AFS_FLAGS in PO.
    change (Z.to_nat (64 - 40)) with 24%nat in PO. change (Z.to_nat 8) with 8%nat in PO.
    rewrite ?unsigned_lit in PO by lia. revert ms' PO.
    aland_open MU.
    match goal with X : as_RFS H ((0, ?f, ?p) :: LF) ?mx |- _ => rename X into RFS2; rename f into ff; rename p into fp end.
    match goal with X : rw_cells asegs _ ff _ |- _ => rename X into FFR end.
    match goal with X : SHAD _ ff _ |- _ => rename X into SHD end.
    match goal with X : rw_cells asegs _ fp _ |- _ => rename X into FPC end.
    match goal with X : ACONST ?mx, Y : as_RFS H _ ?mx |- _ => rename X into AC2 end.
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 0) with 64 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof (SHAD_rw_cells _ _ _ SHD) as SHC. change (poison_bytes 8 0) with [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] in SHC. cbn [length] in SHC.
    assert (APff : aapp ff 64) by (clear - HH FB3 FF5 FF6; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (SHF : ASHADOW_BASE <= sh ff /\ sh ff + 8 < AHI_LO).
    { clear - HH APff FF1. pose proof (sh_aapp_range ff 64 APff ltac:(lia)) as (Q1 & Q2 & Q3).
      change (nsh 64) with 8 in Q2. split; [unfold sh; Z.div_mod_to_equations; lia| lia]. }
    unfold AHI_LO in SHF.
    rewrite <- (sh_shiftr ff) in SHC, SHF, MUc by lia. rewrite ASHADOW_BASE_val in SHC, SHF, MUc.
    pose proof (aapp_not_shadowland _ _ APff) as NSff. unfold ALOWSH_LO, AHI_LO in NSff.
    (* [comment removed for export] *)
    assert (FSa : fsobj H LF a 128) by (eapply (fsobj_block H HH); [exact HP| exact I1]).
    assert (FSc : fsobj H LF (bf_ctx R) 2584) by (eapply (fsobj_block H HH); [exact HP| exact I2]).
    assert (FSe : fsobj H LF (bf_enc R) 92) by (eapply (fsobj_block H HH); [exact HP| exact I3]).
    assert (FSm : fsobj H LF mb 128) by (eapply (fsobj_block H HH); [exact HP| exact J1]).
    assert (FSbb : fsobj H LF (mb_bb M) 16) by (eapply (fsobj_block H HH); [exact HP| exact J2]).
    assert (FSbm : fsobj H LF (mb_bm M) 32) by (eapply (fsobj_block H HH); [exact HP| exact J3]).
    assert (FSrp : fsobj H LF (mb_rp M) 32) by (eapply (fsobj_block H HH); [exact HP| exact J4]).
    pose proof (fsobj_windows H HH LF out outl 0 ff fp m0 RFS1 FOO FRESH ltac:(clear - HH OUTP; lia) ltac:(clear - HH OUTL; lia) ltac:(clear - HH OHI; unfold AAPP_HI; lia)) as (OW1 & OW2 & OW3 & OW4).
    pose proof (fsobj_windows H HH LF (mb_buf M) (mb_len M) 0 ff fp m0 RFS1 FOP FRESH ltac:(clear - HH BUFP; lia) ltac:(clear - HH LENR; lia) ltac:(clear - HH BUFH ACEILB; unfold AAPP_HI; lia)) as (PW1 & PW2 & PW3 & PW4).
    pose proof (fsobj_windows H HH LF a 128 0 ff fp m0 RFS1 FSa FRESH ltac:(clear - HH AP; lia) ltac:(clear; lia) ltac:(clear - HH ACE ACEILB; unfold AAPP_HI; lia)) as (AW1 & AW2 & AW3 & AW4).
    pose proof (fsobj_windows H HH LF (bf_ctx R) 2584 0 ff fp m0 RFS1 FSc FRESH ltac:(clear - HH CP; lia) ltac:(clear; lia) ltac:(clear - HH CCE ACEILB; unfold AAPP_HI; lia)) as (CW1 & CW2 & CW3 & CW4).
    pose proof (fsobj_windows H HH LF (bf_enc R) 92 0 ff fp m0 RFS1 FSe FRESH ltac:(clear - HH EP; lia) ltac:(clear; lia) ltac:(clear - HH ECE ACEILB; unfold AAPP_HI; lia)) as (EW1 & EW2 & EW3 & EW4).
    pose proof (fsobj_windows H HH LF mb 128 0 ff fp m0 RFS1 FSm FRESH ltac:(clear - HH MP; lia) ltac:(clear; lia) ltac:(clear - HH MCE ACEILB; unfold AAPP_HI; lia)) as (MW1 & MW2 & MW3 & MW4).
    pose proof (fsobj_windows H HH LF (mb_bb M) 16 0 ff fp m0 RFS1 FSbb FRESH ltac:(clear - HH BBP; lia) ltac:(clear; lia) ltac:(clear - HH BBCE ACEILB; unfold AAPP_HI; lia)) as (BBW1 & BBW2 & BBW3 & BBW4).
    pose proof (fsobj_windows H HH LF (mb_bm M) 32 0 ff fp m0 RFS1 FSbm FRESH ltac:(clear - HH BMP; lia) ltac:(clear; lia) ltac:(clear - HH BMCE ACEILB; unfold AAPP_HI; lia)) as (BMW1 & BMW2 & BMW3 & BMW4).
    pose proof (fsobj_windows H HH LF (mb_rp M) 32 0 ff fp m0 RFS1 FSrp FRESH ltac:(clear - HH RPP; lia) ltac:(clear; lia) ltac:(clear - HH RPCE ACEILB; unfold AAPP_HI; lia)) as (RPW1 & RPW2 & RPW3 & RPW4).
    change (fsz 0) with 64 in OW1, PW1, AW1, CW1, EW1, MW1, BBW1, BMW1, RPW1. change (fshn 0) with 8 in OW2, PW2, AW2, CW2, EW2, MW2, BBW2, BMW2, RPW2.
    unfold AFS_FLAGS in OW4, PW4, AW4, CW4, EW4, MW4, BBW4, BMW4, RPW4.
    rewrite <- (sh_shiftr ff) in OW2, PW2, AW2, CW2, EW2, MW2, BBW2, BMW2, RPW2 by lia. rewrite ASHADOW_BASE_val in OW2, PW2, AW2, CW2, EW2, MW2, BBW2, BMW2, RPW2.
    hide OW1; hide OW2; hide OW3; hide OW4; hide PW1; hide PW2; hide PW3; hide PW4.
    hide AW1; hide AW2; hide AW3; hide AW4; hide CW1; hide CW2; hide CW3; hide CW4; hide EW1; hide EW2; hide EW3; hide EW4.
    hide MW1; hide MW2; hide MW3; hide MW4; hide BBW1; hide BBW2; hide BBW3; hide BBW4; hide BMW1; hide BMW2; hide BMW3; hide BMW4; hide RPW1; hide RPW2; hide RPW3; hide RPW4.
    (* [comment removed for export] *)
    carry1k MUc WMc FR by (clear - HH FR MUc WMc SP2 LOSm CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc FR0 by (clear - HH FR0 MUc WMc SP2 LOSm CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc ST3 by (clear - HH ST3 MUc WMc SP2 LOSm CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc BC by (clear - HH BC MUc WMc SP2 LOSm BL1 AW1 AW3 AW4 NSa SHF; unhide AW1; unhide AW3; unhide AW4; unhide NSa).
    carry1k MUc WMc BX by (clear - HH BX MUc WMc SP2 LOSm BL2 CW1 CW3 CW4 NSc SHF; unhide CW1; unhide CW3; unhide CW4; unhide NSc).
    carry1k MUc WMc EC by (clear - HH EC MUc WMc SP2 LOSm BL3 EW1 EW3 EW4 NSe SHF; unhide EW1; unhide EW3; unhide EW4; unhide NSe).
    carry1k MUc WMc MC by (clear - HH MC MUc WMc SP2 LOSm ML1 MW1 MW3 MW4 NSm SHF; unhide MW1; unhide MW3; unhide MW4; unhide NSm).
    carry1k MUc WMc MBB by (clear - HH MBB MUc WMc SP2 LOSm ML2 BBW1 BBW3 BBW4 NSbb SHF; unhide BBW1; unhide BBW3; unhide BBW4; unhide NSbb).
    carry1k MUc WMc MBM by (clear - HH MBM MUc WMc SP2 LOSm ML3 BMW1 BMW3 BMW4 NSbm SHF; unhide BMW1; unhide BMW3; unhide BMW4; unhide NSbm).
    carry1k MUc WMc MRP by (clear - HH MRP MUc WMc SP2 LOSm ML4 RPW1 RPW3 RPW4 NSrp SHF; unhide RPW1; unhide RPW3; unhide RPW4; unhide NSrp).
    carry1k MUc WMc OUTC by (clear - HH OUTC MUc WMc SP2 LOSm OUTR OW1 OW3 OW4 OAPP SHF OUTL; unhide OUTR; unhide OW1; unhide OW3; unhide OW4; unhide OAPP).
    carry1k MUc WMc TXT by (clear - HH TXT MUc WMc SP2 LOSm CEIL BUFH TLEN LENR PW1 PW3 PW4 PAPP SHF; unhide PW1; unhide PW3; unhide PW4; unhide PAPP).
    carry1k MUc WMc MT by (clear - HH MT MUc WMc SP2 LOSm CEIL ACEILB FB1 FP1 FF1 SHF).
    carry1k MUc WMc MTM by (clear - HH MTM MUc WMc SP2 LOSm CEIL ACEILB FB1 FP1 FF1 SHF).
    carry1k MUc WMc GFD by (clear - HH GFD MUc WMc SP2 LOSm CEIL ACEILB FB1 FP1 FF1 SHF).
    lazymatch type of MUc with munch _ _ ?mx =>
      assert (HPm : as_RHEAP H sA LB mx)
        by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MUc| exact WMc|]; clear - HH CEIL FB1 FB2 FB3 FF5 FF6 FP3 FP4 FF1 SHF ACEILB SP2 LOSm;
            repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE;
            first [ left; lia
                  | do 4 right; left; lia
                  | do 5 right; left; unfold sh; rewrite ASHADOW_BASE_val, ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia
                 ])
    end.
    hide NSff.
    (* [comment removed for export] *)
    lazymatch type of MUc with munch [_; ?w1; ?w2; ?w3; ?w4] _ _ =>
      let T := fresh "MUw" in
      assert (T : munch ((lo, bv_unsigned sp) :: [w1; w2; w3; w4] ++ [(out, out + outl); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)]) m m0)
        by (eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside app] in Hx |- *; tauto);
      clear MU; rename T into MU; cbn [app] in MU
    end.
    aland_close MU WM MUc WMc. unfold ABRD_SM || idtac.
    rename ST into ST3. match goal with X : stk _ _ lo sp2 |- _ => rename X into ST end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(lo, bv_unsigned sp); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)] mx) as MU3;
      pose proof (wmono_refl asegs mx) as WM3
    end.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    unhide OUTR. st1. hide OUTR.
    (* [comment removed for export] *)
    step. step. zstep. zstep. step. zstep. st1. step.
    (* [comment removed for export] *)
    assert (DJf1 : chunk_disj a 128 ff 64) by (clear - HH AW1; unhide AW1; unfold chunk_disj; lia).
    assert (DJf2 : chunk_disj (bf_ctx R) 2584 ff 64) by (clear - HH CW1; unhide CW1; unfold chunk_disj; lia).
    assert (DJf3 : chunk_disj (bf_enc R) 92 ff 64) by (clear - HH EW1; unhide EW1; unfold chunk_disj; lia).
    assert (DJf4 : chunk_disj mb 128 ff 64) by (clear - HH MW1; unhide MW1; unfold chunk_disj; lia).
    assert (DJf5 : chunk_disj (mb_bb M) 16 ff 64) by (clear - HH BBW1; unhide BBW1; unfold chunk_disj; lia).
    assert (DJf6 : chunk_disj (mb_bm M) 32 ff 64) by (clear - HH BMW1; unhide BMW1; unfold chunk_disj; lia).
    assert (DJf7 : chunk_disj (mb_rp M) 32 ff 64) by (clear - HH RPW1; unhide RPW1; unfold chunk_disj; lia).
    assert (DJf8 : chunk_disj out (Z.of_nat (cells_size [CB (Z.to_nat outl) junk])) ff 64) by (clear - HH OW1 OUTL; unhide OW1; unfold chunk_disj; cbn [cells_size csize]; lia).
    assert (DJf9 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) ff 64) by (clear - HH PW1 TLEN; unhide PW1; unfold chunk_disj; lia).
    assert (DJf10 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 64) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJs1 : chunk_disj a 128 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSa SHF; unhide NSa; unfold chunk_disj; lia).
    assert (DJs2 : chunk_disj (bf_ctx R) 2584 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSc SHF; unhide NSc; unfold chunk_disj; lia).
    assert (DJs3 : chunk_disj (bf_enc R) 92 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSe SHF; unhide NSe; unfold chunk_disj; lia).
    assert (DJs4 : chunk_disj mb 128 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSm SHF; unhide NSm; unfold chunk_disj; lia).
    assert (DJs5 : chunk_disj (mb_bb M) 16 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSbb SHF; unhide NSbb; unfold chunk_disj; lia).
    assert (DJs6 : chunk_disj (mb_bm M) 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSbm SHF; unhide NSbm; unfold chunk_disj; lia).
    assert (DJs7 : chunk_disj (mb_rp M) 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSrp SHF; unhide NSrp; unfold chunk_disj; lia).
    assert (DJs8 : chunk_disj out (Z.of_nat (cells_size [CB (Z.to_nat outl) junk])) (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH OAPP SHF OUTL; unhide OAPP; unfold chunk_disj; cbn [cells_size csize]; lia).
    assert (DJs9 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH PAPP SHF TLEN LENR; unhide PAPP; unfold chunk_disj; lia).
    assert (DJs10 : chunk_disj ff 64 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (APfp : aapp fp 1) by (clear - HH FB3 FP3 FP4; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (DJs11 : chunk_disj fp 1 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH APfp SHF; pose proof (aapp_not_shadowland _ _ APfp) as X; unfold ALOWSH_LO, AHI_LO in X; unfold chunk_disj; lia).
    (* [comment removed for export] *)
    st1. st1. st1.
    (* [comment removed for export] *)
    apply (arw_cells_recut _ _ _ [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)]) in SHC; [| cbn; repeat split; exact I| reflexivity].
    step. st1. st1. st1. st1. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    zstep. step. step. step. step. unfold P_bio_read_intern. step.
    (* [comment removed for export] *)
    lazymatch type of FFR with rw_cells _ _ ff (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: nil) with ([c0; c1; c2; c3] ++ ([c4] ++ [c5])) in FFR end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFR. destruct FFR as [FFA FFB]. cbn [cells_size csize Nat.add] in FFB.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFB. destruct FFB as [FFB FFC]. cbn [cells_size csize Nat.add] in FFC.
    pose proof (rw_cells_CB_split _ _ _ _ 8 _ FFB ltac:(lia)) as [RBC FFB']. clear FFB. cbn [Nat.sub] in FFB'.
    apply (rw_cells_CB8_C8 asegs _ _ [] _ []) in RBC. cbn [app] in RBC. unfold wz in RBC.
    replace (ff + Z.of_nat 32 + Z.of_nat 8) with (ff + 40) in FFB' by lia. replace (ff + Z.of_nat 32 + Z.of_nat 24) with (ff + 56) in FFC by lia.
    replace (ff + Z.of_nat 32) with (ff + 32) in RBC by lia.
    lazymatch type of SHC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in SHC end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in SHC. destruct SHC as [SHA SHB4]. cbn [cells_size csize Nat.add] in SHB4.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in SHB4. destruct SHB4 as [SHB4 SHCr]. cbn [cells_size csize Nat.add] in SHCr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RACC : accessible mx (ff + 32) 8)
        by (apply acc8_of_C1_7; [unfold sh; rewrite ASHADOW_BASE_val; replace (2147450880 + (ff + 32) / 8) with (Z.shiftr ff 3 + 2147450880 + 4)
                                    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia); exact SHB4
                               | lia| Z.div_mod_to_equations; lia| unfold AAPP_HI; lia]) end.
    (* [comment removed for export] *)
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (fs_scratch_of_fresh H _ _ _ _ FRESH))))) as SC4.
    change (fshn 0) with 8 in SC4.
    assert (FOO' : fsobj H LF out outl) by exact FOO. assert (FOP' : fsobj H LF (mb_buf M) (mb_len M)) by exact FOP.
    pose proof (fsobj_scratch_hull H HH _ _ _ _ _ RFS1 FOO' ltac:(clear - HH OUTP; lia) ltac:(clear - HH OUTL; lia) ltac:(clear - HH OHI; unfold AAPP_HI; lia) SC4) as OWH.
    pose proof (fsobj_scratch_hull H HH _ _ _ _ _ RFS1 FOP' ltac:(clear - HH BUFP; lia) ltac:(clear - HH LENR; lia) ltac:(clear - HH BUFH ACEILB; unfold AAPP_HI; lia) SC4) as PWH.
    cbn [fst snd] in OWH, PWH. rewrite <- (sh_shiftr ff) in OWH, PWH by lia. rewrite ASHADOW_BASE_val in OWH, PWH. hide OWH; hide PWH.
    (* [comment removed for export] *)
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (fs_scratch_of_fresh H _ _ _ _ FRESH))))) as SC4'. change (fshn 0) with 8 in SC4'.
    pose proof (fsobj_scratch_hull H HH _ _ _ _ _ RFS1 FSc ltac:(clear - HH CP; lia) ltac:(clear; lia) ltac:(clear - HH CCE ACEILB; unfold AAPP_HI; lia) SC4') as CWH.
    cbn [fst snd] in CWH. rewrite <- (sh_shiftr ff) in CWH by lia. rewrite ASHADOW_BASE_val in CWH. hide CWH. clear SC4 SC4'.
    pose proof (aapp_not_shadowland _ _ FB3) as NSfs. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in NSfs. hide NSfs.
    (* [comment removed for export] *)
    Local Ltac win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm t5 :=
      repeat apply Forall_cons; try apply Forall_nil; unfold winX, winH; cbn [fst snd]; unfold AHI_LO; rewrite ?ASHADOW_BASE_val;
      [> lia | unhide NSfs; lia | unhide NSfs; lia | unhide NSff; lia | t5 | unhide OAPP; lia | unhide NSa; lia | unhide NSc; lia | unhide NSe; lia | unhide NSm; lia | unhide NSbm; lia ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (SHX : B64F_shad mx a R) end.
    { clear - HH ADA ADC ADE MU WM AP CP EP ACE CCE ECE ACEILB CEIL LO112 NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF AW2 CW2 EW2 OAPP NSa NSc NSe NSm NSbm.
      unfold B64F_shad, BIO_SIZE, B64CTX_SIZE. split; [| split].
      - eapply addressable_acrossX; [exact ADA| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide AW2; lia).
      - eapply addressable_acrossX; [exact ADC| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide CW2; lia).
      - eapply addressable_acrossX; [exact ADE| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide EW2; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (MSHX : MEMBIO_shad mx mb M) end.
    { clear - HH ADM ADBB ADBM ADRP MU WM MP BBP BMP RPP MCE BBCE BMCE RPCE ACEILB CEIL LO112 NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF MW2 BBW2 BMW2 RPW2 OAPP NSa NSc NSe NSm NSbb NSbm NSrp.
      unfold MEMBIO_shad, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. split; [| split; [| split]].
      - eapply addressable_acrossX; [exact ADM| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide MW2; lia).
      - eapply addressable_acrossX; [exact ADBB| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide BBW2; lia).
      - eapply addressable_acrossX; [exact ADBM| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide BMW2; lia).
      - eapply addressable_acrossX; [exact ADRP| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide RPW2; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (PAYX : PAYLOAD_shad mx M) end.
    { clear - HH PACC PVIS PAPP MU WM BUFP BUFH LENR ACEILB CEIL LO112 NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF PWH OAPP NSa NSc NSe NSm NSbm.
      split; [| split; [| unhide PAPP; unfold in_app_mem, AHI_LO, AAPP_HI; rewrite ASHADOW_BASE_val; exact PAPP]].
      - eapply accessible_acrossX; [exact PACC| exact MU| lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide PWH; lia).
      - eapply shvis_acrossX; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide PWH; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (OUTX : OUT_shad mx out outl) end.
    { clear - HH OACC OVIS OAPP OAOK OHI MU WM OUTP OUTL ACEILB CEIL LO112 NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF OWH NSa NSc NSe NSm NSbm.
      split; [| split; [| split; [unhide OAPP; unfold in_app_mem, AHI_LO, AAPP_HI; rewrite ASHADOW_BASE_val; exact OAPP| exact OAOK]]].
      - eapply accessible_acrossX; [exact OACC| exact MU| lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide OWH; lia).
      - eapply shvis_acrossX; [exact OVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide OWH; lia). }
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ HP I2) as CVIS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (CVX : shvis mx (bf_ctx R) (bf_ctx R + 2584)) end.
    { clear - HH CVIS MU WM CP CCE ACEILB CEIL LO112 NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF CWH OAPP NSa NSc NSe NSm NSbm.
      eapply shvis_acrossX; [exact CVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win11 NSfs NSff OAPP NSa NSc NSe NSm NSbm ltac:(unhide CWH; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RSHX : RB_shad mx (ff + 32)) end.
    { split; [exact RACC| split]; [eapply aapp_in_app_mem; [exact APff| lia| lia]| eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia]]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (ACX : ACONST mx) end.
    { clear - HH AC2 MU3 WM3 APff ACEILB CEIL LO112 FF1 FF5 FB1 SHF HCEIL.
      eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912;
          rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RFSX : as_RFS H ((0, ff, fp) :: LF) mx) end.
    { clear - HH RFS2 MU3 WM3 ACEILB CEIL LO112 FF1 FF5 FF6 FB1 FB2 FB3 SHF NSfs HCEIL.
      eapply (ah_RFS_frame H HH); [exact RFS2| exact MU3| exact WM3|]. unhide NSfs.
      repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE.
      - left. split; lia.
      - right. exists (0, ff, fp). split; [left; reflexivity| cbn; change (fsz 0) with 64; lia].
      - left. split; lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RLX : arelro_lib mx) end.
    { clear - HH RL MU FF1 FB1 FP1 SHF AH CH EH MH BMH OTOP CEIL LO112 ACEILB. unfold AIMG_TOP in OTOP. eapply arelro_across7; [exact RL| exact MU|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (HPX : as_RHEAP H sA LB mx) end.
    { clear - HH HPm MU3 WM3 CEIL FB1 FB2 FF5 FF6 FF1 SHF ACEILB.
      eapply (ah_RHEAP_frame H HH); [exact HPm| exact MU3| exact WM3|].
      repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE;
        first [ left; lia | do 4 right; left; lia
              | do 5 right; left; unfold sh; rewrite ASHADOW_BASE_val, ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia ]. }
    clear MU3 WM3.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply areadintern_b64_spec with (lo := lo) (R := R) (LB := LB) (LF := (0, ff, fp) :: LF) (sA := sA) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl) (rbp := ff + 32);
        rewrite ?unsigned_lit by (clear - HH SPR SP2 LO112 LO0 FF1 FF2; lia); try reflexivity.
      all: lazymatch goal with
           | |- B64F_fresh _ _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| exact BX]|];
                                        exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact EIN|]; split; [exact EBR| exact DINV]
           | |- MEMBIO _ _ _ _ _ => membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- rw_cells _ _ _ [C8 _] => unfold wz; exact RBC
           | |- _ mod 8 = 0 => first [clear - FF64; lia | clear - FF8; lia]
           | |- memrd_out _ _ _ 8 _ _ => unfold memrd_out; unhide MW1; unhide BBW1; unhide BMW1; unhide RPW1; unhide PW1;
                                        clear - HH MW1 BBW1 BMW1 RPW1 PW1 FF1 FF5 FB1 FF6 FB2 CEIL ACEILB;
                                        split; [lia|]; split; [lia|]; split; [lia|]; split; [| split; [lia| unfold A_mem_buf_method, O_METH_BREAD; lia]];
                                        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]); apply Forall_nil
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; clear - HH OUTR OUTB OF1 OF2 OF3 OF4 OUTM OUTP OUTH SP2 OUTF;
                                        split; [lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; lia
           | |- _ + 8 <= A_b64_method + _ \/ _ => unfold A_b64_method, O_METH_BREAD; clear - HH FF1 FB1; lia
           | |- _ + _ <= A_b64_method + _ \/ _ => exact OUTMB
           | |- Forall _ (blocks_B64F _ _) => first [ exact APO | exact APT | exact APM
                                               | unhide AW1; unhide CW1; unhide EW1; clear - HH AW1 CW1 EW1; unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE;
                                                 repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]); apply Forall_nil ]
           | |- Forall _ _ => first [exact APO | exact APM | exact APT]
           | |- _ + 8 <= _ \/ _ => unhide OW1; clear - HH OW1; lia
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact MT
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact MTM
           | |- B64F_shad _ _ _ => exact SHX
           | |- MEMBIO_shad _ _ _ => exact MSHX
           | |- PAYLOAD_shad _ _ => exact PAYX
           | |- OUT_shad _ _ _ => exact OUTX
           | |- RB_shad _ _ => exact RSHX
           | |- aapp _ 8 => clear - HH APff; eapply aapp_sub; [exact APff| lia| lia]
           | |- shvis _ _ _ => unfold B64CTX_SIZE; exact CVX
           | |- in_app_mem _ _ => unfold B64CTX_SIZE; eapply aapp_in_app_mem; [exact CAP| lia| lia]
           | |- ACONST _ => exact ACX
           | |- arelro_lib _ => exact RLX
           | |- as_RFS _ _ _ => exact RFSX
           | |- (_ < AFS_MAXLIVE)%nat => cbn [length]; clear - HH LFB; lia
           | |- _ = Z_to_bv 64 ATP => exact TP
           | |- as_RHEAP _ _ _ _ => exact HPX
           | |- _ mod 16 = 0 => exact SP2A
           | |- fsobj _ _ _ 8 => eapply fsobj_inframe; [left; reflexivity| cbn; lia| cbn; change (fsz 0) with 64; lia]
           | |- fsobj _ _ _ _ => first [apply fsobj_mono; exact FOO| apply fsobj_mono; exact FOP]
           | |- afs_write_ok _ _ (_, _ + 8) => right; exists (0, ff, fp); split; [left; reflexivity| cbn; change (fsz 0) with 64; lia]
           | |- afs_write_ok _ _ _ => clear - HH AFW; destruct AFW as [A|(f & IN & B)]; [left; exact A| right; exists f; split; [right; exact IN| exact B]]
           | |- aclient_write_ok _ _ (_, _ + 8) => unfold aclient_write_ok; cbn [fst snd]; do 4 right; left; unfold AFS_SIZE; clear - HH FF5 FF6; lia
           | |- aclient_write_ok _ _ _ => exact ACW
           | |- AIMG_TOP <= _ => exact OTOP
           | |- stk _ _ _ _ => exact ST
           | |- aceil <= _ => exact CEIL
           | |- _ <= _ - AREADINTERN_B64_STACK => clear - HH LOSr SP2; lia
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
           end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk' & XSc
                    & -> & FXc & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & [RBCp RBV] & ACp & RFSp & RLp & HPp).
    rewrite ?unsigned_lit in MUc by (clear - HH SPR SP2 LO112 LO0; lia). rewrite ?unsigned_lit in STc by (clear - HH SPR SP2 LO112 LO0; lia).
    remember (b64_read_spec (map bv_unsigned txt) outl) as res eqn:Eres.
    replace (ret_pc (Z_to_bv 64 2324164)) with (Z_to_bv 64 2324164) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    (* [comment removed for export] *)
    Local Ltac xs_stack FXc RFSX := eapply disjoint_from_Forall; [exact FXc|]; intros iv Hiv; pose proof (fs_scratch_below_ceil H HH _ _ _ RFSX Hiv); cbn; lia.
    Local Ltac xs_live ffv k FXc RFSX :=
      eapply disjoint_from_Forall; [exact FXc|]; intros iv Hiv;
      pose proof (scratch_off_live H HH _ _ _ _ _ _ RFSX (or_introl eq_refl) Hiv) as (KL1 & KL2 & KL3);
      change (fsz 0) with 64 in KL1; change (fshn 0) with 8 in KL2; rewrite <- (sh_shiftr ffv) in KL2 by lia; rewrite ASHADOW_BASE_val in KL2; cbn; k KL1 KL2 KL3.
    lazymatch type of MUc with munch ?Wc ?ma ?mb0 =>
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FR;
        [| apply disjoint_from_callee; [right; cbn; clear - HH SP2; lia| clear - HH FXc RFSX CEIL LO112 SP2 SPR; xs_stack FXc RFSX
                                       | cbn; unhide OUTR; clear - HH OUTR BL1 BL2 BL3 ML1 ML3 SPR LO112 SP2 FB2 FF6 CEIL; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FR0;
        [| apply disjoint_from_callee; [right; cbn; clear - HH SP2; lia| clear - HH FXc RFSX CEIL LO112 SP2 SPR; xs_stack FXc RFSX
                                       | cbn; unhide OUTR; clear - HH OUTR BL1 BL2 BL3 ML1 ML3 SPR LO112 SP2 FB2 FF6 CEIL; lia]];
      apply (fun HH0 => @stk_transport_disjoint asegs Wc ma mb0 _ _ HH0 MUc WMc) in ST3;
        [| apply disjoint_from_callee; [right; cbn; clear - HH SP2; lia| clear - HH FXc RFSX CEIL LO112 SP2 SPR; xs_stack FXc RFSX
                                       | cbn; unhide OUTR; clear - HH OUTR BL1 BL2 BL3 ML1 ML3 SPR LO112 SP2 FB2 FF6 CEIL; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FFA;
        [| apply disjoint_from_callee; [left; cbn; clear - HH FB2 FF6 CEIL; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K1; lia) FXc RFSX
                                       | cbn; unhide OW1; unhide AW1; unhide CW1; unhide EW1; unhide MW1; unhide BMW1; clear - HH OW1 AW1 CW1 EW1 MW1 BMW1; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FFB';
        [| apply disjoint_from_callee; [left; cbn; clear - HH FB2 FF6 CEIL; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K1; lia) FXc RFSX
                                       | cbn; unhide OW1; unhide AW1; unhide CW1; unhide EW1; unhide MW1; unhide BMW1; clear - HH OW1 AW1 CW1 EW1 MW1 BMW1; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FFC;
        [| apply disjoint_from_callee; [left; cbn; clear - HH FB2 FF6 CEIL; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K1; lia) FXc RFSX
                                       | cbn; unhide OW1; unhide AW1; unhide CW1; unhide EW1; unhide MW1; unhide BMW1; clear - HH OW1 AW1 CW1 EW1 MW1 BMW1; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in SHA;
        [| apply disjoint_from_callee; [left; cbn; clear - HH SHF CEIL ACEILB; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL SHF; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K2; lia) FXc RFSX
                                       | cbn; unhide OAPP; unhide NSff; unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; clear - HH SHF OAPP NSff NSa NSc NSe NSm NSbm; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in SHB4;
        [| apply disjoint_from_callee; [left; cbn; clear - HH SHF CEIL ACEILB; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL SHF; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K2; lia) FXc RFSX
                                       | cbn; unhide OAPP; unhide NSff; unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; clear - HH SHF OAPP NSff NSa NSc NSe NSm NSbm; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in SHCr;
        [| apply disjoint_from_callee; [left; cbn; clear - HH SHF CEIL ACEILB; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL SHF; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K2; lia) FXc RFSX
                                       | cbn; unhide OAPP; unhide NSff; unhide NSa; unhide NSc; unhide NSe; unhide NSm; unhide NSbm; clear - HH SHF OAPP NSff NSa NSc NSe NSm NSbm; lia]];
      apply (fun HH0 => @rw_cells_transport asegs Wc ma mb0 _ _ HH0 MUc WMc) in FPC;
        [| apply disjoint_from_callee; [left; cbn; clear - HH FB2 FP4 CEIL; lia| clear - HH FXc RFSX FF1 FF6 FB1 FB2 CEIL; xs_live ff ltac:(fun K1 K2 K3 => clear - HH K3; lia) FXc RFSX
                                       | cbn; unhide OW3; unhide AW3; unhide CW3; unhide EW3; unhide MW3; unhide BMW3; clear - HH OW3 AW3 CW3 EW3 MW3 BMW3 FP2 FF1; lia]]
    end.
    (* [comment removed for export] *)
    pose proof (munch_grow9 _ _ _ XSc _ _ _ _ _ MU MUc ltac:(clear - HH SP2; lia)
                  ltac:(clear; intros x Hx; cbn in Hx |- *; repeat match goal with |- _ /\ _ => split end; try tauto; lia)) as MUX.
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMX. clear MU WM MUc WMc. hide MUX. hide WMX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8); (ff, ff + 64); (fp, fp + 1)] m') as MU. pose proof (wmono_refl asegs m') as WM.
    clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    clear BC BX EC MC MBB MBM MRP TXT OUTC MT MTM RBC SHX MSHX PAYX OUTX CVX RSHX ACX RLX HPX.
    bio_unf BCp. unfold b64ctx_used_cells, wz in CTXp.
    destruct ENCp as (raw2 & line2 & RAWL2 & RAWP2 & ECp & LINE2 & _ & _ & DINV2).
    pose proof MBp as MBp0. destruct MBp0 as (MCp & MBBp & MBMp & MRPp & MBpure). clear MBp. bio_unf MCp. unfold buf_cells, wz in MBMp, MRPp. cbn [bm_len bm_data bm_max bm_flags] in MBMp, MRPp. unfold wz in MBBp.
    pose proof METHBp as METHB1. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB1. norm_addr METHB1.
    pose proof METHMp as METHM1. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM1. norm_addr METHM1.
    clear METHBp METHMp. unfold wz in RBCp. unfold zlength in ZLE.
    cbn [mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mb_flags mb_nread mset] in MCp, MBBp, MBMp, MRPp.
    assert (RVB : -1 <= br_rv res <= outl /\ ard_rbv (br_rv res) = Z.max 0 (br_rv res) /\ (ard_conv (br_rv res) <= 0 <-> br_rv res <= 0)).
    { revert RVR RBV. clear. unfold ard_conv, ard_rbv. destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; intros; lia. }
    destruct RVB as (RVB & RBE & RCE).
    (* [comment removed for export] *)
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { destruct (Z.le_gt_cases (br_rv res) 0) as [LE|GT].
      2: { replace (ard_conv (br_rv res)) with 1 by (clear - HH GT; unfold ard_conv; destruct (0 <? br_rv res) eqn:E; [reflexivity| apply Z.ltb_ge in E; lia]).
           rewrite RBE, Z.max_r in RBCp by (clear - HH GT; lia).
           apply (rw_cells_C8_C4C4 asegs _ _ [] (br_rv res) [] ltac:(clear - HH GT RVB OUTL; lia)) in RBCp. cbn [app] in RBCp.
           step. if_false. st1. rewrite sx32_lit by (clear - HH GT RVB OUTL; lia). step. apply evt_done. subst TGT. reflexivity. }
      assert (RVL : br_rv res = 0 \/ br_rv res = -1) by (clear - HH LE RVB; lia).
      replace (ard_conv (br_rv res)) with (br_rv res) by (clear - HH LE; unfold ard_conv; destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E; lia| reflexivity]).
      subst TGT. destruct RVL as [E|E]; rewrite E; step; if_true; apply evt_done; reflexivity. }
    cbv beta. intros ms' ->. subst TGT.
    (* [comment removed for export] *)
    lazymatch type of SHA with rw_cells _ ?mx ?A ?csA =>
    lazymatch type of SHB4 with rw_cells _ _ _ ?csB =>
    lazymatch type of SHCr with rw_cells _ _ _ ?csC =>
      assert (SHC : rw_cells asegs mx A (csA ++ csB ++ csC))
        by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact SHA|]; apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact SHB4| exact SHCr]);
      clear SHA SHB4 SHCr; cbn [app] in SHC
    end end end.
    (* [comment removed for export] *)
    assert (DJt1 : chunk_disj ff 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt2 : chunk_disj (ff + 40) 16 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt3 : chunk_disj (ff + 56) 8 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt4 : chunk_disj (ff + 32) 8 (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt5 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) (Z.shiftr ff 3 + 2147450880) 8)
      by (clear - HH OAPP SHF OUTL ZLE; unhide OAPP; unfold chunk_disj; cbn [cells_size csize Nat.add]; lia).
    assert (DJt6 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) (Z.shiftr ff 3 + 2147450880) 8) by (clear - HH PAPP SHF TLEN LENR; unhide PAPP; unfold chunk_disj; lia).
    assert (DJu1 : chunk_disj a 128 ff 32) by (clear - HH AW1; unhide AW1; unfold chunk_disj; lia).
    assert (DJu2 : chunk_disj (bf_ctx R) 2584 ff 32) by (clear - HH CW1; unhide CW1; unfold chunk_disj; lia).
    assert (DJu3 : chunk_disj (bf_enc R) 92 ff 32) by (clear - HH EW1; unhide EW1; unfold chunk_disj; lia).
    assert (DJu4 : chunk_disj mb 128 ff 32) by (clear - HH MW1; unhide MW1; unfold chunk_disj; lia).
    assert (DJu5 : chunk_disj (mb_bb M) 16 ff 32) by (clear - HH BBW1; unhide BBW1; unfold chunk_disj; lia).
    assert (DJu6 : chunk_disj (mb_bm M) 32 ff 32) by (clear - HH BMW1; unhide BMW1; unfold chunk_disj; lia).
    assert (DJu7 : chunk_disj (mb_rp M) 32 ff 32) by (clear - HH RPW1; unhide RPW1; unfold chunk_disj; lia).
    assert (DJu8 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) ff 32)
      by (clear - HH OW1 OUTL ZLE; unhide OW1; unfold chunk_disj; cbn [cells_size csize Nat.add]; lia).
    assert (DJu9 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) ff 32) by (clear - HH PW1 TLEN; unhide PW1; unfold chunk_disj; lia).
    assert (DJu10 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 32) by (clear - HH NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJv1 : chunk_disj a 128 fp 1) by (clear - HH AW3; unhide AW3; unfold chunk_disj; lia).
    assert (DJv2 : chunk_disj (bf_ctx R) 2584 fp 1) by (clear - HH CW3; unhide CW3; unfold chunk_disj; lia).
    assert (DJv3 : chunk_disj (bf_enc R) 92 fp 1) by (clear - HH EW3; unhide EW3; unfold chunk_disj; lia).
    assert (DJv4 : chunk_disj mb 128 fp 1) by (clear - HH MW3; unhide MW3; unfold chunk_disj; lia).
    assert (DJv5 : chunk_disj (mb_bb M) 16 fp 1) by (clear - HH BBW3; unhide BBW3; unfold chunk_disj; lia).
    assert (DJv6 : chunk_disj (mb_bm M) 32 fp 1) by (clear - HH BMW3; unhide BMW3; unfold chunk_disj; lia).
    assert (DJv7 : chunk_disj (mb_rp M) 32 fp 1) by (clear - HH RPW3; unhide RPW3; unfold chunk_disj; lia).
    assert (DJv8 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) fp 1)
      by (clear - HH OW3 OUTL ZLE; unhide OW3; unfold chunk_disj; cbn [cells_size csize Nat.add]; lia).
    assert (DJv9 : chunk_disj (mb_buf M) (Z.of_nat (length txt)) fp 1) by (clear - HH PW3 TLEN; unhide PW3; unfold chunk_disj; lia).
    assert (DJv10 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 fp 1) by (clear - HH DJs11; unfold chunk_disj in *; lia).
    (* [comment removed for export] *)
    step. st1. step. zstep. st1. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. step.
    (* [comment removed for export] *)
    zstep. do 10 st1. step. step.
    (* [comment removed for export] *)
    release_frame FR0 ST (sp2 + 16).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STm : stk asegs mx lo (bv_unsigned sp + -80)) by (eapply stk_merge; [exact ST| exact ST3| lia]) end.
    clear ST ST3. rename STm into ST. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold bioread_b64_post. cbv zeta. rewrite <- Eres.
    do 14 eexists. eexists.
    exists (bf_with_hdr R fl rt (bf_nread R + ard_rbv (br_rv res)) mb (bf_prev R)), d', (mset M (Z.of_nat (br_used res)) fl' nr'), junk'.
    exists ([(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)] ++ XSc).
    split; [reflexivity|].
    split.
    { apply Forall_app. split.
      - pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FS4. change (fsz 0) with 64 in FS4. change (fshn 0) with 8 in FS4. unfold AFS_FLAGS in FS4.
        rewrite <- (sh_shiftr ff) in FS4 by lia. rewrite ASHADOW_BASE_val in FS4. exact FS4.
      - eapply (fs_scratch_mono_Forall H). exact FXc. }
    split.
    { unhide MUX. unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE. cbn [app].
      pose proof (munch_absorb9 _ _ _ _ _ _ _ _ MUX MU ltac:(clear; intros x Hx; cbn in Hx |- *; tauto)) as MUF.
      pose proof (munch_reshape9 (lo, bv_unsigned sp) (out, out + outl)
                    [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)] XSc
                    [(a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)] _ _ MUF) as MUF2.
      exact MUF2. }
    split; [unhide WMX; exact (wmono_trans _ _ _ _ WMX WM)|].
    split; [exact MI|].
    split. { clear - HH ACp MU WM APff APfp ACEILB CEIL LO112 FF1 FF5 FB1 SHF HCEIL.
             eapply ACONST_frame; [exact ACp| exact MU| exact WM|].
             repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
             - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
             - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912;
                 rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
             - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
             - eapply aconst_ok_aapp; [exact APfp| cbn; lia| cbn; lia]. }
    split; [exact ST|].
    split. { (* [comment removed for export] *) split; [bio_unf_goal; exact BCp|]. split; [exists hdr, cjunk, 0; split; [exact LH|]; split; [exact LJ'|]; split; [clear; lia| unfold b64ctx_used_cells, wz; exact CTXp]|].
             unfold B64F_blocks. cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr].
             split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact RB1|]. split; [exact RB2|]. split; [exact RB3|].
             split; [exact FLp|]. split; [exact RTp|]. split; [clear - HH NRR NR0 RBV RVB OUTL; lia|]. split; [clear - HH MP MH MCE ACEILB; lia| exact PVR]. }
    split; [reflexivity|]. split; [reflexivity|].
    split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
    split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
             split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
             split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact TXTp|]. split; [exact OUTp|].
    split.
    { (* [comment removed for export] *)
      rewrite <- (lf_remove_head 0 ff fp LF).
      eapply (ah_release H HH); [exact RFSp| left; reflexivity| exact MU| exact WM| |].
      - unhide NSfs. clear - HH NSfs SHF FB1 FB2 FP3 FP4 FF5 FF6 ACEILB CEIL LO112.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; cbn [fst snd] in *.
        + left. left. lia.
        + left. left. lia.
        + left. right. exists (0, ff, fp). split; [left; reflexivity|]. cbn. change (fsz 0) with 64. lia.
        + right. split; reflexivity.
      - destruct FPC as [[_ (B0 & B1 & B2)] _]. specialize (B2 0%nat ltac:(cbn; lia)). cbn in B2. rewrite Z.add_0_r in B2. exact B2. }
    split.
    { eapply arelro_across7; [exact RLp| exact MU|].
      clear - HH FF1 FB1 FP1 SHF ACEILB CEIL LO112. unfold AIMG_TOP in *.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    eapply (ah_RHEAP_frame H HH); [exact HPp| exact MU| exact WM|].
    clear - HH CEIL FB1 FB2 FB3 FF5 FF6 FP3 FP4 FF1 SHF ACEILB.
    repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE;
      first [ left; lia | do 4 right; left; lia
            | do 5 right; left; unfold sh; rewrite ASHADOW_BASE_val, ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia
            ].
  Qed.

End S.

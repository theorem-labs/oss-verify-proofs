(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma bytes_at_mid : forall m A ds k n, bytes_at asegs m A ds -> (k + n <= length ds)%nat ->
  bytes_at asegs m (A + Z.of_nat k) (firstn n (skipn k ds)).
Proof.
  intros m A ds k n HB HL. rewrite <- (firstn_skipn k ds) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite firstn_length_le in HB by lia. rewrite <- (firstn_skipn n (skipn k ds)) in HB. apply bytes_at_app in HB. exact (proj1 HB).
Qed.

(* [comment removed for export] *)
Lemma clr_flags_facts : forall f, 0 <= f < 2^31 -> Z.land f 512 = 512 -> Z.land f 128 = 0 ->
  0 <= Z.land f (Z.lnot 15) < 2^31 /\ Z.land (Z.land f (Z.lnot 15)) 512 = 512 /\ Z.land (Z.land f (Z.lnot 15)) 128 = 0.
Proof.
  intros f Hf H9 H7. change (Z.land f (Z.lnot 15)) with (Z.ldiff f 15).
  assert (RNG : 0 <= Z.ldiff f 15 < 2^31).
  { change 15 with (Z.ones 4). rewrite Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    assert (0 <= f / 2^4 <= f / 1) by (split; [apply Z.div_pos; lia| apply Z.div_le_compat_l; lia]). rewrite Z.div_1_r in *. nia. }
  split; [exact RNG|]. split.
  - apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.ldiff_spec by lia.
    destruct (Z.eq_dec n 9) as [->|NE].
    + apply (f_equal (fun z => Z.testbit z 9)) in H9. rewrite Z.land_spec in H9. change (Z.testbit 512 9) with true in H9 |- *.
      change (Z.testbit 15 9) with false. rewrite Bool.andb_true_r in H9. rewrite H9. reflexivity.
    + replace (Z.testbit 512 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
      symmetry. destruct (Z.lt_ge_cases n 9) as [L|L].
      * destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
        destruct (Z.eq_dec n 3) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 5) as [->|]; [reflexivity|].
        destruct (Z.eq_dec n 6) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 7) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 8) as [->|]; [reflexivity|]. lia.
      * apply Z.bits_above_log2; [lia|]. cbn. lia.
  - apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0 by lia.
    destruct (Z.eq_dec n 7) as [->|NE].
    + apply (f_equal (fun z => Z.testbit z 7)) in H7. rewrite Z.land_spec, Z.bits_0 in H7. change (Z.testbit 128 7) with true in H7 |- *.
      rewrite Bool.andb_true_r in H7. rewrite H7. reflexivity.
    + replace (Z.testbit 128 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
      symmetry. destruct (Z.lt_ge_cases n 7) as [L|L].
      * destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
        destruct (Z.eq_dec n 3) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 5) as [->|]; [reflexivity|].
        destruct (Z.eq_dec n 6) as [->|]; [reflexivity|]. lia.
      * apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition AMR_RA1 : Z := 0x417614.   (* [comment removed for export] *)
  Definition AMR_RA2 : Z := 0x417674.   (* [comment removed for export] *)

  Lemma amemread_spec : memread_stmt H.
  Proof.
    unfold memread_stmt. intros until junk; intros A0 A1 A2 OUTL MB BL SEP BS LEN OUTC MO SH PAY OSH AC ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_mem_read, MEMREAD_STACK, FR_mem_read, AINTRIN_STACK in *. acb.
    pose proof BL as BL0. pose proof SH as SH0.
    membio_open m a R MB BL SH AC.
    pose proof SEP as SEP0. destruct SEP0 as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4).
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4. unfold O_METH_BREAD in OUTM.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK).
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4; hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    pose proof ACCa as ACCa0. hide ACCa0. pose proof ACCbm as ACCbm0. hide ACCbm0.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (a, a + 128); (mb_bm R, mb_bm R + 32)]) by nsw_tac.
    carve_frame 80%nat ST.
    unhide OUTR. do 11 step.                                           (* [comment removed for export] *)
    unhide OF1; unhide OF3. membio_reacc MU. hide OF1; hide OF3; hide OUTR.
    unfold id in ACCa, ACCbb, ACCbm, ACCrp.
    (* [comment removed for export] *)
    step. ub_dead. do 2 step. ubal_by AAL. step. if_lit.
    (* [comment removed for export] *)
    do 7 zstep. ck8_check ACCa (a + 64).
    (* [comment removed for export] *)
    do 2 step. ub_dead. step. ubal_by BBAL. step. if_lit. do 4 zstep. ck8_check ACCa (a + 48).
    (* [comment removed for export] *)
    st1. zstep. zstep. zstep. rewrite (sx32_lit (mb_flags R)), (unsigned_lit (mb_flags R)) by lia. rewrite rdonly_off0 by lia. zstep.
    rewrite ?Z.add_0_r.
    (* [comment removed for export] *)
    zstep. zstep. ck8_check ACCbb (mb_bb R).
    (* [comment removed for export] *)
    do 2 step. step. step. unfold P_BIO_clear_flags. step.
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail; lia).
    assert (BOK : bio_ok (membio_bio R)).
    { unfold bio_ok, membio_bio; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_mem_buf_method. lia. }
    eapply evt_cut.
    { eapply (abioclearflags_spec H) with (B := membio_bio R) (lo := lo); [reflexivity| reflexivity| lia| | exact BOK| unfold BIO_SIZE; lia
        | unfold BIO_SIZE; eapply addressable_across2; [exact SHa| exact AAP| exact MU| exact WM| exact NSW0]
        | exact RB1
        | eapply ACONST_memrd; [exact AC| exact MU| exact WM| exact CEIL| exact OAOK| exact AAP| exact BMAP]
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      { unfold bio_cells, membio_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]. exact BC. }
    }
    unfold bioacc_post, BIO_SIZE. aland_open MU.
    carry1 MUc WMc BBC using AP1. carry1 MUc WMc BMC using AP2. carry1 MUc WMc RPC using AP3. carry1 MUc WMc FR.
    carry1 MUc WMc OUTC using OUTR OF1. carry1 MUc WMc BS using PS1. carry1 MUc WMc GSB. carry1 MUc WMc SHB.
    aland_close MU WM MUc WMc. unfold AMR_RA1 || idtac.
    match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC2 end.
    pose proof (clr_flags_facts (mb_flags R) FLR RDO AEOF) as (FL1 & FL2 & FL3).
    unfold bio_cells, bio_with_flags, membio_bio, wz in BC2.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC2.
    clear ACCa ACCbb ACCbm ACCrp.
    pose proof ACCbm0 as ACCbm; unhide ACCbm. unhide OF1; unhide OF3; unhide OUTR. membio_reacc MU. hide OF1; hide OF3; hide OUTR. unfold id in ACCbm.
    (* [comment removed for export] *)
    do 2 step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. ub_dead. step. ubal_by BMAL. step. if_lit. zstep. ck8_check ACCbm (mb_bm R).
    (* [comment removed for export] *)
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { step. step. if_cases K1; zify_cond K1.
      - replace (Z_to_bv 64 (mb_len R - mb_pos R) : word) with (Z_to_bv 64 (mb_rdn R outl) : word) by (unfold mb_rdn, mb_avail; f_equal; lia).
        apply evt_done; subst TGT; reflexivity.
      - step. apply evt_done. subst TGT. unfold mb_rdn, mb_avail. repeat f_equal. lia. }
    subst TGT. cbv beta. intros ms' ->.
    (* [comment removed for export] *)
    unhide OUTR. do 2 step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. hide OUTR.
    step. if_cases K3; zify_cond K3.
    - step. ub_dead. step. if_lit. (* [comment removed for export] *)
      zstep. ck8_check ACCbm (mb_bm R).
      do 2 step. if_cases K4; zify_cond K4; [unfold mb_rdn, mb_avail in K3; kill K4|]. clear K4.
      (* [comment removed for export] *)
      pose proof ACCa0 as ACCa; unhide ACCa. unhide OF1; unhide OF3; unhide OUTR. membio_reacc MU. hide OF1; hide OF3; hide OUTR. unfold id in ACCa.
      zstep. zstep. zstep. ck8_check ACCa (a + 56). st1. rewrite NUMR, sx32_lit by lia. step. if_lit.
      (* [comment removed for export] *)
      rewrite K3. zstep. do 9 st1. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post.
      pose proof (rw_cells_CB_split _ _ _ _ 0%nat _ OUTC ltac:(lia)) as [OUT1 OUT2]. cbn [firstn skipn Nat.sub] in OUT1, OUT2. rewrite Nat.sub_0_r in OUT2.
      do 15 eexists. exists junk. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [eapply ACONST_memrd; [exact AC| exact MU| exact WM| exact CEIL| exact OAOK| exact AAP| exact BMAP]|].
      split; [exact ST|].
      split. { unfold mb_after_bread. membio_tac; cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid]; rewrite ?Z.add_0_r; try assumption; try lia.
               }
      split. { exact BS. }
      split; [| exact I].
      replace (mb_take R ds 0) with (@nil byte) by reflexivity. cbn [length]. rewrite Nat.sub_0_r.
      change ([CB 0%nat (@nil byte); CB (Z.to_nat outl) junk]) with ([CB 0%nat (@nil byte)] ++ [CB (Z.to_nat outl) junk]).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact OUT1| exact OUT2].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. ck8_check ACCbm (mb_bm R + 8). st1. step. step. step. unfold AASAN_MEMCPY || idtac. step.
      pose proof (rw_cells_CB_split _ _ _ _ (Z.to_nat (mb_rdn R outl)) _ OUTC ltac:(lia)) as [OUT1 OUT2].
      pose proof (bytes_at_mid _ _ _ (Z.to_nat (mb_pos R)) (Z.to_nat (mb_rdn R outl)) BS ltac:(lia)) as SRC. rewrite Z2Nat.id in SRC by lia.
      assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
      { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
      pose proof PACC as PACCc. change (id (accessible m (mb_buf R) (mb_len R))) in PACCc.
      pose proof OACC as OACCc. change (id (accessible m out outl)) in OACCc.
      unhide OF1; unhide OF3; unhide OUTR. membio_reacc MU. hide OF1; hide OF3; hide OUTR. unfold id in PACCc, OACCc.
      pose proof OACC as (_ & OHI & _).
      eapply evt_cut.
      { eapply (asan_memcpy_specZ H HH) with (lo := lo) (src := mb_take R ds (mb_rdn R outl)).
        all: lazymatch goal with
         | |- bytes_at _ _ _ _ => exact SRC
         | |- length _ = _ => exact SL
         | |- rw_cells _ _ _ _ => exact OUT1
         | |- accessible _ (mb_buf _ + _) _ => eapply accessible_sub; [exact PACCc| lia| lia| lia]
         | |- accessible _ _ _ => eapply accessible_sub; [exact OACCc| lia| lia| lia]
         | |- shvis _ (mb_buf _ + _) _ => eapply shvis_sub; [eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| lia| lia| lia| lia| lia]
         | |- shvis _ _ _ => eapply shvis_sub; [eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| lia| lia| lia| lia| lia]
         | |- in_app_mem (mb_buf _ + _) _ => eapply in_app_mem_sub; [exact PAPP| lia| lia]
         | |- in_app_mem _ _ => eapply in_app_mem_sub; [exact OAPP| lia| lia]
         | |- aconst_ok _ => intros x Hx; apply OAOK; cbn [fst snd] in *; lia
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => assumption
         | |- ACONST _ => assumption
         | |- _ => unhide OUTR; unhide OUTB; lia
        end. }
      unfold amove_post. clear OUT1 SRC. aland_open MU.
      carry1 MUc WMc BC2 using OF1. carry1 MUc WMc BBC using OF2. carry1 MUc WMc BMC using OF3. carry1 MUc WMc RPC using OF4.
      carry1 MUc WMc FR using OUTR. carry1 MUc WMc OUT2 using OUTR. carry1 MUc WMc BS using OUTB.
      aland_close MU WM MUc WMc. unfold AMR_RA2 || idtac.
      match goal with X : rw_cells asegs _ out [CB _ (mb_take _ _ _)] |- _ => rename X into OUT1' end.
      clear ACCbm PACCc OACCc. repeat match goal with X : bytes_at _ _ (mb_buf R + mb_pos R) _ |- _ => clear X end.
      (* [comment removed for export] *)
      assert (DJ1 : chunk_disj a 128 (mb_bm R) 32) by (unhide AP2; unfold chunk_disj; lia).
      assert (DJ2 : chunk_disj (mb_bb R) 16 (mb_bm R) 32) by (unhide AP4; unfold chunk_disj; lia).
      assert (DJ3 : chunk_disj (mb_rp R) 32 (mb_bm R) 32) by (unhide AP6; unfold chunk_disj; lia).
      unhide OF3; unhide PS3.
      pose proof ACCbm0 as ACCbm; unhide ACCbm. unhide OF1; unhide OUTR. membio_reacc MU. hide OF1; hide OUTR. unfold id in ACCbm.
      (* [comment removed for export] *)
      ck8_check ACCbm (mb_bm R). st1. zstep. st1.
      (* [comment removed for export] *)
      clear ACCbm. pose proof ACCbm0 as ACCbm; unhide ACCbm. unhide OF1; unhide OUTR. membio_reacc MU. hide OF1; hide OUTR. unfold id in ACCbm.
      zstep. zstep. zstep. ck8_check ACCbm (mb_bm R + 16).
      (* [comment removed for export] *)
      st1. st1.
      (* [comment removed for export] *)
      do 2 step. st1. step. ub_dead. step. ub_dead. step. ub_dead. clear ACCbm. pose proof ACCbm0 as ACCbm; unhide ACCbm. unhide OF1; unhide OUTR. membio_reacc MU. hide OF1; hide OUTR. unfold id in ACCbm. ck8_check ACCbm (mb_bm R + 8). st1. step. zstep. rewrite ?Z.add_0_r. rewrite ?swrap32_small by lia. do 9 st1. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post.
      do 15 eexists. exists (skipn (Z.to_nat (mb_rdn R outl)) junk). split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [eapply ACONST_memrd; [exact AC| exact MU| exact WM| exact CEIL| exact OAOK| exact AAP| exact BMAP]|].
      split; [exact ST|].
      split. { unfold mb_after_bread. membio_tac; cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid]; rewrite ?Z.add_0_r; try assumption; try lia.
               all: try (rewrite (unsigned_lit (mb_len R - mb_pos R)), (unsigned_lit (mb_rdn R outl)) in BMC by lia;
                         replace (mb_len R - (mb_pos R + mb_rdn R outl)) with (mb_len R - mb_pos R - mb_rdn R outl) by lia;
                         replace (mb_buf R + (mb_pos R + mb_rdn R outl)) with (mb_rdn R outl + (mb_buf R + mb_pos R)) by lia; exact BMC).
               }
      split. { exact BS. }
      split; [| exact I].
      rewrite SL. change ([CB (Z.to_nat (mb_rdn R outl)) (mb_take R ds (mb_rdn R outl)); CB (Z.to_nat outl - Z.to_nat (mb_rdn R outl)) (skipn (Z.to_nat (mb_rdn R outl)) junk)])
        with ([CB (Z.to_nat (mb_rdn R outl)) (mb_take R ds (mb_rdn R outl))] ++ [CB (Z.to_nat outl - Z.to_nat (mb_rdn R outl)) (skipn (Z.to_nat (mb_rdn R outl)) junk)]).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact OUT1'|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact OUT2.
  Qed.
End S.

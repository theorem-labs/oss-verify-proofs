From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fread_c fread_ro_c memmove_c memmove_ro_c
  pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac show_st := lazymatch goal with |- evt _ _ ?st => idtac "GOAL:" st end.

Ltac untag_fin swb Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2 :=
  let mm := cur_mem in
  let MS5 := fresh "MS5" in let RO5 := fresh "RO5" in let KIND := fresh "KIND" in let TAG := fresh "TAG" in
  pose proof (mstl_transport _ _ _ _ _ _ _ _ _ MS4 MUP WMP ltac:(disj_tac) ltac:(disj_tac)) as MS5;
  pose proof (ro_agree_munch_apart _ _ _ RO4 MUP ltac:(ro_tac)) as RO5;
  assert (KIND : kind swb Fc cap q = KFit) by kind_tac;
  assert (TAG : tagged swb Fc q = false) by (unfold tagged; bool_dec; reflexivity);
  apply evt_done; do 22 eexists; exists mm;
  split; [right; left; split; [exact KIND|] |];
  [ unfold pos_of, vt_of, vid_of, is_fit, rec_len; rewrite KIND, TAG;
    split; [reflexivity|];
    split; [rewrite uns_swrap_mod32_0 by lia; reflexivity|];
    split; [exact MS5|]; split; [exact HPS|];
    exists bj4; split; [exact HBJ4|]; split; [lia|];
    unfold rec_bytes; rewrite TAG; cbv zeta; unfold rec_raw; rewrite Ebj4;
    apply firstn_rec; rewrite length_firstn, length_skipn; lia
  | split; [exact MUT4|]; split; [exact WMT4|]; split; [exact RO5|]; split; [exact ST4|]; exists ph2; exact PH2 ].


Lemma psn_body : fread_ro_contract -> memmove_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ps buf cap h swz b q lo : Z) (sw : bool) (Fc : list byte) (pv nx lolc lvt lvid : word) (bj ph pad : list byte),
    s1 = wz ps -> s2 = wz buf -> s4 = wz cap -> s7 = wz 16 -> s8 = wz 0xff00 -> a3 = wz h -> sw = (swz =? 1) ->
    rw_cells rsegs m (bv_unsigned sp) [CB 16 ph] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 5632 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    bv_unsigned sp + 96 <= ps -> rw_cells rsegs m ps (ps_cells (wz h) (wz swz) lolc lvt lvid pad) ->
    (swz = 0 \/ swz = 1) ->
    mstl m h b Fc q pv nx -> img_apart h 1304 -> h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    Z.of_nat (length Fc) < 2 ^ 26 ->
    0 <= cap < 2 ^ 64 -> 4096 <= buf -> u8arr rsegs m buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
    img_apart buf (Z.max cap 1) -> buf + Z.max cap 1 <= lo ->
    (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) -> (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word) m',
         (((kind sw Fc cap q = KEnd \/ kind sw Fc cap q = KCutH \/ kind sw Fc cap q = KCutFit) /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 (wz (res_of sw Fc cap q)) s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x178)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (pos_of sw Fc cap q) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (if hdr_kind (kind sw Fc cap q) then wz (orig sw Fc q) else lolc)
                                   lvt lvid pad) /\
           exists bj', u8arr rsegs m' buf bj' /\ length bj' = length bj) \/
          (kind sw Fc cap q = KFit /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 s3' (wz (hw sw Fc q 4)) s5' s6' (wz (hw sw Fc q 0)) s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x2ac)%Z)) fc None m' (seg_rom rsegs) /\
           bv_unsigned s6' mod 2 ^ 32 = rec_len sw Fc q /\
           mstl m' h b Fc (pos_of sw Fc cap q) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (wz (orig sw Fc q))
                                   (vt_of sw Fc cap q lvt) (vid_of sw Fc cap q lvid) pad) /\
           exists bj', u8arr rsegs m' buf bj' /\ length bj' = length bj /\
             firstn (Z.to_nat (incl sw Fc q)) bj' = rec_bytes sw Fc q) \/
          (kind sw Fc cap q = KEmpty /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' (wz h) a4' a5' a6' a7'
                         s2 s3' s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (q + 16) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) lolc lvt lvid pad) /\ u8arr rsegs m' buf bj) \/
          (big_kind (kind sw Fc cap q) = true /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 (wz (-1)) s4 s5' (wz (bv_swrap 32 (incl sw Fc q))) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x134)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (q + 16) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (wz (orig sw Fc q)) lvt lvid pad) /\ u8arr rsegs m' buf bj)) /\
         munch [(bv_unsigned sp - 5632, bv_unsigned sp + 16); (ps, ps + 24); (buf, buf + Z.max cap 1); (h, h + 1304)] m m' /\
         wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         exists ph', rw_cells rsegs m' (bv_unsigned sp) [CB 16 ph'])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HFR HMM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ps buf cap h swz b q lo sw Fc pv nx lolc lvt lvid bj ph pad
    E1 E2 E4 E7 E8 EA3 ESW HPH ST LO HLO HPS0 HPS HSW HMS HIH HHL HBL HN26 HCAP HB4K HBJ HBN HIB HBL2 HBH HBB RO.
  subst s1 s2 s4 s7 s8 a3.
  unfold fread_ro_contract, FREAD in HFR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize ps_cells Nat.add] in HPR.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (HQ : 0 <= q <= Z.of_nat (length Fc) /\ 0 < h /\ 0 < b).
  { destruct HMS as (fl & md & q' & rb & (bf & (pd0 & pd1 & pd2 & ung & HC & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd)
                     & R1 & R2 & R3 & R4).
    destruct rb as [[i e]|]; cbn [rlen] in R3; lia. }
  pose proof (munch_refl [(bv_unsigned sp - 5632, bv_unsigned sp + 16); (ps, ps + 24); (buf, buf + Z.max cap 1);
                          (h, h + 1304)] m) as MUT.
  pose proof (wmono_refl rsegs m) as WMT.
  unfold ps_cells, wz in *.
  do 4 step.
  eapply evt_cut.
  { eapply HFR with (lo := lo) (b := b) (Fc := Fc) (p := q) (pv := pv) (nx := nx) (junk := ph).
    - rewrite unsigned_lit by lia. exact HMS.
    - rewrite unsigned_lit by lia. apply not_ro_apart; [lia | lia | exact HIH].
    - reflexivity.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. exact HPH.
    - rewrite unsigned_lit by lia. apply not_ro_hi; lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite unsigned_lit by lia. right. lia.
    - right. lia.
    - exact RO.
    - exact ST.
    - apply not_ro_hi; lia.
    - unfold FREAD_K. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact HBL. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
    & E & EA & MUf & WMf & RO2 & ST2 & BY2 & MS2).
  subst ms'.
  unfold fread_j, FREAD_K in EA, MUf, BY2, MS2.
  rewrite ?unsigned_lit in EA by lia. rewrite ?unsigned_lit in MUf by lia.
  rewrite ?unsigned_lit in BY2 by lia. rewrite ?unsigned_lit in MS2 by lia.
  replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x60)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x60)%Z)) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  xp_rw HPS MUf WMf.
  xp_u8 HBJ MUf WMf.
  pose proof (munch_ext _ _ _ _ _ MUT MUf ltac:(out_tac)) as MUT2. clear MUT.
  pose proof (wmono_trans rsegs _ _ _ WMT WMf) as WMT2. clear WMT.
  pose proof (ph_after _ _ _ _ _ _ HPH MUf WMf BY2 ltac:(rewrite length_firstn; lia)
                ltac:(rewrite length_firstn, length_skipn; out_tac)) as PH2e.
  clear HPH ST RO HMS MUf WMf.
  unfold wz in EA. subst a0'.
  do 2 step.
  destruct (Z_lt_le_dec (Z.of_nat (length Fc) - q) 16) as [CS|CL].
  - rewrite Z.min_r in * by lia. destruct PH2e as [ph2 PH2].
    assert (EJ : bv_unsigned (Z_to_bv 64 (Z.of_nat (length Fc) - q)) = Z.of_nat (length Fc) - q)
      by (apply unsigned_lit; lia).
    replace (q + (Z.of_nat (length Fc) - q)) with (Z.of_nat (length Fc)) in MS2 by lia.
    if_true. step.
    destruct (Z.eq_dec (Z.of_nat (length Fc) - q) 0) as [C0|C0].
    + assert (KIND : kind sw Fc cap q = KEnd) by kind_tac.
      if_false. do 2 step.
      apply evt_done. do 22 eexists. exists m2.
      split; [left; split; [left; exact KIND|]|].
      * unfold res_of, pos_of, hdr_kind. rewrite KIND. unfold flen. rewrite C0.
        split; [reflexivity|]. split; [exact MS2|]. split; [exact HPS|]. exists bj. split; [exact HBJ | reflexivity].
      * split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2|]. split; [exact ST2|]. exists ph2. exact PH2.
    + assert (KIND : kind sw Fc cap q = KCutH) by kind_tac.
      if_true.
      apply evt_done. do 22 eexists. exists m2.
      split; [left; split; [right; left; exact KIND|]|].
      * unfold res_of, pos_of, hdr_kind. rewrite KIND. unfold flen.
        split; [reflexivity|]. split; [exact MS2|]. split; [exact HPS|]. exists bj. split; [exact HBJ | reflexivity].
      * split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2|]. split; [exact ST2|]. exists ph2. exact PH2.
  - rewrite Z.min_l in * by lia.
    change (Z.to_nat 16) with 16%nat in BY2.
    assert (HB : forall k r, 0 <= k < 16 -> r = q + k ->
              ov_read_bytes rsegs m2 (wa (bv_unsigned sp + k)) 1 = Some [nth (Z.to_nat r) Fc (Z_to_bv 8 0)])
      by (intros k r Hk Hr; eapply hdr_ov; [exact BY2 | lia | lia | exact Hk | exact Hr]).
    pose proof (HB 0 (q + 0) ltac:(lia) eq_refl) as HB0. pose proof (HB 1 (q + 1) ltac:(lia) eq_refl) as HB1.
    pose proof (HB 2 (q + 2) ltac:(lia) eq_refl) as HB2. pose proof (HB 3 (q + 3) ltac:(lia) eq_refl) as HB3.
    pose proof (HB 4 (q + 4) ltac:(lia) eq_refl) as HB4. pose proof (HB 5 (q + 5) ltac:(lia) eq_refl) as HB5.
    pose proof (HB 6 (q + 6) ltac:(lia) eq_refl) as HB6. pose proof (HB 7 (q + 7) ltac:(lia) eq_refl) as HB7.
    pose proof (HB 8 (q + 8) ltac:(lia) eq_refl) as HB8. pose proof (HB 9 (q + 9) ltac:(lia) eq_refl) as HB9.
    pose proof (HB 10 (q + 10) ltac:(lia) eq_refl) as HB10. pose proof (HB 11 (q + 11) ltac:(lia) eq_refl) as HB11.
    pose proof (HB 12 (q + 12) ltac:(lia) eq_refl) as HB12. pose proof (HB 13 (q + 13) ltac:(lia) eq_refl) as HB13.
    pose proof (HB 14 (q + 14) ltac:(lia) eq_refl) as HB14. pose proof (HB 15 (q + 15) ltac:(lia) eq_refl) as HB15.
    clear HB.
    if_false.
    destruct HSW as [SW|SW]; subst swz; cbn in ESW; subst sw.
    + pose proof (hw_range false Fc q 8) as RI. change (hw false Fc q 8) with (incl false Fc q) in RI.
      do 12 step.
      if_true.
      rep_reg 22 (Z_to_bv 64 (bv_swrap 32 (incl false Fc q))) ltac:(hw_eq).
      step.
      destruct (Z.eq_dec (incl false Fc q) 0) as [I0|I0].
      * assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl false Fc q))) (Z_to_bv 64 0) = true)
          by (rewrite eqb_swrap0 by lia; apply Z.eqb_eq; exact I0).
        rewrite C; cbv iota.
        do 2 step.
        destruct PH2e as [ph2 PH2].
        assert (KIND : kind false Fc cap q = KEmpty) by kind_tac.
        apply evt_done. do 22 eexists. exists m2.
        split; [right; right; left; split; [exact KIND|]|].
        -- split; [reflexivity|]. split; [exact MS2|]. split; [exact HPS | exact HBJ].
        -- split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2|]. split; [exact ST2|]. exists ph2. exact PH2.
      * assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl false Fc q))) (Z_to_bv 64 0) = false)
          by (rewrite eqb_swrap0 by lia; apply Z.eqb_neq; exact I0).
        rewrite C; cbv iota.
        do 11 step.
        if_true.
        rep_reg 13 (Z_to_bv 64 (orig false Fc q)) ltac:(hw_eq).
        assert (HB0' : ov_read_bytes rsegs m2 sp 1 = Some [nth (Z.to_nat (q + 0)) Fc (Z_to_bv 8 0)]).
        { rewrite <- HB0. f_equal. unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
        do 10 step.
        destruct PH2e as [ph2 PH2].
        pose proof (munch_refl [(ps, ps + 24)] m2) as MUP. pose proof (wmono_refl rsegs m2) as WMP.
        step.
        rewrite zx32_val, uns_swrap_mod32_0 by lia.
        assert (EI : bv_unsigned (Z_to_bv 64 (incl false Fc q)) = incl false Fc q) by (apply unsigned_lit; lia).
        assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
        step.
        let mm := cur_mem in rename mm into m3.
        pose proof (kp_mstl m2 m3 0 ps (keep_munch _ _ _ 0 ps MUP ltac:(lia) ltac:(lia)
                      ltac:(intros; cbn; split; [lia | exact I])) _ _ _ _ _ _ MS2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as MS3.
        pose proof (ro_agree_munch_apart _ _ _ RO2 MUP ltac:(ro_tac)) as RO3.
        clear MS2 RO2.
        destruct (Z_le_gt_dec (incl false Fc q) cap) as [FITp|BIGp].
        -- if_true.
           do 13 step.
           if_true.
           rep_reg 20 (Z_to_bv 64 (hw false Fc q 4)) ltac:(hw_eq).
           rep_reg 23 (Z_to_bv 64 (hw false Fc q 0)) ltac:(hw_eq).
           do 5 step.
           eapply evt_cut.
           { eapply HFR with (lo := lo) (b := b) (Fc := Fc) (p := q + 16) (pv := pv) (nx := nx)
               (junk := firstn (Z.to_nat (incl false Fc q)) bj).
             - rewrite unsigned_lit by lia. exact MS3.
             - rewrite unsigned_lit by lia. apply not_ro_apart; [lia | lia | exact HIH].
             - reflexivity.
             - rewrite unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. apply u8arr_take; [exact HBJ | lia].
             - rewrite !unsigned_lit by lia. apply not_ro_apart; [lia | lia | unfold img_apart in *; lia].
             - rewrite !unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. left. lia.
             - exact RO3.
             - exact ST2.
             - apply not_ro_hi; lia.
             - unfold FREAD_K. lia.
             - rewrite unsigned_lit by lia. lia.
             - exact HBL. }
           intros ms' (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m4
             & E4 & EA4 & MU4 & WM4 & RO4 & ST4 & BY4 & MS4).
           subst ms'.
           unfold fread_j, FREAD_K in EA4, MU4, BY4, MS4.
           rewrite ?unsigned_lit in EA4 by lia. rewrite ?unsigned_lit in MU4 by lia.
           rewrite ?unsigned_lit in BY4 by lia. rewrite ?unsigned_lit in MS4 by lia.
           unfold wz in EA4. subst a0b.
           replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x248)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x248)%Z))
             by (symmetry; apply ret_pc_even; [lia | reflexivity]).
           xp_rw HPS MU4 WM4. xp_rw PH2 MU4 WM4.
           pose proof (u8arr_after _ _ _ _ _ _ HBJ MU4 WM4 BY4 ltac:(rewrite length_firstn; lia)
                         ltac:(rewrite length_firstn, length_skipn; out_tac)) as HBJ4.
           pose proof (munch_ext _ _ _ _ _ MUT2 MU4 ltac:(out_tac)) as MUT4. clear MUT2.
           pose proof (wmono_trans rsegs _ _ _ WMT2 WM4) as WMT4. clear WMT2.
           clear HBJ MS3 RO3 ST2 MU4 WM4 MUP WMP.
           step.
           destruct (Z_lt_le_dec (Z.of_nat (length Fc) - (q + 16)) (incl false Fc q)) as [CF|FF].
           ++ rewrite Z.min_r in * by lia.
              assert (EJ : bv_unsigned (Z_to_bv 64 (Z.of_nat (length Fc) - (q + 16))) = Z.of_nat (length Fc) - (q + 16))
                by (apply unsigned_lit; lia).
              if_true.
              assert (KIND : kind false Fc cap q = KCutFit) by kind_tac.
              replace (q + 16 + (Z.of_nat (length Fc) - (q + 16))) with (Z.of_nat (length Fc)) in MS4 by lia.
              apply evt_done. do 22 eexists. exists m4.
              split; [left; split; [right; right; exact KIND|]|].
              ** unfold res_of, pos_of, hdr_kind. rewrite KIND. unfold flen.
                 split; [reflexivity|]. split; [exact MS4|]. split; [exact HPS|].
                 eexists. split; [exact HBJ4|].
                 rewrite length_app; repeat first [rewrite length_firstn | rewrite length_skipn]; lia.
              ** split; [exact MUT4|]. split; [exact WMT4|]. split; [exact RO4|]. split; [exact ST4|]. exists ph2. exact PH2.
           ++ rewrite Z.min_l in * by lia.
              if_false.
              match type of HBJ4 with u8arr _ _ _ ?L => remember L as bj4 eqn:Ebj4 end.
              assert (HBN4 : Z.of_nat (length bj4) = Z.max cap 1).
              { rewrite Ebj4, length_app; repeat first [rewrite length_firstn | rewrite length_skipn]; lia. }
              clear BY4.
              pose proof (munch_refl [(ps, ps + 24)] m4) as MUP. pose proof (wmono_refl rsegs m4) as WMP.
              do 4 step.
              rewrite ltu_swrap by lia.
              destruct (Z_lt_le_dec (incl false Fc q) 18) as [T18|T18].
              ** rewrite (proj2 (Z.ltb_lt _ _) T18). cbv iota.
                 untag_fin false Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
              ** rewrite (proj2 (Z.ltb_ge _ _) T18). cbv iota.
                 let mm := cur_mem in rename mm into m5.
                 assert (HR12 : ov_read_bytes rsegs m5 (wa (buf + 12)) 1 = Some [nth (Z.to_nat (q + 28)) Fc (Z_to_bv 8 0)]).
                 { eapply (u8arr_read rsegs m5 buf bj4 12); [exact HBJ4 | | lia | reflexivity].
                   rewrite Ebj4, (rec_nth Fc _ q (incl false Fc q) 12) by lia.
                   replace (q + 16 + 12) with (q + 28) by lia. reflexivity. }
                 assert (HR13 : ov_read_bytes rsegs m5 (wa (buf + 13)) 1 = Some [nth (Z.to_nat (q + 29)) Fc (Z_to_bv 8 0)]).
                 { eapply (u8arr_read rsegs m5 buf bj4 13); [exact HBJ4 | | lia | reflexivity].
                   rewrite Ebj4, (rec_nth Fc _ q (incl false Fc q) 13) by lia.
                   replace (q + 16 + 13) with (q + 29) by lia. reflexivity. }
                 assert (EZ28 : bv_unsigned (zxb (nth (Z.to_nat (q + 28)) Fc (Z_to_bv 8 0))) = fb Fc (q + 28))
                   by (rewrite zxb_val; reflexivity).
                 assert (EZ29 : bv_unsigned (zxb (nth (Z.to_nat (q + 29)) Fc (Z_to_bv 8 0))) = fb Fc (q + 29))
                   by (rewrite zxb_val; reflexivity).
                 do 3 step.
                 destruct (Z.eq_dec (fb Fc (q + 28)) 129) as [B28|B28].
                 --- if_false.
                     do 2 step.
                     destruct (Z.eq_dec (fb Fc (q + 29)) 0) as [B29|B29].
                     +++ if_false.
                         do 2 step.
                         let mm := cur_mem in rename mm into m6.
                         assert (HR14 : ov_read_bytes rsegs m6 (wa (buf + 14)) 1 = Some [nth (Z.to_nat (q + 30)) Fc (Z_to_bv 8 0)]).
                         { eapply (u8arr_read rsegs m6 buf bj4 14); [exact HBJ4 | | lia | reflexivity].
                           rewrite Ebj4, (rec_nth Fc _ q (incl false Fc q) 14) by lia.
                           replace (q + 16 + 14) with (q + 30) by lia. reflexivity. }
                         assert (HR15 : ov_read_bytes rsegs m6 (wa (buf + 15)) 1 = Some [nth (Z.to_nat (q + 31)) Fc (Z_to_bv 8 0)]).
                         { eapply (u8arr_read rsegs m6 buf bj4 15); [exact HBJ4 | | lia | reflexivity].
                           rewrite Ebj4, (rec_nth Fc _ q (incl false Fc q) 15) by lia.
                           replace (q + 16 + 15) with (q + 31) by lia. reflexivity. }
                         do 7 step.
                         rep_reg 12 (Z_to_bv 64 (rec_vid Fc q))
                           ltac:(unfold rec_vid, fb; rewrite vid_lor by apply byte_range; bits_eq).
                         do 5 step.
                         rewrite zx32_val, uns_mod32, swrap_add_mod32.
                         rewrite (Z.mod_small (incl false Fc q + -16) (2 ^ 32)) by lia.
                         let mm := cur_mem in rename mm into m7.
                         pose proof (ro_agree_munch_apart _ _ _ RO4 MUP ltac:(ro_tac)) as RO7.
                         eapply evt_cut.
                         { eapply HMM with (U := buf) (us := bj4).
                           - exact HBJ4.
                           - apply not_ro_apart; [lia | lia | unfold img_apart in *; lia].
                           - lia.
                           - rewrite !unsigned_lit by lia. lia.
                           - rewrite !unsigned_lit by lia. lia.
                           - rewrite unsigned_lit by lia. lia.
                           - exact RO7. }
                         intros ms' (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m8
                           & E8 & MU8 & WM8 & RO8 & HBJ8).
                         subst ms'.
                         rewrite ?unsigned_lit in MU8 by lia. rewrite ?unsigned_lit in HBJ8 by lia.
                         replace (buf + 16 - buf) with 16 in HBJ8 by lia.
                         replace (buf + 12 - buf) with 12 in HBJ8 by lia.
                         replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x2a8)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x2a8)%Z))
                           by (symmetry; apply ret_pc_even; [lia | reflexivity]).
                         xp_rw HPS MU8 WM8. xp_rw PH2 MU8 WM8. xp_stk ST4 MU8 WM8.
                         pose proof (mstl_transport _ _ _ _ _ _ _ _ _ MS4 MUP WMP ltac:(disj_tac) ltac:(disj_tac)) as MS7.
                         xp_mstl MS7 MU8 WM8.
                         pose proof (munch_ext _ _ _ _ _ MUT4 MU8 ltac:(out_tac)) as MUT8.
                         pose proof (wmono_trans rsegs _ _ _ WMT4 WM8) as WMT8.
                         step.
                         assert (KIND : kind false Fc cap q = KFit) by kind_tac.
                         assert (TAG : tagged false Fc q = true) by (unfold tagged; bool_dec; reflexivity).
                         apply evt_done. do 22 eexists. exists m8.
                         split; [right; left; split; [exact KIND|]|].
                         ***** unfold pos_of, vt_of, vid_of, is_fit, rec_len. rewrite KIND, TAG.
                               split; [reflexivity|].
                               split; [rewrite uns_mod32, swrap_add_mod32, Z.mod_small by lia; lia|].
                               split; [exact MS7|]. split; [exact HPS|].
                               eexists. split; [exact HBJ8|]. split.
                               { unfold mm_result, slice. rewrite upd_bytes_length; [lia|].
                                 rewrite length_firstn, length_skipn. lia. }
                               { unfold rec_bytes. rewrite TAG. cbv zeta. unfold rec_raw, mm_result, slice. rewrite Ebj4.
                                 apply mm_rec_z; [lia|]. rewrite length_firstn, length_skipn. lia. }
                         ***** split; [exact MUT8|]. split; [exact WMT8|]. split; [exact RO8|]. split; [exact ST4|].
                               exists ph2. exact PH2.
                     +++ if_true. untag_fin false Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
                 --- if_true. untag_fin false Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
        -- if_false.
           apply evt_done. do 22 eexists. exists m3.
           split; [right; right; right; split; [big_tac|]|].
           ++ split; [reflexivity|]. split; [exact MS3|]. split; [exact HPS | exact HBJ].
           ++ split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO3|]. split; [exact ST2|]. exists ph2. exact PH2.
    + pose proof (hw_range true Fc q 8) as RI. change (hw true Fc q 8) with (incl true Fc q) in RI.
      do 12 step.
      if_false.
      do 8 step.
      rep_reg 22 (Z_to_bv 64 (bv_swrap 32 (incl true Fc q))) ltac:(hw_eq).
      step.
      destruct (Z.eq_dec (incl true Fc q) 0) as [I0|I0].
      * assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl true Fc q))) (Z_to_bv 64 0) = true)
          by (rewrite eqb_swrap0 by lia; apply Z.eqb_eq; exact I0).
        rewrite C; cbv iota.
        do 2 step.
        destruct PH2e as [ph2 PH2].
        assert (KIND : kind true Fc cap q = KEmpty) by kind_tac.
        apply evt_done. do 22 eexists. exists m2.
        split; [right; right; left; split; [exact KIND|]|].
        -- split; [reflexivity|]. split; [exact MS2|]. split; [exact HPS | exact HBJ].
        -- split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2|]. split; [exact ST2|]. exists ph2. exact PH2.
      * assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl true Fc q))) (Z_to_bv 64 0) = false)
          by (rewrite eqb_swrap0 by lia; apply Z.eqb_neq; exact I0).
        rewrite C; cbv iota.
        do 11 step.
        if_false.
        do 7 step.
        rep_reg 13 (Z_to_bv 64 (orig true Fc q)) ltac:(hw_eq).
        assert (HB0' : ov_read_bytes rsegs m2 sp 1 = Some [nth (Z.to_nat (q + 0)) Fc (Z_to_bv 8 0)]).
        { rewrite <- HB0. f_equal. unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
        do 10 step.
        destruct PH2e as [ph2 PH2].
        pose proof (munch_refl [(ps, ps + 24)] m2) as MUP. pose proof (wmono_refl rsegs m2) as WMP.
        step.
        rewrite zx32_val, uns_swrap_mod32_0 by lia.
        assert (EI : bv_unsigned (Z_to_bv 64 (incl true Fc q)) = incl true Fc q) by (apply unsigned_lit; lia).
        assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
        step.
        let mm := cur_mem in rename mm into m3.
        pose proof (kp_mstl m2 m3 0 ps (keep_munch _ _ _ 0 ps MUP ltac:(lia) ltac:(lia)
                      ltac:(intros; cbn; split; [lia | exact I])) _ _ _ _ _ _ MS2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as MS3.
        pose proof (ro_agree_munch_apart _ _ _ RO2 MUP ltac:(ro_tac)) as RO3.
        clear MS2 RO2.
        destruct (Z_le_gt_dec (incl true Fc q) cap) as [FITp|BIGp].
        -- if_true.
           do 13 step.
           if_false.
           do 18 step.
           rep_reg 20 (Z_to_bv 64 (hw true Fc q 4)) ltac:(hw_eq).
           rep_reg 23 (Z_to_bv 64 (hw true Fc q 0)) ltac:(hw_eq).
           do 5 step.
           eapply evt_cut.
           { eapply HFR with (lo := lo) (b := b) (Fc := Fc) (p := q + 16) (pv := pv) (nx := nx)
               (junk := firstn (Z.to_nat (incl true Fc q)) bj).
             - rewrite unsigned_lit by lia. exact MS3.
             - rewrite unsigned_lit by lia. apply not_ro_apart; [lia | lia | exact HIH].
             - reflexivity.
             - rewrite unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. apply u8arr_take; [exact HBJ | lia].
             - rewrite !unsigned_lit by lia. apply not_ro_apart; [lia | lia | unfold img_apart in *; lia].
             - rewrite !unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. lia.
             - rewrite !unsigned_lit by lia. left. lia.
             - exact RO3.
             - exact ST2.
             - apply not_ro_hi; lia.
             - unfold FREAD_K. lia.
             - rewrite unsigned_lit by lia. lia.
             - exact HBL. }
           intros ms' (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m4
             & E4 & EA4 & MU4 & WM4 & RO4 & ST4 & BY4 & MS4).
           subst ms'.
           unfold fread_j, FREAD_K in EA4, MU4, BY4, MS4.
           rewrite ?unsigned_lit in EA4 by lia. rewrite ?unsigned_lit in MU4 by lia.
           rewrite ?unsigned_lit in BY4 by lia. rewrite ?unsigned_lit in MS4 by lia.
           unfold wz in EA4. subst a0b.
           replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x248)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x248)%Z))
             by (symmetry; apply ret_pc_even; [lia | reflexivity]).
           xp_rw HPS MU4 WM4. xp_rw PH2 MU4 WM4.
           pose proof (u8arr_after _ _ _ _ _ _ HBJ MU4 WM4 BY4 ltac:(rewrite length_firstn; lia)
                         ltac:(rewrite length_firstn, length_skipn; out_tac)) as HBJ4.
           pose proof (munch_ext _ _ _ _ _ MUT2 MU4 ltac:(out_tac)) as MUT4. clear MUT2.
           pose proof (wmono_trans rsegs _ _ _ WMT2 WM4) as WMT4. clear WMT2.
           clear HBJ MS3 RO3 ST2 MU4 WM4 MUP WMP.
           step.
           destruct (Z_lt_le_dec (Z.of_nat (length Fc) - (q + 16)) (incl true Fc q)) as [CF|FF].
           ++ rewrite Z.min_r in * by lia.
              assert (EJ : bv_unsigned (Z_to_bv 64 (Z.of_nat (length Fc) - (q + 16))) = Z.of_nat (length Fc) - (q + 16))
                by (apply unsigned_lit; lia).
              if_true.
              assert (KIND : kind true Fc cap q = KCutFit) by kind_tac.
              replace (q + 16 + (Z.of_nat (length Fc) - (q + 16))) with (Z.of_nat (length Fc)) in MS4 by lia.
              apply evt_done. do 22 eexists. exists m4.
              split; [left; split; [right; right; exact KIND|]|].
              ** unfold res_of, pos_of, hdr_kind. rewrite KIND. unfold flen.
                 split; [reflexivity|]. split; [exact MS4|]. split; [exact HPS|].
                 eexists. split; [exact HBJ4|].
                 rewrite length_app; repeat first [rewrite length_firstn | rewrite length_skipn]; lia.
              ** split; [exact MUT4|]. split; [exact WMT4|]. split; [exact RO4|]. split; [exact ST4|]. exists ph2. exact PH2.
           ++ rewrite Z.min_l in * by lia.
              if_false.
              match type of HBJ4 with u8arr _ _ _ ?L => remember L as bj4 eqn:Ebj4 end.
              assert (HBN4 : Z.of_nat (length bj4) = Z.max cap 1).
              { rewrite Ebj4, length_app; repeat first [rewrite length_firstn | rewrite length_skipn]; lia. }
              clear BY4.
              pose proof (munch_refl [(ps, ps + 24)] m4) as MUP. pose proof (wmono_refl rsegs m4) as WMP.
              do 4 step.
              rewrite ltu_swrap by lia.
              destruct (Z_lt_le_dec (incl true Fc q) 18) as [T18|T18].
              ** rewrite (proj2 (Z.ltb_lt _ _) T18). cbv iota.
                 untag_fin true Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
              ** rewrite (proj2 (Z.ltb_ge _ _) T18). cbv iota.
                 let mm := cur_mem in rename mm into m5.
                 assert (HR12 : ov_read_bytes rsegs m5 (wa (buf + 12)) 1 = Some [nth (Z.to_nat (q + 28)) Fc (Z_to_bv 8 0)]).
                 { eapply (u8arr_read rsegs m5 buf bj4 12); [exact HBJ4 | | lia | reflexivity].
                   rewrite Ebj4, (rec_nth Fc _ q (incl true Fc q) 12) by lia.
                   replace (q + 16 + 12) with (q + 28) by lia. reflexivity. }
                 assert (HR13 : ov_read_bytes rsegs m5 (wa (buf + 13)) 1 = Some [nth (Z.to_nat (q + 29)) Fc (Z_to_bv 8 0)]).
                 { eapply (u8arr_read rsegs m5 buf bj4 13); [exact HBJ4 | | lia | reflexivity].
                   rewrite Ebj4, (rec_nth Fc _ q (incl true Fc q) 13) by lia.
                   replace (q + 16 + 13) with (q + 29) by lia. reflexivity. }
                 assert (EZ28 : bv_unsigned (zxb (nth (Z.to_nat (q + 28)) Fc (Z_to_bv 8 0))) = fb Fc (q + 28))
                   by (rewrite zxb_val; reflexivity).
                 assert (EZ29 : bv_unsigned (zxb (nth (Z.to_nat (q + 29)) Fc (Z_to_bv 8 0))) = fb Fc (q + 29))
                   by (rewrite zxb_val; reflexivity).
                 do 3 step.
                 destruct (Z.eq_dec (fb Fc (q + 28)) 129) as [B28|B28].
                 --- if_false.
                     do 2 step.
                     destruct (Z.eq_dec (fb Fc (q + 29)) 0) as [B29|B29].
                     +++ if_false.
                         do 2 step.
                         let mm := cur_mem in rename mm into m6.
                         assert (HR14 : ov_read_bytes rsegs m6 (wa (buf + 14)) 1 = Some [nth (Z.to_nat (q + 30)) Fc (Z_to_bv 8 0)]).
                         { eapply (u8arr_read rsegs m6 buf bj4 14); [exact HBJ4 | | lia | reflexivity].
                           rewrite Ebj4, (rec_nth Fc _ q (incl true Fc q) 14) by lia.
                           replace (q + 16 + 14) with (q + 30) by lia. reflexivity. }
                         assert (HR15 : ov_read_bytes rsegs m6 (wa (buf + 15)) 1 = Some [nth (Z.to_nat (q + 31)) Fc (Z_to_bv 8 0)]).
                         { eapply (u8arr_read rsegs m6 buf bj4 15); [exact HBJ4 | | lia | reflexivity].
                           rewrite Ebj4, (rec_nth Fc _ q (incl true Fc q) 15) by lia.
                           replace (q + 16 + 15) with (q + 31) by lia. reflexivity. }
                         do 7 step.
                         rep_reg 12 (Z_to_bv 64 (rec_vid Fc q))
                           ltac:(unfold rec_vid, fb; rewrite vid_lor by apply byte_range; bits_eq).
                         do 5 step.
                         rewrite zx32_val, uns_mod32, swrap_add_mod32.
                         rewrite (Z.mod_small (incl true Fc q + -16) (2 ^ 32)) by lia.
                         let mm := cur_mem in rename mm into m7.
                         pose proof (ro_agree_munch_apart _ _ _ RO4 MUP ltac:(ro_tac)) as RO7.
                         eapply evt_cut.
                         { eapply HMM with (U := buf) (us := bj4).
                           - exact HBJ4.
                           - apply not_ro_apart; [lia | lia | unfold img_apart in *; lia].
                           - lia.
                           - rewrite !unsigned_lit by lia. lia.
                           - rewrite !unsigned_lit by lia. lia.
                           - rewrite unsigned_lit by lia. lia.
                           - exact RO7. }
                         intros ms' (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m8
                           & E8 & MU8 & WM8 & RO8 & HBJ8).
                         subst ms'.
                         rewrite ?unsigned_lit in MU8 by lia. rewrite ?unsigned_lit in HBJ8 by lia.
                         replace (buf + 16 - buf) with 16 in HBJ8 by lia.
                         replace (buf + 12 - buf) with 12 in HBJ8 by lia.
                         replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x2a8)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x2a8)%Z))
                           by (symmetry; apply ret_pc_even; [lia | reflexivity]).
                         xp_rw HPS MU8 WM8. xp_rw PH2 MU8 WM8. xp_stk ST4 MU8 WM8.
                         pose proof (mstl_transport _ _ _ _ _ _ _ _ _ MS4 MUP WMP ltac:(disj_tac) ltac:(disj_tac)) as MS7.
                         xp_mstl MS7 MU8 WM8.
                         pose proof (munch_ext _ _ _ _ _ MUT4 MU8 ltac:(out_tac)) as MUT8.
                         pose proof (wmono_trans rsegs _ _ _ WMT4 WM8) as WMT8.
                         step.
                         assert (KIND : kind true Fc cap q = KFit) by kind_tac.
                         assert (TAG : tagged true Fc q = true) by (unfold tagged; bool_dec; reflexivity).
                         apply evt_done. do 22 eexists. exists m8.
                         split; [right; left; split; [exact KIND|]|].
                         ***** unfold pos_of, vt_of, vid_of, is_fit, rec_len. rewrite KIND, TAG.
                               split; [reflexivity|].
                               split; [rewrite uns_mod32, swrap_add_mod32, Z.mod_small by lia; lia|].
                               split; [exact MS7|]. split; [exact HPS|].
                               eexists. split; [exact HBJ8|]. split.
                               { unfold mm_result, slice. rewrite upd_bytes_length; [lia|].
                                 rewrite length_firstn, length_skipn. lia. }
                               { unfold rec_bytes. rewrite TAG. cbv zeta. unfold rec_raw, mm_result, slice. rewrite Ebj4.
                                 apply mm_rec_z; [lia|]. rewrite length_firstn, length_skipn. lia. }
                         ***** split; [exact MUT8|]. split; [exact WMT8|]. split; [exact RO8|]. split; [exact ST4|].
                               exists ph2. exact PH2.
                     +++ if_true. untag_fin true Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
                 --- if_true. untag_fin true Fc cap q bj4 MS4 MUP WMP RO4 HPS HBJ4 Ebj4 MUT4 WMT4 ST4 PH2 ph2.
        -- if_false.
           apply evt_done. do 22 eexists. exists m3.
           split; [right; right; right; split; [big_tac|]|].
           ++ split; [reflexivity|]. split; [exact MS3|]. split; [exact HPS | exact HBJ].
           ++ split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO3|]. split; [exact ST2|]. exists ph2. exact PH2.
  Unshelve. all: try exact (Z_to_bv 64 0).
Qed.

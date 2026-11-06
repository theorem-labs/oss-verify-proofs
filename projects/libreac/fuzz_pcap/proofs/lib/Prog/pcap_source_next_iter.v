From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fread_c fread_ro_c memmove_c memmove_ro_c
  pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib pcap_source_next_ep pcap_source_next_body
  pcap_source_next_skip.
Import ListNotations.
Open Scope Z_scope.

Lemma psn_iter : fread_ro_contract -> memmove_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ps buf cap ts h swz b q lo : Z) (sw : bool) (Fc : list byte) (pv nx lolc lvt lvid tsv : word) (bj ph pad : list byte)
         (sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o : word),
    s0 = wz ts -> s1 = wz ps -> s2 = wz buf -> s4 = wz cap -> s7 = wz 16 -> s8 = wz 0xff00 -> a3 = wz h ->
    sw = (swz =? 1) ->
    bv_unsigned sp = bv_unsigned sp0 - 96 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 16 ph] ->
    rw_cells rsegs m (bv_unsigned sp + 16)
      [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 5632 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    bv_unsigned sp0 <= ps -> rw_cells rsegs m ps (ps_cells (wz h) (wz swz) lolc lvt lvid pad) ->
    (swz = 0 \/ swz = 1) ->
    mstl m h b Fc q pv nx -> img_apart h 1304 -> h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    Z.of_nat (length Fc) < 2 ^ 26 ->
    0 <= cap < 2 ^ 64 -> 4096 <= buf -> u8arr rsegs m buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
    img_apart buf (Z.max cap 1) -> buf + Z.max cap 1 <= lo ->
    (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) -> (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) ->
    (ts <> 0 -> bv_unsigned sp0 <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs m ts [C8 tsv]) ->
    0 <= ts < 2 ^ 64 ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' t3' t4' t5' t6' : word) m',
         ((exit_kind (kind sw Fc cap q) = true /\
           ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0o s1o (wz (res_of sw Fc cap q)) a1' a2' a3' a4' a5' a6' a7'
                         s2o s3o s4o s5o s6o s7o s8o s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (pos_of sw Fc cap q) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (if hdr_kind (kind sw Fc cap q) then wz (orig sw Fc q) else lolc)
                                   (vt_of sw Fc cap q lvt) (vid_of sw Fc cap q lvid) pad) /\
           (exists bj', u8arr rsegs m' buf bj' /\ length bj' = length bj /\
              (is_fit (kind sw Fc cap q) = true -> firstn (Z.to_nat (incl sw Fc q)) bj' = rec_bytes sw Fc q)) /\
           (ts <> 0 -> rw_cells rsegs m' ts [C8 (ts_of sw Fc cap q tsv)])) \/
          (kind sw Fc cap q = KEmpty /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' (wz h) a4' a5' a6' a7'
                         s2 s3' s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (q + 16) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) lolc lvt lvid pad) /\ u8arr rsegs m' buf bj /\
           (ts <> 0 -> rw_cells rsegs m' ts [C8 tsv])) \/
          (big_kind (kind sw Fc cap q) = true /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 (wz (-1)) s4 s5' (wz (bv_swrap 32 (incl sw Fc q))) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x134)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (q + 16) pv nx /\
           rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (wz (orig sw Fc q)) lvt lvid pad) /\ u8arr rsegs m' buf bj /\
           (ts <> 0 -> rw_cells rsegs m' ts [C8 tsv]))) /\
         munch [(bv_unsigned sp - 5632, bv_unsigned sp + 16); (ps, ps + 24); (buf, buf + Z.max cap 1); (ts, ts + (if ts =? 0 then 0 else 8));
                (h, h + 1304)] m m' /\
         wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (exists ph', rw_cells rsegs m' (bv_unsigned sp) [CB 16 ph']) /\
         rw_cells rsegs m' (bv_unsigned sp + 16)
           [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HFR HMM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ps buf cap ts h swz b q lo sw Fc pv nx lolc lvt lvid tsv bj ph pad sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o
    E0 E1 E2 E4 E7 E8 EA3 ESW Hsp HPH HSV ST LO HLO HPS0 HPS HSW HMS HIH HHL HBL HN26 HCAP HB4K HBJ HBN HIB HBL2
    HBH HBB HTS HTR RO.
  pose proof (zr_word sp0) as Rsp0. unfold inr64 in Rsp0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize ps_cells Nat.add] in HPR.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  eapply evt_cut.
  { eapply (psn_body HFR HMM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m ps buf cap h swz b q lo sw Fc pv nx lolc lvt lvid bj ph pad); try eassumption; lia. }
  intros ms' (ra' & t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' & s6' & s7'
    & t3' & t4' & t5' & t6' & m' & DISJ & MU & WM & RO' & ST' & (ph' & PH')).
  xp_rw HSV MU WM.
  assert (HTS' : ts <> 0 -> rw_cells rsegs m' ts [C8 tsv]).
  { intros T. destruct (HTS T) as (T1 & T2 & C).
    pose proof (rw_cells_bound rsegs _ _ _ C) as CB. cbn [cells_size csize Nat.add] in CB.
    exact (rw_cells_transport rsegs _ _ _ _ _ C MU WM ltac:(disj_tac)). }
  assert (MUW : munch [(bv_unsigned sp - 5632, bv_unsigned sp + 16); (ps, ps + 24); (buf, buf + Z.max cap 1); (ts, ts + (if ts =? 0 then 0 else 8));
                (h, h + 1304)] m m') by (eapply munch_weaken; [| exact MU]; unfold sub_fp; out_tac).
  destruct DISJ as [(KA & -> & MSa & HPSa & (bja & HBJa & LBa))|[(KF & -> & S3M & MSf & HPSf & (bjf & HBJf & LBf & FBf))|
                    [(KB & -> & MSb & HPSb & HBJb)|(KC & -> & MSc & HPSc & HBJc)]]].
  - eapply evt_cut; [eapply psn_epi; [exact Hsp | exact HSV]|].
    intros ms'' ->. apply evt_done. do 19 eexists. exists m'.
    assert (NF : is_fit (kind sw Fc cap q) = false) by (destruct KA as [K|[K|K]]; rewrite K; reflexivity).
    split; [left|].
    + split; [destruct KA as [K|[K|K]]; rewrite K; reflexivity|]. split; [reflexivity|]. split; [exact MSa|].
      unfold vt_of, vid_of, ts_of. rewrite NF. split; [exact HPSa|]. split; [|exact HTS'].
      exists bja. split; [exact HBJa|]. split; [exact LBa|]. intros C. discriminate C.
    + split; [exact MUW|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|]. split; [exists ph'; exact PH'|].
      exact HSV.
  - pose proof (hw_range sw Fc q 4) as R4. pose proof (hw_range sw Fc q 0) as R0.
    assert (RL : 0 <= rec_len sw Fc q < 2 ^ 32).
    { pose proof (hw_range sw Fc q 8) as R8. unfold rec_len, incl in *. destruct (tagged sw Fc q); lia. }
    eapply evt_cut.
    { eapply (psn_ts _ _ _ _ _ _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' ts (hw sw Fc q 4) (hw sw Fc q 0)
                (rec_len sw Fc q) tsv); try reflexivity; try eassumption; lia. }
    intros ms'' (a0'' & a1'' & s4'' & s6'' & s7'' & m'' & -> & MUt & WMt & Z0 & HTSt).
    destruct (Z.eq_dec ts 0) as [T0|T0];
      [ specialize (Z0 T0); subst m'; clear MUt WMt;
        pose proof (munch_refl [] m'') as MUt; pose proof (wmono_refl rsegs m'') as WMt
      | clear Z0; destruct (HTS T0) as (TS1 & TS2 & _); assert (TSN : (if ts =? 0 then 0 else 8) = 8) by (rewrite (proj2 (Z.eqb_neq ts 0) T0); reflexivity) ].
    all: xp_rw HSV MUt WMt.
    all: eapply evt_cut; [eapply psn_epi; [exact Hsp | exact HSV]|].
    all: intros ms3 ->; apply evt_done; do 19 eexists; exists m''; split; [left|].
    1,3: unfold res_of, hdr_kind, ts_of, is_fit; rewrite KF;
      split; [reflexivity|]; split; [reflexivity|];
      split; [exact (mstl_transport _ _ _ _ _ _ _ _ _ MSf MUt WMt ltac:(disj_tac) ltac:(disj_tac))|];
      split; [exact (rw_cells_transport rsegs _ _ _ _ _ HPSf MUt WMt ltac:(unfold ps_cells; disj_tac))|];
      split; [|exact HTSt];
      exists bjf; split; [exact (u8arr_transport rsegs _ _ _ _ _ HBJf MUt WMt ltac:(disj_tac))|];
      split; [exact LBf|]; intros _; exact FBf.
    all: split; [exact (munch_ext _ _ _ _ _ MUW MUt ltac:(out_tac))|];
      split; [exact (wmono_trans rsegs _ _ _ WM WMt)|];
      split; [first [assumption | exact (ro_agree_munch_apart _ _ _ RO' MUt ltac:(ro_tac))]|];
      split; [xp_stk ST' MUt WMt; exact ST'|];
      split; [exists ph'; xp_rw PH' MUt WMt; exact PH'|]; exact HSV.
  - apply evt_done. do 19 eexists. exists m'.
    split; [right; left; split; [exact KB|]|].
    + split; [reflexivity|]. split; [exact MSb|]. split; [exact HPSb|]. split; [exact HBJb | exact HTS'].
    + split; [exact MUW|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|]. split; [exists ph'; exact PH'|].
      exact HSV.
  - apply evt_done. do 19 eexists. exists m'.
    split; [right; right; split; [exact KC|]|].
    + split; [reflexivity|]. split; [exact MSc|]. split; [exact HPSc|]. split; [exact HBJc | exact HTS'].
    + split; [exact MUW|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|]. split; [exists ph'; exact PH'|].
      exact HSV.
  Unshelve. all: try exact (Z_to_bv 64 0).
Qed.

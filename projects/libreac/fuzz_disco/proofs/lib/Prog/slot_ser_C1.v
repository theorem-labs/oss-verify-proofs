From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c jtok_is_c strlen_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J slot_ser_P.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition W_TAIL (lo X : Z) : list (Z * Z) :=
  [(lo, X); (X, X + 16); (X + 160, X + 168); (X + 184, X + 200); (X + 216, X + 232); (X + 920, X + 2488)].

Lemma task_by : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> exists b, mrd rsegs m (wa x) = Some b) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TM MU H. eapply task_of; [exact TM | exact MU |]. intros x Hx O.
  destruct (H x Hx O) as [b Hb]. exact (tsk_of_mrd m x b TM Hx Hb).
Qed.

Lemma cb_mrd : forall m A n bs x, rw_cells rsegs m A [CB n bs] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof. intros m A n bs x H Hx. apply ser_cb in H as (L & B & _). eapply bytes_at_mrd; [exact B | rewrite L; exact Hx]. Qed.

Lemma stk_mrd : forall m lo hi x, stk rsegs m lo hi -> lo <= x < hi -> exists b, mrd rsegs m (wa x) = Some b.
Proof. intros m lo hi x (_ & _ & H) Hx. exact (proj2 (H x Hx)). Qed.

Lemma ser_tail : strlen_contract -> json_scalar_contract -> jtok_is_contract -> reac_box_name_contract ->
  snprintf_stk_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
    (X lo buf cap now i p : Z) (T slack j0 j160 j184 j192 j216 j224 jage jwid jtok jk jo jv jscr : list byte),
  sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s1 = Z_to_bv 64 i -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 buf ->
  s4 = Z_to_bv 64 (Z.of_nat (length (tj_text T now))) -> s5 = Z_to_bv 64 cap -> s7 = Z_to_bv 64 p ->
  s8 = Z_to_bv 64 (X + 2336) -> s11 = Z_to_bv 64 now ->
  0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 < buf ->
  length T = 400%nat -> disco_table_c.table_ok T -> Z.of_nat (length (tj_text T now)) < cap < 2 ^ 63 ->
  bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) ->
  bytes_at rsegs m (buf + Z.of_nat (length (tj_text T now)) + 1) slack ->
  (- (buf + Z.of_nat (length (tj_text T now)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  buf + Z.of_nat (length (tj_text T now)) + 1 + Z.of_nat (length slack) <= lo ->
  rw_cells rsegs m X [CB 16 j0] -> rw_cells rsegs m (X + 160) [CB 8 j160] -> rw_cells rsegs m (X + 184) [CB 8 j184] ->
  rw_cells rsegs m (X + 192) [CB 8 j192] -> rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 W0X0)] ->
  rw_cells rsegs m (X + 216) [CB 8 j216] -> rw_cells rsegs m (X + 224) [CB 8 j224] ->
  rw_cells rsegs m (X + 512) [CB 400 T] ->
  rw_cells rsegs m (X + 920) [CB 24 jage] -> rw_cells rsegs m (X + 944) [CB 24 jwid] ->
  rw_cells rsegs m (X + 968) [CB 24 jtok] -> rw_cells rsegs m (X + 992) [CB 32 jk] ->
  rw_cells rsegs m (X + 1024) [CB 1296 jo] -> rw_cells rsegs m (X + 2320) [CB 24 jv] ->
  rw_cells rsegs m (X + 2344) [CB 144 jscr] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> bytes_at rsegs m BN_TS bn_table ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo X -> lo + TJ_K <= X -> IMG_END <= lo ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s9' s10' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte)
                       (j0' j192' j216' j224' jw' : list byte),
       ms' = MS (mkR (Z_to_bv 64 SER_FREE_RET) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 buf)
                     a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5' s6' s7 s8 s9' s10' s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 SER_FREE) fc' None m' (seg_rom rsegs) /\
       frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
       munch (W_TAIL lo X) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
       stk rsegs m' lo X /\
       rw_cells rsegs m' X [CB 16 j0'] /\ rw_cells rsegs m' (X + 160) [C8 s1] /\ rw_cells rsegs m' (X + 184) [C8 s7] /\
       rw_cells rsegs m' (X + 192) [CB 8 j192'] /\ rw_cells rsegs m' (X + 216) [CB 8 j216'] /\
       rw_cells rsegs m' (X + 224) [CB 8 j224'] /\ rw_cells rsegs m' (X + 920) [CB 1568 jw'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SER_R9) fc None m (seg_rom rsegs)).
Proof.
  intros SLC JS JT BNC SNK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m canary X lo buf cap now i p T slack j0 j160 j184 j192 j216 j224 jage jwid jtok jk jo jv jscr
    Esp Es0 Es1 Es2 Es3 Es4 Es5 Es7 Es8 Es11 HX0 HX16 HX1 Hnow Hb LT TOK Hcap BB BS HSL HSX
    C0 C160 C184 C192 C200 C208 C216 C224 CT CAGE CWID CTOK CK CO CV CSCR JTB BN GG GW FC MI TM ST HLO HI.
  change TJ_K with 6224 in HLO. unfold IMG_END in HI.
  pose proof (ser_tj_ok T LT TOK) as [TOK' WF].
  destruct (F1_1_text_shape box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as (_ & N0 & NL & L2).
  pose proof (ser_text_g33 box_tok (tj_entries T) now ser_tok_ok WF Hnow) as G33.
  destruct (F1_2_json_read_table box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as (os & JR & _).
  change (table_json_text box_tok (tj_entries T) now) with (tj_text T now) in N0, NL, L2, G33, JR.
  assert (Hc : 0 <= Z.of_nat (length (tj_entries T)) <= 8).
  { rewrite ser_tj_len. destruct TOK as (T1 & _). unfold tbl_T1 in T1. lia. }
  assert (LBB : Z.of_nat (length (pf_bytes (tj_text T now ++ [0]))) = Z.of_nat (length (tj_text T now)) + 1)
    by (rewrite length_pf_bytes, length_app; cbn [length]; lia).
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity. assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (HBN : BN_TS = 0x1fe40) by reflexivity. assert (LBN : Z.of_nat (length bn_table) = 24) by reflexivity.
  assert (HGG : GOT_GUARD = 0x1fee8) by reflexivity. assert (HGW : GUARD = 0x514d0) by reflexivity.
  pose proof (munch_refl (W_TAIL lo X) m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold W_TAIL in MU.
  subst sp s0 s1 s2 s3 s4 s5 s7 s8 s11.
  eapply evt_cut.
  { eapply (slot_R9 SLC) with (X := X) (buf := buf) (cap := cap) (i := i) (p := p) (B := tj_text T now)
      (slack := slack) (j160 := j160) (j184 := j184);
      first [ reflexivity | exact N0 | exact NL | exact L2 | exact G33 | eassumption | lia ]. }
  intros ms' (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m3 &
              E3 & MU3 & WM3 & MI3 & C160' & C184'). subst ms'.
  assert (TM3 : MemNorm.task_mem rsegs m3).
  { eapply task_by; [exact TM | exact MU3 |]. intros x Hx O. cbn [outside] in O.
    assert (D : X + 160 <= x < X + 168 \/ X + 184 <= x < X + 192) by lia.
    destruct D as [D|D]; [exact (cb_mrd m _ _ _ x C160 ltac:(lia)) | exact (cb_mrd m _ _ _ x C184 ltac:(lia))]. }
  transport_after_call rsegs m m3 MU3 WM3. clear MU3 WM3 MI.
  pose proof (ser_J JS JT) as SJ. unfold ser_J_spec in SJ.
  eapply evt_cut.
  { eapply SJ with (X := X) (lo := lo) (buf := buf) (now := now) (count := Z.of_nat (length (tj_entries T)))
      (B := tj_text T now) (os := os) (j192 := j192) (j216 := j216) (j224 := j224) (jk := jk) (jo := jo) (jv := jv);
      first [ reflexivity | exact G33 | exact JR | eassumption | lia | (unfold JSON_SCALAR_K; lia) ]. }
  intros ms' (ra4 & t04 & t14 & t24 & s14 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & s54 & s74 & s94 & s104 &
              t34 & t44 & t54 & t64 & m4 & vpad & j192' & j216' & j224' & jk' & jo' & jv' &
              E4 & MU4 & WM4 & MI4 & ST4 & C192' & C216' & C224' & CK' & COB & COR & CV' & LV). subst ms'.
  assert (TM4 : MemNorm.task_mem rsegs m4).
  { eapply task_by; [exact TM3 | exact MU4 |]. intros x Hx O. cbn [outside] in O.
    assert (D : lo <= x < X \/ X + 192 <= x < X + 200 \/ X + 216 <= x < X + 224 \/ X + 224 <= x < X + 232 \/
                X + 992 <= x < X + 1024 \/ X + 1024 <= x < X + 2320 \/ X + 2320 <= x < X + 2344) by lia.
    destruct D as [D|[D|[D|[D|[D|[D|D]]]]]];
      [ exact (stk_mrd m3 lo X x ST D) | exact (cb_mrd m3 _ _ _ x C192 ltac:(lia))
      | exact (cb_mrd m3 _ _ _ x C216 ltac:(lia)) | exact (cb_mrd m3 _ _ _ x C224 ltac:(lia))
      | exact (cb_mrd m3 _ _ _ x CK ltac:(lia)) | exact (cb_mrd m3 _ _ _ x CO ltac:(lia))
      | exact (cb_mrd m3 _ _ _ x CV ltac:(lia)) ]. }
  transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
  pose proof (ser_P3 BNC SNK JT) as SP3. unfold ser_P3_spec in SP3.
  eapply evt_cut.
  { eapply SP3 with (X := X) (lo := lo) (buf := buf) (now := now) (i := i) (p := p)
      (count := Z.of_nat (length (tj_entries T))) (T := T) (os := os) (vpad := vpad) (j0 := j0) (jage := jage)
      (jwid := jwid) (jtok := jtok) (jused := jk') (jnm := jv') (jscr := jscr) (canary := canary);
      first [ reflexivity | exact JR | eassumption | lia | (unfold SNPRINTF_K; lia) | (unfold IMG_END; lia) ]. }
  intros ms' (t05 & t15 & t25 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s45 & s55 & s65 & s95 & s105 &
              t35 & t45 & t55 & t65 & F5 & fc5 & m5 & j0' & jage' & jwid' & jtok' & jused' & jnm' & jscr' &
              E5 & FC5 & FK5 & MU5 & WM5 & MI5 & TM5 & ST5 & C0' & CAGE' & CWID' & CTOK' & CUSED' & CNM' & CSCR').
  subst ms'.
  transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
  assert (W1 : rw_cells rsegs m5 (X + 1024) [CB 1296 (objs_bytes buf vpad os ++ jo')]).
  { apply (ser_join m5 (X + 1024) (X + 1024 + 144 * Z.of_nat (length (tj_entries T)))
             (Z.to_nat (144 * Z.of_nat (length (tj_entries T)))) (Z.to_nat (1296 - 144 * Z.of_nat (length (tj_entries T))))
             1296); [lia | lia | exact COB | exact COR]. }
  assert (W6 : rw_cells rsegs m5 (X + 2320) [CB 168 (jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 2320) (X + 2344) 24 144 168); [lia | lia | exact CNM' | exact CSCR']).
  assert (W5 : rw_cells rsegs m5 (X + 1024) [CB 1464 ((objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 1024) (X + 2320) 1296 168 1464); [lia | lia | exact W1 | exact W6]).
  assert (W4 : rw_cells rsegs m5 (X + 992) [CB 1496 (jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 992) (X + 1024) 32 1464 1496); [lia | lia | exact CUSED' | exact W5]).
  assert (W3 : rw_cells rsegs m5 (X + 968)
                 [CB 1520 (jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 968) (X + 992) 24 1496 1520); [lia | lia | exact CTOK' | exact W4]).
  assert (W2 : rw_cells rsegs m5 (X + 944)
                 [CB 1544 (jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 944) (X + 968) 24 1520 1544); [lia | lia | exact CWID' | exact W3]).
  assert (W0 : rw_cells rsegs m5 (X + 920)
                 [CB 1568 (jage' ++ jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (ser_join m5 (X + 920) (X + 944) 24 1544 1568); [lia | lia | exact CAGE' | exact W2]).
  apply evt_done. do 19 eexists.
  exists F5, fc5, m5, j0', j192', j216', j224',
    (jage' ++ jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr').
  split; [reflexivity|]. split; [exact FC5|]. split; [exact FK5|]. split; [unfold W_TAIL; exact MU|].
  split; [exact WM|]. split; [exact MI5|]. split; [exact TM5|]. split; [exact ST5|]. split; [exact C0'|].
  split; [exact C160'|]. split; [exact C184'|]. split; [exact C192'|]. split; [exact C216'|].
  split; [exact C224'|exact W0].
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs slot_ser_pure slot_ser.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c strlen_c disco_table_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser_pure uslot_ser_tokb uslot_ser.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_Pq.
Import ListNotations.
Open Scope Z_scope.

Definition uW_TAIL (lo X : Z) : list (Z * Z) :=
  [(lo, X); (X, X + 16); (X + 208, X + 216); (X + 232, X + 256); (X + 952, X + 2520)].

Lemma ubytes_mrd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (Ha & Hl & H) Hx.
  replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia. rewrite H by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma ucb_mrd : forall m A n bs x, rw_cells rsegs m A [CB n bs] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof. intros m A n bs x H Hx. apply user_cb in H as (L & B & _). eapply ubytes_mrd; [exact B | rewrite L; exact Hx]. Qed.

Lemma ustk_mrd : forall m lo hi x, stk rsegs m lo hi -> lo <= x < hi -> exists b, mrd rsegs m (wa x) = Some b.
Proof. intros m lo hi x (_ & _ & H) Hx. exact (proj2 (H x Hx)). Qed.

Lemma utask_by : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> exists b, mrd rsegs m (wa x) = Some b) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TM MU H. eapply utask_of; [exact TM | exact MU |]. intros x Hx O.
  destruct (H x Hx O) as [b Hb]. exact (utsk_of_mrd m x b TM Hx Hb).
Qed.

Lemma user_tail : strlen_contract -> user_J_spec -> user_P3_spec ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
    (X lo buf cap now : Z) (T slack j0 j208 j232 jage jwid jtok jk jo jv jscr : list byte),
  sp = Z_to_bv 64 X -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 buf ->
  s4 = Z_to_bv 64 (Z.of_nat (length (tj_text T now))) -> s5 = Z_to_bv 64 cap ->
  s8 = Z_to_bv 64 (X + 2368) -> s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 1 ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 < buf ->
  length T = 400%nat -> U.Prog.disco_table_c.table_ok T -> Z.of_nat (length (tj_text T now)) < cap < 2 ^ 31 ->
  bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) ->
  bytes_at rsegs m (buf + Z.of_nat (length (tj_text T now)) + 1) slack ->
  (- (buf + Z.of_nat (length (tj_text T now)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  buf + Z.of_nat (length (tj_text T now)) + 1 + Z.of_nat (length slack) <= lo ->
  rw_cells rsegs m X [CB 16 j0] -> rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] ->
  rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] -> rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] -> rw_cells rsegs m (X + 208) [CB 8 j208] ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 232) [CB 24 j232] -> rw_cells rsegs m (X + 544) [CB 400 T] ->
  rw_cells rsegs m (X + 952) [CB 24 jage] -> rw_cells rsegs m (X + 976) [CB 24 jwid] ->
  rw_cells rsegs m (X + 1000) [CB 24 jtok] -> rw_cells rsegs m (X + 1024) [CB 32 jk] ->
  rw_cells rsegs m (X + 1056) [CB 1296 jo] -> rw_cells rsegs m (X + 2352) [CB 24 jv] ->
  rw_cells rsegs m (X + 2376) [CB 144 jscr] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> bytes_at rsegs m BN_TS bn_table ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo X ->
  lo + U.Prog.reac_disco_table_json_c.TJ_K <= X -> IMG_END <= lo ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte)
                       (j0' j208' j232' jw' : list byte),
       ms' = MS (mkR (Z_to_bv 64 uSER_FREE_RET) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 buf)
                     a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5' s6' s7' s8 s9' s10 s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 uSER_FREE) fc' None m' (seg_rom rsegs) /\
       frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
       munch (uW_TAIL lo X) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
       stk rsegs m' lo X /\
       rw_cells rsegs m' X [CB 16 j0'] /\ rw_cells rsegs m' (X + 208) [CB 8 j208'] /\
       rw_cells rsegs m' (X + 232) [CB 24 j232'] /\ rw_cells rsegs m' (X + 952) [CB 1568 jw'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uSER_R9) fc None m (seg_rom rsegs)).
Proof.
  intros SLC SJ SP3 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m canary X lo buf cap now T slack j0 j208 j232 jage jwid jtok jk jo jv jscr
    Esp Es2 Es3 Es4 Es5 Es8 Es10 Es11 HX0 HX16 HX1 Hnow Hb LT TOK Hcap BB BS HSL HSX
    C0 C176 C184 C192 C200 C208 C216 C224 C232 CT CAGE CWID CTOK CK CO CV CSCR JTB BN GG GW FC MI TM ST HLO HI.
  change U.Prog.reac_disco_table_json_c.TJ_K with 6240 in HLO. unfold IMG_END in HI.
  pose proof (user_tj_ok T LT TOK) as [TOK' WF].
  destruct (F1_1_text_shape box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as (_ & N0 & NL & L2).
  pose proof (ser_text_g33 box_tok (tj_entries T) now ser_tok_ok WF Hnow) as G33.
  destruct (F1_2_json_read_table box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as (os & JR & _).
  change (table_json_text box_tok (tj_entries T) now) with (tj_text T now) in N0, NL, L2, G33, JR.
  assert (Hc : 0 <= Z.of_nat (length (tj_entries T)) <= 8).
  { rewrite user_tj_len. destruct TOK as (T1 & _). unfold tbl_T1 in T1. lia. }
  assert (LBB : Z.of_nat (length (pf_bytes (tj_text T now ++ [0]))) = Z.of_nat (length (tj_text T now)) + 1)
    by (rewrite ulength_pf_bytes, length_app; cbn [length]; lia).
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity. assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (HBN : BN_TS = 0x205f8) by reflexivity. assert (LBN : Z.of_nat (length bn_table) = 24) by reflexivity.
  assert (HGG : GOT_GUARD = 0x206a0) by reflexivity. assert (HGW : GUARD = 0x51c90) by reflexivity.
  pose proof (munch_refl (uW_TAIL lo X) m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold uW_TAIL in MU.
  subst sp s2 s3 s4 s5 s8 s10 s11.
  eapply evt_cut.
  { eapply (uslot_R9 SLC) with (buf := buf) (cap := cap) (B := tj_text T now) (slack := slack);
      first [ reflexivity | exact N0 | exact NL | exact L2 | exact G33 | eassumption | lia ]. }
  intros ms' (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m3 &
              E3 & MU3 & WM3 & MI3). subst ms'.
  assert (TM3 : MemNorm.task_mem rsegs m3).
  { eapply utask_by; [exact TM | exact MU3 |]. intros x Hx O. exfalso. apply O. cbn [outside]. exact I. }
  transport_after_call rsegs m m3 MU3 WM3. clear MU3 WM3 MI.
  eapply evt_cut.
  { eapply SJ with (X := X) (lo := lo) (buf := buf) (count := Z.of_nat (length (tj_entries T)))
      (B := tj_text T now) (os := os) (j208 := j208) (j232 := j232) (jk := jk) (jo := jo) (jv := jv);
      first [ reflexivity | exact G33 | exact JR | eassumption | lia | (unfold JSON_SCALAR_K; lia)
            | (unfold IMG_END; lia) ]. }
  intros ms' (ra4 & t04 & t14 & t24 & s04 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & s54 & s64 & s74 &
              t34 & t44 & t54 & t64 & m4 & vpad & j208' & j232' & jk' & jo' & jv' &
              E4 & MU4 & WM4 & MI4 & ST4 & C208' & C232' & CK' & COB & COR & CV' & LV). subst ms'.
  assert (TM4 : MemNorm.task_mem rsegs m4).
  { eapply utask_by; [exact TM3 | exact MU4 |]. intros x Hx O. cbn [outside] in O.
    assert (D : lo <= x < X \/ X + 208 <= x < X + 216 \/ X + 232 <= x < X + 256 \/
                X + 1024 <= x < X + 1056 \/ X + 1056 <= x < X + 2352 \/ X + 2352 <= x < X + 2376) by lia.
    destruct D as [D|[D|[D|[D|[D|D]]]]];
      [ exact (ustk_mrd m3 lo X x ST D) | exact (ucb_mrd m3 _ _ _ x C208 ltac:(lia))
      | exact (ucb_mrd m3 _ _ _ x C232 ltac:(lia)) | exact (ucb_mrd m3 _ _ _ x CK ltac:(lia))
      | exact (ucb_mrd m3 _ _ _ x CO ltac:(lia)) | exact (ucb_mrd m3 _ _ _ x CV ltac:(lia)) ]. }
  transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
  eapply evt_cut.
  { eapply SP3 with (X := X) (lo := lo) (buf := buf) (now := now) (count := Z.of_nat (length (tj_entries T)))
      (T := T) (os := os) (vpad := vpad) (j0 := j0) (jage := jage) (jwid := jwid) (jtok := jtok) (jused := jk')
      (jnm := jv') (jscr := jscr) (canary := canary);
      first [ reflexivity | exact JR | eassumption | lia | (unfold SNPRINTF_K; lia) | (unfold IMG_END; lia) ]. }
  intros ms' (t05 & t15 & t25 & s05 & s15 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s45 & s55 & s65 & s75 & s95 &
              t35 & t45 & t55 & t65 & F5 & fc5 & m5 & j0' & jage' & jwid' & jtok' & jused' & jnm' & jscr' &
              E5 & FC5 & FK5 & MU5 & WM5 & MI5 & TM5 & ST5 & C0' & CAGE' & CWID' & CTOK' & CUSED' & CNM' & CSCR').
  subst ms'.
  transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
  set (c := Z.of_nat (length (tj_entries T))) in *.
  assert (W1 : rw_cells rsegs m5 (X + 1056) [CB 1296 (objs_bytes buf vpad os ++ jo')]).
  { apply (user_join m5 (X + 1056) (X + 1056 + 144 * c) (Z.to_nat (144 * c)) (Z.to_nat (1296 - 144 * c)) 1296);
      [lia | lia | exact COB | exact COR]. }
  assert (W6 : rw_cells rsegs m5 (X + 2352) [CB 168 (jnm' ++ jscr')])
    by (apply (user_join m5 (X + 2352) (X + 2376) 24 144 168); [lia | lia | exact CNM' | exact CSCR']).
  assert (W5 : rw_cells rsegs m5 (X + 1056) [CB 1464 ((objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (user_join m5 (X + 1056) (X + 2352) 1296 168 1464); [lia | lia | exact W1 | exact W6]).
  assert (W4 : rw_cells rsegs m5 (X + 1024) [CB 1496 (jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (user_join m5 (X + 1024) (X + 1056) 32 1464 1496); [lia | lia | exact CUSED' | exact W5]).
  assert (W3 : rw_cells rsegs m5 (X + 1000)
                 [CB 1520 (jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (user_join m5 (X + 1000) (X + 1024) 24 1496 1520); [lia | lia | exact CTOK' | exact W4]).
  assert (W2 : rw_cells rsegs m5 (X + 976)
                 [CB 1544 (jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (user_join m5 (X + 976) (X + 1000) 24 1520 1544); [lia | lia | exact CWID' | exact W3]).
  assert (W0 : rw_cells rsegs m5 (X + 952)
                 [CB 1568 (jage' ++ jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr')])
    by (apply (user_join m5 (X + 952) (X + 976) 24 1544 1568); [lia | lia | exact CAGE' | exact W2]).
  apply evt_done. do 21 eexists.
  exists F5, fc5, m5, j0', j208', j232',
    (jage' ++ jwid' ++ jtok' ++ jused' ++ (objs_bytes buf vpad os ++ jo') ++ jnm' ++ jscr').
  split; [reflexivity|]. split; [exact FC5|]. split; [exact FK5|]. split; [unfold uW_TAIL; exact MU|].
  split; [exact WM|]. split; [exact MI5|]. split; [exact TM5|]. split; [exact ST5|]. split; [exact C0'|].
  split; [exact C208'|]. split; [exact C232'|exact W0].
Qed.

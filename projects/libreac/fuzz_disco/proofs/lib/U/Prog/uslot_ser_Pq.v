From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model disco_json_text reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_pure slot_ser_tokb slot_ser_Pq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import jtok_is_c reac_box_name_c disco_table_c disco_table uslot_ser_pure.
Import ListNotations.
Open Scope Z_scope.

Lemma ulength_pf_bytes : forall a, length (pf_bytes a) = length a.
Proof. intros. unfold pf_bytes. apply length_map. Qed.

Lemma ustk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hb'].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact Hb'.
Qed.

Lemma utj_resv : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
  [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 204800)].
Proof. vm_compute. reflexivity. Qed.

Lemma upf_hex2_hex2 : forall v, 0 <= v < 256 -> pf_hex2 v = hex2 v.
Proof.
  intros v Hv.
  assert (A : forallb (fun k => if list_eq_dec Z.eq_dec (pf_hex2 (Z.of_nat k)) (hex2 (Z.of_nat k)) then true else false)
                (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in A by lia. destruct (list_eq_dec Z.eq_dec _ _); [assumption | discriminate].
Qed.

Definition upinv (X lo buf now : Z) (T : list byte) (os : list jobj) (vpad : list byte) (canary : word)
    (m0 : word -> option byte) (k : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (X + 544) T /\
  bytes_at rsegs m (X + 1056) (objs_bytes buf vpad os) /\
  bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) /\
  rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] /\
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] /\
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] /\
  stk rsegs m X (X + 16) /\ stk rsegs m (X + 952) (X + 1024) /\ u32arr rsegs m (X + 1024) (used_ws k) /\
  stk rsegs m (X + 2352) (X + 2520) /\
  bytes_at rsegs m BN_TS bn_table /\ bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\
  bytes_at rsegs m GUARD (le8 canary) /\
  mem_inv rsegs m /\ stk rsegs m lo X /\ wmono rsegs m0 m /\
  munch [(lo, X); (X, X + 16); (X + 952, X + 1056); (X + 2352, X + 2520)] m0 m.

Lemma ubytes_tr : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply Hd. lia.
Qed.

Lemma urw_tr : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply ubytes_tr; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma uu32_tr : forall W m m' A ws, u32arr rsegs m A ws -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + 4 * Z.of_nat (length ws) -> outside W x) -> u32arr rsegs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] Hm Hmono Hd. split.
  - eapply ubytes_tr; [exact Hb | exact Hm |]. rewrite u32s_length. intros x Hx. apply Hd. lia.
  - eapply wr_at_transport; eauto.
Qed.

Lemma upinv_tr : forall X lo buf now T os vpad canary m0 k W m m',
  length T = 400%nat -> Z.of_nat (length (objs_bytes buf vpad os)) <= 1296 ->
  0 < buf -> buf + Z.of_nat (length (tj_text T now)) + 1 <= lo -> IMG_END <= lo -> lo <= X ->
  upinv X lo buf now T os vpad canary m0 k m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' lo X ->
  (forall x, outside [(lo, X); (X, X + 16); (X + 952, X + 1024); (X + 2352, X + 2520)] x -> outside W x) ->
  (forall x, X <= x < X + 16 \/ X + 952 <= x < X + 1024 \/ X + 2352 <= x < X + 2520 ->
     outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  upinv X lo buf now T os vpad canary m0 k m'.
Proof.
  intros X lo buf now T os vpad canary m0 k W m m' LT LO Hb Hbl HI HX
    (HT & HO & HB & C1 & C2 & C3 & C4 & S1 & S2 & HU & S3 & BN & G1 & G2 & MI & ST & WM & MU) MUc WMc MI' ST' SUB RD.
  unfold IMG_END in HI.
  unfold upinv.
  split; [eapply ubytes_tr; [exact HT | exact MUc |]; rewrite LT; out_tac SUB|].
  split; [eapply ubytes_tr; [exact HO | exact MUc |]; out_tac SUB|].
  split; [eapply ubytes_tr; [exact HB | exact MUc |]; rewrite ulength_pf_bytes, length_app; cbn [length]; out_tac SUB|].
  split; [eapply urw_tr; [exact C1 | exact MUc | exact WMc |]; cbn [cells_size csize]; out_tac SUB|].
  split; [eapply urw_tr; [exact C2 | exact MUc | exact WMc |]; cbn [cells_size csize]; out_tac SUB|].
  split; [eapply urw_tr; [exact C3 | exact MUc | exact WMc |]; cbn [cells_size csize]; out_tac SUB|].
  split; [eapply urw_tr; [exact C4 | exact MUc | exact WMc |]; cbn [cells_size csize]; out_tac SUB|].
  split; [eapply ustk_tr; [exact S1 | exact MUc | exact WMc |]; intros x Hx; apply RD; lia|].
  split; [eapply ustk_tr; [exact S2 | exact MUc | exact WMc |]; intros x Hx; apply RD; lia|].
  split; [eapply uu32_tr; [exact HU | exact MUc | exact WMc |]; rewrite len_used; out_tac SUB|].
  split; [eapply ustk_tr; [exact S3 | exact MUc | exact WMc |]; intros x Hx; apply RD; lia|].
  split; [eapply ubytes_tr; [exact BN | exact MUc |]; rewrite len_bn_table; unfold BN_TS; out_tac SUB|].
  split; [eapply ubytes_tr; [exact G1 | exact MUc |]; rewrite length_le8; unfold GOT_GUARD; out_tac SUB|].
  split; [eapply ubytes_tr; [exact G2 | exact MUc |]; rewrite length_le8; unfold GUARD; out_tac SUB|].
  split; [exact MI'|]. split; [exact ST'|].
  split; [eapply wmono_trans; [exact WM | exact WMc]|].
  eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
  intros x Hx. apply SUB. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4 & _).
  repeat split; try exact I; lia.
Qed.

Lemma uimg_free_hi : forall D n, 0x53000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs C.
  pose proof (in_map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) _ _ Hs) as H.
  rewrite utj_resv in H. cbn [In] in H.
  repeat destruct H as [H|H]; try contradiction; injection H as E1 E2; lia.
Qed.

Lemma uro_at : forall m a bs, mem_inv rsegs m -> ro_bytes_b rsegs a bs = true -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m a bs.
Proof. intros m a bs MI H Ha Hl. apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact H. Qed.

Lemma ucstr_of : forall m lo hi a s sl, mem_inv rsegs m ->
  ro_bytes_b rsegs a (bn_bytes s ++ Z_to_bv 8 0 :: sl) = true ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  ((- (a + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length sl)) = true ->
  a + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= 0x21000 -> 0x21000 <= lo -> 0 <= a ->
  bn_cstr m lo hi a s.
Proof.
  intros m lo hi a s sl MI R F A D HL Ha. split.
  - rewrite forallb_forall in F. apply Forall_forall. intros c Hc. specialize (F c Hc).
    apply andb_prop in F as [F1 F2]. lia.
  - exists sl. split; [|split].
    + apply uro_at; [exact MI | exact R | exact Ha |].
      unfold bn_bytes. rewrite length_app, length_map. cbn [length]. lia.
    + apply Z.leb_le. exact A.
    + cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma ulit_of : forall m lo hi a s, mem_inv rsegs m -> ro_bytes_b rsegs a (bn_bytes (s ++ [0])) = true ->
  a + Z.of_nat (length s) + 1 <= 0x21000 -> 0x21000 <= lo -> 0 <= a -> bn_lit m lo hi a s.
Proof.
  intros m lo hi a s MI R D HL Ha. split.
  - apply uro_at; [exact MI | exact R | exact Ha |]. unfold bn_bytes. rewrite length_map, length_app. cbn [length]. lia.
  - cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma ubn_img : forall m lo hi, mem_inv rsegs m -> bytes_at rsegs m BN_TS bn_table -> 0x21000 <= lo -> bn_image m lo hi.
Proof.
  intros m lo hi MI BT HL. unfold bn_image.
  split; [exact BT|].
  split; [cbn [disjoint_from]; unfold BN_TS; split; [lia | exact I]|].
  split; [apply (ucstr_of m lo hi BN_S1 _ (pf_bytes [44; 34])); [exact MI | vm_compute; reflexivity | vm_compute; reflexivity
            | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_S1; lia]|].
  split; [apply (ucstr_of m lo hi BN_S2 _ (pf_bytes [105; 110; 102; 0; 32])); [exact MI | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_S2; lia]|].
  split; [apply (ucstr_of m lo hi BN_S3 _ (pf_bytes [255; 255; 255; 255; 255])); [exact MI | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_S3; lia]|].
  split; [apply (ucstr_of m lo hi BN_REAC _ (pf_bytes [47])); [exact MI | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_REAC; lia]|].
  split; [apply ulit_of; [exact MI | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_PAREN; lia]|].
  split; [apply ulit_of; [exact MI | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_IN; lia]|].
  apply ulit_of; [exact MI | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HL | unfold BN_OUT; lia].
Qed.

Lemma upf_bytes_inj : forall a b, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b ->
  pf_bytes a = pf_bytes b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Fa Fb E; unfold pf_bytes in E; cbn [map] in E; try discriminate; [reflexivity|].
  pose proof (f_equal (hd (Z_to_bv 8 0)) E) as E1. pose proof (f_equal (@tl byte) E) as E2. cbn [hd tl] in E1, E2.
  inversion Fa as [|x' a' Hx Fa']; subst. inversion Fb as [|y' b' Hy Fb']; subst.
  f_equal; [|apply IH; [assumption | assumption | exact E2]].
  apply (f_equal bv_unsigned) in E1. rewrite !Z_to_bv_unsigned in E1. unfold bv_wrap in E1.
  change (bv_modulus 8) with 256 in E1. rewrite !Z.mod_small in E1 by lia. exact E1.
Qed.

Lemma upf_no_zero : forall s, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (pf_bytes s).
Proof.
  intros s F H. unfold pf_bytes in H. apply in_map_iff in H. destruct H as (c & E & Hc).
  rewrite Forall_forall in F. specialize (F c Hc).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma ubytes_at_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (firstn n (skipn (Z.to_nat k) bs)).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn.
  assert (Ln : length (firstn n (skipn (Z.to_nat k) bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite H by lia. rewrite nth_firstn by lia. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma upf_sub : forall B s l, 0 <= s -> 0 <= l -> s + l <= jlen B ->
  firstn (Z.to_nat l) (skipn (Z.to_nat s) (pf_bytes (B ++ [0]))) = pf_bytes (firstn (Z.to_nat l) (skipn (Z.to_nat s) B)).
Proof.
  intros B s l Hs Hl H. unfold jlen in H. unfold pf_bytes. rewrite map_app, skipn_app, length_map.
  replace (Z.to_nat s - length B)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn, length_map.
  replace (Z.to_nat l - (length B - Z.to_nat s))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite skipn_map, firstn_map. reflexivity.
Qed.

Lemma ujt_iff : forall B t kind text, Forall (fun c => 0 <= c < 256) B -> Forall (fun c => 0 < c < 256) text ->
  0 <= snd t < 2 ^ 64 ->
  jtok_match (tv_kind t) kind (Z_to_bv 64 (snd t)) (pf_bytes (tv_text B t)) (pf_bytes text) <->
  jtok_is B t kind text = true.
Proof.
  intros B t kind text FB FT Hl. unfold jtok_match, jtok_is. rewrite unsigned_lit by lia. rewrite ulength_pf_bytes.
  split.
  - intros (E1 & E2 & E3). rewrite E1, E2, !Z.eqb_refl. cbn [andb]. apply lzeqb_true.
    apply upf_bytes_inj; [| | exact E3].
    + unfold tv_text. apply forall_fs. exact FB.
    + apply Forall_forall. intros c Hc. rewrite Forall_forall in FT. specialize (FT c Hc). lia.
  - intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply lzeqb_true in H3.
    split; [exact H1|]. split; [exact H2|]. rewrite H3. reflexivity.
Qed.

Lemma ujt_call : jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo S SA TA buf kind : Z) (B text : list Z)
    (t : tokv) (vpad slack : list byte) (Q : machine_state -> Prop),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 kind -> a2 = Z_to_bv 64 TA ->
  - 2 ^ 31 <= kind < 2 ^ 31 -> tv_kind t <> 0 -> - 2 ^ 31 <= tv_kind t < 2 ^ 31 -> tok_inb B t ->
  SA mod 8 = 0 -> bytes_at rsegs m SA (slot24 buf vpad t) -> bytes_at rsegs m buf (pf_bytes (B ++ [0])) ->
  Forall (fun c => 0 <= c < 256) B -> Forall (fun c => 0 < c < 256) text ->
  bytes_at rsegs m TA (pf_bytes text ++ Z_to_bv 8 0 :: slack) ->
  (- (TA + Z.of_nat (length text) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < buf -> buf + Z.of_nat (length B) + 1 <= S - JTOK_IS_K ->
  (SA + 20 <= S - JTOK_IS_K \/ S <= SA) ->
  (TA + Z.of_nat (length text + 1 + length slack) <= S - JTOK_IS_K \/ S <= TA) ->
  mem_inv rsegs m -> stk rsegs m lo S -> lo + JTOK_IS_K <= S -> S < 2 ^ 64 ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(S - JTOK_IS_K, S)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo S ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 (Z.b2z (jtok_is B t kind text)))
                         y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 JTOK_IS) fc None m (seg_rom rsegs)).
Proof.
  intros JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo S SA TA buf kind B text t vpad slack Q Esp Ea0 Ea1 Ea2 Hk Hk0 Hkr IB HAL HSA HB FB FT HTA Hal Hb0 HbS
    HSAd HTAd MI ST HLO HS K.
  destruct IB as [IB|(Is & Il & Isl)]; [contradiction|].
  pose proof ST as (STa & STb & _).
  unfold jlen in Isl. unfold JTOK_IS_K in *.
  rewrite slot24_split in HSA by exact Hk0. apply bytes_at_app in HSA. destruct HSA as [HSA _].
  pose proof (bytes_at_bound rsegs m SA _ HSA) as BSA. rewrite !length_app, !length_le8, length_le4 in BSA.
  pose proof (bytes_at_bound rsegs m TA _ HTA) as BTA.
  pose proof (bytes_at_bound rsegs m buf _ HB) as BB.
  rewrite ulength_pf_bytes, length_app in BB. cbn [length] in BB.
  rewrite length_app, ulength_pf_bytes in BTA. cbn [length] in BTA.
  assert (LP : length (tv_text B t) = Z.to_nat (snd t)).
  { unfold tv_text. rewrite length_firstn, length_skipn. lia. }
  assert (HP : bytes_at rsegs m (buf + snd (fst t)) (pf_bytes (tv_text B t))).
  { unfold tv_text. rewrite <- upf_sub by (unfold jlen; lia).
    apply ubytes_at_sub; [exact HB | lia |]. rewrite ulength_pf_bytes, length_app. cbn [length]. lia. }
  subst sp a0 a1 a2.
  eapply evt_cut.
  { apply (JT ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SA) (Z_to_bv 64 kind) (Z_to_bv 64 TA) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo kind (tv_kind t)
              (Z_to_bv 64 (buf + snd (fst t))) (Z_to_bv 64 (snd t)) (pf_bytes text) slack (pf_bytes (tv_text B t)));
      rewrite ?(unsigned_lit S), ?(unsigned_lit SA), ?(unsigned_lit TA) by lia.
    - exact Hk.
    - reflexivity.
    - exact Hkr.
    - exact HAL.
    - exact HSA.
    - exact HTA.
    - apply upf_no_zero. exact FT.
    - rewrite ulength_pf_bytes. exact Hal.
    - intros _ E. rewrite unsigned_lit in E by lia. rewrite ulength_pf_bytes in E.
      rewrite (unsigned_lit (buf + snd (fst t))) by lia.
      split; [exact HP|]. split; [rewrite !ulength_pf_bytes, LP; lia|]. left. rewrite ulength_pf_bytes. unfold JTOK_IS_K. lia.
    - exact MI.
    - exact ST.
    - unfold JTOK_IS_K. lia.
    - unfold JTOK_IS_K. lia.
    - rewrite ulength_pf_bytes. unfold JTOK_IS_K. lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & R).
  subst ms'. rewrite unsigned_lit in MU, ST' by lia.
  assert (Ea : a0' = Z_to_bv 64 (Z.b2z (jtok_is B t kind text))).
  { pose proof (ujt_iff B t kind text FB FT ltac:(lia)) as J.
    destruct R as [[Hm Ea]|[Hm Ea]]; subst a0'.
    - rewrite (proj1 J Hm). reflexivity.
    - destruct (jtok_is B t kind text) eqn:Ej; [exfalso; apply Hm; apply J; reflexivity | reflexivity]. }
  subst a0'. apply K; assumption.
Qed.

Lemma usn_call : snprintf_stk_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo S D n A : Z) (canary : word)
    (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (q : list Z) (junk : list byte) (xs : list word)
    (Q : machine_state -> Prop),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
  bytes_at rsegs m A (pf_bytes (fmt ++ [0])) -> RO_LO <= A -> A + Z.of_nat (length fmt) + 1 <= RO_END ->
  pf_parse fmt = Some ps -> pf_args_ok m S lo D n ([a3; a4; a5; a6; a7] ++ xs) args ->
  bytes_at rsegs m S (u64s xs) -> pf_text ps args = Some q ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] -> 1 <= n < 2 ^ 31 -> Z.of_nat (length q) < 2 ^ 31 - 1 ->
  S + 8 * Z.of_nat (length xs) <= D -> 0x53000 <= D -> D < 2 ^ 63 ->
  stk rsegs m lo S -> lo + SNPRINTF_K <= S -> IMG_END <= lo -> frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  (forall (m' : word -> option byte) (Ft : bvmap 5 word) (fc' : bv 32)
          (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(lo, S); (D, D + Z.of_nat (length (firstn (Z.to_nat (n - 1)) q)) + 1)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     stk rsegs m' lo S -> bytes_at rsegs m' D (pf_bytes (firstn (Z.to_nat (n - 1)) q ++ [0])) ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 (Z.of_nat (length q))) y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) Ft (ret_pc ra) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros SNK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo S D n A canary fmt ps args q junk xs Q Esp Ea0 Ea1 Ea2 FB FLO FHI FP FA XS FT JB Hn HL HXD HD HD63
    ST HLO HIMG FC MI TM GG GW K.
  pose proof (rw_cells_bound rsegs m D _ JB) as BD. cbn [cells_size csize] in BD.
  pose proof (bytes_at_bound rsegs m A _ FB) as BA.
  pose proof ST as (STa & STb & _).
  unfold IMG_END, SNPRINTF_K, RO_END, RO_LO in *.
  subst sp a0 a1 a2.
  pose proof (SNK ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt ps args q junk xs) as H.
  cbv zeta in H.
  rewrite (unsigned_lit S), (unsigned_lit D), (unsigned_lit n), (unsigned_lit A) in H by lia.
  eapply evt_cut.
  { apply H; try assumption; unfold IMG_END, SNPRINTF_K, RO_END, RO_LO; try lia. apply uimg_free_hi. lia. }
  intros ms' PP. unfold printf_post in PP.
  destruct PP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Ft & fc' & m'
                  & E & MU' & WM' & MI' & TM' & FC' & FK' & ST' & BY').
  subst ms'. rewrite (unsigned_lit S) in MU', ST' by lia.
  apply K; assumption.
Qed.

Lemma umac_nth : forall T a k, 0 <= a -> a + 6 <= Z.of_nat (length T) -> (k < 6)%nat ->
  nth k (map bv_unsigned (sub T a 6)) 0 = u_at T (a + Z.of_nat k) 1.
Proof.
  intros T a k Ha HT Hk.
  destruct (nth_error T (Z.to_nat a + k)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  assert (E : nth_error (map bv_unsigned (sub T a 6)) k = Some (bv_unsigned b)).
  { unfold sub. rewrite nth_error_map, nth_firstn by lia. rewrite nth_error_skipn, Eb. reflexivity. }
  erewrite nth_error_nth; [|exact E]. unfold u_at, sub.
  replace (Z.to_nat (a + Z.of_nat k)) with (Z.to_nat a + k)%nat by lia.
  rewrite (firstn1_skipn T _ (Z_to_bv 8 0)) by (apply nth_error_Some; congruence).
  erewrite nth_error_nth; [|exact Eb]. symmetry. apply b1_unsigned.
Qed.

Lemma uu1_range : forall T k, 0 <= u_at T k 1 < 256.
Proof. intros T k. pose proof (user_u_at_bound T k 1) as H. change (2 ^ (8 * Z.of_nat 1)) with 256 in H. exact H. Qed.

Definition umac_ps : list pf_piece := [Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02].

Lemma umac_fmt_parse : pf_parse mac_fmt = Some umac_ps.
Proof. reflexivity. Qed.

Lemma umac_text_pf : forall T j, 0 <= j -> 48 * j + 6 <= Z.of_nat (length T) ->
  pf_text umac_ps [AInt (u_at T (48 * j + 0) 1); AInt (u_at T (48 * j + 1) 1); AInt (u_at T (48 * j + 2) 1);
                   AInt (u_at T (48 * j + 3) 1); AInt (u_at T (48 * j + 4) 1); AInt (u_at T (48 * j + 5) 1)] =
  Some (mac_text (map bv_unsigned (mac_of T j))).
Proof.
  intros T j Hj HT. unfold umac_ps. cbn [pf_text option_map].
  rewrite !upf_hex2_hex2 by apply uu1_range.
  unfold mac_text, mac_of. rewrite !umac_nth by lia. reflexivity.
Qed.

Definition utsk (x : Z) : Prop := find_segment rsegs x 1 <> None \/ x < TASK_SIZE.

Lemma utask_of : forall W m0 m, MemNorm.task_mem rsegs m0 -> munch W m0 m ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> utsk x) -> MemNorm.task_mem rsegs m.
Proof.
  intros W m0 m TM MU HW a b E. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
  destruct (outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (TM a b E).
  - apply HW; [lia | exact O].
Qed.

Lemma utsk_of_mrd : forall m x b, MemNorm.task_mem rsegs m -> 0 <= x < 2 ^ 64 -> mrd rsegs m (wa x) = Some b -> utsk x.
Proof.
  intros m x b TM Hx H. unfold mrd in H. unfold utsk.
  destruct (m (wa x)) as [b'|] eqn:E.
  - pose proof (TM _ _ E) as R. rewrite wa_unsigned in R by lia. exact R.
  - left. intros N. rewrite <- (wa_unsigned x) in N by lia.
    rewrite (MemNorm.seg_rom_unmapped rsegs (wa x) N) in H. discriminate.
Qed.

Lemma utsk_of_stk : forall m lo hi x, MemNorm.task_mem rsegs m -> stk rsegs m lo hi -> lo <= x < hi -> utsk x.
Proof.
  intros m lo hi x TM (H1 & H2 & H) Hx. destruct (H x Hx) as [_ (b & Hb)].
  eapply utsk_of_mrd; [exact TM | lia | exact Hb].
Qed.

Lemma uconcat_at : forall {A} (f : A -> list byte) L m a l k d, Forall (fun x => length (f x) = L) l ->
  (k < length l)%nat -> bytes_at rsegs m a (concat (map f l)) ->
  bytes_at rsegs m (a + Z.of_nat (L * k)) (f (nth k l d)).
Proof.
  intros A f L m a l. revert a. induction l as [|x l IH]; intros a k d H Hk B; cbn [length] in Hk; [lia|].
  apply Forall_cons_iff in H as [Hx H']. cbn [map concat] in B. apply bytes_at_app in B as [B1 B2].
  destruct k as [|k].
  - cbn [nth]. replace (a + Z.of_nat (L * 0)) with a by lia. exact B1.
  - cbn [nth]. replace (a + Z.of_nat (L * S k)) with (a + Z.of_nat (length (f x)) + Z.of_nat (L * k)) by lia.
    apply IH; [exact H' | lia | exact B2].
Qed.

Lemma uobjs_slot_at : forall m A buf vpad os k s, length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os ->
  (k < length os)%nat -> (s < 6)%nat -> bytes_at rsegs m A (objs_bytes buf vpad os) ->
  bytes_at rsegs m (A + 144 * Z.of_nat k + 24 * Z.of_nat s) (slot24 buf vpad (nth s (nth k os []) tok_none)).
Proof.
  intros m A buf vpad os k s L H Hk Hs B.
  assert (H6 : length (nth k os []) = 6%nat) by (rewrite Forall_forall in H; apply H; apply nth_In; exact Hk).
  assert (B1 : bytes_at rsegs m (A + Z.of_nat (144 * k)) (obj_bytes buf vpad (nth k os []))).
  { apply (uconcat_at (obj_bytes buf vpad) 144 m A os k []); [|exact Hk | exact B].
    eapply Forall_impl; [|exact H]. intros o Ho. unfold obj_bytes. rewrite (concat_len _ 24); [rewrite Ho; reflexivity|].
    apply Forall_forall. intros t _. apply slot24_len. exact L. }
  replace (A + 144 * Z.of_nat k + 24 * Z.of_nat s) with (A + Z.of_nat (144 * k) + Z.of_nat (24 * s)) by lia.
  apply (uconcat_at (slot24 buf vpad) 24 m _ (nth k os []) s tok_none); [| rewrite H6; exact Hs | exact B1].
  apply Forall_forall. intros t _. apply slot24_len. exact L.
Qed.

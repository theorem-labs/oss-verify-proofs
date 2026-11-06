(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_B64 ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C6_acc ECH_C7_read ECH_C7_rd ECH_C7_rd2 ECH_C9_ctrl ECH_C9_rdfacts ECH_C9_rdseg ECH_C9_rdloop
     ECH_C8_small ECH_C8_blockA ECH_C8_update ECH_C8_final.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma le4_cont_bytes : forall c, map bv_unsigned (le4 (wz c)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216].
Proof.
  intros c. unfold le4, wz, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  cbn [Z_to_le_bytes map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod c (2^64) ltac:(lia)) as DM. set (q := c / 2 ^ 64) in DM.
  replace (c mod 2^64) with (c + 2^64 * (- q)) by lia.
  change (2 ^ 8) with (256 ^ 1). change (2 ^ (8 + 8)) with (256 ^ 2). change (2 ^ (8 + 8 + 8)) with (256 ^ 3).
  rewrite !div256k_mod64 by lia. rewrite Z.pow_1_r. change (256 ^ 2) with 65536. change (256 ^ 3) with 16777216.
  replace ((c + 2 ^ 64 * - q) mod 256) with (c mod 256); [reflexivity|].
  replace (c + 2 ^ 64 * - q) with (c + (- 72057594037927936 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => hide H end.
  Local Ltac killb K :=
    first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia ].
  Local Ltac take_cells n cs := lazymatch n with O => constr:(@nil cell) | S ?k => lazymatch cs with ?c :: ?tl => let r := take_cells k tl in constr:(c :: r) end end.
  Local Ltac drop_cells n cs := lazymatch n with O => cs | S ?k => lazymatch cs with _ :: ?tl => drop_cells k tl end end.
  Local Ltac lit_ofnat H := repeat match type of H with context [Z.of_nat (S ?k)] => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in H end.
  Local Ltac split_chunk H n H1 H2 :=
    lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
      let cs1 := take_cells n cs in let cs2 := drop_cells n cs in
      change (rw_cells segs m A (cs1 ++ cs2)) in H;
      apply (proj1 (rw_cells_app segs m A cs1 cs2)) in H;
      let T1 := fresh "T1" in let T2 := fresh "T2" in
      destruct H as [T1 T2];
      cbn [cells_size csize Nat.add] in T2; lit_ofnat T2;
      repeat match type of T2 with context [Z.add (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c + d)%Z in
           replace (Z.add (Z.add b c) d) with (Z.add b v) in T2 by lia end;
      rename T1 into H1; rename T2 into H2
    end.
  Local Ltac join_chunk H1 H2 H :=
    lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      pose proof (proj2 (rw_cells_app segs m A cs1 cs2)) as H;
      specialize (H (conj H1 ltac:(replace (A + Z.of_nat (cells_size cs1)) with A2 by (cbn; lia); exact H2)));
      clear H1 H2
    end end.
  Local Ltac norm_addr_goal := match goal with |- rw_cells ?sg ?mm ?a ?cs => let v := eval vm_compute in a in change (rw_cells sg mm v cs) end.
  Local Ltac land_open :=
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      match goal with M1 : munch _ ?m0 m1 |- _ =>
        match goal with W1 : wmono _ m0 m1 |- _ =>
          let a := fresh "MUc" in let b := fresh "WMc" in rename M1 into a; rename W1 into b;
          rewrite ?unsigned_lit in a by lia end end end;
    repeat match goal with H : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
      lazymatch type of H with munch _ _ _ => fail | hidden _ => fail | _ => rewrite ?unsigned_lit in H by lia end end.
  Local Ltac carry1 H :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MUc : munch ?W ?m0 m1 |- _ => lazymatch goal with WMc : wmono _ m0 m1 |- _ =>
        lazymatch type of H with
        | rw_cells ?segs m0 ?A ?cs => apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MUc WMc) in H; [| cbn; lia]
        | bytes_at ?segs m0 ?A ?bs => apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MUc) in H; [| cbn; lia]
        | stk ?segs m0 ?lo ?hi => apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MUc WMc) in H; [| cbn; lia]
        end end end end.
  Local Ltac land_close MU WM :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      match goal with MUc : munch ?W ?m0 m1 |- _ => match goal with WMc : wmono _ m0 m1 |- _ =>
        extm MU WM MUc WMc end end;
      repeat match goal with H : mem_inv _ ?mx |- _ => lazymatch mx with m1 => fail | _ => clear H end end;
      repeat match goal with H : rw_cells _ ?mx _ _ |- _ => lazymatch mx with m1 => fail | _ => clear H end end;
      repeat match goal with H : bytes_at _ ?mx _ _ |- _ => lazymatch mx with m1 => fail | _ => clear H end end;
      repeat match goal with H : stk _ ?mx _ _ |- _ => lazymatch mx with m1 => fail | _ => clear H end end;
      try (lazymatch goal with _ : stk _ m1 _ _ |- _ => idtac end; match goal with H : stk _ m1 _ _ |- _ => rename H into ST end)
    end;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
    repeat match goal with H : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.

  (* [comment removed for export] *)
  Lemma rw_cells_CB0 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
  Proof.
    intros m A cs H. eapply rw_cells_recut; [exact H| |].
    - destruct H as [[WF _] _]. cbn. split; [reflexivity| exact WF].
    - reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma rdframe_of_head : forall m spx ctx mb a jA j16 j8 (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word),
    rw_cells rsegs m spx [C8 (Z_to_bv 64 (ctx + 1542)); CB 16 jA; C8 (Z_to_bv 64 (ctx + 1542)); C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 0);
                         CB 16 j16; C8 (Z_to_bv 64 (ctx + 40)); CB 8 j8; C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra] ->
    rw_cells rsegs m spx (rdframe ctx mb a (bytes_le_to_Z (firstn 8 jA)) (bytes_le_to_Z (skipn 8 jA)) 0 j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra).
  Proof.
    intros until qra. intros H. pose proof H as W. destruct W as [[WF _] _]. cbn in WF.
    assert (LA : length jA = 16%nat) by tauto. assert (L16 : length j16 = 16%nat) by tauto. assert (L8 : length j8 = 8%nat) by tauto.
    eapply rw_cells_recut; [exact H| |].
    - cbn. tauto.
    - unfold rdframe. cbn [cells_bytes cbytes app].
      change (Z_to_bv 64 (bytes_le_to_Z (firstn 8 jA))) with (wz (bytes_le_to_Z (firstn 8 jA))).
      change (Z_to_bv 64 (bytes_le_to_Z (skipn 8 jA))) with (wz (bytes_le_to_Z (skipn 8 jA))).
      rewrite !le8_wz_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
      rewrite <- (firstn_skipn 8 jA) at 3. rewrite <- !app_assoc. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma b64ctx_at_head : forall m ctx enc bjunk, length bjunk = 2528%nat ->
    rw_cells rsegs m ctx [C4 (wz 0); C4 (wz (0 ≫ 32)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                         C8 (Z_to_bv 64 enc); CB 2528 bjunk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
       rw_cells rsegs m ctx (rdhdr 0 0 0 1 enc)
    /\ rw_cells rsegs m (ctx + 40) [CB 1502 (firstn 1502 bjunk)]
    /\ rw_cells rsegs m (ctx + 1542) [CB 1024 (firstn 1024 (skipn 1502 bjunk))]
    /\ rw_cells rsegs m (ctx + 2566) [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)].
  Proof.
    intros m ctx enc bjunk LJ H.
    assert (E : rw_cells rsegs m ctx ((rdhdr 0 0 0 1 enc ++ [CB 1502 (firstn 1502 bjunk)]) ++ [CB 1024 (firstn 1024 (skipn 1502 bjunk))]
                                     ++ [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)])).
    { eapply rw_cells_recut; [exact H| |].
      - cbn. rewrite !length_firstn, !length_skipn. repeat split; lia.
      - unfold rdhdr. cbn [cells_bytes cbytes app]. change (0 ≫ 32) with 0.
        rewrite <- (firstn_skipn 1502 bjunk) at 4. rewrite <- (firstn_skipn 1024 (skipn 1502 bjunk)) at 2. rewrite skipn_skipn. cbn [Nat.add].
        rewrite <- !app_assoc. reflexivity. }
    apply rw_cells_app in E. destruct E as [E1 E]. apply rw_cells_app in E. destruct E as [E2 E3].
    apply rw_cells_app in E1. destruct E1 as [E0 E1].
    revert E1 E2 E3. rewrite !cells_size_app. cbn [cells_size csize app Nat.add rdhdr]. intros E1 E2 E3.
    replace (ctx + Z.of_nat 40) with (ctx + 40) in E1 by lia.
    replace (ctx + Z.of_nat 1542) with (ctx + 1542) in E2 by lia.
    replace (ctx + Z.of_nat 1542 + Z.of_nat 1024) with (ctx + 2566) in E3 by lia.
    split; [exact E0|]. split; [exact E1|]. split; [exact E2| exact E3].
  Qed.
  (* [comment removed for export] *)
  Local Ltac app_at H1 H2 A2 :=
    apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact H1| match goal with |- rw_cells _ _ ?A _ => replace A with A2 by (cbn; lia) end; exact H2].
  Lemma b64ctx_used_of_exit : forall m ctx enc bl bo c jb jt tl,
    rw_cells rsegs m ctx (rdhdr bl bo 0 c enc) -> rw_cells rsegs m (ctx + 40) [CB 1502 jb] -> rw_cells rsegs m (ctx + 1542) [CB 1024 jt] ->
    rw_cells rsegs m (ctx + 2566) [CB 2 tl; C8 (wz 0); C8 (wz 0)] ->
    let hdr := cells_bytes [C4 (wz bl); C4 (wz bo); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0)] in
       rw_cells rsegs m ctx (b64ctx_used_cells enc hdr (jb ++ jt ++ tl) 0) /\ length hdr = 32%nat /\ length (jb ++ jt ++ tl) = 2528%nat
    /\ map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216].
  Proof.
    intros until tl. intros H0 H1 H2 H3. cbv zeta.
    pose proof H1 as W1. destruct W1 as [[WF1 _] _]. cbn in WF1. pose proof H2 as W2. destruct W2 as [[WF2 _] _]. cbn in WF2.
    pose proof H3 as W3. destruct W3 as [[WF3 _] _]. cbn in WF3.
    assert (L1 : length jb = 1502%nat) by tauto. assert (L2 : length jt = 1024%nat) by tauto. assert (L3 : length tl = 2%nat) by tauto.
    assert (E1 : rw_cells rsegs m ctx (rdhdr bl bo 0 c enc ++ [CB 1502 jb])) by (app_at H0 H1 (ctx + 40)).
    assert (E2 : rw_cells rsegs m ctx ((rdhdr bl bo 0 c enc ++ [CB 1502 jb]) ++ [CB 1024 jt])) by (app_at E1 H2 (ctx + 1542)).
    assert (E : rw_cells rsegs m ctx (((rdhdr bl bo 0 c enc ++ [CB 1502 jb]) ++ [CB 1024 jt]) ++ [CB 2 tl; C8 (wz 0); C8 (wz 0)])) by (app_at E2 H3 (ctx + 2566)).
    clear E1 E2.
    split; [| split; [reflexivity| split; [rewrite !length_app; lia|]]].
    - eapply rw_cells_recut; [exact E| |].
      + cbn. rewrite !length_app. repeat split; lia.
      + unfold rdhdr, b64ctx_used_cells. cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity.
    - generalize (le4_cont_bytes c). unfold le4, wz, word_to_le_bytes. cbn. intros E4. exact E4.
  Qed.

  (* [comment removed for export] *)
  Definition rdhead_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (a : Z) (R : b64frep) (mb : Z) (M : membio) (txt junk : list byte) (out outl lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m3 (ra' t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 : word) (vout voutl : Z) (j16 j8 bjunk : list byte),
         ms' = HEADMS sp gp tp F fc a mb R ra' t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' s8 s10 s11 t3 t4 t5 t6 outl out m3
      /\ munch ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m m3 /\ wmono rsegs m m3 /\ mem_inv rsegs m3
      /\ stk rsegs m3 lo (bv_unsigned sp + -192)
      /\ rw_cells rsegs m3 (bv_unsigned sp + -192) (rdframe (bf_ctx R) mb a vout voutl 0 j16 j8 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells rsegs m3 a (bio_cells (mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0))
      /\ length bjunk = 2528%nat
      /\ rw_cells rsegs m3 (bf_ctx R) [C4 (wz 0); C4 (wz (0 ≫ 32)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 (bf_enc R)); CB 2528 bjunk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      /\ ENCCTX LB m3 (bf_enc R) [] (bf_eid R)
      /\ MEMBIO LB m3 mb M
      /\ bytes_at rsegs m3 (mb_buf M) txt /\ rw_cells rsegs m3 out [CB (Z.to_nat outl) junk]
      /\ METH_b64 m3 /\ METH_mem m3.
  Lemma rd_entry :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at rsegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - B64READ_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (rdhead_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc LB a R mb M txt junk out outl lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_read) fc None m (seg_rom rsegs)).
  Proof.
    intros until junk. intros A0 A1 A2 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT METHB METHM ST CEIL LO MI RAE.
    subst a0 a1 a2. pose proof OUTMB as OUTMB0. unfold A_b64_method, O_METH_BREAD in OUTMB.
    pose proof LO as LO_orig.
    unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK, DECFINAL_STACK, DECBLOCK_STACK,
      FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_EVP_DecodeUpdate, FR_EVP_DecodeFinal, FR_evp_decodeblock_int,
      BIOACC_STACK, FR_BIO_set_data in LO.
    unfold P_b64_read. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & _ & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as MO0. destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    unfold BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in *.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail APM3)) as DJ_e_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM3)))) as DJ_e_rp.
    cbn [blk_addr blk_size fst snd] in DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp. clear APM3.
    pose proof (Forall_inv APT) as PT1. pose proof (Forall_inv (Forall_inv_tail APT)) as PT2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT))) as PT3.
    cbn [blk_addr blk_size fst snd] in PT1, PT2, PT3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NXT, RT0, NR0 in BC.
    unfold b64ctx_fresh_cells, wz in BX.
    pose proof MB as MB0.
    destruct MB0 as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE, B64CTX_SIZE in *.
    hide_ors.
    unfold bio_cells, membio_bio, wz in MC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in MC.
    unfold A_mem_buf_method in MC. rewrite NUMR in MC.
    unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof METHM as METHM0. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM. norm_addr METHM.
    unfold zlength in TLEN, TLE.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & _ & _ & DINV).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    unhide OUTR. carve_frame 192%nat ST. st1. st1. hide OUTR.
    do 13 st1.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply biogetdata_spec with (lo := lo) (a := a) (x := out)
        (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BC
           | |- bio_ok _ => unfold bio_ok; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; unhide MI0; lia
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => try (unfold BIOACC_STACK, FR_BIO_set_data, BIO_SIZE; lia); try lia
           end. }
    unfold bioacc_post, BIO_SIZE. clear BC. land_open.
    carry1 FR. unhide BA1. carry1 BX. hide BA1. unhide BA2. carry1 EC. hide BA2.
    unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp. carry1 MC. carry1 MBB. carry1 MBM. carry1 MRP. hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp.
    unhide PT1. carry1 TXT. hide PT1. unhide OUTR; unhide OA1. carry1 OUTC. hide OUTR; hide OA1. unhide AI. carry1 METHB. carry1 METHM. hide AI.
    land_close MU WM.
    cbn [bio_ptr]. unfold bio_cells, wz in PO; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in PO; unfold A_b64_method in PO; rename PO into BC1.
    (* [comment removed for export] *)
    step. step. step. step.
    eapply evt_cut.
    { eapply bionext_spec with (lo := lo) (a := a) (x := 0)
        (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BC1
           | |- bio_ok _ => unfold bio_ok; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; unhide MI0; lia
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => try (unfold BIOACC_STACK, FR_BIO_set_data, BIO_SIZE; lia); try lia
           end. }
    unfold bioacc_post, BIO_SIZE. clear BC1. land_open.
    carry1 FR. unhide BA1. carry1 BX. hide BA1. unhide BA2. carry1 EC. hide BA2.
    unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp. carry1 MC. carry1 MBB. carry1 MBM. carry1 MRP. hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp.
    unhide PT1. carry1 TXT. hide PT1. unhide OUTR; unhide OA1. carry1 OUTC. hide OUTR; hide OA1. unhide AI. carry1 METHB. carry1 METHM. hide AI.
    land_close MU WM.
    cbn [bio_next]. unfold bio_cells, wz in PO; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in PO; unfold A_b64_method in PO; try clear BC1; rename PO into BC1.
    (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. step. step. step.
    eapply evt_cut.
    { eapply bioclearflags_spec with (lo := lo) (a := a) (x := 15)
        (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BC1
           | |- bio_ok _ => unfold bio_ok; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; unhide MI0; lia
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => try (unfold BIOACC_STACK, FR_BIO_set_data, BIO_SIZE; lia); try lia
           end. }
    unfold bioacc_post, BIO_SIZE. clear BC1. land_open.
    carry1 FR. unhide BA1. carry1 BX. hide BA1. unhide BA2. carry1 EC. hide BA2.
    unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp. carry1 MC. carry1 MBB. carry1 MBM. carry1 MRP. hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp.
    unhide PT1. carry1 TXT. hide PT1. unhide OUTR; unhide OA1. carry1 OUTC. hide OUTR; hide OA1. unhide AI. carry1 METHB. carry1 METHM. hide AI.
    land_close MU WM.
    unfold bio_with_flags, bio_cells, wz in PO; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in PO; unfold A_b64_method in PO; try clear BC1; rename PO into BC1.
    (* [comment removed for export] *)
    st1. rewrite (sx32_lit 0) by lia. step. step. if_false.
    st1.
    apply (rw_cells_merge rsegs _ (bf_ctx R) [] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in BX. cbn [app cells_size csize cells_bytes cbytes Nat.add] in BX.
    unhide BA1; unhide BA3; unhide CI; unhide DJ_c_mb; unhide DJ_c_bb; unhide DJ_c_bm; unhide DJ_c_rp; unhide PT2; unhide OA2.
    st1. hide_ors. st1. st1.
    match goal with H : rw_cells rsegs _ (bf_ctx R) _ |- _ => apply (rw_cells_C8_C4C4 rsegs _ (bf_ctx R) [] 0) in H; [cbn [app Z.shiftr] in H| lia]; rename H into BX0 end.
    step.
    (* [comment removed for export] *)
    pose proof EC as EC0.
    apply (rw_cells_merge rsegs _ (bf_enc R) [] [C4 (wz (zlength (@nil Z))); CB 80 raw; C4 (wz line); C4 (wz 0)] []) in EC0. clear EC.
    eapply evt_cut.
    { pose proof decinit_spec as DIS. unfold decinit_stmt in DIS.
      eapply DIS with (lo := lo) (a := bf_enc R) (LB := LB) (p := bf_eid R); clear DIS; rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [CB 92 _] => exact EC0
           | |- In _ _ => exact I3
           | |- rblock_range _ _ => exact RB3
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => try (unfold DECINIT_STACK, FR_EVP_DecodeInit, ENCCTX_SIZE; lia); try lia
           end.
      all: match goal with |- ?G => idtac "DI-LEFT:" G end. }
    unfold c8_post, ENCCTX_foot, ENCCTX_SIZE. clear EC0. land_open.
    carry1 FR. unhide BA3. carry1 BX0. hide BA3. unhide BA2. carry1 BC1. hide BA2.
    unhide DJ_e_mb; unhide DJ_e_bb; unhide DJ_e_bm; unhide DJ_e_rp. carry1 MC. carry1 MBB. carry1 MBM. carry1 MRP. hide DJ_e_mb; hide DJ_e_bb; hide DJ_e_bm; hide DJ_e_rp.
    unhide PT3. carry1 TXT. hide PT3. unhide OUTR; unhide OA3. carry1 OUTC. hide OUTR; hide OA3. unhide EI. carry1 METHB. carry1 METHM. hide EI.
    land_close MU WM.
    (* [comment removed for export] *)
    st1. rewrite (sx32_lit 0) by lia. step. if_true.
    match goal with H : ENCCTX LB _ (bf_enc R) [] _ |- _ => destruct H as (raw1 & line1 & RAWL1 & RAWP1 & EC1 & LINE1 & _ & _ & DINV1) end.
    st1. st1. rewrite ?(sx32_lit 1) by lia. step. step. step. if_cases K4; zify_cond K4; [killb K4|]. try clear K4.
    step. step. st1. step. st1. step. st1. st1. st1.
    (* [comment removed for export] *)
    apply evt_done. unfold rdhead_post, HEADMS.
    match goal with H : rw_cells rsegs _ a _ |- _ => rename H into BCf end.
    match goal with H : rw_cells rsegs _ (bf_ctx R) _ |- _ => rename H into BXf end.
    match goal with H : rw_cells rsegs _ (bf_enc R) _ |- _ => rename H into ECf end.
    assert (ENCf : ENCCTX LB m3 (bf_enc R) [] (bf_eid R)).
    { exists raw1, line1. split; [exact RAWL1|]. split; [exact RAWP1|]. split; [exact ECf|]. split; [exact LINE1|]. split; [exact I3|]. split; [exact RB3| exact DINV1]. }
    match goal with H : rw_cells rsegs _ (bv_unsigned sp + -192) _ |- _ => rename H into FRf end.
    apply rdframe_of_head in FRf.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, (bytes_le_to_Z _), (bytes_le_to_Z _), _, _, _.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { exact FRf. }
    split. { unfold bio_cells, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BCf. }
    split; [exact LJ|]. split; [exact BXf|]. split; [exact ENCf|].
    split. { unhide MI0. membio_tac.
             all: try (unfold bio_cells, membio_bio, buf_cells, wz;
                   cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
                        mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
                   unfold A_mem_buf_method; rewrite ?NUMR, ?Z.add_0_r; assumption).
             all: match goal with |- ?G => idtac "MBLEFT:" G end. }
    split; [assumption|]. split; [assumption|].
    split. { unfold METH_b64, O_METH_BREAD, A_b64_method, wz. match goal with H : rw_cells rsegs _ 2992824 _ |- _ => norm_addr_goal; exact H end. }
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz. match goal with H : rw_cells rsegs _ 2810272 _ |- _ => norm_addr_goal; exact H end.
    all: match goal with |- ?G => idtac "ENTRY-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Definition b64rd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv : Z) (a : Z) (R : b64frep) (nr : Z) (mb : Z) (M : membio) (txt : list byte)
      (out : Z) (data : list Z) (outl : Z) (used : nat) (rb : option (Z * Z)) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (fl rt c fl' nr' : Z) (d' : list Z) (hdr junk junk' : list byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' a (bio_cells (b64f_bio (bf_with_hdr R fl rt nr mb (bf_prev R)))) /\ 0 <= fl < 2^31 /\ 0 <= rt < 2^32
      /\ length hdr = 32%nat /\ length junk = 2528%nat /\ rw_cells rsegs m' (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk 0)
      /\ map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216]
      /\ - 2^31 <= c < 2^31 /\ (rv = 0 -> c <= 0) /\ -1 <= rv <= outl /\ zlength data <= outl
      /\ ENCCTX LB m' (bf_enc R) d' (bf_eid R)
      /\ MEMBIO LB m' mb (mset M (Z.of_nat used) fl' nr')
      /\ bytes_at rsegs m' (mb_buf M) txt
      /\ rw_cells rsegs m' out [CB (length data) (map b8 data); CB (Z.to_nat outl - length data) junk']
      /\ METH_b64 m' /\ METH_mem m'
      /\ match rb with None => True | Some (rbp, v) => rw_cells rsegs m' rbp [C8 (wz v)] /\ 0 <= v <= outl end.


  (* [comment removed for export] *)
  Lemma b64read_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at rsegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - B64READ_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (b64rd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (br_rv (b64_read_spec (map bv_unsigned txt) outl)) a R (bf_nread R) mb M txt
                   out (br_out (b64_read_spec (map bv_unsigned txt) outl)) outl (br_used (b64_read_spec (map bv_unsigned txt) outl)) None
                   ((out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_read) fc None m (seg_rom rsegs)).
  Proof.
    intros until junk. intros A0 A1 A2 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT METHB METHM ST CEIL LO MI RAE.
    eapply evt_cut; [eapply rd_entry; eassumption|]. cbv beta.
    intros ms1 (m3 & ra' & u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & vout & voutl & j16 & j8 & bjunk
                & -> & MU & WM & MI3 & ST3 & FR3 & BC3 & LJ & BX3 & ENC3 & MB3 & TXT3 & OUTC3 & METHB3 & METHM3).
    clear ENC TXT OUTC METHB METHM MI.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BF as (_ & _ & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & _ & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MB as MBc.
    destruct MBc as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    destruct (b64ctx_at_head _ _ _ _ LJ BX3) as (HD3 & BUF3 & TMP3 & TAIL3). clear BX3.
    pose proof (b64_flags_facts (bf_flags R) FLR ltac:(unfold BIO_FLAGS_BASE64_NO_NL in NONL; exact NONL)) as [FL1 FL2].
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv APT) as PT1. cbn [blk_addr blk_size fst snd] in PT1.
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp, DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp, PT1, AI, CI, EI, MI0.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. unfold A_b64_method, O_METH_BREAD in OUTMB.
    assert (LOS : lo <= bv_unsigned sp + -192 - Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK (Z.max DECFINAL_STACK (Z.max DECINIT_STACK 16)))).
    { revert LO. unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK,
        DECFINAL_STACK, DECBLOCK_STACK, DECINIT_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
        FR_EVP_DecodeUpdate, FR_EVP_DecodeFinal, FR_evp_decodeblock_int, FR_EVP_DecodeInit, BIOACC_STACK, FR_BIO_set_data. clear. intros; lia. }
    assert (LO16 : lo <= bv_unsigned sp + -192 - 16) by (clear - LOS; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { match goal with |- evt _ _ ?ms =>
        replace ms with (HEADMS sp gp tp F fc a mb R ra' u0 u1 u2 w0 w1 w2 w3 w4 w5 w6 w7 s8 s10 s11 u3 u4 u5 u6 (outl - zlength (@nil Z)) (out + zlength (@nil Z)) m3)
          by (unfold HEADMS, zlength; cbn [length Z.of_nat]; rewrite Z.sub_0_r, Z.add_0_r; reflexivity) end.
      eapply (@rd_loop HCEIL sp gp tp s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra F fc m3 LB a mb lo out outl R M txt
                BAP BEL RB1 RB2 RB3 FLR I3 MBL MSEP (conj RM1 (conj RM2 (conj RM3 RM4))) LENR TLEN APM APT OUTF OUTB OUTM APO OUTR OUTP OUTH OUTL CEIL LOS METHM3
                _ BC3 FL1 FL2 (S (S (length txt))) 0%nat [] [] m3 (mb_flags M) (mb_nread M) 1 vout voutl (firstn 1502 bjunk) (firstn 1024 (skipn 1502 bjunk)) junk j16 j8).
      - clear; cbn; lia.
      - clear; lia.
      - unfold zlength; cbn; clear - OUTL; lia.
      - left; reflexivity.
      - clear; lia.
      - unfold HINV. split; [exact FR3|]. split; [exact HD3|]. split; [exact BUF3|]. split; [exact TMP3|]. split; [exact ENC3|].
        split. { change (Z.of_nat 0) with 0. rewrite <- POS0. rewrite mset_self. exact MB3. }
        split; [exact TXT3|]. split. { cbn [length map]. rewrite Nat.sub_0_r. apply rw_cells_CB0. exact OUTC3. }
        split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI3)|]. split; [exact MI3|]. split; [exact ST3|]. split; [apply munch_refl| apply wmono_refl]. }
    cbv beta. intros ms2 EX. unfold EXITQ in EX.
    destruct EX as (m' & rcf & c' & vout' & voutl' & fl' & nr' & bl' & bo' & d' & jb' & jt' & jo' & j16' & j8' & ra2 & x0 & x1 & x2 & y1 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7
                    & y2 & y4 & y5 & y7 & y8 & y9 & y10 & y11 & x3 & x4 & x5 & x6
                    & -> & RV & RCF & CLE & CR & ZLE & USED & FLR' & FRx & HDx & BUFx & TMPx & ENCx & MBx & TXTx & OUTx & TABx & MIx & STx & MUx & WMx).
    replace (b64r_loop (S (S (length txt))) (skipn 0 (map bv_unsigned txt)) [] (zlength (@nil Z)) (outl - zlength (@nil Z)) [] 0)
      with (b64_read_spec (map bv_unsigned txt) outl) in *
      by (unfold b64_read_spec, zlength; rewrite length_map; cbn [skipn length Z.of_nat]; rewrite Z.sub_0_r; reflexivity).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    (* [comment removed for export] *)
    pose proof RM3 as (_ & _ & _ & _ & BMI). unfold BUFMEM_SIZE in BMI.
    unfold WL in MUx.
    assert (BCx : rw_cells rsegs m' a (bio_cells (mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0))).
    { eapply rw_cells_transport; [exact BC3| exact MUx| exact WMx|]. cbn. clear - BL1 OA1 BA1 BA2 DJ_a_mb DJ_a_bm. lia. }
    assert (TAILx : rw_cells rsegs m' (bf_ctx R + 2566) [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact TAIL3| exact MUx| exact WMx|]. cbn. clear - BL2 OA2 BA3 DJ_c_mb DJ_c_bm. lia. }
    assert (METHBx : METH_b64 m').
    { unfold METH_b64 in METHB3 |- *. eapply rw_cells_transport; [exact METHB3| exact MUx| exact WMx|].
      unfold A_b64_method, O_METH_BREAD. cbn. clear - CEIL HCEILB OUTMB CI EI MI0 BMI SPR. lia. }
    assert (METHMx : METH_mem m').
    { unfold METH_mem in METHM3 |- *. eapply rw_cells_transport; [exact METHM3| exact MUx| exact WMx|].
      unfold A_mem_buf_method, O_METH_BREAD. cbn. clear - CEIL HCEILB OUTM CI EI MI0 BMI SPR. lia. }
    clear BC3 TAIL3 METHB3 METHM3 HD3 BUF3 TMP3 ENC3 MB3 TXT3 OUTC3 FR3.
    pose proof MBx as MBx1. destruct MBx1 as (NCx & _).
    assert (ZNN : 0 <= zlength (br_out res)) by (unfold zlength; clear; lia).
    eapply evt_cut.
    { eapply rd_exit with (B := mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0)
                          (NB := membio_bio (mset M (Z.of_nat (br_used res)) fl' nr')) (lo := lo);
        cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite membio_bio mset
             mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp].
      all: try first [exact FRx | exact BCx | exact NCx | exact STx | exact MIx | exact CEIL | exact RAE | reflexivity].
      all: try (unfold BIO_SIZE; clear - ZLE ZNN OUTL RCF AP BL1 MP ML1 DJ_a_mb FL1 FLR' LO16 CR; lia).
      all: match goal with |- ?G => idtac "EXIT-LEFT:" G end. }
    cbv beta. intros ms3 (m1 & g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & -> & MU1 & WM1 & MI1 & ST1 & BC1 & NC1).
    rewrite ?unsigned_lit in MU1 by (clear - SPR LO16 LO0; lia).
    unfold BIO_SIZE in MU1.
    assert (TAIL1 : rw_cells rsegs m1 (bf_ctx R + 2566) [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact TAILx| exact MU1| exact WM1|]. cbn. clear - BL2 BA1 LO16. lia. }
    assert (HD1 : rw_cells rsegs m1 (bf_ctx R) (rdhdr bl' bo' 0 c' (bf_enc R))).
    { eapply rw_cells_transport; [exact HDx| exact MU1| exact WM1|]. cbn. clear - BL2 BA1 LO16. lia. }
    assert (BUF1 : rw_cells rsegs m1 (bf_ctx R + 40) [CB 1502 jb']).
    { eapply rw_cells_transport; [exact BUFx| exact MU1| exact WM1|]. cbn. clear - BL2 BA1 LO16. lia. }
    assert (TMP1 : rw_cells rsegs m1 (bf_ctx R + 1542) [CB 1024 jt']).
    { eapply rw_cells_transport; [exact TMPx| exact MU1| exact WM1|]. cbn. clear - BL2 BA1 LO16. lia. }
    assert (ENC1 : ENCCTX LB m1 (bf_enc R) d' (bf_eid R)).
    { eapply ENCCTX_transport; [exact MU1| exact WM1| | exact ENCx]. cbn. clear - BL3 BA2 LO16. lia. }
    assert (MB1 : MEMBIO LB m1 mb (mset M (Z.of_nat (br_used res)) fl' nr')).
    { eapply MEMBIO_transport; [exact MU1| exact WM1| | | | | exact MBx]; cbn [mb_bb mb_bm mb_rp mset]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn.
      - clear - ML1 DJ_a_mb LO16. lia. - clear - ML2 DJ_a_bb LO16. lia. - clear - ML3 DJ_a_bm LO16. lia. - clear - ML4 DJ_a_rp LO16. lia. }
    assert (TXT1 : bytes_at rsegs m1 (mb_buf M) txt).
    { eapply bytes_at_transport; [exact TXTx| exact MU1|]. cbn. unfold zlength in TLEN. clear - BUFH CEIL LO16 TLEN PT1 SPR. lia. }
    assert (OUT1 : rw_cells rsegs m1 out [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) jo']).
    { eapply rw_cells_transport; [exact OUTx| exact MU1| exact WM1|]. cbn. unfold zlength in ZLE. clear - OUTR OA1 ZLE OUTL SPR LO16. lia. }
    assert (METHB1 : METH_b64 m1).
    { unfold METH_b64 in METHBx |- *. eapply rw_cells_transport; [exact METHBx| exact MU1| exact WM1|]. unfold A_b64_method, O_METH_BREAD. cbn. clear - CEIL HCEILB AI SPR LO16. lia. }
    assert (METHM1 : METH_mem m1).
    { unfold METH_mem in METHMx |- *. eapply rw_cells_transport; [exact METHMx| exact MU1| exact WM1|]. unfold A_mem_buf_method, O_METH_BREAD. cbn. clear - CEIL HCEILB AI SPR LO16. lia. }
    destruct (b64ctx_used_of_exit _ _ _ _ _ _ _ _ _ HD1 BUF1 TMP1 TAIL1) as (USED1 & LH1 & LJ1 & CONT1).
    assert (MUf : munch ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m m1).
    { apply (munch_trans _ m m3 m1 MU). apply (munch_trans _ m3 m' m1).
      - eapply munch_weaken; [| exact MUx]. clear. unfold sub_fp, B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [outside app]. intros x Hx. lia.
      - eapply munch_weaken; [| exact MU1]. clear - LO16. unfold sub_fp, B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [outside app]. intros x Hx. lia. }
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM WMx) WM1) as WMf.
    apply evt_done. unfold b64rd_post.
    eexists g0, g1, g2, h1, h2, h3, h4, h5, h6, h7, g3, g4, g5, g6, m1, (Z.lor (Z.land (bf_flags R) (Z.lnot 15)) (fl' mod 16)), 0, c', fl', nr', d', _, _, jo'.
    split. { rewrite <- RV. reflexivity. }
    split. { exact MUf. }
    split; [exact WMf|]. split; [exact MI1|]. split; [exact ST1|].
    split. { rewrite NR0. unfold b64f_bio, bf_with_hdr, bio_copy_retry in BC1 |- *.
             cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite membio_bio mset
                  mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc] in BC1 |- *.
             exact BC1. }
    split. { apply lor_lt_pow2; [exact FL1|]. pose proof (Z.mod_pos_bound fl' 16 ltac:(lia)). clear - H. lia. }
    split; [clear; lia|].
    split; [exact LH1|]. split; [exact LJ1|]. split; [exact USED1|]. split; [exact CONT1|].
    split; [exact CR|].
    split. { intros E. rewrite RV in E. destruct (Z.eqb_spec (zlength (br_out res)) 0) as [E0|E0]; clear - E CLE E0 ZNN RCF; lia. }
    split. { rewrite RV. destruct (zlength (br_out res) =? 0); clear - RCF ZLE ZNN OUTL; lia. }
    split; [exact ZLE|].
    split; [exact ENC1|]. split; [exact MB1|]. split; [exact TXT1|]. split; [exact OUT1|]. split; [exact METHB1|]. split; [exact METHM1|]. exact I.
  Qed.
End S.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit Z_adler32.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_adler32.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_READBUF_STACK : Z := 48 + 128.


Definition rb1_adler (s : deflate_state) (b : Z) : Z :=
  if ds_wrap s =? 1 then adler32_len1 (cs_adler (ds_strm s)) b else cs_adler (ds_strm s).

Lemma rb1_cells : forall L s b p1 p2 p3 resv,
  zs_call_cells L (rb1_strm s b) p1 p2 p3 resv =
  [C8 (wz (dl_NI L + (cs_next_in (ds_strm s) + 1))); C4 (wz (cs_avail_in (ds_strm s) - 1)); CB 4 p1;
   C8 (wz (wrap64 (cs_total_in (ds_strm s) + 1)));
   C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm s))))); C4 (wz (cs_avail_out (ds_strm s))); CB 4 p2;
   C8 (wz (cs_total_out (ds_strm s)));
   C8 (wz (msg_ptr (cs_msg (ds_strm s)))); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
   C4 (wz (cs_data_type (ds_strm s))); CB 4 p3; C8 (wz (rb1_adler s b)); C8 resv].
Proof.
  intros. unfold zs_call_cells, zs_priv_cells, rb1_strm, rb1_adler. destruct (ds_wrap s =? 1); reflexivity.
Qed.

Lemma firstn1_skipn_map : forall {A B} (f : A -> B) (l : list A) k d, (k < length l)%nat ->
  firstn 1 (skipn k (map f l)) = [f (nth k l d)].
Proof.
  intros A B f l. induction l as [|x l IH]; intros [|k] d Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma din_byte : forall m L inp i, din m L inp -> 0 <= i < zlength inp ->
  bytes_at usegs m (dl_NI L + i) [Z_to_bv 8 (nth (Z.to_nat i) inp 0)].
Proof.
  intros m L inp i D Hi. unfold din in D. unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) (zb8 inp)) in D. apply bytes_at_app in D. destruct D as [_ D].
  rewrite length_firstn, zb8_length in D. replace (Z.of_nat (Nat.min (Z.to_nat i) (length inp))) with i in D by lia.
  rewrite <- (firstn_skipn 1 (skipn (Z.to_nat i) (zb8 inp))) in D. apply bytes_at_app in D. destruct D as [D _].
  unfold zb8 in D. rewrite (firstn1_skipn_map (Z_to_bv 8) inp (Z.to_nat i) 0) in D by lia. exact D.
Qed.

Lemma arr_get_of_list_nth : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.

Lemma av8_set1 : forall a n k v (s : nat), 0 <= k < n -> n <= arr_len a -> s = S (Z.to_nat k) ->
  firstn (Z.to_nat k) (av8 a n) ++ [Z_to_bv 8 v] ++ skipn s (av8 a n) = av8 (arr_set a k v) n.
Proof.
  intros a n k v s Hk Hn ->. rewrite <- av8_upd by assumption. rewrite upd_firstn_skipn by (rewrite av8_length; lia). reflexivity.
Qed.

Lemma u8arr_join3z : forall m A (b1 b2 b3 : list byte) (k n : Z), Z.of_nat (length b1) = k -> Z.of_nat (length b2) = n ->
  u8arr usegs m A b1 -> rw_cells usegs m (A + k) [CB (Z.to_nat n) b2] -> u8arr usegs m (A + k + n) b3 -> u8arr usegs m A (b1 ++ b2 ++ b3).
Proof.
  intros m A b1 b2 b3 k n L1 L2 H1 H2 H3. apply (u8arr_join3 _ A b1 b2 b3 (Z.to_nat n)); [exact H1| |].
  - rewrite L1. exact H2.
  - rewrite L1. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact H3.
Qed.


Ltac with_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
Ltac name_mem id := with_mem ltac:(fun mm => rename mm into id).

Ltac join_x9 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode ?A ?x1 (TNode (TNode ?B (Some _) ?C) ?x5 ?D)) None ?E) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode (TNode A x1 (TNode (TNode B (Some v) C) x5 D)) None E) F (wz pcj) fc None m rom))
  end.


Definition read_buf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (more : Z) (inp : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (snd (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + DS_WIN)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fst (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more)) /\ din m' L inp.

Lemma read_buf_spec : forall (L : dlay) (X : deflate_state) (inp : list Z) (nout lo more D : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L X -> din m L inp -> din_tie inp X -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_READBUF_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) nout lo ->
  fw_wf 32768 32768 X -> ds_wrap X <> 2 -> cs_avail_in (ds_strm X) = 1 ->
  0 <= more < 2^32 -> ds_strstart X + ds_lookahead X + more <= 65536 ->
  D = dl_Aw L + (ds_strstart X + ds_lookahead X) ->
  evt usegs (read_buf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X more inp lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_S L)) (wz D) (wz more) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_READ_BUF) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DR DIN TIE MI STK LO SP16 BEL IO FW W2 A1 RM SLM ED. unfold Z_READ_BUF, Z_READBUF_STACK in *. subst D.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof FW as FW0. destruct FW as [_ _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ _ Wni Wai Winl Wti Wwr Wad1 _ _ _ _ Wib].
  destruct TIE as [TIE1 TIE2]. rewrite TIE1, arr_len_of_list in Winl. rewrite TIE1, arr_len_of_list in Wib.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  open_DST ST. open_A GA. open_zs ZS.
  carve_frame 48%nat STK.
  do 6 zs.
  gF. zstep. zstep. al8 (dl_S L). gF.
  zstep.
  zs.
  zs. zstep. join_x9 (wz (Z.min (cs_avail_in (ds_strm X)) more)) 0x193fc.
  { if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. rewrite Z.min_l by lia. reflexivity.
    - zstep. apply evt_done. rewrite Z.min_r by lia. reflexivity. }
  intros ms' ->.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    assert (M0 : more = 0) by lia. subst more. replace (Z.min (cs_avail_in (ds_strm X)) 0) with 0 by lia.
    assert (RB0 : read_buf X (RB_window (ds_strstart X + ds_lookahead X)) 0 = (X, 0)) by (unfold read_buf; rewrite A1; reflexivity).
    zstep. do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mE. tr_groups MUf WM.
    apply evt_done. unfold read_buf_post. rewrite RB0. cbn [fst snd]. do 14 eexists. exists mE.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|]. split; [split|].
    - exists zp1, zp2, zp3, zresv. exact ZS.
    - constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    - unfold din in *. eapply bytes_at_transport; [exact DIN| exact MUf| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]. }
  rewrite Z.min_l by lia. rewrite A1.
  pose proof (Wib (cs_next_in (ds_strm X)) ltac:(lia)) as Hb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (din_byte mm L inp (cs_next_in (ds_strm X))) as SRC end.
  lazymatch type of DIN with din ?m1 _ _ => lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DIN1 : din mm L inp) by (pose proof (io_iw _ _ _ _ IO) as JW; unfold apart in JW; unfold din in *; eapply bytes_at_transport;
      [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]) end end.
  specialize (SRC DIN1 ltac:(lia)). clear DIN1.
  rewrite <- (arr_get_of_list_nth inp (cs_next_in (ds_strm X))) in SRC by lia.
  remember (arr_get (arr_of_list inp) (cs_next_in (ds_strm X))) as b eqn:Eb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (dwin_munch m mm L X [(lo, bv_unsigned sp)]) in Gwin; [| exact MUf| exact WM| cbn [disjoint_from]; slia] end.
  clear MUf. open_win Gwin.
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_strstart X + ds_lookahead X)) (Z.to_nat 1) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin LW.
  remember (firstn (Z.to_nat (ds_strstart X + ds_lookahead X)) (av8 (ds_window X) 65536)) as w1 eqn:Ew1.
  assert (LO1 : Z.of_nat (length w1) = ds_strstart X + ds_lookahead X) by (rewrite Ew1, length_firstn, av8_length; lia).
  remember (skipn (Z.to_nat (ds_strstart X + ds_lookahead X) + Z.to_nat 1) (av8 (ds_window X) 65536)) as w3 eqn:Ew3.
  assert (LO3 : Z.of_nat (length w3) = 65536 - (ds_strstart X + ds_lookahead X) - 1) by (rewrite Ew3, length_skipn, av8_length; lia).
  replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_strstart X + ds_lookahead X))) with (dl_Aw L + (ds_strstart X + ds_lookahead X)) in O2 by lia.
  replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_strstart X + ds_lookahead X)) + Z.of_nat (Z.to_nat 1)) with (dl_Aw L + (ds_strstart X + ds_lookahead X) + 1) in O3 by lia.
  zs. zs. zs. zs. zs. rewrite ?Z.mod_small by lia. zstep. zstep.
  zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (memcpy_Z (dl_Aw L + (ds_strstart X + ds_lookahead X)) (dl_NI L + cs_next_in (ds_strm X)) 1);
                      [exact SRC| reflexivity| exact O2| zsep| eassumption| lia| lia| lia]
                    | clear O2 SRC; post_call segs mm ] end.
  name_mem mc.
  pose proof (proj1 (u8arr_of_rw_cells usegs mc _ _ _ PC)) as BY.
  pose proof (u8arr_join3z mc (dl_Aw L) w1 [Z_to_bv 8 b] w3 _ 1 LO1 eq_refl O1 PC O3) as WIN. clear O1 PC O3 LO1 LO3 POST. subst w1 w3.
  rewrite (av8_set1 (ds_window X) 65536 (ds_strstart X + ds_lookahead X) b) in WIN by lia.
  assert (LWF : Z.of_nat (length (av8 (arr_set (ds_window X) (ds_strstart X + ds_lookahead X) b) 65536)) = 65536) by (rewrite av8_length; lia).
  zs. gF. zstep. al8 (dl_As L). gF.
  zs. zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zstep.
  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = rb1_adler X b ->
    rw_cells usegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X))); C4 (wz 0); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X)));
       C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X))))); C4 (wz (cs_avail_out (ds_strm X))); CB 4 zp2;
       C8 (wz (cs_total_out (ds_strm X))); C8 (wz (msg_ptr (cs_msg (ds_strm X)))); C8 (wz (dl_As L));
       C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz (cs_data_type (ds_strm X))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells usegs mA (dl_As L) (dsA_cells L X hA1 hA2 hA3 hA4 hA5) ->
    u8arr usegs mA (dl_Aw L) (av8 (arr_set (ds_window X) (ds_strstart X + ds_lookahead X) b) 65536) ->
    rw_cells usegs mA (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mA lo (bv_unsigned sp + -48) ->
    munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m mA -> wmono usegs m mA -> mem_inv usegs mA ->
    evt usegs (read_buf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X more inp lo m)
      (MS (mkR v1 (wz (bv_unsigned sp + -48)) gp tp v5 v6 v7 (wz (dl_S L)) (wz 1) v10 v11 v12 v13 v14 v15 v16 v17
               (wz 1) (wz (dl_Aw L + (ds_strstart X + ds_lookahead X))) s4 s5 s6 s7 s8 s9 s10 s11 v28 v29 v30 v31)
          F (wz 0x1946c) fc None mA (seg_rom usegs))).
  { clear ZS GA WIN BY FR STK MU WM LWF. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA WIN FR STK MU WM MI. unfold dsA_cells in GA.
    pose proof (av8_zlength (arr_set (ds_window X) (ds_strstart X + ds_lookahead X) b) 65536 ltac:(lia)) as LWF.
    zs. zstep. gF. gF. gF. zs. zstep. zs. zs. zstep.
    do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mB. tr_groups MU WM.
    apply evt_done. unfold read_buf_post.
    rewrite (read_buf_eq1 X _ more A1 ltac:(lia) W2). cbn [fst snd]. rewrite TIE1, <- Eb.
    do 14 eexists. exists mB.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [split|].
    - exists zp1, zp2, zp3, zresv. cbn [ds_strm set_strm]. rewrite rb1_cells, <- EADL, A1. close_cells ZS.
    - constructor.
      + exists hA1, hA2, hA3, hA4, hA5. unfold dsA_cells. dsred. close_cells GA.
      + exact GB. + exact GC. + exact GD. + exact Glt. + exact Gdt. + exact Gbt. + exact Gblc. + exact Gheap. + exact Gdep.
      + unfold dwin. dsred. exact WIN.
      + exact Gprev. + exact Ghead. + exact Gpend.
      + destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
        constructor; dsred; rewrite ?arr_len_set; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11|exact l12|exact l13].
      + exact LAY.
    - pose proof (io_iw _ _ _ _ IO) as JW. unfold apart in JW. unfold din in *.
      eapply bytes_at_transport; [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]. }
  zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  -
    apply (KJ mc (cs_adler (ds_strm X))); [unfold rb1_adler; replace (ds_wrap X =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| exact STK| exact MU| exact WM| assumption].
  -
    zs. zstep. zstep. zstep.
    remember (wz (bv_unsigned sp + -48)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned sp + -48) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_len1_spec lo). 1:{ apply Wad1; exact K4. } 1:{ lia. } 1:{ lia. } 1:{ exact Hb. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK1 end.
    subst spw.
    zstep. zs. name_mem md.
    apply (KJ md (adler32_len1 (cs_adler (ds_strm X)) b)); [unfold rb1_adler; rewrite K4; reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| exact STK1| exact MU| exact WM| assumption].
Qed.

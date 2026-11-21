(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_tr_kit Z_defl_iface Z_fw_model Zg_fw_model Z_ukit Z_adler32 Zg_adler32_iface Z_readbuf.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel AdlerModel RefDeflStored1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arr_slice_of_list : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
  arr_slice (arr_of_list l) i n = firstn (Z.to_nat n) (skipn (Z.to_nat i) l).
Proof.
  intros l i n Hi Hn Hin. unfold zlength in Hin. apply (nth_ext _ _ 0 0).
  - rewrite arr_slice_length', length_firstn, length_skipn. lia.
  - intros k Hk. rewrite arr_slice_length' in Hk. unfold arr_slice. rewrite arr_slice_nat_nth by exact Hk.
    rewrite arr_get_of_list_nth by lia. rewrite nth_firstn, nth_skipn. replace (k <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
    f_equal. lia.
Qed.

Lemma din_bytes : forall m L inp i n, din m L inp -> 0 <= i -> 0 <= n -> i + n <= zlength inp ->
  bytes_at usegs m (dl_NI L + i) (zb8 (arr_slice (arr_of_list inp) i n)).
Proof.
  intros m L inp i n D Hi Hn Hin. unfold din in D. unfold zlength in Hin.
  rewrite (arr_slice_of_list inp i n Hi Hn ltac:(unfold zlength; lia)).
  rewrite <- (firstn_skipn (Z.to_nat i) (zb8 inp)) in D. apply bytes_at_app in D. destruct D as [_ D].
  rewrite length_firstn, zb8_length in D. replace (Z.of_nat (Nat.min (Z.to_nat i) (length inp))) with i in D by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) (zb8 inp))) in D. apply bytes_at_app in D. destruct D as [D _].
  unfold zb8 in *. rewrite skipn_map, firstn_map in D. exact D.
Qed.

(* [comment removed for export] *)
Lemma adler32_call : adler32_stmt -> forall (adler B lo : Z) (d : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
    bytes_at usegs m B d -> mem_inv usegs m ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
    (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
    evt usegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz (Z.of_nat (length d))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof. intros H. intros. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Ltac set_x12 v E :=
  lazymatch goal with
  | |- evt ?sg ?Q (MS (TNode ?Lt None (TNode (TNode ?A ?o4 (TNode ?B (Some ?old) ?C)) ?o2 ?D)) ?F ?pc ?fc ?rv ?m ?rom) =>
      replace (MS (TNode Lt None (TNode (TNode A o4 (TNode B (Some old) C)) o2 D)) F pc fc rv m rom)
         with (MS (TNode Lt None (TNode (TNode A o4 (TNode B (Some v) C)) o2 D)) F pc fc rv m rom) by (rewrite E; reflexivity)
  end.

Ltac name_mem id := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into id end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_buf_win_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (off more : Z) (inp : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (snd (read_buf X (RB_window off) more))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + DS_WIN)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fst (read_buf X (RB_window off) more)) /\ din m' L inp.

Section RB.
Hypothesis HADL : adler32_stmt.

Lemma read_buf_win_spec : forall (L : dlay) (X : deflate_state) (inp : list Z) (nout lo more off D : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L X -> din m L inp -> din_tie inp X -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_READBUF_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) nout lo ->
  arr_len (ds_window X) = 65536 -> 0 <= off -> 0 <= more < 2^31 -> off + more <= 65536 ->
  0 <= ds_wrap X <= 2 -> ds_wrap X <> 2 -> (ds_wrap X = 1 -> 0 <= cs_adler (ds_strm X) < 2^64) ->
  0 <= cs_next_in (ds_strm X) -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) <= zlength inp ->
  0 <= cs_total_in (ds_strm X) < 2^64 ->
  D = dl_Aw L + off ->
  evt usegs (read_buf_win_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X off more inp lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_S L)) (wz D) (wz more) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_READ_BUF) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DR DIN TIE MI STK LO SP16 BEL IO LW OFF RM OM Wwr W2 Wad1 Wni Wai Winl Wti ED. unfold Z_READ_BUF, Z_READBUF_STACK in *. subst D.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  destruct TIE as [TIE1 TIE2].
  assert (Wib : forall i, 0 <= i < zlength inp -> 0 <= arr_get (arr_of_list inp) i < 256).
  { intros i Hi. unfold zlength in Hi. rewrite arr_get_of_list_nth by lia. apply (Forall_nth (fun b => 0 <= b < 256) inp); [exact TIE2| lia]. }
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  open_DST ST. open_A GA. open_zs ZS.
  (* [comment removed for export] *)
  carve_frame 48%nat STK.
  do 6 zs.
  gF. zstep. zstep. al8 (dl_S L). gF.
  zstep.
  zs. (* [comment removed for export] *)
  (* [comment removed for export] *)
  remember (rb_len X more) as n eqn:En.
  pose proof (rb_len_range X more ltac:(lia) ltac:(lia)) as RN. rewrite <- En in RN. destruct RN as (RN1 & RN2 & RN3).
  zs. zstep. join_x9 (wz n) 0x19820.
  { if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. replace n with (cs_avail_in (ds_strm X)) by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity.
    - zstep. apply evt_done. replace n with more by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity. }
  intros ms' ->.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { (* [comment removed for export] *)
    assert (RB0 : read_buf X (RB_window off) more = (X, 0)).
    { unfold read_buf. cbv zeta. replace ((if more <? cs_avail_in (ds_strm X) then more else cs_avail_in (ds_strm X)) =? 0) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. rewrite En in K2. unfold rb_len in K2. exact K2. }
    zstep. do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mE. tr_groups MUf WM.
    apply evt_done. unfold read_buf_win_post. rewrite RB0. cbn [fst snd]. rewrite K2. do 14 eexists. exists mE.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|]. split; [split|].
    - exists zp1, zp2, zp3, zresv. exact ZS.
    - constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    - unfold din in *. eapply bytes_at_transport; [exact DIN| exact MUf| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]. }
  (* [comment removed for export] *)
  assert (Pn : 0 < n) by (destruct (Z.eq_dec n 0) as [E0|E0]; [exfalso; exact (K2 E0)| lia]).
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm X)) n) as l eqn:El.
  assert (Ll : length (zb8 l) = Z.to_nat n) by (rewrite zb8_length, El; apply arr_slice_length').
  assert (Bl : Forall (fun b => 0 <= b < 256) l).
  { rewrite El. apply Forall_forall. intros b Hb. eapply (arr_slice_In (arr_of_list inp) (cs_next_in (ds_strm X)) n b); [| exact Hb].
    intros i Hi. apply Wib. lia. }
  lazymatch type of DIN with din ?m1 _ _ => lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DIN1 : din mm L inp) by (pose proof (io_iw _ _ _ _ IO) as JW; unfold apart in JW; unfold din in *; eapply bytes_at_transport;
      [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]) end end.
  pose proof (din_bytes _ L inp (cs_next_in (ds_strm X)) n DIN1 ltac:(lia) ltac:(lia) ltac:(lia)) as SRC. rewrite <- El in SRC. clear DIN1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (dwin_munch m mm L X [(lo, bv_unsigned sp)]) in Gwin; [| exact MUf| exact WM| cbn [disjoint_from]; slia] end.
  clear MUf. open_win Gwin.
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat off) (Z.to_nat n) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
  rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
  remember (firstn (Z.to_nat off) (av8 (ds_window X) 65536)) as w1 eqn:Ew1.
  assert (LO1 : Z.of_nat (length w1) = off) by (rewrite Ew1, length_firstn, av8_length; lia).
  remember (skipn (Z.to_nat off + Z.to_nat n) (av8 (ds_window X) 65536)) as w3 eqn:Ew3.
  assert (LO3 : Z.of_nat (length w3) = 65536 - off - n) by (rewrite Ew3, length_skipn, av8_length; lia).
  zs. zs. zs. (* [comment removed for export] *) zs. zs. rewrite ?Z.mod_small by lia. zstep. zstep.
  (* [comment removed for export] *)
  zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (memcpy_Z (dl_Aw L + off) (dl_NI L + cs_next_in (ds_strm X)) n);
                      [exact SRC| exact Ll| exact O2| zsep| eassumption| lia| lia| lia]
                    | clear O2 SRC; post_call segs mm ] end.
  name_mem mc.
  pose proof (proj1 (u8arr_of_rw_cells usegs mc _ _ _ PC)) as BY.
  pose proof (u8arr_join3z mc (dl_Aw L) w1 (zb8 l) w3 off n LO1 ltac:(rewrite Ll; lia) O1 PC O3) as WIN. clear O1 PC O3 LO1 LO3 POST. subst w1 w3.
  unfold zb8 in WIN. rewrite El in WIN.
  rewrite (av8_blit' (ds_window X) (arr_of_list inp) 65536 off (cs_next_in (ds_strm X)) n) in WIN by lia.
  rewrite arr_blit_upd, <- El in WIN.
  pose proof (arr_len_blit (ds_window X) off (arr_of_list inp) (cs_next_in (ds_strm X)) n) as LNW.
  rewrite arr_blit_upd, <- El, LW in LNW.
  assert (LWF : Z.of_nat (length (av8 (arr_upd (ds_window X) off l) 65536)) = 65536) by (rewrite av8_length; lia).
  (* [comment removed for export] *)
  zs. gF. zstep. al8 (dl_As L). gF.
  zs. zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zstep.
  (* [comment removed for export] *)
  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = rbn_adler X l ->
    rw_cells usegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X))); C4 (wz (cs_avail_in (ds_strm X) - n)); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X)));
       C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X))))); C4 (wz (cs_avail_out (ds_strm X))); CB 4 zp2;
       C8 (wz (cs_total_out (ds_strm X))); C8 (wz (msg_ptr (cs_msg (ds_strm X)))); C8 (wz (dl_As L));
       C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz (cs_data_type (ds_strm X))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells usegs mA (dl_As L) (dsA_cells L X hA1 hA2 hA3 hA4 hA5) ->
    u8arr usegs mA (dl_Aw L) (av8 (arr_upd (ds_window X) off l) 65536) ->
    rw_cells usegs mA (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mA lo (bv_unsigned sp + -48) ->
    munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m mA -> wmono usegs m mA -> mem_inv usegs mA ->
    evt usegs (read_buf_win_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X off more inp lo m)
      (MS (mkR v1 (wz (bv_unsigned sp + -48)) gp tp v5 v6 v7 (wz (dl_S L)) (wz n) v10 v11 v12 v13 v14 v15 v16 v17
               (wz n) (wz (dl_Aw L + off)) s4 s5 s6 s7 s8 s9 s10 s11 v28 v29 v30 v31)
          F (wz 0x19890) fc None mA (seg_rom usegs))).
  { clear ZS GA WIN BY FR STK MU WM LWF. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA WIN FR STK MU WM MI. unfold dsA_cells in GA.
    pose proof (av8_zlength (arr_upd (ds_window X) off l) 65536 ltac:(lia)) as LWF.
    zs. zstep. gF. gF. gF. zs. zstep. zs. zs. zstep.
    do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mB. tr_groups MU WM.
    apply evt_done. unfold read_buf_win_post.
    rewrite (read_buf_eqn X off more n En Pn W2). cbn [fst snd]. rewrite TIE1, <- El.
    do 14 eexists. exists mB.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [split|].
    - exists zp1, zp2, zp3, zresv. cbn [ds_strm set_strm]. rewrite rbn_cells, <- EADL. close_cells ZS.
    - constructor.
      + exists hA1, hA2, hA3, hA4, hA5. unfold dsA_cells. dsred. close_cells GA.
      + exact GB. + exact GC. + exact GD. + exact Glt. + exact Gdt. + exact Gbt. + exact Gblc. + exact Gheap. + exact Gdep.
      + unfold dwin. dsred. exact WIN.
      + exact Gprev. + exact Ghead. + exact Gpend.
      + destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
        constructor; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact LNW|exact l11|exact l12|exact l13].
      + exact LAY.
    - pose proof (io_iw _ _ _ _ IO) as JW. unfold apart in JW. unfold din in *.
      eapply bytes_at_transport; [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]. }
  zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  - (* [comment removed for export] *)
    apply (KJ mc (cs_adler (ds_strm X))); [unfold rbn_adler; replace (ds_wrap X =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| exact STK| exact MU| exact WM| assumption].
  - (* [comment removed for export] *)
    zs. zstep. zstep. zstep.
    assert (E12 : wz n = wz (Z.of_nat (length (zb8 l)))) by (rewrite Ll; f_equal; lia).
    set_x12 (wz (Z.of_nat (length (zb8 l)))) E12. clear E12.
    (* [comment removed for export] *)
    remember (wz (bv_unsigned sp + -48)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned sp + -48) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_call HADL (cs_adler (ds_strm X)) (dl_Aw L + off) lo (zb8 l)).
    1:{ apply Wad1; exact K4. } 1:{ lia. } 1:{ rewrite Ll. lia. } 1:{ rewrite Ll. lia. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ rewrite Ll. lia. }
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK1 end.
    subst spw.
    replace (adler32_z_spec (cs_adler (ds_strm X)) (dl_Aw L + off) (zb8 l)) with (adler32_upd (cs_adler (ds_strm X)) l)
      by (symmetry; apply adler32_upd_spec; [pose proof (Wad1 K4); lia | lia | exact Bl]).
    zstep. zs. name_mem md.
    apply (KJ md (adler32_upd (cs_adler (ds_strm X)) l)); [unfold rbn_adler; rewrite K4; reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| exact STK1| exact MU| exact WM| assumption].
Qed.
End RB.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rbo_strm (s : deflate_state) (l : list Z) (n : Z) : cstrm :=
  let st := cs_emit (cset_avail_in (ds_strm s) (cs_avail_in (ds_strm s) - n)) l in
  let st2 := if ds_wrap s =? 1 then cset_adler st (adler32_upd (cs_adler (ds_strm s)) l) else st in
  cset_total_in (cset_next_in st2 (cs_next_in (ds_strm s) + n)) (wrap64 (cs_total_in (ds_strm s) + n)).

Lemma read_buf_eqo : forall s more n, n = rb_len s more -> 0 < n -> ds_wrap s <> 2 ->
  read_buf s RB_next_out more = (set_strm s (rbo_strm s (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) n), n).
Proof.
  intros s more n En Pn W2. unfold read_buf, rbo_strm. unfold rb_len in En. cbv zeta. rewrite <- En.
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ds_wrap s =? 2) with false by (symmetry; apply Z.eqb_neq; exact W2).
  destruct (ds_wrap s =? 1); reflexivity.
Qed.

(* [comment removed for export] *)
Definition rbo_zs (L : dlay) (X : deflate_state) (l : list Z) (n : Z) (p1 p2 p3 : list byte) (resv : word) : list cell :=
  [C8 (wz (dl_NI L + (cs_next_in (ds_strm X) + n))); C4 (wz (cs_avail_in (ds_strm X) - n)); CB 4 p1;
   C8 (wz (wrap64 (cs_total_in (ds_strm X) + n)));
   C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X))))); C4 (wz (cs_avail_out (ds_strm X))); CB 4 p2;
   C8 (wz (cs_total_out (ds_strm X)));
   C8 (wz (msg_ptr (cs_msg (ds_strm X)))); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
   C4 (wz (cs_data_type (ds_strm X))); CB 4 p3; C8 (wz (rbn_adler X l)); C8 resv].

Definition read_buf_out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (more : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let n := rb_len X more in
    let l := arr_slice (cs_input (ds_strm X)) (cs_next_in (ds_strm X)) n in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ (exists p1 p2 p3 resv, rw_cells usegs m' (dl_S L) (if n =? 0 then zs_call_cells L (ds_strm X) p1 p2 p3 resv else rbo_zs L X l n p1 p2 p3 resv))
    /\ DST m' L X /\ din m' L inp
    /\ dout m' L rest0 (if n =? 0 then ds_strm X else cs_emit (ds_strm X) l).

Section RBO.
Hypothesis HADL : adler32_stmt.

(* [comment removed for export] *)
Lemma read_buf_out_spec : forall (L : dlay) (X : deflate_state) (inp : list Z) (rest0 : list byte) (lo more D : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L X -> din m L inp -> din_tie inp X -> dout m L rest0 (ds_strm X) -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_READBUF_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  (Z.of_nat (length (cs_out_rev (ds_strm X))) + more <= Z.of_nat (length rest0)) -> 0 <= more < 2^31 ->
  0 <= ds_wrap X <= 2 -> ds_wrap X <> 2 -> (ds_wrap X = 1 -> 0 <= cs_adler (ds_strm X) < 2^64) ->
  0 <= cs_next_in (ds_strm X) -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) <= zlength inp ->
  0 <= cs_total_in (ds_strm X) < 2^64 ->
  D = dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X))) ->
  evt usegs (read_buf_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X more inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_S L)) (wz D) (wz more) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_READ_BUF) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DR DIN TIE DOUT MI STK LO SP16 BEL IO ROOM RM Wwr W2 Wad1 Wni Wai Winl Wti ED. unfold Z_READ_BUF, Z_READBUF_STACK in *. subst D.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  destruct TIE as [TIE1 TIE2].
  assert (Wib : forall i, 0 <= i < zlength inp -> 0 <= arr_get (arr_of_list inp) i < 256).
  { intros i Hi. unfold zlength in Hi. rewrite arr_get_of_list_nth by lia. apply (Forall_nth (fun b => 0 <= b < 256) inp); [exact TIE2| lia]. }
  unfold dout in DOUT.
  remember (length (cs_out_rev (ds_strm X))) as k eqn:Ek.
  assert (OL : length (outv rest0 (ds_strm X)) = length rest0) by (apply outv_length; rewrite <- Ek; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  open_DST ST. open_A GA. open_zs ZS. rewrite <- Ek in ZS.
  (* [comment removed for export] *)
  carve_frame 48%nat STK.
  do 6 zs.
  gF. zstep. zstep. al8 (dl_S L). gF.
  zstep.
  zs. (* [comment removed for export] *)
  remember (rb_len X more) as n eqn:En.
  pose proof (rb_len_range X more ltac:(lia) ltac:(lia)) as RN. rewrite <- En in RN. destruct RN as (RN1 & RN2 & RN3).
  zs. zstep. join_x9 (wz n) 0x19820.
  { if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. replace n with (cs_avail_in (ds_strm X)) by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity.
    - zstep. apply evt_done. replace n with more by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity. }
  intros ms' ->.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { (* [comment removed for export] *)
    assert (RB0 : read_buf X RB_next_out more = (X, 0)).
    { unfold read_buf. cbv zeta. replace ((if more <? cs_avail_in (ds_strm X) then more else cs_avail_in (ds_strm X)) =? 0) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. rewrite En in K2. unfold rb_len in K2. exact K2. }
    zstep. do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mE. tr_groups MUf WM.
    apply evt_done. unfold read_buf_out_post. cbv zeta. rewrite <- En, K2. cbn [Z.eqb]. do 14 eexists. exists mE.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].
    split; [exists zp1, zp2, zp3, zresv; unfold zs_call_cells, zs_priv_cells; cbn [app]; rewrite <- ?Ek; exact ZS|].
    split; [constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]|].
    split.
    - unfold din in *. eapply bytes_at_transport; [exact DIN| exact MUf| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia].
    - unfold dout. first [exact DOUT | eapply u8arr_agree; [exact DOUT|]; apply (agree_on_of_munch _ _ _ _ _ MUf WM); [lia| rewrite OL; lia| cbn [disjoint_from]; rewrite OL; lia]]. }
  (* [comment removed for export] *)
  assert (Pn : 0 < n) by (destruct (Z.eq_dec n 0) as [E0|E0]; [exfalso; exact (K2 E0)| lia]).
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm X)) n) as l eqn:El.
  assert (Ll : length l = Z.to_nat n) by (rewrite El; apply arr_slice_length').
  assert (LSRC : length (zb8 l) = Z.to_nat n) by (rewrite zb8_length; exact Ll).
  assert (Bl : Forall (fun b => 0 <= b < 256) l).
  { rewrite El. apply Forall_forall. intros b Hb. eapply (arr_slice_In (arr_of_list inp) (cs_next_in (ds_strm X)) n b); [| exact Hb].
    intros i Hi. apply Wib. lia. }
  lazymatch type of DIN with din ?m1 _ _ => lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DIN1 : din mm L inp) by (pose proof (io_io _ _ _ _ IO) as JO; unfold apart in JO; unfold din in *; eapply bytes_at_transport;
      [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia]) end end.
  pose proof (din_bytes _ L inp (cs_next_in (ds_strm X)) n DIN1 ltac:(lia) ltac:(lia) ltac:(lia)) as SRC. rewrite <- El in SRC. clear DIN1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DOUT1 : u8arr usegs mm (dl_NO L) (outv rest0 (ds_strm X)))
      by (first [exact DOUT | eapply u8arr_agree; [exact DOUT|]; apply (agree_on_of_munch _ _ _ _ _ MUf WM); [lia| rewrite OL; lia| cbn [disjoint_from]; rewrite OL; lia]]) end.
  clear MUf DOUT.
  destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat n) DOUT1 ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT1.
  assert (LO1 : length (firstn k (outv rest0 (ds_strm X))) = k) by (rewrite length_firstn, OL; lia).
  assert (LO3 : length (skipn (k + Z.to_nat n) (outv rest0 (ds_strm X))) = (length rest0 - (k + Z.to_nat n))%nat) by (rewrite length_skipn, OL; lia).
  zs. zs. zs. (* [comment removed for export] *) zs. zs. rewrite ?Z.mod_small by lia. zstep. zstep.
  (* [comment removed for export] *)
  zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (memcpy_Z (dl_NO L + Z.of_nat k) (dl_NI L + cs_next_in (ds_strm X)) n);
                      [exact SRC| exact LSRC| exact O2| zsep| eassumption| lia| lia| lia]
                    | clear O2 SRC; post_call segs mm ] end.
  name_mem mc.
  pose proof (proj1 (u8arr_of_rw_cells usegs mc _ _ _ PC)) as BY.
  pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat n) LO1 O1 PC O3) as OUT. clear O1 PC O3 LO1 LO3 POST.
  rewrite <- Ll in OUT. rewrite Ek in OUT.
  rewrite <- outv_emit in OUT by (rewrite <- Ek, Ll; lia).
  assert (OL' : length (outv rest0 (cs_emit (ds_strm X) l)) = length rest0) by (apply outv_length; rewrite cs_emit_out_len, Ll, <- Ek; lia).
  (* [comment removed for export] *)
  zs. gF. zstep. al8 (dl_As L). gF.
  zs. zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zstep.
  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = rbn_adler X l ->
    rw_cells usegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X))); C4 (wz (cs_avail_in (ds_strm X) - n)); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X)));
       C8 (wz (dl_NO L + Z.of_nat k)); C4 (wz (cs_avail_out (ds_strm X))); CB 4 zp2;
       C8 (wz (cs_total_out (ds_strm X))); C8 (wz (msg_ptr (cs_msg (ds_strm X)))); C8 (wz (dl_As L));
       C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz (cs_data_type (ds_strm X))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells usegs mA (dl_As L) (dsA_cells L X hA1 hA2 hA3 hA4 hA5) ->
    u8arr usegs mA (dl_NO L) (outv rest0 (cs_emit (ds_strm X) l)) ->
    rw_cells usegs mA (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mA lo (bv_unsigned sp + -48) ->
    munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m mA -> wmono usegs m mA -> mem_inv usegs mA ->
    evt usegs (read_buf_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X more inp rest0 lo m)
      (MS (mkR v1 (wz (bv_unsigned sp + -48)) gp tp v5 v6 v7 (wz (dl_S L)) (wz n) v10 v11 v12 v13 v14 v15 v16 v17
               (wz n) (wz (dl_NO L + Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 v28 v29 v30 v31)
          F (wz 0x19890) fc None mA (seg_rom usegs))).
  { clear ZS GA OUT BY FR STK MU WM OL'. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA OUT FR STK MU WM MI. unfold dsA_cells in GA.
    pose proof (outv_length rest0 (cs_emit (ds_strm X) l) ltac:(rewrite cs_emit_out_len, Ll, <- Ek; lia)) as OL2.
    zs. zstep. gF. gF. gF. zs. zstep. zs. zs. zstep.
    do 6 zs. release_frame FR STK (bv_unsigned sp). zs.
    name_mem mB. tr_groups MU WM.
    apply evt_done. unfold read_buf_out_post. cbv zeta. rewrite <- En, TIE1, <- El.
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    do 14 eexists. exists mB.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
    split; [exists zp1, zp2, zp3, zresv; unfold rbo_zs; rewrite <- EADL, <- Ek; close_cells ZS|].
    split; [constructor; [exists hA1, hA2, hA3, hA4, hA5; unfold dsA_cells; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]|].
    split.
    - pose proof (io_io _ _ _ _ IO) as JO. unfold apart in JO. unfold din in *.
      eapply bytes_at_transport; [exact DIN| exact MU| cbn [disjoint_from]; rewrite zb8_length; unfold zlength in *; lia].
    - unfold dout. exact OUT. }
  zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  - (* [comment removed for export] *)
    apply (KJ mc (cs_adler (ds_strm X))); [unfold rbn_adler; replace (ds_wrap X =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact OUT| exact FR| exact STK| exact MU| exact WM| assumption].
  - (* [comment removed for export] *)
    zs. zstep. zstep. zstep.
    assert (E12 : wz n = wz (Z.of_nat (length (zb8 l)))) by (rewrite LSRC; f_equal; lia).
    set_x12 (wz (Z.of_nat (length (zb8 l)))) E12. clear E12.
    remember (wz (bv_unsigned sp + -48)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned sp + -48) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_call HADL (cs_adler (ds_strm X)) (dl_NO L + Z.of_nat k) lo (zb8 l)).
    1:{ apply Wad1; exact K4. } 1:{ lia. } 1:{ rewrite LSRC. lia. } 1:{ rewrite LSRC. lia. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ rewrite LSRC. lia. }
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK1 end.
    subst spw.
    replace (adler32_z_spec (cs_adler (ds_strm X)) (dl_NO L + Z.of_nat k) (zb8 l)) with (adler32_upd (cs_adler (ds_strm X)) l)
      by (symmetry; apply adler32_upd_spec; [pose proof (Wad1 K4); lia | lia | exact Bl]).
    zstep. zs. name_mem md.
    apply (KJ md (adler32_upd (cs_adler (ds_strm X)) l)); [unfold rbn_adler; rewrite K4; reflexivity
      | exact ZS| exact GA| exact OUT| exact FR| exact STK1| exact MU| exact WM| assumption].
Qed.
End RBO.

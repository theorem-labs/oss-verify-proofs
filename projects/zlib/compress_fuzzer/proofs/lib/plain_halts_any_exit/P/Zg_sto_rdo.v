(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_adler32
     Zg_adler32_iface Zg_defl_iface Zg_sto_model Zg_sto_kit Zg_sto_copy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel ZChkAdl AdlerModel
     RefDeflFast1 RefDeflFastM RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma arr_get_of_list_nth' : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.

Lemma arr_slice_of_list : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
  arr_slice (arr_of_list l) i n = firstn (Z.to_nat n) (skipn (Z.to_nat i) l).
Proof.
  intros l i n Hi Hn Hin. unfold zlength in Hin. apply (nth_ext _ _ 0 0).
  - rewrite arr_slice_length', length_firstn, length_skipn. lia.
  - intros k Hk. rewrite arr_slice_length' in Hk. unfold arr_slice. rewrite arr_slice_nat_nth by exact Hk.
    rewrite arr_get_of_list_nth' by lia. rewrite nth_firstn, nth_skipn. replace (k <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
    f_equal. lia.
Qed.

Lemma din_bytes : forall m L inp i n, din m L inp -> 0 <= i -> 0 <= n -> i + n <= zlength inp ->
  bytes_at psegs m (dl_NI L + i) (zb8 (arr_slice (arr_of_list inp) i n)).
Proof.
  intros m L inp i n D Hi Hn Hin. unfold din in D. unfold zlength in Hin.
  rewrite (arr_slice_of_list inp i n Hi Hn ltac:(unfold zlength; lia)).
  rewrite <- (firstn_skipn (Z.to_nat i) (zb8 inp)) in D. apply bytes_at_app in D. destruct D as [_ D].
  rewrite length_firstn, zb8_length in D. replace (Z.of_nat (Nat.min (Z.to_nat i) (length inp))) with i in D by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) (zb8 inp))) in D. apply bytes_at_app in D. destruct D as [D _].
  unfold zb8 in *. rewrite skipn_map, firstn_map in D. exact D.
Qed.

Lemma adler32_call : adler32_stmt -> forall (adler B lo : Z) (d : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
    bytes_at psegs m B d -> mem_inv psegs m ->
    stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 ->
    (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
    evt psegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz (Z.of_nat (length d))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ADLER32) fc None m (seg_rom psegs)).
Proof. intros H. intros. eapply H; eassumption. Qed.

Ltac set_x12 v E :=
  lazymatch goal with
  | |- evt ?sg ?Q (MS (TNode ?Lt None (TNode (TNode ?A ?o4 (TNode ?B (Some ?old) ?C)) ?o2 ?D)) ?F ?pc ?fc ?rv ?m ?rom) =>
      replace (MS (TNode Lt None (TNode (TNode A o4 (TNode B (Some old) C)) o2 D)) F pc fc rv m rom)
         with (MS (TNode Lt None (TNode (TNode A o4 (TNode B (Some v) C)) o2 D)) F pc fc rv m rom) by (rewrite E; reflexivity)
  end.

Section RDO.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HADL : adler32_stmt.

Definition KLATCH (Q : machine_state -> Prop) (last : Z) (X6 : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 1 rest0 lo r me X6 m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (wz last) y19 y20 y21 y22 y27 y28 y29 y30 y31)
                    F (wz Z_STO_LATCH) fc None m' (seg_rom psegs)).

Variables (Q : machine_state -> Prop) (last : Z) (X5 : deflate_state) (n : Z).
Hypothesis TIE : din_tie inp X5.
Hypothesis HV5 : so_inv X5.
Hypothesis WRAP : ds_wrap X5 <> 2.
Hypothesis RWR : 0 <= ds_wrap X5 <= 2.
Hypothesis RAD : 1 <= ds_wrap X5 -> 0 <= cs_adler (ds_strm X5) < 2^64.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X5) < 2^31.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X5) < 2^31.
Hypothesis RNI : 0 <= cs_next_in (ds_strm X5).
Hypothesis RINL : cs_next_in (ds_strm X5) + cs_avail_in (ds_strm X5) <= zlength inp.
Hypothesis RTI : 0 <= cs_total_in (ds_strm X5) < 2^64.
Hypothesis RN : n = 0 \/ (0 < n <= cs_avail_in (ds_strm X5) /\ n <= cs_avail_out (ds_strm X5)).
Hypothesis RM6 : Box (length (cs_out_rev (ds_strm (st_rdo X5 n))) <= length rest0)%nat.
Hypothesis KL : KLATCH Q last (st_rdo X5 n).

Lemma rdo_core : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 1 rest0 lo r me X5 m' -> n <> 0 ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz n) y10 y11 y12 y13 y14 y15 y16 y17 (wz last) y19 y20 y21 y22 y27 y28 y29 y30 y31)
                    F (wz 0x180f0) fc None m' (seg_rom psegs)).
Proof using KL RM6 RN RTI RINL RNI RAO RAI RAD RWR WRAP HV5 TIE HADL CTX inp.
  intros until m'. intros INV NZ.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  unfold KLATCH in KL. destruct TIE as [TIE1 TIE2].
  assert (RNz : 0 <= n < 2^31) by lia.
  assert (RN' : 0 < n <= cs_avail_in (ds_strm X5) /\ n <= cs_avail_out (ds_strm X5)) by lia. clear RN.
  open_DST ST. open_A GA. open_zs ZS.
  zstep. zs. zstep.

  zstep. br_cases K1; [exfalso; lia|]. zstep.
  zstep. zstep. br_cases K2; [exfalso; lia|].
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN.
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X5) (unbox _ RM)) as OL.
  remember (length (cs_out_rev (ds_strm X5))) as k eqn:Ek.
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm X5)) n) as l eqn:El.
  assert (Ll : length l = Z.to_nat n) by (rewrite El; apply arr_slice_length').
  assert (Bl : Forall (fun b => 0 <= b < 256) l).
  { rewrite El, <- TIE1. apply Forall_forall. apply (slice_input_bytes X5); [exact HV5| lia| rewrite TIE1, arr_len_of_list; lia]. }
  assert (KLn : (k + Z.to_nat n <= length rest0)%nat).
  { pose proof (unbox _ RM6) as R6. rewrite (st_rdo_eq X5 n) in R6 by lia. unfold st_rbfin, rb_mid in R6.
    destruct (ds_wrap X5 =? 1); [|destruct (ds_wrap X5 =? 2)]; dsred in R6; rewrite cs_emit_out_len, arr_slice_length' in R6; dsred in R6; lia. }
  pose proof (din_bytes m' L inp (cs_next_in (ds_strm X5)) n DIN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC. rewrite <- El in SRC.
  assert (LSRC : length (zb8 l) = Z.to_nat n) by (rewrite zb8_length; exact Ll).
  destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat n) DOUT ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT.
  assert (LO1 : length (firstn k (outv rest0 (ds_strm X5))) = k) by (rewrite length_firstn, OL; lia).
  assert (LO3 : length (skipn (k + Z.to_nat n) (outv rest0 (ds_strm X5))) = (length rest0 - (k + Z.to_nat n))%nat) by (rewrite length_skipn, OL; lia).
  unfold sto_W, slow_W in MU.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -160); (dl_NO L, dl_NO L + Z.of_nat (length rest0)); (dl_S L, dl_S L + 112)] mc) as MUf;
    pose proof (wmono_refl psegs mc) as WMf end.
  zs. zstep. zs. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. zstep.
  zstep. call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_NI L + cs_next_in (ds_strm X5)) n).
  1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat n) LO1 O1 PC O3) as OUT.
  pose proof (proj1 (u8arr_of_rw_cells psegs _ _ _ _ PC)) as BY.
  rewrite <- Ll in OUT. rewrite Ek in OUT.
  rewrite <- outv_emit in OUT by (rewrite <- Ek, Ll; exact KLn).
  assert (OL' : length (outv rest0 (cs_emit (ds_strm X5) l)) = length rest0).
  { apply outv_length. rewrite cs_emit_out_len, Ll, <- Ek. lia. }
  clear O1 O3 PC POST SRC LO1 LO3.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -160)) = bv_unsigned (r_sp r) + -160) by (apply unsigned_lit; lia).

  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = (if ds_wrap X5 =? 1 then adler32_upd (cs_adler (ds_strm X5)) l else cs_adler (ds_strm X5)) ->
    rw_cells psegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X5))); C4 (wz (cs_avail_in (ds_strm X5) - n)); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X5)));
       C8 (wz (dl_NO L + Z.of_nat k)); C4 (wz (cs_avail_out (ds_strm X5))); CB 4 zp2; C8 (wz (cs_total_out (ds_strm X5)));
       C8 (wz (msg_ptr (cs_msg (ds_strm X5)))); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
       C4 (wz (cs_data_type (ds_strm X5))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells psegs mA (dl_As L) (dsA_cells L X5 hA1 hA2 hA3 hA4 hA5) ->
    u8arr psegs mA (dl_NO L) (outv rest0 (cs_emit (ds_strm X5) l)) ->
    rw_cells psegs mA (bv_unsigned (r_sp r) + -160) (sto_frame j0 flush ai0 1 r) -> stk psegs mA lo (bv_unsigned (r_sp r) + -160) ->
    munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536);
           (dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768); (dl_Ab L, dl_Ab L + 65536); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] me mA ->
    wmono psegs me mA ->
    munch [(lo, bv_unsigned (r_sp r) + -160); (dl_NO L, dl_NO L + Z.of_nat (length rest0)); (dl_S L, dl_S L + 112)] m' mA -> wmono psegs m' mA ->
    mem_inv psegs mA ->
    evt psegs Q
      (MS (stoR L r v1 v5 v6 v7 (wz n) v10 v11 v12 v13 v14 v15 v16 v17
               (wz last) (wz (dl_NO L + Z.of_nat k)) (wz n) (wz n) (wz (dl_S L)) y27 v28 v29 v30 v31)
          F (wz 0x17e9c) fc None mA (seg_rom psegs))).
  { clear ZS GA OUT BY FR STK MU WM MUf WMf OL'. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA OUT FR STK MU WM MUf WMf MI.
    unfold sto_frame in FR. unfold dsA_cells in GA. unfold stoR, stoR7.
    pose proof (outv_length rest0 (cs_emit (ds_strm X5) l) ltac:(rewrite cs_emit_out_len, Ll, <- Ek; lia)) as OL2.
    do 6 zs. zstep. do 11 zs. rewrite ?Z.mod_small by lia.
    tr_groups MUf WMf. eapply KL.
    rewrite (st_rdo_eq X5 n) by lia. unfold st_rbfin, rb_mid. cbv zeta. rewrite TIE1, <- El.
    replace (ds_wrap X5 =? 2) with false by (symmetry; apply Z.eqb_neq; exact WRAP).
    destruct (ds_wrap X5 =? 1); subst adl.
    all: split; [split|];
    [ eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
      rewrite ?rev_append_rev, ?length_app, ?length_rev, ?Ll, <- ?Ek; close_cells ZS
    | constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY]
    | split; [unfold dout; dsred; exact OUT|];
      split; [constructor; dsred; rewrite cs_emit_out_len, Ll; dsred; rewrite <- Ek; exact KLn|];
      split; [eexists; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ]. }

  zstep. zs. zstep. zstep. br_cases K3; [exfalso; lia|].
  zstep. zstep. br_cases K4.
  -
    apply (KJ _ (cs_adler (ds_strm X5))); [replace (ds_wrap X5 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact OUT| exact FR| exact STK| exact MU| exact WM| exact MUf| exact WMf| assumption].
  -
    zstep. zstep. zstep.
    assert (E12 : wz n = wz (Z.of_nat (length (zb8 l)))) by (rewrite zb8_length, Ll; f_equal; lia).
    set_x12 (wz (Z.of_nat (length (zb8 l)))) E12. clear E12.
    zstep. call (adler32_call HADL (cs_adler (ds_strm X5)) (dl_NO L + Z.of_nat k) lo (zb8 l)).
    1:{ apply RAD. lia. } 1:{ lia. } 1:{ rewrite zb8_length, Ll. lia. } 1:{ rewrite zb8_length, Ll. lia. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ rewrite zb8_length, Ll. lia. }
    rewrite ESP in *.
    replace (adler32_z_spec (cs_adler (ds_strm X5)) (dl_NO L + Z.of_nat k) (zb8 l)) with (adler32_upd (cs_adler (ds_strm X5)) l)
      by (symmetry; apply adler32_upd_spec; [pose proof (RAD ltac:(lia)); lia | lia | exact Bl]).
    zstep. zs. name_mem mE.
    apply (KJ mE (adler32_upd (cs_adler (ds_strm X5)) l)); [rewrite K4; reflexivity
      | exact ZS| exact GA| exact OUT| exact FR| assumption| exact MU| exact WM| exact MUf| exact WMf| assumption].
Qed.
Lemma sto_rdo : KRDO L flush ai0 rest0 lo r F fc me Q Z_STO_RDO last X5 n.
Proof using KL RM6 RN RTI RINL RNI RAO RAI RAD RWR WRAP HV5 TIE HADL CTX inp.
  unfold KRDO. intros until m'. intros INV. pose proof KL as KL'. unfold KLATCH in KL'. unfold Z_STO_RDO, stoR, stoR7.
  assert (RNz : 0 <= n < 2^31) by lia.
  zstep. br_cases K.
  - assert (En : n = 0) by lia. rewrite En, st_rdo_0 in KL'. unfold stoR, stoR7 in KL'. eapply KL'. exact INV.
  - eapply rdo_core; [exact INV| lia].
Qed.

Lemma sto_rdo2 : KRDO L flush ai0 rest0 lo r F fc me Q Z_STO_RDO2 last X5 n.
Proof using KL RM6 RN RTI RINL RNI RAO RAI RAD RWR WRAP HV5 TIE HADL CTX inp.
  unfold KRDO. intros until m'. intros INV. pose proof KL as KL'. unfold KLATCH in KL'. unfold Z_STO_RDO2, stoR, stoR7.
  assert (RNz : 0 <= n < 2^31) by lia.
  zstep. br_cases K.
  - eapply rdo_core; [exact INV| lia].
  - zstep. assert (En : n = 0) by lia. rewrite En, st_rdo_0 in KL'. unfold stoR, stoR7 in KL'. eapply KL'. exact INV.
Qed.
End RDO.

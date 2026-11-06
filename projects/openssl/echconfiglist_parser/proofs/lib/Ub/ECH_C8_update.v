(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState ECH_B64 ECH_C1_stmt ECH_C8_stmt ECH_C8_blockA ECH_C8_block ECH_C8_final ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition DU_LOOP : Z := 0x20e4f8.  Definition DU_ERRX : Z := 0x20e4c0.  Definition DU_TAIL : Z := 0x20e628.
Definition DU_ST : Z := 0x20e580.    Definition DU_ADV : Z := 0x20e61c.   Definition DU_EXIT : Z := 0x20e6f0.
Definition DU_RA1 : Z := 0x20e5b0.   Definition DU_RA2 : Z := 0x20e664.   Definition DU_RV : Z := 0x20e6e0.

(* [comment removed for export] *)
Definition du_frame (c0 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


Lemma prefix_join : forall (dout dec : list Z) (bs : list byte),
  firstn (length dec) bs = map b8 dec -> firstn (length (dout ++ dec)) (map b8 dout ++ bs) = map b8 (dout ++ dec).
Proof.
  intros dout dec bs P. rewrite length_app, map_app, firstn_app, length_map, firstn_all2 by (rewrite length_map; lia).
  f_equal. replace (length dout + length dec - length dout)%nat with (length dec) by lia. exact P.
Qed.

Section CTXU.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Definition CTXU (m : mem) (a nn : Z) (raw : list byte) (line : Z) : Prop :=
    rw_cells usegs m a [C4 (wz nn)] /\ u8arr usegs m (a + 4) raw /\ length raw = 80%nat
    /\ rw_cells usegs m (a + 84) [C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]].
  Lemma CTXU_split : forall m a nn raw line, rw_cells usegs m a (ctx_chunk nn raw line) -> CTXU m a nn raw line.
  Proof.
    intros m a nn raw line H. unfold ctx_chunk in H.
    assert (L : length raw = 80%nat) by (destruct H as [[WF _] _]; cbn in WF; tauto).
    change [C4 (wz nn); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz nn)] ++ [CB 80 raw] ++ [C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]]) in H.
    apply rw_cells_app in H. destruct H as [H1 H]. apply rw_cells_app in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H2, H3.
    split; [exact H1|]. split; [apply (u8arr_of_rw_cells usegs m (a + 4) 80 raw); exact H2|]. split; [exact L|].
    replace (a + 84) with (a + Z.of_nat 4 + Z.of_nat 80) by lia. exact H3.
  Qed.
  Lemma CTXU_join : forall m a nn raw line, CTXU m a nn raw line -> rw_cells usegs m a (ctx_chunk nn raw line).
  Proof.
    intros m a nn raw line (H1 & H2 & L & H3). unfold ctx_chunk.
    change [C4 (wz nn); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz nn)] ++ [CB 80 raw] ++ [C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]]).
    apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. cbn [cells_size csize Nat.add]. split.
    - rewrite <- L. apply rw_cells_of_u8arr. exact H2.
    - replace (a + Z.of_nat 4 + Z.of_nat 80) with (a + 84) by lia. exact H3.
  Qed.
End CTXU.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive cclass : Type := CErr | CEof (e1 : Z) | CGo (d1 : list Z) (e1 : Z).
Definition classify (d : list Z) (eof c : Z) : cclass :=
  let v := a2b c in
  if v =? B64_ERROR then CErr else
  let e1 := if c =? CH_EQ then eof + 1 else eof in
  if negb (c =? CH_EQ) && (0 <? eof) && b64_base64 v then CErr else
  if 2 <? e1 then CErr else
  if v =? B64_EOF then CEof e1 else
  CGo (if b64_base64 v then d ++ [c] else d) e1.
Lemma du_step_classify : forall d eof dout c, (length d < 64)%nat ->
  du_step (mkDU d eof dout) c =
  match classify d eof c with
  | CErr => DUerr d
  | CEof e1 => DUeof (mkDU d e1 dout)
  | CGo d1 e1 =>
      if Nat.eqb (length d1) 64 then
        match decodeblock d1 e1 with
        | None => DUerr []
        | Some bs => if Nat.eqb (length bs) 0 && (0 <? e1) then DUerr [] else DUcont (mkDU [] e1 (dout ++ bs))
        end
      else DUcont (mkDU d1 e1 dout)
  end.
Proof.
  intros d eof dout c L. unfold du_step, classify. cbn [du_d du_eof du_out].
  destruct (a2b c =? B64_ERROR); [reflexivity|].
  destruct (negb (c =? CH_EQ) && (0 <? eof) && b64_base64 (a2b c)); [reflexivity|].
  destruct (2 <? (if c =? CH_EQ then eof + 1 else eof)); [reflexivity|].
  destruct (a2b c =? B64_EOF); [reflexivity|].
  replace (Nat.leb 64 (length d)) with false by (symmetry; apply Nat.leb_gt; lia). rewrite andb_false_r. reflexivity.
Qed.
(* [comment removed for export] *)
Definition nb_landb (c : Z) : bool := Bool.eqb (Z.land (a2b c) 236 =? 224) (negb (b64_base64 (a2b c))) && (0 <=? a2b c) && (a2b c <? 256).
Lemma a2b_facts : forall c, 0 <= c < 128 -> (Z.land (a2b c) 236 =? 224) = negb (b64_base64 (a2b c)) /\ 0 <= a2b c < 256.
Proof.
  intros c Hc. pose proof (zall_ok 128 nb_landb ltac:(vm_compute; reflexivity) c Hc) as K. unfold nb_landb in K.
  apply andb_prop in K. destruct K as [K K3]. apply andb_prop in K. destruct K as [K1 K2].
  apply Bool.eqb_prop in K1. apply Z.leb_le in K2. apply Z.ltb_lt in K3. split; [exact K1| lia].
Qed.
Lemma a2b_high : forall c, 128 <= c -> a2b c = B64_ERROR.
Proof. intros c Hc. unfold a2b. replace (128 <=? c) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma sxb_big : forall b : byte, 128 <= bv_unsigned b -> sxb b = Z_to_bv 64 (bv_unsigned b - 256).
Proof.
  intros b Hb. unfold sxb. f_equal. unfold bv_signed, bv_swrap. pose proof (byte_range b).
  change (bv_half_modulus 8) with 128%Z. change (bv_wrap 8 (bv_unsigned b + 128)) with ((bv_unsigned b + 128) mod bv_modulus 8).
  change (bv_modulus 8) with 256. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma prefix_snoc : forall (raw : list byte) (d : list Z) (cb : byte),
  map bv_unsigned (firstn (length d) raw) = d -> (length d < length raw)%nat ->
  map bv_unsigned (firstn (S (length d)) (upd_bytes raw (length d) [cb])) = d ++ [bv_unsigned cb].
Proof.
  intros raw d cb P L. unfold upd_bytes.
  replace (S (length d)) with (length (firstn (length d) raw ++ [cb])) by (rewrite length_app, length_firstn; cbn; lia).
  rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r, map_app, P. reflexivity.
Qed.

Section U.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (a out outlp inp_a inl lo line nn0 : Z) (inp obs0 : list byte) (LB : list block) (p : bptr).
  Hypothesis A92 : a + 92 <= lo.
  Hypothesis APOS : 0 < a.
  Hypothesis INL : 0 <= inl < 2^20.
  Hypothesis INPL : Z.of_nat (length inp) = inl.
  Hypothesis OSZ : 0 < out.
  Hypothesis OLP : 0 < outlp.          (* [comment removed for export] *)
  Hypothesis OLA : outlp mod 4 = 0.    (* [comment removed for export] *)
  Hypothesis IPOS : 0 < inp_a.         (* [comment removed for export] *)
  Hypothesis IEND : inp_a + inl < 2^64. (* [comment removed for export] *)
  Hypothesis OEND : out + Z.of_nat (length obs0) < 2^64. (* [comment removed for export] *)
  Hypothesis SEPo : out + Z.of_nat (length obs0) <= lo \/ bv_unsigned sp <= out.
  Hypothesis SEPl : outlp + 4 <= lo \/ bv_unsigned sp <= outlp.
  Hypothesis SEPi : inp_a + inl <= lo \/ bv_unsigned sp <= inp_a.
  Hypothesis SEPoa : out + Z.of_nat (length obs0) <= a \/ a + 92 <= out.
  Hypothesis SEPla : outlp + 4 <= a \/ a + 92 <= outlp.
  Hypothesis SEPlo : outlp + 4 <= out \/ out + Z.of_nat (length obs0) <= outlp.
  Hypothesis SEPio : inp_a + inl <= out \/ out + Z.of_nat (length obs0) <= inp_a.
  Hypothesis SEPia : inp_a + inl <= a \/ a + 92 <= inp_a.
  Hypothesis SEPil : inp_a + inl <= outlp \/ outlp + 4 <= inp_a.
  Hypothesis LO : lo <= bv_unsigned sp - 160.    (* [comment removed for export] *)
  Hypothesis AAL : a mod 16 = 0.                  (* [comment removed for export] *)
  Hypothesis LO0 : 0 <= lo.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis LNR : 0 <= line < 2^32.
  Hypothesis NN0 : 0 <= nn0 < 64.
  (* [comment removed for export] *)
  Local Ltac boxsep := box SEPo; box SEPl; box SEPi; box SEPoa; box SEPla; box SEPlo; box SEPio; box SEPia; box SEPil.
  Let WW : list (Z * Z) := [(lo, bv_unsigned sp); (out, out + Z.of_nat (length obs0)); (a, a + 92)].

  (* [comment removed for export] *)
  Definition UST (pc i n eof k : Z) (fl : word) (m : mem) (xra xt0 xa0 xa1 xa4 xa5 xs7 xs9 xt3 xt4 : word) : machine_state :=
    MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 (Z_to_bv 64 k) (Z_to_bv 64 (out + k)) sp (Z_to_bv 64 (inp_a + i)) xa0 xa1
             (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) xa4 xa5 (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 a)
             (Z_to_bv 64 61) (Z_to_bv 64 242) fl (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) xs7 (Z_to_bv 64 64) xs9 (Z_to_bv 64 eof) (Z_to_bv 64 DB_NTAB)
             xt3 xt4 (Z_to_bv 64 2) (Z_to_bv 64 255))
       F (Z_to_bv 64 pc) fc None m (seg_rom usegs).

  (* [comment removed for export] *)
  Definition du_final (m0 : mem) (r : duresult) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' raw obs,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (dr_rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (WW ++ [(outlp, outlp + 4)]) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ CTXU m' a (zlength (dr_d r)) raw line /\ map bv_unsigned (firstn (length (dr_d r)) raw) = dr_d r /\ du_inv (dr_d r)
      /\ u8arr usegs m' out obs /\ length obs = length obs0 /\ firstn (length (dr_out r)) obs = map b8 (dr_out r)
      /\ rw_cells usegs m' outlp [C4 (wz (zlength (dr_out r)))] /\ bytes_at usegs m' inp_a inp.

  (* [comment removed for export] *)
  Lemma du_exit : forall (rax t0 t2 xs1 a0 a1 a4 a5 a6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t5 t6 : word) (m0 m : mem)
      (retv nv rv ov nn : Z) (raw obs : list byte) (dout dd : list Z) (c0 : cell),
      rw_cells usegs m outlp [C4 (wz ov)] -> CTXU m a nn raw line -> rw_cells usegs m (bv_unsigned sp + -112) (du_frame c0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      csize c0 = 8%nat ->
      stk usegs m lo (bv_unsigned sp + -112) -> mem_inv usegs m -> munch WW m0 m -> wmono usegs m0 m ->
      u8arr usegs m out obs -> length obs = length obs0 -> firstn (length dout) obs = map b8 dout -> bytes_at usegs m inp_a inp ->
      map bv_unsigned (firstn (length dd) raw) = dd -> du_inv dd ->
      retv = zlength dout -> nv = zlength dd -> 0 <= retv < 2^31 -> - 1 <= rv <= 1 ->
      evt usegs (du_final m0 (mkDR rv dout dd))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 (Z_to_bv 64 retv) t2 sp xs1 a0 a1 (Z_to_bv 64 outlp) (Z_to_bv 64 nv) a4 a5 a6 (Z_to_bv 64 a)
                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 (Z_to_bv 64 rv) t5 t6)
            F (Z_to_bv 64 DU_EXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until c0. intros OL (C1 & C2 & L80 & C3) FR CS ST MI MU WM OA OLEN OPRE INP DPRE DI -> -> RR RV.
    unfold DU_EXIT. unfold du_frame in FR. pose proof (word_range sp) as SPR. boxsep.
    destruct c0 as [w1|w2|w4|w8|nj j]; cbn in CS; try lia; try subst nj.
    all: pose proof (rw_cells_bound _ _ _ _ OL) as OB; cbn [cells_size csize Nat.add length] in OB;
      pose proof (u8arr_bound _ _ _ _ C2) as EB; pose proof (u8arr_bound _ _ _ _ OA) as AB; rewrite OLEN in AB;
      pose proof (bytes_at_bound _ _ _ _ INP) as IB;
      assert (DL : (length dd < 64)%nat) by (destruct DI as [_ K]; exact K);
      assert (OL64 : (length dout <= length obs0)%nat) by (pose proof (f_equal (@length byte) OPRE) as OP2; rewrite length_map, length_firstn in OP2; lia);
      unfold wz in OL, C1, C3; unfold WW in MU;
      assert (SUBW : sub_fp WW (WW ++ [(outlp, outlp + 4)])) by (unfold WW; intros z Hz; cbn in Hz |- *; clear -Hz; lia);
      apply (munch_weaken _ _ m0 m SUBW) in MU; clear SUBW; unfold WW in MU; cbn [app] in MU;
      (* [comment removed for export] *)
      step; fbr; step; ubal_by OLA; step; if_lit;
      unbox SEPl; unbox SEPla; unbox SEPlo; unbox SEPil; st1; box SEPl; box SEPlo; box SEPil;
      unbox SEPia; unbox SEPoa; st1; box SEPia; box SEPoa; box SEPla;
      step; do 13 st1; step; step;
      release_frame FR ST (bv_unsigned sp);
      apply evt_done; unfold du_final; cbn [dr_rv dr_out dr_d];
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, raw, obs;
      (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact ST|]);
      (split; [split; [unfold wz; exact C1| split; [exact C2| split; [exact L80| exact C3]]]|]);
      (split; [exact DPRE|]); (split; [exact DI|]); (split; [exact OA|]); (split; [exact OLEN|]); (split; [exact OPRE|]);
      (split; [unfold wz; exact OL| exact INP]).
  Qed.

  (* [comment removed for export] *)
  Lemma rv_and : forall (seof : bool) eof n, 0 <= eof -> 0 <= n ->
    Z.land (if seof then 0 else 1) (Z.lor (Z.b2z (eof <? 1)) (Z.b2z (0 <? n))) = (if seof || ((0 <? eof) && (n =? 0)) then 0 else 1).
  Proof.
    intros seof eof n E N. destruct seof, (eof <? 1) eqn:K1, (0 <? eof) eqn:K2, (0 <? n) eqn:K3, (n =? 0) eqn:K4; cbn; try reflexivity; exfalso;
      first [apply Z.ltb_lt in K1| apply Z.ltb_ge in K1]; first [apply Z.ltb_lt in K2| apply Z.ltb_ge in K2];
      first [apply Z.ltb_lt in K3| apply Z.ltb_ge in K3]; first [apply Z.eqb_eq in K4| apply Z.eqb_neq in K4]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma rv_and' : forall (seof : bool) eof n, 0 <= eof -> 0 <= n ->
    Z.land (if seof then 0 else 1) (Z.lor (Z.b2z (eof <? 1)) (Z.b2z (0 <? n))) = (if seof || ((0 <? eof) && (n =? 0)) then 0 else 1).
  Proof. intros. apply rv_and; assumption. Qed.

  (* [comment removed for export] *)
  Lemma out_split : forall m obs k, u8arr usegs m out obs -> (k <= length obs)%nat ->
    u8arr usegs m out (firstn k obs) /\ u8arr usegs m (out + Z.of_nat k) (skipn k obs).
  Proof.
    intros m obs k OA K. apply rw_cells_of_u8arr in OA. apply (rw_cells_CB_split usegs m out _ k obs) in OA; [| exact K].
    destruct OA as [O1 O2]. split; [eapply u8arr_of_rw_cells; exact O1| eapply u8arr_of_rw_cells; exact O2].
  Qed.
  Lemma out_join : forall m o1 o2, u8arr usegs m out o1 -> u8arr usegs m (out + Z.of_nat (length o1)) o2 -> u8arr usegs m out (o1 ++ o2).
  Proof.
    intros m o1 o2 O1 O2. apply rw_cells_of_u8arr in O1. apply rw_cells_of_u8arr in O2.
    eapply u8arr_of_rw_cells. eapply rw_cells_CB_join; [exact O1| exact O2].
  Qed.

  (* [comment removed for export] *)
  Lemma du_tail_walk : forall (i : Z) (xra xt0 xa0 xa1 xa4 xa5 xs7 xs9 xt3 xt4 : word) (m0 m : mem)
      (d dout : list Z) (eof : Z) (seof : bool) (raw obs : list byte) (ov : Z),
      CTXU m a nn0 raw line -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d -> 0 <= eof <= 2 ->
      u8arr usegs m out obs -> length obs = length obs0 -> firstn (length dout) obs = map b8 dout ->
      Z.of_nat (length dout) + 3 * (Z.of_nat (length d) / 4) <= Z.of_nat (length obs0) ->
      Z.of_nat (length dout) + 3 * (Z.of_nat (length d) / 4) < 2^21 ->
      rw_cells usegs m outlp [C4 (wz ov)] -> bytes_at usegs m inp_a inp ->
      rw_cells usegs m (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> stk usegs m lo (bv_unsigned sp + -112) -> mem_inv usegs m ->
      munch WW m0 m -> wmono usegs m0 m ->
      evt usegs (du_final m0 (du_tail (mkDU d eof dout) seof))
        (UST DU_TAIL i (zlength d) eof (zlength dout) (Z_to_bv 64 (if seof then 0 else 1)) m xra xt0 xa0 xa1 xa4 xa5 xs7 xs9 xt3 xt4).
  Proof.
    intros until ov. intros CU DPRE DI ER OA OLEN OPRE CAP CAPB OL INP FR ST MI MU WM.
    unfold UST, DU_TAIL, DB_NTAB, A_data_ascii2bin. pose proof (word_range sp) as SPR. boxsep.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    assert (OL64 : (length dout <= length obs0)%nat).
    { apply (f_equal (@length byte)) in OPRE. rewrite length_map, length_firstn in OPRE. lia. }
    assert (SFR : 0 <= (if seof then 0 else 1) <= 1) by (destruct seof; lia).
    assert (FR' := FR). unfold du_frame in FR'.
    unfold zlength. destruct d as [|d0 drest].
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0. step. try if_lit. step.
      unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi.
      zstep. zstep. zstep. zstep.
      rewrite (rv_and seof eof 0) by lia. change (0 =? 0) with true. rewrite andb_true_r.
      change (du_tail {| du_d := []; du_eof := eof; du_out := dout |} seof) with (mkDR (if seof || (0 <? eof) then 0 else 1) dout []).
      eapply du_exit; try eassumption; try reflexivity; try lia.
      destruct seof; destruct (0 <? eof); cbn; lia.
    - (* [comment removed for export] *)
      set (d := d0 :: drest) in *. assert (DPOS : 0 < Z.of_nat (length d)) by (subst d; cbn; lia).
      step. tbr.
      zstep. change (Z.land (Z.of_nat (length d)) 3) with (Z.land (Z.of_nat (length d)) (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
      step. if_cases EQ1; zify_cond EQ1.
      + (* [comment removed for export] *)
        set (q := Z.of_nat (length d) / 4).
        assert (NQ : Z.of_nat (length d) = 4 * q) by (subst q; lia).
        assert (QR : 1 <= q <= 16) by lia.
        do 5 step. step.
        rewrite NQ.
        destruct (out_split m obs (length dout) OA ltac:(lia)) as [OA1 OA2].
        assert (SAVED : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw))).
        { replace (Z.to_nat (4 * q)) with (length d) by lia. rewrite DPRE. exact (proj1 DI). }
        eapply evt_cut.
        { unbox SEPoa. unbox SEPo.
          eapply (decblock_ok_spec _ (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo) (tj := skipn (length dout) obs); rewrite ?unsigned_lit by lia;
            try eassumption.
          all: try (apply CTXU_join; exact CU).
          all: rewrite ?length_skipn; try lia.
          }
        box SEPoa; box SEPo.
        intros ms2 PO. unfold db_post in PO.
        destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2 & bs2 & OB2 & LB2 & PB2).
        rewrite (unsigned_lit (bv_unsigned sp + -112)) in MU2, ST2 by lia. rewrite length_skipn in LB2. rewrite length_skipn, OLEN in MU2.
        replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in MU2 by lia.
        (* [comment removed for export] *)
        unbox SEPl. unbox SEPlo. unbox SEPo. unbox SEPi. unbox SEPio.
        apply (rw_cells_transport usegs _ m m2 _ _ OL) in MU2 as OL2; [| exact WM2| cbn; lia].
        apply (rw_cells_transport usegs _ m m2 _ _ FR) in MU2 as FR2; [| exact WM2| cbn; lia].
        assert (INP2 : bytes_at usegs m2 inp_a inp) by (eapply bytes_at_transport; [exact INP| exact MU2| cbn; lia]).
        assert (OA12 : u8arr usegs m2 out (firstn (length dout) obs)).
        { eapply u8arr_transport; [exact OA1| exact MU2| exact WM2|]. rewrite length_firstn. cbn. lia. }
        box SEPl; box SEPlo; box SEPo; box SEPi; box SEPio.
        pose proof (out_join m2 _ _ OA12 ltac:(rewrite length_firstn; replace (Init.Nat.min (length dout) (length obs)) with (length dout) by lia; exact OB2)) as OA2'.
        assert (MU02 : munch WW m0 m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold WW. intros z Hz. cbn in Hz |- *. clear -Hz OL64 AB LO SPR. lia. }
        (* [comment removed for export] *)
        unfold DU_RA2. replace (ret_pc (Z_to_bv 64 0x20e664)) with (Z_to_bv 64 0x20e664) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. fbr. step.
        assert (VS : vs q raw = map a2b d).
        { transitivity (map a2b (map bv_unsigned (firstn (length d) raw))); [unfold vs; f_equal; f_equal; f_equal; lia| rewrite DPRE; reflexivity]. }
        assert (TL : du_tail {| du_d := d; du_eof := eof; du_out := dout |} seof
                     = mkDR (if seof || (0 <? eof) then 0 else 1) (dout ++ firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw))) []).
        { unfold du_tail. cbn [du_d du_eof du_out]. replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
          replace (length d mod 4 =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; apply Nat2Z.inj; rewrite Nat2Z.inj_mod; change (Z.of_nat 4) with 4; rewrite NQ, Z.mul_comm, Z.mod_mul; lia).
          rewrite (decodeblock_saved d (Z.to_nat q) eof); [| | lia| lia| lia].
          2:{ eapply Forall_impl; [| exact (proj1 DI)]. intros c Hc. apply b64_saved_lt64. exact Hc. }
          rewrite length_firstn, (groups_bytes_length (Z.to_nat q)) by (rewrite length_map; lia).
          replace ((Init.Nat.min (3 * Z.to_nat q - Z.to_nat eof) (3 * Z.to_nat q) =? 0)%nat && (0 <? eof)) with false
            by (symmetry; apply andb_false_intro1; apply Nat.eqb_neq; lia).
          rewrite VS. f_equal. f_equal. f_equal. lia. }
        rewrite TL.
        set (dec := firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw))) in *.
        assert (LD : length dec = Z.to_nat (3 * q - eof)).
        { subst dec. rewrite length_firstn, (groups_bytes_length (Z.to_nat q)); [lia|]. rewrite VS, length_map. lia. }
        (* [comment removed for export] *)
        assert (J : evt usegs (du_final m0 (mkDR (if seof || (0 <? eof) then 0 else 1) (dout ++ dec) []))
          (MS (mkR (Z_to_bv 64 0x20e664) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp y0 (Z_to_bv 64 (Z.of_nat (length dout))) y2 sp
                   (Z_to_bv 64 a) (Z_to_bv 64 (3 * q - eof)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.of_nat (length dout)))
                   (Z_to_bv 64 242) (Z_to_bv 64 (if seof then 0 else 1)) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) xs7 (Z_to_bv 64 64) xs9 (Z_to_bv 64 eof)
                   (Z_to_bv 64 18446744073709156439) y28 (Z_to_bv 64 (-1)) y30 y31)
              F (Z_to_bv 64 0x20e6c4) fc None m2 (seg_rom usegs))).
        { (* [comment removed for export] *)
          zstep. rewrite ?Z.add_0_r. rewrite (bv_swrap_small 32 (Z.of_nat (length dout))) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
          zstep. zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length dout) + (3 * q - eof))) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
          step. fbr. step. step.
          pose proof FR2 as FR2'. unfold du_frame in FR2'.
          unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi. clear FR2'.
          zstep. zstep. zstep. zstep.
          rewrite (rv_and seof eof 0) by lia. change (0 =? 0) with true. rewrite andb_true_r.
          eapply du_exit; try eassumption; try reflexivity; try lia.
          all: try (apply CTXU_split; exact CTX2).
          all: try (eapply wmono_trans; [exact WM| exact WM2]).
          all: lazymatch goal with
               | |- length _ = length obs0 => rewrite length_app, length_firstn, LB2; lia
               | |- firstn _ _ = map b8 _ => rewrite OPRE; apply prefix_join; rewrite LD; exact PB2
               | |- du_inv [] => split; [constructor| cbn; lia]
               | |- _ = zlength _ => unfold zlength; rewrite length_app, LD; lia
               | |- _ <= _ <= _ => destruct seof; destruct (0 <? eof); cbn; lia
               | |- _ => idtac
               end.
          }
        step. if_cases EQ2; zify_cond EQ2; try rewrite !signed_lit in * by lia; [exact J|]. step. tbr. exact J.
      + (* [comment removed for export] *)
        assert (TL : du_tail (mkDU d eof dout) seof = if seof then mkDR (-1) dout d else mkDR 1 dout d).
        { unfold du_tail. cbn [du_d du_eof du_out]. replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
          replace (length d mod 4 =? 0)%nat with false; [destruct seof; reflexivity|].
          symmetry. apply Nat.eqb_neq. intros K. apply EQ1. rewrite <- (Nat2Z.inj_mod _ 4) . change (Z.of_nat 4) with 4 in *. lia. }
        rewrite TL.
        unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi.
        destruct seof.
        * (* [comment removed for export] *)
          step. try if_lit. step. step.
          eapply du_exit; try eassumption; try reflexivity; unfold zlength; try lia.
        * (* [comment removed for export] *)
          step. try if_lit. step. zstep. zstep. zstep. zstep.
          rewrite (rv_and false eof (Z.of_nat (length d))) by lia. cbn [orb].
          replace (Z.of_nat (length d) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r.
          eapply du_exit; try eassumption; try reflexivity; unfold zlength; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition LOOPst (i : Z) (d : list Z) (eof k : Z) (m : mem) (xra xt0 xa0 xa1 xa4 xa5 fl xs9 xt3 xt4 : word) : machine_state :=
    UST DU_LOOP i (Z.of_nat (length d)) eof k fl m xra xt0 xa0 xa1 xa4 xa5 (Z_to_bv 64 (inp_a + i)) xs9 xt3 xt4.

  (* [comment removed for export] *)
  Definition char_post (i : Z) (d : list Z) (k : Z) (m0 m : mem) (obs : list byte) (ov : Z) (xra xs9 : word) (cls : cclass)
      : machine_state -> Prop := fun ms' =>
    match cls with
    | CErr => exists xt0 xa0 xa1 xa4 xa5 xs4 xs10 xt3,
        ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 (Z_to_bv 64 k) (Z_to_bv 64 (out + k)) sp (Z_to_bv 64 (inp_a + i)) xa0 xa1
                      (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) xa4 xa5 (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 a)
                      (Z_to_bv 64 61) (Z_to_bv 64 242) xs4 (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 64) xs9 xs10 (Z_to_bv 64 DB_NTAB)
                      xt3 (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255))
                 F (Z_to_bv 64 DU_ERRX) fc None m (seg_rom usegs)
    | CEof e1 => exists xt0 xa0 xa1 xa4 xa5 xt3,
        ms' = UST DU_TAIL i (Z.of_nat (length d)) e1 k (Z_to_bv 64 0) m xra xt0 xa0 xa1 xa4 xa5 (Z_to_bv 64 (inp_a + i + 1)) xs9 xt3 (Z_to_bv 64 (-1))
    | CGo d1 e1 => exists xt0 xa0 xa1 xa4 xa5 xt3 m' raw',
        ms' = UST DU_ST i (Z.of_nat (length d1)) e1 k (Z_to_bv 64 1) m' xra xt0 xa0 xa1 xa4 xa5 (Z_to_bv 64 (inp_a + i + 1)) xs9 xt3 (Z_to_bv 64 (-1))
        /\ CTXU m' a nn0 raw' line /\ map bv_unsigned (firstn (length d1) raw') = d1
        /\ bytes_at usegs m' inp_a inp /\ mem_inv usegs m' /\ u8arr usegs m' out obs /\ rw_cells usegs m' outlp [C4 (wz ov)]
        /\ rw_cells usegs m' (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
        /\ stk usegs m' lo (bv_unsigned sp + -112) /\ munch WW m0 m' /\ wmono usegs m0 m'
    end.

  Local Ltac cls_done CL :=
    lazymatch goal with |- evt _ (char_post _ _ _ _ _ _ _ _ _ (classify ?d ?e ?c)) _ =>
      replace (classify d e c) with CL; [apply evt_done; unfold char_post, UST, DU_ERRX, DU_TAIL, DU_ST, DB_NTAB, A_data_ascii2bin | ] end.

  (* [comment removed for export] *)
  Lemma b_char : forall (i eof k : Z) (d : list Z) (m0 m : mem) (raw obs : list byte) (ov : Z) (cb : byte)
      (xra xt0 xa0 xa1 xa4 xa5 fl xs9 xt3 xt4 : word),
      0 <= i < inl -> nth_error inp (Z.to_nat i) = Some cb -> 0 <= k <= Z.of_nat (length obs0) ->
      CTXU m a nn0 raw line -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d -> 0 <= eof <= 2 ->
      bytes_at usegs m inp_a inp -> mem_inv usegs m -> u8arr usegs m out obs -> length obs = length obs0 -> rw_cells usegs m outlp [C4 (wz ov)] ->
      rw_cells usegs m (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk usegs m lo (bv_unsigned sp + -112) -> munch WW m0 m -> wmono usegs m0 m ->
      evt usegs (char_post i d k m0 m obs ov xra xs9 (classify d eof (bv_unsigned cb)))
        (LOOPst i d eof k m xra xt0 xa0 xa1 xa4 xa5 fl xs9 xt3 xt4).
  Proof.
    intros until xt4. intros IR NTH KR CU DPRE DI ER INP MI OA OLEN OL FR ST MU WM.
    unfold LOOPst, UST, DU_LOOP, DB_NTAB, A_data_ascii2bin. pose proof (word_range sp) as SPR. boxsep.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (byte_range cb) as CB. set (c := bv_unsigned cb) in *.
    unfold WW in MU. unfold wz in C1, C3, OL. unfold du_frame in FR.
    (* [comment removed for export] *)
    zstep. step. fbr.
    (* [comment removed for export] *)
    pose proof (rd_raw _ _ _ i cb INP NTH ltac:(lia)) as RD. step. clear RD. step.
    destruct (Z.lt_ge_cases c 128) as [CLO|CHI].
    2:{ (* [comment removed for export] *)
        rewrite (sxb_big cb) by lia. step. tbr.
        cls_done CErr; [eexists _, _, _, _, _, _, _, _; reflexivity|].
        unfold classify. rewrite (a2b_high c) by lia. reflexivity. }
    rewrite (sxb_small cb) by lia. fold c.
    destruct (a2b_facts c ltac:(lia)) as [NBL VR].
    step. fbr.
    (* [comment removed for export] *)
    step. fbr.
    step. pose proof (rd_tab _ c MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD. unfold wz.
    (* [comment removed for export] *)
    step. if_cases EQE; zify_cond EQE.
    { cls_done CErr; [eexists _, _, _, _, _, _, _, _; reflexivity|].
      unfold classify, B64_ERROR. replace (a2b c =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    assert (E255 : (a2b c =? B64_ERROR) = false) by (apply Z.eqb_neq; unfold B64_ERROR; lia).
    (* [comment removed for export] *)
    assert (J98 : forall e1 (y3 : word), 0 <= e1 <= 2 ->
      classify d eof c = (if a2b c =? B64_EOF then CEof e1 else CGo (if b64_base64 (a2b c) then d ++ [c] else d) e1) ->
      evt usegs (char_post i d k m0 m obs ov xra xs9 (classify d eof c))
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 (Z.land (a2b c) 236)) (Z_to_bv 64 k) (Z_to_bv 64 (out + k)) sp (Z_to_bv 64 (inp_a + i))
                 (Z_to_bv 64 c) (Z_to_bv 64 (a2b c)) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) xa4 xa5 (Z_to_bv 64 395176) (Z_to_bv 64 a)
                 (Z_to_bv 64 61) (Z_to_bv 64 242) fl (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 64) xs9
                 (Z_to_bv 64 e1) (Z_to_bv 64 18446744073709156439) y3 (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255))
            F (Z_to_bv 64 0x20e544) fc None m (seg_rom usegs))).
    { intros e1 y3 E1 CL. rewrite CL. unfold B64_EOF.
      (* [comment removed for export] *)
      zstep. zstep. step. if_cases EQF; zify_cond EQF.
      { replace (a2b c =? 242) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done. unfold char_post, UST, DU_TAIL, DB_NTAB, A_data_ascii2bin.
        replace (Z.b2z (0 <? (a2b c + -242) mod 18446744073709551616)) with 0 by (rewrite EQF; reflexivity).
        eexists _, _, _, _, _, _. reflexivity. }
      replace (a2b c =? 242) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.b2z (0 <? (a2b c + -242) mod 18446744073709551616)) with 1.
      2:{ destruct (0 <? (a2b c + -242) mod 18446744073709551616) eqn:Q; [reflexivity|]. apply Z.ltb_ge in Q. exfalso. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      step. if_cases EQB; zify_cond EQB.
      - (* [comment removed for export] *)
        assert (BF : b64_base64 (a2b c) = false).
        { destruct (b64_base64 (a2b c)); [| reflexivity]. cbn in NBL. apply Z.eqb_neq in NBL. exfalso. lia. }
        rewrite BF. apply evt_done. unfold char_post, UST, DU_ST, DB_NTAB, A_data_ascii2bin.
        eexists _, _, _, _, _, _, m, raw. split; [reflexivity|].
        split; [exact CU|]. split; [exact DPRE|]. split; [exact INP|]. split; [exact MI|]. split; [exact OA|]. split; [unfold wz; exact OL|].
        split; [exact FR|]. split; [exact ST|]. split; [exact MU| exact WM].
      - (* [comment removed for export] *)
        assert (BT : b64_base64 (a2b c) = true).
        { destruct (b64_base64 (a2b c)); [reflexivity|]. cbn in NBL. apply Z.eqb_eq in NBL. exfalso. lia. }
        rewrite BT.
        (* [comment removed for export] *)
        step. step. fbr. zstep. step. fbr.
        zstep. zstep. zstep. zstep. ub_b2z. change (Z.lxor (Z.lxor 0 0) 1) with 1. step. try fbr.
        zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + 1)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
        replace (Z.of_nat (length d) + (a + 4)) with (a + 4 + Z.of_nat (length d)) by lia.
        unbox SEPia. unbox SEPoa. unbox SEPla.
        pose proof (u8arr_store_ok usegs m (a + 4) raw (Z.of_nat (length d)) (wa (a + 4 + Z.of_nat (length d))) C2 ltac:(lia) eq_refl) as SOK.
        step. change (Z_to_bv 64 c) with (zxb cb). rewrite le1_zxb.
        pose proof (u8arr_write_bytes usegs m (a + 4) raw (Z.of_nat (length d)) [cb] C2 ltac:(lia) ltac:(cbn; lia)) as C2'.
        clear C2. store_done.
        box SEPia. box SEPoa. box SEPla.
        apply evt_done. unfold char_post, UST, DU_ST, DB_NTAB, A_data_ascii2bin.
        eexists _, _, _, _, _, _, _, (upd_bytes raw (Z.to_nat (Z.of_nat (length d))) [cb]).
        split. { rewrite length_app. cbn [length]. replace (Z.of_nat (length d + 1)) with (Z.of_nat (length d) + 1) by lia. reflexivity. }
        split. { split; [unfold wz; exact C1|]. split; [exact C2'|]. split; [rewrite upd_bytes_length by (cbn; lia); exact L80| unfold wz; exact C3]. }
        split. { rewrite Nat2Z.id, length_app. cbn [length]. rewrite Nat.add_1_r. apply prefix_snoc; [exact DPRE| lia]. }
        split; [exact INP|]. split; [exact MI|]. split; [exact OA|]. split; [unfold wz; exact OL|].
        split; [exact FR|]. split; [exact ST|]. split; [exact MU| exact WM]. }
    (* [comment removed for export] *)
    zstep. unfold CH_EQ. step. if_cases EQC; zify_cond EQC.
    - (* [comment removed for export] *)
      step. if_cases EQZ; zify_cond EQZ; try rewrite !signed_lit in * by lia.
      + (* [comment removed for export] *)
        step. replace (Z_to_bv 64 0) with (Z_to_bv 64 eof) by (f_equal; lia).
        apply (J98 eof); [lia|].
        unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (0 <? eof) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb andb].
        replace (2 <? eof) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      + (* [comment removed for export] *)
        step. if_cases EQB; zify_cond EQB.
        * (* [comment removed for export] *)
          assert (BT : b64_base64 (a2b c) = true).
          { destruct (b64_base64 (a2b c)); [reflexivity|]. cbn in NBL. apply Z.eqb_eq in NBL. exfalso. lia. }
          cls_done CErr; [eexists _, _, _, _, _, _, _, _; reflexivity|].
          unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
          replace (0 <? eof) with true by (symmetry; apply Z.ltb_lt; lia). rewrite BT. reflexivity.
        * (* [comment removed for export] *)
          assert (BF : b64_base64 (a2b c) = false).
          { destruct (b64_base64 (a2b c)); [| reflexivity]. cbn in NBL. apply Z.eqb_neq in NBL. exfalso. lia. }
          step. apply (J98 eof); [lia|].
          unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
          rewrite BF, andb_false_r. replace (2 <? eof) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      step. step. if_cases EQ3; zify_cond EQ3; try rewrite !signed_lit in * by lia.
      + cls_done CErr; [eexists _, _, _, _, _, _, _, _; reflexivity|].
        unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb andb]. replace (2 <? eof + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        zstep. try rewrite (bv_swrap_small 32 (eof + 1)) by (change (bv_half_modulus 32) with 2147483648%Z; lia). step.
        apply (J98 (eof + 1)); [lia|].
        unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb andb]. replace (2 <? eof + 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition MEMI (m0 m : mem) (d dout : list Z) (ov : Z) : Prop :=
    exists raw obs, CTXU m a nn0 raw line /\ map bv_unsigned (firstn (length d) raw) = d
      /\ u8arr usegs m out obs /\ length obs = length obs0 /\ firstn (length dout) obs = map b8 dout
      /\ rw_cells usegs m outlp [C4 (wz ov)] /\ bytes_at usegs m inp_a inp
      /\ rw_cells usegs m (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk usegs m lo (bv_unsigned sp + -112) /\ mem_inv usegs m /\ munch WW m0 m /\ wmono usegs m0 m.

  (* [comment removed for export] *)
  Definition flush (d1 : list Z) (e1 : Z) (dout : list Z) : list Z * list Z :=
    if Nat.eqb (length d1) 64 then ([], dout ++ firstn (Z.to_nat (48 - e1)) (groups_bytes (map a2b d1))) else (d1, dout).

  (* [comment removed for export] *)
  Lemma b_flush_adv : forall (i e1 : Z) (d1 dout : list Z) (m0 m : mem) (ov : Z) (xra xt0 xa0 xa1 xa4 xa5 xs9 xt3 xt4 : word),
      0 <= i < inl -> Forall b64_saved d1 -> (length d1 <= 64)%nat -> 0 <= e1 <= 2 ->
      zlength dout + 3 * ((zlength d1 + (inl - i - 1)) / 4) <= Z.of_nat (length obs0) ->
      zlength dout + 3 * ((zlength d1 + (inl - i - 1)) / 4) < 2^21 ->
      MEMI m0 m d1 dout ov ->
      evt usegs (fun ms' => exists m2 xra' xt0' xa0' xa1' xa4' xa5' xs9' xt3' xt4',
          let fd := flush d1 e1 dout in
          ms' = UST (if i + 1 <? inl then DU_LOOP else DU_TAIL) (i + 1) (zlength (fst fd)) e1 (zlength (snd fd)) (Z_to_bv 64 1) m2
                    xra' xt0' xa0' xa1' xa4' xa5' (Z_to_bv 64 (inp_a + i + 1)) xs9' xt3' xt4'
          /\ MEMI m0 m2 (fst fd) (snd fd) ov /\ (length (fst fd) < 64)%nat /\ Forall b64_saved (fst fd)
          /\ zlength (snd fd) + 3 * ((zlength (fst fd) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0)
          /\ zlength (snd fd) + 3 * ((zlength (fst fd) + (inl - (i + 1))) / 4) < 2^21)
        (UST DU_ST i (zlength d1) e1 (zlength dout) (Z_to_bv 64 1) m xra xt0 xa0 xa1 xa4 xa5 (Z_to_bv 64 (inp_a + i + 1)) xs9 xt3 xt4).
  Proof.
    intros until xt4. intros IR SAVED DL E1 CAP CAPB (raw & obs & CU & DPRE & OA & OLEN & OPRE & OL & INP & FR & ST & MI & MU & WM).
    unfold UST, DU_ST, DU_LOOP, DU_TAIL, DB_NTAB, A_data_ascii2bin, zlength in *. pose proof (word_range sp) as SPR. boxsep.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (OL64 : (length dout <= length obs0)%nat).
    { apply (f_equal (@length byte)) in OPRE. rewrite length_map, length_firstn in OPRE. lia. }
    assert (DIV0 : forall x, 0 <= x -> 0 <= x / 4) by (intros x Hx; apply Z.div_pos; lia).
    pose proof (DIV0 (Z.of_nat (length d1) + (inl - i - 1)) ltac:(lia)) as DV.
    (* [comment removed for export] *)
    assert (ADV : forall m2 (d2 dout2 : list Z) (xra' xt0' xa0' xa1' xa4' xa5' xs9' xt3' xt4' : word),
      flush d1 e1 dout = (d2, dout2) -> MEMI m0 m2 d2 dout2 ov -> (length d2 < 64)%nat -> Forall b64_saved d2 ->
      Z.of_nat (length dout2) + 3 * ((Z.of_nat (length d2) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0) ->
      Z.of_nat (length dout2) + 3 * ((Z.of_nat (length d2) + (inl - (i + 1))) / 4) < 2^21 ->
      evt usegs (fun ms' => exists m3 xra'' xt0'' xa0'' xa1'' xa4'' xa5'' xs9'' xt3'' xt4'',
          let fd := flush d1 e1 dout in
          ms' = MS (mkR xra'' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0'' (Z_to_bv 64 (Z.of_nat (length (snd fd)))) (Z_to_bv 64 (out + Z.of_nat (length (snd fd)))) sp
                        (Z_to_bv 64 (inp_a + (i + 1))) xa0'' xa1'' (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length (fst fd)))) xa4'' xa5'' (Z_to_bv 64 395176) (Z_to_bv 64 a)
                        (Z_to_bv 64 61) (Z_to_bv 64 242) (Z_to_bv 64 1) (Z_to_bv 64 224) (Z_to_bv 64 (inl - (i + 1))) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 64) xs9''
                        (Z_to_bv 64 e1) (Z_to_bv 64 18446744073709156439) xt3'' xt4'' (Z_to_bv 64 2) (Z_to_bv 64 255))
                   F (Z_to_bv 64 (if i + 1 <? inl then 2155768 else 2156072)) fc None m3 (seg_rom usegs)
          /\ MEMI m0 m3 (fst fd) (snd fd) ov /\ (length (fst fd) < 64)%nat /\ Forall b64_saved (fst fd)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) < 2^21)
        (MS (mkR xra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0' (Z_to_bv 64 (Z.of_nat (length dout2))) (Z_to_bv 64 (out + Z.of_nat (length dout2))) sp
                 (Z_to_bv 64 (inp_a + i)) xa0' xa1' (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d2))) xa4' xa5' (Z_to_bv 64 395176) (Z_to_bv 64 a)
                 (Z_to_bv 64 61) (Z_to_bv 64 242) (Z_to_bv 64 1) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 64) xs9'
                 (Z_to_bv 64 e1) (Z_to_bv 64 18446744073709156439) xt3' xt4' (Z_to_bv 64 2) (Z_to_bv 64 255))
            F (Z_to_bv 64 0x20e61c) fc None m2 (seg_rom usegs))).
    { intros m2 d2 dout2 xra' xt0' xa0' xa1' xa4' xa5' xs9' xt3' xt4' FD MI2 DL2 SV2 CAP2 CAPB2. rewrite FD. cbn [fst snd].
      destruct MI2 as (raw2 & obs2 & CU2 & DPRE2 & OA2 & OLEN2 & OPRE2 & OL2 & INP2 & FR2 & ST2 & MI2 & MU2 & WM2). unfold WW in MU2.
      (* [comment removed for export] *)
      zstep. try rewrite (bv_swrap_small 32 (inl - i - 1)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      zstep. step. if_cases EQL; zify_cond EQL.
      - replace (i + 1 <? inl) with true by (symmetry; apply Z.ltb_lt; lia).
        apply evt_done. eexists m2, _, _, _, _, _, _, _, _, _.
        replace (inl - i - 1) with (inl - (i + 1)) by lia. replace (inp_a + i + 1) with (inp_a + (i + 1)) by lia.
        split; [reflexivity|]. split; [exists raw2, obs2; unfold WW; repeat (split; [eassumption|]); exact WM2|]. repeat (split; [first [exact DL2| exact SV2| exact CAP2]|]). exact CAPB2.
      - replace (i + 1 <? inl) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists m2, _, _, _, _, _, _, _, _, _.
        replace (inl - i - 1) with (inl - (i + 1)) by lia. replace (inp_a + i + 1) with (inp_a + (i + 1)) by lia.
        split; [reflexivity|]. split; [exists raw2, obs2; unfold WW; repeat (split; [eassumption|]); exact WM2|]. repeat (split; [first [exact DL2| exact SV2| exact CAP2]|]). exact CAPB2. }
    (* [comment removed for export] *)
    step. if_cases EQ64; zify_cond EQ64.
    - (* [comment removed for export] *)
      assert (FD : flush d1 e1 dout = (d1, dout)) by (unfold flush; replace (length d1 =? 64)%nat with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity).
      eapply ADV; [exact FD| | lia| exact SAVED| lia| lia].
      exists raw, obs. unfold WW. repeat (split; [eassumption|]). exact WM.
    - (* [comment removed for export] *)
      assert (L64 : length d1 = 64%nat) by lia.
      assert (FD : flush d1 e1 dout = ([], dout ++ firstn (Z.to_nat (48 - e1)) (groups_bytes (map a2b d1)))) by (unfold flush; rewrite L64; reflexivity).
      (* [comment removed for export] *)
      do 10 step. step.
      destruct (out_split m obs (length dout) OA ltac:(lia)) as [OA1 OAR].
      assert (SAVED' : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * 16)) raw))).
      { change (Z.to_nat (4 * 16)) with 64%nat. rewrite <- L64, DPRE. exact SAVED. }
      eapply evt_cut.
      { unbox SEPoa. unbox SEPo.
        eapply (decblock_ok_spec _ (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo) (q := 16) (tj := skipn (length dout) obs); rewrite ?unsigned_lit by lia;
          try eassumption.
        all: try (apply CTXU_join; exact CU).
        all: rewrite ?length_skipn; try lia.
        all: match goal with |- ?G => idtac "DB2-LEFT" G end. }
      box SEPoa; box SEPo.
      intros ms2 PO. unfold db_post in PO.
      destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2 & bs2 & OB2 & LB2 & PB2).
      rewrite (unsigned_lit (bv_unsigned sp + -112)) in MU2, ST2 by lia. rewrite length_skipn in LB2. rewrite length_skipn, OLEN in MU2.
      replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in MU2 by lia.
      unbox SEPl. unbox SEPlo. unbox SEPo. unbox SEPi. unbox SEPio.
      apply (rw_cells_transport usegs _ m m2 _ _ OL) in MU2 as OL2; [| exact WM2| cbn; lia].
      unfold du_frame in FR. apply (rw_cells_transport usegs _ m m2 _ _ FR) in MU2 as FR2; [| exact WM2| cbn; lia].
      assert (INP2 : bytes_at usegs m2 inp_a inp) by (eapply bytes_at_transport; [exact INP| exact MU2| cbn; lia]).
      assert (OA12 : u8arr usegs m2 out (firstn (length dout) obs)).
      { eapply u8arr_transport; [exact OA1| exact MU2| exact WM2|]. rewrite length_firstn. cbn. lia. }
      box SEPl; box SEPlo; box SEPo; box SEPi; box SEPio.
      pose proof (out_join m2 _ _ OA12 ltac:(rewrite length_firstn; replace (Init.Nat.min (length dout) (length obs)) with (length dout) by lia; exact OB2)) as OA2'.
      assert (MU02 : munch WW m0 m2).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold WW. intros z Hz. cbn in Hz |- *. clear -Hz OL64 AB LO SPR. lia. }
      assert (VS : vs 16 raw = map a2b d1).
      { unfold vs. change (Z.to_nat (4 * 16)) with 64%nat. rewrite <- L64, DPRE. reflexivity. }
      rewrite VS in PB2. try replace (3 * 16 - e1)%Z with (48 - e1) in PB2 by lia.
      set (dec := firstn (Z.to_nat (48 - e1)) (groups_bytes (map a2b d1))) in *.
      assert (LD : length dec = Z.to_nat (48 - e1)).
      { subst dec. rewrite length_firstn, (groups_bytes_length 16); [lia|]. rewrite length_map. exact L64. }
      (* [comment removed for export] *)
      unfold DU_RA1 in *. replace (ret_pc (Z_to_bv 64 0x20e5b0)) with (Z_to_bv 64 0x20e5b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. fbr. step.
      assert (J : forall pcx, pcx = Z_to_bv 64 0x20e5c0 ->
        evt usegs (fun ms' => exists m3 xra'' xt0'' xa0'' xa1'' xa4'' xa5'' xs9'' xt3'' xt4'',
          let fd := flush d1 e1 dout in
          ms' = MS (mkR xra'' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0'' (Z_to_bv 64 (Z.of_nat (length (snd fd)))) (Z_to_bv 64 (out + Z.of_nat (length (snd fd)))) sp
                        (Z_to_bv 64 (inp_a + (i + 1))) xa0'' xa1'' (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length (fst fd)))) xa4'' xa5'' (Z_to_bv 64 395176) (Z_to_bv 64 a)
                        (Z_to_bv 64 61) (Z_to_bv 64 242) (Z_to_bv 64 1) (Z_to_bv 64 224) (Z_to_bv 64 (inl - (i + 1))) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 64) xs9''
                        (Z_to_bv 64 e1) (Z_to_bv 64 18446744073709156439) xt3'' xt4'' (Z_to_bv 64 2) (Z_to_bv 64 255))
                   F (Z_to_bv 64 (if i + 1 <? inl then 2155768 else 2156072)) fc None m3 (seg_rom usegs)
          /\ MEMI m0 m3 (fst fd) (snd fd) ov /\ (length (fst fd) < 64)%nat /\ Forall b64_saved (fst fd)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) < 2^21)
        (MS (mkR (Z_to_bv 64 0x20e5b0) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp y0 (Z_to_bv 64 (Z.of_nat (length dout))) y2 sp
                 (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 (48 - e1)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 395176)
                 (Z_to_bv 64 (out + Z.of_nat (length dout))) (Z_to_bv 64 (Z.of_nat (length dout))) (Z_to_bv 64 a)
                 (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 1) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 e1)
                 (Z_to_bv 64 18446744073709156439) y28 y29 y30 y31)
            F pcx fc None m2 (seg_rom usegs))).
      { intros pcx ->.
        (* [comment removed for export] *)
        zstep. rewrite ?Z.add_0_r. rewrite (bv_swrap_small 32 (Z.of_nat (length dout))) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
        zstep. zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length dout) + (48 - e1))) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
        step. fbr. step. step. step. zstep. step. do 6 step.
        (* [comment removed for export] *)
        step. fbr. zstep. zstep. zstep. ub_b2z. change (Z.lxor 1 0) with 1. step. try fbr. step. step. zstep.
        replace (Z.of_nat (length dout) + (48 - e1)) with (Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        try replace (48 - e1 + Z.of_nat (length dout)) with (Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        try replace (out + Z.of_nat (length dout) + (48 - e1)) with (out + Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        try replace (48 - e1 + (out + Z.of_nat (length dout))) with (out + Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length Z []))).
        eapply ADV; [exact FD| | cbn; lia| constructor| |].
        - exists raw, (firstn (length dout) obs ++ bs2). unfold WW.
          split; [apply CTXU_split; exact CTX2|]. split; [reflexivity|]. split; [exact OA2'|].
          split; [rewrite length_app, length_firstn, LB2; lia|].
          split; [rewrite OPRE; apply prefix_join; rewrite LD; exact PB2|].
          split; [exact OL2|]. split; [exact INP2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
          split; [exact MU02| eapply wmono_trans; [exact WM| exact WM2]].
        - rewrite length_app, LD. cbn [length]. clear -CAP E1 L64 IR DIV0. Z.div_mod_to_equations. lia.
        - rewrite length_app, LD. cbn [length]. clear -CAPB E1 L64 IR DIV0. Z.div_mod_to_equations. lia. }
      step. if_cases EQZ; zify_cond EQZ; try rewrite !signed_lit in * by lia.
      + apply J. reflexivity.
      + step. fbr. apply J. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma classify_facts : forall d eof c, du_inv d -> 0 <= eof <= 2 -> 0 <= c < 256 ->
    match classify d eof c with
    | CErr => True
    | CEof e1 => 0 <= e1 <= 2
    | CGo d1 e1 => 0 <= e1 <= 2 /\ Forall b64_saved d1 /\ (length d1 <= S (length d))%nat
    end.
  Proof.
    intros d eof c [DF DL] ER CR. unfold classify.
    destruct (a2b c =? B64_ERROR) eqn:E1; [exact I|].
    destruct (negb (c =? CH_EQ) && (0 <? eof) && b64_base64 (a2b c)); [exact I|].
    destruct (2 <? (if c =? CH_EQ then eof + 1 else eof)) eqn:E3; [exact I|]. apply Z.ltb_ge in E3.
    assert (E1R : 0 <= (if c =? CH_EQ then eof + 1 else eof) <= 2) by (destruct (c =? CH_EQ); lia).
    destruct (a2b c =? B64_EOF) eqn:E4; [exact E1R|].
    split; [exact E1R|]. destruct (b64_base64 (a2b c)) eqn:BB.
    - split; [| rewrite length_app; cbn; lia]. apply Forall_app. split; [exact DF|]. constructor; [| constructor].
      apply Z.eqb_neq in E1. apply Z.eqb_neq in E4.
      assert (C128 : c < 128) by (destruct (Z.lt_ge_cases c 128) as [|K]; [assumption|]; exfalso; apply E1; apply a2b_high; exact K).
      split; [lia|]. split; [exact BB|]. split; [exact E1| exact E4].
    - split; [exact DF| lia].
  Qed.

  Lemma flush_du : forall d1 e1 dout, Forall b64_saved d1 -> (length d1 <= 64)%nat -> 0 <= e1 <= 2 ->
    (if Nat.eqb (length d1) 64 then
       match decodeblock d1 e1 with
       | None => DUerr []
       | Some bs => if Nat.eqb (length bs) 0 && (0 <? e1) then DUerr [] else DUcont (mkDU [] e1 (dout ++ bs))
       end
     else DUcont (mkDU d1 e1 dout))
    = DUcont (mkDU (fst (flush d1 e1 dout)) e1 (snd (flush d1 e1 dout))).
  Proof.
    intros d1 e1 dout SV L E1. unfold flush. destruct (Nat.eqb (length d1) 64) eqn:E64; [| reflexivity]. apply Nat.eqb_eq in E64.
    rewrite (decodeblock_saved d1 16 e1); [| | lia| lia| lia].
    2:{ eapply Forall_impl; [| exact SV]. intros c Hc. apply b64_saved_lt64. exact Hc. }
    rewrite length_firstn, (groups_bytes_length 16) by (rewrite length_map; lia).
    replace ((Init.Nat.min (3 * 16 - Z.to_nat e1) (3 * 16) =? 0)%nat && (0 <? e1)) with false by (symmetry; apply andb_false_intro1; apply Nat.eqb_neq; lia).
    cbn [fst snd]. f_equal. f_equal. f_equal. f_equal. f_equal. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma loop_walk : forall (kk : nat) (i eof : Z) (d dout : list Z) (m0 m : mem) (ov : Z)
      (xra xt0 xa0 xa1 xa4 xa5 fl xs9 xt3 xt4 : word),
      Z.to_nat (inl - i) = kk -> 0 <= i < inl ->
      MEMI m0 m d dout ov -> du_inv d -> 0 <= eof <= 2 ->
      zlength dout + 3 * ((zlength d + (inl - i)) / 4) <= Z.of_nat (length obs0) ->
      zlength dout + 3 * ((zlength d + (inl - i)) / 4) < 2^21 ->
      evt usegs (du_final m0 (du_loop (mkDU d eof dout) (skipn (Z.to_nat i) (map bv_unsigned inp))))
        (LOOPst i d eof (zlength dout) m xra xt0 xa0 xa1 xa4 xa5 fl xs9 xt3 xt4).
  Proof.
    induction kk as [|kk IH]; intros until xt4; intros HK IR MEM DI ER CAP CAPB; [lia|].
    pose proof (word_range sp) as SPR. boxsep. unfold zlength in *.
    destruct MEM as (raw & obs & CU & DPRE & OA & OLEN & OPRE & OL & INP & FR & ST & MI & MU & WM).
    assert (DIV0 : forall x, 0 <= x -> 0 <= x / 4) by (intros x Hx; apply Z.div_pos; lia).
    pose proof (DIV0 (Z.of_nat (length d) + (inl - i)) ltac:(lia)) as DV.
    assert (OL64 : (length dout <= length obs0)%nat).
    { apply (f_equal (@length byte)) in OPRE. rewrite length_map, length_firstn in OPRE. lia. }
    destruct (nth_error inp (Z.to_nat i)) as [cb|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    pose proof (byte_range cb) as CB.
    rewrite (skipn_nth_cons' (map bv_unsigned inp) (Z.to_nat i) (bv_unsigned cb)) by (rewrite nth_error_map, NTH; reflexivity).
    cbn [du_loop]. rewrite (du_step_classify d eof dout (bv_unsigned cb)) by (destruct DI as [_ K]; exact K).
    pose proof (classify_facts d eof (bv_unsigned cb) DI ER CB) as CF.
    eapply evt_cut.
    { eapply (b_char i eof (Z.of_nat (length dout)) d m0 m raw obs ov cb); try eassumption; lia. }
    intros ms1 PO. unfold char_post in PO.
    destruct (classify d eof (bv_unsigned cb)) as [|e1|d1 e1].
    - (* [comment removed for export] *)
      destruct PO as (x5 & x10 & x11 & x14 & x15 & y20 & y26 & x28 & ->). cbn [du_out]. unfold DU_ERRX.
      pose proof FR as FR'. unfold du_frame in FR'.
      unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi. clear FR'. step.
      eapply du_exit; try eassumption; try reflexivity; unfold zlength; try lia.
    - (* [comment removed for export] *)
      destruct PO as (x5 & x10 & x11 & x14 & x15 & x28 & ->).
      change (Z.of_nat (length d)) with (zlength d). change (Z.of_nat (length dout)) with (zlength dout).
      change (Z_to_bv 64 0) with (Z_to_bv 64 (if true then 0 else 1)).
      eapply du_tail_walk; try eassumption; unfold zlength; try lia.
    - (* [comment removed for export] *)
      destruct CF as (E1R & SV1 & L1).
      destruct PO as (x5 & x10 & x11 & x14 & x15 & x28 & m1 & raw1 & -> & CU1 & DPRE1 & INP1 & MI1 & OA1 & OL1 & FR1 & ST1 & MU1 & WM1).
      rewrite (flush_du d1 e1 dout SV1) by (destruct DI as [_ K]; lia).
      change (Z.of_nat (length d1)) with (zlength d1). change (Z.of_nat (length dout)) with (zlength dout).
      eapply evt_cut.
      { eapply (b_flush_adv i e1 d1 dout m0 m1 ov); try eassumption; unfold zlength; try (destruct DI as [_ K]; lia).
        all: lazymatch goal with
             | |- MEMI _ _ _ _ _ => exists raw1, obs; repeat (split; [eassumption|]); exact WM1
             | |- _ <= _ => destruct DI as [_ K];
                 eapply Z.le_trans; [| exact CAP]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             | |- _ < _ => destruct DI as [_ K];
                 eapply Z.le_lt_trans; [| exact CAPB]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             end. }
      intros ms2 (m2 & xra' & xt0' & xa0' & xa1' & xa4' & xa5' & xs9' & xt3' & xt4' & -> & MEM2 & DL2 & SV2 & CAP2 & CAPB2).
      destruct (flush d1 e1 dout) as [d2 dout2] eqn:FD. cbn [fst snd] in *.
      assert (DI2 : du_inv d2) by (split; [exact SV2| exact DL2]).
      destruct (Z.lt_ge_cases (i + 1) inl) as [MORE|DONE].
      + replace (i + 1 <? inl) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia. replace (inp_a + i + 1) with (inp_a + (i + 1)) by lia.
        eapply (IH (i + 1)); try eassumption; lia.
      + replace (i + 1 <? inl) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite skipn_all2 by (rewrite length_map; lia). cbn [du_loop].
        destruct MEM2 as (raw2 & obs2 & CU2 & DPRE2 & OA2 & OLEN2 & OPRE2 & OL2 & INP2 & FR2 & ST2 & MI2 & MU2 & WM2).
        change (Z_to_bv 64 1) with (Z_to_bv 64 (if false then 0 else 1)).
        eapply du_tail_walk; try eassumption; unfold zlength in *; try lia.
        all: lazymatch goal with
             | |- _ <= _ => eapply Z.le_trans; [| exact CAP2]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             | |- _ < _ => eapply Z.le_lt_trans; [| exact CAPB2]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             end.
  Qed.
  Lemma prefix_nth : forall (raw : list byte) (d : list Z) i c,
    map bv_unsigned (firstn (length d) raw) = d -> nth_error raw i = Some c -> (i < length d)%nat -> nth i d 0 = bv_unsigned c.
  Proof.
    intros raw d i c P N L. rewrite <- P. apply nth_error_nth. rewrite nth_error_map, nth_error_firstn.
    replace (i <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite N. reflexivity.
  Qed.

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Lemma s0_walk : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (d : list Z) (raw obs : list byte) (ov : Z),
      rw_cells usegs m a (ctx_chunk nn0 raw line) -> nn0 = zlength d -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d ->
      bytes_at usegs m inp_a inp -> u8arr usegs m out obs -> length obs = length obs0 -> rw_cells usegs m outlp [C4 (wz ov)] ->
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          if inl =? 0 then du_final m (mkDR 0 [] d) ms'
          else exists m1 xt0 xa0 xa1 xa4 xa5 xs9 xt3 xt4,
                 ms' = LOOPst 0 d (initial_eof d) 0 m1 ra xt0 xa0 xa1 xa4 xa5 s4 xs9 xt3 xt4 /\ MEMI m m1 d [] ov)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 out) (Z_to_bv 64 outlp) (Z_to_bv 64 inp_a) (Z_to_bv 64 inl) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m (seg_rom usegs)).
  Proof.
    intros until ov. intros CTX NN DPRE DI INP OA OLEN OL ST MI.
    unfold P_EVP_DecodeUpdate. pose proof (word_range sp) as SPR. boxsep.
    pose proof (CTXU_split _ _ _ _ _ CTX) as (C1 & C2 & L80 & C3). clear CTX.
    pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB. pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (munch_refl WW m) as MU. unfold WW in MU. pose proof (wmono_refl usegs m) as WM.
    unfold wz in C1, C3, OL. pose proof (proj1 C2) as RAW.
    carve_frame 112%nat ST.
    unbox SEPo. unbox SEPl. unbox SEPi. do 15 step. box SEPo. box SEPl. box SEPi.
    (* [comment removed for export] *)
    step. fbr. step. step. ubal_by AAL. step. if_lit.
    (* [comment removed for export] *)
    step. step. step.
    unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi.
    st1. change (Z_to_bv 64 nn0) with (wz nn0). rewrite sx32_wz by lia. unfold wz. rewrite NN. step.
    unfold zlength.
    unfold LOOPst, UST, DU_LOOP, DB_NTAB, A_data_ascii2bin. rewrite !Z.add_0_r, !Z.sub_0_r.
    (* [comment removed for export] *)
    assert (JEXIT : forall (e : Z) (x10 x11 x14 x19 : word) mz,
      inl = 0 ->
      rw_cells usegs mz (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk usegs mz lo (bv_unsigned sp + -112) -> mem_inv usegs mz -> munch WW m mz -> wmono usegs m mz ->
      CTXU mz a nn0 raw line -> u8arr usegs mz out obs -> rw_cells usegs mz outlp [C4 (Z_to_bv 64 ov)] -> bytes_at usegs mz inp_a inp ->
      evt usegs (fun ms' => if inl =? 0 then du_final m (mkDR 0 [] d) ms'
          else exists m2 xt0 xa0 xa1 xa4 xa5 xs9 xt3 xt4,
                 ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 (Z_to_bv 64 0) (Z_to_bv 64 out) sp (Z_to_bv 64 inp_a) xa0 xa1
                              (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) xa4 xa5 (Z_to_bv 64 395176) (Z_to_bv 64 a)
                              (Z_to_bv 64 61) (Z_to_bv 64 242) s4 (Z_to_bv 64 224) (Z_to_bv 64 inl) (Z_to_bv 64 inp_a) (Z_to_bv 64 64) xs9 (Z_to_bv 64 (initial_eof d)) (Z_to_bv 64 18446744073709156439)
                              xt3 xt4 (Z_to_bv 64 2) (Z_to_bv 64 255))
                          F (Z_to_bv 64 2155768) fc None m2 (seg_rom usegs) /\ MEMI m m2 d [] ov)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 (Z_to_bv 64 out) sp (Z_to_bv 64 inp_a) x10 x11 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) x14 a5 a6
                 (Z_to_bv 64 a) s2 x19 s4 s5 (Z_to_bv 64 inl) s7 s8 s9 (Z_to_bv 64 e) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20e4b8) fc None mz (seg_rom usegs))).
    { intros e x10 x11 x14 x19 mz I0 FR1 ST1 MI1 MU1 WM1 CU1 OA1 OL1 INP1. rewrite I0. cbn [Z.eqb].
      (* [comment removed for export] *)
      step. step. pose proof FR1 as FR1'. unfold du_frame in FR1'.
      unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi. clear FR1'. step.
      eapply (du_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mz 0 (zlength d) 0 ov nn0 raw obs [] d (C8 (Z_to_bv 64 outlp))); try eassumption; try reflexivity; unfold zlength; try lia. }
    assert (JGO : forall (e : Z) (x10 x11 x14 x19 : word) mz,
      inl <> 0 -> e = initial_eof d ->
      rw_cells usegs mz (bv_unsigned sp + -112) (du_frame (C8 (Z_to_bv 64 outlp)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk usegs mz lo (bv_unsigned sp + -112) -> mem_inv usegs mz -> munch WW m mz -> wmono usegs m mz ->
      rw_cells usegs mz a [C4 (Z_to_bv 64 nn0)] -> u8arr usegs mz (a + 4) raw -> rw_cells usegs mz (a + 84) [C4 (Z_to_bv 64 line); CB 4 [b8 0; b8 0; b8 0; b8 0]] ->
      u8arr usegs mz out obs -> rw_cells usegs mz outlp [C4 (Z_to_bv 64 ov)] -> bytes_at usegs mz inp_a inp ->
      evt usegs (fun ms' => if inl =? 0 then du_final m (mkDR 0 [] d) ms'
          else exists m2 xt0 xa0 xa1 xa4 xa5 xs9 xt3 xt4,
                 ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 (Z_to_bv 64 0) (Z_to_bv 64 out) sp (Z_to_bv 64 inp_a) xa0 xa1
                              (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) xa4 xa5 (Z_to_bv 64 395176) (Z_to_bv 64 a)
                              (Z_to_bv 64 61) (Z_to_bv 64 242) s4 (Z_to_bv 64 224) (Z_to_bv 64 inl) (Z_to_bv 64 inp_a) (Z_to_bv 64 64) xs9 (Z_to_bv 64 (initial_eof d)) (Z_to_bv 64 18446744073709156439)
                              xt3 xt4 (Z_to_bv 64 2) (Z_to_bv 64 255))
                          F (Z_to_bv 64 2155768) fc None m2 (seg_rom usegs) /\ MEMI m m2 d [] ov)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 (Z_to_bv 64 out) sp (Z_to_bv 64 inp_a) x10 x11 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length d))) x14 a5 a6
                 (Z_to_bv 64 a) s2 x19 s4 s5 (Z_to_bv 64 inl) s7 s8 s9 (Z_to_bv 64 e) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20e498) fc None mz (seg_rom usegs))).
    { intros e x10 x11 x14 x19 mz I0 -> FR1 ST1 MI1 MU1 WM1 C11 C21 C31 OA1 OL1 INP1.
      replace (inl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold WW in MU1.
      (* [comment removed for export] *)
      st1. step. step. try if_lit. step. step. step. step. fbr. step. ubnot.
      do 7 step.
      apply evt_done. eexists _, _, _, _, _, _, _, _, _. split; [reflexivity|].
      exists raw, obs. unfold WW. split; [split; [unfold wz; eassumption| split; [eassumption| split; [exact L80| unfold wz; eassumption]]]|].
      split; [exact DPRE|]. split; [eassumption|]. split; [exact OLEN|]. split; [reflexivity|]. split; [unfold wz; eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| eassumption]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length d)) 0) as [D0|DPOS].
    - step. tbr.
      assert (IE : initial_eof d = 0) by (unfold initial_eof; destruct d; [reflexivity| cbn in D0; lia]).
      (* [comment removed for export] *)
      step. step. if_cases EQI; zify_cond EQI.
      + eapply JGO; try eassumption; try lia.
      + eapply JEXIT; try eassumption; try lia. split; [eassumption|]. split; [eassumption|]. split; [exact L80| eassumption].
    - step. fbr.
      (* [comment removed for export] *)
      zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + -1)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      step. ubnot. step. fbr. zstep.
      destruct (nth_error raw (Z.to_nat (Z.of_nat (length d) - 1))) as [cl|] eqn:NL; [| apply nth_error_None in NL; lia].
      pose proof (rd_raw _ _ _ (Z.of_nat (length d) - 1) cl RAW NL ltac:(lia)) as RD.
      replace (a + 4 + (Z.of_nat (length d) - 1)) with (a + 4 + (Z.of_nat (length d) + -1)) in RD by lia. step. clear RD.
      change (zxb cl) with (Z_to_bv 64 (bv_unsigned cl)). pose proof (byte_range cl) as CLR.
      pose proof (prefix_nth raw d _ cl DPRE NL ltac:(lia)) as NTH1. replace (Z.to_nat (Z.of_nat (length d) - 1)) with (length d - 1)%nat in NTH1 by lia.
      step. step. if_cases EQ1; zify_cond EQ1.
      + (* [comment removed for export] *)
        assert (IE : initial_eof d = 0).
        { unfold initial_eof. rewrite NTH1. unfold CH_EQ. replace (bv_unsigned cl =? 61) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r. reflexivity. }
        step. step. if_cases EQI; zify_cond EQI.
        * eapply JGO; try eassumption; try lia.
        * eapply JEXIT; try eassumption; try lia. split; [eassumption|]. split; [eassumption|]. split; [exact L80| eassumption].
      + (* [comment removed for export] *)
        step. step. if_cases EQN1; zify_cond EQN1.
        * (* [comment removed for export] *)
          assert (IE : initial_eof d = 1).
          { unfold initial_eof. rewrite NTH1. unfold CH_EQ. replace (bv_unsigned cl =? 61) with true by (symmetry; apply Z.eqb_eq; lia).
            replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia). replace (1 <? length d)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
          step. if_cases EQI; zify_cond EQI.
          -- eapply JEXIT; try eassumption; try lia. split; [eassumption|]. split; [eassumption|]. split; [exact L80| eassumption].
          -- eapply JGO; try eassumption; try lia.
        * (* [comment removed for export] *)
          zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + -2)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
          step. fbr. zstep.
          destruct (nth_error raw (Z.to_nat (Z.of_nat (length d) - 2))) as [cp|] eqn:NP; [| apply nth_error_None in NP; lia].
          pose proof (rd_raw _ _ _ (Z.of_nat (length d) - 2) cp RAW NP ltac:(lia)) as RD.
          replace (a + 4 + (Z.of_nat (length d) - 2)) with (a + 4 + (Z.of_nat (length d) + -2)) in RD by lia. step. clear RD.
          change (zxb cp) with (Z_to_bv 64 (bv_unsigned cp)). pose proof (byte_range cp) as CPR.
          pose proof (prefix_nth raw d _ cp DPRE NP ltac:(lia)) as NTH2. replace (Z.to_nat (Z.of_nat (length d) - 2)) with (length d - 2)%nat in NTH2 by lia.
          zstep. zstep. zstep.
          assert (IE : initial_eof d = 1 + Z.b2z (bv_unsigned cp + -61 =? 0)).
          { unfold initial_eof. rewrite NTH1, NTH2. unfold CH_EQ. replace (bv_unsigned cl =? 61) with true by (symmetry; apply Z.eqb_eq; lia).
            replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia). replace (1 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
            cbn [andb]. destruct (Z.eqb_spec (bv_unsigned cp) 61) as [E|NE].
            - replace (bv_unsigned cp + -61 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
            - replace (bv_unsigned cp + -61 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
          assert (EV : bv_swrap 32 (Z.b2z ((bv_unsigned cp + -61) mod 18446744073709551616 <? 1) + 1) = initial_eof d).
          { rewrite IE. destruct (Z.eq_dec (bv_unsigned cp) 61) as [E|NE].
            - rewrite E. reflexivity.
            - replace ((bv_unsigned cp + -61) mod 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
              replace (bv_unsigned cp + -61 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
          rewrite EV.
          step. if_cases EQI; zify_cond EQI.
          -- eapply JEXIT; try eassumption; try lia. split; [eassumption|]. split; [eassumption|]. split; [exact L80| eassumption].
          -- eapply JGO; try eassumption; try lia.
  Qed.
End U.
(* [comment removed for export] *)
Section FINAL.
  Context {HCEIL : HeapCeil}.

  Lemma decupdate_spec : decupdate_stmt.
  Proof.
    unfold decupdate_stmt. intros until junk.
    intros A0 A1 A2 A3 A4 INL INPL EC TAB INP OUT CAP OPOS OLP OLA IPOS IEND OEND OL A92 SEPo SEPl SEPi SEPoa SEPla SEPlo SEPio SEPia SEPil ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3 a4. unfold DECUPDATE_STACK, FR_EVP_DecodeUpdate, DECBLOCK_STACK, FR_evp_decodeblock_int in LO. unfold ENCCTX_SIZE in *.
    destruct EC as (raw & line & L80 & DPRE & CELLS & LR & EIN & EBR & DI).
    pose proof EBR as (APOS & AAL & _). pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ OUT) as OA.
    assert (OLEN : length junk = Z.to_nat outsz) by (exact (rw_cells_CB_length _ _ _ _ _ OUT)).
    assert (CAP0 : 0 <= du_outcap d inl) by (unfold du_outcap; apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; unfold zlength; lia]).
    assert (OSZ : Z.of_nat (length junk) = outsz) by lia.
    rewrite <- OSZ in SEPo, SEPoa, SEPlo, SEPio, OEND.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (ctx_chunk_of_enc _ _ _ _ _ CELLS) as CTX.
    (* [comment removed for export] *)
    assert (FIN : forall r ms', du_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a lo line inp junk m r ms' ->
      c8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (dr_rv r) a (dr_d r) p
        [(out, out + outsz); (outlp, outlp + 4); (a, a + 92)]
        (fun m' => exists junk', rw_cells usegs m' out [CB (length (dr_out r)) (map (Z_to_bv 8) (dr_out r)); CB (Z.to_nat outsz - length (dr_out r)) junk']
                   /\ rw_cells usegs m' outlp [C4 (wz (zlength (dr_out r)))] /\ bytes_at usegs m' inp_a inp /\ B64TAB m'
                   /\ (length (dr_out r) <= Z.to_nat outsz)%nat) lo m ms').
    { intros r ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & raw' & obs' & -> & MU & WM & MI' & ST' & CU & DP & DI' & OA' & OLEN' & OP & OL' & INP').
      unfold c8_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. intros z Hz. cbn in Hz |- *. clear -Hz OSZ. lia. }
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      split. { destruct CU as (C1 & C2 & L80' & C3). exists raw', line. split; [exact L80'|]. split; [exact DP|].
               split; [apply enc_of_ctx_chunk; apply CTXU_join; split; [exact C1| split; [exact C2| split; [exact L80'| exact C3]]]|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI']. }
      assert (OPL : (length (dr_out r) <= length obs')%nat).
      { apply (f_equal (@length byte)) in OP. rewrite length_map, length_firstn in OP. lia. }
      exists (skipn (length (dr_out r)) obs').
      split. { apply rw_cells_of_u8arr in OA'.
               apply (rw_cells_CB_split usegs m' out _ (length (dr_out r))) in OA'; [| exact OPL]. destruct OA' as [O1 O2].
               rewrite OP in O1. change [CB (length (dr_out r)) (map (Z_to_bv 8) (dr_out r)); CB (Z.to_nat outsz - length (dr_out r)) (skipn (length (dr_out r)) obs')]
                 with ([CB (length (dr_out r)) (map b8 (dr_out r))] ++ [CB (Z.to_nat outsz - length (dr_out r)) (skipn (length (dr_out r)) obs')]).
               apply rw_cells_app. split; [exact O1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, <- OLEN, <- OLEN'. exact O2. }
      split; [exact OL'|]. split; [exact INP'|]. split; [apply B64TAB_of_mem_inv; exact MI'| rewrite <- OLEN, <- OLEN'; exact OPL]. }
    eapply evt_cut.
    { eapply (s0_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk);
        try eassumption; unfold zlength; try lia; try reflexivity. }
    intros ms1 PO. destruct (Z.eqb_spec inl 0) as [I0|I1].
    - (* [comment removed for export] *)
      replace (inl =? 0) with true in PO by (symmetry; apply Z.eqb_eq; exact I0).
      apply evt_done. assert (inp = []) as -> by (destruct inp; [reflexivity| cbn in INPL; lia]). cbn [map decode_update].
      exact (FIN _ _ PO).
    - replace (inl =? 0) with false in PO by (symmetry; apply Z.eqb_neq; exact I1).
      destruct PO as (m1 & xt0 & xa0 & xa1 & xa4 & xa5 & xs9 & xt3 & xt4 & -> & MEM).
      assert (INP1 : inp <> []) by (intros ->; cbn in INPL; lia).
      replace (decode_update d (map bv_unsigned inp)) with (du_loop (mkDU d (initial_eof d) []) (skipn (Z.to_nat 0) (map bv_unsigned inp)))
        by (unfold decode_update; destruct inp; [congruence| reflexivity]).
      eapply evt_mono; [| intros ms' Q; exact (FIN _ _ Q)].
      change 0 with (zlength (@nil Z)) at 3.
      eapply (loop_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk) with (kk := Z.to_nat inl);
        try eassumption; unfold zlength; try lia; try reflexivity.
      + pose proof (initial_eof d). unfold initial_eof. destruct (_ && _); [destruct (_ && _)|]; lia.
      + cbn [length]. rewrite Z.sub_0_r. unfold du_outcap, zlength in CAP. lia.
      + cbn [length]. rewrite Z.sub_0_r. unfold zlength.
        assert (Z.of_nat (length d) + inl < 64 + 2^20) by lia.
        assert ((Z.of_nat (length d) + inl) / 4 < 2^19) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.
End FINAL.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C8 ECH_AKit ECH_AsKit ECH_AsKitK ECH_AC8_small ECH_AC8_blockA ECH_AC8_block ECH_AC8_final.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ADU_LOOP : Z := 0x42230c.  Definition ADU_J1C : Z := 0x422324.  Definition ADU_ERRX : Z := 0x42258c.  Definition ADU_ST : Z := 0x4223b8.
Definition ADU_ADV : Z := 0x422460.   Definition ADU_TAIL : Z := 0x4224b8. Definition ADU_EXIT : Z := 0x42258c.  Definition ADU_RA1 : Z := 0x4223ec.
Definition ADU_RA2 : Z := 0x4224f0.   Definition ADU_FAIL : Z := 0x3fa208. Definition ADU_J1A0 : Z := 0x422508.  Definition ADU_J1C4 : Z := 0x42252c.
Definition ADU_J1F4 : Z := 0x4225ac.

(* [comment removed for export] *)
Definition adu_frame (j : list byte) (ol shc : word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (Z_to_bv 64 ASHADOW_BASE); C8 shc; C8 ol; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition adu_frame24 (jj : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 24 jj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Section HD.
  Context {HCEIL : HeapCeil}.
  Lemma adu_frame_hd24 : forall m A j ol shc s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra,
    rw_cells asegs m A (adu_frame j ol shc s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells asegs m A (adu_frame24 (le8 (Z_to_bv 64 ASHADOW_BASE) ++ le8 shc ++ le8 ol) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
  Proof.
    intros until ra. intros R.
    eapply rw_cells_recut; [exact R| |].
    - cbn [cells_wf cell_wf adu_frame24]. rewrite !length_app, !length_le8. split; [reflexivity| repeat split; exact I].
    - cbn [cells_bytes cbytes adu_frame adu_frame24]. rewrite <- !app_assoc. reflexivity.
  Qed.
End HD.

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
    rw_cells asegs m a [C4 (wz nn)] /\ u8arr asegs m (a + 4) raw /\ length raw = 80%nat
    /\ rw_cells asegs m (a + 84) [C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]].
  Lemma CTXU_split : forall m a nn raw line, rw_cells asegs m a (ctx_chunk nn raw line) -> CTXU m a nn raw line.
  Proof.
    intros m a nn raw line H. unfold ctx_chunk in H.
    assert (L : length raw = 80%nat) by (destruct H as [[WF _] _]; cbn in WF; tauto).
    change [C4 (wz nn); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz nn)] ++ [CB 80 raw] ++ [C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]]) in H.
    apply rw_cells_app in H. destruct H as [H1 H]. apply rw_cells_app in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H2, H3.
    split; [exact H1|]. split; [apply (u8arr_of_rw_cells asegs m (a + 4) 80 raw); exact H2|]. split; [exact L|].
    replace (a + 84) with (a + Z.of_nat 4 + Z.of_nat 80) by lia. exact H3.
  Qed.
  Lemma CTXU_join : forall m a nn raw line, CTXU m a nn raw line -> rw_cells asegs m a (ctx_chunk nn raw line).
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
Lemma neg_char_lts : forall cb : byte, 128 <= bv_unsigned cb -> bv_lts (Z_to_bv 64 (bv_unsigned cb - 256)) (Z_to_bv 64 0) = true.
Proof.
  intros cb H. pose proof (byte_range cb) as CB. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply Z.leb_le.
  Z.div_mod_to_equations. lia.
Qed.
Lemma b8_of_byte : forall cb : byte, b8 (bv_unsigned cb) = cb.
Proof.
  intros cb. apply bv_eq. unfold b8. rewrite Z_to_bv_unsigned. pose proof (byte_range cb) as CB.
  unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. apply Z.mod_small. cbn. lia.
Qed.
Lemma prefix_snoc : forall (raw : list byte) (d : list Z) (cb : byte),
  map bv_unsigned (firstn (length d) raw) = d -> (length d < length raw)%nat ->
  map bv_unsigned (firstn (S (length d)) (upd_bytes raw (length d) [cb])) = d ++ [bv_unsigned cb].
Proof.
  intros raw d cb P L. unfold upd_bytes.
  replace (S (length d)) with (length (firstn (length d) raw ++ [cb])) by (rewrite length_app, length_firstn; cbn; lia).
  rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r, map_app, P. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma b2z_eq242 : forall (seof : bool) v2, (seof = true <-> v2 = 242) -> 0 <= v2 < 2^63 ->
  Z.b2z (Z.land (v2 + -242) 18446744073709551615 <? 1) = (if seof then 1 else 0).
Proof.
  intros seof v2 SE VR. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. destruct seof.
  - assert (v2 = 242) by (apply SE; reflexivity). subst v2. reflexivity.
  - assert (NE : v2 <> 242) by (intros E; destruct SE as [_ SE2]; specialize (SE2 E); discriminate).
    replace ((v2 + -242) mod 2 ^ 64 <? 1) with false; [reflexivity|]. symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Section U.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Local Ltac b2z_in K := repeat match type of K with context [Z.b2z (?x <? ?y)] =>
      first [rewrite (proj2 (Z.ltb_lt x y) ltac:(lia)) in K | rewrite (proj2 (Z.ltb_ge x y) ltac:(lia)) in K]; cbn [Z.b2z] in K end.
  Local Ltac ubnc := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; b2z_in K; vm_compute in K; congruence | clear K].
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (a out outlp inp_a inl lo line nn0 : Z) (inp obs0 : list byte) (LB : list block) (p : bptr) (m00 : mem).
  Hypothesis A92 : a + 92 <= lo.
  Hypothesis APOS : 0 < a.
  Hypothesis AAL : a mod 16 = 0.
  Hypothesis ACEIL : a + 92 <= aceil.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis INL : 0 <= inl < 2^20.
  Hypothesis INPL : Z.of_nat (length inp) = inl.
  Hypothesis OSZ : 0 < out.
  Hypothesis OMOD : outlp mod 4 = 0.
  Hypothesis OLP : 0 < outlp.
  Hypothesis IPOS : 0 < inp_a.
  Hypothesis IEND : inp_a + inl < 2^64.
  Hypothesis OEND : out + Z.of_nat (length obs0) < 2^64.
  Hypothesis SEPo : out + Z.of_nat (length obs0) <= lo \/ bv_unsigned sp <= out.
  Hypothesis SEPl : outlp + 4 <= lo \/ bv_unsigned sp <= outlp.
  Hypothesis SEPi : inp_a + inl <= lo \/ bv_unsigned sp <= inp_a.
  Hypothesis SEPoa : out + Z.of_nat (length obs0) <= a \/ a + 92 <= out.
  Hypothesis SEPla : outlp + 4 <= a \/ a + 92 <= outlp.
  Hypothesis SEPlo : outlp + 4 <= out \/ out + Z.of_nat (length obs0) <= outlp.
  Hypothesis SEPio : inp_a + inl <= out \/ out + Z.of_nat (length obs0) <= inp_a.
  Hypothesis SEPia : inp_a + inl <= a \/ a + 92 <= inp_a.
  Hypothesis SEPil : inp_a + inl <= outlp \/ outlp + 4 <= inp_a.
  (* [comment removed for export] *)
  Hypothesis NSHo : out + Z.of_nat (length obs0) <= ALOWSH_LO \/ AHI_LO <= out.
  Hypothesis NSHl : outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp.
  Hypothesis NSHi : inp_a + inl <= ALOWSH_LO \/ AHI_LO <= inp_a.
  Hypothesis NSHa : a + 92 <= ALOWSH_LO \/ AHI_LO <= a.
  Hypothesis OAPP : aapp out (Z.of_nat (length obs0)) \/ bv_unsigned sp <= out.
  Hypothesis AAPP : aapp a 92.
  Hypothesis ACCa0 : accessible m00 a 92.
  Hypothesis ACCo0 : accessible m00 out (Z.of_nat (length obs0)).
  Hypothesis ACCl0 : accessible m00 outlp 4.
  Hypothesis ACCi0 : accessible m00 inp_a inl.
  Hypothesis AC00 : ACONST m00.
  Hypothesis LO : lo <= bv_unsigned sp - 192.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis LNR : 0 <= line < 2^32.
  Hypothesis NN0 : 0 <= nn0 < 64.
  (* [comment removed for export] *)
  Local Ltac boxsep := box SEPo; box SEPl; box SEPi; box SEPoa; box SEPla; box SEPlo; box SEPio; box SEPia; box SEPil.
  Let WW : list (Z * Z) := [(lo, bv_unsigned sp); (out, out + Z.of_nat (length obs0)); (a, a + 92)].
  Let SHC : Z := Z.shiftr a 3 + 2147450880.
  (* [comment removed for export] *)
  Local Ltac reacc H0 MU :=
    let A := fresh "ACC" in
    lazymatch type of MU with munch _ m00 ?mc =>
    lazymatch type of H0 with accessible _ ?o ?n =>
      assert (A : accessible mc o n) by
        (eapply accessible_across; [exact H0| exact MU|]; unfold WW;
         repeat (apply Forall_cons; [cbn [fst snd]; first [exact NSHo| exact NSHl| exact NSHi| exact NSHa| (acb; unfold AHI_LO in *; lia)] |]);
         apply Forall_nil) end end.

  (* [comment removed for export] *)
  Definition du_final (r : duresult) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' raw obs,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (dr_rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (WW ++ [(outlp, outlp + 4)]) m00 m' /\ wmono asegs m00 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ CTXU m' a (zlength (dr_d r)) raw line /\ map bv_unsigned (firstn (length (dr_d r)) raw) = dr_d r /\ du_inv (dr_d r)
      /\ u8arr asegs m' out obs /\ length obs = length obs0 /\ firstn (length (dr_out r)) obs = map b8 (dr_out r)
      /\ rw_cells asegs m' outlp [C4 (wz (zlength (dr_out r)))] /\ bytes_at asegs m' inp_a inp.

  (* [comment removed for export] *)
  Lemma adu_exit : forall (rax t0 t1 t2 a0 a1 a2 a4 a5 a6 x18 x19 x21 x22 x23 x24 x25 x26 x27 t4 t5 t6 : word) (m : mem)
      (retv nv rv ov nn : Z) (raw obs : list byte) (dout dd : list Z) (j : list byte),
      rw_cells asegs m outlp [C4 (wz ov)] -> CTXU m a nn raw line ->
      rw_cells asegs m (bv_unsigned sp + -128) (adu_frame j (Z_to_bv 64 outlp) (Z_to_bv 64 SHC) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -128) -> mem_inv asegs m -> munch WW m00 m -> wmono asegs m00 m ->
      u8arr asegs m out obs -> length obs = length obs0 -> firstn (length dout) obs = map b8 dout -> bytes_at asegs m inp_a inp ->
      map bv_unsigned (firstn (length dd) raw) = dd -> du_inv dd ->
      retv = zlength dout -> nv = zlength dd -> 0 <= retv < 2^31 -> - 1 <= rv <= 1 ->
      evt asegs (du_final (mkDR rv dout dd))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) a0 a1 a2 (Z_to_bv 64 nv) a4 a5 a6 (Z_to_bv 64 retv)
                 x18 x19 (Z_to_bv 64 ASHADOW_BASE) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 rv) t4 t5 t6)
            F (Z_to_bv 64 ADU_EXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros OL (C1 & C2 & L80 & C3) FR ST MI MU WM OA OLEN OPRE INP DPRE DI -> -> RR RV.
    unfold ADU_EXIT. unfold adu_frame in FR. pose proof (aword_range sp) as SPR. boxsep. subst SHC. rewrite ASHADOW_BASE_val. acb.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    assert (DL : (length dd < 64)%nat) by (destruct DI as [_ K]; exact K).
    assert (OL64 : (length dout <= length obs0)%nat) by (pose proof (f_equal (@length byte) OPRE) as OP2; rewrite length_map, length_firstn in OP2; lia).
    unfold wz in OL, C1, C3. unfold WW in MU.
    assert (SUBW : sub_fp WW (WW ++ [(outlp, outlp + 4)])) by (unfold WW; intros z Hz; cbn in Hz |- *; clear -Hz; lia).
    apply (munch_weaken _ _ m00 m SUBW) in MU. clear SUBW. unfold WW in MU. cbn [app] in MU.
    reacc ACCl0 MU. reacc ACCa0 MU.
    (* [comment removed for export] *)
    step. step.
    if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - OLP OB; lia); clear - OLP; intros K; lia| clear K].
    step. ubal_by OMOD. step. if_lit.
    step. step.
    rewrite (unsigned_lit outlp) by (clear - OLP OB; lia).
    ck4_load ACC outlp v V1 V2 Ha.
    ck_K 11 ADU_J1F4 KJ.
    { intros tv. red_tset. unfold ADU_J1F4.
      (* [comment removed for export] *)
      unbox SEPl; unbox SEPla; unbox SEPlo; unbox SEPil. st1. box SEPl; box SEPlo; box SEPil.
      step.
      (* [comment removed for export] *)
      match goal with MU' : munch _ m00 ?mc |- _ => clear ACC ACC0; reacc ACCa0 MU' end.
      pose proof (accessible_read8 _ _ (accessible_sub _ _ _ a 8 ACC ltac:(lia) ltac:(lia) ltac:(lia))) as RD.
      rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by lia.
      replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia).
      step. clear RD. rewrite ?ck8_sxb0. step. if_false_by (ck1_bnez_false 0 eq_refl).
      (* [comment removed for export] *)
      unbox SEPia; unbox SEPoa. st1. box SEPia; box SEPoa; box SEPla.
      (* [comment removed for export] *)
      step. do 15 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold du_final. cbn [dr_rv dr_out dr_d].
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, raw, obs.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [split; [unfold wz; exact C1| split; [exact C2| split; [exact L80| exact C3]]]|].
      split; [exact DPRE|]. split; [exact DI|]. split; [exact OA|]. split; [exact OLEN|]. split; [exact OPRE|].
      split; [unfold wz; exact OL| exact INP]. }
    unfold ADU_J1F4 in KJ. ck4_branch_blt outlp v V1 V2 Ha KJ.
  Qed.

  (* [comment removed for export] *)
  Lemma out_split : forall m obs k, u8arr asegs m out obs -> (k <= length obs)%nat ->
    u8arr asegs m out (firstn k obs) /\ u8arr asegs m (out + Z.of_nat k) (skipn k obs).
  Proof.
    intros m obs k OA K. apply rw_cells_of_u8arr in OA. apply (rw_cells_CB_split asegs m out _ k obs) in OA; [| exact K].
    destruct OA as [O1 O2]. split; [eapply u8arr_of_rw_cells; exact O1| eapply u8arr_of_rw_cells; exact O2].
  Qed.
  Lemma out_join : forall m o1 o2, u8arr asegs m out o1 -> u8arr asegs m (out + Z.of_nat (length o1)) o2 -> u8arr asegs m out (o1 ++ o2).
  Proof.
    intros m o1 o2 O1 O2. apply rw_cells_of_u8arr in O1. apply rw_cells_of_u8arr in O2.
    eapply u8arr_of_rw_cells. eapply rw_cells_CB_join; [exact O1| exact O2].
  Qed.

  (* [comment removed for export] *)
  Lemma rv_tail : forall (seof : bool) eof, 0 <= eof ->
    (if seof then 0 else Z.b2z (eof =? 0)) = (if seof || (0 <? eof) then 0 else 1).
  Proof. intros seof eof E. destruct seof; [reflexivity|]. cbn [orb]. destruct (Z.eqb_spec eof 0) as [->|NE]; [reflexivity|]. replace (0 <? eof) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma adu_tail_walk : forall (rax x6 x7 x10 x11 x12 x15 x18 x19 x21 x22 x23 x24 x26 x27 t3x t4x t5x t6x : word) (m : mem)
      (d dout : list Z) (eof v2 : Z) (seof : bool) (raw obs : list byte) (ov : Z) (j : list byte),
      CTXU m a nn0 raw line -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d -> 0 <= eof <= 2 ->
      (seof = true <-> v2 = 242) -> 0 <= v2 < 256 ->
      u8arr asegs m out obs -> length obs = length obs0 -> firstn (length dout) obs = map b8 dout ->
      Z.of_nat (length dout) + 3 * (Z.of_nat (length d) / 4) <= Z.of_nat (length obs0) ->
      Z.of_nat (length dout) + 3 * (Z.of_nat (length d) / 4) < 2^21 ->
      rw_cells asegs m outlp [C4 (wz ov)] -> bytes_at asegs m inp_a inp ->
      rw_cells asegs m (bv_unsigned sp + -128) (adu_frame j (Z_to_bv 64 outlp) (Z_to_bv 64 SHC) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -128) -> mem_inv asegs m -> munch WW m00 m -> wmono asegs m00 m ->
      evt asegs (du_final (du_tail (mkDU d eof dout) seof))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + zlength dout)) x6 x7 sp (Z_to_bv 64 a) x10 x11 x12
                 (Z_to_bv 64 (zlength d)) (Z_to_bv 64 eof) x15 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (zlength dout))
                 x18 x19 (Z_to_bv 64 ASHADOW_BASE) x21 x22 x23 x24 (Z_to_bv 64 v2) x26 x27 t3x t4x t5x t6x)
            F (Z_to_bv 64 ADU_TAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros CU DPRE DI ER SEOF V2R OA OLEN OPRE CAP CAPB OL INP FR ST MI MU WM.
    unfold ADU_TAIL. pose proof (aword_range sp) as SPR. boxsep. rewrite ASHADOW_BASE_val. acb.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    assert (OL64 : (length dout <= length obs0)%nat).
    { apply (f_equal (@length byte)) in OPRE. rewrite length_map, length_firstn in OPRE. lia. }
    assert (SFR : 0 <= (if seof then 0 else 1) <= 1) by (destruct seof; lia).
    unfold zlength. destruct d as [|d0 drest].
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0. step. try if_lit.
      step. step.
      change (du_tail {| du_d := []; du_eof := eof; du_out := dout |} seof) with (mkDR (if seof || (0 <? eof) then 0 else 1) dout []).
      destruct seof.
      + assert (v2 = 242) as -> by (apply SEOF; reflexivity). if_lit.
        (* [comment removed for export] *)
        step. step. cbn [orb].
        eapply adu_exit; try eassumption; try reflexivity; try lia.
      + assert (NE : v2 <> 242) by (intros E; destruct SEOF as [_ S2]; specialize (S2 E); discriminate).
        if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia]. clear K2.
        (* [comment removed for export] *)
        step. if_lit. step. zstep.
        replace (Z.b2z (eof <? 1)) with (if false || (0 <? eof) then 0 else 1) by (destruct (Z.ltb_spec eof 1), (Z.ltb_spec 0 eof); cbn; lia).
        eapply adu_exit; try eassumption; try reflexivity; try lia. destruct (0 <? eof); cbn; lia.
    - (* [comment removed for export] *)
      set (d := d0 :: drest) in *. assert (DPOS : 0 < Z.of_nat (length d)) by (subst d; cbn; lia).
      step. fbr.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. change (Z.land (Z.of_nat (length d)) 3) with (Z.land (Z.of_nat (length d)) (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
      rewrite (b2z_eq242 seof v2 SEOF) by lia.
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
        reacc ACCa0 MU. reacc ACCo0 MU.
        assert (AC : ACONST m).
        { assert (HI : 0x7fff7f800000 <= lo) by (pose proof (proj1 (proj1 aceil_facts)) as K; clear -CEIL K; lia).
          eapply ACONST_frame; [exact AC00| exact MU| exact WM|]. unfold WW.
          apply Forall_cons.
          { apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI; lia| clear -HI; lia]. }
          apply Forall_cons.
          { destruct OAPP as [OP|OP]; [eapply aconst_ok_aapp; [exact OP| clear; lia| clear; lia]|].
          apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI LO OP; lia| clear -HI LO OP; lia]. }
          apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPP| clear; lia| clear; lia]| apply Forall_nil]. }
        eapply evt_cut.
        { unbox SEPoa. unbox SEPo.
          eapply (adecblock_ok_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (tj := skipn (length dout) obs); rewrite ?unsigned_lit by lia;
            try eassumption; try (clear - OSZ; lia); try lia.
          all: try (apply CTXU_join; exact CU).
          all: rewrite ?length_skipn; try lia.
          all: try (eapply accessible_sub; [exact ACC0| lia| lia| lia]). }
        box SEPoa; box SEPo.
        intros ms2 PO. unfold adb_post in PO.
        destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2 & bs2 & OB2 & LB2 & PB2).
        rewrite (unsigned_lit (bv_unsigned sp + -128)) in MU2, ST2 by lia. rewrite length_skipn in LB2. rewrite length_skipn, OLEN in MU2.
        replace (bv_unsigned sp + -128 + -64) with (bv_unsigned sp + -192) in MU2 by lia.
        (* [comment removed for export] *)
        unbox SEPl. unbox SEPlo. unbox SEPo. unbox SEPi. unbox SEPio.
        apply (rw_cells_transport asegs _ m m2 _ _ OL) in MU2 as OL2; [| exact WM2| cbn; lia].
        apply (rw_cells_transport asegs _ m m2 _ _ FR) in MU2 as FR2; [| exact WM2| cbn; lia].
        assert (FR2' := FR2). unfold adu_frame in FR2'.
        assert (INP2 : bytes_at asegs m2 inp_a inp) by (eapply bytes_at_transport; [exact INP| exact MU2| cbn; lia]).
        assert (OA12 : u8arr asegs m2 out (firstn (length dout) obs)).
        { eapply u8arr_transport; [exact OA1| exact MU2| exact WM2|]. rewrite length_firstn. cbn. lia. }
        box SEPl; box SEPlo; box SEPo; box SEPi; box SEPio.
        pose proof (out_join m2 _ _ OA12 ltac:(rewrite length_firstn; replace (Init.Nat.min (length dout) (length obs)) with (length dout) by lia; exact OB2)) as OA2'.
        assert (MU02 : munch WW m00 m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold WW. intros z Hz. cbn in Hz |- *. clear -Hz OL64 AB LO SPR. lia. }
        clear FR.
        (* [comment removed for export] *)
        retpc.
        step. step. if_cases K; zify_cond K; [exfalso; revert K; rewrite ?signed_lit by (clear - QR ER; lia); clear - QR ER; intros K; lia| clear K].
        step. step. step.
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
        match goal with |- evt _ ?Q (MS ?R ?Fm (if _ then ?p1 else _) ?fx ?x ?mm ?rom) => assert (J : evt asegs Q (MS R Fm p1 fx x mm rom)) end.
        { step. step. step.
          assert (KD : 0 <= Z.of_nat (length dout) < 2^21) by (clear - CAPB; Z.div_mod_to_equations; lia).
          rewrite (unsigned_lit (Z.of_nat (length dout))) by (clear - KD; lia). rewrite Z.add_0_r.
          rewrite (bv_swrap_small 32 (Z.of_nat (length dout))) by (change (bv_half_modulus 32) with (2^31); clear - KD; lia).
          rewrite (unsigned_lit (Z.of_nat (length dout))) by (clear - KD; lia).
          rewrite (unsigned_lit (3 * q - eof)) by (clear - QR ER; lia).
          rewrite (bv_swrap_small 32 (Z.of_nat (length dout) + (3 * q - eof))) by (change (bv_half_modulus 32) with (2^31); clear - CAPB QR ER; subst q; Z.div_mod_to_equations; lia).
          step. rewrite bv_eqb_refl. cbn [negb].
          step.
          destruct seof.
          - if_lit. step. step. step. step. cbn [orb]. clear FR2'.
            eapply adu_exit; try eassumption; try reflexivity; try lia.
            all: try (apply CTXU_split; exact CTX2).
            all: try (eapply wmono_trans; [exact WM| exact WM2]).
            all: lazymatch goal with
                 | |- length _ = length obs0 => rewrite length_app, length_firstn, LB2; lia
                 | |- firstn _ _ = map b8 _ => rewrite OPRE; apply prefix_join; rewrite LD; exact PB2
                 | |- du_inv [] => split; [constructor| cbn; lia]
                 | |- _ = zlength _ => unfold zlength; rewrite ?length_app, ?LD; cbn [length]; lia
                 | |- 0 <= _ < 2^31 => clear - CAPB QR ER; subst q; Z.div_mod_to_equations; lia
                 | |- _ => idtac
                 end.
          - if_lit. step. step. zstep.
            replace (Z.b2z (eof <? 1)) with (if false || (0 <? eof) then 0 else 1) by (destruct (Z.ltb_spec eof 1), (Z.ltb_spec 0 eof); cbn; lia). clear FR2'.
            eapply adu_exit; try eassumption; try reflexivity; try lia.
            all: try (apply CTXU_split; exact CTX2).
            all: try (eapply wmono_trans; [exact WM| exact WM2]).
            all: lazymatch goal with
                 | |- length _ = length obs0 => rewrite length_app, length_firstn, LB2; lia
                 | |- firstn _ _ = map b8 _ => rewrite OPRE; apply prefix_join; rewrite LD; exact PB2
                 | |- du_inv [] => split; [constructor| cbn; lia]
                 | |- _ = zlength _ => unfold zlength; rewrite ?length_app, ?LD; cbn [length]; lia
                 | |- 0 <= _ < 2^31 => clear - CAPB QR ER; subst q; Z.div_mod_to_equations; lia
                 | |- _ <= _ <= _ => destruct (0 <? eof); cbn; lia
                 | |- _ => idtac
                 end. }
        if_cases EQ2; [exact J| clear EQ2].
        step. if_cases EQ4; zify_cond EQ4; [exact J| exfalso; revert EQ4; rewrite ?unsigned_lit by (clear - QR ER; lia); clear - QR ER; intros EQ4; lia].
      + (* [comment removed for export] *)
        assert (TL : du_tail (mkDU d eof dout) seof = if seof then mkDR (-1) dout d else mkDR 1 dout d).
        { unfold du_tail. cbn [du_d du_eof du_out]. replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
          replace (length d mod 4 =? 0)%nat with false; [destruct seof; reflexivity|].
          symmetry. apply Nat.eqb_neq. intros KK. apply EQ1. change 4 with (Z.of_nat 4). rewrite <- Nat2Z.inj_mod, KK. reflexivity. }
        rewrite TL.
        destruct seof.
        * step. step. step.
          match goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?t3v _ _ _)] =>
            replace t3v with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity) end.
          eapply adu_exit; try eassumption; try reflexivity; unfold zlength; try lia.
          all: try (apply CTXU_split; apply CTXU_join; exact CU).
        * step. step. step.
          match goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?t3v _ _ _)] =>
            replace t3v with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity) end.
          eapply adu_exit; try eassumption; try reflexivity; unfold zlength; try lia.
  Qed.
  (* [comment removed for export] *)
  Lemma AC_now : forall m, munch WW m00 m -> wmono asegs m00 m -> ACONST m.
  Proof.
    intros m MU WM.
    assert (HI : 0x7fff7f800000 <= lo) by (pose proof (proj1 (proj1 aceil_facts)) as K; clear -CEIL K; lia).
    eapply ACONST_frame; [exact AC00| exact MU| exact WM|]. unfold WW.
    apply Forall_cons.
    { apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI; lia| clear -HI; lia]. }
    apply Forall_cons.
    { destruct OAPP as [OP|OP]; [eapply aconst_ok_aapp; [exact OP| clear; lia| clear; lia]|].
      apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI LO OP; lia| clear -HI LO OP; lia]. }
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPP| clear; lia| clear; lia]| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Definition ALOOPst (i : Z) (d : list Z) (eof k : Z) (m : mem) (rax t2x a1x a2x s2x s9x s10x s11x t3x : word) : machine_state :=
    MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + k)) (Z_to_bv 64 18446744073708761311) t2x sp (Z_to_bv 64 a)
             (Z_to_bv 64 (inp_a + i)) a1x a2x (Z_to_bv 64 (Z.of_nat (length d))) (Z_to_bv 64 eof) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 k)
             s2x (Z_to_bv 64 242) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 64) s9x s10x s11x
             t3x (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
       F (Z_to_bv 64 ADU_LOOP) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition achar_post (i : Z) (d : list Z) (k : Z) (m : mem) (obs : list byte) (ov : Z) (j : list byte) (rax : word) (cls : cclass)
      : machine_state -> Prop := fun ms' =>
    match cls with
    | CErr => exists t0y t1y t2y a0y a1y a2y a4y a5y a6y x18 x19 x21 x22 x23 x24 x25 x26 x27 t4y t5y t6y : word,
        ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0y t1y t2y sp (Z_to_bv 64 a) a0y a1y a2y
                      (Z_to_bv 64 (Z.of_nat (length d))) a4y a5y a6y (Z_to_bv 64 k)
                      x18 x19 (Z_to_bv 64 ASHADOW_BASE) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (-1)) t4y t5y t6y)
                 F (Z_to_bv 64 ADU_ERRX) fc None m (seg_rom asegs)
    | CEof e1 => exists t1y t2y a0y a1y a2y a5y x18 x19 x21 x22 x23 x24 x26 x27 t3y t4y t5y t6y : word,
        ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + k)) t1y t2y sp (Z_to_bv 64 a) a0y a1y a2y
                      (Z_to_bv 64 (Z.of_nat (length d))) (Z_to_bv 64 e1) a5y (Z_to_bv 64 (a + 4)) (Z_to_bv 64 k)
                      x18 x19 (Z_to_bv 64 ASHADOW_BASE) x21 x22 x23 x24 (Z_to_bv 64 242) x26 x27 t3y t4y t5y t6y)
                 F (Z_to_bv 64 ADU_TAIL) fc None m (seg_rom asegs)
    | CGo d1 e1 => exists (t2y a0y a1y a2y s10y s11y : word) (v : Z) m' raw',
        ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + k)) (Z_to_bv 64 18446744073708761311) t2y sp (Z_to_bv 64 a)
                      a0y a1y a2y (Z_to_bv 64 (Z.of_nat (length d1))) (Z_to_bv 64 e1) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 k)
                      (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 242) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 64)
                      (Z_to_bv 64 v) s10y s11y (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
                 F (Z_to_bv 64 ADU_ST) fc None m' (seg_rom asegs)
        /\ (0 <= v < 256 /\ v <> 242)
        /\ CTXU m' a nn0 raw' line /\ map bv_unsigned (firstn (length d1) raw') = d1
        /\ bytes_at asegs m' inp_a inp /\ mem_inv asegs m' /\ u8arr asegs m' out obs /\ rw_cells asegs m' outlp [C4 (wz ov)]
        /\ rw_cells asegs m' (bv_unsigned sp + -128) (adu_frame j (Z_to_bv 64 outlp) (Z_to_bv 64 SHC) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
        /\ stk asegs m' lo (bv_unsigned sp + -128) /\ munch WW m00 m' /\ wmono asegs m00 m'
    end.

  Local Ltac cls_done CL :=
    lazymatch goal with |- evt _ (achar_post _ _ _ _ _ _ _ _ (classify ?d ?e ?c)) _ =>
      replace (classify d e c) with CL; [apply evt_done; unfold achar_post, ADU_ERRX, ADU_TAIL, ADU_ST | ] end.

  (* [comment removed for export] *)
  Lemma ab_char : forall (i eof k : Z) (d : list Z) (m : mem) (raw obs : list byte) (ov : Z) (cb : byte) (j : list byte)
      (rax t2x a1x a2x s2x s9x s10x s11x t3x : word),
      0 <= i < inl -> nth_error inp (Z.to_nat i) = Some cb -> 0 <= k <= Z.of_nat (length obs0) ->
      CTXU m a nn0 raw line -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d -> 0 <= eof <= 2 ->
      bytes_at asegs m inp_a inp -> mem_inv asegs m -> u8arr asegs m out obs -> length obs = length obs0 -> rw_cells asegs m outlp [C4 (wz ov)] ->
      rw_cells asegs m (bv_unsigned sp + -128) (adu_frame j (Z_to_bv 64 outlp) (Z_to_bv 64 SHC) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -128) -> munch WW m00 m -> wmono asegs m00 m ->
      evt asegs (achar_post i d k m obs ov j rax (classify d eof (bv_unsigned cb)))
        (ALOOPst i d eof k m rax t2x a1x a2x s2x s9x s10x s11x t3x).
  Proof.
    intros until t3x. intros IR NTH KR CU DPRE DI ER INP MI OA OLEN OL FR ST MU WM.
    unfold ALOOPst, ADU_LOOP, A_data_ascii2bin. pose proof (aword_range sp) as SPR. boxsep. rewrite ASHADOW_BASE_val. acb.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (byte_range cb) as CB. set (c := bv_unsigned cb) in *.
    pose proof (AC_now m MU WM) as AC. pose proof (tab_accessible _ AC) as TACC. unfold A_data_ascii2bin in TACC.
    reacc ACCa0 MU. reacc ACCi0 MU.
    unfold WW in MU. unfold wz in C1, C3, OL. assert (FR' := FR). unfold adu_frame in FR'.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - IPOS IEND IR; lia); clear - IPOS IEND IR; intros K; lia| clear K].
    step. step. rewrite (unsigned_lit (inp_a + i)) by (clear - IPOS IEND IR; lia).
    ck1_load ACC0 (inp_a + i) v V1 V2 Ha.
    ck_K 12 ADU_J1C KJ.
    { intros tv. red_tset. unfold ADU_J1C.
      (* [comment removed for export] *)
      pose proof (rd_raw _ _ _ i cb INP NTH ltac:(lia)) as RD. step. clear RD. step.
      destruct (Z.lt_ge_cases c 128) as [CLO|CHI].
      2:{ (* [comment removed for export] *)
          rewrite (sxb_big cb) by lia. step. if_true_by (neg_char_lts cb ltac:(exact CHI)).
          cls_done CErr; [do 21 eexists; reflexivity|].
          unfold classify. rewrite (a2b_high c) by lia. reflexivity. }
      rewrite (sxb_small cb) by lia. fold c.
      destruct (a2b_facts c ltac:(lia)) as [NBL VR].
      step. fbr.
      (* [comment removed for export] *)
      step. if_cases K6; zify_cond K6; [exfalso; revert K6; rewrite ?unsigned_lit by (clear - CB CLO; lia); clear - CLO; intros K6; lia| clear K6].
      zstep. zstep. zstep. ck1f_load TACC (790304 + c). step. if_false_by (ck1_bnez_false 0 eq_refl).
      (* [comment removed for export] *)
      pose proof (rd_tab _ c MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD. unfold wz.
      step. if_cases EQE; zify_cond EQE.
      { cls_done CErr; [do 21 eexists; reflexivity|].
        unfold classify, B64_ERROR. replace (a2b c =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      assert (E255 : (a2b c =? B64_ERROR) = false) by (apply Z.eqb_neq; unfold B64_ERROR; lia).
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      assert (J115 : forall e1 (a2y : word), 0 <= e1 <= 2 -> a2b c <> 242 ->
        classify d eof c = CGo (if b64_base64 (a2b c) then d ++ [c] else d) e1 ->
        evt asegs (achar_post i d k m obs ov j rax (classify d eof c))
          (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + k)) (Z_to_bv 64 18446744073708761311) t2x sp (Z_to_bv 64 a)
                   (Z_to_bv 64 (Z.land (a2b c) 236)) (Z_to_bv 64 c) a2y (Z_to_bv 64 (Z.of_nat (length d))) (Z_to_bv 64 e1) (Z_to_bv 64 790304) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 k)
                   (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 242) (Z_to_bv 64 2147450880) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 64)
                   (Z_to_bv 64 (a2b c)) s10x s11x (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
              F (Z_to_bv 64 0x422378) fc None m (seg_rom asegs))).
      { intros e1 a2y E1R NE CL.
        (* [comment removed for export] *)
        step. if_cases EQB; zify_cond EQB.
        - (* [comment removed for export] *)
          assert (BF : b64_base64 (a2b c) = false).
          { destruct (b64_base64 (a2b c)); [| reflexivity]. cbn in NBL. apply Z.eqb_neq in NBL. exfalso. lia. }
          rewrite CL, BF. apply evt_done. unfold achar_post, ADU_ST.
          eexists _, _, _, _, _, _, (a2b c), m, raw. split; [reflexivity|]. split; [clear - VR NE; lia|].
          split; [exact CU|]. split; [exact DPRE|]. split; [exact INP|]. split; [exact MI|]. split; [exact OA|]. split; [unfold wz; exact OL|].
          split; [exact FR|]. split; [exact ST|]. split; [exact MU| exact WM].
        - (* [comment removed for export] *)
          assert (BT : b64_base64 (a2b c) = true).
          { destruct (b64_base64 (a2b c)); [reflexivity|]. cbn in NBL. apply Z.eqb_eq in NBL. exfalso. lia. }
          rewrite CL, BT.
          step. step. if_cases KN; zify_cond KN; rewrite ?signed_lit in KN by (clear - DL; lia); [exfalso; clear - KN DL; lia| clear KN].
          (* [comment removed for export] *)
          step. step. if_cases KZ; zify_cond KZ.
          { exfalso; revert KZ; rewrite ?unsigned_lit by (clear - APOS ACEIL CEIL LO SPR DL; lia); clear - APOS DL; intros KZ; lia. }
          clear KZ.
          (* [comment removed for export] *)
          assert (SU : v_sltu (Z_to_bv 64 (Z.of_nat (length d) + (a + 4))) (Z_to_bv 64 (a + 4)) = Z_to_bv 64 0).
          { rewrite v_sltu_b2z, !unsigned_lit by (clear - APOS ACEIL CEIL LO SPR DL; lia).
            replace (Z.of_nat (length d) + (a + 4) <? a + 4) with false by (symmetry; apply Z.ltb_ge; clear - DL; lia). reflexivity. }
          assert (SI : v_slti (Z_to_bv 64 (Z.of_nat (length d))) 0 = Z_to_bv 64 0).
          { rewrite v_slti_b2z, unsigned_lit by (clear - DL; lia). rewrite zb_lxor_sign by (clear - DL; lia).
            rewrite Z.mod_small by (clear - DL; lia).
            replace (Z.of_nat (length d) + 2^63 <? 0 + 2^63) with false by (symmetry; apply Z.ltb_ge; clear - DL; lia). reflexivity. }
          step. step. step. step. step. rewrite SU, SI. if_lit. clear SU SI.
          (* [comment removed for export] *)
          rewrite (Z.add_comm (Z.of_nat (length d)) (a + 4)).
          zstep. zstep. ck1f_load ACC (a + 4 + Z.of_nat (length d)). step. if_false_by (ck1_bnez_false 0 eq_refl).
          zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + 1)) by (change (bv_half_modulus 32) with (2^31)%Z; clear - DL; lia).
          unbox SEPia. unbox SEPoa. unbox SEPla.
          pose proof (u8arr_store_ok asegs m (a + 4) raw (Z.of_nat (length d)) (wa (a + 4 + Z.of_nat (length d))) C2 ltac:(lia) eq_refl) as SOK.
          step. rewrite le1_mod. rewrite (Z.mod_small c 256) by lia. replace (b8 c) with cb by (subst c; symmetry; apply b8_of_byte).
          pose proof (u8arr_write_bytes asegs m (a + 4) raw (Z.of_nat (length d)) [cb] C2 ltac:(lia) ltac:(cbn; lia)) as C2'.
          clear C2. store_done.
          box SEPia. box SEPoa. box SEPla.
          apply evt_done. unfold achar_post, ADU_ST.
          eexists _, _, _, _, _, _, (a2b c), _, (upd_bytes raw (Z.to_nat (Z.of_nat (length d))) [cb]).
          split. { rewrite length_app. cbn [length]. replace (Z.of_nat (length d + 1)) with (Z.of_nat (length d) + 1) by (clear - DL; lia). reflexivity. }
          split; [clear - VR NE; lia|].
          split. { split; [unfold wz; exact C1|]. split; [exact C2'|]. split; [rewrite upd_bytes_length by (cbn; lia); exact L80| unfold wz; exact C3]. }
          split. { rewrite Nat2Z.id, length_app. cbn [length]. rewrite Nat.add_1_r. apply prefix_snoc; [exact DPRE| lia]. }
          split; [exact INP|]. split; [exact MI|]. split; [exact OA|]. split; [unfold wz; exact OL|].
          split; [exact FR|]. split; [exact ST|]. split; [exact MU| exact WM]. }
      (* [comment removed for export] *)
      step. if_cases EQC; zify_cond EQC.
      - (* [comment removed for export] *)
        step. if_cases EQZ; zify_cond EQZ.
        + (* [comment removed for export] *)
          assert (E0 : eof = 0) by (clear - EQZ ER; lia). subst eof.
          step. step. if_cases EQF; zify_cond EQF.
          * cls_done (CEof 0); [rewrite EQF; do 18 eexists; reflexivity|].
            unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
            cbn [negb andb Z.ltb]. unfold B64_EOF. replace (a2b c =? 242) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
          * step. apply (J115 0 (Z_to_bv 64 0)); [lia| lia|].
            unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
            cbn [negb andb Z.ltb]. unfold B64_EOF. replace (a2b c =? 242) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        + (* [comment removed for export] *)
          assert (EP : 0 < eof) by (clear - EQZ0 ER; lia).
          step. if_cases EQB; zify_cond EQB.
          * assert (BT : b64_base64 (a2b c) = true).
            { destruct (b64_base64 (a2b c)); [reflexivity|]. cbn in NBL. apply Z.eqb_eq in NBL. exfalso. lia. }
            cls_done CErr; [do 21 eexists; reflexivity|].
            unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (0 <? eof) with true by (symmetry; apply Z.ltb_lt; lia). rewrite BT. reflexivity.
          * assert (BF : b64_base64 (a2b c) = false).
            { destruct (b64_base64 (a2b c)); [| reflexivity]. cbn in NBL. apply Z.eqb_neq in NBL. exfalso. lia. }
            step. if_cases EQF; zify_cond EQF.
            -- cls_done (CEof eof); [rewrite EQF; do 18 eexists; reflexivity|].
               unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
               rewrite BF, andb_false_r. replace (2 <? eof) with false by (symmetry; apply Z.ltb_ge; lia).
               unfold B64_EOF. replace (a2b c =? 242) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
            -- apply (J115 eof (Z_to_bv 64 0)); [lia| lia|].
               unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; lia).
               rewrite BF, andb_false_r. replace (2 <? eof) with false by (symmetry; apply Z.ltb_ge; lia).
               unfold B64_EOF. replace (a2b c =? 242) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - (* [comment removed for export] *)
        step. step. if_cases EQT; zify_cond EQT; rewrite ?signed_lit in EQT by (clear - ER; lia).
        + cls_done CErr; [do 21 eexists; reflexivity|].
          unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
          replace (2 <? eof + 1) with true by (symmetry; apply Z.ltb_lt; clear - EQT ER; lia). reflexivity.
        + assert (E1 : eof <= 1) by (clear - EQT ER; lia).
          zstep. rewrite (bv_swrap_small 32 (eof + 1)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
          step. if_cases EQF; zify_cond EQF.
          * cls_done (CEof (eof + 1)); [rewrite EQF; do 18 eexists; reflexivity|].
            unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
            replace (2 <? eof + 1) with false by (symmetry; apply Z.ltb_ge; lia).
            unfold B64_EOF. replace (a2b c =? 242) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
          * step. apply (J115 (eof + 1) (Z_to_bv 64 1)); [lia| lia|].
            unfold classify. cbv zeta. rewrite E255. unfold CH_EQ. replace (c =? 61) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
            replace (2 <? eof + 1) with false by (symmetry; apply Z.ltb_ge; lia).
            unfold B64_EOF. replace (a2b c =? 242) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    (* [comment removed for export] *)
    unfold ADU_J1C in KJ. ck1_branch_bge (inp_a + i) v V1 V2 Ha KJ.
  Qed.
  (* [comment removed for export] *)
  Definition MEMI (m : mem) (d dout : list Z) (ov : Z) (j : list byte) : Prop :=
    exists raw obs, CTXU m a nn0 raw line /\ map bv_unsigned (firstn (length d) raw) = d
      /\ u8arr asegs m out obs /\ length obs = length obs0 /\ firstn (length dout) obs = map b8 dout
      /\ rw_cells asegs m outlp [C4 (wz ov)] /\ bytes_at asegs m inp_a inp
      /\ rw_cells asegs m (bv_unsigned sp + -128) (adu_frame j (Z_to_bv 64 outlp) (Z_to_bv 64 SHC) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk asegs m lo (bv_unsigned sp + -128) /\ mem_inv asegs m /\ munch WW m00 m /\ wmono asegs m00 m.

  (* [comment removed for export] *)
  Definition flush (d1 : list Z) (e1 : Z) (dout : list Z) : list Z * list Z :=
    if Nat.eqb (length d1) 64 then ([], dout ++ firstn (Z.to_nat (48 - e1)) (groups_bytes (map a2b d1))) else (d1, dout).

  (* [comment removed for export] *)
  Lemma ab_flush_adv : forall (i e1 : Z) (d1 dout : list Z) (m : mem) (ov : Z) (j : list byte) (v : Z)
      (rax t2x a0x a1x a2x s10x s11x : word),
      0 <= i < inl -> Forall b64_saved d1 -> (length d1 <= 64)%nat -> 0 <= e1 <= 2 ->
      zlength dout + 3 * ((zlength d1 + (inl - i - 1)) / 4) <= Z.of_nat (length obs0) ->
      zlength dout + 3 * ((zlength d1 + (inl - i - 1)) / 4) < 2^21 ->
      MEMI m d1 dout ov j ->
      evt asegs (fun ms' => exists m2 rax' t2' a1' a2' s2' s10' s11' t3',
          let fd := flush d1 e1 dout in
          ms' = MS (mkR rax' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + zlength (snd fd))) (Z_to_bv 64 18446744073708761311) t2' sp (Z_to_bv 64 a)
                        (Z_to_bv 64 (inp_a + (i + 1))) a1' a2' (Z_to_bv 64 (zlength (fst fd))) (Z_to_bv 64 e1) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (zlength (snd fd)))
                        s2' (Z_to_bv 64 242) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 224) (Z_to_bv 64 (inl - (i + 1))) (Z_to_bv 64 (inp_a + (i + 1))) (Z_to_bv 64 64) (Z_to_bv 64 v) s10' s11'
                        t3' (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
                   F (Z_to_bv 64 (if i + 1 <? inl then ADU_LOOP else ADU_TAIL)) fc None m2 (seg_rom asegs)
          /\ MEMI m2 (fst fd) (snd fd) ov j /\ (length (fst fd) < 64)%nat /\ Forall b64_saved (fst fd)
          /\ zlength (snd fd) + 3 * ((zlength (fst fd) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0)
          /\ zlength (snd fd) + 3 * ((zlength (fst fd) + (inl - (i + 1))) / 4) < 2^21)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + zlength dout)) (Z_to_bv 64 18446744073708761311) t2x sp (Z_to_bv 64 a)
                 a0x a1x a2x (Z_to_bv 64 (zlength d1)) (Z_to_bv 64 e1) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (zlength dout))
                 (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 242) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 64)
                 (Z_to_bv 64 v) s10x s11x (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
            F (Z_to_bv 64 ADU_ST) fc None m (seg_rom asegs)).
  Proof.
    intros until s11x. intros IR SAVED DL E1 CAP CAPB (raw & obs & CU & DPRE & OA & OLEN & OPRE & OL & INP & FR & ST & MI & MU & WM).
    unfold ADU_ST, ADU_LOOP, ADU_TAIL, A_data_ascii2bin, zlength in *. pose proof (aword_range sp) as SPR. boxsep. rewrite ASHADOW_BASE_val. acb.
    pose proof CU as (C1 & C2 & L80 & C3). pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
    pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (OL64 : (length dout <= length obs0)%nat).
    { apply (f_equal (@length byte)) in OPRE. rewrite length_map, length_firstn in OPRE. lia. }
    assert (DIV0 : forall x, 0 <= x -> 0 <= x / 4) by (intros x Hx; apply Z.div_pos; lia).
    pose proof (DIV0 (Z.of_nat (length d1) + (inl - i - 1)) ltac:(lia)) as DV.
    (* [comment removed for export] *)
    assert (ADV : forall m2 (d2 dout2 : list Z) (rax' t2' a0' a1' a2' s10' s11' t3' : word),
      flush d1 e1 dout = (d2, dout2) -> MEMI m2 d2 dout2 ov j -> (length d2 < 64)%nat -> Forall b64_saved d2 ->
      Z.of_nat (length dout2) + 3 * ((Z.of_nat (length d2) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0) ->
      Z.of_nat (length dout2) + 3 * ((Z.of_nat (length d2) + (inl - (i + 1))) / 4) < 2^21 ->
      evt asegs (fun ms' => exists m3 rax'' t2'' a1'' a2'' s2'' s10'' s11'' t3'',
          let fd := flush d1 e1 dout in
          ms' = MS (mkR rax'' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + Z.of_nat (length (snd fd)))) (Z_to_bv 64 18446744073708761311) t2'' sp (Z_to_bv 64 a)
                        (Z_to_bv 64 (inp_a + (i + 1))) a1'' a2'' (Z_to_bv 64 (Z.of_nat (length (fst fd)))) (Z_to_bv 64 e1) (Z_to_bv 64 790304) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length (snd fd))))
                        s2'' (Z_to_bv 64 242) (Z_to_bv 64 2147450880) (Z_to_bv 64 224) (Z_to_bv 64 (inl - (i + 1))) (Z_to_bv 64 (inp_a + (i + 1))) (Z_to_bv 64 64) (Z_to_bv 64 v) s10'' s11''
                        t3'' (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
                   F (Z_to_bv 64 (if i + 1 <? inl then 4334348 else 4334776)) fc None m3 (seg_rom asegs)
          /\ MEMI m3 (fst fd) (snd fd) ov j /\ (length (fst fd) < 64)%nat /\ Forall b64_saved (fst fd)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) <= Z.of_nat (length obs0)
          /\ Z.of_nat (length (snd fd)) + 3 * ((Z.of_nat (length (fst fd)) + (inl - (i + 1))) / 4) < 2^21)
        (MS (mkR rax' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (out + Z.of_nat (length dout2))) (Z_to_bv 64 18446744073708761311) t2' sp (Z_to_bv 64 a)
                 a0' a1' a2' (Z_to_bv 64 (Z.of_nat (length d2))) (Z_to_bv 64 e1) (Z_to_bv 64 790304) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (Z.of_nat (length dout2)))
                 (Z_to_bv 64 (inp_a + i + 1)) (Z_to_bv 64 242) (Z_to_bv 64 2147450880) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (inp_a + i)) (Z_to_bv 64 64) (Z_to_bv 64 v) s10' s11'
                 t3' (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 61))
            F (Z_to_bv 64 ADU_ADV) fc None m2 (seg_rom asegs))).
    { intros m2 d2 dout2 rax' t2' a0' a1' a2' s10' s11' t3' FD MI2 DL2 SV2 CAP2 CAPB2. rewrite FD. cbn [fst snd]. unfold ADU_ADV.
      destruct MI2 as (raw2 & obs2 & CU2 & DPRE2 & OA2 & OLEN2 & OPRE2 & OL2 & INP2 & FR2 & ST2 & MI2 & MU2 & WM2). unfold WW in MU2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. try rewrite (unsigned_lit (inl - i)) by lia. try rewrite (bv_swrap_small 32 (inl - i + -1)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      step. if_cases EQL; zify_cond EQL.
      - replace (i + 1 <? inl) with true by (symmetry; apply Z.ltb_lt; lia).
        apply evt_done. eexists m2, _, _, _, _, _, _, _, _.
        try replace (inl - i + -1) with (inl - (i + 1)) by lia. try replace (inl - i - 1) with (inl - (i + 1)) by lia. replace (inp_a + i + 1) with (inp_a + (i + 1)) by lia.
        rewrite ?ASHADOW_BASE_val.
        split; [reflexivity|]. split; [exists raw2, obs2; unfold WW; repeat (split; [eassumption|]); exact WM2|]. repeat (split; [first [exact DL2| exact SV2| exact CAP2]|]). exact CAPB2.
      - replace (i + 1 <? inl) with false by (symmetry; apply Z.ltb_ge; lia).
        step. apply evt_done. eexists m2, _, _, _, _, _, _, _, _.
        try replace (inl - i + -1) with (inl - (i + 1)) by lia. try replace (inl - i - 1) with (inl - (i + 1)) by lia. replace (inp_a + i + 1) with (inp_a + (i + 1)) by lia.
        rewrite ?ASHADOW_BASE_val.
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
      remember (Z_to_bv 64 18446744073708761311) as NT eqn:HNT.
      do 11 step. step.
      destruct (out_split m obs (length dout) OA ltac:(lia)) as [OA1 OAR].
      assert (SAVED' : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * 16)) raw))).
      { change (Z.to_nat (4 * 16)) with 64%nat. rewrite <- L64, DPRE. exact SAVED. }
      pose proof (AC_now m MU WM) as AC. reacc ACCa0 MU. reacc ACCo0 MU.
      eapply evt_cut.
      { unbox SEPoa. unbox SEPo.
        eapply (adecblock_ok_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (q := 16) (tj := skipn (length dout) obs); rewrite ?unsigned_lit by lia;
          try eassumption; try lia.
        all: try (apply CTXU_join; exact CU).
        all: rewrite ?length_skipn; try lia.
        all: try (eapply accessible_sub; [exact ACC0| lia| lia| lia]). }
      box SEPoa; box SEPo.
      intros ms2 PO. unfold adb_post in PO.
      destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2 & bs2 & OB2 & LB2 & PB2).
      rewrite (unsigned_lit (bv_unsigned sp + -128)) in MU2, ST2 by lia. rewrite length_skipn in LB2. rewrite length_skipn, OLEN in MU2.
      replace (bv_unsigned sp + -128 + -64) with (bv_unsigned sp + -192) in MU2 by lia.
      unbox SEPl. unbox SEPlo. unbox SEPo. unbox SEPi. unbox SEPio. unfold WW in MU.
      apply (rw_cells_transport asegs _ m m2 _ _ OL) in MU2 as OL2; [| exact WM2| cbn; lia].
      apply (rw_cells_transport asegs _ m m2 _ _ FR) in MU2 as FR2; [| exact WM2| cbn; lia].
      assert (INP2 : bytes_at asegs m2 inp_a inp) by (eapply bytes_at_transport; [exact INP| exact MU2| cbn; lia]).
      assert (OA12 : u8arr asegs m2 out (firstn (length dout) obs)).
      { eapply u8arr_transport; [exact OA1| exact MU2| exact WM2|]. rewrite length_firstn. cbn. lia. }
      box SEPl; box SEPlo; box SEPo; box SEPi; box SEPio.
      pose proof (out_join m2 _ _ OA12 ltac:(rewrite length_firstn; replace (Init.Nat.min (length dout) (length obs)) with (length dout) by lia; exact OB2)) as OA2'.
      assert (MU02 : munch WW m00 m2).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold WW. intros z Hz. cbn in Hz |- *. clear -Hz OL64 AB LO SPR. lia. }
      assert (VS : vs 16 raw = map a2b d1).
      { unfold vs. change (Z.to_nat (4 * 16)) with 64%nat. rewrite <- L64, DPRE. reflexivity. }
      rewrite VS in PB2. try replace (3 * 16 - e1)%Z with (48 - e1) in PB2 by lia.
      set (dec := firstn (Z.to_nat (48 - e1)) (groups_bytes (map a2b d1))) in *.
      assert (LD : length dec = Z.to_nat (48 - e1)).
      { subst dec. rewrite length_firstn, (groups_bytes_length 16); [lia|]. rewrite length_map. exact L64. }
      (* [comment removed for export] *)
      unfold ADU_RA1 in *. retpc.
      try replace (3 * 16 - e1) with (48 - e1) by lia.
      step. fbr.
      step. step. step.
      lazymatch goal with |- evt _ ?Q (MS ?rg ?fr (if _ then ?p1 else _) ?cs ?rs ?mm ?rom) =>
        assert (J : forall pcx, pcx = p1 -> evt asegs Q (MS rg fr pcx cs rs mm rom)) end.
      { intros pcx ->.
        (* [comment removed for export] *)
        step. step. step.
        assert (KD : 0 <= Z.of_nat (length dout) < 2^21) by (clear - CAPB DV; lia).
        try rewrite (unsigned_lit (Z.of_nat (length dout))) by (clear - KD; lia). try rewrite Z.add_0_r.
        rewrite (bv_swrap_small 32 (Z.of_nat (length dout))) by (change (bv_half_modulus 32) with (2^31); clear - KD; lia).
        try rewrite (unsigned_lit (Z.of_nat (length dout))) by (clear - KD; lia).
        try rewrite (unsigned_lit (48 - e1)) by (clear - E1; lia).
        rewrite (bv_swrap_small 32 (Z.of_nat (length dout) + (48 - e1))) by (change (bv_half_modulus 32) with (2^31); clear - KD E1; lia).
        step. try rewrite bv_eqb_refl. cbn [negb].
        step. step. assert (FR2' := FR2). unfold adu_frame in FR2'. step. do 7 step.
        step. fbr. step. step. step. step. step. ubnc. do 4 step. clear FR2'.
        try replace (48 - e1 + Z.of_nat (length dout)) with (Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        try replace (Z.of_nat (length dout) + (48 - e1)) with (Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        try replace (out + Z.of_nat (length dout) + (48 - e1)) with (out + Z.of_nat (length (dout ++ dec))) by (rewrite length_app, LD; lia).
        change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length Z []))).
        subst NT.
        rewrite ?ASHADOW_BASE_val.
        eapply ADV; [exact FD| | cbn; lia| constructor| |].
        - exists raw, (firstn (length dout) obs ++ bs2). unfold WW.
          split; [apply CTXU_split; exact CTX2|]. split; [reflexivity|]. split; [exact OA2'|].
          split; [rewrite length_app, length_firstn, LB2; lia|].
          split; [rewrite OPRE; apply prefix_join; rewrite LD; exact PB2|].
          split; [exact OL2|]. split; [exact INP2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
          split; [exact MU02| eapply wmono_trans; [exact WM| exact WM2]].
        - rewrite length_app, LD. cbn [length]. clear -CAP E1 L64 IR DIV0. Z.div_mod_to_equations. lia.
        - rewrite length_app, LD. cbn [length]. clear -CAPB E1 L64 IR DIV0. Z.div_mod_to_equations. lia. }
      if_cases EQZ; zify_cond EQZ; try rewrite !signed_lit in * by lia.
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
  Lemma aloop_walk : forall (kk : nat) (i eof : Z) (d dout : list Z) (m : mem) (ov : Z) (j : list byte)
      (rax t2x a1x a2x s2x s9x s10x s11x t3x : word),
      Z.to_nat (inl - i) = kk -> 0 <= i < inl ->
      MEMI m d dout ov j -> du_inv d -> 0 <= eof <= 2 ->
      zlength dout + 3 * ((zlength d + (inl - i)) / 4) <= Z.of_nat (length obs0) ->
      zlength dout + 3 * ((zlength d + (inl - i)) / 4) < 2^21 ->
      evt asegs (du_final (du_loop (mkDU d eof dout) (skipn (Z.to_nat i) (map bv_unsigned inp))))
        (ALOOPst i d eof (zlength dout) m rax t2x a1x a2x s2x s9x s10x s11x t3x).
  Proof.
    induction kk as [|kk IH]; intros until t3x; intros HK IR MEM DI ER CAP CAPB; [lia|].
    pose proof (aword_range sp) as SPR. boxsep. unfold zlength in *.
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
    { eapply (ab_char i eof (Z.of_nat (length dout)) d m raw obs ov cb j); try eassumption; lia. }
    intros ms1 PO. unfold achar_post in PO.
    destruct (classify d eof (bv_unsigned cb)) as [|e1|d1 e1].
    - (* [comment removed for export] *)
      destruct PO as (t0y & t1y & t2y & a0y & a1y & a2y & a4y & a5y & a6y & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & t4y & t5y & t6y & ->).
      cbn [du_out]. unfold ADU_ERRX.
      eapply adu_exit; try eassumption; try reflexivity; unfold zlength; try lia.
    - (* [comment removed for export] *)
      destruct PO as (t1y & t2y & a0y & a1y & a2y & a5y & x18 & x19 & x21 & x22 & x23 & x24 & x26 & x27 & t3y & t4y & t5y & t6y & ->).
      change (Z.of_nat (length d)) with (zlength d). change (Z.of_nat (length dout)) with (zlength dout).
      eapply adu_tail_walk; try eassumption; unfold zlength; try lia.
      all: lazymatch goal with
           | |- (_ = true <-> _) => split; intros _; reflexivity
           | |- _ => idtac
           end.
    - (* [comment removed for export] *)
      destruct CF as (E1R & SV1 & L1).
      destruct PO as (t2y & a0y & a1y & a2y & s10y & s11y & v & m1 & raw1 & -> & VR & CU1 & DPRE1 & INP1 & MI1 & OA1 & OL1 & FR1 & ST1 & MU1 & WM1).
      rewrite (flush_du d1 e1 dout SV1) by (destruct DI as [_ K]; lia).
      change (Z.of_nat (length d1)) with (zlength d1). change (Z.of_nat (length dout)) with (zlength dout).
      eapply evt_cut.
      { eapply (ab_flush_adv i e1 d1 dout m1 ov j v); try eassumption; unfold zlength; try (destruct DI as [_ K]; lia).
        all: lazymatch goal with
             | |- MEMI _ _ _ _ _ => exists raw1, obs; repeat (split; [eassumption|]); exact WM1
             | |- _ <= _ => destruct DI as [_ K];
                 eapply Z.le_trans; [| exact CAP]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             | |- _ < _ => destruct DI as [_ K];
                 eapply Z.le_lt_trans; [| exact CAPB]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             end. }
      intros ms2 (m2 & rax' & t2' & a1' & a2' & s2' & s10' & s11' & t3' & -> & MEM2 & DL2 & SV2 & CAP2 & CAPB2).
      destruct (flush d1 e1 dout) as [d2 dout2] eqn:FD. cbn [fst snd] in *.
      assert (DI2 : du_inv d2) by (split; [exact SV2| exact DL2]).
      destruct (Z.lt_ge_cases (i + 1) inl) as [MORE|DONE].
      + replace (i + 1 <? inl) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
        eapply (IH (i + 1)); try eassumption; lia.
      + replace (i + 1 <? inl) with false by (symmetry; apply Z.ltb_ge; lia). unfold ADU_TAIL.
        rewrite skipn_all2 by (rewrite length_map; lia). cbn [du_loop].
        destruct MEM2 as (raw2 & obs2 & CU2 & DPRE2 & OA2 & OLEN2 & OPRE2 & OL2 & INP2 & FR2 & ST2 & MI2 & MU2 & WM2).
        eapply adu_tail_walk; try eassumption; unfold zlength in *; try lia.
        all: lazymatch goal with
             | |- (_ = true <-> _) => split; [intros KX; discriminate KX| intros KX; exfalso; lia]
             | |- _ <= _ => eapply Z.le_trans; [| exact CAP2]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             | |- _ < _ => eapply Z.le_lt_trans; [| exact CAPB2]; apply Zplus_le_compat_l; apply Zmult_le_compat_l; [| lia]; apply Z.div_le_mono; lia
             | |- _ => idtac
             end.
  Qed.
  Lemma prefix_nth : forall (raw : list byte) (d : list Z) i c,
    map bv_unsigned (firstn (length d) raw) = d -> nth_error raw i = Some c -> (i < length d)%nat -> nth i d 0 = bv_unsigned c.
  Proof.
    intros raw d i c P N L. rewrite <- P. apply nth_error_nth. rewrite nth_error_map, nth_error_firstn.
    replace (i <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite N. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma as0_walk : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (d : list Z) (raw obs : list byte) (ov : Z),
      rw_cells asegs m00 a (ctx_chunk nn0 raw line) -> nn0 = zlength d -> map bv_unsigned (firstn (length d) raw) = d -> du_inv d ->
      bytes_at asegs m00 inp_a inp -> u8arr asegs m00 out obs -> length obs = length obs0 -> rw_cells asegs m00 outlp [C4 (wz ov)] ->
      stk asegs m00 lo (bv_unsigned sp) -> mem_inv asegs m00 ->
      evt asegs (fun ms' =>
          if inl =? 0 then du_final (mkDR 0 [] d) ms'
          else exists m1 t2x a1x a2x s2x s9x s10x s11x t3x j,
                 ms' = ALOOPst 0 d (initial_eof d) 0 m1 ra t2x a1x a2x s2x s9x s10x s11x t3x /\ MEMI m1 d [] ov j)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 out) (Z_to_bv 64 outlp) (Z_to_bv 64 inp_a) (Z_to_bv 64 inl) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m00 (seg_rom asegs)).
  Proof.
    assert (JX : forall (rax t0 t1 t2 a0 a1 a2 a4 a5 a6 x18 x19 x21 x22 x23 x24 x25 x26 x27 t4 t5 t6 : word) (m : mem)
        (retv nv rv ov nn : Z) (raw obs : list byte) (dout dd : list Z) (j : list byte),
        rw_cells asegs m outlp [C4 (wz ov)] -> CTXU m a nn raw line ->
        rw_cells asegs m (bv_unsigned sp + -128) [CB 8 j; C8 (Z_to_bv 64 SHC); C8 (Z_to_bv 64 outlp); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk asegs m lo (bv_unsigned sp + -128) -> mem_inv asegs m -> munch WW m00 m -> wmono asegs m00 m ->
        u8arr asegs m out obs -> length obs = length obs0 -> firstn (length dout) obs = map b8 dout -> bytes_at asegs m inp_a inp ->
        map bv_unsigned (firstn (length dd) raw) = dd -> du_inv dd ->
        retv = zlength dout -> nv = zlength dd -> 0 <= retv < 2^31 -> - 1 <= rv <= 1 ->
        evt asegs (du_final (mkDR rv dout dd))
          (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) a0 a1 a2 (Z_to_bv 64 nv) a4 a5 a6 (Z_to_bv 64 retv)
                   x18 x19 (Z_to_bv 64 ASHADOW_BASE) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 rv) t4 t5 t6)
              F (Z_to_bv 64 ADU_EXIT) fc None m (seg_rom asegs))).
    {
      intros until j. intros OL (C1 & C2 & L80 & C3) FR ST MI MU WM OA OLEN OPRE INP DPRE DI -> -> RR RV.
      unfold ADU_EXIT. pose proof (aword_range sp) as SPR. boxsep. subst SHC. rewrite ASHADOW_BASE_val. acb.
      pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
      pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB.
      pose proof (bytes_at_bound _ _ _ _ INP) as IB.
      assert (DL : (length dd < 64)%nat) by (destruct DI as [_ K]; exact K).
      assert (OL64 : (length dout <= length obs0)%nat) by (pose proof (f_equal (@length byte) OPRE) as OP2; rewrite length_map, length_firstn in OP2; lia).
      unfold wz in OL, C1, C3. unfold WW in MU.
      assert (SUBW : sub_fp WW (WW ++ [(outlp, outlp + 4)])) by (unfold WW; intros z Hz; cbn in Hz |- *; clear -Hz; lia).
      apply (munch_weaken _ _ m00 m SUBW) in MU. clear SUBW. unfold WW in MU. cbn [app] in MU.
      reacc ACCl0 MU. reacc ACCa0 MU.
      step. step.
      if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - OLP OB; lia); clear - OLP; intros K; lia| clear K].
      step. ubal_by OMOD. step. if_lit.
      step. step.
      rewrite (unsigned_lit outlp) by (clear - OLP OB; lia).
      ck4_load ACC outlp v V1 V2 Ha.
      ck_K 11 ADU_J1F4 KJ.
      { intros tv. red_tset. unfold ADU_J1F4.
        unbox SEPl; unbox SEPla; unbox SEPlo; unbox SEPil. st1. box SEPl; box SEPlo; box SEPil.
        step.
        match goal with MU' : munch _ m00 ?mc |- _ => clear ACC ACC0; reacc ACCa0 MU' end.
        pose proof (accessible_read8 _ _ (accessible_sub _ _ _ a 8 ACC ltac:(lia) ltac:(lia) ltac:(lia))) as RD.
        rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by lia.
        replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia).
        step. clear RD. rewrite ?ck8_sxb0. step. if_false_by (ck1_bnez_false 0 eq_refl).
        unbox SEPia; unbox SEPoa. st1. box SEPia; box SEPoa; box SEPla.
        step. do 15 step.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. unfold du_final. cbn [dr_rv dr_out dr_d].
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, raw, obs.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [split; [unfold wz; exact C1| split; [exact C2| split; [exact L80| exact C3]]]|].
        split; [exact DPRE|]. split; [exact DI|]. split; [exact OA|]. split; [exact OLEN|]. split; [exact OPRE|].
        split; [unfold wz; exact OL| exact INP]. }
      unfold ADU_J1F4 in KJ. ck4_branch_blt outlp v V1 V2 Ha KJ. }
    intros until ov. intros CTX NN DPRE DI INP OA OLEN OL ST MI.
    unfold P_EVP_DecodeUpdate. pose proof (aword_range sp) as SPR. boxsep. acb.
    pose proof (CTXU_split _ _ _ _ _ CTX) as (C1 & C2 & L80 & C3). clear CTX.
    pose proof (u8arr_bound _ _ _ _ OA) as AB. rewrite OLEN in AB. pose proof (u8arr_bound _ _ _ _ C2) as EB. pose proof (bytes_at_bound _ _ _ _ INP) as IB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (munch_refl WW m00) as MU. unfold WW in MU. pose proof (wmono_refl asegs m00) as WM.
    unfold wz in C1, C3, OL. pose proof (proj1 C2) as RAW.
    pose proof (ACONST_shbase _ AC00) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    carve_frame 128%nat ST.
    unbox SEPo. unbox SEPl. unbox SEPi. do 15 step. box SEPo. box SEPl. box SEPi.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear - APOS ACEIL ACEILB; lia); clear - APOS; intros K0; lia| clear K0].
    step. step. ubal_by AAL. step. if_lit.
    do 8 step. st1.
    (* [comment removed for export] *)
    reacc ACCa0 MU. ck1f_load ACC a. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    st1. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MU' : munch _ m00 mc |- _ => clear ACC; reacc ACCa0 MU' end end.
    step. change (Z_to_bv 64 nn0) with (wz nn0). rewrite sx32_wz by lia. unfold wz. rewrite NN. unfold zlength. step.
    match goal with FRx : rw_cells _ _ (bv_unsigned sp + -128) _ |- _ => rewrite (unsigned_lit a) in FRx by (clear - APOS ACEIL ACEILB; lia) end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mc _) =>
    assert (JGO : forall (e : Z) (x10 x11 x12 x21 : word), inl <> 0 -> e = initial_eof d ->
      evt asegs P (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 out) t1 t2 sp (Z_to_bv 64 a) x10 x11 x12
                (Z_to_bv 64 (Z.of_nat (length d))) (Z_to_bv 64 e) a5 (Z_to_bv 64 (a + 4)) a7
                s2 s3 (Z_to_bv 64 ASHADOW_BASE) x21 (Z_to_bv 64 inl) (Z_to_bv 64 inp_a) s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x422298) fc None mc (seg_rom asegs))) end.
    { intros e x10 x11 x12 x21 I0 ->. rewrite ASHADOW_BASE_val.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck4_load ACC (a + 88) v V1 V2 Ha.
      ck_K 12 0x4222ac K2.
      { intros tv. red_tset.
        (* [comment removed for export] *)
        step. step. step. if_lit. step. step.
        (* [comment removed for export] *)
        unbox SEPl. unbox SEPo. unbox SEPi. st1. box SEPl. box SEPo. box SEPi.
        (* [comment removed for export] *)
        step. assert (CN : negb (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 inl)) = false)
          by (rewrite bv_lts_zero_l, unsigned_lit by (clear - INL; lia); apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; clear - I0 INL; lia).
        rewrite CN; cbv iota; clear CN.
        (* [comment removed for export] *)
        do 9 step.
        apply evt_done. replace (inl =? 0) with false by (symmetry; apply Z.eqb_neq; exact I0).
        eexists _, _, _, _, _, _, _, _, _, (@nil byte). split.
        { unfold ALOOPst, ADU_LOOP. rewrite ?Z.add_0_r, ?Z.sub_0_r. reflexivity. }
        exists raw, obs. unfold WW.
        split; [split; [unfold wz; eassumption| split; [eassumption| split; [exact L80| unfold wz; eassumption]]]|].
        split; [exact DPRE|]. split; [eassumption|]. split; [exact OLEN|]. split; [reflexivity|]. split; [unfold wz; eassumption|].
        split; [eassumption|]. split; [unfold adu_frame; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| eassumption]. }
      ck4_branch_blt (a + 88) v V1 V2 Ha K2. }
    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mc _) =>
    assert (JEXIT : forall (e : Z) (x10 x11 x12 x21 : word), inl = 0 ->
      evt asegs P (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 out) t1 t2 sp (Z_to_bv 64 a) x10 x11 x12
                (Z_to_bv 64 (Z.of_nat (length d))) (Z_to_bv 64 e) a5 (Z_to_bv 64 (a + 4)) a7
                s2 s3 (Z_to_bv 64 ASHADOW_BASE) x21 (Z_to_bv 64 inl) (Z_to_bv 64 inp_a) s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x4222cc) fc None mc (seg_rom asegs))) end.
    { intros e x10 x11 x12 x21 I0. rewrite I0. cbn [Z.eqb].
      (* [comment removed for export] *)
      step. step. step.
      eapply (JX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (zlength d) 0 ov nn0 raw obs [] d); try eassumption; try reflexivity; unfold zlength; try (clear; lia).
      split; [eassumption|]. split; [eassumption|]. split; [exact L80| eassumption]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length d)) 0) as [D0|DPOS].
    - step.
      assert (CN : negb (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length d)))) = true) by (rewrite D0; reflexivity).
      rewrite CN; cbv iota; clear CN.
      assert (IE : initial_eof d = 0) by (unfold initial_eof; destruct d; [reflexivity| cbn in D0; lia]).
      (* [comment removed for export] *)
      step. step. if_cases EQI; zify_cond EQI.
      + eapply JGO; [exact EQI| rewrite IE; reflexivity].
      + eapply JEXIT; exact EQI.
    - step.
      assert (CN : negb (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length d)))) = false)
        by (rewrite bv_lts_zero_l, unsigned_lit by (clear - DL; lia); apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; clear - DPOS DL; lia).
      rewrite CN; cbv iota; clear CN.
      (* [comment removed for export] *)
      zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + -1)) by (clear - DL DPOS; change (bv_half_modulus 32) with (2^31); lia).
      zstep. rewrite zb_lxor_ones by (clear - APOS ACEIL ACEILB; lia).
      step. if_cases K; [exfalso; revert K; clear - APOS ACEIL ACEILB DL DPOS; intros K; zify_cond K; lia| clear K].
      zstep. zstep. zstep. ck1f_load ACC (a + 4 + (Z.of_nat (length d) + -1)). step. if_false_by (ck1_bnez_false 0 eq_refl).
      destruct (nth_error raw (Z.to_nat (Z.of_nat (length d) - 1))) as [cl|] eqn:NL; [| apply nth_error_None in NL; clear - NL L80 DL; lia].
      pose proof (rd_raw _ _ _ (Z.of_nat (length d) - 1) cl RAW NL ltac:(clear - L80 DL DPOS; lia)) as RD.
      replace (a + 4 + (Z.of_nat (length d) - 1)) with (a + 4 + (Z.of_nat (length d) + -1)) in RD by (clear; lia). step. clear RD.
      change (zxb cl) with (Z_to_bv 64 (bv_unsigned cl)). pose proof (byte_range cl) as CLR.
      pose proof (prefix_nth raw d _ cl DPRE NL ltac:(clear - L80 DL DPOS; lia)) as NTH1.
      replace (Z.to_nat (Z.of_nat (length d) - 1)) with (length d - 1)%nat in NTH1 by (clear - DPOS; lia).
      step. step. if_cases EQ1; zify_cond EQ1.
      + (* [comment removed for export] *)
        assert (IE : initial_eof d = 0).
        { unfold initial_eof. rewrite NTH1. unfold CH_EQ. replace (bv_unsigned cl =? 61) with false by (symmetry; apply Z.eqb_neq; clear - EQ1; lia). rewrite andb_false_r. reflexivity. }
        step. step. if_cases EQI; zify_cond EQI.
        * eapply JGO; [exact EQI| rewrite IE; reflexivity].
        * eapply JEXIT; exact EQI.
      + (* [comment removed for export] *)
        step. step. if_cases EQN1; zify_cond EQN1.
        * (* [comment removed for export] *)
          assert (IE : initial_eof d = 1).
          { unfold initial_eof. rewrite NTH1. unfold CH_EQ. replace (bv_unsigned cl =? 61) with true by (symmetry; apply Z.eqb_eq; clear - EQ1; lia).
            replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; clear - DPOS; lia).
            replace (1 <? length d)%nat with false by (symmetry; apply Nat.ltb_ge; clear - EQN1; lia). reflexivity. }
          step. if_cases EQI; zify_cond EQI.
          -- eapply JEXIT; exact EQI.
          -- eapply JGO; [exact EQI| rewrite IE; reflexivity].
        * (* [comment removed for export] *)
          zstep. rewrite (bv_swrap_small 32 (Z.of_nat (length d) + -2)) by (clear - DL DPOS EQN1; change (bv_half_modulus 32) with (2^31); lia).
          step. if_cases K; [exfalso; revert K; clear - APOS ACEIL ACEILB DL DPOS EQN1; intros K; zify_cond K; lia| clear K].
          zstep. zstep. zstep. ck1f_load ACC (a + 4 + (Z.of_nat (length d) + -2)). step. if_false_by (ck1_bnez_false 0 eq_refl).
          destruct (nth_error raw (Z.to_nat (Z.of_nat (length d) - 2))) as [cp|] eqn:NP; [| apply nth_error_None in NP; clear - NP L80 DL; lia].
          pose proof (rd_raw _ _ _ (Z.of_nat (length d) - 2) cp RAW NP ltac:(clear - L80 DL DPOS EQN1; lia)) as RD.
          replace (a + 4 + (Z.of_nat (length d) - 2)) with (a + 4 + (Z.of_nat (length d) + -2)) in RD by (clear; lia). step. clear RD.
          change (zxb cp) with (Z_to_bv 64 (bv_unsigned cp)). pose proof (byte_range cp) as CPR.
          pose proof (prefix_nth raw d _ cp DPRE NP ltac:(clear - L80 DL DPOS EQN1; lia)) as NTH2.
          replace (Z.to_nat (Z.of_nat (length d) - 2)) with (length d - 2)%nat in NTH2 by (clear - DPOS EQN1; lia).
          zstep. zstep. zstep.
          assert (IE : initial_eof d = 1 + Z.b2z (bv_unsigned cp + -61 =? 0)).
          { unfold initial_eof. rewrite NTH1, NTH2. unfold CH_EQ. replace (bv_unsigned cl =? 61) with true by (symmetry; apply Z.eqb_eq; clear - EQ1; lia).
            replace (0 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; clear - DPOS; lia). replace (1 <? length d)%nat with true by (symmetry; apply Nat.ltb_lt; clear - DPOS EQN1; lia).
            cbn [andb]. destruct (Z.eqb_spec (bv_unsigned cp) 61) as [E|NE].
            - replace (bv_unsigned cp + -61 =? 0) with true by (symmetry; apply Z.eqb_eq; clear - E; lia). reflexivity.
            - replace (bv_unsigned cp + -61 =? 0) with false by (symmetry; apply Z.eqb_neq; clear - NE; lia). reflexivity. }
          lazymatch goal with |- context [bv_swrap 32 (Z.b2z (Z.land (bv_unsigned cp + -61) ?M <? 1) + 1)] =>
            assert (EV : bv_swrap 32 (Z.b2z (Z.land (bv_unsigned cp + -61) M <? 1) + 1) = initial_eof d) end.
          { rewrite <- unsigned_lit_land, unsigned_lit_wrap. rewrite IE. destruct (Z.eq_dec (bv_unsigned cp) 61) as [E|NE].
            - rewrite E. reflexivity.
            - replace ((bv_unsigned cp + -61) mod 2 ^ 64 <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NE CPR; Z.div_mod_to_equations; lia).
              replace (bv_unsigned cp + -61 =? 0) with false by (symmetry; apply Z.eqb_neq; clear - NE; lia). reflexivity. }
          rewrite EV.
          step. if_cases EQI; zify_cond EQI.
          -- eapply JEXIT; exact EQI.
          -- eapply JGO; [exact EQI| reflexivity].
  Qed.
End U.
(* [comment removed for export] *)
Section FINAL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma adecupdate_spec : decupdate_stmt H.
  Proof.
    unfold decupdate_stmt. intros until junk.
    intros A0 A1 A2 A3 A4 INL INPL EC TAB INP OUT CAP OPOS IPOS IHI OHI OL ACCa ACCo ACCl ACCi AC OAPP LAPP IAPP OMOD A92 SEPo SEPl SEPi SEPoa SEPla SEPlo SEPio SEPia SEPil ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3 a4. unfold DECUPDATE_STACK, FR_EVP_DecodeUpdate, DECBLOCK_STACK, FR_evp_decodeblock_int in LO. unfold ENCCTX_SIZE in *.
    destruct EC as (raw & line & L80 & DPRE & CELLS & LR & EIN & EBR & DI).
    pose proof EBR as (APOS & AAL & _ & _ & ACEIL & _ & AAPP). unfold ENCCTX_SIZE in ACEIL, AAPP. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    acb.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ OUT) as OA.
    assert (OLEN : length junk = Z.to_nat outsz) by (exact (rw_cells_CB_length _ _ _ _ _ OUT)).
    assert (CAP0 : 0 <= du_outcap d inl) by (unfold du_outcap; apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; unfold zlength; lia]).
    assert (OSZ : Z.of_nat (length junk) = outsz) by lia.
    rewrite <- OSZ in SEPo, SEPoa, SEPlo, SEPio, ACCo, OAPP, OHI.
    assert (DL : (length d < 64)%nat) by (destruct DI as [_ K]; exact K).
    pose proof (ctx_chunk_of_enc _ _ _ _ _ CELLS) as CTX.
    (* [comment removed for export] *)
    assert (NSHo : out + Z.of_nat (length junk) <= ALOWSH_LO \/ AHI_LO <= out) by (destruct OAPP as [K|K]; [exact (aapp_not_shadowland _ _ K)| right; unfold AHI_LO; clear -K LO CEIL ACEILB; lia]).
    assert (NSHl : outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp) by (destruct LAPP as [K|K]; [exact (aapp_not_shadowland _ _ K)| right; unfold AHI_LO; clear -K LO CEIL ACEILB; lia]).
    assert (NSHi : inp_a + inl <= ALOWSH_LO \/ AHI_LO <= inp_a) by (destruct IAPP as [K|K]; [exact (aapp_not_shadowland _ _ K)| right; unfold AHI_LO; clear -K LO CEIL ACEILB; lia]).
    pose proof (aapp_not_shadowland _ _ AAPP) as NSHa.
    assert (OLP : 0 < outlp) by (destruct LAPP as [K|K]; [exact (proj1 (proj2 (proj2 (proj2 (aapp_bounds _ _ K ltac:(lia))))))| clear - K LO LO0; lia]).
    (* [comment removed for export] *)
    assert (FIN : forall r ms', du_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a lo line inp junk m r ms' ->
      c8_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (dr_rv r) a (dr_d r) p
        [(out, out + outsz); (outlp, outlp + 4); (a, a + 92)]
        (fun m' => exists junk', rw_cells asegs m' out [CB (length (dr_out r)) (map (Z_to_bv 8) (dr_out r)); CB (Z.to_nat outsz - length (dr_out r)) junk']
                   /\ rw_cells asegs m' outlp [C4 (wz (zlength (dr_out r)))] /\ bytes_at asegs m' inp_a inp /\ B64TAB m'
                   /\ (length (dr_out r) <= Z.to_nat outsz)%nat) lo m ms').
    { intros r ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & raw' & obs' & -> & MU & WM & MI' & ST' & CU & DP & DI' & OA' & OLEN' & OP & OL' & INP').
      unfold c8_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|]. split; [reflexivity|].
      assert (MUW : munch [(lo, bv_unsigned sp); (out, out + outsz); (outlp, outlp + 4); (a, a + 92)] m m').
      { eapply munch_weaken; [| exact MU]. intros z Hz. cbn in Hz |- *. clear -Hz OSZ. lia. }
      split; [exact MUW|]. split; [exact WM|]. split; [exact MI'|].
      split. { assert (HI : 0x7fff7f800000 <= lo) by (clear -CEIL ACEILB; lia).
               eapply ACONST_frame; [exact AC| exact MUW| exact WM|].
               apply Forall_cons. { apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI; lia| clear -HI; lia]. }
               apply Forall_cons. { destruct OAPP as [OQ|OQ]; [eapply aconst_ok_aapp; [exact OQ| clear; lia| clear -OSZ; lia]|].
                                    apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI LO OQ; lia| clear -HI LO OQ; lia]. }
               apply Forall_cons. { destruct LAPP as [OQ|OQ]; [eapply aconst_ok_aapp; [exact OQ| clear; lia| clear; lia]|].
                                    apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; clear -HI LO OQ; lia| clear -HI LO OQ; lia]. }
               apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPP| clear; lia| clear; lia]| apply Forall_nil]. }
      split; [exact ST'|].
      split. { destruct CU as (C1 & C2 & L80' & C3). exists raw', line. split; [exact L80'|]. split; [exact DP|].
               split; [apply enc_of_ctx_chunk; apply CTXU_join; split; [exact C1| split; [exact C2| split; [exact L80'| exact C3]]]|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI']. }
      assert (OPL : (length (dr_out r) <= length obs')%nat).
      { apply (f_equal (@length byte)) in OP. rewrite length_map, length_firstn in OP. lia. }
      exists (skipn (length (dr_out r)) obs').
      split. { apply rw_cells_of_u8arr in OA'.
               apply (rw_cells_CB_split asegs m' out _ (length (dr_out r))) in OA'; [| exact OPL]. destruct OA' as [O1 O2].
               rewrite OP in O1. change [CB (length (dr_out r)) (map (Z_to_bv 8) (dr_out r)); CB (Z.to_nat outsz - length (dr_out r)) (skipn (length (dr_out r)) obs')]
                 with ([CB (length (dr_out r)) (map b8 (dr_out r))] ++ [CB (Z.to_nat outsz - length (dr_out r)) (skipn (length (dr_out r)) obs')]).
               apply rw_cells_app. split; [exact O1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, <- OLEN, <- OLEN'. exact O2. }
      split; [exact OL'|]. split; [exact INP'|]. split; [apply B64TAB_of_mem_inv; exact MI'| rewrite <- OLEN, <- OLEN'; exact OPL]. }
    eapply evt_cut.
    { first [ eapply (as0_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk LB m)
            | eapply (as0_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk m) ];
        try eassumption; unfold zlength; try lia; try reflexivity. }
    intros ms1 PO. destruct (Z.eqb_spec inl 0) as [I0|I1].
    - (* [comment removed for export] *)
      replace (inl =? 0) with true in PO by (symmetry; apply Z.eqb_eq; exact I0).
      apply evt_done. assert (inp = []) as -> by (destruct inp; [reflexivity| cbn in INPL; lia]). cbn [map decode_update].
      exact (FIN _ _ PO).
    - replace (inl =? 0) with false in PO by (symmetry; apply Z.eqb_neq; exact I1).
      destruct PO as (m1 & t2x & a1x & a2x & s2x & s9x & s10x & s11x & t3x & j & -> & MEM).
      assert (INP1 : inp <> []) by (intros ->; cbn in INPL; lia).
      replace (decode_update d (map bv_unsigned inp)) with (du_loop (mkDU d (initial_eof d) []) (skipn (Z.to_nat 0) (map bv_unsigned inp)))
        by (unfold decode_update; destruct inp; [congruence| reflexivity]).
      eapply evt_mono; [| intros ms' Q; exact (FIN _ _ Q)].
      change 0 with (zlength (@nil Z)) at 3.
      first [ eapply (aloop_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk LB m) with (kk := Z.to_nat inl)
            | eapply (aloop_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a out outlp inp_a inl lo line (zlength d) inp junk m) with (kk := Z.to_nat inl) ];
        try eassumption; unfold zlength; try lia; try reflexivity.
      + pose proof (initial_eof d). unfold initial_eof. destruct (_ && _); [destruct (_ && _)|]; lia.
      + cbn [length]. rewrite Z.sub_0_r. unfold du_outcap, zlength in CAP. lia.
      + cbn [length]. rewrite Z.sub_0_r. unfold zlength.
        assert (Z.of_nat (length d) + inl < 64 + 2^20) by lia.
        assert ((Z.of_nat (length d) + inl) / 4 < 2^19) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.
End FINAL.

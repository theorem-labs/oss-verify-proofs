(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState
     ECH_B64 ECH_C1_stmt ECH_C8_stmt ECH_C8_blockA.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma groups_bytes_nth' : forall vs g j a b c d,
  nth_error vs (4 * g) = Some a -> nth_error vs (4 * g + 1) = Some b -> nth_error vs (4 * g + 2) = Some c -> nth_error vs (4 * g + 3) = Some d ->
  (j < 3)%nat -> nth_error (groups_bytes vs) (3 * g + j) = nth_error (quad_bytes (quad_val a b c d)) j.
Proof.
  intros vs g j a b c d Na Nb Nc Nd J. eapply groups_bytes_nth; [| exact J].
  rewrite (skipn_nth_cons' _ _ a) by exact Na. f_equal. replace (S (4 * g)) with (4 * g + 1)%nat by lia.
  rewrite (skipn_nth_cons' _ _ b) by exact Nb. f_equal. replace (S (4 * g + 1)) with (4 * g + 2)%nat by lia.
  rewrite (skipn_nth_cons' _ _ c) by exact Nc. f_equal. replace (S (4 * g + 2)) with (4 * g + 3)%nat by lia.
  rewrite (skipn_nth_cons' _ _ d) by exact Nd. reflexivity.
Qed.

Lemma firstn1_of_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof. intros X l i x N. rewrite (skipn_nth_cons' l i x N). reflexivity. Qed.

Section LOOP.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  (* [comment removed for export] *)
  Variables (ra sp gp tp s1 a0w s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 t q eof : Z) (raw tj : list byte) (m0 : mem).
  Hypothesis L80 : length raw = 80%nat.
  Hypothesis SAVED : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Hypothesis QR : 1 <= q <= 16.
  Hypothesis ER : 0 <= eof <= 2.
  Hypothesis TJ : 3 * q <= Z.of_nat (length tj).
  Hypothesis SEP : f0 + 80 <= t \/ t + Z.of_nat (length tj) <= f0.
  Hypothesis RB : 0 <= f0 /\ f0 + 80 <= 2^64.
  Hypothesis TB : 0 <= t /\ t + Z.of_nat (length tj) <= 2^64.
  Definition vs : list Z := map a2b (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Definition SRC : list byte := map b8 (groups_bytes vs) ++ skipn (Z.to_nat (3 * q)) tj.
  Definition W : list (Z * Z) := [(t, t + Z.of_nat (length tj))].
  Definition INV (m : mem) (bs : list byte) (k : Z) : Prop :=
    bytes_at rsegs m f0 raw /\ u8arr rsegs m t bs /\ length bs = length tj /\ copied SRC bs (Z.to_nat k)
    /\ mem_inv rsegs m /\ munch W m0 m /\ wmono rsegs m0 m.

  Lemma vs_length : length vs = Z.to_nat (4 * q).
  Proof. unfold vs. rewrite !length_map, length_firstn. lia. Qed.
  Lemma SRC_length : length SRC = length tj.
  Proof. unfold SRC. rewrite length_app, length_map, (groups_bytes_length (Z.to_nat q)), length_skipn; [lia|]. rewrite vs_length. lia. Qed.
  Lemma vs_nth : forall i c, nth_error raw (Z.to_nat i) = Some c -> 0 <= i < 4 * q -> nth_error vs (Z.to_nat i) = Some (a2b (bv_unsigned c)).
  Proof.
    intros i c N R. unfold vs. rewrite !nth_error_map, nth_error_firstn.
    replace (Z.to_nat i <? Z.to_nat (4 * q))%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite N. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma grp_facts : forall g, 0 <= g < q ->
    exists ca cb cc cd,
      nth_error raw (Z.to_nat (4 * g)) = Some ca /\ nth_error raw (Z.to_nat (4 * g + 1)) = Some cb /\
      nth_error raw (Z.to_nat (4 * g + 2)) = Some cc /\ nth_error raw (Z.to_nat (4 * g + 3)) = Some cd /\
      bv_unsigned ca < 128 /\ bv_unsigned cb < 128 /\ bv_unsigned cc < 128 /\ bv_unsigned cd < 128 /\
      0 <= a2b (bv_unsigned ca) < 64 /\ 0 <= a2b (bv_unsigned cb) < 64 /\ 0 <= a2b (bv_unsigned cc) < 64 /\ 0 <= a2b (bv_unsigned cd) < 64 /\
      (forall j, (j < 3)%nat -> nth_error SRC (Z.to_nat (3 * g) + j)
           = Some (b8 (nth j (quad_bytes (quad_val (a2b (bv_unsigned ca)) (a2b (bv_unsigned cb)) (a2b (bv_unsigned cc)) (a2b (bv_unsigned cd)))) 0))).
  Proof.
    intros g G.
    destruct (nth_error raw (Z.to_nat (4 * g))) as [ca|] eqn:Na; [| apply nth_error_None in Na; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 1))) as [cb|] eqn:Nb; [| apply nth_error_None in Nb; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 2))) as [cc|] eqn:Nc; [| apply nth_error_None in Nc; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 3))) as [cd|] eqn:Nd; [| apply nth_error_None in Nd; lia].
    pose proof (saved_nth (4 * q) raw (4 * g) ca SAVED Na ltac:(lia)) as Sa.
    pose proof (saved_nth (4 * q) raw (4 * g + 1) cb SAVED Nb ltac:(lia)) as Sb.
    pose proof (saved_nth (4 * q) raw (4 * g + 2) cc SAVED Nc ltac:(lia)) as Sc.
    pose proof (saved_nth (4 * q) raw (4 * g + 3) cd SAVED Nd ltac:(lia)) as Sd.
    pose proof (b64_saved_lt64 _ Sa) as Va. pose proof (b64_saved_lt64 _ Sb) as Vb. pose proof (b64_saved_lt64 _ Sc) as Vc. pose proof (b64_saved_lt64 _ Sd) as Vd.
    exists ca, cb, cc, cd. do 4 (split; [reflexivity|]).
    split; [destruct Sa as [K _]; lia|]. split; [destruct Sb as [K _]; lia|]. split; [destruct Sc as [K _]; lia|]. split; [destruct Sd as [K _]; lia|].
    split; [exact Va|]. split; [exact Vb|]. split; [exact Vc|]. split; [exact Vd|].
    intros j J. unfold SRC. rewrite nth_error_app1.
    2:{ rewrite length_map, (groups_bytes_length (Z.to_nat q)) by (rewrite vs_length; lia). lia. }
    rewrite nth_error_map. replace (Z.to_nat (3 * g) + j)%nat with (3 * Z.to_nat g + j)%nat by lia.
    rewrite (groups_bytes_nth' vs (Z.to_nat g) j (a2b (bv_unsigned ca)) (a2b (bv_unsigned cb)) (a2b (bv_unsigned cc)) (a2b (bv_unsigned cd))).
    - destruct j as [|[|[|j]]]; cbn; try reflexivity. lia.
    - replace (4 * Z.to_nat g)%nat with (Z.to_nat (4 * g)) by lia. apply vs_nth; [exact Na| lia].
    - replace (4 * Z.to_nat g + 1)%nat with (Z.to_nat (4 * g + 1)) by lia. apply vs_nth; [exact Nb| lia].
    - replace (4 * Z.to_nat g + 2)%nat with (Z.to_nat (4 * g + 2)) by lia. apply vs_nth; [exact Nc| lia].
    - replace (4 * Z.to_nat g + 3)%nat with (Z.to_nat (4 * g + 3)) by lia. apply vs_nth; [exact Nd| lia].
    - exact J.
  Qed.
  (* [comment removed for export] *)
  Local Ltac arr_store E P P' MB NS :=
    match goal with ARR : u8arr rsegs ?m t ?bs, CP : copied _ ?bs' _, LEN : length ?bs'' = length tj |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok rsegs m t bs P (wa E) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      step; rewrite le1_mod; rewrite MB;
      let ARR2 := fresh "ARR" in let CP2 := fresh "CP" in let LEN2 := fresh "LEN" in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?x]) _) =>
        pose proof (u8arr_write_bytes rsegs m t bs P [x] ARR ltac:(lia) ltac:(cbn; lia)) as ARR2;
        try (replace (t + P) with E in ARR2 by lia);
        pose proof (copied_updZ _ bs P [x] CP ltac:(lia) (firstn1_of_nth _ _ _ NS) ltac:(rewrite SRC_length; cbn; lia)) as CP2;
        lazymatch type of CP2 with copied _ _ ?idx => replace idx with (Z.to_nat P') in CP2 by (cbn; lia) end;
        pose proof LEN as LEN2; rewrite <- (upd_bytes_length bs (Z.to_nat P) [x]) in LEN2 by (cbn; lia);
        clear ARR CP LEN; store_done;
        let bs2 := fresh "bs" in let Ebs := fresh "Ebs" in remember (upd_bytes bs (Z.to_nat P) [x]) as bs2 eqn:Ebs; clear Ebs
      end
    end.
  (* [comment removed for export] *)
  Local Ltac ldc i c N B RAW := let RD := fresh "RD" in
    pose proof (rd_raw _ _ _ i c RAW N ltac:(lia)) as RD; step; clear RD; rewrite (sxb_small c) by lia.
  Local Ltac ldt c MI := let RD := fresh "RD" in
    pose proof (rd_tab _ (bv_unsigned c) MI ltac:(lia)) as RD; unfold A_data_ascii2bin in RD; st1; clear RD.

  (* [comment removed for export] *)
  Definition L3st (g : Z) (m : mem) (x5 x6 x7 x28 x29 x30 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 sp s1 a0w (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (f0 + 4 * g)) (Z_to_bv 64 (3 + 3 * g)) (Z_to_bv 64 eof)
            (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (4 * q - 4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
       F (Z_to_bv 64 DB_L3) fc None m (seg_rom rsegs).
  Definition DB_L3X : Z := 0x1dada4.

  (* [comment removed for export] *)
  Lemma l3_iter : forall g m bs x5 x6 x7 x28 x29 x30,
    0 <= g -> g + 2 <= q -> INV m bs (3 * g) ->
    evt rsegs (fun ms' => exists m' bs' x6' x7' x28' x29' x30',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (t + 3 * g + 3)) x6' x7' sp s1 a0w (Z_to_bv 64 (t + 3 * g + 3)) (Z_to_bv 64 (f0 + 4 * g + 4))
                      (Z_to_bv 64 (3 + 3 * g + 3)) (Z_to_bv 64 eof) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (4 * g + 4)) (Z_to_bv 64 (4 * q - 4))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' t6)
                 F (Z_to_bv 64 (if 4 * g + 4 <? 4 * q - 4 then DB_L3 else DB_L3X)) fc None m' (seg_rom rsegs)
        /\ INV m' bs' (3 * g + 3))
      (L3st g m x5 x6 x7 x28 x29 x30).
  Proof.
    intros g m bs x5 x6 x7 x28 x29 x30 G0 GQ (RAW & ARR & LEN & CP & MI & MU & WM).
    unfold L3st, DB_L3, DB_L3X, A_data_ascii2bin. unfold W in MU.
    destruct (grp_facts g ltac:(lia)) as (ca & cb & cc & cd & Na & Nb & Nc & Nd & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    pose proof (NS 0%nat ltac:(lia)) as NS0. pose proof (NS 1%nat ltac:(lia)) as NS1. pose proof (NS 2%nat ltac:(lia)) as NS2. clear NS.
    rewrite Nat.add_0_r in NS0. replace (Z.to_nat (3 * g) + 1)%nat with (Z.to_nat (3 * g + 1)) in NS1 by lia.
    replace (Z.to_nat (3 * g) + 2)%nat with (Z.to_nat (3 * g + 2)) in NS2 by lia.
    cbn [nth quad_bytes] in NS0, NS1, NS2.
    pose proof (byte_range ca). pose proof (byte_range cb). pose proof (byte_range cc). pose proof (byte_range cd).
    (* [comment removed for export] *)
    ldc (4 * g) ca Na Ba RAW. step. step. step. fbr. step. ldt ca MI. set (va := a2b (bv_unsigned ca)) in *.
    (* [comment removed for export] *)
    ldc (4 * g + 1) cb Nb Bb RAW. step. fbr. step. ldt cb MI. set (vb := a2b (bv_unsigned cb)) in *.
    (* [comment removed for export] *)
    ldc (4 * g + 2) cc Nc Bc RAW. step. step. step. fbr. step. ldt cc MI. set (vc := a2b (bv_unsigned cc)) in *.
    (* [comment removed for export] *)
    ldc (4 * g + 3) cd Nd Bd RAW. step. fbr. step. ldt cd MI. set (vd := a2b (bv_unsigned cd)) in *.
    unfold wz.
    (* [comment removed for export] *)
    pose proof (lor_lt_pow2 vb va 6 ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow2 vc vd 6 ltac:(lia) ltac:(lia)) as L2.
    pose proof (lor_lt_pow2 (Z.lor vb va) (Z.lor vc vd) 6 L1 L2) as L3. change (2^6) with 64 in L1, L2, L3.
    zstep. zstep. zstep. zstep.
    set (x := Z.lor (Z.lor vb va) (Z.lor vc vd)) in *. rewrite (Z.shiftl_mul_pow2 x 56) by lia. change (2^56) with 72057594037927936.
    step. fbr.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. change (2^18) with 262144. change (2^6) with 64.
    rewrite !(Z.mod_small _ 18446744073709551616) by lia.
    rewrite (bv_swrap_small 32 (4 * g + 4)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    (* [comment removed for export] *)
    arr_store (t + 3 * g) (3 * g) (3 * g + 1) (mb0_ok va vb vc vd Va Vb Vc Vd) NS0.
    arr_store (t + 3 * g + 1) (3 * g + 1) (3 * g + 2) (mb1_ok va vb vc vd Va Vb Vc Vd) NS1.
    arr_store (t + 3 * g + 2) (3 * g + 2) (3 * g + 3) (mb2_ok va vb vc vd Va Vb Vc Vd) NS2.
    (* [comment removed for export] *)
    zstep. zstep. step.
    lazymatch goal with ARRx : u8arr rsegs ?mx t ?bsx |- _ =>
      if_cases EQ; zify_cond EQ; rewrite !signed_lit in EQ by lia;
      [ replace (4 * g + 4 <? 4 * q - 4) with true by (symmetry; apply Z.ltb_lt; lia)
      | replace (4 * g + 4 <? 4 * q - 4) with false by (symmetry; apply Z.ltb_ge; lia) ];
      apply evt_done; exists mx, bsx; eexists _, _, _, _, _;
      (split; [reflexivity| split; [exact RAW| split; [exact ARRx| split; [exact LEN0| split; [exact CP0| split; [exact MI| split; [exact MU| exact WM]]]]]]])
    end.
  Qed.

  (* [comment removed for export] *)
  Lemma l3_loop : forall k g m bs x5 x6 x7 x28 x29 x30,
    Z.to_nat (q - 2 - g) = k -> 0 <= g -> g + 2 <= q -> INV m bs (3 * g) ->
    evt rsegs (fun ms' => exists m' bs' x6' x7' x28' x29' x30',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (t + 3 * (q - 1))) x6' x7' sp s1 a0w (Z_to_bv 64 (t + 3 * (q - 1))) (Z_to_bv 64 (f0 + 4 * (q - 1)))
                      (Z_to_bv 64 (3 * q)) (Z_to_bv 64 eof) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * q - 4))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' t6) F (Z_to_bv 64 DB_LAST) fc None m' (seg_rom rsegs)
        /\ INV m' bs' (3 * (q - 1)))
      (L3st g m x5 x6 x7 x28 x29 x30).
  Proof.
    induction k as [|k IH]; intros g m bs x5 x6 x7 x28 x29 x30 HK G0 GQ I.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply l3_iter; [exact G0| exact GQ| exact I]|].
      intros ms1 (m1 & bs1 & x6' & x7' & x28' & x29' & x30' & -> & I1).
      replace (4 * g + 4 <? 4 * q - 4) with false by (symmetry; apply Z.ltb_ge; lia). unfold DB_L3X, DB_LAST.
      step. step. apply evt_done. exists m1, bs1, x6', x7', x28', x29', x30'.
      replace (t + 3 * g + 3) with (t + 3 * (q - 1)) by lia. replace (f0 + 4 * g + 4) with (f0 + 4 * (q - 1)) by lia.
      replace (3 + 3 * g + 3) with (3 * q) by lia. replace (4 * g + 4) with (4 * q - 4) by lia. replace (3 * g + 3) with (3 * (q - 1)) in I1 by lia.
      split; [reflexivity| exact I1].
    - eapply evt_cut; [eapply l3_iter; [exact G0| exact GQ| exact I]|].
      intros ms1 (m1 & bs1 & x6' & x7' & x28' & x29' & x30' & -> & I1).
      replace (4 * g + 4 <? 4 * q - 4) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (t + 3 * g + 3) with (t + 3 * (g + 1)) by lia. replace (f0 + 4 * g + 4) with (f0 + 4 * (g + 1)) by lia.
      replace (3 + 3 * g + 3) with (3 + 3 * (g + 1)) by lia. replace (4 * g + 4) with (4 * (g + 1)) by lia. replace (3 * g + 3) with (3 * (g + 1)) in I1 by lia.
      eapply (IH (g + 1)); [lia| lia| lia| exact I1].
  Qed.
  (* [comment removed for export] *)
  Lemma mb1L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 ((Z.lor (Z.lor (vc * 64) vd) (Z.lor (vb * 4096) (va * 262144)) ≫ 8) mod 256) = b8 ((quad_val va vb vc vd / 256) mod 256).
  Proof.
    intros va vb vc vd Ra Rb Rc Rd. rewrite (Z.lor_comm (vc * 64) vd).
    change (vc * 64) with (vc * 2^6). rewrite (lor_add_disjoint vd vc 6) by lia.
    change (va * 262144) with (va * 2^18). rewrite (lor_add_disjoint (vb * 4096) va 18) by lia.
    replace (vb * 4096 + va * 2^18) with ((vb + va * 64) * 2^12) by lia. rewrite (lor_add_disjoint _ _ 12) by lia.
    rewrite Z.shiftr_div_pow2 by lia. apply b8_eqm. unfold quad_val. rewrite !Z.mod_mod by lia.
    change (2^6) with 64. change (2^12) with 4096. change (2^8) with 256. f_equal. f_equal. lia.
  Qed.
  Lemma mb2L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 (Z.lor (vc * 64) vd mod 256) = b8 (quad_val va vb vc vd mod 256).
  Proof. intros va vb vc vd Ra Rb Rc Rd. rewrite (Z.lor_comm (vc * 64) vd). exact (mb2_ok va vb vc vd Ra Rb Rc Rd). Qed.
  Lemma mb0L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 ((Z.lor (vb * 4096) (va * 262144) ≫ 16) mod 256) = b8 ((quad_val va vb vc vd / 65536) mod 256).
  Proof. intros. apply mb0_ok; assumption. Qed.

  (* [comment removed for export] *)
  Lemma last_grp : forall m bs x5 x6 x7 x16 x17 x28 x29 x30 (s0 : word) (lo : Z),
    INV m bs (3 * (q - 1)) ->
    rw_cells rsegs m0 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk rsegs m0 lo (bv_unsigned sp + -16) -> 0 <= lo -> lo <= bv_unsigned sp + -16 ->
    (t + Z.of_nat (length tj) <= lo \/ bv_unsigned sp <= t) -> bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists m' bs' x5' x6' x7' x12 x13 x14 x15 x16' x17' x28' x29' x30',
        ms' = MS (mkR ra sp gp tp x5' x6' x7' s0 s1 (Z_to_bv 64 (3 * q - eof)) (Z_to_bv 64 (t + 3 * (q - 1))) x12 x13 x14 x15 x16' x17'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ INV m' bs' (3 * q - eof) /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 sp s1 a0w (Z_to_bv 64 (t + 3 * (q - 1))) (Z_to_bv 64 (f0 + 4 * (q - 1))) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 eof)
               (Z_to_bv 64 A_data_ascii2bin) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 DB_LAST) fc None m (seg_rom rsegs)).
  Proof.
    intros m bs x5 x6 x7 x16 x17 x28 x29 x30 s0 lo (RAW & ARR & LEN & CP & MI & MU & WM) FR0 ST0 LO0 LO TSEP RAE.
    unfold DB_LAST, A_data_ascii2bin. unfold W in MU. pose proof (word_range sp) as SPR.
    destruct (grp_facts (q - 1) ltac:(lia)) as (ca & cb & cc & cd & Na & Nb & Nc & Nd & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    pose proof (NS 0%nat ltac:(lia)) as NS0. pose proof (NS 1%nat ltac:(lia)) as NS1. pose proof (NS 2%nat ltac:(lia)) as NS2. clear NS.
    rewrite Nat.add_0_r in NS0. replace (Z.to_nat (3 * (q - 1)) + 1)%nat with (Z.to_nat (3 * (q - 1) + 1)) in NS1 by lia.
    replace (Z.to_nat (3 * (q - 1)) + 2)%nat with (Z.to_nat (3 * (q - 1) + 2)) in NS2 by lia.
    cbn [nth quad_bytes] in NS0, NS1, NS2.
    pose proof (byte_range ca). pose proof (byte_range cb). pose proof (byte_range cc). pose proof (byte_range cd).
    (* [comment removed for export] *)
    ldc (4 * (q - 1)) ca Na Ba RAW. step. step. step. fbr. step. ldt ca MI. set (va := a2b (bv_unsigned ca)) in *.
    (* [comment removed for export] *)
    ldc (4 * (q - 1) + 1) cb Nb Bb RAW. step. fbr. step. ldt cb MI. set (vb := a2b (bv_unsigned cb)) in *.
    (* [comment removed for export] *)
    ldc (4 * (q - 1) + 2) cc Nc Bc RAW. step. step. step. fbr. step. ldt cc MI. set (vc := a2b (bv_unsigned cc)) in *.
    (* [comment removed for export] *)
    ldc (4 * (q - 1) + 3) cd Nd Bd RAW. step. fbr. step. ldt cd MI. set (vd := a2b (bv_unsigned cd)) in *.
    unfold wz.
    (* [comment removed for export] *)
    pose proof (lor_lt_pow2 vb va 6 ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow2 vc vd 6 ltac:(lia) ltac:(lia)) as L2.
    pose proof (lor_lt_pow2 (Z.lor vb va) (Z.lor vc vd) 6 L1 L2) as L3. change (2^6) with 64 in L1, L2, L3.
    zstep. zstep. zstep. zstep.
    set (x := Z.lor (Z.lor vb va) (Z.lor vc vd)) in *. rewrite (Z.shiftl_mul_pow2 x 56) by lia. change (2^56) with 72057594037927936.
    step. fbr.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. change (2^18) with 262144. change (2^6) with 64.
    rewrite !(Z.mod_small _ 18446744073709551616) by lia.
    step. tbr.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    assert (EPI : forall m2 bs2 (k : Z) x5' x12' x13' x14' x15',
      INV m2 bs2 k ->
      evt rsegs (fun ms' => exists m' bs' x5'' x6' x7' x12 x13 x14 x15 x16' x17' x28' x29' x30',
          ms' = MS (mkR ra sp gp tp x5'' x6' x7' s0 s1 (Z_to_bv 64 (3 * q - eof)) (Z_to_bv 64 (t + 3 * (q - 1))) x12 x13 x14 x15 x16' x17'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' t6)
                   F (ret_pc ra) fc None m' (seg_rom rsegs)
          /\ INV m' bs' k /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5' (Z_to_bv 64 vc) (Z_to_bv 64 (394760 + bv_unsigned cc)) sp s1
                 x12' (Z_to_bv 64 (t + 3 * (q - 1))) x13' (Z_to_bv 64 (3 * q)) (Z_to_bv 64 eof) x14' x15' (Z_to_bv 64 (va * 262144))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x1dae88) fc None m2 (seg_rom rsegs))).
    { intros m2 bs2 k x5' x12' x13' x14' x15' (RAW2 & ARR2 & LEN2 & CP2 & MI2 & MU2 & WM2).
      pose proof (rw_cells_transport rsegs _ m0 m2 _ _ FR0 MU2 WM2 ltac:(cbn; lia)) as FR.
      pose proof (stk_transport_disjoint rsegs _ m0 m2 _ _ ST0 MU2 WM2 ltac:(cbn; lia)) as ST.
      (* [comment removed for export] *)
      zstep. rewrite (bv_swrap_small 32 (3 * q - eof)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      st1. st1. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eexists m2, bs2, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|]. split; [| exact ST].
      split; [exact RAW2|]. split; [exact ARR2|]. split; [exact LEN2|]. split; [exact CP2|]. split; [exact MI2|]. split; [exact MU2| exact WM2]. }
    step. if_cases EQ0; zify_cond EQ0.
    - (* [comment removed for export] *)
      zstep.
      arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * (q - 1) + 1) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
      arr_store (t + 3 * (q - 1) + 1) (3 * (q - 1) + 1) (3 * (q - 1) + 2) (mb1L_ok va vb vc vd Va Vb Vc Vd) NS1.
      arr_store (t + 3 * (q - 1) + 2) (3 * (q - 1) + 2) (3 * q - eof) (mb2L_ok va vb vc vd Va Vb Vc Vd) NS2.
      step. eapply EPI. split; [exact RAW|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact MI|]. split; [exact MU| exact WM].
    - (* [comment removed for export] *)
      step. step. if_cases EQ1; zify_cond EQ1.
      + (* [comment removed for export] *)
        arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * q - eof) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
        eapply EPI. split; [exact RAW|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact MI|]. split; [exact MU| exact WM].
      + (* [comment removed for export] *)
        zstep.
        arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * (q - 1) + 1) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
        arr_store (t + 3 * (q - 1) + 1) (3 * (q - 1) + 1) (3 * q - eof) (mb1L_ok va vb vc vd Va Vb Vc Vd) NS1.
        step. eapply EPI. split; [exact RAW|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.
End LOOP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TOP.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Definition ctx_chunk (nn : Z) (raw : list byte) (line : Z) : list cell := [C4 (wz nn); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]].

  (* [comment removed for export] *)
  Lemma db_pre :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a n lo nn line : Z) (raw : list byte),
      rw_cells rsegs m a (ctx_chunk nn raw line) -> 0 < a -> a + 92 <= lo -> 0 < n <= 64 ->
      Forall b64_saved (map bv_unsigned (firstn (Z.to_nat n) raw)) ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1 x5 x10 x16 x17,
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 t1 t2 sp s1 x10 a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) a4
                       (Z_to_bv 64 A_data_ascii2bin) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DB_J) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -16) /\ rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
          /\ rw_cells rsegs m1 a (ctx_chunk nn raw line))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom rsegs)).
  Proof.
    intros until raw. intros CTX POS BL NR SAVED ST LO MI. unfold P_evp_decodeblock_int, DB_J, A_data_ascii2bin.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    assert (L80 : length raw = 80%nat) by (destruct CTX as [[WF _] _]; cbn in WF; tauto).
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ctx_chunk, wz in CTX.
    carve_frame 16%nat ST.
    do 4 step.
    (* [comment removed for export] *) step. fbr.
    (* [comment removed for export] *) st1. step. step. try if_lit.
    (* [comment removed for export] *) step. step. step. tbr.
    (* [comment removed for export] *) step. step.
    (* [comment removed for export] *)
    pose proof (ctx_raw _ _ _ _ _ _ CTX) as RAW. box CTX.
    destruct (nth_error raw (Z.to_nat 0)) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    pose proof (saved_nth n raw 0 c0 SAVED N0 ltac:(lia)) as S0. pose proof (b64_saved_lt64 _ S0) as V0. destruct S0 as [B0 _]. pose proof (byte_range c0).
    pose proof (rd_raw _ _ _ 0 c0 RAW N0 ltac:(lia)) as RD. replace (a + 4 + 0) with (a + 4) in RD by lia. step. clear RD. rewrite (sxb_small c0) by lia.
    step. step. fbr. step.
    pose proof (rd_tab _ (bv_unsigned c0) MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD.
    unfold wz. step. tbr.
    (* [comment removed for export] *)
    step. step. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      step. unbox CTX. finish.
    - (* [comment removed for export] *)
      step. step. zstep. zstep. rewrite (Z.mod_small n 4294967296) by lia. zstep.
      destruct (nth_error raw (Z.to_nat (n - 1))) as [cl|] eqn:NL; [| apply nth_error_None in NL; lia].
      pose proof (saved_nth n raw (n - 1) cl SAVED NL ltac:(lia)) as SL. pose proof (b64_saved_lt64 _ SL) as VL. destruct SL as [BL1 _]. pose proof (byte_range cl).
      pose proof (rd_raw _ _ _ (n - 1) cl RAW NL ltac:(lia)) as RD. step. clear RD. rewrite (sxb_small cl) by lia.
      step. fbr. step.
      pose proof (rd_tab _ (bv_unsigned cl) MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD. unfold wz.
      pose proof (land_lt_pow2 (a2b (bv_unsigned cl)) 236 6 ltac:(lia) ltac:(lia)) as LL. change (2^6) with 64 in LL.
      zstep. step. tbr.
      unbox CTX. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma db_bad_tail :
    forall (ra sp gp tp x5 t1 t2 s0 s1 x10 a1 a2 a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n lo : Z),
      n mod 4 <> 0 -> 0 < n <= 64 ->
      rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk rsegs m lo (bv_unsigned sp + -16) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists x5' x16',
          ms' = MS (mkR ra sp gp tp x5' t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 (Z_to_bv 64 n) a4 a5 x16' x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 t1 t2 sp s1 x10 a1 a2 (Z_to_bv 64 n) a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros NM NR FR ST LO0 LO MI. unfold DB_J. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. change (Z.land n 3) with (Z.land n (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
    step. step. tbr.
    st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. eexists _, _. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma db_disp_loop :
    forall (ra sp gp tp x5 t1 t2 s0 s1 x10 a1 a2 a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q : Z),
      2 <= q <= 16 ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 (Z_to_bv 64 3) a4 a5 (Z_to_bv 64 0) (Z_to_bv 64 (4 * q - 4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DB_L3) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 a1 a2 (Z_to_bv 64 (4 * q)) a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom rsegs)).
  Proof.
    intros until q. intros QR. unfold DB_J, DB_L3.
    zstep. change (Z.land (4 * q) 3) with (Z.land (4 * q) (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
    replace ((4 * q) mod 4) with 0 by (rewrite Z.mul_comm, Z.mod_mul; lia).
    step. step. try if_lit. step. fbr. step. step. fbr. step. zstep.
    rewrite (bv_swrap_small 32 (4 * q - 4)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma db_disp_one :
    forall (ra sp gp tp x5 t1 t2 s0 s1 x10 a1 a2 a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      evt rsegs (fun ms' => exists x16',
          ms' = MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 (Z_to_bv 64 3) a4 a5 x16' x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DB_LAST) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 a1 a2 (Z_to_bv 64 4) a4 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom rsegs)).
  Proof.
    intros. unfold DB_J, DB_LAST.
    step. step. step. try if_lit. step. try if_lit. step. step. try if_lit. step.
    apply evt_done. eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition db_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : Z) (Q : mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\ Q m'.

  (* [comment removed for export] *)
  Lemma decblock_bad_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a n lo nn line : Z) (raw : list byte),
      rw_cells rsegs m a (ctx_chunk nn raw line) -> 0 < a -> a + 92 <= lo -> 0 < n <= 64 -> n mod 4 <> 0 ->
      Forall b64_saved (map bv_unsigned (firstn (Z.to_nat n) raw)) ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (db_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (-1)
                   (fun m' => munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                              /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' a (ctx_chunk nn raw line)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom rsegs)).
  Proof.
    intros until raw. intros CTX POS BL NR NM SAVED ST LO MI RAE.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply evt_cut; [eapply db_pre; eassumption|].
    intros ms1 (m1 & x5 & x10 & x16 & x17 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & CTX1).
    eapply evt_mono; [eapply db_bad_tail; [exact NM| exact NR| exact FR1| exact ST1| exact LO0| lia| exact MI1]|].
    intros ms2 (x5' & x16' & -> & ST2). unfold db_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST2| exact CTX1].
  Qed.

  (* [comment removed for export] *)
  Lemma decblock_ok_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a t q eof lo nn line : Z) (raw tj : list byte),
      rw_cells rsegs m a (ctx_chunk nn raw line) -> 0 < a -> a + 92 <= lo -> 1 <= q <= 16 -> 0 <= eof <= 2 ->
      Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)) ->
      u8arr rsegs m t tj -> 3 * q <= Z.of_nat (length tj) -> (a + 92 <= t \/ t + Z.of_nat (length tj) <= a) ->
      (t + Z.of_nat (length tj) <= lo \/ bv_unsigned sp <= t) ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (db_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (3 * q - eof)
                   (fun m' => munch [(bv_unsigned sp + -16, bv_unsigned sp); (t, t + Z.of_nat (length tj))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                              /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' a (ctx_chunk nn raw line)
                              /\ exists bs', u8arr rsegs m' t bs' /\ length bs' = length tj
                                   /\ firstn (Z.to_nat (3 * q - eof)) bs' = map b8 (firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw)))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 t) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 eof) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom rsegs)).
  Proof.
    intros until tj. intros CTX POS BL QR ER SAVED ARR TJ ASEP TSEP ST LO MI RAE.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (u8arr_bound _ _ _ _ ARR) as TB.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    assert (L80 : length raw = 80%nat) by (destruct CTX as [[WF _] _]; cbn in WF; tauto).
    eapply evt_cut; [eapply db_pre; try eassumption; lia|].
    intros ms1 (m1 & x5 & x10 & x16 & x17 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & CTX1).
    pose proof (ctx_raw _ _ _ _ _ _ CTX1) as RAW1.
    assert (ARR1 : u8arr rsegs m1 t tj) by (eapply u8arr_transport; [exact ARR| exact MU1| exact WM1| cbn; lia]).
    assert (I0 : INV (a + 4) t q raw tj m1 m1 tj 0).
    { split; [exact RAW1|]. split; [exact ARR1|]. split; [reflexivity|]. split; [apply copied_0; symmetry; apply SRC_length; lia|].
      split; [exact MI1|]. split; [apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    assert (FIN : forall m2 bs2 x5' x6' x7' x16' x17' x28' x29' x30',
      INV (a + 4) t q raw tj m1 m2 bs2 (3 * (q - 1)) ->
      evt rsegs (db_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (3 * q - eof)
                   (fun m' => munch [(bv_unsigned sp + -16, bv_unsigned sp); (t, t + Z.of_nat (length tj))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                              /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' a (ctx_chunk nn raw line)
                              /\ exists bs', u8arr rsegs m' t bs' /\ length bs' = length tj
                                   /\ firstn (Z.to_nat (3 * q - eof)) bs' = map b8 (firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw)))))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5' x6' x7' sp s1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (t + 3 * (q - 1))) (Z_to_bv 64 (a + 4 + 4 * (q - 1))) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 eof)
                 (Z_to_bv 64 A_data_ascii2bin) x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' t6)
            F (Z_to_bv 64 DB_LAST) fc None m2 (seg_rom rsegs))).
    { intros m2 bs2 x5' x6' x7' x16' x17' x28' x29' x30' I2.
      eapply evt_mono.
      { eapply (last_grp ra sp gp tp s1 (Z_to_bv 64 (-1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc (a + 4) t q eof raw tj m1); try eassumption; try lia. }
      intros ms3 (m3 & bs3 & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & -> & I3 & ST3).
      destruct I3 as (RAW3 & ARR3 & LEN3 & CP3 & MI3 & MU3 & WM3). unfold W in MU3.
      unfold db_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m3. split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; lia. }
      split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply rw_cells_transport; [exact CTX1| exact MU3| exact WM3|]. unfold ctx_chunk. cbn. lia. }
      exists bs3. split; [exact ARR3|]. split; [exact LEN3|].
      destruct CP3 as [_ CP3]. rewrite CP3. unfold SRC.
      assert (LG : length (map b8 (groups_bytes (vs q raw))) = (3 * Z.to_nat q)%nat).
      { rewrite length_map. apply groups_bytes_length. unfold vs. rewrite !length_map, length_firstn. lia. }
      rewrite firstn_app, LG, firstn_map. replace (Z.to_nat (3 * q - eof) - 3 * Z.to_nat q)%nat with 0%nat by lia.
      cbn [firstn]. rewrite app_nil_r. reflexivity. }
    destruct (Z.eq_dec q 1) as [Q1|QN].
    - (* [comment removed for export] *)
      subst q. change (4 * 1) with 4.
      eapply evt_cut; [eapply db_disp_one|]. intros ms2 (y16 & ->).
      replace (t + 3 * (1 - 1)) with t in FIN by lia. replace (a + 4 + 4 * (1 - 1)) with (a + 4) in FIN by lia.
      replace (3 * (1 - 1)) with 0 in FIN by lia. change (3 * 1) with 3 in FIN.
      eapply FIN. exact I0.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply db_disp_loop; lia|]. intros ms2 ->.
      replace (Z_to_bv 64 t) with (Z_to_bv 64 (t + 3 * 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (a + 4)) with (Z_to_bv 64 (a + 4 + 4 * 0)) by (f_equal; lia).
      change (Z_to_bv 64 3) with (Z_to_bv 64 (3 + 3 * 0)). change (Z_to_bv 64 0) with (Z_to_bv 64 (4 * 0)).
      eapply evt_cut.
      { eapply (l3_loop ra sp gp tp s1 (Z_to_bv 64 (-1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc (a + 4) t q eof raw tj m1) with (k := Z.to_nat (q - 2)) (g := 0);
          try eassumption; try lia. }
      intros ms3 (m3 & bs3 & y6 & y7 & y28 & y29 & y30 & -> & I3).
      eapply FIN. exact I3.
  Qed.
End TOP.

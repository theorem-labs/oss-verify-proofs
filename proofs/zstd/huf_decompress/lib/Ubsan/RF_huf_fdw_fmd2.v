From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_bdt_model RF_huf_fdw_cut RF_huf_fdw_fmb RF_huf_fdw_fmc.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fdw_fmd2_stmt : Prop :=
  fdw_fmc_stmt ->
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (m1 : fmem) (out : list Z) (s2 s1a c b1 p : Z) (jp junk : list byte)
         (o0 o1 s2a o2 s1b o3 s2b : Z) (d2 d3 d4 : bitD) (y1 y23 y25 y26 y27 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
  decode_sym dt true s2 (mkBD c b1 p false) = Ok (o1, s2a, d2) ->
  decode_sym dt true s1a d2 = Ok (o2, s1b, d3) -> decode_sym dt true s2a d3 = Ok (o3, s2b, d4) ->
  0 <= b1 < 20 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> p = 0) ->
  zlen out + 4 <= dcap -> Forall (fun v => 0 <= v < 256) out -> 0 <= o0 < 256 ->
  0 <= s1a < 2^(dt_tableLog dt) -> 0 <= s2 < 2^(dt_tableLog dt) ->
  rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells usegs m1 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                               C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  u8arr usegs m1 DST (map (Z_to_bv 8) (out ++ [o0]) ++ junk) -> zlen junk = dcap - zlen out - 1 ->
  munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
  bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
  bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> stk usegs m1 lo SP ->
  fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) ->
  evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1a) (Z_to_bv 64 s2) (Z_to_bv 64 1)
                          (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                          (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                          (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                          (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 b1) (Z_to_bv 64 (4 * s2 + (DT + 4))) y23
                          (Z_to_bv 64 0) y25 y26 y27 (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                      F (Z_to_bv 64 (PFDW_D + 112)) fc None m1 (seg_rom usegs)).

Ltac fm_brpc := try lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 ?b) _ _ _ _) =>
      let k := eval vm_compute in (b - 0x1f638 - 4) in let kk := fresh "brpc" in pose (kk := k)
  | |- evt _ _ (MS _ _ (if _ then _ else ?b) _ _ _ _) => idtac "PROBEBRFORM" b end.

Section FM.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
            (bs : list Z) (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Definition fm_box (P : Prop) : Prop := P.

  Lemma fm_dsym : forall s d o s' d', decode_sym dt true s d = Ok (o, s', d') ->
    exists c, nth_error (dt_cells dt) (Z.to_nat s) = Some c /\ 0 <= s < 2^(dt_tableLog dt)
      /\ 0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= dt_tableLog dt /\ 0 <= dc_newState c
      /\ dc_newState c + 2^(dc_nbBits c) <= 2^(dt_tableLog dt)
      /\ o = dc_symbol c /\ s' = dc_newState c + look_bits_fast d (dc_nbBits c) /\ d' = skip_bits d (dc_nbBits c).
  Proof.
    intros s d o s' d' D.
    destruct PRE as (HTL & HCL & HCOK & _).
    destruct (dsym_inv _ _ _ _ _ _ _ D) as (c & lb & SR & NE & -> & -> & -> & LB). cbv iota in LB. subst lb.
    pose proof (proj1 (Forall_forall _ _) HCOK c (nth_error_In _ _ NE)) as CK. cbv beta in CK.
    exists c. rewrite HCL in SR. repeat split; tauto || lia.
  Qed.

  Ltac fm_eqz := fd_zx; rewrite ?fd_nb by lia; rewrite ?fd_nbd by lia; rewrite ?Z.shiftl_mul_pow2 by lia; lia.
  Ltac fm_tb := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | T : bytes_at usegs mm (DT + 4) _ |- _ => idtac
    | MU : munch [(SP + 16, SP + 88); (DST, DST + dcap)] ?ma mm, T0 : fm_box (bytes_at usegs ?ma (DT + 4) _) |- _ =>
        let T := fresh "TBM" in
        assert (T : bytes_at usegs mm (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))
          by (apply (bytes_at_transport usegs _ ma mm (DT + 4) _ T0 MU); rewrite fse_cells_length; cbn [disjoint_from];
              lia)
    end end.
  Ltac fm_rd := fm_tb; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let a := cur_mem_addr in
    first [
      match goal with T : bytes_at usegs mm (DT + 4) _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_ns usegs mm (DT + 4) (dt_cells dt) s c a T NE ltac:(lia) ltac:(unfold wa; f_equal; fm_eqz))
          as R
      end
    | match goal with T : bytes_at usegs mm (DT + 4) _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_off usegs mm (DT + 4) (dt_cells dt) s c 2 2%nat T NE ltac:(lia) ltac:(lia) ltac:(lia)) as R;
        change (Z.to_nat 2) with 2%nat in R; unfold fse_cell_bytes, le2 in R; cbn [firstn skipn app Z_to_le_bytes] in R;
        rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in R by lia;
        replace (wa (DT + 4 + (4 * s + 2))) with a in R by (unfold wa; f_equal; fm_eqz)
      end ] end.
  Ltac fm_dstep stop := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2016c) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2040c) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [fm_rd; zstep | zstep] end).
  Ltac fm_lx := repeat match goal with H : context [Z.lxor ?a ?b] |- _ =>
    let a' := eval vm_compute in a in is_Zlit a'; let b' := eval vm_compute in b in is_Zlit b';
    let v := eval vm_compute in (Z.lxor a' b') in change (Z.lxor a b) with v in H end.
  Ltac fm_dref := try (exfalso; fd_clr; fm_lx; fd_zx; rewrite ?fd_nb in * by lia;
    rewrite ?fd_nbd in * by lia; rewrite ?fd_x4 in * by lia; rewrite ?Z.shiftl_mul_pow2 in * by lia; lia).
  Ltac fm_dwalk stop := fm_dstep stop; repeat (fm_brpc; fd_brk; fm_dref; fm_dstep stop).

  Lemma fm_lo16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    Z.land (ns + 65536 * sy + 16777216 * nb) 65535 = ns.
  Proof.
    intros sy nb ns A B C. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
    symmetry. apply (Z.mod_unique _ _ (sy + 256 * nb)); lia.
  Qed.

  Ltac fm_nrm := fd_zx; rewrite ?fd_nb in * by lia; rewrite ?fd_w in * by lia; rewrite ?fm_lo16 in * by lia;
    rewrite ?fd_land in * by lia; rewrite ?fd_sh in * by lia.
  Ltac fm_fix c B := fm_nrm; try replace (dc_nbBits c + B) with (B + dc_nbBits c) in * by lia.
  Ltac fm_st off sv E := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells usegs mm (SP + off) [C8 (Z_to_bv 64 ?e); _] |- _ =>
      let ES := fresh "ES" in
      assert (ES : e = sv)
        by (rewrite E; unfold look_bits_fast, u64; cbn [bd_cont bd_bits bd_ptr bd_zero];
            repeat match goal with |- context [u32 ?x] => lazymatch x with 64 - _ => fail | _ =>
              replace (u32 x) with x by (unfold u32; rewrite Z.mod_small; lia) end end;
            etransitivity; [apply Z.add_comm|]; reflexivity);
      rewrite ES in * end end.
  Ltac osb OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok usegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite le1_lit;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      let LJ2 := fresh "LJ" in
      pose proof (out_sb usegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite zlen_tl by lia; lia);
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end end.


  Ltac osb2 OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok usegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite le1_lit;
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m0' ?a [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      let LJ2 := fresh "LJ" in
      pose proof (out_sb usegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite zlen_tl by lia; lia);
      clear OUTA LJ;
      change (write_to_mem m0' a [Z_to_bv 8 v]) with (write_to_mem m0' (wa (D + zlen o)) [Z_to_bv 8 v]);
      repeat match goal with H : rw_cells segs m0' ?A ?cs |- _ =>
        apply (rw_cells_frame segs m0' A cs (D + zlen o) [Z_to_bv 8 v]) in H;
        [ | lia | simpl_sizes; slia | simpl_sizes; slia] end;
      repeat match goal with H : bytes_at segs m0' ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_write_other segs m0' (D + zlen o) [Z_to_bv 8 v] A2 bs2) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; rewrite ?fse_cells_length in *; slia ]
              | clear H ] end;
      footprint_after_store segs m0' (D + zlen o) [Z_to_bv 8 v];
      (lazymatch goal with HI : mem_inv segs m0' |- _ =>
         apply (mem_inv_store segs m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in HI; [ | exact SOK] end);
      clear SOK;
      let mN := fresh "m" in
      set (mN := write_to_mem m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in *; clearbody mN;
      try clear m0';
      rename OUT2 into OUTA; rename LJ2 into LJ
    end end.

  Notation W := [(SP + 16, SP + 88); (DST, DST + dcap)].
  Notation tl := (dt_tableLog dt).

  Lemma l2_nbw : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    Z.shiftr (bv_wrap 32 (ns + 65536 * sy + 16777216 * nb)) 24 = nb.
  Proof.
    intros sy nb ns A B C. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216.
    symmetry. apply (Z.div_unique _ _ nb (ns + 65536 * sy)); lia.
  Qed.

  Lemma l2_wrap : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    bv_wrap 32 (ns + 65536 * sy + 16777216 * nb) = ns + 65536 * sy + 16777216 * nb.
  Proof.
    intros sy nb ns A B C. unfold bv_wrap. change (bv_modulus 32) with 4294967296. apply Z.mod_small; lia.
  Qed.

  Lemma l2_nb2 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    Z.shiftr (ns + 65536 * sy + 16777216 * nb) 24 = nb.
  Proof.
    intros sy nb ns A B C. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216.
    symmetry. apply (Z.div_unique _ _ nb (ns + 65536 * sy)); lia.
  Qed.

  Ltac l2_nrm c B :=
    rewrite ?(sx16_short (dc_symbol c + 256 * dc_nbBits c)) in * by lia;
    rewrite ?(unsigned_lit (dc_symbol c + 256 * dc_nbBits c)) in * by lia;
    fm_fix c B;
    let LW := fresh "LW" in
    pose proof (l2_wrap (dc_symbol c) (dc_nbBits c) (dc_newState c) ltac:(lia) ltac:(lia) ltac:(lia)) as LW;
    rewrite LW in *; clear LW;
    let LN := fresh "LN" in
    pose proof (l2_nb2 (dc_symbol c) (dc_nbBits c) (dc_newState c) ltac:(lia) ltac:(lia) ltac:(lia)) as LN;
    rewrite LN in *; clear LN;
    try (replace (bv_swrap 32 (dc_nbBits c)) with (dc_nbBits c) in * by (symmetry; apply FseWalkKit.swrap32_small; lia));
    rewrite ?(Z.mod_small (dc_nbBits c) 18446744073709551616) in * by lia;
    rewrite ?(fd_lo16 (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia;
    rewrite ?(Z.mod_small (dc_newState c + 65536 * dc_symbol c + 16777216 * dc_nbBits c)) in * by lia;
    rewrite ?(fm_lo16 (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia;
    fm_fix c B;
    try (replace (bv_swrap 32 (B + dc_nbBits c)) with (B + dc_nbBits c) in * by (symmetry; apply FseWalkKit.swrap32_small; lia)).

  Lemma l2_byte : forall sy nb, 0 <= sy < 256 -> 0 <= nb -> Z_to_bv 8 (sy + 256 * nb) = Z_to_bv 8 sy.
  Proof.
    intros sy nb A B. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mul_comm 256 nb), Z.mod_add by lia. reflexivity.
  Qed.

  Lemma fmd2_core : forall (m1 : fmem) (out : list Z) (s2 s1a c b1 p : Z) (jp junk : list byte) (o0 o1 s2a : Z) (d2 : bitD)
      (y1 y23 y25 y26 y27 : word),
    decode_sym dt true s2 (mkBD c b1 p false) = Ok (o1, s2a, d2) ->
    0 <= b1 < 20 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) ->
    zlen out + 4 <= dcap -> 0 <= o0 < 256 -> 0 <= s1a < 2^tl -> 0 <= s2 < 2^tl ->
    rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                                 C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
    u8arr usegs m1 DST (map (Z_to_bv 8) (out ++ [o0]) ++ junk) -> zlen junk = dcap - zlen out - 1 ->
    munch W m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
    bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> stk usegs m1 lo SP ->
    (forall (m2 : fmem) (junk2 : list byte) (x23 x24 x26 x27 : word),
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s2a); C8 (Z_to_bv 64 (DT + 4))] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 (DT + 4))] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bd_bits d2)); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                                    C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       u8arr usegs m2 DST (map (Z_to_bv 8) (out ++ [o0; o1]) ++ junk2) -> zlen junk2 = dcap - zlen out - 2 ->
       munch W m0 m2 -> wmono usegs m0 m2 -> mem_inv usegs m2 ->
       bytes_at usegs m2 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
       bytes_at usegs m2 S (map (Z_to_bv 8) bs) -> stk usegs m2 lo SP ->
       evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1a) (Z_to_bv 64 s2a) (Z_to_bv 64 1)
                              (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                              (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                              (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                              (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d2)) (Z_to_bv 64 (4 * s1a + (DT + 4))) x23
                              x24 (Z_to_bv 64 0) x26 x27 (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                          F (Z_to_bv 64 (PFDW_D + 208)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1a) (Z_to_bv 64 s2) (Z_to_bv 64 1)
                            (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                            (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                            (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 b1) (Z_to_bv 64 (4 * s2 + (DT + 4))) y23
                            (Z_to_bv 64 0) y25 y26 y27 (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                       F (Z_to_bv 64 (PFDW_D + 112)) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros until y27. intros DK BR CR PR PE OL HO0 S1R S2R FS2 FS1 FBD OUTA LJ MU WM MI TBB SRCB STK KN.
    destruct PRE as (HTL & HCL & HCOK & HBY & HLO & HSP16 & HSPT & HS8 & HSE & HDT0 & HDT4 & HDTE & HD4 & HDE & HDC
                     & DJ1 & DJ2 & DJ3).
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    destruct (fm_dsym _ _ _ _ _ DK) as (cc & NE & SR & CS & CN & CX & CNS & Eo & Es & Ed). clear DK.
    unfold skip_bits, u32 in Ed. cbn [bd_cont bd_bits bd_ptr bd_zero] in Ed. rewrite Z.mod_small in Ed by lia.
    subst o1 d2. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits cc) ltac:(lia) ltac:(lia)) as PN.
    pose proof (munch_refl W m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    assert (TB0 : fm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    assert (SB0 : fm_box (bytes_at usegs m1 S (map (Z_to_bv 8) bs))) by exact SRCB.
    assert (SK0 : fm_box (stk usegs m1 lo SP)) by exact STK.
    assert (LO0 : zlen (out ++ [o0]) = zlen out + 1) by (rewrite length_app; cbn [length]; lia).
    clear TBB SRCB STK HBY HCOK.
    let s := eval vm_compute in (PFDW_D + 204) in fm_dwalk s.
    l2_nrm cc b1.
    fm_st 16 s2a Es.
    osb2 OUTA LJ.
    rewrite map_app in OUTA. cbn [map] in OUTA.
    rewrite (l2_byte (dc_symbol cc) (dc_nbBits cc)) in OUTA by lia.
    change ([Z_to_bv 8 (dc_symbol cc)]) with (map (Z_to_bv 8) [dc_symbol cc]) in OUTA.
    rewrite <- map_app, <- app_assoc in OUTA. cbn [app] in OUTA.
    rewrite (Z.shiftl_mul_pow2 s1a 2) by lia. change (2^2) with 4. rewrite (Z.mul_comm s1a 4).
    lazymatch goal with |- context [Z.b2z (?a mod ?M <? 1)] =>
      replace (Z.b2z (a mod M <? 1)) with 0 by (rewrite Z.mod_small by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.
    unfold fm_box in TB0, SB0, SK0.
    eapply KN.
    all: first [ eassumption
               | (rewrite ?length_app in *; cbn [length] in *; lia)
               | (apply (bytes_at_transport usegs W m1 _ (DT + 4) _ TB0 MU1); rewrite fse_cells_length; cbn [disjoint_from]; lia)
               | (apply (bytes_at_transport usegs W m1 _ S _ SB0 MU1); rewrite length_map; cbn [disjoint_from]; lia)
               | (apply (stk_transport_disjoint usegs W m1 _ lo SP SK0 MU1 WM1); cbn [disjoint_from]; lia) ].
  Qed.
End FM.

Theorem fdw_fmd2_proof : fdw_fmd2_stmt.
Proof.
  unfold fdw_fmd2_stmt. intros FMC SP gp tp F fc m0 S DT DST dcap lo bs dt POST m1 out s2 s1a c b1 p jp junk o0 o1 s2a o2 s1b o3
    s2b d2 d3 d4 y1 y23 y25 y26 y27 HPRE HNB D2 D3 D4 BR CR PR PE PZ OL OBY HO0 S1R S2R FS2 FS1 FBD OUTA LJ MU WM MI TBB SRCB STK
    KL3.
  pose proof HPRE as (HTL & HCL & HCOK & _).
  destruct (dsym_inv _ _ _ _ _ _ _ D2) as (c2 & lb & SR2 & NE2 & Eo & Es & Ed & LB).
  pose proof (proj1 (Forall_forall _ _) HCOK c2 (nth_error_In _ _ NE2)) as (CS2 & CN2 & CX2 & CNS2).
  unfold skip_bits, u32 in Ed. cbn [bd_cont bd_bits bd_ptr bd_zero] in Ed. rewrite Z.mod_small in Ed by lia.
  subst d2.
  destruct (dsym_inv _ _ _ _ _ _ _ D4) as (c4 & lb4 & SR4 & _ & _ & _ & _ & _).
  eapply (fmd2_core SP gp tp F fc m0 S DT DST dcap lo bs dt POST HPRE m1 out s2 s1a c b1 p jp junk o0 o1 s2a _ y1 y23 y25 y26
            y27 D2).
  all: try eassumption. all: try lia.
  intros m2 junk2 x23 x24 x26 x27 FS22 FS12 FBD2 OUTA2 LJ2 MU2 WM2 MI2 TB2 SB2 SK2.
  cbn [bd_bits] in *.
  eapply (FMC SP gp tp F fc m0 S DT DST dcap lo bs dt POST m2 out s1a s2a c (b1 + dc_nbBits c2) p jp junk2 o0 o1 o2 s1b o3 s2b
            d3 d4 y1 x23 x24 x26 x27).
  all: try eassumption. all: try lia.
Qed.

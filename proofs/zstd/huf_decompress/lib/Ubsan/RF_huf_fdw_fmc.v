From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_bdt_model RF_huf_fdw_cut RF_huf_fdw_fmb.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fdw_fmc_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (m1 : fmem) (out : list Z) (s1a s2a c b2 p : Z) (jp junk : list byte)
         (o0 o1 o2 s1b o3 s2b : Z) (d3 d4 : bitD) (y1 y23 y24 y26 y27 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
  decode_sym dt true s1a (mkBD c b2 p false) = Ok (o2, s1b, d3) -> decode_sym dt true s2a d3 = Ok (o3, s2b, d4) ->
  0 <= b2 < 32 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> p = 0) ->
  zlen out + 4 <= dcap -> Forall (fun v => 0 <= v < 256) out -> 0 <= o0 < 256 -> 0 <= o1 < 256 ->
  0 <= s1a < 2^(dt_tableLog dt) -> 0 <= s2a < 2^(dt_tableLog dt) ->
  rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2a); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells usegs m1 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b2); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                               C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  u8arr usegs m1 DST (map (Z_to_bv 8) (out ++ [o0; o1]) ++ junk) -> zlen junk = dcap - zlen out - 2 ->
  munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
  bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
  bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> stk usegs m1 lo SP ->
  fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) ->
  evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1a) (Z_to_bv 64 s2a) (Z_to_bv 64 1)
                          (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                          (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                          (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                          (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 b2) (Z_to_bv 64 (4 * s1a + (DT + 4))) y23 y24
                          (Z_to_bv 64 0) y26 y27 (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                      F (Z_to_bv 64 (PFDW_D + 208)) fc None m1 (seg_rom usegs)).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fm_d8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q.
Proof. intros q r R. symmetry. apply (Z.div_unique (8 * q + r) 8 q r); lia. Qed.

Ltac fm_q := repeat match goal with H : context [bv_wrap 32 (8 * ?q + ?r)] |- _ =>
                rewrite (wrap32_small (8 * q + r)) in H by lia end;
  repeat match goal with H : context [(8 * ?q + ?r) / 8] |- _ => rewrite (fm_d8 q r) in H by lia end;
  repeat match goal with H : context [bv_swrap 32 ?q] |- _ => rewrite (swrap32_small q) in H by lia end;
  repeat match goal with H : context [?q mod ?M] |- _ => is_var q; rewrite (Z.mod_small q M) in H by lia end.

Ltac fm_ref := try (exfalso; fd_clr; fm_q; lia).

Lemma fm_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac fm_zn := rewrite ?fm_land7, ?wrap32_eq, ?swrap32_eq in *;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 in * by lia; try change (2 ^ 3) with 8 in *.

Ltac fm_fix7 q r p := let v := reg_val 7%Z in lazymatch v with Z_to_bv 64 ?e =>
  let E := fresh "E7" in
  first [ assert (E : e = r) by (fd_clr; fm_zn; lia)
        | assert (E : e = 8 * q + r - 8 * p) by (fd_clr; fm_zn; lia) ];
  rewrite E in * end.

Lemma fm_le64_range : forall bs p, Forall (fun c => 0 <= c < 256) bs -> 0 <= p -> p + 8 <= zlen bs ->
  0 <= Znth p bs + 2^8 * Znth (p+1) bs + 2^16 * Znth (p+2) bs + 2^24 * Znth (p+3) bs
       + 2^32 * Znth (p+4) bs + 2^40 * Znth (p+5) bs + 2^48 * Znth (p+6) bs + 2^56 * Znth (p+7) bs < 2^64.
Proof.
  intros bs p BY P0 P8.
  pose proof (byte_Znth bs p BY ltac:(lia)). pose proof (byte_Znth bs (p+1) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+2) BY ltac:(lia)). pose proof (byte_Znth bs (p+3) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+4) BY ltac:(lia)). pose proof (byte_Znth bs (p+5) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+6) BY ltac:(lia)). pose proof (byte_Znth bs (p+7) BY ltac:(lia)).
  lia.
Qed.

Ltac fm_fin := repeat split; try lia; try reflexivity; try (intros; discriminate); try (intros; lia).

Lemma fm_reload_ok : forall bs d st d0, Forall (fun c => 0 <= c < 256) bs -> bitd_ok bs d -> bd_bits d <= 64 ->
  reload_dstream bs d = Ok (st, d0) ->
  bitd_ok bs d0 /\ bd_bits d0 <= 64 /\ bd_zero d0 = false /\ (st = Unfinished -> bd_bits d0 < 8).
Proof.
  intros bs [c bc p z] st d0 BY (BC & BB & BP0 & BPE & BSM & BZ) B64 RL.
  cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  assert (Z0 : z = false) by (destruct z; [specialize (BZ eq_refl); lia | reflexivity]). subst z.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  replace (64 <? bc) with false in RL by (symmetry; apply Z.ltb_ge; lia).
  assert (NB : Z.shiftr bc 3 = bc / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite NB in RL.
  destruct (8 <=? p) eqn:P8.
  - apply Z.leb_le in P8.
    rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
    pose proof (fm_le64_range bs (p - bc / 8) BY ltac:(lia) ltac:(lia)) as R.
    assert (L7 : Z.land bc 7 = bc mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite L7. fm_fin.
  - apply Z.leb_gt in P8. destruct (p =? 0) eqn:P0.
    + apply Z.eqb_eq in P0. subst p.
      destruct (bc <? 64); injection RL as <- <-; unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero];
        fm_fin.
    + apply Z.eqb_neq in P0.
      assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BSM L); lia | lia]).
      destruct (p - bc / 8 <? 0) eqn:PN.
      * apply Z.ltb_lt in PN. cbn iota in RL.
        rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
        pose proof (fm_le64_range bs (p - p) BY ltac:(lia) ltac:(lia)) as R.
        unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. fm_fin.
      * apply Z.ltb_ge in PN. cbn iota in RL.
        rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
        pose proof (fm_le64_range bs (p - bc / 8) BY ltac:(lia) ltac:(lia)) as R.
        unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. fm_fin.
Qed.

Ltac fm_pc := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let k := eval vm_compute in (pc - 0x1f638) in idtac "PROBEPC" k
  | |- _ => idtac "PROBEOTHER" end.

Ltac fm_brpc := try lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 ?b) _ _ _ _) =>
      let k := eval vm_compute in (b - 0x1f638 - 4) in let kk := fresh "brpc" in pose (kk := k)
  | |- evt _ _ (MS _ _ (if _ then _ else ?b) _ _ _ _) => idtac "PROBEBRFORM" b end.

Ltac fm_last n := lazymatch n with
  | O => idtac
  | Datatypes.S ?k => match goal with H : ?T |- _ =>
      let t := type of T in lazymatch t with Prop => idtac "PROBEH" T; clear H; fm_last k end end end.

Ltac fm_show := fm_pc;
  try (match goal with b := ?v |- _ => idtac "PROBEBR" v end);
  try (fd_clr; fm_last 5%nat).

Ltac fm_step stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20218) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2027c) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20438) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      try (match goal with E1 : bv_unsigned (zx32 _) = _, E2 : Z.shiftr _ 3 = _, E3 : _ mod 2 ^ 3 = _ |- _ =>
             rewrite ?E1, ?E2, ?E3 end); zstep end).


Section FM.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
            (bs : list Z) (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation SL3 pc mm x1 s1 s2 bits j ptr x21 x22 x23 x24 x25 x26 x27 cont :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1) (Z_to_bv 64 s2) (Z_to_bv 64 bits) (Z_to_bv 64 DST)
             (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ptr)
             (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + dcap - 3)) x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 cont) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac fm_fix17 q p := let v := reg_val 17%Z in lazymatch v with Z_to_bv 64 ?e =>
    let E := fresh "E17" in
    first [ assert (E : e = S + (p - q)) by (fd_clr; fm_zn; lia)
          | assert (E : e = S + 0) by (fd_clr; fm_zn; lia) ];
    rewrite E in * end.

  Ltac fm_src := let v := reg_val 17%Z in lazymatch v with Z_to_bv 64 (S + ?pp) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with SB : bytes_at usegs mm S (map (Z_to_bv 8) bs) |- _ =>
      pose proof (src_rd usegs mm S bs (pp + 0) SB ltac:(fd_clr; fm_zn; lia)) as B0;
      pose proof (src_rd usegs mm S bs (pp + 1) SB ltac:(fd_clr; fm_zn; lia)) as B1;
      pose proof (src_rd usegs mm S bs (pp + 2) SB ltac:(fd_clr; fm_zn; lia)) as B2;
      pose proof (src_rd usegs mm S bs (pp + 3) SB ltac:(fd_clr; fm_zn; lia)) as B3;
      pose proof (src_rd usegs mm S bs (pp + 4) SB ltac:(fd_clr; fm_zn; lia)) as B4;
      pose proof (src_rd usegs mm S bs (pp + 5) SB ltac:(fd_clr; fm_zn; lia)) as B5;
      pose proof (src_rd usegs mm S bs (pp + 6) SB ltac:(fd_clr; fm_zn; lia)) as B6;
      pose proof (src_rd usegs mm S bs (pp + 7) SB ltac:(fd_clr; fm_zn; lia)) as B7 end end end.

  Ltac fm_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    try (match goal with H : u8arr usegs mm DST _ |- _ => idtac "PROBEM u8arr" end);
    try (match goal with H : mem_inv usegs mm |- _ => idtac "PROBEM mem_inv" end);
    try (match goal with H : stk usegs mm lo SP |- _ => idtac "PROBEM stk" end);
    try (match goal with H : munch ?W ?ma mm |- _ => idtac "PROBEM munch" W end);
    try (match goal with H : wmono usegs ?ma mm |- _ => idtac "PROBEM wmono" end);
    try (match goal with H : bytes_at usegs mm (DT + 4) _ |- _ => idtac "PROBEM tbl" end);
    try (match goal with H : bytes_at usegs mm S _ |- _ => idtac "PROBEM src" end) end.

  Ltac fm_regs :=
    let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v8 := reg_val 8%Z in
    let v9 := reg_val 9%Z in let v10 := reg_val 10%Z in let v11 := reg_val 11%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v14 := reg_val 14%Z in let v15 := reg_val 15%Z in let v16 := reg_val 16%Z in
    let v17 := reg_val 17%Z in let v18 := reg_val 18%Z in let v19 := reg_val 19%Z in let v20 := reg_val 20%Z in
    let v21 := reg_val 21%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    idtac "PROBEXA" v5 v6 v7 v8 v9; idtac "PROBEXB" v10 v11 v12 v13 v14; idtac "PROBEXC" v15 v16 v17 v18;
    idtac "PROBEXD" v19 v20 v21 v29 v30 v31;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      try (match goal with H : rw_cells usegs mm (SP + 48) [?a; ?b; ?c; ?d; ?e; ?f] |- _ =>
             idtac "PROBEBD" b d e f end);
      try (match goal with H : rw_cells usegs mm (SP + 16) ?c |- _ => idtac "PROBEF16" c end);
      try (match goal with H : rw_cells usegs mm (SP + 32) ?c |- _ => idtac "PROBEF32" c end) end.

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
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [zstep | fm_rd; zstep] end).
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
      repeat match goal with H : bytes_at segs m0' _ _ |- _ => clear H end;
      footprint_after_store segs m0' (D + zlen o) [Z_to_bv 8 v];
      (lazymatch goal with HI : mem_inv segs m0' |- _ =>
         apply (mem_inv_store segs m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in HI; [ | exact SOK] end);
      clear SOK;
      let mN := fresh "m" in
      set (mN := write_to_mem m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in *; clearbody mN;
      try clear m0';
      rename OUT2 into OUTA; rename LJ2 into LJ
    end end.


  Lemma fmc_byte : forall a b, Z_to_bv 8 (a + 256 * b) = Z_to_bv 8 a.
  Proof.
    intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    replace (a + 256 * b) with (a + b * 2 ^ Z.pos 8) by (cbn; ring). rewrite Z.mod_add by (cbn; lia). reflexivity.
  Qed.

  Lemma fmc_ob : forall ns sy nb, 0 <= ns < 65536 -> 0 <= sy -> 0 <= nb ->
    (ns + 65536 * sy + 16777216 * nb) ≫ 16 = sy + 256 * nb.
  Proof.
    intros ns sy nb N Y B. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
    replace (ns + 65536 * sy + 16777216 * nb) with (ns + (sy + 256 * nb) * 65536) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  Qed.

  Ltac fmc_pcd := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let k := eval vm_compute in (pc - PFDW_D) in idtac "PCD" k
    | |- _ => idtac "PCD other" end.
  Ltac ogen := lazymatch goal with OUTA : u8arr usegs ?mm DST ?L |- _ =>
    lazymatch L with
    | _ ++ _ =>
        let LOB := fresh "LOB" in let ob := fresh "ob" in let EOB := fresh "EOB" in
        assert (LOB : Z.of_nat (length L) = dcap)
          by (rewrite !length_app, !length_map, ?length_app; cbn [length];
              try (match goal with LJx : Z.of_nat (length ?j) = dcap - Z.of_nat (length ?o) |- _ =>
                let LJc := fresh "LJc" in pose proof LJx as LJc; rewrite ?length_app in LJc; cbn [length] in LJc end);
              lia);
        remember L as ob eqn:EOB
    | _ => idtac end end.
  Ltac oun := match goal with EOB : ?ob = _ ++ _ |- _ => subst ob end.
  Ltac fmc_have := first [ match goal with H : u8arr usegs _ DST _ |- _ => idtac "OUTA present" end | idtac "OUTA GONE" ].

  Ltac osb4 OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    let a0 := cur_mem_addr in
    pose proof (u8arr_store_ok usegs mm D _ (zlen o) a0 OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia)
                  ltac:(first [reflexivity | unfold wa; f_equal; rewrite ?length_app; cbn [length]; lia])) as SOK;
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) =>
        replace E with (D + zlen o) in SOK |- * by (rewrite ?length_app; cbn [length]; lia)
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) =>
        replace E with (D + zlen o) in SOK |- * by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite le1_lit; rewrite ?fmc_ob by lia; rewrite ?fmc_byte;
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m0' ?a [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      let LJ2 := fresh "LJ" in
      pose proof (out_sb usegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v]))
        by (rewrite zlen_tl by lia; rewrite !length_app; cbn [length]; lia);
      clear OUTA LJ;
      change (write_to_mem m0' a [Z_to_bv 8 v]) with (write_to_mem m0' (wa (D + zlen o)) [Z_to_bv 8 v]);
      repeat match goal with H : rw_cells segs m0' ?A ?cs |- _ =>
        apply (rw_cells_frame segs m0' A cs (D + zlen o) [Z_to_bv 8 v]) in H;
        [ | lia | simpl_sizes; slia | simpl_sizes; slia] end;
      repeat match goal with H : bytes_at segs m0' _ _ |- _ => clear H end;
      footprint_after_store segs m0' (D + zlen o) [Z_to_bv 8 v];
      (lazymatch goal with HI : mem_inv segs m0' |- _ =>
         apply (mem_inv_store segs m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in HI; [ | exact SOK] end);
      clear SOK;
      let mN := fresh "m" in
      set (mN := write_to_mem m0' (wa (D + zlen o)) [Z_to_bv 8 v]) in *; clearbody mN;
      try clear m0';
      rename OUT2 into OUTA; rename LJ2 into LJ
    end end.
  Lemma fmc_lbf : forall dd nb, 1 <= nb <= 63 -> 0 <= look_bits_fast dd nb < 2^nb.
  Proof.
    intros dd nb N. unfold look_bits_fast, u64.
    replace ((FseNCount.u32 (64 - nb)) mod 64) with (64 - nb)
      by (unfold FseNCount.u32; rewrite (Z.mod_small (64 - nb) (2^32)) by lia; rewrite Z.mod_small by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftl (bd_cont dd) ((FseNCount.u32 (bd_bits dd)) mod 64)) (2^64) ltac:(lia)) as XB.
    rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia.
    replace (64 - nb + nb) with 64 by lia. lia.
  Qed.

  Ltac fmc_src := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | T : bytes_at usegs mm S (map (Z_to_bv 8) bs) |- _ => idtac
    | MU : munch [(SP + 16, SP + 88); (DST, DST + dcap)] ?ma mm, T0 : fm_box (bytes_at usegs ?ma S (map (Z_to_bv 8) bs)) |- _ =>
        let T := fresh "SRCM" in
        assert (T : bytes_at usegs mm S (map (Z_to_bv 8) bs))
          by (apply (bytes_at_transport usegs _ ma mm S _ T0 MU); rewrite length_map; cbn [disjoint_from]; lia)
    end end.

  Ltac fmc_open :=
    destruct PRE as (HTL & HCL & HCOK & HBY & HLO & HSP16 & HSPT & HS8 & HSE & HDT0 & HDT4 & HDTE & HD4 & HDE & HDC
                     & DJ1 & DJ2 & DJ3).

  Lemma fmc_d4 : forall (m1 : fmem) (o3l : list Z) (s1b s2a c B3 p r9 r22 r24 : Z) (jp junk : list byte)
         (o3 s2b : Z) (d4 : bitD) (y1 y23 y26 y27 : word),
    Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
    decode_sym dt true s2a (mkBD c B3 p false) = Ok (o3, s2b, d4) ->
    r9 = DST + zlen o3l - 3 -> r22 = 4 * s2a + (DT + 4) -> r24 = 0 ->
    0 <= B3 < 48 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> p = 0) ->
    zlen o3l + 1 <= dcap -> 3 <= zlen o3l -> Forall (fun v => 0 <= v < 256) o3l ->
    0 <= s1b < 2^(dt_tableLog dt) -> 0 <= s2a < 2^(dt_tableLog dt) ->
    rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2a); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1b); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 B3); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                                 C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
    u8arr usegs m1 DST (map (Z_to_bv 8) o3l ++ junk) -> zlen junk = dcap - zlen o3l ->
    munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
    bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> stk usegs m1 lo SP ->
    fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (o3l ++ [o3]) s1b s2b d4) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1b) (Z_to_bv 64 s2a) (Z_to_bv 64 1)
                            (Z_to_bv 64 DST) (Z_to_bv 64 r9) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                            (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                            (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B3) (Z_to_bv 64 r22) y23 (Z_to_bv 64 r24)
                            (Z_to_bv 64 0) y26 y27 (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                        F (Z_to_bv 64 (PFDW_D + 304)) fc None m1 (seg_rom usegs)).
  Proof.
    intros until y27. intros FNB D4 E9 E22 E24 BR CR PR PE PZ OL O3 OB S1 S2 F16 F32 F48 OUTA LJ MU WM MI TBB SRCB STK K.
    subst r9 r22 r24.
    pose proof PRE as PRE0. fmc_open.
    pose proof (munch_refl [(SP + 16, SP + 88); (DST, DST + dcap)] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    assert (TB0 : fm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    assert (SB0 : fm_box (bytes_at usegs m1 S (map (Z_to_bv 8) bs))) by exact SRCB.
    pose proof (Z.pow_pos_nonneg 2 (dt_tableLog dt) ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^(dt_tableLog dt) <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    destruct (fm_dsym _ _ _ _ _ D4) as (c4 & NE4 & SR4 & CS4 & CN4 & CX4 & CNS4 & E4o & E4s & E4d). subst o3 d4.
    clear D4.
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c4) ltac:(lia) ltac:(lia)) as PN4.
    ogen.
    fm_dwalk 0.
    oun.
    fm_fix c4 B3.
    fm_st 16 s2b E4s.
    osb4 OUTA LJ.
    ogen.
    fm_dstep 0.
    all: fm_brpc; fd_brk; fm_dref.
    all: fm_dstep 0.
    all: replace (bv_swrap 32 (B3 + dc_nbBits c4)) with (B3 + dc_nbBits c4) in *
           by (symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2^31); lia).
    all: fm_brpc; fd_brk; fm_dref.
    all: try (fm_dstep (PFDW_D + -272)).
    all: change (Z_to_bv 64 (PFDW_D + -272)) with (Z_to_bv 64 PFDW_L3).
    all: oun.
    all: fm_tb.
    all: fmc_src.
    all: unfold fdw_l3_K in K; unfold skip_bits, FseNCount.u32 in K; cbn [bd_cont bd_bits bd_ptr bd_zero] in K.
    all: rewrite (Z.mod_small (B3 + dc_nbBits c4)) in K by lia.
    all: replace (DST + zlen o3l - 3 + 4) with (DST + zlen (o3l ++ [dc_symbol c4])) by (rewrite length_app; cbn [length]; lia).
    all: assert (NB4 : 1 <= dc_nbBits c4) by (rewrite Forall_forall in FNB; apply FNB; eapply nth_error_In; exact NE4).
    all: pose proof (fmc_lbf (mkBD c B3 p false) (dc_nbBits c4) ltac:(lia)) as LB4.
    all: eapply K.
    all: lazymatch goal with
         | |- sm_ok _ _ _ =>
             unfold sm_ok, bitd_ok; cbn [de_bd de_out bd_cont bd_bits bd_ptr bd_zero];
             split; [repeat split; try lia; intros; discriminate|];
             split; [lia|]; split; [rewrite length_app; cbn [length]; lia|];
             apply Forall_app; split; [assumption | constructor; [lia | constructor]]
         | |- st_ok _ _ => unfold st_ok; cbn [de_s1 de_s2]; split; [lia | rewrite E4s; lia]
         | |- fdw_mem _ _ _ _ _ _ _ _ _ _ _ _ =>
             unfold fdw_mem, sm_inv, bitdz_cells; cbn [de_s1 de_s2 de_bd de_out bd_cont bd_bits bd_ptr bd_zero];
             repeat match goal with |- _ /\ _ => split end;
             first [ eassumption | eexists; split; eassumption | idtac ]
         | |- _ => idtac
         end.
  Qed.
  Lemma fmc_d3 : forall (m1 : fmem) (out : list Z) (s1a s2a c B p : Z) (jp junk : list byte)
         (o0 o1 o2 s1b o3 s2b : Z) (d3 d4 : bitD) (y1 y23 y24 y26 y27 : word),
    Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
    decode_sym dt true s1a (mkBD c B p false) = Ok (o2, s1b, d3) -> decode_sym dt true s2a d3 = Ok (o3, s2b, d4) ->
    0 <= B < 32 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> p = 0) ->
    zlen out + 4 <= dcap -> Forall (fun v => 0 <= v < 256) out -> 0 <= o0 < 256 -> 0 <= o1 < 256 ->
    0 <= s1a < 2^(dt_tableLog dt) -> 0 <= s2a < 2^(dt_tableLog dt) ->
    rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2a); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 48) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + p));
                                 C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
    u8arr usegs m1 DST (map (Z_to_bv 8) (out ++ [o0; o1]) ++ junk) -> zlen junk = dcap - zlen out - 2 ->
    munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
    bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> stk usegs m1 lo SP ->
    fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1a) (Z_to_bv 64 s2a) (Z_to_bv 64 1)
                            (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8))
                            (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5))
                            (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B) (Z_to_bv 64 (4 * s1a + (DT + 4))) y23 y24
                            (Z_to_bv 64 0) y26 y27
                            (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                        F (Z_to_bv 64 (PFDW_D + 208)) fc None m1 (seg_rom usegs)).
  Proof.
    intros until y27. intros FNB D3 D4 BR CR PR PE PZ OL OB O0 O1 S1 S2 F16 F32 F48 OUTA LJ MU WM MI TBB SRCB STK K.
    pose proof PRE as PRE0. fmc_open.
    pose proof (munch_refl [(SP + 16, SP + 88); (DST, DST + dcap)] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    assert (TB0 : fm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    assert (SB0 : fm_box (bytes_at usegs m1 S (map (Z_to_bv 8) bs))) by exact SRCB.
    pose proof (Z.pow_pos_nonneg 2 (dt_tableLog dt) ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^(dt_tableLog dt) <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    destruct (fm_dsym _ _ _ _ _ D3) as (c3 & NE3 & SR3 & CS3 & CN3 & CX3 & CNS3 & E3o & E3s & E3d). subst o2 d3.
    clear D3.
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c3) ltac:(lia) ltac:(lia)) as PN3.
    unfold skip_bits, FseNCount.u32 in D4. cbn [bd_cont bd_bits bd_ptr bd_zero] in D4.
    rewrite (Z.mod_small (B + dc_nbBits c3)) in D4 by lia.
    assert (NB3 : 1 <= dc_nbBits c3) by (rewrite Forall_forall in FNB; apply FNB; eapply nth_error_In; exact NE3).
    pose proof (fmc_lbf (mkBD c B p false) (dc_nbBits c3) ltac:(lia)) as LB3.
    ogen.
    fm_dwalk 0.
    oun.
    fm_fix c3 B.
    fm_st 32 s1b E3s.
    osb4 OUTA LJ.
    fm_tb. fmc_src.
    replace (out ++ [o0; o1; dc_symbol c3; o3]) with (((out ++ [o0; o1]) ++ [dc_symbol c3]) ++ [o3]) in K
      by (rewrite <- !app_assoc; reflexivity).
    eapply (fmc_d4 _ _ s1b s2a c (B + dc_nbBits c3) p); try exact K; try exact D4.
    all: first [ eassumption
               | reflexivity
               | (rewrite !length_app; cbn [length]; lia)
               | (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia)
               | (lazymatch goal with |- Z.b2z ?b = 0 => destruct b eqn:EB; [apply Z.ltb_lt in EB;
                    rewrite ?Z.shiftl_mul_pow2 in EB by lia; rewrite Z.mod_small in EB by lia; lia | reflexivity] end)
               | (apply Forall_app; split; [apply Forall_app; split; [assumption | repeat constructor; lia] | repeat constructor; lia])
               | (rewrite E3s; lia)
               | lia
               | idtac ].
  Qed.
End FM.

Theorem fdw_fmc_proof : fdw_fmc_stmt.
Proof.
  unfold fdw_fmc_stmt. intros SP gp tp F fc m0 S DT DST dcap lo bs dt POST. intros until y27. intros PRE.
  eapply (fmc_d3 SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE).
Qed.

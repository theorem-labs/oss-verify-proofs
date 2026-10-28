From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_iface2 RF_huf_tbl_kit
  RF_huf_bdt_model RF_huf_fdw_cut RF_huf_fdw_tk RF_huf_x2t_fr RF_huf_fdw_topb.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fw_zn1 H := match type of H with
  | context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) in H by lia
  | context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_lit x) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in H by lia
  | context [bv_wrap 32 ?x] => unfold bv_wrap in H; change (bv_modulus 32) with (2^32) in H
  | context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in H by lia
  | context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) in H by lia
  | context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) in H by lia
  | context [?x mod ?y] => rewrite (Z.mod_small x y) in H by lia
  | context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in H
  | context [Z.lxor ?x ?c] => is_Zlit c; rewrite (zb_lxor_ones x) in H by lia
  | context [1 * ?x] => rewrite (Z.mul_1_l x) in H
  end.
Ltac fw_zn H := repeat fw_zn1 H.
Ltac fw_zn_all := repeat match goal with H : _ |- _ => progress (fw_zn H) end.
Ltac fw_arith_only := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail | not (@eq Z _ _) => fail
      | and _ _ => fail | or _ _ => fail | @eq bool _ _ => fail
      | _ => clear H end end end.
Ltac fw_bsplit := repeat match goal with
  | H : context [Z.b2z (?a <? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (Z.ltb_spec a b) as [E|E]; intro H; cbn [Z.b2z] in H
  | H : context [Z.b2z (?a =? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (Z.eqb_spec a b) as [E|E]; intro H; cbn [Z.b2z] in H
  | H : context [Z.b2z (?a <=? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (Z.leb_spec a b) as [E|E]; intro H; cbn [Z.b2z] in H
  end.
Lemma fw_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fw_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fw_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac fw_lits := repeat match goal with
  | H : context [Z.lxor ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  | H : context [Z.land ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
  | H : context [Z.lor ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
  end.
Ltac fw_land := rewrite ?fw_land1, ?fw_land3, ?fw_land7 in *.
Ltac fw_refute U := exfalso; fw_arith_only; first [ lia
  | (fw_bsplit; fw_lits; lia)
  | (fw_land; Z.div_mod_to_equations; lia)
  | (fw_zn U; lia)
  | (change 1 with (Z.ones 1) in U; rewrite Z.land_ones in U by lia; change (2^1) with 2 in U; lia)
  | (change 3 with (Z.ones 2) in U; rewrite Z.land_ones in U by lia; change (2^2) with 4 in U; lia)
  | (change 7 with (Z.ones 3) in U; rewrite Z.land_ones in U by lia; change (2^3) with 8 in U; lia) ].
Ltac fw_is_uim pc := let b := eval vm_compute in (Z.eqb pc (PFSE_DECOMP + 4592)) in lazymatch b with true => idtac end.
Ltac fw_side_uim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => fw_is_uim pc end.
Ltac fw_alive U := let T := type of U in idtac "ALIVE" T.
Ltac fw_side U := first [ fw_side_uim; first [fw_refute U | fw_alive U]
                        | try (exfalso; fw_arith_only; (first [lia | fw_zn U; lia])) ].
Ltac fw_chk := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | true => cbv iota
  | false => cbv iota
  | _ => let U := fresh "U" in if_cases U; zify_cond U; fw_side U
  end end.
Ltac fw_uimref := fw_side_uim; exfalso; fw_arith_only; first [ (try fw_zn_all; lia) | (fw_bsplit; lia)
  | (fw_land; Z.div_mod_to_equations; lia) | (fw_bsplit; fw_lits; lia)
  | (fw_land; fw_bsplit; fw_lits; Z.div_mod_to_equations; lia) ].
Ltac fw_norm := rewrite ?zx16_lit by lia; try (rewrite ?Z.shiftl_mul_pow2 by lia);
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by lia end.
Ltac fw_notuim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  tryif fw_is_uim pc then fail else idtac end.
Ltac fw_notin L := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let b := eval vm_compute in (existsb (Z.eqb pc) L) in lazymatch b with true => fail | false => idtac end end.
Ltac fw_stops := constr:([PFSE_READNC_B; PFSE_BUILD_DT; PFDW_F; PFDW_NF; PFDW_EXIT]).
Ltac fw_step := let L := fw_stops in first [fw_chk | fw_uimref | fw_notin L; fw_notuim; zstep; fw_norm].
Ltac fw_walk := do 400 (try fw_step).
Ltac fw_where := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
  first [ lazymatch pc with Z_to_bv 64 ?p => let d := eval vm_compute in (p - PFSE_DECOMP) in idtac "STOP" d end
        | idtac "STOPX" ] end.


Ltac fw_addr H := repeat match type of H with
  | context [?b + ?c + Z.of_nat ?n] => is_Zlit c; let v := eval vm_compute in (c + Z.of_nat n) in
      replace (b + c + Z.of_nat n) with (b + v) in H by lia
  end.
Ltac fw_a0 := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
  let p := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
  let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in
  idtac "A0" v end.
Ltac fw_pc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let d := eval vm_compute in (pc - PFSE_DECOMP) in d end.


Lemma fdw_m_maxlog : forall dcap src maxLog wks nc msv tl hn, 512 <= wks ->
  read_ncount (repeat 0 256) 255 src = Ok (nc, msv, tl, hn) -> maxLog < tl ->
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = Err 44.
Proof.
  intros dcap src maxLog wks nc msv tl hn W5 RN ML. unfold fse_decompress_wksp, FSE_MAX_SYMBOL_VALUE.
  rewrite (proj2 (Z.ltb_ge wks 512) W5), RN. cbn [bind]. rewrite (proj2 (Z.ltb_lt maxLog tl) ML). reflexivity.
Qed.

Lemma fdw_m_wksp : forall dcap src maxLog wks nc msv tl hn, 512 <= wks ->
  read_ncount (repeat 0 256) 255 src = Ok (nc, msv, tl, hn) -> tl <= maxLog -> wks < FSE_DECOMPRESS_WKSP_SIZE tl msv ->
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = Err 44.
Proof.
  intros dcap src maxLog wks nc msv tl hn W5 RN ML WK. unfold fse_decompress_wksp, FSE_MAX_SYMBOL_VALUE.
  rewrite (proj2 (Z.ltb_ge wks 512) W5), RN. cbn [bind]. rewrite (proj2 (Z.ltb_ge maxLog tl) ML).
  rewrite (proj2 (Z.ltb_lt wks _) WK). reflexivity.
Qed.



Lemma fdw_m_small : forall dcap src maxLog wks, wks < 512 ->
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = Err 1.
Proof. intros dcap src maxLog wks W5. unfold fse_decompress_wksp. rewrite (proj2 (Z.ltb_lt wks 512) W5). reflexivity. Qed.

Lemma fdw_m_rnerr : forall dcap src maxLog wks e, 512 <= wks -> read_ncount (repeat 0 256) 255 src = Err e ->
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = Err e.
Proof.
  intros dcap src maxLog wks e W5 RN. unfold fse_decompress_wksp, FSE_MAX_SYMBOL_VALUE.
  rewrite (proj2 (Z.ltb_ge wks 512) W5), RN. reflexivity.
Qed.

Lemma fw_landm4 : forall x c, c = 2^63 - 4 -> 0 <= x < 4294967296 -> Z.land x c = 4 * (x / 4).
Proof.
  intros x c -> Hx.
  replace (2^63 - 4) with (Z.ldiff (Z.ones 63) (Z.ones 2)) by (vm_compute; reflexivity).
  rewrite Z.ldiff_land, Z.land_assoc, (Z.land_ones x 63) by lia.
  rewrite Z.mod_small by (split; [lia | apply (Z.lt_le_trans _ 4294967296); [lia | vm_compute; discriminate]]).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^2) with 4. lia.
Qed.

Lemma fw_negbv : forall e, Z_to_bv 64 (2^64 - e) = Z_to_bv 64 (- e).
Proof.
  intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (2^64 - e) with (- e + 1 * bv_modulus 64) by (unfold bv_modulus; cbn; lia).
  rewrite Z.mod_add by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Ltac fw_neg := repeat match goal with |- context [Z_to_bv 64 (?c - ?e)] => is_Zlit c;
  let b := eval vm_compute in (Z.eqb c (2^64)) in lazymatch b with true =>
  change c with (2^64); rewrite (fw_negbv e) end end.

Lemma fw_stk104w : forall m1 lo SPV, stk usegs m1 lo (SPV + -192) -> wr_at usegs m1 (SPV + -192) 88 -> lo <= SPV + -192 ->
  stk usegs m1 lo (SPV + -104).
Proof.
  intros m1 lo SPV ST W L. apply stk_of_wr_at in W. replace (SPV + -192 + 88) with (SPV + -104) in W by lia.
  apply (stk_merge usegs m1 lo (SPV + -192) (SPV + -104)); [exact ST | exact W | lia].
Qed.

Lemma fw_divmul : forall x c d k, c = k * d -> 0 < d -> x * c / d = x * k.
Proof. intros x c d k -> D. rewrite Z.mul_assoc. apply Z.div_mul. lia. Qed.

Ltac fw_wk H := repeat (first [ progress fw_zn H
  | match type of H with context [Z.land ?x ?c] => is_Zlit c; rewrite (fw_landm4 x c) in H by (first [reflexivity | lia]) end
  | match type of H with context [?x * ?c / ?d] => is_Zlit c; is_Zlit d; let k := eval vm_compute in (c / d) in
       rewrite (fw_divmul x c d k) in H by (first [reflexivity | lia]) end ]).


Lemma fw_u8split : forall m A (l : list byte) n1 n2, 0 <= n1 -> 0 <= n2 -> n1 + n2 <= zlen l -> u8arr usegs m A l ->
  exists l1 l2 l3, u8arr usegs m A l1 /\ u8arr usegs m (A + n1) l2 /\ u8arr usegs m (A + n1 + n2) l3
    /\ zlen l1 = n1 /\ zlen l2 = n2 /\ zlen l3 = zlen l - n1 - n2.
Proof.
  intros m A l n1 n2 H1 H2 H3 U.
  rewrite <- (firstn_skipn (Z.to_nat n1) l) in U. apply (u8arr_app usegs) in U. destruct U as [U1 U].
  rewrite length_firstn in U. replace (A + Z.of_nat (Nat.min (Z.to_nat n1) (length l))) with (A + n1) in U by lia.
  rewrite <- (firstn_skipn (Z.to_nat n2) (skipn (Z.to_nat n1) l)) in U. apply (u8arr_app usegs) in U. destruct U as [U2 U3].
  rewrite length_firstn, length_skipn in U3.
  replace (A + n1 + Z.of_nat (Nat.min (Z.to_nat n2) (length l - Z.to_nat n1))) with (A + n1 + n2) in U3 by lia.
  exists (firstn (Z.to_nat n1) l), (firstn (Z.to_nat n2) (skipn (Z.to_nat n1) l)), (skipn (Z.to_nat n2) (skipn (Z.to_nat n1) l)).
  rewrite !length_firstn, !length_skipn.
  split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [lia|]. split; lia.
Qed.

Lemma fw_resok : forall dcap src maxLog wks, Forall (fun c => 0 <= c < 256) src -> 0 <= dcap -> 0 <= maxLog <= 12 ->
  res_ok (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks).
Proof.
  intros dcap src maxLog wks B D M.
  destruct (fse_decompress_wksp_safe (repeat 0 256) dcap src maxLog wks read_ncount_safe (Forall_all_bytes _ B) D
             ltac:(unfold FSE_MAX_TABLELOG; lia) ltac:(unfold FseNCount.Zlength; rewrite repeat_length; lia)) as [(l & E & _) | (e & E)];
    rewrite E; unfold res_ok; exact I.
Qed.


Ltac fw_goaladdr := repeat match goal with |- context [?x + ?a + ?b] => is_Zlit a; is_Zlit b;
  let v := eval vm_compute in (a + b) in replace (x + a + b) with (x + v) by lia end.
Ltac fw_litfold := repeat match goal with
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  end.


Lemma fw_pre : forall SPV S W DST dcap lo src hn dt wks,
  dt_tableLog dt <= 12 -> 5 <= dt_tableLog dt -> zlen (dt_cells dt) = 2^(dt_tableLog dt) ->
  cells_ok (dt_tableLog dt) (dt_cells dt) -> Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat hn) src) ->
  zlen (skipn (Z.to_nat hn) src) = zlen src - hn -> 1 <= hn <= zlen src ->
  lo <= SPV - 448 -> SPV mod 16 = 0 -> SPV <= 2^47 -> 8 <= S -> S + zlen src <= lo ->
  0 < W -> W mod 4 = 0 -> W + wks <= lo -> 512 + FSE_DTABLE_SIZE (dt_tableLog dt) <= wks ->
  4 <= DST -> DST + dcap <= lo -> 0 <= dcap <= 255 ->
  (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
  fdw_pre (SPV + -192) (hn + S) (W + 512) DST dcap lo (skipn (Z.to_nat hn) src) dt.
Proof.
  intros SPV S W DST dcap lo src hn dt wks T12 T5 ZL CO BY ZB HN LO SA SP S8 SL W0 WA WL WD D4 DL DC J1 J2 J3.
  unfold FSE_DTABLE_SIZE in WD. unfold fdw_pre. rewrite ZB.
  split; [lia|]. split; [exact ZL|]. split; [exact CO|]. split; [exact BY|].
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. lia.
Qed.

Ltac fw_exit R a := eapply (fdw_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R a).
Ltac fw_side_close := first [ eassumption | exact (eq_refl _) | lia | (unfold FSE_DECOMP_STACK; eassumption)
  | (cbn [dres]; split; [reflexivity | lia])
  | (eapply fw_stk104w; [eassumption | eassumption | lia])
  | (eapply fdw_m_rnerr; [lia | eassumption])
  | (eapply fdw_m_maxlog; [lia | eassumption | eassumption]) ].

Theorem fdw_top : fse_readh_stmt -> fse_build_stmt -> fdw_nf_entry_stmt -> fdw_f_entry_stmt -> fse_decomp_stmt.
Proof.
  intros READ BUILD ENF EF. unfold fse_decomp_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    DST dcap S W wks maxLog src jd jw lo.
  intros OUT LJD SRCB BYS WKS LJW HDC HSL HML HWK HDST HS HW0 HWA HDL HSL2 HWL DJ1 DJ2 DJ3 STK LOS SPA SPR MI.
  intros -> -> -> -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold FSE_DECOMP_STACK in LOS.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp); (DST, DST + dcap); (W, W + wks)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct STK as [L _]; exact L).
  carve_frame 192%nat STK.
  unfold PFSE_DECOMP.
  fw_walk.
  2: (lazymatch goal with FR : rw_cells _ _ ?A (CB 8 ?j0 :: C4 ?v :: CB 76 ?j1 :: ?sv) |- _ =>
        apply (proj1 (rw_cells_app' usegs _ _ [CB 8 j0; C4 v; CB 76 j1] sv)) in FR; destruct FR as [FP FS];
        cbn [cells_size csize Nat.add] in FS; fw_addr FS;
        pose proof (stk_of_rw_cells usegs _ _ _ FP) as SP1; cbn [cells_size csize Nat.add] in SP1; fw_addr SP1
      end;
      fw_exit (@Err (list Z) 1) (-1);
      first [fw_side_close | (apply fdw_m_small; lia) | (eapply stk_merge; [eassumption | eassumption | lia])]).
  (* [comment removed for export] *)
  lazymatch goal with FR : rw_cells _ _ ?A (CB 8 ?j0 :: C4 ?v :: CB 76 ?j1 :: ?sv) |- _ =>
    pose proof (proj2 (proj1 (proj1 (rw_cells_app' usegs _ _ [CB 8 j0; C4 v; CB 76 j1] sv) FR))) as WR88;
    cbn [cells_size csize Nat.add] in WR88; change (Z.of_nat 88) with 88 in WR88;
    apply (rw_cells_split_CB usegs _ _ [CB 8 j0; C4 v] 76 j1 sv [4; 72]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR;
    apply (proj1 (rw_cells_app' usegs _ _ [CB 8 j0] _)) in FR; destruct FR as [F0 FR]; cbn [cells_size csize Nat.add] in FR; fw_addr FR;
    apply (proj1 (rw_cells_app' usegs _ _ [C4 v] _)) in FR; destruct FR as [FM FR]; cbn [cells_size csize Nat.add] in FR; fw_addr FR;
    apply (proj1 (rw_cells_app' usegs _ _ [CB 4 _] _)) in FR; destruct FR as [FT FR]; cbn [cells_size csize Nat.add] in FR; fw_addr FR;
    apply (proj1 (rw_cells_app' usegs _ _ [CB 72 _] _)) in FR; destruct FR as [FX FSAV]; cbn [cells_size csize Nat.add] in FSAV; fw_addr FSAV
  end.
  apply rw_cells_cb4_c4 in FT.
  assert (W512 : 512 <= wks) by lia.
  rewrite <- (firstn_skipn 512 jw) in WKS. apply (proj1 (u8arr_app usegs _ _ _ _)) in WKS. destruct WKS as [WK1 WK2].
  assert (LJ1 : length (firstn 512 jw) = (2 * 256)%nat) by (rewrite length_firstn; lia).
  destruct (u16_decode 256 _ LJ1) as (rt0 & LRT0 & RT0B & ERT0). rewrite <- ERT0 in WK1.
  rewrite length_firstn in WK2. replace (W + Z.of_nat (Nat.min 512 (length jw))) with (W + 512) in WK2 by lia.
  assert (LSB : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
  assert (LW2 : Z.of_nat (length (skipn 512 jw)) = wks - 512) by (rewrite length_skipn; lia).
  eapply evt_cut.
  { eapply (READ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -192) W (bv_unsigned sp + -184)
             (bv_unsigned sp + -180) S rt0 src 255 lo).
    all: unfold FSE_READ_STACK; first [eassumption | reflexivity | (unfold zlen; rewrite LRT0; lia) | lia | (f_equal; lia)]. }
  assert (ZRT : zlen rt0 = 256) by (rewrite LRT0; reflexivity).
  intros ms' PO; unfold fse_readh_post, FSE_READ_STACK in PO; rewrite ZRT in PO; revert ms' PO.
  lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
  rewrite (read_ncount_indep rt0 src ZRT) in POST.
  pose proof (read_ncount_safe (repeat 0 256) 255 src (Forall_all_bytes _ BYS) ltac:(unfold FSE_MAX_SYMBOL_VALUE; lia)
                ltac:(first [lia | unfold FseNCount.Zlength; rewrite repeat_length; lia | vm_compute; discriminate])) as RS.
  destruct RS as [(nc & msv & tl & hn & RN & TL0 & NOK & MSV & HNR) | (e & RN)]; rewrite RN in POST.
  - destruct POST as (RET & NCA & MSVC & TLC). subst.
    assert (TLR : 5 <= tl <= 15 /\ 0 <= msv).
    { destruct (read_ncount_total (repeat 0 256) 255 src (Forall_all_bytes _ BYS) ltac:(lia)
                  ltac:(unfold FseNCount.Zlength; rewrite repeat_length; lia)) as [(nc' & msv' & tl' & n' & RN' & _ & MSV' & TLR' & _) | (e' & RN')];
        rewrite RN in RN'; [injection RN' as _ <- <- _; split; [exact TLR' | lia] | discriminate]. }
    destruct TLR as [TLR MSV0].
    unfold FseNCount.Zlength in HNR.
    assert (P2 : 32 <= 2^tl <= 2^15) by (split; [change 32 with (2^5); apply Z.pow_le_mono_r; lia | apply Z.pow_le_mono_r; lia]).
    fw_walk.
    all: try (lazymatch fw_pc with 3608 => fw_exit (@Err (list Z) 44) (-44) | _ => fail end).
    all: try (lazymatch goal with |- evt _ _ _ => fail | |- _ => fw_side_close end).
    all: try (lazymatch goal with |- fse_decompress_wksp _ _ _ _ _ = Err 44 =>
      eapply fdw_m_wksp; [lia | eassumption | lia | ];
      match goal with H : _ < (Z.land _ _ + _) mod _ |- _ =>
        assert (T12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia);
        fw_wk H;
        unfold FSE_DECOMPRESS_WKSP_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_MAX_SYMBOL_VALUE;
        assert (P4 : 2^tl = 4 * 2^(tl-2)) by (replace tl with (2 + (tl - 2)) at 1 by lia; rewrite Z.pow_add_r by lia; reflexivity);
        rewrite P4 in H |- *; Z.div_mod_to_equations; lia
      end end).
    (* [comment removed for export] *)
    match goal with H : ?a <= zlen jw |- _ => lazymatch a with context [Z.land _ _] => fw_wk H; rename H into WKM end end.
    assert (T12 : tl <= 12) by lia.
    assert (WKFIT : 512 + FSE_DTABLE_SIZE tl + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= zlen jw /\ FSE_DECOMPRESS_WKSP_SIZE tl msv <= zlen jw).
    { clear - WKM P2 TLR MSV0 MSV T12.
      assert (P4 : 2^tl = 4 * 2^(tl-2)) by (replace tl with (2 + (tl - 2)) at 1 by lia; rewrite Z.pow_add_r by lia; reflexivity).
      unfold FSE_DECOMPRESS_WKSP_SIZE, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_MAX_SYMBOL_VALUE.
      rewrite P4 in *. Z.div_mod_to_equations; lia. }
    destruct WKFIT as [WKFIT WKD].
    destruct (fw_u8split _ _ (skipn 512 jw) (FSE_DTABLE_SIZE tl) (FSE_BUILD_DTABLE_WKSP_SIZE tl msv)
                ltac:(unfold FSE_DTABLE_SIZE; lia) ltac:(unfold FSE_BUILD_DTABLE_WKSP_SIZE; lia) ltac:(lia) WK2)
      as (ldt & lbw & lrs & UDT & UBW & URS & LDT & LBW & LRS).
    clear WK2.
    destruct (fdw_bdt_ok nc msv tl (zlen jw - 512 - FSE_DTABLE_SIZE tl) (NOK ltac:(lia)) T12 ltac:(lia) ltac:(lia))
      as (dt & BD & DTL & DZL & DCOK & DFM & DNB).
    destruct (rt_shorts src nc msv tl hn (Forall_all_bytes _ BYS) RN ltac:(lia)) as (NCS & NCL).
    eapply evt_cut.
    { eapply (BUILD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (W + 512) W (W + 512 + FSE_DTABLE_SIZE tl)
               (zlen jw - 512 - FSE_DTABLE_SIZE tl) msv tl nc ldt lbw dt lo).
      all: rewrite ?unsigned_lit by lia; unfold FSE_BUILD_STACK.
      all: first [eassumption | exact (proj1 NCA) | reflexivity | lia | (f_equal; lia)
                 | (unfold FSE_DTABLE_SIZE in *; Z.div_mod_to_equations; lia) | idtac].
      all: try (f_equal; unfold FSE_DTABLE_SIZE;
        assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia);
        rewrite (Z.mod_small tl 32) by lia; rewrite Z.mul_1_l; rewrite (swrap32_small (2^tl)) by lia;
        rewrite Z.mod_small by lia; try rewrite Z.mod_small by lia; lia).
 }
    intros ms' PO; unfold fse_build_post, FSE_BUILD_STACK in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO.
    lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    lazymatch goal with H : u8arr usegs _ (W + 512) (fse_dt_bytes dt) |- _ => apply fdw_dt_split in H; destruct H as [DTH TBB] end.
    pose proof SRCB as SRC2. rewrite <- (firstn_skipn (Z.to_nat hn) src) in SRC2. rewrite map_app in SRC2.
    apply bytes_at_app in SRC2. destruct SRC2 as [_ SRC2]. rewrite length_map, length_firstn in SRC2.
    replace (S + Z.of_nat (Nat.min (Z.to_nat hn) (length src))) with (hn + S) in SRC2 by lia.
    pose proof BYS as BY2. rewrite <- (firstn_skipn (Z.to_nat hn) src) in BY2. apply Forall_app in BY2. destruct BY2 as [_ BY2].
    assert (ZBS : zlen (skipn (Z.to_nat hn) src) = zlen src - hn) by (rewrite length_skipn; lia).
    lazymatch goal with FXh : rw_cells usegs _ (bv_unsigned sp + -176) [CB 72 ?j] |- _ =>
      apply (rw_cells_split_CB usegs _ _ [] 72 j [] [16; 16; 40]%nat) in FXh; [|reflexivity]; cbn [mk_CB_cells app] in FXh;
      apply (proj1 (rw_cells_app' usegs _ _ [CB 16 _] _)) in FXh; destruct FXh as [FR2 FXh]; cbn [cells_size csize Nat.add] in FXh; fw_addr FXh;
      apply (proj1 (rw_cells_app' usegs _ _ [CB 16 _] _)) in FXh; destruct FXh as [FR1 FRB]; cbn [cells_size csize Nat.add] in FRB; fw_addr FRB
    end.
    unfold fdw_nf_entry_stmt, fdw_f_entry_stmt, fdw_entry_at, PFDW_NF, PFDW_F in ENF, EF.
    fw_walk.
    all: rewrite ?(proj2 (Z.ltb_lt 0 DST)) by lia.
    all: rewrite ?(proj2 (Z.ltb_ge (DST + zlen jd) DST)) by lia.
    all: rewrite ?(proj2 (Z.ltb_ge (DST + zlen jd) 1)) by lia.
    all: cbn [Z.b2z]; fw_litfold.
    all: replace (Z_to_bv 64 (zlen src - hn)) with (Z_to_bv 64 (zlen (skipn (Z.to_nat hn) src))) by (rewrite ZBS; reflexivity).
    all: lazymatch fw_pc with
      | 732 => eapply (ENF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fse_decompress_wksp (repeat 0 256) (zlen jd) src maxLog (zlen jw)))
      | 416 => eapply (EF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fse_decompress_wksp (repeat 0 256) (zlen jd) src maxLog (zlen jw)))
      end.
    all: try (lazymatch goal with
      | |- true = true -> _ => intros _; apply DNB; lia
      | |- false = true -> _ => intros E; discriminate
      end).
    all: try (lazymatch goal with |- fdw_pre _ _ _ _ _ _ _ _ =>
      eapply (fw_pre _ _ _ _ _ _ _ _ _ (zlen jw)); rewrite ?DTL; first [eassumption | lia] end).
    all: try (first [eassumption | reflexivity | (fw_goaladdr; eassumption)]).
    all: try (lazymatch goal with |- decompress_usingDTable _ _ _ _ = _ =>
      rewrite (fdw_m_ok (zlen jd) src maxLog (zlen jw) nc msv tl hn dt) by (first [lia | eassumption]);
      f_equal; first [ match goal with H : dt_fastMode ?d = 0 |- _ => rewrite H; reflexivity end
                     | match goal with H : dt_fastMode ?d <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity end ] end).
    all: try (lazymatch goal with |- res_ok _ => apply fw_resok; [exact BYS | lia | lia] end).
    all: try (lazymatch goal with |- fdw_K _ _ _ _ _ _ _ _ _ _ _ =>
      eapply fdw_K_ok; [reflexivity | eassumption | eassumption | eassumption | lia | exact SPA | lia | lia | lia | lia
                       | eassumption | eassumption] end).
  - destruct POST as (RET & ER). subst.
    fw_walk.
    all: fw_neg.
    all: try (lazymatch fw_pc with 3608 => fw_exit (@Err (list Z) e) (- e) | _ => fail end).
    all: try (lazymatch goal with |- evt _ _ _ => fail | |- _ => fw_side_close end).
Qed.

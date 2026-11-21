(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_ukit Zg_defl_iface Zg_sto_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2 RefDeflStored5 RefDeflStored6 RefDeflStored7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_EMIT : Z := 0x187dc.
Definition Z_STO_TESTS : Z := 0x187c8.   (* [comment removed for export] *)
Definition Z_STO_TB4 : Z := 0x1879c.     (* [comment removed for export] *)
Definition Z_STO_TC4 : Z := 0x187ac.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hdr_srlw : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 3) = Z.shiftr x 3.
Proof.
  intros x Hx. assert (E : bv_wrap 32 x = x) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  rewrite E. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= x / 2^3 <= x) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). apply bv_swrap32_id. lia.
Qed.


Lemma land_brk : forall (b1 b2 b3 : bool) (e : Z), (e = 0 \/ e = 1) ->
  Z.land (Z.land (if b1 then 0 else 1) (Z.lor (if b2 then 1 else 0) (Z.b2z b3))) e = if negb b1 && (b2 || b3) && (e =? 1) then 1 else 0.
Proof. intros b1 b2 b3 e H. destruct b1, b2, b3; destruct H as [-> | ->]; reflexivity. Qed.

Lemma brk_bool : forall (f len w : Z), 0 <= len ->
  ((len =? 0) && negb (f =? 4) || (f =? 0) || negb (len =? w)) =
  negb (negb (f =? 0) && ((f =? 4) || (0 <? len)) && ((if len =? w then 1 else 0) =? 1)).
Proof.
  intros f len w H. destruct (f =? 0), (f =? 4), (len =? w); destruct (Z.eqb_spec len 0); destruct (Z.ltb_spec 0 len); cbn; try reflexivity; lia.
Qed.

Lemma lxor_b2z : forall a b, 0 <= a -> 0 <= b -> Z.b2z (Z.lxor a b <? 1) = if a =? b then 1 else 0.
Proof.
  intros a b Ha Hb. pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)) as N.
  destruct (Z.eqb_spec a b) as [E|NE].
  - subst. rewrite Z.lxor_nilpotent. reflexivity.
  - destruct (Z.eq_dec (Z.lxor a b) 0) as [Z0|Z0].
    + exfalso. apply NE. apply (proj1 (Z.lxor_eq_0_iff a b)). exact Z0.
    + replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.


Section PURE.
Variable X : deflate_state.
Let v := ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X).
Let have := cs_avail_out (ds_strm X) - sb_hdr X.

Lemma sb_left_eq' : 0 <= ds_block_start X <= ds_strstart X -> ds_strstart X <= 65536 -> sb_left X = ds_strstart X - ds_block_start X.
Proof using have v. intros H1 H2. unfold sb_left. rewrite wrap32_mod. apply Z.mod_small. lia. Qed.

Lemma sb_len1_mach : 0 <= ds_block_start X <= ds_strstart X -> ds_strstart X <= 65536 -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  sb_len1 X = (if v <? 65535 then v else 65535).
Proof using have.
  intros H1 H2 H3. unfold sb_len1. rewrite sb_left_eq' by assumption. subst v.
  destruct (Z.ltb_spec (ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X)) 65535); [|reflexivity].
  rewrite wrap32_mod. apply Z.mod_small. lia.
Qed.

Lemma sb_len_mach : sb_len X = (if have <? sb_len1 X then have else sb_len1 X).
Proof using. reflexivity. Qed.
End PURE.

(* [comment removed for export] *)
Lemma swrap32_big : forall v, 2^31 <= v < 2^32 -> wz (bv_swrap 32 v) = wz (v + 2^64 - 2^32).
Proof.
  intros v Hv. apply Z_to_bv_eqm. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div]. change (4294967296 / 2) with 2147483648.
  change (2^31) with 2147483648 in Hv. change (2^32) with 4294967296 in Hv.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_swrap32 : forall a v, 0 <= a < 2^31 -> 0 <= v < 2^32 -> bv_eqb (wz a) (wz (bv_swrap 32 v)) = (a =? v).
Proof.
  intros a v Ha Hv. unfold bv_eqb.
  destruct (Z_lt_le_dec v (2^31)).
  - rewrite bv_swrap32_id by lia. rewrite !unsigned_lit by lia. reflexivity.
  - rewrite swrap32_big by lia. rewrite !unsigned_lit by lia.
    destruct (Z.eqb_spec a (v + 2^64 - 2^32)); destruct (Z.eqb_spec a v); first [reflexivity| exfalso; lia].
Qed.

(* [comment removed for export] *)
Lemma slt0_lxor : forall b, 0 <= b < 2^63 -> (9223372036854775808 <? Z.lxor b 9223372036854775808) = (0 <? b).
Proof.
  intros b Hb. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec 0 b); [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Lemma lss_guard : forall bs ss, 0 <= bs <= ss -> ss < 2^62 ->
  (Z.lxor (ss - bs) 9223372036854775808 <? Z.lxor ss 9223372036854775808) = (0 <? bs).
Proof.
  intros bs ss H1 H2. rewrite slt_lxor by lia.
  destruct (Z.ltb_spec 0 bs); [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Lemma and26 : forall flush len, 0 <= len ->
  Z.land (if flush =? Z_FINISH then 0 else 1) (Z.b2z (len <? 1)) = (if (len =? 0) && negb (flush =? Z_FINISH) then 1 else 0).
Proof.
  intros flush len H. destruct (Z.eqb_spec flush Z_FINISH); destruct (Z.ltb_spec len 1); destruct (Z.eqb_spec len 0); cbn; first [reflexivity| lia].
Qed.

Section HEAD.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.

(* at Z_STO_EMIT (0x1877c): s1 = left, s2 = len, a1 = all, s3 = 1 *)
Definition KEMIT (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush rest0 lo r me X m' ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) y10
                        (wz (if sb_len X =? ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X) then 1 else 0))
                        y12 y13 y14 y15 y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31)
                    F (wz Z_STO_EMIT) fc None m' (seg_rom usegs)).

Variables (Q : machine_state -> Prop) (X : deflate_state).
Hypothesis RBV : 0 <= ds_bi_valid X <= 16.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X) < 2^31.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X) < 2^31.
Hypothesis RBS : 0 <= ds_block_start X <= ds_strstart X.
Hypothesis RSTR : ds_strstart X <= 65536.
Hypothesis KB : sb_broke X flush 32768 = true -> TK10 L flush ai0 1 rest0 lo r F fc me Q Z_STO_BREAK (dl_S L) X.
Hypothesis KE : sb_broke X flush 32768 = false -> KEMIT Q X.

Let v := ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X).
Let have := cs_avail_out (ds_strm X) - sb_hdr X.

Lemma sto_head : forall lz, TK L flush ai0 lz rest0 lo r F fc me Q Z_STO_HEAD X.
Proof using have v KE KB RSTR RBS RAI RAO RBV HFL CTX inp.
  intros lz. unfold TK. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_HEAD, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL.
  open_DST ST. open_A GA. open_D GD. open_zs ZS.
  pose proof (sb_hdr_eq X RBV) as [EH RH].
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  zs. gF. zstep. al8 (dl_S L). gF.
  zs. zs. zs. zs. zs.
  rewrite hdr_srlw by lia. first [rewrite <- EH | change (Z.shiftr (ds_bi_valid X + 42) 3) with (sb_hdr X)].
  zstep. br_cases K.
  { unfold TK10 in KB. eapply KB; [| exact INV]. rewrite sb_broke_eq. replace (cs_avail_out (ds_strm X) <? sb_hdr X) with true by (symmetry; apply Z.ltb_lt; exact K). reflexivity. }
  assert (HH : sb_hdr X <= cs_avail_out (ds_strm X)) by lia.
  pose proof (sb_len_range X ltac:(lia) HH) as (RL1 & RL2 & RL3).
  pose proof (sb_len1_mach X RBS RSTR RAI) as EL1. pose proof (sb_len_mach X) as EL. fold v in EL1. fold have in EL.
  assert (EBROKE : sb_broke X flush 32768 = sb_brk X flush 32768).
  { rewrite sb_broke_eq. replace (cs_avail_out (ds_strm X) <? sb_hdr X) with false by (symmetry; apply Z.ltb_ge; exact HH). reflexivity. }
  set (eqv := if sb_len X =? v then 1 else 0).
  assert (EBRK : sb_len X < 32768 ->
    sb_brk X flush 32768 = negb (negb (flush =? 0) && ((flush =? 4) || (0 <? sb_len X)) && (eqv =? 1))).
  { intros HLT. unfold sb_brk, Z_FINISH, Z_NO_FLUSH. rewrite (sb_left_eq' X RBS RSTR), wrap32_mod, Z.mod_small by lia.
    replace (sb_len X <? 32768) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    rewrite brk_bool by lia. reflexivity. }
  assert (KE' : forall (a0v a2v a3v a4v a5v : word), sb_brk X flush 32768 = false ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) a0v (wz eqv) a2v a3v a4v a5v y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31) F (wz 0x187dc) fc None m' (seg_rom usegs))).
  { intros a0v a2v a3v a4v a5v NB. unfold KEMIT in KE. eapply KE; [rewrite EBROKE; exact NB| exact INV]. }
  assert (K04 : forall (a2v a3v a4v a5v : word), sb_len X < 32768 ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) (wz (dl_S L)) (wz eqv) a2v a3v a4v a5v y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31) F (wz 0x187c8) fc None m' (seg_rom usegs))).
  { intros a2v a3v a4v a5v HLT. unfold stoR. zs. zs. zs. zs.
    rewrite (land_brk (flush =? 0) (flush =? 4) (0 <? sb_len X) eqv) by (unfold eqv; destruct (sb_len X =? v); [right|left]; reflexivity).
    pose proof (EBRK HLT) as EB.
    remember (negb (flush =? 0) && ((flush =? 4) || (0 <? sb_len X)) && (eqv =? 1)) as c eqn:EC.
    zstep. br_cases K4; destruct c; rewrite ?unsigned_lit in K4 by lia; try (exfalso; lia).
    all: first [ (unfold TK10 in KB; eapply KB; [| exact INV]; rewrite EBROKE, EB; reflexivity)
               | (eapply KE'; rewrite EB; reflexivity) ]. }
  assert (KCC : forall (a1v a3v a4v a5v : word), ds_strstart X - ds_block_start X <= sb_len X ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) (wz (dl_S L)) a1v (wz (ds_strstart X - ds_block_start X)) a3v a4v a5v y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31) F (wz 0x187b4) fc None m' (seg_rom usegs))).
  { intros a1v a3v a4v a5v HGE. unfold stoR. zs. zs. zs. zs.
    rewrite lxor_b2z by lia.
    replace (if sb_len X - (ds_strstart X - ds_block_start X) =? cs_avail_in (ds_strm X) then 1 else 0) with eqv
      by (unfold eqv; subst v; destruct (Z.eqb_spec (sb_len X - (ds_strstart X - ds_block_start X)) (cs_avail_in (ds_strm X)));
          destruct (Z.eqb_spec (sb_len X) (ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X))); lia).
    zstep. br_cases K5.
    - eapply KE'. unfold sb_brk. replace (sb_len X <? 32768) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - eapply K04. lia. }
  assert (KF8 : forall (a1v a2v a3v a4v a5v : word), sb_len X < ds_strstart X - ds_block_start X ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) (wz (dl_S L)) a1v a2v a3v a4v a5v y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31) F (wz 0x18798) fc None m' (seg_rom usegs))).
  { intros a1v a2v a3v a4v a5v HLT. unfold stoR. zs.
    replace (wz 0) with (wz eqv) by (f_equal; unfold eqv; replace (sb_len X =? v) with false by (symmetry; apply Z.eqb_neq; subst v; lia); reflexivity).
    zstep. br_cases K5.
    - eapply K04. lia.
    - zstep. eapply KE'. unfold sb_brk. replace (sb_len X <? 32768) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (KJ1 : forall (s2v a3v a4v a5v : word), sb_len X = have ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) (wz (dl_S L)) (wz (cs_avail_out (ds_strm X) - sb_hdr X)) (wz (ds_strstart X - ds_block_start X)) a3v a4v a5v y16 y17 s2v y20 y28 y29 y30 y31) F (wz 0x187ac) fc None m' (seg_rom usegs))).
  { intros s2v a3v a4v a5v ELEN. unfold stoR. zs.
    replace (wz (cs_avail_out (ds_strm X) - sb_hdr X)) with (wz (sb_len X)) by (f_equal; rewrite ELEN; reflexivity).
    zstep. br_cases K6.
    - eapply KF8. lia.
    - eapply KCC. lia. }
  assert (KJ2 : forall (s2v a1v a3v a4v a5v : word), s2v = wz (sb_len X) ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) (wz (dl_S L)) a1v (wz (ds_strstart X - ds_block_start X)) a3v a4v a5v y16 y17 s2v y20 y28 y29 y30 y31) F (wz 0x18794) fc None m' (seg_rom usegs))).
  { intros s2v a1v a3v a4v a5v ->. unfold stoR.
    zstep. br_cases K6.
    - eapply KCC. lia.
    - eapply KF8. lia. }
  zs. zs. zstep. zstep. zstep.
  rewrite (slt0_lxor (ds_block_start X)) by lia. rewrite (lss_guard (ds_block_start X) (ds_strstart X)) by lia.
  zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv iota.
  zs. rewrite ?(Z.mod_small (ds_strstart X - ds_block_start X)) by lia. rewrite ?(bv_swrap32_id (ds_strstart X - ds_block_start X)) by lia.
  zs. zstep. br_cases K1.
  - assert (EL1' : sb_len1 X = 65535) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
    zs. rewrite ?(bv_swrap32_id (cs_avail_out (ds_strm X) - sb_hdr X)) by lia.
    zstep. br_cases K2.
    + eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
    + eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
  - zs. zs. rewrite ?(bv_swrap32_id (65535 - (ds_strstart X - ds_block_start X))) by lia.
    zstep. br_cases K2.
    + assert (EL1' : sb_len1 X = v) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
      zs. rewrite ?(bv_swrap32_id (cs_avail_in (ds_strm X) + (ds_strstart X - ds_block_start X))) by lia.
      replace (cs_avail_in (ds_strm X) + (ds_strstart X - ds_block_start X)) with v by (subst v; lia).
      zs. rewrite ?(bv_swrap32_id (cs_avail_out (ds_strm X) - sb_hdr X)) by lia.
      zstep. br_cases K3.
      * eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have v); subst have v; lia.
      * zstep. eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have v); subst have v; lia.
    + assert (EL1' : sb_len1 X = 65535) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
      zs. zs. rewrite ?(bv_swrap32_id (cs_avail_out (ds_strm X) - sb_hdr X)) by lia.
      zstep. br_cases K3.
      * eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
      * eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
Qed.
End HEAD.

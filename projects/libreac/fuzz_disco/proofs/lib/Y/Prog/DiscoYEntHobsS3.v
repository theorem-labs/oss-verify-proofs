(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntHobsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis TCHKS : CheckSighting.tcheck_sighting_spec B.

Definition hb_inv9 : Z := 0xffffffffffff8e39.
Definition hb_rot (len : Z) : Z := Z.land (Z.lor (((hb_inv9 * len - 6) mod 2 ^ 64 * 2 ^ 14) mod 2 ^ 64) ((((hb_inv9 * len - 6) mod 2 ^ 64 * 2 ^ 48) mod 2 ^ 64) / 2 ^ 50)) 65535.

Lemma hb_land0 : forall a b, 0 <= b < 2 ^ 14 -> Z.land (a * 2 ^ 14) b = 0.
Proof.
  intros a b Hb. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 14) as [Hl | Hl].
  - rewrite Z.mul_pow2_bits_low by exact Hl. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ 14) Hb). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma hb_lor_add : forall a b, 0 <= b < 2 ^ 14 -> Z.lor (a * 2 ^ 14) b = a * 2 ^ 14 + b.
Proof.
  intros a b Hb. pose proof (hb_land0 a b Hb) as H0.
  rewrite <- (Z.lxor_lor _ _ H0). symmetry. apply Z.add_nocarry_lxor. exact H0.
Qed.

Lemma hb_rot_w : forall w, Z.land (Z.lor ((w * 2 ^ 14) mod 2 ^ 64) (((w * 2 ^ 48) mod 2 ^ 64) / 2 ^ 50)) 65535 = (w mod 2 ^ 16) mod 4 * 2 ^ 14 + (w mod 2 ^ 16) / 4.
Proof.
  intros w.
  assert (E1 : ((w * 2 ^ 14) mod 2 ^ 64) mod 2 ^ 16 = (w mod 2 ^ 16) mod 4 * 2 ^ 14).
  { rewrite (Z.mod_mod_divide (w * 2 ^ 14) (2 ^ 64) (2 ^ 16)) by (exists (2 ^ 48); reflexivity).
    rewrite (Z.mod_mod_divide w (2 ^ 16) 4) by (exists (2 ^ 14); reflexivity).
    change (2 ^ 16) with (4 * 2 ^ 14). apply Z.mul_mod_distr_r; lia. }
  assert (E2 : (((w * 2 ^ 48) mod 2 ^ 64) / 2 ^ 50) mod 2 ^ 16 = (w mod 2 ^ 16) / 4).
  { change (2 ^ 64) with (2 ^ 16 * 2 ^ 48). rewrite Z.mul_mod_distr_r by lia.
    change (2 ^ 50) with (4 * 2 ^ 48). rewrite Z.div_mul_cancel_r by lia.
    apply Z.mod_small. pose proof (Z.mod_pos_bound w (2 ^ 16) ltac:(lia)).
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  change 65535 with (Z.ones 16).
  rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
  rewrite E1, E2. apply hb_lor_add.
  pose proof (Z.mod_pos_bound w (2 ^ 16) ltac:(lia)).
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma hb_inv9_mod : forall len, (hb_inv9 * len - 6) mod 2 ^ 16 = (36409 * (len - 54)) mod 2 ^ 16.
Proof.
  intros len.
  replace (hb_inv9 * len - 6) with (36409 * (len - 54) + (30 + (2 ^ 48 - 1) * len) * 2 ^ 16) by (unfold hb_inv9; ring).
  apply Z.mod_add. lia.
Qed.

Lemma hb_rot_eq : forall len, hb_rot len = ((36409 * (len - 54)) mod 2 ^ 16) mod 4 * 2 ^ 14 + ((36409 * (len - 54)) mod 2 ^ 16) / 4.
Proof.
  intros len. unfold hb_rot. rewrite hb_rot_w.
  rewrite (Z.mod_mod_divide (hb_inv9 * len - 6) (2 ^ 64) (2 ^ 16)) by (exists (2 ^ 48); reflexivity).
  rewrite hb_inv9_mod. reflexivity.
Qed.

Lemma hb_core_iff : forall m q v b t, 0 <= m <= 65481 -> 36409 * m = 65536 * q + v -> 0 <= v < 65536 -> v = 4 * t + b -> 0 <= b < 4 -> (b * 16384 + t < 1821 <-> m mod 36 = 0).
Proof.
  intros m q v b t Hm Hq Hv Ht Hb. split.
  - intros H.
    assert (Hb0 : b = 0) by lia.
    subst b.
    assert (Hd : m + 65536 * (5 * m - 9 * q) = 36 * t) by lia.
    assert (Hz : forall d, m + 65536 * d = 36 * t -> d = 0) by (intros d Hd'; lia).
    assert (Hm36 : m = 36 * t) by (pose proof (Hz _ Hd); lia).
    clear - Hm36. lia.
  - intros H.
    pose proof (Z.div_mod m 36 ltac:(lia)) as Hj. rewrite H, Z.add_0_r in Hj.
    set (j := m / 36) in *. clearbody j. clear H.
    assert (Hz : forall d, v - 4 * j = 65536 * d -> d = 0) by (intros d Hd'; lia).
    assert (Hv4 : v = 4 * j) by (pose proof (Hz (20 * j - q) ltac:(lia)); lia).
    lia.
Qed.

Lemma hb_mod36 : forall x, (x - 52) mod 36 = 2 <-> (x - 54) mod 36 = 0.
Proof.
  intros x. split; intro; lia.
Qed.

Lemma hb_rot_cond : forall len, 54 <= len <= 65535 -> (hb_rot len <? 1821) = ((len - 52) mod 36 =? 2).
Proof.
  intros len Hl. rewrite hb_rot_eq.
  change (2 ^ 16) with 65536. change (2 ^ 14) with 16384.
  pose proof (Z.div_mod (36409 * (len - 54)) 65536 ltac:(lia)) as Hq.
  pose proof (Z.mod_pos_bound (36409 * (len - 54)) 65536 ltac:(lia)) as Hv.
  set (v := (36409 * (len - 54)) mod 65536) in *.
  set (q := (36409 * (len - 54)) / 65536) in *.
  pose proof (Z.div_mod v 4 ltac:(lia)) as Ht.
  pose proof (Z.mod_pos_bound v 4 ltac:(lia)) as Hb.
  set (b := v mod 4) in *. set (t := v / 4) in *.
  assert (Hm : 0 <= len - 54 <= 65481) by lia.
  pose proof (hb_core_iff (len - 54) q v b t Hm Hq Hv Ht Hb) as Hc.
  apply eq_true_iff_eq. rewrite Z.ltb_lt, Z.eqb_eq, hb_mod36. exact Hc.
Qed.

Lemma hb_mask1 : forall len, 2 <= len <= 65535 -> (len + Z.land ((0 - 1) mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64 = len - 2.
Proof.
  intros len Hl.
  replace (Z.land ((0 - 1) mod 2 ^ 64) (2 ^ 64 - 2)) with (2 ^ 64 - 2) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma hb_mask0 : forall len, 0 <= len <= 65535 -> (len + Z.land ((0 - 0) mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64 = len.
Proof.
  intros len Hl.
  replace (Z.land ((0 - 0) mod 2 ^ 64) (2 ^ 64 - 2)) with 0 by (vm_compute; reflexivity).
  lia.
Qed.

Lemma hb_clean_eq : forall len, 0 <= len <= 65535 -> (if len <? 54 then len else (len + Z.land ((0 - (if hb_rot len <? 1821 then 1 else 0)) mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64) = reac_frame_clean_len_model len.
Proof.
  intros len Hl. unfold reac_frame_clean_len_model.
  destruct (Z.ltb_spec len 54) as [Hs | Hs].
  - rewrite (proj2 (Z.leb_gt 54 len) Hs). reflexivity.
  - rewrite (proj2 (Z.leb_le 54 len) Hs). rewrite (hb_rot_cond len ltac:(lia)).
    destruct ((len - 52) mod 36 =? 2).
    + exact (hb_mask1 len ltac:(lia)).
    + exact (hb_mask0 len Hl).
Qed.

Lemma hb_clean_rng : forall len, 0 <= len <= 65535 -> 0 <= reac_frame_clean_len_model len <= len.
Proof.
  intros len Hl. unfold reac_frame_clean_len_model.
  destruct ((54 <=? len) && ((len - 52) mod 36 =? 2)) eqn:E.
  - apply andb_prop in E. destruct E as [E1 _]. apply Z.leb_le in E1. lia.
  - lia.
Qed.

Lemma hb_clean_small : forall len, 0 <= len < 54 -> reac_frame_clean_len_model len = len.
Proof.
  intros len Hl. unfold reac_frame_clean_len_model.
  rewrite (proj2 (Z.leb_gt 54 len)) by lia. reflexivity.
Qed.

Definition h3_acs : list YP09.chunk :=
  [YP09.mkChunk 368 (CVal 8 (SOff 563 0)); YP09.mkChunk 408 (CVal 8 (SOff 564 0))].
Definition h3_bigsv (k : nat) : sv :=
  SAlu ALU_ADD (SOff k 0)
    (SAlu ALU_AND
       (SAlu ALU_SUB (SLit 0)
          (SAlu ALU_SLTU
             (SAlu ALU_AND
                (SAlu ALU_OR
                   (SAlu ALU_SRL
                      (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 5192296858534819430008849677942784))
                         (SLit (-1688849860263936)))
                      (SLit 50))
                   (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 302231454903656816459776)) (SLit (-98304))))
                (SLit 65535))
             (SLit 1821)))
       (SLit (-2))).

Lemma h3_one : 0 <= 1 < 2 ^ 64.
Proof. lia. Qed.

Lemma h3_stk : 0 <= CheckSighting.TCHECK_SIGHTING_STK <= 16640.
Proof. unfold CheckSighting.TCHECK_SIGHTING_STK, ESTACK. lia. Qed.

Lemma h3_abort : forall E (k : nat) r, sv_denot E (SOff k 0) = w64 r -> (r = -1 \/ r = 0 \/ r = 1) ->
  branch_taken BC_GEU (sv_denot E (SAluw ALU_ADD (SOff k 0) (SLit (-2)))) (sv_denot E (SLit 18446744073709551613)) = true.
Proof.
intros E k r Hk Hr.
change (sv_denot E (SAluw ALU_ADD (SOff k 0) (SLit (-2)))) with
  (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SOff k 0))) (low32 (sv_denot E (SLit (-2)))))).
rewrite Hk. change (sv_denot E (SLit 18446744073709551613)) with (Z_to_bv 64 18446744073709551613).
change (sv_denot E (SLit (-2))) with (Z_to_bv 64 (-2)).
destruct Hr as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

Lemma h3_bltz : forall E (k : nat) r, sv_denot E (SOff k 0) = w64 r -> (r = -1 \/ r = 0 \/ r = 1) ->
  branch_taken BC_LT (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = (r <? 0).
Proof.
intros E k r Hk Hr. rewrite Hk. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
destruct Hr as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

Lemma h3_U48 : forall E k len, U E (SOff k 0) = len ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 5192296858534819430008849677942784)) (SLit (-1688849860263936))) =
  ((hb_inv9 * len - 6) mod 2 ^ 64 * 2 ^ 48) mod 2 ^ 64.
Proof.
intros E k len Hk. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite Hk, !U_SLit. unfold zcanon, M64.
rewrite Z.mul_mod_idemp_r by lia. rewrite Z.add_mod_idemp_l by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite Z.mul_mod_idemp_l by lia. f_equal. unfold hb_inv9. lia.
Qed.

Lemma h3_U14 : forall E k len, U E (SOff k 0) = len ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 302231454903656816459776)) (SLit (-98304))) =
  ((hb_inv9 * len - 6) mod 2 ^ 64 * 2 ^ 14) mod 2 ^ 64.
Proof.
intros E k len Hk. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite Hk, !U_SLit. unfold zcanon, M64.
rewrite Z.mul_mod_idemp_r by lia. rewrite Z.add_mod_idemp_l by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite Z.mul_mod_idemp_l by lia. f_equal. unfold hb_inv9. lia.
Qed.

Lemma h3_srl : forall E e, U E (SAlu ALU_SRL e (SLit 50)) = U E e / 2 ^ 50.
Proof.
intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 50) 63) with 50.
rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E e) as Hr. unfold M64 in Hr. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma h3_or_and : forall E a b,
  U E (SAlu ALU_AND (SAlu ALU_OR a b) (SLit 65535)) = Z.land (Z.lor (U E a) (U E b)) 65535.
Proof.
intros E a b. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64.
change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
apply Z.mod_mod_divide. exists (2 ^ 48). reflexivity.
Qed.

Lemma h3_big : forall E k len, U E (SOff k 0) = len ->
  U E (h3_bigsv k) = (len + Z.land ((0 - (if hb_rot len <? 1821 then 1 else 0)) mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64.
Proof.
intros E k len Hk. unfold h3_bigsv.
assert (HR : U E (SAlu ALU_AND
                (SAlu ALU_OR
                   (SAlu ALU_SRL
                      (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 5192296858534819430008849677942784))
                         (SLit (-1688849860263936)))
                      (SLit 50))
                   (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 302231454903656816459776)) (SLit (-98304))))
                (SLit 65535)) = hb_rot len).
{ rewrite h3_or_and, h3_srl, (h3_U48 E k len Hk), (h3_U14 E k len Hk). unfold hb_rot. rewrite Z.lor_comm. reflexivity. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hk.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite HR, !U_SLit. change (zcanon 1821) with 1821.
destruct (hb_rot len <? 1821); unfold zcanon, M64; f_equal; f_equal; vm_compute; reflexivity.
Qed.

Ltac h3_narrow HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac h3_awr := cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac h3_after :=
  lazymatch goal with HF : frame_of _ _ _ (ms_mem _) |- _ =>
    let M := fresh "M" in pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M; clear HF end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma h3_av : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HM a. unfold aview.
assert (E : mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a) by (unfold mbyte, mrestrict; rewrite HM; reflexivity).
rewrite E. reflexivity.
Qed.

Lemma h3_sg_ro : forall cx nb fr len A (W : world SEGS) m m', (forall x, m' x = m x) ->
  hb_sg cx nb fr len A W m -> hb_sg cx nb fr len A W m'.
Proof.
intros cx nb fr len A W m m' HM (LA & GA & SA). split; [exact LA|]. split; [|exact SA].
eapply YC88.garr8_aview_kept; [|exact GA]. intros x _. exact (h3_av (w_H W) m m' HM x).
Qed.

Lemma h3_rL : forall cx (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' RG (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
rewrite !RG by (cbv; tauto). repeat split; assumption.
Qed.

Lemma h3_pre8 : forall STK ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B STK ly S W regs mem md ch -> afn_pre SEGS B STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md [].
Proof.
intros STK ly S W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & _ & HQT).
assert (Q8 : forall r : bv 5, bv_unsigned r <> 8 -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r)
  by (intros r Hr; apply getr_other; intros X; apply Hr; rewrite X; reflexivity).
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite Q8 by (cbv; lia); reflexivity).
assert (Era : raZ (regupd regs 8 (Z_to_bv 64 0)) = raZ regs) by (unfold raZ; rewrite Q8 by (cbv; lia); reflexivity).
assert (E8 : s0Z (regupd regs 8 (Z_to_bv 64 0)) = 0).
{ unfold s0Z. rewrite getr_same; [reflexivity|]. intros X. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate X. }
unfold afn_pre. rewrite Esp, Era, E8. rewrite !Q8 by (cbv; lia).
refine (conj HAR (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj Hstk (conj Hpres (conj _ HQT)))))))).
left. split; [|reflexivity]. left. pose proof asan_consts as (C1 & _). lia.
Qed.

Lemma h3_fr_rng : forall cx h n nb fr len ly3 S3 (W : world SEGS) m md k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W m md k -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m ->
  d_frm cx nb fr len W m -> 0 <= fr < 2 ^ 64.
Proof.
intros cx h n nb fr len ly3 S3 W m md k HC HB (F1 & F2 & F3 & F4).
destruct (Z.eq_dec fr 0) as [-> | Hne]; [lia|].
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR & _).
assert (Hin : In (fr, len) (ablocks B ly3 S3)).
{ pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
  unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
destruct (al_blocks _ _ LAWS ly3 S3 W m md fr len HAR Hin) as (_ & Hfr0 & Hfrc & _).
pose proof alloc_ceiling_lt as HCL. pose proof (req_size_pos len ltac:(unfold REC_MAX in F1; lia)). lia.
Qed.

Lemma h3_ro : forall cx h i n now op nb fr len ly3 S3 (W : world SEGS) m m' md' k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W m' md' k -> (forall x, m' x = m x) ->
  hb_X cx op nb fr len W m -> d_sp0 cx i now W m -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m ->
  hb_X cx op nb fr len W m' /\ d_sp0 cx i now W m' /\ d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m'.
Proof.
intros cx h i n now op nb fr len ly3 S3 W m m' md' k HC HM
  (Hop & Hop2 & (F1 & F2 & F3 & F4) & (V200 & V328 & V368 & V408) & (V360 & V352) & Hlen & Hnb) (V208 & V320) Hbody.
pose proof (h3_av (w_H W) m m' HM) as Hav.
assert (VM : forall a nn vv, val_mem SEGS (rd W m) a nn vv -> val_mem SEGS (rd W m') a nn vv)
  by (intros a nn vv Hv; eapply YC88.val_mem_aview_kept_x; [|exact Hv]; intros x _; exact (Hav x)).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _ & _ & (Hn0 & _) & _).
split; [|split].
- split; [exact Hop|]. split; [exact Hop2|]. split.
  + split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    eapply YC88.garr8_aview_kept; [|exact F4]. intros x _. exact (Hav x).
  + split; [exact (conj (VM _ _ _ V200) (conj (VM _ _ _ V328) (conj (VM _ _ _ V368) (VM _ _ _ V408))))|].
    split; [exact (conj (VM _ _ _ V360) (VM _ _ _ V352))|]. exact (conj Hlen Hnb).
- exact (conj (VM _ _ _ V208) (VM _ _ _ V320)).
- destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m' md' k HC) as (_ & Hlo & _).
  pose proof asan_consts as (C1 & _).
  pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & _).
  apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W m m' (d_A cx) (d_A cx) (fun _ => False) Hbody).
  + unfold LLVMF_STK, MFRAME in *; lia.
  + unfold MFRAME in HA1; lia.
  + intros a [].
  + intros a _ _. exact (Hav a).
  + intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb.
  + exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W m ly3 S3 W m' md' k HC Hframe (fun a _ => Hav a)).
  + exact (cl_shadow_keep cx dsh_rec W W m m' Hshadow (fun a _ => Hav a)).
  + lia.
Qed.

Lemma h3_land4 : forall cx h i n now op nb fr len (fq : YK11.FPState) ly3 S3 (W : world SEGS) md' k acc E ss
  (ms : machine_state),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = HB_P4 ->
  d_rL B cx (ms_regs ms) -> hb_X cx op nb fr len W (ms_mem ms) -> d_sp0 cx i now W (ms_mem ms) ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) ->
  hb_R4 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros cx h i n now op nb fr len fq ly3 S3 W md' k acc E ss ms HB Hfq HJ HFR Hk Hev Hmo Hacc Hi Hn Hnow HS Hrv Hpc
  HrL HX Hsp0 HBD.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact Hfq|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
exact (conj Hi (conj Hn (conj Hnow (conj HrL (conj I (conj HX (conj Hsp0 HBD))))))).
Qed.

Lemma h3_kept : forall ly3 S3 (W : world SEGS) m4 (W2 : world SEGS) mem2 lo hi,
  acall_kept SEGS B ly3 S3 W m4 W2 mem2 lo hi (fun _ => False) -> cl_kept B ly3 S3 W m4 W2 mem2 lo hi (fun _ => False).
Proof.
intros ly3 S3 W m4 W2 mem2 lo hi (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hn _; exact (K1 a Ha Hn)|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. exact K6.
Qed.

Lemma h3_land3 : forall cx h i n now op nb fr len v (fq : YK11.FPState) ly3 S3 (W : world SEGS) (regs4 : bvmap 5 word)
  m4 md4 k acc ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rL B cx regs4 -> getr regs4 22 = w64 1 -> getr regs4 23 = w64 v ->
  hb_X cx op nb fr len W m4 -> (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) ->
  (exists A, hb_sg cx nb fr len A W m4 /\ (v = 1 -> s_role A <> 2)) ->
  d_sp0 cx i now W m4 -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m4 ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  ajournal SEGS B CheckSighting.TCHECK_SIGHTING_STK (d_A cx) [] ly3 S3 W m4 md4 [] ly2 S2 W2 mem2 md2 0 ->
  aregs_preserved regs4 regs2 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - CheckSighting.TCHECK_SIGHTING_STK <= a < d_A cx) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m4 a) ->
  hb_R3 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len v W2 (cfg_at (fx := fq) SEGS (BASE + HB_P3) regs2 mem2 md2).
Proof.
intros cx h i n now op nb fr len v fq ly3 S3 W regs4 m4 md4 k acc ly2 S2 W2 regs2 mem2 md2
  Hb Hfq HJ3 Hfrs Hk Hacc Hi Hn Hnow HrL R22 R23 HX Hv (A & HsgA & HroleA) Hsp0 Hbody HJ2 HJc HPR Hperm KEPT.
assert (HC3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W m4 md4 k)
  by (split; [exact Hb | split; [exact HJ3 | exact Hfrs]]).
pose proof HJc as (_ & _ & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfr2; exact Hfrs).
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hb | split; [exact HJ2 | exact Hfrs2]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k HC3)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HK : cl_kept B ly3 S3 W m4 W2 mem2 (d_A cx - CheckSighting.TCHECK_SIGHTING_STK) (d_A cx) (fun _ => False)).
{ apply h3_kept. exact (acall_kept_of_journal SEGS B pa_segs_low CheckSighting.TCHECK_SIGHTING_STK (d_A cx) [] [] ly3 S3 W m4 md4
    ly2 S2 W2 mem2 md2 0 (fun _ => False) HJc HAR ltac:(intros a (rg & Hrg & _); destruct Hrg)
    ltac:(intros b m0 i0 Hin _ _; exact (Permutation_in _ (Permutation_sym Hperm) Hin)) sink_closed_nil). }
assert (Hlo2 : d_S cx - LLVMF_STK <= d_A cx - CheckSighting.TCHECK_SIGHTING_STK)
  by (unfold CheckSighting.TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *; lia).
assert (VA : forall o w, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W m4) (d_A cx + o) 8 w ->
  val_mem SEGS (rd W2 mem2) (d_A cx + o) 8 w).
{ intros o w Ho1 Ho2 Hw. eapply YC88.val_mem_aview_kept_x; [|exact Hw]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply KEPT; unfold MFRAME, LLVMF_STK in *; lia. }
unfold hb_R3, d_arm_at_pf, d_at.
exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [reflexivity|]. split; [exact Hfq|]. split; [exact Hb|]. split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL. unfold spZ in Hsp |- *.
  assert (E2 : getr regs2 2 = getr regs4 2) by exact (cl_cs regs4 regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
  rewrite E2. split; [exact Hsp|].
  split; [exact (cl_cs regs4 regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Hgp)|].
  split; [exact (cl_cs regs4 regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Htp)|].
  split; [exact (cl_cs regs4 regs2 8 _ HPR ltac:(unfold acallee_saved; lia) H8)|].
  split; [exact (cl_cs regs4 regs2 9 _ HPR ltac:(unfold acallee_saved; lia) H9)|].
  split; [exact (cl_cs regs4 regs2 19 _ HPR ltac:(unfold acallee_saved; lia) H19)|].
  split; [exact (cl_cs regs4 regs2 18 _ HPR ltac:(unfold acallee_saved; lia) H18)|].
  split; [exact (cl_cs regs4 regs2 20 _ HPR ltac:(unfold acallee_saved; lia) H20)|].
  exact (cl_cs regs4 regs2 27 _ HPR ltac:(unfold acallee_saved; lia) H27). }
split; [exact (conj (cl_cs regs4 regs2 22 _ HPR ltac:(unfold acallee_saved; lia) R22)
  (cl_cs regs4 regs2 23 _ HPR ltac:(unfold acallee_saved; lia) R23))|].
split.
{ destruct HX as (Hop & Hop2 & Hfrm & (V200 & V328 & V368 & V408) & (V360 & V352) & Hlen & Hnb).
  split.
  - split; [exact Hop|]. split; [exact Hop2|].
    split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W m4 md4 k W2 mem2 _ _ (fun _ => False)
      h n dsh_rec HC3 Hbody HK (fun a Ha => False_ind _ Ha) Hfrm)|].
    split; [split; [apply VA; [lia | lia | exact V200]|]; split; [apply VA; [lia | lia | exact V328]|];
      split; [apply VA; [lia | lia | exact V368] | apply VA; [lia | lia | exact V408]]|].
    split; [split; [apply VA; [lia | lia | exact V360] | apply VA; [lia | lia | exact V352]]|].
    exact (conj Hlen Hnb).
  - split; [exact Hv|]. exists A. split; [|exact HroleA].
    destruct HsgA as (LA & GA & SA). split; [exact LA|]. split; [|exact SA].
    eapply YC88.garr8_aview_kept; [|exact GA]. intros a Ha. rewrite length_map, LA in Ha.
    change (Z.of_nat 24) with 24 in Ha. unfold d_obj in Ha. cbn [dobj_off] in Ha.
    pose proof alloc_ceiling_lt as HCL.
    apply KEPT; unfold CheckSighting.TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *; lia. }
split; [destruct Hsp0 as (S1 & S1'); split; apply VA; first [lia | assumption]|].
exact (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W m4 md4 k ly2 S2 W2 mem2
  md2 k (d_A cx - CheckSighting.TCHECK_SIGHTING_STK) (d_A cx) (fun _ => False) [] Hbody HC3 HC2 HK Hlo2 (Z.le_refl _)
  (fun a Ha => False_ind _ Ha) (fun a Ha _ => False_ind _ Ha) (Forall_nil _) Hperm BTOBS).
Qed.

Lemma h3_call : forall cx h i n now op nb fr len v (W : world SEGS) (fq : YK11.FPState) ly3 S3 (ms : machine_state)
  md4 k acc E ss,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rL B cx (ms_regs ms) -> getr (ms_regs ms) 22 = w64 1 -> getr (ms_regs ms) 23 = w64 v ->
  hb_X cx op nb fr len W (ms_mem ms) -> (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) ->
  forall A, hb_sg cx nb fr len A W (ms_mem ms) -> (v = 1 -> s_role A <> 2) ->
  d_sp0 cx i now W (ms_mem ms) -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) ->
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = BASE + AF_both3_check_sighting ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 (d_A cx - d_S cx)) -> bv_unsigned (ew E 2) = d_S cx ->
  getr (ms_regs ms) 1 = w64 (BASE + HB_P3) ->
  getr (ms_regs ms) 10 = w64 (d_obj cx OS) -> getr (ms_regs ms) 11 = w64 fr ->
  getr (ms_regs ms) 12 = w64 (reac_frame_clean_len_model len) -> getr (ms_regs ms) 13 = w64 (d_obj cx OOUR) ->
  getr (ms_regs ms) 14 = w64 1 ->
  SRr SEGS W (mkCfg ms md4) (fun W' c' => hb_R3 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len v W' c' \/
     hb_R4 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c').
Proof.
intros cx h i n now op nb fr len v W fq ly3 S3 ms md4 k acc E ss Hb Hfq HJ Hfrs Hk Hacc Hi Hn Hnow HrL R22 R23 HX Hv
  A HsgA HroleA Hsp0 Hbody HS Hrv Hpc Hsp2 HE2 R1 R10 R11 R12 R13 R14.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hb | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & _).
pose proof HX as (Hop & Hop2 & Hfrm & HspREC & HspOP & Hlen & Hnb).
pose proof Hfrm as (F1 & F2 & F3 & F4).
pose proof HsgA as (LA & GA & SA).
pose proof SA as (H50 & _).
pose proof (hb_clean_rng len ltac:(clear - F1; unfold REC_MAX in F1; lia)) as Hcr.
assert (Hlen0 : 0 < len) by (clear - H50 Hcr; lia).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct (hb_blk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k
  CheckSighting.TCHECK_SIGHTING_STK HC Hbody Hfrm Hlen Hlen0 h3_stk)
  as (Hin & Hf0 & Hf63 & _ & _ & _ & Hfoff & Hfstk & Hfsep & _).
destruct (hb_obj_read B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OS
  CheckSighting.TCHECK_SIGHTING_STK HC Hshadow ltac:(vm_compute; reflexivity) h3_stk)
  as (Hs0 & Hs63 & Hs8 & Hsam & Hsra & Hsshv & Hsoff & Hsstk & _).
destruct (hb_obj_read B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OOUR
  CheckSighting.TCHECK_SIGHTING_STK HC Hshadow ltac:(vm_compute; reflexivity) h3_stk)
  as (Hu0 & Hu63 & Hu8 & Huam & Hura & Hushv & Huoff & Hustk & _).
pose proof Hobjs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GU & _).
pose proof Hgeo as (_ & _ & _ & _ & _ & G6 & _).
assert (LF : length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) = Z.to_nat len)
  by (apply cl_rest_len; clear - F1 F3 G6 Hlen; lia).
assert (LFB : length (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) = 50%nat)
  by (rewrite length_firstn, LF; clear - H50 Hcr; lia).
pose proof (cl_garr8_firstn SEGS _ fr _ 50 F4) as GFB.
assert (LU : length (our_of (c_pl cx)) = 6%nat) by (unfold our_of; rewrite length_map, length_seq; reflexivity).
pose proof (req_size_pos len ltac:(clear - Hlen0; lia)) as Hrq.
pose proof Hframe as (E1 & HdE1 & Hregs1 & _).
destruct (cl_achain B MT XM_LIB XN_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k E1 (d_A cx) HC HdE1 (Forall_inv Hregs1)
  ltac:(clear - HA1; unfold MFRAME in HA1; lia)) as (ch & Hch).
assert (Hs0z : s0Z (ms_regs ms) = d_S cx)
  by (unfold s0Z; rewrite H8; unfold w64; apply unsigned_lit_small; clear - Hlo Hhi C1; unfold LLVMF_STK in *; lia).
assert (Hraw : YK0s.ret_ok (w64 (BASE + HB_P3))) by (apply ret_ok_codeptr_v; [unfold HB_P3; clear; lia | reflexivity]).
assert (Hraw4 : 4096 <= bv_unsigned (w64 (BASE + HB_P3))).
{ unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _). pose proof (pa_base_lo (PI := PI)) as HBL.
  unfold IMG_LO, HB_P3 in *. rewrite unsigned_lit_small by (clear - HB0 HB1 HBL; lia). clear - HB0 HB1 HBL; lia. }
assert (Hch' : achain ly3 (aview SEGS (w_H W) (ms_mem ms)) (d_S cx + (d_A cx - d_S cx)) (s0Z (ms_regs ms)) ch)
  by (rewrite Hs0z; replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by (clear; lia); exact Hch).
assert (Ho16 : (d_A cx - d_S cx) mod 16 = 0) by (clear - HA2 Hal16; lia).
assert (Ho0 : d_A cx - d_S cx <= 0) by (clear - HA1; unfold MFRAME in HA1; lia).
assert (Hstk1 : 0 <= CheckSighting.TCHECK_SIGHTING_STK) by exact (proj1 h3_stk).
assert (Hstk2 : CheckSighting.TCHECK_SIGHTING_STK - (d_A cx - d_S cx) <= LLVMF_STK)
  by (clear - HA1; unfold CheckSighting.TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *; lia).
assert (Hs4 : d_obj cx OS mod 4 = 0) by (clear - Hs8; lia).
assert (Hs24 : d_obj cx OS + 24 <= 2 ^ 63) by exact Hs63.
assert (Hf50 : fr + 50 <= 2 ^ 63) by (clear - Hf63 H50 Hcr; lia).
assert (Hu6 : d_obj cx OOUR + 6 <= 2 ^ 63) by exact Hu63.
assert (Hcl : 0 <= reac_frame_clean_len_model len < 2 ^ 64) by (clear - F1 Hcr; unfold REC_MAX in F1; lia).
assert (Hcl2 : reac_frame_clean_len_model len <= 65535) by (clear - F1 Hcr; unfold REC_MAX in F1; lia).
assert (Hf50r : fr + 50 <= fr + req_size len) by (clear - Hrq H50 Hcr; lia).
assert (Hfam : amem_range fr 50)
  by exact (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len fr 50 HAR Hin (Z.le_refl fr) Hf50r).
assert (Hfra : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF fr 50)
  by exact (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len fr 50 HAR Hin (Z.le_refl fr) Hf50r).
assert (Hfshv : shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) fr 50)
  by exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len fr 50 HAR Hin (Z.le_refl fr) Hf50r
    ltac:(clear; lia)).
assert (Hssep : d_obj cx OS + 24 <= spZ (ms_regs ms) - CheckSighting.TCHECK_SIGHTING_STK \/ spZ (ms_regs ms) <= d_obj cx OS)
  by (left; rewrite Hsp; exact Hsstk).
assert (Hfsep2 : fr + 50 <= spZ (ms_regs ms) - CheckSighting.TCHECK_SIGHTING_STK \/ spZ (ms_regs ms) <= fr)
  by (left; rewrite Hsp; clear - Hfstk H50 Hcr; lia).
assert (Husep : d_obj cx OOUR + 6 <= spZ (ms_regs ms) - CheckSighting.TCHECK_SIGHTING_STK \/ spZ (ms_regs ms) <= d_obj cx OOUR)
  by (left; rewrite Hsp; exact Hustk).
assert (Hfoff50 : off_img fr 50) by (clear - Hfoff H50 Hcr; unfold off_img in *; lia).
assert (Hsf : d_obj cx OS + 24 <= fr \/ fr + 50 <= d_obj cx OS)
  by (clear - Hfsep Hrq H50 Hcr; unfold d_obj; cbn [dobj_off]; lia).
eapply SRr_bind.
{ eapply (hb_aj_call B LAWS fq W E ss ms LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md4 k CheckSighting.TCHECK_SIGHTING_STK [] 0 (d_A cx - d_S cx) (ew E 2)
    (w64 (BASE + HB_P3)) ch _ HS Hrv HJ Hsp2 eq_refl HE2 Ho16 Ho0 Hstk1 Hstk2 Hgp Htp R1 Hraw Hraw4 Hch').
  - intros HPRE1. rewrite Hpc.
    exact (TCHKS fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 [] (d_obj cx OS) fr (reac_frame_clean_len_model len)
      (d_obj cx OOUR) 1 A (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx))
      (h3_pre8 CheckSighting.TCHECK_SIGHTING_STK ly3 S3 W (ms_regs ms) (ms_mem ms) md4 ch HPRE1) Himg
      R10 R11 R12 R13 R14 Hs0 Hs4 Hs24 Hf0 Hf50 Hu0 Hu6 Hcl h3_one Hcl2 LA GA LFB GFB LU GU Hsam Hfam Huam
      Hsra Hsshv Hfra Hfshv Hura Hushv Hssep Hfsep2 Hsoff Hfoff50 Hsf Husep SA).
  - intros a (rg & Hrg & _). destruct Hrg. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hcsr2 & HJ2 & HJc & HPR & Hperm & HKEEP).
apply SRr_ret. left.
rewrite Z.add_0_r in HJ2. rewrite Hsp in HKEEP.
replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) in HJc by (clear; lia).
exact (h3_land3 cx h i n now op nb fr len v fx2 ly3 S3 W (ms_regs ms) (ms_mem ms) md4 k acc ly2 S2 W2 regs2 mem2 md2
  Hb (hb_frm0_post fq fx2 Hfq Hcsr2) HJ Hfrs Hk Hacc Hi Hn Hnow HrL R22 R23 HX Hv (ex_intro _ A (conj HsgA HroleA))
  Hsp0 Hbody HJ2 HJc HPR Hperm HKEEP).
Qed.

Lemma h3_s : forall cx h i n now op nb fr len v r W c,
  hb_R2 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len v r W c ->
  SRr SEGS W c (fun W' c' => hb_R3 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len v W' c' \/
     hb_R4 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c').
Proof.
intros cx h i n now op nb fr len v r W c HR2.
destruct HR2 as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R22 & R26 & R23 & R10) & (HX & Hv & Hr & HA) & Hsp0 & Hbody).
pose proof HX as (Hop & Hop2 & Hfrm & HspREC & HspOP & Hlen & Hnb).
pose proof HspREC as (V200 & V328 & V368 & V408).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hfrm as (F1 & F2 & F3 & F4).
pose proof (h3_fr_rng cx h n nb fr len ly3 S3 W mem3 md3 k HC Hbody Hfrm) as Rfr.
assert (EX : forall j, (j < 34)%nat -> ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) (AT_X + j) =
  nth j (cl_vals regs [w64 fr; w64 len]) (Z_to_bv 64 0)).
{ intros j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (unfold cl_vals; cbn [length];
    rewrite length_app, length_map, length_seq; cbn [length]; lia). reflexivity. }
assert (E563 : ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) 563 = w64 fr).
{ change 563%nat with (AT_X + 32)%nat. rewrite EX by lia. unfold cl_vals.
  rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq. reflexivity. }
assert (E564 : ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) 564 = w64 len).
{ change 564%nat with (AT_X + 33)%nat. rewrite EX by lia. unfold cl_vals.
  rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq. reflexivity. }
assert (E516 : ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) 516 = w64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HFx & _). exact HFx. }
assert (E60 : bv_unsigned (ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) 60) = d_A cx).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & HAx & _). unfold AT_A in HAx.
  rewrite HAx. unfold w64. apply unsigned_lit_small. exact HAr2. }
assert (E2S : bv_unsigned (ew (d_env cx E (cl_vals regs [w64 fr; w64 len])) 2) = d_S cx).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (EE & _). rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 fr; w64 len])) (rd W mem3) (d_A cx)) h3_acs).
{ unfold h3_acs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ fr);
      [cbn [sv_denot]; rewrite E563, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V368].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ len);
      [cbn [sv_denot]; rewrite E564, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; unfold REC_MAX in F1; lia | lia | exact V408]. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_P2 cl_sr (cl_vals regs [w64 fr; w64 len]) h3_acs
  [] [] (d_facts [] []) HC HdE Hregs Hflag (cl_regs_ok B cx E regs [w64 fr; w64 len] HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 fr; w64 len]) [] [] HC HdE I I) HACS (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
h3_narrow HS 516%nat. h3_narrow HS 529%nat. h3_narrow HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 fr; w64 len]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia).
  exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [w64 fr; w64 len])) (rd W mem3)) by constructor.
pose proof (cl_regs_ok B cx E regs [w64 fr; w64 len] HdE HrL HAr2) as HROK.
assert (D541 : sv_denot (d_env cx E (cl_vals regs [w64 fr; w64 len])) (SOff 541 0) = w64 r)
  by (rewrite <- R10, (HROK 10%bv); f_equal; vm_compute; reflexivity).
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + HB_P2)) with (Z_to_bv 64 (BASE + HB_P2)).
paj_run_tok RUN HS HJ SHOK cl_span. { h3_awr. }
h3_after.
psrr_branch_tok RUN BR HS SHOK cl_span.
2:{ exfalso. rewrite (h3_abort _ 541 r D541 Hr) in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK cl_span. { h3_awr. }
h3_after.
psrr_branch_tok RUN BR HS SHOK cl_span.
- rewrite (h3_bltz _ 541 r D541 Hr) in Hc. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cl_span HB_P4. { h3_awr. }
  h3_after.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msC end.
  assert (MEQ : forall x, ms_mem msC x = mem3 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end; reflexivity).
  assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs msC) r0 = getr regs r0).
  { intros r0 Hr0. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msC r0 HS), (HROK r0). cbv [In] in Hr0.
    repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    assert (HCC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msC) mdx k)
      by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]) end.
  destruct (h3_ro cx h i n now op nb fr len ly3 S3 W mem3 (ms_mem msC) _ k HCC MEQ HX Hsp0 Hbody) as (HXC & Hsp0C & HbodyC).
  apply SRr_ret. right.
  exact (h3_land4 cx h i n now op nb fr len fq ly3 S3 W _ k acc _ _ msC Hbase Hfrm0 HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HS
    eq_refl eq_refl (h3_rL cx regs (ms_regs msC) RG HrL) HXC Hsp0C HbodyC).
- rewrite (h3_bltz _ 541 r D541 Hr) in Hc. apply Z.ltb_ge in Hc.
  destruct (HA Hc) as (A & HsgA & HroleA). clear Hc.
  paj_run_tok RUN HS HJ SHOK cl_span. { h3_awr. }
  h3_after.
  psrr_branch_tok RUN BR HS SHOK cl_span.
  all: rewrite branch_ltu_U, (U_atom _ 564 len E564 ltac:(unfold REC_MAX in F1; lia)), U_lit in Hc by lia.
  1: apply Z.ltb_lt in Hc.
  2: apply Z.ltb_ge in Hc.
  all: paj_run_tok RUN HS HJ SHOK cl_span; [h3_awr|].
  all: h3_after.
  all: lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msC end.
  all: assert (MEQ : forall x, ms_mem msC x = mem3 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end; reflexivity).
  all: assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 27]%bv -> getr (ms_regs msC) r0 = getr regs r0)
    by (intros r0 Hr0; rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC r0 HS), (HROK r0); cbv [In] in Hr0;
        repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]); destruct Hr0).
  all: assert (R1 : getr (ms_regs msC) 1 = w64 (BASE + HB_P3))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 1%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        exact (codeptr_val _ 3720 HEI)).
  all: assert (R2 : getr (ms_regs msC) 2 = sv_denot (d_env cx E (cl_vals regs [w64 fr; w64 len])) (SOff 2 (d_A cx - d_S cx)))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 2%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        cbn [sv_denot]; rewrite E60, E2S; f_equal; lia).
  all: assert (R10C : getr (ms_regs msC) 10 = w64 (d_obj cx OS))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 10%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        cbn [sv_denot]; rewrite E516; unfold w64, d_obj; rewrite unsigned_lit_small by lia; reflexivity).
  all: assert (R11 : getr (ms_regs msC) 11 = w64 fr)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 11%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        cbn [sv_denot]; rewrite E563, Z.add_0_r; unfold w64; apply Z_to_bv_bv_unsigned).
  all: assert (R13 : getr (ms_regs msC) 13 = w64 (d_obj cx OOUR))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 13%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        cbn [sv_denot]; rewrite E516; unfold w64, d_obj; rewrite unsigned_lit_small by lia; reflexivity).
  all: assert (R14 : getr (ms_regs msC) 14 = w64 1)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 14%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        reflexivity).
  1: assert (R12 : getr (ms_regs msC) 12 = w64 (reac_frame_clean_len_model len))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 12%bv HS);
        lazymatch goal with |- context [sr_get ?sr ?r0] => let x := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with x end;
        cbn [sv_denot]; rewrite E564, Z.add_0_r, hb_clean_small by lia; unfold w64; apply Z_to_bv_bv_unsigned).
  2: assert (R12 : getr (ms_regs msC) 12 = w64 (reac_frame_clean_len_model len)).
  2: { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msC 12%bv HS).
       lazymatch goal with |- sv_denot _ (sr_get ?sr _) = _ =>
         replace (sr_get sr 12%bv) with (h3_bigsv 564) by (vm_compute; reflexivity) end.
       pose proof (hb_clean_eq len ltac:(unfold REC_MAX in F1; lia)) as HCE.
       rewrite (proj2 (Z.ltb_ge len 54) Hc) in HCE.
       rewrite denot_lit_U, (h3_big _ 564 len (U_atom _ 564 len E564 ltac:(unfold REC_MAX in F1; lia))), HCE.
       reflexivity. }
  all: lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    assert (HCC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msC) mdx k)
      by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]) end.
  all: destruct (h3_ro cx h i n now op nb fr len ly3 S3 W mem3 (ms_mem msC) _ k HCC MEQ HX Hsp0 Hbody)
    as (HXC & Hsp0C & HbodyC).
  all: lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
    apply (h3_call cx h i n now op nb fr len v W fq ly3 S3 msC _ k acc _ ssx Hbase Hfrm0 HJ Hfrs Hk Hacc Hi Hn Hnow
      (h3_rL cx regs (ms_regs msC) (fun r0 Hr0 => RG r0 ltac:(cbv [In] in Hr0 |- *; tauto)) HrL)
      ltac:(rewrite RG by (cbv; tauto); exact R22) ltac:(rewrite RG by (cbv; tauto); exact R23)
      HXC Hv A (h3_sg_ro cx nb fr len A W mem3 (ms_mem msC) MEQ HsgA) HroleA Hsp0C HbodyC HS eq_refl
      ltac:(cbn [ss_pc setpc]; exact pa_sigma_check_sighting) R2 E2S R1 R10C R11 R12 R13 R14) end.
Qed.

Theorem hb_L3 : hb_L3_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact h3_s. Qed.
End h.
End f.
End d.

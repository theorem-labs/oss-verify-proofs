(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the SHARED FACTS of pj_free's image-B walk segments (lib/B/Prog/pj_free_defs.v): stack
   numbers, ledger blocks' bounds, the chunks of a seated symbolic state, memory keeps.
   proves no function (kind: walk glue).
   Numerals: 128 / 16416 (DERIVED: pi_frame F_pj_free and STK_fuzz_free at prh_img_B, by computation); 8 / 56
   (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Existing Instance prh_img_B.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the stack numbers at prh_img_B ---- *)
Lemma pfg_stk : forall n, @STK_pj_free prh_img_B n = 128 * Z.of_nat (S n) + 16416.
Proof.
intros n. unfold STK_pj_free.
replace (pi_frame F_pj_free) with 128 by (vm_compute; reflexivity).
lazymatch goal with |- context [zmaxl ?l] => replace (zmaxl l) with 16416 by (vm_compute; reflexivity) end. lia.
Qed.
Lemma pfg_stk_ff : @STK_fuzz_free prh_img_B = 16416.
Proof. vm_compute. reflexivity. Qed.

(* ---- bv bookkeeping ---- *)
Lemma pfg_w64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- a harness block of the ledger: its bounds ---- *)
Lemma pfg_lam_blk : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ 4096 + cf_head <= a /\ a + k <= YM05.alloc_ceiling /\ a mod 16 = 0 /\
  In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLd Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLd Hin) as (Hk & Hab & Hhp & Ha16 & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hkc : 0 <= k + cf_head) by lia.
pose proof (req_size_pos (k + cf_head) Hkc) as [_ Hrq].
repeat split; first [assumption | lia].
Qed.

(* ---- views: a byte kept in the view keeps its byte, and a word / value ---- *)
Lemma pfg_val_keep : forall (W W' : world SEGS) m m' a (n : nat) v, val_mem SEGS (rdW W m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W' m') a n v.
Proof.
intros W W' m m' a n v Hv Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)).
- exact (Hv k Hkn).
- apply Hk. lia.
Qed.
Lemma pfg_u64_keep : forall (W W' : world SEGS) m m' a v, rd_u64 SEGS (rdW W m) a v ->
  (forall x, a <= x < a + 8 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  rd_u64 SEGS (rdW W' m') a v.
Proof.
intros W W' m m' a v (Hr & Hv) Hk. split; [exact Hr|]. apply (pfg_val_keep W W' m m' a 8 v Hv). intros x Hx. apply Hk.
cbn in Hx. lia.
Qed.
(* two memories agree on the bytes a view keeps, and a writable byte stays writable when the memory grows *)
Lemma pfg_agree : forall (W W' : world SEGS) m m' (X : Z -> Prop),
  mem_grows (rdW W m) (rdW W' m') ->
  (forall x, X x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  pj_agreeR SEGS (rdW W m) (rdW W' m') X.
Proof.
intros W W' m m' X MG Hk x Hx. split.
- apply (mbyte_of_aview SEGS (w_H W) (w_H W') m m' x). exact (Hk x Hx).
- intros Hw. exact (writable_at_grows SEGS _ _ x MG Hw).
Qed.

(* ---- a chunk of a seated symbolic state and the value it states (pj_parse_seg_ent.v pje_cv / pje_val's form) ---- *)
Definition pfg_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pfg_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pfg_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pfg_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pfg_val : forall E ss ms j off (w : N) e v b a, st_ok_pi SEGS VAL E ss ms ->
  pfg_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pfg_cv_ok E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the memory only grows when every present byte stays present *)
Lemma pfg_grows_of_apresent : forall (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Ehx; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
(* the sum of two U values *)
Lemma pfg_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
(* a shift right by 3, and the ASan cell address (x >> 3) + shadow offset *)
Lemma pfg_U_srl3 : forall E x, U E (SAlu ALU_SRL x (SLit 3)) = U E x / 8.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. pose proof (U_range E x) as R. unfold M64 in R.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ (U E x)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Lemma pfg_U_cell : forall E x bx xv, U E x = xv -> U E bx = SHADOW_OFF -> 0 <= xv < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) bx) = xv / 8 + SHADOW_OFF.
Proof.
intros E x bx xv Hx Hb Hr. rewrite pfg_U_add, pfg_U_srl3, Hx, Hb.
assert (0 <= xv / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold SHADOW_OFF in *. apply Z.mod_small. lia.
Qed.
(* a register whose symbolic value has a known U *)
Lemma pfg_reg_of_U : forall E e (w : word) z, w = sv_denot E e -> U E e = z -> w = Z_to_bv 64 z.
Proof. intros E e w z -> <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the shadow hull of an application range below kHighMemEnd lies in [kLowMemEnd, kHighShadowEnd) *)
Lemma pfg_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.
(* the engine's 56 * i, and an address plus it *)
Lemma pfg_U_mul56 : forall E x i, U E x = i -> 0 <= i < 2 ^ 42 -> U E (SMd M_MUL x (SLit 56)) = 56 * i.
Proof.
intros E x i Hx Hi. rewrite U_SMd, U_SLit, Hx. cbn [zmd_raw]. change (zcanon 56) with 56.
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pfg_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small; [lia|]. change (2 ^ 64) with (2 * 2 ^ 63).
replace (2 ^ 64 / 2) with (2 ^ 63) by reflexivity. lia.
Qed.
(* UBSan's product check on 56 * i (+0xd4 .. +0xe0): mulh, srai 63, xor, sltu: 0 for a small i *)
Lemma pfg_U_mulchk : forall E x i, U E x = i -> 0 <= i < 2 ^ 42 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH x (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL x (SLit 56)) (SLit 63)))) = 0.
Proof.
intros E x i Hx Hi.
assert (Hm : U E (SMd M_MUL x (SLit 56)) = 56 * i) by (apply pfg_U_mul56; assumption).
assert (Hh : U E (SMd M_MULH x (SLit 56)) = 0).
{ rewrite U_SMd, U_SLit, Hx. cbn [zmd_raw]. change (zcanon 56) with 56.
  rewrite (pfg_swrap_small i) by lia. rewrite (pfg_swrap_small 56) by lia.
  rewrite Z.shiftr_div_pow2 by lia. cbn [Z.of_N]. rewrite Z.div_small by lia. reflexivity. }
assert (Hs : U E (SAlu ALU_SRA (SMd M_MUL x (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu, U_SLit, Hm. cbn [zalu_raw]. change (Z.land (zcanon 63) 63) with 63.
  rewrite (pfg_swrap_small (56 * i)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity. }
rewrite U_SAlu, U_SLit, U_SAlu, Hh, Hs. reflexivity.
Qed.
End g.
(* the register's value from a seated state, its symbolic value computed *)
Ltac pfg_reg HS r R :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    lazymatch type of R with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R end
  end.
(* the image word at a listing offset and its decoding (pj_parse_seg_c2ref.v pjr_fd's form) *)
Ltac pfg_fd k Hl Hd :=
  let r := eval vm_compute in
    (clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) in
  lazymatch r with
  | Some ?w =>
    assert (Hl : clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k) = Some w)
      by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "pfg_fd: no image word at offset" k
  end.
(* one concrete `jal` at a listing offset k of image B (pj_parse_seg_c2ref.v pjr_step_jal), over any world relation R
   (the walk's is wle' SEGS RZ_cf; a step does not change the world, YSRrG.SRrG_step) *)
Section j. Context {rc : YM05.RunCeil}.
Lemma pfg_step_jal : forall (fy : YK11.FPState)
  (R : world (@pa_segs _ B_prog_listing PI_prog_B) -> world (@pa_segs _ B_prog_listing PI_prog_B) -> Prop)
  (W : world (@pa_segs _ B_prog_listing PI_prog_B)) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (Q : world (@pa_segs _ B_prog_listing PI_prog_B) -> config -> Prop) (k : Z) w
  (rd : bv 5) (imm : bv 21) (rd' : bv 5) (ra pc' : word),
  clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) 4 = ra ->
  btgt (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) (bv_signed imm) = pc' ->
  (forall X, SRrG (@pa_segs _ B_prog_listing PI_prog_B) R W (mkCfg (@YK11.mkst fy (regupd regs rd' ra) pc' mem
     (YK11.seg_rom (@pa_segs _ B_prog_listing PI_prog_B))) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG (@pa_segs _ B_prog_listing PI_prog_B) R W (mkCfg (@YK11.mkst fy regs
    (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) mem (YK11.seg_rom (@pa_segs _ B_prog_listing PI_prog_B))) md) Q.
Proof.
intros fy R W regs mem md Q k w rd imm rd' ra pc' Hl Hd Hrd Erd Era Hpc HK. subst rd' ra pc'.
eapply (SRrG_step _ R (@pa_wx _ B_prog_listing PI_prog_B) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fy)).
  rewrite (step_jal_link (fx := fy) _ regs _ (mrestrict (w_H W) mem) _
    (Z_to_bv 32 w) rd imm (pa_fetch_ok (PI := PI_prog_B) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fy)). apply HK.
Qed.
End j.

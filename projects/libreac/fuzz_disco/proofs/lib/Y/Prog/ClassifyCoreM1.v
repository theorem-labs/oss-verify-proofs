(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1529 of its 1562 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ClassifyCoreM1.v, with its module paths, module names and numbers changed; 99 of its 1260 lines of code are new or changed and 401 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YK0w.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition m1_Bx : sv := SOff 21 0.
Definition m1_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition m1_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 32 8 16 [YP09.mkChunk 24 (CVal 8 (SOff 24 0))].
Definition m1_q : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0 20 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 10 0))].
Definition m1_lk : YP09.region := YP09.mkRegion (Some 23%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition m1_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0)] [] [].
Definition ss_R1 : sstate := mkSS PC_R1 sr_atoms [m1_stk; m1_q] None m1_facts.

Lemma m1_ps_bytes : forall n fr,
  nth 0 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = Z_to_bv 8 (fst (RcParse.ctrlparse n fr)) /\
  nth 1 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 2 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 3 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z.
Proof.
intros n fr. unfold RcParse.ctrlparse. destruct (RcParse.cp_hdr n fr); cbn [fst snd].
- unfold RcParse.cp_struct. cbn [nth app].
  destruct (RcParse.cp_bcast fr); repeat split; reflexivity.
- cbn [nth repeat]. repeat split; reflexivity.
Qed.

Lemma m1_nth_bytes : forall l j, nth j (cls_bytes l) 0 = bv_unsigned (nth j l RcParse.cp_z).
Proof.
intros l. unfold cls_bytes. induction l as [|b l IH]; intros [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

Lemma m1_le4 : forall v k, 0 <= v < 256 -> (k < 4)%nat ->
  Z_to_bv 8 (YO0f.le_byte v 4 k) = Z_to_bv 8 (if (k =? 0)%nat then v else 0).
Proof.
intros v k Hv Hk. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small v) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Nat.eqb].
- change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r, Z.mod_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.div_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 3)) with 16777216. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma m1_vm_mod : forall segs (m : word -> option byte) a n v,
  YI04.val_mem segs m a n v -> YI04.val_mem segs m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros segs m a n v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma m1_ble4 : forall b0 b1 b2 b3 : byte,
  bytes_le_to_Z [b0; b1; b2; b3] =
  bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)).
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
rewrite (YK0w.lor_shiftl8 (bv_unsigned b2)) by lia.
rewrite (YK0w.lor_shiftl8 (bv_unsigned b1)) by lia.
rewrite (YK0w.lor_shiftl8 (bv_unsigned b0)) by lia.
reflexivity.
Qed.

Lemma m1_le4_byte : forall B0 B1 B2 B3, 0 <= B0 < 256 -> 0 <= B1 < 256 -> 0 <= B2 < 256 -> 0 <= B3 < 256 ->
  YO0f.le_byte (B0 + 256 * (B1 + 256 * (B2 + 256 * B3))) 4 0 = B0 /\
  YO0f.le_byte (B0 + 256 * (B1 + 256 * (B2 + 256 * B3))) 4 1 = B1 /\
  YO0f.le_byte (B0 + 256 * (B1 + 256 * (B2 + 256 * B3))) 4 2 = B2 /\
  YO0f.le_byte (B0 + 256 * (B1 + 256 * (B2 + 256 * B3))) 4 3 = B3.
Proof.
intros B0 B1 B2 B3 H0 H1 H2 H3. unfold YO0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 0)) with 1.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 3)) with 16777216.
repeat split; lia.
Qed.

Lemma m1_S1_bounds : forall SP, SP mod 16 = 0 ->
  SP - 176 <= cls_S1 SP <= SP - 160 /\ cls_S1 SP mod 32 = 0 /\ cls_S1 SP mod 16 = 0.
Proof. intros SP H. unfold cls_S1. lia. Qed.

Lemma m1_and3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v mod 4 = 0 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 3)) = 0.
Proof.
intros E n v H Hv Hm. rewrite U_SAlu, (U_atom E n v H Hv), U_SLit. cbn [zalu_raw].
change (zcanon 3) with 3. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
change (2 ^ 2) with 4. rewrite Hm. reflexivity.
Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma m1_beq : forall (a b : list byte) ka kb,
  (ka + 6 <= length a)%nat -> (kb + 6 <= length b)%nat ->
  (CtrlParsed.bytes_eqb (CtrlParsed.fld a ka 6) (CtrlParsed.fld b kb 6) = true <->
   forall i, (i < 6)%nat -> bv_unsigned (nth (ka + i) a RcParse.cp_z) = bv_unsigned (nth (kb + i) b RcParse.cp_z)).
Proof.
intros a b ka kb Ha Hb.
assert (NF : forall (l : list byte) k i, (k + 6 <= length l)%nat -> (i < 6)%nat ->
  nth i (map (fun x : byte => bv_unsigned x) (CtrlParsed.fld l k 6)) 0 = bv_unsigned (nth (k + i) l RcParse.cp_z)).
{ intros l k i Hl Hi. change (map (fun x : byte => bv_unsigned x) (CtrlParsed.fld l k 6)) with (cls_bytes (CtrlParsed.fld l k 6)).
  rewrite m1_nth_bytes. unfold CtrlParsed.fld. rewrite nth_firstn.
  replace (i <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn. reflexivity. }
assert (LF : forall (l : list byte) k, (k + 6 <= length l)%nat ->
  length (map (fun x : byte => bv_unsigned x) (CtrlParsed.fld l k 6)) = 6%nat).
{ intros l k Hl. rewrite length_map. unfold CtrlParsed.fld. rewrite length_firstn, length_skipn. lia. }
unfold CtrlParsed.bytes_eqb.
destruct (list_eq_dec Z.eq_dec (map (fun x : byte => bv_unsigned x) (CtrlParsed.fld a ka 6))
  (map (fun x : byte => bv_unsigned x) (CtrlParsed.fld b kb 6))) as [E|E]; split; intros H.
- intros i Hi. rewrite <- (NF a ka i Ha Hi), <- (NF b kb i Hb Hi), E. reflexivity.
- reflexivity.
- discriminate.
- exfalso. apply E. apply (nth_ext _ _ 0 0); [rewrite (LF a ka Ha), (LF b kb Hb); reflexivity|].
  intros i Hi. rewrite (LF a ka Ha) in Hi. rewrite (NF a ka i Ha Hi), (NF b kb i Hb Hi). apply H. exact Hi.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition m1_lv (cx : ccx) : Z := match x_L cx with Some Lb => disco_classify_c.lv Lb | None => 0 end.
Definition m1_extra (cx : ccx) : list word := map (Z_to_bv 64) [m1_lv cx].

Lemma m1_vm4 : forall (m : word -> option byte) p l j v, garr8 SEGS m p l -> (j + 4 <= length l)%nat ->
  nth j l 0 = v -> nth (j + 1) l 0 = 0 -> nth (j + 2) l 0 = 0 -> nth (j + 3) l 0 = 0 ->
  val_mem SEGS m (p + Z.of_nat j) 4 v.
Proof.
intros m p l j v H Hl H0 H1 H2 H3 k Hk.
assert (Hv : 0 <= v < 256) by (subst v; apply (H j); lia).
replace (p + Z.of_nat j + Z.of_nat k) with (p + Z.of_nat (j + k)) by lia.
rewrite (garr8_mbyte SEGS m p l (j + k) H) by lia.
rewrite (m1_le4 v k Hv Hk).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Nat.eqb].
- rewrite Nat.add_0_r, H0. reflexivity.
- rewrite H1. reflexivity.
- rewrite H2. reflexivity.
- rewrite H3. reflexivity.
Qed.

Lemma m1_garr8_kept : forall H (m m' : word -> option byte) p l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m' (p + j) = aview SEGS H m (p + j)) ->
  garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H m') p l.
Proof.
intros H m m' p l HA HG. apply (garr8_frame SEGS _ _ p l HG).
intros a Ha. replace a with (p + (a - p)) by lia. apply (mbyte_of_aview SEGS). apply HA. lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.

Lemma m1_nums : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  cSP cx mod 16 = 0 /\ cSP cx - 176 <= cS1 cx <= cSP cx - 160 /\ cS1 cx mod 32 = 0 /\
  alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx - x_STK cx <= cSP cx - CLS_STK /\
  cSP cx <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  (forall a, x_sp0 cx - x_STK cx <= a < x_sp0 cx -> apresent (w_H W3) mem3 a) /\
  4096 <= cF cx fpos /\ cF cx fpos + 256 <= alloc_ceiling /\ cF cx fpos mod 32 = 0 /\
  CLS_STK = 8512 /\ ESTACK = 4096.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut.
pose proof (NOW cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as Hnow. cbv zeta in Hnow.
destruct Hnow as ((HF4 & HFc & HFal & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
pose proof Hcut as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (CS : CLS_STK = 8512) by reflexivity.
assert (HSP : cSP cx mod 16 = 0) by exact Hal.
assert (HL : x_sp0 cx - x_STK cx <= cSP cx - CLS_STK) by exact Hlo.
assert (HH : cSP cx <= x_sp0 cx) by exact Hhi.
pose proof (Z.div_mod (cSP cx - 160) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (cSP cx - 160) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (cSP cx) 16 ltac:(lia)) as D2.
unfold cS1, cls_S1.
split; [exact HSP|]. split; [split; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
split; [lia|]. split; [exact HL|]. split; [exact HH|]. split; [lia|].
split; [exact Hpres|]. split; [exact HF4|]. split; [exact HFc|]. split; [exact HFal|].
split; [exact CS | reflexivity].
Qed.


Lemma m1_bv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Lemma m1_entry : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_at_R1 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  st_ok_pi (fx := x_fq cx) SEGS VAL (Eimg (Ereg regs3 (m1_extra cx))) ss_R1
    (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_R1)) mem3 (seg_rom SEGS))).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut. unfold cls_at_R1 in Hcut. cbv zeta in Hcut.
destruct (m1_nums cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut)
  as (Hsp16 & HS1 & HS1al & Hceil & Hstk & Hsp & H47 & Hpres & HF4 & HFc & HFal & CS & ES).
pose proof Hcut as (HJ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV & Hspill
  & Vo & Vf & VF & _ & _ & _ & _ & HPS & _).
destruct HPS as (HPSl & HPS).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & HFBl & HUl & HOBl & _).
apply Forall_cons_iff in HRV as [Ra0 HRV]. apply Forall_cons_iff in HRV as [Rs5 HRV].
apply Forall_cons_iff in HRV as [Rs6 HRV]. apply Forall_cons_iff in HRV as [Rs7 HRV].
apply Forall_cons_iff in HRV as [Rs8 HRV]. apply Forall_cons_iff in HRV as [Rs9 HRV].
apply Forall_cons_iff in HRV as [Rs10 _].
cbn [fst snd] in Ra0, Rs5, Rs6, Rs7, Rs8, Rs9, Rs10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (RcParse.ctrlparse_kind_range (x_len cx) (x_FB cx)) as HKr.
destruct (m1_ps_bytes (x_len cx) (x_FB cx)) as (B0 & B1 & B2 & B3).
set (E := Eimg (Ereg regs3 (m1_extra cx))).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U2 : bv_unsigned (ew E 2) = cS1 cx)
  by (rewrite (EW 2%nat 2%bv eq_refl), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = cS1 cx)
  by (rewrite (EW 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U22 : bv_unsigned (ew E 22) = cF cx fpos + 32)
  by (rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl), Rs6; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U21 : bv_unsigned (ew E 21) = SB)
  by (rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl), Rs5; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (HK0 : nth 0 (cls_bytes (cPS cx)) 0 = cK cx).
{ rewrite m1_nth_bytes. unfold cPS. rewrite B0. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. unfold cK, disco_classify_c.dkind. apply Z.mod_small. lia. }
assert (HPSb : length (cls_bytes (cPS cx)) = 36%nat) by (unfold cls_bytes; rewrite length_map; exact HPSl).
rewrite restrict_mkst_fx. unfold ss_R1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, m1_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * constructor; [|constructor].
      pose proof (Z.mod_pos_bound (x_f cx) (2 ^ 64) ltac:(lia)) as Mf.
      apply (chunk_ok_val SEGS E _ (cS1 cx) 24 8 (SOff 24 0) (x_f cx mod 2 ^ 64));
        [cbn [sv_denot]; rewrite (EW 24%nat (Z_to_bv 5 24) eq_refl), Rs8, Z.add_0_r, Z_to_bv_bv_unsigned;
         unfold w64; rewrite m1_bv_mod; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. pose proof (m1_vm_mod SEGS _ _ 8 _ Vf) as Vf'.
      change (8 * Z.of_nat 8) with 64 in Vf'. exact Vf'.
  + unfold region_ok, m1_q. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (cF cx fpos + 32) 0 4 (SOff 10 0) (cK cx));
      [cbn [sv_denot]; rewrite (EW 10%nat (Z_to_bv 5 10) eq_refl), Ra0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold cK, disco_classify_c.dkind in *; zside | zside |].
    change (N.to_nat 4) with 4%nat.
    pose proof (m1_vm4 _ _ _ 0 (cK cx) HPS ltac:(lia) HK0) as V.
    rewrite Z.add_0_r. rewrite Z.add_0_r in V. apply V.
    * cbn [Nat.add]. rewrite m1_nth_bytes. unfold cPS. rewrite B1. reflexivity.
    * cbn [Nat.add]. rewrite m1_nth_bytes. unfold cPS. rewrite B2. reflexivity.
    * cbn [Nat.add]. rewrite m1_nth_bytes. unfold cPS. rewrite B3. reflexivity.
- apply pairwise_disjoint_of_extents. unfold m1_stk, m1_q, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold m1_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  assert (HS16 : cS1 cx mod 16 = 0).
  { unfold cS1, cls_S1. replace (32 * ((cSP cx - 160) / 32)) with ((2 * ((cSP cx - 160) / 32)) * 16) by ring.
    apply Z.mod_mul. lia. }
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U2; change (2 ^ 4) with 16; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 4) with 16; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U21; rewrite Z.pow_0_r, Z.mod_1_r; unfold SB; lia|].
  exact I.
Qed.

Lemma m1_cut : forall cx fpos pc RV O3 PS LS W3 ly3 S3 regs3 mem3 md3 pc' RV' O4 PS' LS' regs4 mem4 md4,
  cls_pre B cx ->
  cls_cut B cx fpos pc RV O3 (x_L cx) PAT_A PS LS W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cS1 cx - 2 * ESTACK <= a < cS1 cx + 16) -> ~ (x_o cx <= a < x_o cx + 24) ->
     aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = getr regs3 19 -> getr regs4 20 = getr regs3 20 -> getr regs4 27 = getr regs3 27 ->
  Forall (fun rv => getr regs4 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV' ->
  (LS' = true -> val_mem SEGS (mrestrict (w_H W3) mem4) (cS1 cx + 8) 8 (x_len cx)) ->
  (match PS' with Some P => PS = Some P | None => True end) ->
  length O4 = 24%nat -> garr8 SEGS (mrestrict (w_H W3) mem4) (x_o cx) (cls_bytes O4) ->
  cls_cut B cx fpos pc' RV' O4 (x_L cx) PAT_A PS' LS' W3 ly3 S3 regs4 mem4 md4.
Proof.
intros cx fpos pc RV O3 PS LS W3 ly3 S3 regs3 mem3 md3 pc' RV' O4 PS' LS' regs4 mem4 md4
  Hpre Hcut HJ4 HK HP G2 G3 G4 G8 G9 G18 G19 G20 G27 HRV' HLS' HPS' HO4l HO4.
destruct (m1_nums cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut)
  as (Hsp16 & HS1 & HS1al & Hceil & Hstk & Hsp & H47 & Hpres & HF4 & HFc & HFal & CS & ES).
pose proof (NOW cx fpos pc RV O3 (x_L cx) PAT_A PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as Hnow.
cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & ((HOa0 & HOa47 & _ & _ & HOsh) & _ & HOF & HOsp) & HO4096 & HOc & _ & HLok).
pose proof Hcut as (HJ3 & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27
  & HRV & Hspill & Vo & Vf & VF & HLS & HSl & HSHP & VFL & HPS & HO3l & HO3 & HL3).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLd).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod (cF cx fpos) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (cF cx fpos) 8 ltac:(lia)) as MF.
set (Wr := fun a => (cS1 cx - 2 * ESTACK <= a < cS1 cx + 16) \/ (x_o cx <= a < x_o cx + 24)).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw. apply HK; [exact Ha | intros X; apply Hw; left; exact X | intros X; apply Hw; right; exact X]. }
assert (Hkept4 : tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem4 (cSP cx) (x_lk cx) (x_o cx) (x_L cx)).
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 mem4 Wr Hpre (proj1 HJ3) Hfr Hnin Hperm Hfa Hfl Hkept KA HP).
  intros a [Ha|Ha]; [left; lia | right; left; unfold cls_wr; left; exact Ha]. }
assert (KS1 : forall a, cS1 cx + 16 <= a < 2 ^ 47 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha; apply HK; lia).
assert (KLO : forall a, 0 <= a < alloc_ceiling -> ~ (x_o cx <= a < x_o cx + 24) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a) by (intros a Ha Hn; apply HK; lia).
unfold cls_cut. cbv zeta.
split; [exact HJ4|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|]. split; [exact Hkept4|].
split; [rewrite G2; exact R2|]. split; [rewrite G3; exact R3|]. split; [rewrite G4; exact R4|].
split; [rewrite G8; exact R8|]. split; [rewrite G9; exact R9|]. split; [rewrite G18; exact R18|].
split; [rewrite G19; exact R19|]. split; [rewrite G20; exact R20|]. split; [rewrite G27; exact R27|].
split; [exact HRV'|].
split.
{ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) Hspill p Hp) as V.
  assert (Hpr : -104 <= snd p <= -8)
    by (unfold cls_spills in Hp; repeat (destruct Hp as [<-|Hp]; [cbn; lia|]); destruct Hp).
  refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ V). intros k Hk. apply KS1. cbn in Hk. lia. }
split; [refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ Vo); intros k Hk; apply KS1; cbn in Hk; lia|].
split; [refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ Vf); intros k Hk; apply KS1; cbn in Hk; lia|].
split; [refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ VF); intros k Hk; apply KS1; cbn in Hk; lia|].
split; [exact HLS'|].
split; [exact HSl|].
split.
{ refine (m1_garr8_kept _ _ _ _ _ _ HSHP). intros j Hj. rewrite HSl in Hj. apply KLO;
    [unfold SHADOW_OFF; lia | unfold SHADOW_OFF, kLowShadowBeg in *; lia]. }
split.
{ refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ VFL). intros k Hk. apply KLO; cbn in Hk; lia. }
split.
{ destruct PS' as [P|]; [|exact I]. subst PS. destruct HPS as (HPl & HPg). split; [exact HPl|].
  refine (m1_garr8_kept _ _ _ _ _ _ HPg). intros j Hj. unfold cls_bytes in Hj. rewrite length_map, HPl in Hj.
  apply KLO; lia. }
split; [exact HO4l|]. split; [exact HO4|].
destruct (x_L cx) as [Lb|]; [|exact I].
destruct HL3 as (HLl & HLg). destruct HLok as ((_ & _ & _ & _) & HLk4 & HLkc & _).
destruct HLd as (HLo & _ & _). split; [exact HLl|].
refine (m1_garr8_kept _ _ _ _ _ _ HLg). intros j Hj. unfold cls_bytes in Hj. rewrite length_map, HLl in Hj.
apply KLO; lia.
Qed.

Lemma m1_aview_garr8 : forall H (m : word -> option byte) p l j,
  garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j HG Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. destruct (HG j Hj) as [_ R]. change (bv_modulus 8) with 256.
apply Z.mod_small. lia.
Qed.

Lemma m1_cmp6 : forall H (m : word -> option byte) pa pb (la lb : list byte) ka kb,
  garr8 SEGS (mrestrict H m) pa (cls_bytes la) -> garr8 SEGS (mrestrict H m) pb (cls_bytes lb) ->
  (ka + 6 <= length la)%nat -> (kb + 6 <= length lb)%nat ->
  ((forall i, 0 <= i < 6 -> aview SEGS H m (pa + Z.of_nat ka + i) = aview SEGS H m (pb + Z.of_nat kb + i)) <->
   CtrlParsed.bytes_eqb (CtrlParsed.fld la ka 6) (CtrlParsed.fld lb kb 6) = true).
Proof.
intros H m pa pb la lb ka kb Ga Gb Ha Hb. rewrite (m1_beq la lb ka kb Ha Hb).
assert (La : length (cls_bytes la) = length la) by (unfold cls_bytes; apply length_map).
assert (Lb : length (cls_bytes lb) = length lb) by (unfold cls_bytes; apply length_map).
assert (A : forall i, (i < 6)%nat ->
  aview SEGS H m (pa + Z.of_nat ka + Z.of_nat i) = Some (bv_unsigned (nth (ka + i) la RcParse.cp_z)) /\
  aview SEGS H m (pb + Z.of_nat kb + Z.of_nat i) = Some (bv_unsigned (nth (kb + i) lb RcParse.cp_z))).
{ intros i Hi. rewrite <- !m1_nth_bytes.
  replace (pa + Z.of_nat ka + Z.of_nat i) with (pa + Z.of_nat (ka + i)) by lia.
  replace (pb + Z.of_nat kb + Z.of_nat i) with (pb + Z.of_nat (kb + i)) by lia.
  split; apply m1_aview_garr8; first [exact Ga | exact Gb | lia]. }
split; intros X i Hi.
- destruct (A i Hi) as [A1 A2]. pose proof (X (Z.of_nat i) ltac:(lia)) as Y. rewrite A1, A2 in Y.
  injection Y as Y. exact Y.
- destruct (A (Z.to_nat i) ltac:(lia)) as [A1 A2]. rewrite Z2Nat.id in A1, A2 by lia. rewrite A1, A2.
  f_equal. apply X. lia.
Qed.

Lemma m1_fld_src : forall cx, cK cx <> 0 -> length (x_FB cx) = 50%nat ->
  CtrlParsed.fld (cPS cx) 4 6 = disco_classify_c.src (x_FB cx).
Proof.
intros cx Hk HL. unfold cK, disco_classify_c.dkind in Hk.
destruct (RcParse.ctrlparse_fields (x_len cx) (x_FB cx) Hk) as (F1 & _).
assert (Lp : length (cPS cx) = 36%nat) by apply RcParse.ctrlparse_length.
apply (nth_ext _ _ RcParse.cp_z RcParse.cp_z).
- unfold disco_classify_c.src, CtrlParsed.fld. rewrite !length_firstn, !length_skipn, Lp, HL. reflexivity.
- intros n Hn. unfold CtrlParsed.fld in Hn. rewrite length_firstn, length_skipn, Lp in Hn.
  unfold disco_classify_c.src, CtrlParsed.fld. rewrite !nth_firstn.
  replace (n <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite !nth_skipn. unfold cPS. rewrite (F1 n ltac:(lia)). reflexivity.
Qed.

Lemma m1_mod_k0 : forall cx, cK cx = 0 -> cRet cx = -1 /\ cOut cx = x_OB cx /\ cLock cx = x_L cx.
Proof.
intros cx H. unfold cK in H. unfold cRet, cOut, cLock, disco_classify_c.cm_ret, disco_classify_c.cm_out,
  disco_classify_c.cm_lock, disco_classify_c.classify_model. cbv zeta. rewrite H. cbn. repeat split.
Qed.

Lemma m1_mod_eq : forall cx, cK cx <> 0 -> CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = true ->
  cRet cx = -1 /\ cOut cx = x_OB cx /\ cLock cx = x_L cx.
Proof.
intros cx H HE. unfold cK in H. unfold cRet, cOut, cLock, disco_classify_c.cm_ret, disco_classify_c.cm_out,
  disco_classify_c.cm_lock, disco_classify_c.classify_model. cbv zeta.
rewrite (proj2 (Z.eqb_neq _ _) H), HE. cbn. repeat split.
Qed.

Lemma m1_mod_none : forall cx, cK cx = 1 -> CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false ->
  x_L cx = None -> cRet cx = 0 /\ cLock cx = None.
Proof.
intros cx H HE HL. unfold cK in H. unfold cRet, cLock, disco_classify_c.cm_ret,
  disco_classify_c.cm_lock, disco_classify_c.classify_model. cbv zeta.
rewrite H, HE, HL. cbn. split; reflexivity.
Qed.

Lemma m1_mod_rej : forall cx Lb, cK cx = 1 -> CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false ->
  x_L cx = Some Lb -> disco_classify_c.lv Lb <> 0 ->
  CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src (x_FB cx)) = false ->
  cRet cx = -1 /\ cOut cx = x_OB cx /\ cLock cx = x_L cx.
Proof.
intros cx Lb H HE HL Hv HM. unfold cK in H. unfold cRet, cOut, cLock, disco_classify_c.cm_ret,
  disco_classify_c.cm_out, disco_classify_c.cm_lock, disco_classify_c.classify_model. cbv zeta.
rewrite H, HE, HL, HM. rewrite (proj2 (Z.eqb_neq _ _) Hv). cbn. repeat split.
Qed.

Lemma m1_mod_acc : forall cx Lb, cK cx = 1 -> CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false ->
  x_L cx = Some Lb ->
  (disco_classify_c.lv Lb = 0 \/ CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src (x_FB cx)) = true) ->
  cRet cx = 0 /\ cLock cx = x_L cx.
Proof.
intros cx Lb H HE HL Hv. unfold cK in H. unfold cRet, cLock, disco_classify_c.cm_ret,
  disco_classify_c.cm_lock, disco_classify_c.classify_model. cbv zeta.
rewrite H, HE, HL. destruct Hv as [Hv|HM]; [rewrite Hv | rewrite HM]; cbn;
  [split; reflexivity|]. rewrite andb_false_r. cbn. split; reflexivity.
Qed.

Definition m1_kept0 (cx : ccx) (W3 : world SEGS) (mem3 m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cS1 cx - 2 * ESTACK <= a < cS1 cx + 16) ->
     aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a) /\
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m a).

Definition m1_kept1 (cx : ccx) (W3 : world SEGS) (mem3 m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cS1 cx - 2 * ESTACK <= a < cS1 cx + 16) -> ~ (x_o cx <= a < x_o cx + 24) ->
     aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a) /\
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m a).

Definition m1_rd6 (cx : ccx) (W3 : world SEGS) (mem3 : word -> option byte) (p : Z) : Prop :=
  0 <= p /\ p + 6 <= 2 ^ 47 /\ amem_range p 6 /\ (p + 6 <= cS1 cx - 2 * ESTACK \/ cSP cx <= p) /\
  (p + 6 <= x_o cx \/ x_o cx + 24 <= p) /\
  (forall a, p <= a < p + 6 -> apresent (w_H W3) mem3 a) /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF p 6 /\ shadow_hull_vis (aview SEGS (w_H W3) mem3) p 6.

Lemma m1_kept01 : forall cx W3 mem3 m, m1_kept0 cx W3 mem3 m -> m1_kept1 cx W3 mem3 m.
Proof. intros cx W3 mem3 m [K P]. split; [intros a Ha Hs _; apply K; assumption | exact P]. Qed.

Lemma m1_shadow_band : forall p n s, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> kLowShadowBeg <= s < kHighMemBeg.
Proof.
intros p n s Hp Hn Hpn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold shadow_addr in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold SHADOW_OFF, kLowShadowBeg in *.
lia.
Qed.

Lemma m1_rd_band : forall p n x, 0 <= p -> p + n <= 2 ^ 47 -> p <= x < p + n ->
  kLowShadowBeg <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros p n x Hp Hpn Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg in *.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1. lia.
Qed.

Lemma m1_ra_kept : forall H (m m' : word -> option byte) p n,
  0 <= p -> p + n <= 2 ^ 47 ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS H m' a = aview SEGS H m a) ->
  range_addressable (aview SEGS H m) SHADOW_OFF p n -> range_addressable (aview SEGS H m') SHADOW_OFF p n.
Proof.
intros H m m' p n Hp Hpn K R. apply (range_addressable_agree (aview SEGS H m) _ SHADOW_OFF p n); [|exact R].
intros x Hx. apply K. exact (m1_rd_band p n x Hp Hpn Hx).
Qed.

Lemma m1_hull_kept : forall H (m m' : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n <= 2 ^ 47 ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS H m' a = aview SEGS H m a) ->
  shadow_hull_vis (aview SEGS H m) p n -> shadow_hull_vis (aview SEGS H m') p n.
Proof.
intros H m m' p n Hp Hn Hpn K V s Hs. rewrite K by exact (m1_shadow_band p n s Hp Hn Hpn Hs). apply V. exact Hs.
Qed.

Lemma m1_ra_sub : forall rd B0 a n a' n', range_addressable rd B0 a n -> a <= a' -> a' + n' <= a + n ->
  range_addressable rd B0 a' n'.
Proof. intros rd B0 a n a' n' R H1 H2 x Hx. apply R. lia. Qed.

Lemma m1_hull_sub : forall rd p n p' n', shadow_hull_vis rd p n -> p <= p' -> p' + n' <= p + n -> 0 < n' ->
  shadow_hull_vis rd p' n'.
Proof.
intros rd p n p' n' V H1 H2 Hn s Hs. apply V. unfold shadow_addr in *.
pose proof (Z.div_le_mono p p' 8 ltac:(lia) H1) as M1.
pose proof (Z.div_le_mono (p' + n' - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + p' / 8) 8 ltac:(lia) ltac:(lia)) as M3.
pose proof (Z.div_le_mono (SHADOW_OFF + (p' + n' - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as M4.
lia.
Qed.

Lemma m1_ra_pat : forall H (m : word -> option byte) F a n,
  0 <= F -> F mod 32 = 0 -> garr8 SEGS (mrestrict H m) (SHADOW_OFF + F / 8) PAT_A ->
  F + 32 <= a -> a + n <= F + 64 -> range_addressable (aview SEGS H m) SHADOW_OFF a n.
Proof.
intros H m F a n HF0 HFal HG Ha Hn x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M1.
pose proof (Z.div_mod F 32 ltac:(lia)) as D0.
pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
assert (Hj : 4 <= x / 8 - F / 8 < 8) by lia.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + Z.of_nat (Z.to_nat (x / 8 - F / 8))) by lia.
rewrite (m1_aview_garr8 H m _ PAT_A _ HG) by (unfold PAT_A; cbn [length]; lia).
f_equal. assert (Hc : (Z.to_nat (x / 8 - F / 8) = 4 \/ Z.to_nat (x / 8 - F / 8) = 5 \/
  Z.to_nat (x / 8 - F / 8) = 6 \/ Z.to_nat (x / 8 - F / 8) = 7)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma m1_rd6_kept : forall cx W3 (mem3 m : word -> option byte) p,
  m1_rd6 cx W3 mem3 p ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m a) ->
  m1_rd6 cx W3 m p.
Proof.
intros cx W3 mem3 m p (H0 & H47 & Ham & Hs & Ho & Hp & Hra & Hhu) K P.
split; [exact H0|]. split; [exact H47|]. split; [exact Ham|]. split; [exact Hs|]. split; [exact Ho|].
split; [intros a Ha; apply P, Hp, Ha|].
split; [exact (m1_ra_kept _ _ _ p 6 H0 H47 K Hra) | exact (m1_hull_kept _ _ _ p 6 H0 ltac:(lia) H47 K Hhu)].
Qed.

Section call.
Variables (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model).
Hypothesis Hpre : cls_pre B cx.
Hypothesis Hcut : cls_at_R1 B cx fpos W3 ly3 S3 regs3 mem3 md3.

Lemma m1_ctx : cSP cx mod 16 = 0 /\ cSP cx - 176 <= cS1 cx <= cSP cx - 160 /\ cS1 cx mod 16 = 0 /\
  alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx - x_STK cx <= cSP cx - 8512 /\
  cSP cx <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  4096 <= cF cx fpos /\ cF cx fpos + 256 <= alloc_ceiling /\ cF cx fpos mod 32 = 0 /\
  getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
  4096 <= x_o cx /\ x_o cx + 24 <= alloc_ceiling /\ (x_o cx + 24 <= kLowShadowBeg \/ kHighMemBeg <= x_o cx) /\
  (x_o cx + 24 <= cF cx fpos \/ cF cx fpos + 256 <= x_o cx) /\ ESTACK = 4096.
Proof.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
destruct (m1_nums cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc)
  as (Hsp16 & HS1 & HS1al & Hceil & Hstk & Hsp & H47 & Hpres & HF4 & HFc & HFal & CS & ES).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & ((_ & _ & _ & _ & HOsh) & _ & HOF & _) & HO4096 & HOc & _).
pose proof Hc as (HJ & _ & _ & _ & _ & _ & _ & _ & R3 & R4 & _).
pose proof Hpre as (_ & _ & _ & _ & Hgp & Htp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
pose proof (m1_S1_bounds (cSP cx) Hsp16) as (_ & _ & H16).
rewrite CS in Hstk.
repeat split; try assumption; try lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
Qed.

Lemma m1_rd6_q : m1_rd6 cx W3 mem3 (cF cx fpos + 36).
Proof.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as ((HF4 & HFc & HFal & Hz & Hia & HFp & _) & _).
pose proof Hc as (HJ & Hfr & _ & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSHP & _).
pose proof m1_ctx as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOF & ES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|].
split; [apply (amem_range_sub_app (cF cx fpos) 256); [exact Hia | lia | lia | lia | lia]|].
split; [left; lia|]. split; [lia|].
split; [intros a Ha; apply HFp; lia|].
split; [apply (m1_ra_pat _ _ (cF cx fpos)); [lia | exact HFal | exact HSHP | lia | lia]|].
apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 mem3 md3 2 fpos); [exact (proj1 HJ) | rewrite Hfr; left; reflexivity | | | lia];
  rewrite Hfa; change (fs_frame_bytes 2) with 256; lia.
Qed.

Lemma m1_rd6_u : m1_rd6 cx W3 mem3 (x_u cx).
Proof.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & ((Hu0 & Hu47 & Huam & _ & _) & (Hup & Hura & Huhu) & _ & Husp) & _).
pose proof m1_ctx as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOF & ES).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & HOU & _).
assert (CS : CLS_STK = 8512) by reflexivity.
split; [exact Hu0|]. split; [exact Hu47|]. split; [exact Huam|]. split; [rewrite CS in Husp; lia|].
split; [lia|]. split; [exact Hup|]. split; [exact Hura | exact Huhu].
Qed.

Lemma m1_rd6_lk : forall Lb, x_L cx = Some Lb -> m1_rd6 cx W3 mem3 (x_lk cx).
Proof.
intros Lb HL.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & _ & _ & _ & _ & HLk). rewrite HL in HLk.
destruct HLk as (((Hk0 & Hk47 & Hkam & _ & _) & (Hkp & Hkra & Hkhu) & _ & _) & Hk4 & Hkc & _).
pose proof m1_ctx as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOF & ES).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLd).
rewrite HL in HLd. destruct HLd as (HLo & _).
split; [lia|]. split; [lia|].
split; [unfold amem_range in *; lia|]. split; [left; lia|]. split; [lia|].
split; [intros a Ha; apply Hkp; lia|].
split; [apply (m1_ra_sub _ _ _ _ _ _ Hkra); lia | apply (m1_hull_sub _ _ _ _ _ Hkhu); lia].
Qed.

End call.

Section call2.
Variables (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model).
Hypothesis Hpre : cls_pre B cx.
Hypothesis Hcut : cls_at_R1 B cx fpos W3 ly3 S3 regs3 mem3 md3.

Lemma m1_band0 : forall m, m1_kept1 cx W3 mem3 m ->
  forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a.
Proof.
intros m [K _] a Ha. pose proof (m1_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut)
  as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOsh & _ & ES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold kLowShadowBeg in *.
apply K; lia.
Qed.

Lemma m1_bcmp : forall (fq : YK11.FPState) (regsT : bvmap 5 word) memT mdT x y (ra : word),
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 memT mdT (x_k cx) ->
  m1_kept0 cx W3 mem3 memT ->
  spZ regsT = cS1 cx -> getr regsT 3 = getr regs3 3 -> getr regsT 4 = getr regs3 4 ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 6 -> getr regsT 1 = ra -> YK0s.ret_ok ra ->
  m1_rd6 cx W3 mem3 x -> m1_rd6 cx W3 mem3 y ->
  SRr SEGS W3 (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA AS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
   (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2 (v : word),
      c2 = mkCfg (mkst (fx := fq) regs2 ra mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        ((2, fpos) :: x_own cx) ly3 S3 W3 mem2 md2 (x_k cx) /\
      aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
      (v = w64 0 <-> forall i, 0 <= i < 6 -> aview SEGS (w_H W3) mem3 (x + i) = aview SEGS (w_H W3) mem3 (y + i)) /\
      m1_kept0 cx W3 mem3 mem2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (cS1 cx - 2 * ESTACK <= a < cS1 cx) ->
         aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a) /\
      (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a)).
Proof.
intros fq regsT memT mdT x y ra HJT HKT Hsp3 G3 G4 Ha0 Ha1 Ha2 Hra1 Hra Hx Hy.
pose proof (m1_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut)
  as (_ & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & _ & _ & _ & Hgp & Htp & _ & _ & HOsh & _ & ES).
pose proof (m1_band0 memT (m1_kept01 _ _ _ _ HKT)) as KB.
destruct (m1_rd6_kept cx W3 mem3 memT x Hx KB (proj2 HKT)) as (Hx0 & Hx47 & Hxam & Hxs & _ & Hxp & Hxra & Hxhu).
destruct (m1_rd6_kept cx W3 mem3 memT y Hy KB (proj2 HKT)) as (Hy0 & Hy47 & Hyam & Hys & _ & Hyp & Hyra & Hyhu).
pose proof pa_segs_low as Hsegs.
eapply SRr_mono.
{ apply (aj_bcmp_at SEGS B LAWS Hsegs _ (ABCMP fq) W3 regsT memT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx)
    (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 mdT (x_k cx) x y 6 (cS1 cx - x_sp0 cx)
    ra HJT Ha0 Ha1 Ha2 ltac:(lia) Hx0 ltac:(lia) Hy0 ltac:(lia)).
  - lia.
  - rewrite Zminus_mod, HS16, Hsp0al. reflexivity.
  - lia.
  - rewrite ES. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact Hra1.
  - exact Hra.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hxp; lia | rewrite Hsp3, ES; lia].
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hyp; lia | rewrite Hsp3, ES; lia].
  - intros a Ha. rewrite ES. lia.
  - intros a Ha. rewrite ES. lia.
  - exact Hxam.
  - exact Hyam.
  - exact Hxra.
  - intros _. exact Hxhu.
  - exact Hyra.
  - intros _. exact Hyhu. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2).
replace (x_sp0 cx + (cS1 cx - x_sp0 cx)) with (cS1 cx) in Hfr by lia.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
destruct HKT as [KT PT].
split.
{ rewrite Hcmp. split; intros X i Hi.
  - rewrite <- (KT (x + i)), <- (KT (y + i)); [apply X; exact Hi | lia | | lia |]; rewrite ES; lia.
  - rewrite (KT (x + i)), (KT (y + i)); [apply X; exact Hi | lia | | lia |]; rewrite ES; lia. }
split.
{ split; [|intros a Ha; apply Hpres2, PT, Ha].
  intros a Ha Hn. rewrite (Hfr a Ha) by lia. apply KT; assumption. }
split; [exact Hfr | exact Hpres2].
Qed.

End call2.

Lemma m1_frame_aview : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> ~ in_wrange E rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Hn Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma m1_pres_grows : forall (m m' : word -> option byte) (H : word -> bool) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros m m' H a HG (Hh & b & Hb). split; [exact Hh|].
assert (Hne : mrestrict H m' (Z_to_bv 64 a) <> None).
{ apply HG. unfold mrestrict. rewrite Hh, Hb. discriminate. }
unfold mrestrict in Hne. rewrite Hh in Hne. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. apply Hne. reflexivity.
Qed.

Lemma m1_kept0_run : forall cx W3 (mem3 m m' : word -> option byte) E rs,
  m1_kept0 cx W3 mem3 m -> frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  mem_grows (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall a, in_wrange E rs a -> cS1 cx + 8 <= a < cS1 cx + 16) -> m1_kept0 cx W3 mem3 m'.
Proof.
intros cx W3 mem3 m m' E rs [K P] HF HG Hw. split.
- intros a Ha Hn. rewrite (m1_frame_aview E rs _ m m' a HF) by (try exact Ha; intros X; apply Hn; pose proof (Hw a X); unfold ESTACK; lia).
  apply K; assumption.
- intros a Ha. apply (m1_pres_grows m m'); [exact HG | apply P, Ha].
Qed.

Lemma m1_br_eq : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros E n v Hv Hc. rewrite branch_eq_U, U_SOff, Hv, Z.add_0_r in Hc. apply Z.eqb_eq in Hc.
unfold U in Hc. cbn [sv_denot] in Hc. rewrite zcanon_id in Hc by (pose proof (u64_range v); unfold M64; lia).
apply bv_eq. rewrite Hc. reflexivity.
Qed.

Lemma m1_br_ne : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros E n v Hv Hc Heq. rewrite branch_eq_U, U_SOff, Hv, Heq, Z.add_0_r in Hc. apply Z.eqb_neq in Hc.
apply Hc. unfold U. cbn [sv_denot]. reflexivity.
Qed.

Lemma m1_U_sext : forall E n k, ew E n = Z_to_bv 64 k -> 0 <= k < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = k.
Proof.
intros E n k H Hk. rewrite U_SExt, (U_atom E n k H) by lia. change (2 ^ Z.of_N 32) with 4294967296.
rewrite (Z.mod_small k) by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
rewrite (Z.mod_small (k + 2147483648)) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma m1_U_sext0 : forall E n k, ew E n = Z_to_bv 64 k -> 0 <= k < 2 ^ 32 ->
  (U E (SExt true 32 (SOff n 0)) = 0 <-> k = 0).
Proof.
intros E n k H Hk. rewrite U_SExt, (U_atom E n k H) by lia. change (2 ^ Z.of_N 32) with 4294967296.
rewrite (Z.mod_small k) by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
unfold zcanon, M64. destruct (Z_lt_le_dec k 2147483648) as [Hl|Hl].
- rewrite (Z.mod_small (k + 2147483648)) by lia. rewrite (Z.mod_small (k + 2147483648 - 2147483648)) by lia. lia.
- rewrite (Z.mod_eq (k + 2147483648) 4294967296) by lia.
  replace ((k + 2147483648) / 4294967296) with 1 by (apply Z.div_unique with (r := k - 2147483648); lia).
  rewrite (Z.mod_eq _ (2 ^ 64)) by lia.
  replace ((k + 2147483648 - 4294967296 * 1 - 2147483648) / 2 ^ 64) with (-1)
    by (apply Z.div_unique with (r := k - 4294967296 + 2 ^ 64); lia).
  lia.
Qed.

Section exits.
Variables (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model).
Hypothesis Hpre : cls_pre B cx.
Hypothesis Hcut : cls_at_R1 B cx fpos W3 ly3 S3 regs3 mem3 md3.

Lemma m1_o_kept : forall m, m1_kept0 cx W3 mem3 m ->
  garr8 SEGS (mrestrict (w_H W3) m) (x_o cx) (cls_bytes (x_OB cx)).
Proof.
intros m [K _].
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HOl & HO & _).
pose proof (m1_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut)
  as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & Ho4 & Hoc & _ & _ & ES).
refine (m1_garr8_kept _ _ _ _ _ _ HO). intros j Hj. unfold cls_bytes in Hj. rewrite length_map, HOl in Hj.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply K; rewrite ?ES; lia.
Qed.

Lemma m1_to_X : forall regs4 mem4 md4,
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
  m1_kept0 cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = getr regs3 19 -> getr regs4 20 = getr regs3 20 -> getr regs4 27 = getr regs3 27 ->
  getr regs4 24 = w64 (cRet cx) -> cOut cx = x_OB cx -> cLock cx = x_L cx ->
  cls_at_X B cx fpos W3 ly3 S3 regs4 mem4 md4.
Proof.
intros regs4 mem4 md4 HJ4 HK4 G2 G3 G4 G8 G9 G18 G19 G20 G27 G24 HO HL.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOBl & _).
unfold cls_at_X. rewrite HO, HL.
apply (m1_cut cx fpos _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 PC_X _ _ None false regs4 mem4 md4 Hpre Hc HJ4
  (proj1 (m1_kept01 _ _ _ _ HK4)) (proj2 HK4) G2 G3 G4 G8 G9 G18 G19 G20 G27).
- constructor; [exact G24 | constructor].
- intros X; discriminate X.
- exact I.
- exact HOBl.
- exact (m1_o_kept mem4 HK4).
Qed.

Lemma m1_to_SW : forall regs4 mem4 md4,
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
  m1_kept0 cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = getr regs3 19 -> getr regs4 20 = getr regs3 20 -> getr regs4 27 = getr regs3 27 ->
  getr regs4 21 = w64 SHADOW_OFF -> getr regs4 22 = w64 (cF cx fpos + 32) -> getr regs4 25 = w64 (cF cx fpos + 36) ->
  val_mem SEGS (mrestrict (w_H W3) mem4) (cS1 cx + 8) 8 (x_len cx) ->
  cRet cx = 0 -> cLock cx = x_L cx ->
  cls_at_SW B cx fpos W3 ly3 S3 regs4 mem4 md4.
Proof.
intros regs4 mem4 md4 HJ4 HK4 G2 G3 G4 G8 G9 G18 G19 G20 G27 G21 G22 G25 VL HR HL.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOBl & _).
unfold cls_at_SW. cbv zeta. split; [exact HR|]. rewrite HL.
apply (m1_cut cx fpos _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 PC_SW _ _ (Some (cPS cx)) true regs4 mem4 md4 Hpre Hc HJ4
  (proj1 (m1_kept01 _ _ _ _ HK4)) (proj2 HK4) G2 G3 G4 G8 G9 G18 G19 G20 G27).
- constructor; [exact G21|]. constructor; [exact G22|]. constructor; [exact G25 | constructor].
- intros _; exact VL.
- reflexivity.
- exact HOBl.
- exact (m1_o_kept mem4 HK4).
Qed.

Lemma m1_to_K : forall regs4 mem4 md4,
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
  m1_kept0 cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = getr regs3 19 -> getr regs4 20 = getr regs3 20 -> getr regs4 27 = getr regs3 27 ->
  getr regs4 1 = w64 (BASE + PC_R2) -> getr regs4 10 = w64 (x_f cx) ->
  getr regs4 21 = w64 SHADOW_OFF -> getr regs4 22 = w64 (cF cx fpos + 32) -> getr regs4 23 = w64 (x_lk cx) ->
  getr regs4 24 = w64 (-1) -> getr regs4 25 = w64 (cF cx fpos + 36) -> getr regs4 26 = w64 (x_u cx) ->
  val_mem SEGS (mrestrict (w_H W3) mem4) (cS1 cx + 8) 8 (x_len cx) ->
  cK cx <> 0 -> cK cx <> 1 -> CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false ->
  cls_at_K B cx fpos W3 ly3 S3 regs4 mem4 md4.
Proof.
intros regs4 mem4 md4 HJ4 HK4 G2 G3 G4 G8 G9 G18 G19 G20 G27 G1 G10 G21 G22 G23 G24 G25 G26 VL H0 H1 HE.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOBl & _).
unfold cls_at_K. cbv zeta. split; [exact H0|]. split; [exact H1|]. split; [exact HE|].
apply (m1_cut cx fpos _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 AF_both3_reac_ctrl_checksum_verify _ _ (Some (cPS cx)) true
  regs4 mem4 md4 Hpre Hc HJ4 (proj1 (m1_kept01 _ _ _ _ HK4)) (proj2 HK4) G2 G3 G4 G8 G9 G18 G19 G20 G27).
- repeat (constructor; [eassumption|]). constructor.
- intros _; exact VL.
- reflexivity.
- exact HOBl.
- exact (m1_o_kept mem4 HK4).
Qed.

Lemma m1_src_iff : cK cx <> 0 ->
  ((forall i, 0 <= i < 6 -> aview SEGS (w_H W3) mem3 (cF cx fpos + 36 + i) = aview SEGS (w_H W3) mem3 (x_u cx + i)) <->
   CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = true).
Proof.
intros Hk.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HPS & _). destruct HPS as (HPSl & HPS).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & HU & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFBl & HUl & _).
rewrite <- (m1_fld_src cx Hk HFBl).
assert (UF : CtrlParsed.fld (x_U cx) 0 6 = x_U cx)
  by (unfold CtrlParsed.fld; cbn [skipn]; apply firstn_all2; lia).
rewrite <- UF.
rewrite <- (m1_cmp6 (w_H W3) mem3 (cF cx fpos + 32) (x_u cx) (cPS cx) (x_U cx) 4 0 HPS HU ltac:(lia) ltac:(lia)).
split; intros X i Hi.
- replace (cF cx fpos + 32 + Z.of_nat 4 + i) with (cF cx fpos + 36 + i) by lia.
  replace (x_u cx + Z.of_nat 0 + i) with (x_u cx + i) by lia. apply X; exact Hi.
- replace (cF cx fpos + 36 + i) with (cF cx fpos + 32 + Z.of_nat 4 + i) by lia.
  replace (x_u cx + i) with (x_u cx + Z.of_nat 0 + i) by lia. apply X; exact Hi.
Qed.

Lemma m1_lk_iff : forall Lb, cK cx <> 0 -> x_L cx = Some Lb ->
  ((forall i, 0 <= i < 6 -> aview SEGS (w_H W3) mem3 (x_lk cx + i) = aview SEGS (w_H W3) mem3 (cF cx fpos + 36 + i)) <->
   CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src (x_FB cx)) = true).
Proof.
intros Lb Hk HL.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HPS & _ & _ & HL3). destruct HPS as (HPSl & HPS). rewrite HL in HL3. destruct HL3 as (HLl & HLg).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFBl & _).
rewrite <- (m1_fld_src cx Hk HFBl). unfold disco_classify_c.lm.
rewrite <- (m1_cmp6 (w_H W3) mem3 (x_lk cx) (cF cx fpos + 32) Lb (cPS cx) 0 4 HLg HPS ltac:(lia) ltac:(lia)).
split; intros X i Hi.
- replace (cF cx fpos + 32 + Z.of_nat 4 + i) with (cF cx fpos + 36 + i) by lia.
  replace (x_lk cx + Z.of_nat 0 + i) with (x_lk cx + i) by lia. apply X; exact Hi.
- replace (cF cx fpos + 36 + i) with (cF cx fpos + 32 + Z.of_nat 4 + i) by lia.
  replace (x_lk cx + i) with (x_lk cx + Z.of_nat 0 + i) by lia. apply X; exact Hi.
Qed.

Lemma m1_lk_ok : forall Lb, x_L cx = Some Lb ->
  0 < x_lk cx /\ 4096 <= x_lk cx /\ x_lk cx + 12 <= alloc_ceiling /\ x_lk cx mod 4 = 0 /\ length Lb = 12%nat /\
  (x_lk cx + 12 <= kLowShadowBeg \/ kHighMemBeg <= x_lk cx) /\
  (x_lk cx + 12 <= cF cx fpos \/ cF cx fpos + 256 <= x_lk cx) /\
  (x_lk cx + 12 <= x_o cx \/ x_o cx + 24 <= x_lk cx) /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (x_lk cx) 12 /\
  garr8 SEGS (mrestrict (w_H W3) mem3) (x_lk cx) (cls_bytes Lb).
Proof.
intros Lb HL.
pose proof Hcut as Hc. unfold cls_at_R1 in Hc. cbv zeta in Hc.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & _ & _ & _ & _ & HLk). rewrite HL in HLk.
destruct HLk as (((_ & _ & _ & _ & Hksh) & (_ & Hkra & _) & HkF & _) & Hk4 & Hkc & _).
pose proof Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & HL3). rewrite HL in HL3. destruct HL3 as (HLl & HLg).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & HLm & _ & _ & HLd).
rewrite HL in HLm, HLd. destruct HLm as (Hk0 & Hkal & _). destruct HLd as (HLo & _).
split; [exact Hk0|]. split; [exact Hk4|]. split; [exact Hkc|]. split; [exact Hkal|]. split; [exact HLl|].
split; [exact Hksh|]. split; [exact HkF|]. split; [exact HLo|]. split; [exact Hkra | exact HLg].
Qed.

Lemma m1_vm_lv : forall H (m : word -> option byte) p (Lb : list byte), length Lb = 12%nat ->
  garr8 SEGS (mrestrict H m) p (cls_bytes Lb) ->
  val_mem SEGS (mrestrict H m) (p + 8) 4 (disco_classify_c.lv Lb) /\ 0 <= disco_classify_c.lv Lb < 2 ^ 32.
Proof.
intros H m p Lb HL HG.
destruct Lb as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|]]]]]]]]]]]]]; try discriminate.
pose proof (bv_unsigned_in_range 8 b8) as R8. pose proof (bv_unsigned_in_range 8 b9) as R9.
pose proof (bv_unsigned_in_range 8 b10) as R10. pose proof (bv_unsigned_in_range 8 b11) as R11.
unfold bv_modulus in R8, R9, R10, R11. change (2 ^ Z.of_N 8) with 256 in R8, R9, R10, R11.
unfold disco_classify_c.lv, CtrlParsed.fu, CtrlParsed.fld. cbn [skipn firstn]. rewrite m1_ble4.
destruct (m1_le4_byte (bv_unsigned b8) (bv_unsigned b9) (bv_unsigned b10) (bv_unsigned b11) R8 R9 R10 R11)
  as (L0 & L1 & L2 & L3).
split; [|lia].
intros k Hk. replace (p + 8 + Z.of_nat k) with (p + Z.of_nat (8 + k)) by lia.
rewrite (garr8_mbyte SEGS _ p _ (8 + k) HG) by (cbn; lia).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Nat.add nth cls_bytes map].
- rewrite L0. reflexivity.
- rewrite L1. reflexivity.
- rewrite L2. reflexivity.
- rewrite L3. reflexivity.
Qed.

End exits.

Ltac m1_awr cx Ub :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (cS1 cx - x_sp0 cx));
  [reflexivity | rewrite Ub; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].

Ltac m1_wr Ub :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros a (r & Hin & Ha); vm_compute in Hin;
repeat (destruct Hin as [Hin|Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  first [rewrite Ub in Ha | idtac]; lia|]);
destruct Hin.

Ltac m1_step0 KM Ub :=
lazymatch goal with
| HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
  let K := fresh "KM" in
  pose proof (m1_kept0_run _ _ _ _ _ _ _ KM HFr HG ltac:(m1_wr Ub)) as K;
  clear KM HFr HG; rename K into KM;
  try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end
end.

Ltac m1_fix HS AG EW :=
lazymatch goal with |- getr _ ?r = getr _ ?r =>
  let G := fresh "G" in prreg HS r G; refine (eq_trans G _); refine (eq_trans (AG _ _) _);
  first [apply EW; reflexivity | cbv; lia] end.

Ltac m1_rv HS :=
lazymatch goal with |- getr _ ?r = _ => let G := fresh "G" in prreg HS r G; refine (eq_trans G _) end.

Ltac m1_kept_b Hfr Hp Ub9 Ub22 :=
eapply region_kept_aview;
[ first [exact Ub9 | exact Ub22]
| let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr; unfold ESTACK in *; lia
| exact Hp ].

Ltac m1_shok HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) (mkst _ _ ?mx _)) =>
  try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
  assert (SHOK : sh_ok SEGS m1_Bx [] Ex (mrestrict (w_H Wx) mx)) by apply Forall_nil end.

Ltac m1_bres HS Hv Hc VZ :=
lazymatch type of Hv with getr _ ?r = _ =>
  let G := fresh "G" in prreg HS r G; rewrite Hv in G;
  first [ pose proof (m1_br_eq _ _ _ (eq_sym G) Hc) as VZ | pose proof (m1_br_ne _ _ _ (eq_sym G) Hc) as VZ ];
  clear G Hc end.

Ltac m1_exitX HX HS HJ KM AG EW Hpre Hcut0 MR MO ML :=
pmkst HS; eapply (HX _ _ _ _ _ _ _ _ Hpre);
apply (m1_to_X _ _ _ _ _ _ _ _ Hpre Hcut0 _ _ _ HJ KM); try (m1_fix HS AG EW);
[ m1_rv HS; rewrite MR; apply bv_eq; vm_compute; reflexivity | exact MO | exact ML ].

Ltac m1_len HS i Ub AG EW Rs9 :=
let RG := fresh "RG" in
lazymatch type of HS with
| st_ok _ _ _ _ => pose proof (st_ok_region_nth _ _ _ i _ HS eq_refl) as RG
| st_ok_pi _ _ _ _ _ => pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as RG
end;
cbn [ms_mem restrict mkst] in RG;
refine (field_of_region _ _ 9 _ _ _ _ _ _ 8 8 (SOff 25 0) _ RG Ub _ _ _ _);
[ cbn; tauto
| cbn [sv_denot]; rewrite (AG 25%nat) by lia; rewrite (EW 25%nat (Z_to_bv 5 25) eq_refl), Rs9, Z.add_0_r;
  unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
| change (8 * Z.of_N 8) with 64; lia
| lia ].

Ltac m1_exitSW HSW HS HJ KM AG EW Hpre Hcut0 i Ub9 Rs5 Rs6 Rs9 U22c MR ML :=
pmkst HS; eapply (HSW _ _ _ _ _ _ _ _ Hpre);
apply (m1_to_SW _ _ _ _ _ _ _ _ Hpre Hcut0 _ _ _ HJ KM); try (m1_fix HS AG EW);
[ m1_rv HS; rewrite (AG 21%nat) by lia; rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl); exact Rs5
| m1_rv HS; rewrite (AG 22%nat) by lia; rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl); exact Rs6
| m1_rv HS; rewrite U22c; unfold w64; f_equal; lia
| m1_len HS i Ub9 AG EW Rs9
| exact MR | exact ML ].

Ltac m1_sp HS AG U2 :=
unfold spZ; lazymatch goal with |- bv_unsigned (getr _ ?r) = _ =>
  let G := fresh "G" in prreg HS r G; rewrite G; rewrite (AG 2%nat) by lia; exact U2 end.

Ltac m1_envU HS AG U9 U22 U9n U22n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
lazymatch type of U9 with bv_unsigned (ew _ 9) = ?v9 =>
lazymatch type of U22 with bv_unsigned (ew _ 22) = ?v22 =>
  assert (U9n : bv_unsigned (ew Ex 9) = v9) by (rewrite (AG 9%nat) by lia; exact U9);
  assert (U22n : bv_unsigned (ew Ex 22) = v22) by (rewrite (AG 22%nat) by lia; exact U22) end end end.

Ltac m1_reenv HS AG :=
lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
lazymatch type of AG with forall n, _ -> ew _ n = ew ?E0 n =>
  let Ev := fresh "E" in let HEv := fresh "HEv" in
  remember En as Ev eqn:HEv;
  let AG2 := fresh "AGn" in
  assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
    by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
  clear AG HEv; rename AG2 into AG
end end.

Ltac m1_ew HS AG E32 Elv v Ex32 :=
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (Ex32 : ew Ex 32 = Z_to_bv 64 v) by (rewrite (AG 32%nat) by lia; rewrite E32, Elv; reflexivity) end.

Ltac m1_eU HS AG EW Rs n r Un v :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex _ _ => assert (Un : bv_unsigned (ew Ex n) = v)
| st_ok _ ?Ex _ _ => assert (Un : bv_unsigned (ew Ex n) = v)
end;
[ rewrite (AG n) by lia; rewrite (EW n r eq_refl), Rs;
  unfold w64; rewrite unsigned_lit_small by lia; reflexivity |].

Ltac m1_kept_c Hfr Hp Ub9 Ub22 Ub23 :=
eapply region_kept_aview;
[ first [exact Ub9 | exact Ub22 | exact Ub23]
| let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr; unfold ESTACK in *; lia
| exact Hp ].

Theorem cls_m1 : cls_from_K B -> cls_from_SW B -> cls_from_X B -> cls_from_R1 B.
Proof.
intros HK HSW HX. unfold cls_from_R1, cls_from.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0.
pose proof (m1_entry cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0) as HS.
pose proof Hcut0 as Hcut. unfold cls_at_R1 in Hcut. cbv zeta in Hcut.
pose proof (m1_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0)
  as (Hsp16 & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & HF4 & HFc & HFal & Hgp & Htp & Ho4 & Hoc & HOsh & HOF & ES).
pose proof Hcut as (HJ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV & _ & _ & _ & _ & _ & _ & _
  & _ & HPS & _).
destruct HPS as (HPSl & HPSg).
apply Forall_cons_iff in HRV as [Ra0 HRV]. apply Forall_cons_iff in HRV as [Rs5 HRV].
apply Forall_cons_iff in HRV as [Rs6 HRV]. apply Forall_cons_iff in HRV as [Rs7 HRV].
apply Forall_cons_iff in HRV as [Rs8 HRV]. apply Forall_cons_iff in HRV as [Rs9 HRV].
apply Forall_cons_iff in HRV as [Rs10 _].
cbn [fst snd] in Ra0, Rs5, Rs6, Rs7, Rs8, Rs9, Rs10.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & HFBl & HUl & HOBl & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HKr : 0 <= cK cx <= 13) by exact (RcParse.ctrlparse_kind_range (x_len cx) (x_FB cx)).
assert (Hsig : SIGMA AS_reac_ctrl_checksum_verify = BASE + AF_both3_reac_ctrl_checksum_verify)
  by (apply pa_xcalls; cbn [In both3_xcalls]; repeat (first [left; reflexivity | right])).
set (fq := x_fq cx) in *.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
set (E0 := Eimg (Ereg regs3 (m1_extra cx))) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs3 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = Z_to_bv 64 (m1_lv cx))
  by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (SHOK : sh_ok SEGS m1_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
clearbody E0.
assert (AG : forall n, (n < 33)%nat -> ew E0 n = ew E0 n) by reflexivity.
assert (U9 : bv_unsigned (ew E0 9) = cS1 cx)
  by (rewrite (EW 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U2 : bv_unsigned (ew E0 2) = cS1 cx)
  by (rewrite (EW 2%nat 2%bv eq_refl), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U22 : bv_unsigned (ew E0 22) = cF cx fpos + 32)
  by (rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl), Rs6; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (KM : m1_kept0 cx W3 mem3 mem3) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
unfold cfg_at. change (w64 (BASE + PC_R1)) with (Z_to_bv 64 (BASE + PC_R1)).
paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9] |].
m1_step0 KM U9.
psrr_branch_tok RUN BR HS SHOK m1_span.
- assert (Hk0 : cK cx = 0).
  { rewrite branch_eq_U, (U_atom E0 10 (cK cx) ltac:(rewrite (EW 10%nat (Z_to_bv 5 10) eq_refl); exact Ra0) ltac:(lia)) in Hc.
    unfold U in Hc. cbn [sv_denot] in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  destruct (m1_mod_k0 cx Hk0) as (MR & MO & ML).
  paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_X; [solve [m1_awr cx U9] |].
  m1_step0 KM U9.
  pmkst HS.
  apply (HX cx fpos W3 ly3 S3 _ _ _ Hpre).
  apply (m1_to_X cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 _ _ _ HJ KM); try (m1_fix HS AG EW).
  + m1_rv HS. rewrite MR. apply bv_eq. vm_compute. reflexivity.
  + exact MO.
  + exact ML.
- assert (Hk0 : cK cx <> 0).
  { rewrite branch_eq_U, (U_atom E0 10 (cK cx) ltac:(rewrite (EW 10%nat (Z_to_bv 5 10) eq_refl); exact Ra0) ltac:(lia)) in Hc.
    unfold U in Hc. cbn [sv_denot] in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9] |].
  m1_step0 KM U9.
  pmkst HS.
  eapply SRr_bind.
  { eapply (m1_bcmp cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 fq _ _ _ (cF cx fpos + 36) (x_u cx) _ HJ KM).
    - unfold spZ. lazymatch goal with |- bv_unsigned (getr _ ?r) = _ => let G := fresh "G" in prreg HS r G; rewrite G end.
      exact U2.
    - m1_fix HS AG EW.
    - m1_fix HS AG EW.
    - m1_rv HS. rewrite U22. unfold w64. f_equal. lia.
    - m1_rv HS. rewrite (EW 26%nat (Z_to_bv 5 26) eq_refl). exact Rs10.
    - m1_rv HS. reflexivity.
    - m1_rv HS. reflexivity.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact (m1_rd6_q cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0).
    - exact (m1_rd6_u cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KM2 & Hfr2 & Hpres2).
  reseat HS HJ2 HP2 [0;1]%nat AG ltac:(m1_kept_b Hfr2 Hpres2 U9 U22).
  clear KM HJ. rename KM2 into KM. rename HJ2 into HJ. m1_shok HS.
  assert (U9b : bv_unsigned (ew E 9) = cS1 cx) by (rewrite (AG 9%nat) by lia; exact U9).
  assert (U22b : bv_unsigned (ew E 22) = cF cx fpos + 32) by (rewrite (AG 22%nat) by lia; exact U22).
  psrr_branch_tok RUN BR HS SHOK m1_span.
  + m1_bres HS Hv Hc VZ.
    pose proof (proj1 (m1_src_iff cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Hk0) (proj1 Hcmp VZ)) as VE.
    destruct (m1_mod_eq cx Hk0 VE) as (MR & MO & ML).
    paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_X; [solve [m1_awr cx U9b] |].
    m1_step0 KM U9b.
    m1_exitX HX HS HJ KM AG EW Hpre Hcut0 MR MO ML.
  + m1_bres HS Hv Hc VZ.
    assert (HUe : CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false).
    { destruct (CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx)) eqn:Eb; [|reflexivity].
      exfalso. apply VZ. apply (proj2 Hcmp). apply (proj2 (m1_src_iff cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Hk0)).
      exact Eb. }
    clear VZ Hcmp Hv.
    paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9b] |].
    m1_step0 KM U9b.
    assert (E10 : ew E 10 = Z_to_bv 64 (cK cx))
      by (rewrite (AG 10%nat) by lia; rewrite (EW 10%nat (Z_to_bv 5 10) eq_refl); exact Ra0).
    psrr_branch_tok RUN BR HS SHOK m1_span.
    * assert (Hk1 : cK cx <> 1).
      { rewrite branch_ne_U, (m1_U_sext E 10 (cK cx) E10 ltac:(lia)), U_SLit in Hc.
        rewrite zcanon_id in Hc by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9b] |].
      m1_step0 KM U9b.
      pmkst HS. rewrite Hsig.
      eapply (HK _ _ _ _ _ _ _ _ Hpre).
      apply (m1_to_K cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 _ _ _ HJ KM); try (m1_fix HS AG EW).
      -- m1_rv HS. reflexivity.
      -- m1_rv HS. rewrite (AG 24%nat) by lia. rewrite (EW 24%nat (Z_to_bv 5 24) eq_refl). exact Rs8.
      -- m1_rv HS. rewrite (AG 21%nat) by lia. rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl). exact Rs5.
      -- m1_rv HS. rewrite (AG 22%nat) by lia. rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl). exact Rs6.
      -- m1_rv HS. rewrite (AG 23%nat) by lia. rewrite (EW 23%nat (Z_to_bv 5 23) eq_refl). exact Rs7.
      -- m1_rv HS. apply bv_eq. vm_compute. reflexivity.
      -- m1_rv HS. rewrite U22b. unfold w64. f_equal. lia.
      -- m1_rv HS. rewrite (AG 26%nat) by lia. rewrite (EW 26%nat (Z_to_bv 5 26) eq_refl). exact Rs10.
      -- m1_len HS 0%nat U9b AG EW Rs9.
      -- exact Hk0.
      -- exact Hk1.
      -- exact HUe.
    * assert (Hk1 : cK cx = 1).
      { rewrite branch_ne_U, (m1_U_sext E 10 (cK cx) E10 ltac:(lia)), U_SLit in Hc.
        rewrite zcanon_id in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9b] |].
      m1_step0 KM U9b.
      assert (E23 : ew E 23 = Z_to_bv 64 (x_lk cx))
        by (rewrite (AG 23%nat) by lia; rewrite (EW 23%nat (Z_to_bv 5 23) eq_refl); exact Rs7).
      pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & _ & _ & _ & HLm & _).
      destruct (x_L cx) as [Lb|] eqn:HL.
      ++ destruct (m1_lk_ok cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Lb HL)
           as (Hlk0 & Hlk4 & Hlkc & Hlkal & HLbl & Hlksh & HlkF & HlkO & Hlkra & HLbg).
         psrr_branch_tok RUN BR HS SHOK m1_span.
         1:{ exfalso. rewrite branch_eq_U, (U_atom E 23 (x_lk cx) E23 ltac:(lia)), U_SLit in Hc.
             rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc. lia. }
         clear Hc.
         paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9b] |].
         m1_step0 KM U9b.
         psrr_branch_tok RUN BR HS SHOK m1_span.
         1:{ exfalso. rewrite branch_ne_U, (m1_and3 E 23 (x_lk cx) E23 ltac:(lia) Hlkal), U_SLit in Hc.
             vm_compute in Hc. discriminate Hc. }
         clear Hc.
         destruct (m1_vm_lv _ _ _ Lb HLbl HLbg) as (Vlv & Rlv).
         assert (Elv : m1_lv cx = disco_classify_c.lv Lb) by (unfold m1_lv; rewrite HL; reflexivity).
         assert (U21b : U E m1_Bx = SHADOW_OFF).
         { unfold m1_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
           rewrite (AG 21%nat) by lia. rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl). exact Rs5. }
         assert (E32b : ew E 32 = Z_to_bv 64 (disco_classify_c.lv Lb))
           by (rewrite (AG 32%nat) by lia; rewrite E32, Elv; reflexivity).
         lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
           assert (RLK : region_ok SEGS E (ms_mem (restrict (w_H W3) msx)) m1_lk);
           [ cbn [ms_mem restrict];
             unfold region_ok, m1_lk; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
             rewrite E23, unsigned_lit_small by lia;
             split; [lia|]; split; [lia|]; split; [intros q Hq; lia|];
             constructor; [|constructor];
             apply (chunk_ok_val SEGS E _ (x_lk cx) 8 4 (SOff 32 0) (disco_classify_c.lv Lb));
             [ cbn [sv_denot]; rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
             change (N.to_nat 4) with 4%nat;
             refine (val_mem_kept SEGS _ _ _ _ _ _ _ _ Vlv); intros k Hk; apply (proj1 KM); cbn in Hk; unfold ESTACK; lia
           | pose proof (st_ok_pi_add_region _ _ _ m1_lk HS eq_refl RLK) as HSa ] end.
         lazymatch type of HSa with ?D -> _ => assert (HD : D) end.
         { apply all_disjoint_of_extents.
           match goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
           unfold m1_lk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
           rewrite E23, U9b, U22b, unsigned_lit_small by lia.
           cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
         specialize (HSa HD). clear HS RLK HD.
         pose proof (st_ok_pi_add_fact _ _ _ 23 (mkAF 4096 (2 ^ 47 - 12) 2) HSa) as HS.
         lazymatch type of HS with ?D -> _ => assert (HD : D) end.
         { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E23, unsigned_lit_small by lia. change (2 ^ 2) with 4. lia. }
         specialize (HS HD). clear HSa HD.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
           try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
           assert (SHOK : sh_ok SEGS m1_Bx [mkSHE 23 0 12] E (mrestrict (w_H W3) (ms_mem msx))) end.
         { unfold sh_ok. constructor; [|constructor].
           apply (shent_ok_of_range SEGS (w_H W3) _ E m1_Bx 23 (x_lk cx) 12 (x_lk cx) 0 12).
           - refine (m1_ra_kept _ _ _ (x_lk cx) 12 _ _ _ Hlkra); [lia | lia |].
             exact (m1_band0 cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 _ (m1_kept01 _ _ _ _ KM)).
           - exact U21b.
           - apply U_atom; [exact E23 | lia].
           - lia.
           - lia.
           - intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
         paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9b] |].
         m1_step0 KM U9b.
         m1_reenv HS AG.
         m1_envU HS AG U9 U22 U9e U22e.
         m1_ew HS AG E32 Elv (disco_classify_c.lv Lb) E32e.
         psrr_branch_tok RUN BR HS SHOK m1_span.
         --- assert (Hlv0 : disco_classify_c.lv Lb = 0).
             { rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
               apply Z.eqb_eq in Hc. exact (proj1 (m1_U_sext0 _ 32 _ E32e Rlv) Hc). }
             clear Hc.
             destruct (m1_mod_acc cx Lb Hk1 HUe HL (or_introl Hlv0)) as (MR & ML).
             paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_SW; [solve [m1_awr cx U9e] |].
             m1_step0 KM U9e.
             m1_exitSW HSW HS HJ KM AG EW Hpre Hcut0 1%nat U9e Rs5 Rs6 Rs9 U22e MR ML.
         --- assert (Hlvn : disco_classify_c.lv Lb <> 0).
             { rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
               apply Z.eqb_neq in Hc. intros X. apply Hc. exact (proj2 (m1_U_sext0 _ 32 _ E32e Rlv) X). }
             clear Hc.
             paj_run_tok RUN HS HJ SHOK m1_span; [solve [m1_awr cx U9e] |].
             m1_step0 KM U9e.
             pmkst HS.
             eapply SRr_bind.
             { eapply (m1_bcmp cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 fq _ _ _ (x_lk cx) (cF cx fpos + 36) _ HJ KM).
               - m1_sp HS AG U2.
               - m1_fix HS AG EW.
               - m1_fix HS AG EW.
               - m1_rv HS. rewrite (AG 23%nat) by lia. rewrite (EW 23%nat (Z_to_bv 5 23) eq_refl). exact Rs7.
               - m1_rv HS. rewrite U22e. unfold w64. f_equal. lia.
               - m1_rv HS. reflexivity.
               - m1_rv HS. reflexivity.
               - apply ret_ok_codeptr_v; [lia | reflexivity].
               - exact (m1_rd6_lk cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Lb HL).
               - exact (m1_rd6_q cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0). }
             cbv beta. intros W2 c2 _ (-> & regs6 & mem6 & md6 & v2 & -> & HJ2 & HPb & Hv2 & Hcmp2 & KM2 & Hfrb & Hprb).
             m1_eU HS AG EW Rs7 23%nat (Z_to_bv 5 23) U23e (x_lk cx).
             reseat HS HJ2 HPb [0;1;2]%nat AG ltac:(m1_kept_c Hfrb Hprb U9e U22e U23e).
             clear KM HJ. rename KM2 into KM. rename HJ2 into HJ. m1_shok HS.
             m1_envU HS AG U9 U22 U9f U22f.
             psrr_branch_tok RUN BR HS SHOK m1_span.
             +++ m1_bres HS Hv2 Hc VZ.
                 pose proof (proj1 (m1_lk_iff cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Lb Hk0 HL) (proj1 Hcmp2 VZ)) as VE.
                 destruct (m1_mod_acc cx Lb Hk1 HUe HL (or_intror VE)) as (MR & ML).
                 paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_SW; [solve [m1_awr cx U9f] |].
                 m1_step0 KM U9f.
                 m1_exitSW HSW HS HJ KM AG EW Hpre Hcut0 1%nat U9f Rs5 Rs6 Rs9 U22f MR ML.
             +++ m1_bres HS Hv2 Hc VZ.
                 assert (HMe : CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src (x_FB cx)) = false).
                 { destruct (CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src (x_FB cx))) eqn:Eb;
                     [|reflexivity].
                   exfalso. apply VZ. apply (proj2 Hcmp2).
                   apply (proj2 (m1_lk_iff cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hcut0 Lb Hk0 HL)). exact Eb. }
                 destruct (m1_mod_rej cx Lb Hk1 HUe HL Hlvn HMe) as (MR & MO & ML).
                 paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_X; [solve [m1_awr cx U9f] |].
                 m1_step0 KM U9f.
                 m1_exitX HX HS HJ KM AG EW Hpre Hcut0 MR MO ML.
      ++ psrr_branch_tok RUN BR HS SHOK m1_span.
         2:{ exfalso. rewrite branch_eq_U, (U_atom E 23 (x_lk cx) E23 ltac:(lia)), U_SLit in Hc.
             rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc. exact (Hc HLm). }
         clear Hc.
         destruct (m1_mod_none cx Hk1 HUe HL) as (MR & ML0).
         assert (ML : cLock cx = x_L cx) by (rewrite ML0, HL; reflexivity).
         paj_run_to_tok RUNTO HS HJ SHOK m1_span PC_SW; [solve [m1_awr cx U9b] |].
         m1_step0 KM U9b.
         m1_exitSW HSW HS HJ KM AG EW Hpre Hcut0 0%nat U9b Rs5 Rs6 Rs9 U22b MR ML.
Qed.

End h.
End f.
End d.

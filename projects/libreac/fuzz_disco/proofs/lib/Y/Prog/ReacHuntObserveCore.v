(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 294 of its 342 lines of code are new or changed and 3292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntObserve.v; 426 of its 617 lines of code are new or changed and 151 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition REAC_HUNT_OBSERVE_FRAME : Z := 176.
Definition REAC_HUNT_OBSERVE_STK : Z := REAC_HUNT_OBSERVE_FRAME + CLS_STK.
Definition REAC_HUNT_OBSERVE_DEPTH : Z := CLS_DEPTH - 1.

Definition tho_wr (h out a : Z) : Prop := (h <= a < h + 480) \/ (out <> 0 /\ out <= a < out + 24).

Definition tho_model (H FB O : list byte) (len now out r : Z) (H' : list byte) (OUT : list byte -> Prop) : Prop :=
  let L := reac_frame_clean_len_c.reac_frame_clean_len_model len in
  let T := disco_table_c.sub H 0 400 in
  let U := disco_table_c.sub H 412 6 in
  let Lk := Some (disco_table_c.sub H 400 12) in
  let Lk' := match disco_classify_c.cm_lock FB L U Lk with Some x => x | None => disco_table_c.sub H 400 12 end in
  (disco_classify_c.cm_ret FB L U Lk <> 0 ->
     r = -1 /\ H' = T ++ Lk' ++ skipn 412 H /\ (out <> 0 -> OUT O)) /\
  (disco_classify_c.cm_ret FB L U Lk = 0 ->
     exists T' c, reac_disco_table_observe_c.observe_model T (disco_classify_c.sight FB L) 0 now T' c /\
       r = (if c =? 0 then 0 else 1) /\
       H' = T' ++ Lk' ++ disco_table_c.sub H 412 12 ++
            (if disco_table_c.n_of T =? 0 then Mem.le8 (Z_to_bv 64 now) else disco_table_c.sub H 424 8) ++
            skipn 432 H /\
       (out <> 0 -> exists A, reac_hunt_observe_c.ho_answer T' (disco_classify_c.sight FB L) A /\ OUT A /\
                              reac_hunt_observe_c.ho_facts H FB L T A)).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.

Definition tho_out (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp out : Z) (O : list byte) : Prop :=
  out mod 8 = 0 /\ out + 24 <= 2 ^ 63 /\ amem_range out 24 /\
  (sp <= out \/ out + 24 <= sp - REAC_HUNT_OBSERVE_STK) /\ cls_sep B lyc Sc out 24 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF out 24 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) out 24 /\
  (forall a, out <= a < out + 24 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  length O = 24%nat /\ garr8 SEGS (mrestrict (w_H W) memc) out (map (fun b : byte => bv_unsigned b) O) /\
  ((exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= out /\
      out + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= out /\ out + 24 <= b + req_size m)).

Definition treac_hunt_observe_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp h out : Z) : Prop :=
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_HUNT_OBSERVE_STK <= a < sp) -> ~ tho_wr h out a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ tho_wr h out (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ tho_wr h out a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_HUNT_OBSERVE_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_HUNT_OBSERVE_STK <= a < sp -> apresent (w_H W2) mem2 a).

Definition treac_hunt_observe_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (h len now out : Z) (H FB O : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2 (r : Z) (H' : list byte),
    c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fq) k) /\
    (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ getr regs2 10 = w64 r /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_hunt_observe_kept lyc Sc W memc W2 mem2 (spZ regs) h out /\
    garr8 SEGS (mrestrict (w_H W2) mem2) h (map (fun b : byte => bv_unsigned b) H') /\ hunt_c.hunt_ok H' /\
    (r = -1 \/ r = 0 \/ r = 1) /\
    tho_model H FB O len now out r H'
      (fun A => garr8 SEGS (mrestrict (w_H W2) mem2) out (map (fun b : byte => bv_unsigned b) A)).

Definition treac_hunt_observe_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
         (h f len now out hb hn : Z) (H FB O : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= REAC_HUNT_OBSERVE_DEPTH ->
  getr regs 10 = w64 h -> getr regs 11 = w64 f -> getr regs 12 = w64 len ->
  getr regs 13 = w64 now -> getr regs 14 = w64 out ->
  0 <= len < 2 ^ 64 -> 0 <= now < 2 ^ 64 -> 0 <= out < 2 ^ 64 ->
  0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  (forall a, h <= a < h + 480 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  hunt_c.hunt_ok H ->
  garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) H) ->
  length FB = 50%nat ->
  (50 <= len -> 0 < f /\
     (exists fb fn, In (fb, fn) (ablocks B lyc Sc) /\ fb <= f /\ f + 50 <= fb + req_size fn) /\
     (f + 50 <= h \/ h + 480 <= f) /\
     garr8 SEGS (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) FB)) ->
  (out <> 0 -> tho_out STK sp0 FP ly S own lyc Sc W memc (spZ regs) out O /\
     (out + 24 <= h \/ h + 480 <= out) /\ (50 <= len -> out + 24 <= f \/ f + 50 <= out)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_hunt_observe) regs memc mdc)
    (treac_hunt_observe_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs h len now out H FB O).

Lemma le4_bytes_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  YG0f.le_byte v 4 k = nth k (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 v))) 0.
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia.
unfold YG0f.le_byte. rewrite (Z.mod_small v) by (cbn [Z.of_nat Z.mul]; lia).
destruct k as [|[|[|[|k]]]]; try (exfalso; lia);
cbn [Z_to_le_bytes map nth Z.of_nat Z.mul];
rewrite ?Z.shiftr_0_r, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; reflexivity.
Qed.

Lemma val_mem_of_garr8_4 : forall m a v,
  0 <= v < 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 v))) ->
  val_mem SEGS m a 4 v.
Proof.
intros m a v Hv HG k Hk.
assert (HL : (k < length (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 v))))%nat)
by (rewrite length_map, Mem.length_le4; exact Hk).
rewrite (garr8_mbyte SEGS m a _ k HG HL). f_equal. f_equal. symmetry. apply le4_bytes_nth; [lia | exact Hk].
Qed.

Lemma ho_count : forall m h (H : list byte),
  hunt_c.hunt_ok H ->
  garr8 SEGS m h (map (fun b : byte => bv_unsigned b) H) ->
  0 <= disco_table_c.n_of (disco_table_c.sub H 0 400) <= 8 /\
  val_mem SEGS m (h + 384) 4 (disco_table_c.n_of (disco_table_c.sub H 0 400)).
Proof.
intros m h H HOK HG.
destruct HOK as (HL & HT & _ & _).
assert (HTe : disco_table_c.sub H 0 400 = firstn 400 H)
by (unfold disco_table_c.sub; cbn [Z.to_nat skipn]; reflexivity).
assert (Hn : 0 <= disco_table_c.n_of (disco_table_c.sub H 0 400) <= 8)
by (rewrite HTe; destruct HT as (HT1 & _); exact HT1).
split; [exact Hn|].
set (v := disco_table_c.n_of (disco_table_c.sub H 0 400)) in *.
assert (HLT : length (disco_table_c.sub H 0 400) = 400%nat)
by (rewrite HTe, length_firstn; lia).
assert (HL4 : length (disco_table_c.sub (disco_table_c.sub H 0 400) 384 4) = 4%nat)
by (apply HuntObsLib.len_sub; [lia | rewrite HLT; cbn; lia]).
assert (Hle : Mem.le4 (Z_to_bv 64 v) = disco_table_c.sub (disco_table_c.sub H 0 400) 384 4).
{ unfold v, disco_table_c.n_of, disco_table_c.s32_at, disco_table_c.u_at.
  apply HuntObsFacts.le4_lw. exact HL4. }
assert (Hsub : disco_table_c.sub (disco_table_c.sub H 0 400) 384 4 = disco_table_c.sub H 384 4)
by (rewrite (HuntObsLib.sub_sub H 0 400 384 4 ltac:(lia) ltac:(lia) ltac:(cbn; lia)); reflexivity).
apply val_mem_of_garr8_4; [cbn; lia|].
rewrite Hle, Hsub.
assert (HGm : garr8 SEGS m (h + Z.of_nat 384) (firstn 4 (skipn 384 (map (fun b : byte => bv_unsigned b) H))))
by (apply garr8_sub_x; [exact HG | rewrite length_map; lia]).
replace (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H 384 4))
  with (firstn 4 (skipn 384 (map (fun b : byte => bv_unsigned b) H))).
- replace (h + 384) with (h + Z.of_nat 384) by (cbn; lia). exact HGm.
- unfold disco_table_c.sub. cbn [Z.to_nat].
  rewrite skipn_map, firstn_map. reflexivity.
Qed.

Definition HOBx : sv := SOff 32 0.
Definition HOspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ho_extra (n uar : Z) : list word := map (Z_to_bv 64) ([SB; n] ++ repeat 0 25 ++ [uar]).
Definition EHO (regs : bvmap 5 word) (n uar : Z) : env := Eimg (Ereg regs (ho_extra n uar)).
Definition ho_hregion : YP09.region := YP09.mkRegion (Some 10%nat) 0 480 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))].
Definition ho_regions : smem :=
  [ stack_region REAC_HUNT_OBSERVE_FRAME; got_regionP; bcell_regionP 32; uar_got_regionP 59; uar_cell_regionP 59; ho_hregion ].
Definition ho_atoms0 : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, HPTR 3); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0);
    (59%nat, mkAF YImgTop.IMG_LO YImgTop.IMG_TOP 2) ].
Definition ss_ho : sstate := mkSS AF_both3_reac_hunt_observe sr_atoms ho_regions None (mkFacts ho_atoms0 [] []).
Definition ho_SH : list shent := [ mkSHE 10 0 480 ].

Lemma ho_shent_gen : forall E (Hv : word -> bool) (mm : word -> option byte) (mnum : nat) (p lo hi : Z),
  ew E 32 = Z_to_bv 64 SB -> ew E mnum = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  lo <= hi -> amem_range (p + lo) (hi - lo) ->
  range_addressable (aview SEGS Hv mm) SHADOW_OFF (p + lo) (hi - lo) ->
  shent_ok SEGS HOBx E (mrestrict Hv mm) (mkSHE mnum lo hi).
Proof.
intros E Hv mm mnum p lo hi E32 Em Hp Hlh Ham Hra.
assert (HB : U E HOBx = SHADOW_OFF)
by (unfold HOBx; rewrite U_SOff, E32, unsigned_lit_small by (unfold SB; lia); rewrite Z.add_0_r;
    apply zcanon_id; unfold SB, SHADOW_OFF, M64; lia).
assert (HU : U E (SOff mnum 0) = p)
by (rewrite U_SOff, Em, unsigned_lit_small by lia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, HU. split.
- rewrite <- (aview_rd_of SEGS). exact Hra.
- intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. unfold SHADOW_OFF. lia.
Qed.

Lemma ho_firstn_exact : forall (a b : list byte) n, length a = n -> firstn n (a ++ b) = a.
Proof. intros a b n <-. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. Qed.

Lemma ho_skipn_exact : forall (a b : list byte) n, length a = n -> skipn n (a ++ b) = b.
Proof. intros a b n <-. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma ho_hok_gen : forall (Hh T' Lk' Rest : list byte), length Hh = 480%nat -> hunt_c.hunt_ok Hh ->
  length T' = 400%nat -> disco_table_c.table_ok T' ->
  length Lk' = 12%nat -> disco_classify_c.lock_ok Lk' -> length Rest = 68%nat ->
  disco_table_c.sub Rest 28 4 = disco_table_c.sub Hh 440 4 ->
  hunt_c.hunt_ok (T' ++ Lk' ++ Rest).
Proof.
  intros Hh T' Lk' Rest LH (_ & _ & _ & V) LT TOK LL LOK LR SR.
  split; [rewrite !length_app; lia|]. split; [|split].
  - rewrite (ho_firstn_exact T' (Lk' ++ Rest) 400 LT). exact TOK.
  - rewrite (ho_skipn_exact T' (Lk' ++ Rest) 400 LT). rewrite (ho_firstn_exact Lk' Rest 12 LL). exact LOK.
  - unfold disco_table_c.s32_at, disco_table_c.u_at in V |- *.
    rewrite HuntObsLib.sub_app_r by lia. rewrite LT. rewrite HuntObsLib.sub_app_r by lia. rewrite LL.
    replace (440 - Z.of_nat 400 - Z.of_nat 12) with 28 by lia. rewrite SR. exact V.
Qed.

Lemma tho_model_ok : forall (Hh FB O : list byte) (len now out : Z) (Lk' T' : list byte) (c : Z)
    (OUT : list byte -> Prop),
  disco_classify_c.cm_ret FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 412 6) (Some (disco_table_c.sub Hh 400 12)) = 0 ->
  disco_classify_c.cm_lock FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 412 6) (Some (disco_table_c.sub Hh 400 12)) = Some Lk' ->
  reac_disco_table_observe_c.observe_model (disco_table_c.sub Hh 0 400)
    (disco_classify_c.sight FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)) 0 now T' c ->
  (out <> 0 -> exists A, reac_hunt_observe_c.ho_answer T'
     (disco_classify_c.sight FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)) A /\ OUT A /\
     reac_hunt_observe_c.ho_facts Hh FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
       (disco_table_c.sub Hh 0 400) A) ->
  tho_model Hh FB O len now out (if c =? 0 then 0 else 1)
    (T' ++ Lk' ++ disco_table_c.sub Hh 412 12 ++
     (if disco_table_c.n_of (disco_table_c.sub Hh 0 400) =? 0
      then Mem.le8 (Z_to_bv 64 now) else disco_table_c.sub Hh 424 8) ++ skipn 432 Hh) OUT.
Proof.
  intros Hh FB O len now out Lk' T' c OUT R EL OM ANS. unfold tho_model. cbv zeta. rewrite EL. split.
  - intros X. contradiction.
  - intros _. exists T', c. split; [exact OM|]. split; [reflexivity|]. split; [reflexivity|]. exact ANS.
Qed.

Record hoC : Type := mkHoC {
  c_fq : YK11.FPState; c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z);
  c_ly : alayout; c_S : astate; c_W0 : world SEGS; c_mem0 : word -> option byte; c_md0 : Model;
  c_own : list (Z * Z); c_lyc : alayout; c_Sc : astate; c_W : world SEGS;
  c_memc : word -> option byte; c_k : Z; c_regs : bvmap 5 word;
  c_h : Z; c_f : Z; c_len : Z; c_now : Z; c_out : Z; c_hb : Z; c_hn : Z;
  c_H : list byte; c_FB : list byte; c_O : list byte }.

Definition ho_pre (c : hoC) : Prop :=
  (exists mdc, ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
     (c_own c) (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc (c_k c)) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W c)) (c_memc c)) /\
  YK0s.ret_ok (getr (c_regs c) 1) /\ 4096 <= raZ (c_regs c) /\
  getr (c_regs c) 3 = w64 (as_gp B) /\ getr (c_regs c) 4 = w64 (as_tp B) /\
  spZ (c_regs c) mod 16 = 0 /\
  c_sp0 c - c_STK c <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\ spZ (c_regs c) <= c_sp0 c /\
  Z.of_nat (length (frames (c_Sc c))) <= REAC_HUNT_OBSERVE_DEPTH /\
  0 <= c_len c < 2 ^ 64 /\ 0 <= c_now c < 2 ^ 64 /\ 0 <= c_out c < 2 ^ 64 /\
  0 < c_h c /\ c_h c mod 8 = 0 /\
  In (c_hb c, c_hn c) (ablocks B (c_lyc c) (c_Sc c)) /\ c_hb c <= c_h c /\
  c_h c + 480 <= c_hb c + req_size (c_hn c) /\
  (forall a, c_h c <= a < c_h c + 480 ->
     awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
       (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c) a) /\
  hunt_c.hunt_ok (c_H c) /\ length (c_FB c) = 50%nat /\
  garr8 SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (c_h c)
    (map (fun b : byte => bv_unsigned b) (c_H c)) /\
  (50 <= c_len c -> 0 < c_f c /\
     (exists fb fn, In (fb, fn) (ablocks B (c_lyc c) (c_Sc c)) /\ fb <= c_f c /\
        c_f c + 50 <= fb + req_size fn) /\
     (c_f c + 50 <= c_h c \/ c_h c + 480 <= c_f c) /\
     garr8 SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (c_f c)
       (map (fun b : byte => bv_unsigned b) (c_FB c))) /\
  (c_out c <> 0 ->
     tho_out (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_own c) (c_lyc c) (c_Sc c)
       (c_W c) (c_memc c) (spZ (c_regs c)) (c_out c) (c_O c) /\
     (c_out c + 24 <= c_h c \/ c_h c + 480 <= c_out c) /\
     (50 <= c_len c -> c_out c + 24 <= c_f c \/ c_f c + 50 <= c_out c)) /\
  val_mem SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM /\
  val_mem SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT.

Definition ho_post (c : hoC) : world SEGS -> config -> Prop :=
  treac_hunt_observe_post (c_fq c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c)
    (c_mem0 c) (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) (c_W c) (c_memc c) (c_k c) (c_regs c)
    (c_h c) (c_len c) (c_now c) (c_out c) (c_H c) (c_FB c) (c_O c).

Definition ho_mid (c : hoC) (fpos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) (k2 : Z) (H2 : list byte) : Prop :=
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem2 md2 k2 /\
  frames S2 = (1, fpos) :: frames (c_Sc c) /\
  (forall cid p, frame_addr ly2 cid p = frame_addr (c_lyc c) cid p) /\
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) /\
  treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem2
    (spZ (c_regs c)) (c_h c) (c_out c) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_h c) (map (fun b : byte => bv_unsigned b) H2) /\
  length H2 = 480%nat /\
  rdword (aview SEGS (w_H W2) mem2) (frame_addr ly2 1 fpos + 120) = Some (flag_addr ly2 1 fpos) /\
  k2 <= c_k c.

Definition ho_fsh (W2 : world SEGS) (mem2 : word -> option byte) (F : Z) (SH : list Z) : Prop :=
  forall i, 0 <= i < 16 -> aview SEGS (w_H W2) mem2 (SB + F / 8 + i) = Some (nth (Z.to_nat i) SH 0).

Definition ho_sreg (j : nat) : bv 5 :=
  nth j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv 0%bv.

Definition ho_saved (c : hoC) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
    val_mem SEGS (mrestrict (w_H W2) mem2) (spZ (c_regs c) - 8 * (Z.of_nat j + 1)) 8
      (bv_unsigned (getr (c_regs c) (ho_sreg j))).

Definition ho_regs_mid (c : hoC) (regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  getr regs2 2 = w64 sp1 /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  getr regs2 8 = w64 (spZ (c_regs c)) /\ getr regs2 9 = w64 sp1 /\
  getr regs2 18 = w64 F /\ getr regs2 21 = w64 (c_h c) /\
  getr regs2 24 = w64 (SB + F / 8) /\ getr regs2 25 = w64 F.

Definition ho_sp1 (c : hoC) (sp1 : Z) : Prop :=
  sp1 = 32 * ((spZ (c_regs c) + -160) / 32) /\
  spZ (c_regs c) - 176 <= sp1 <= spZ (c_regs c) - 160 /\ sp1 mod 32 = 0.

Definition ho_cfg (c : hoC) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  (md2 : Model) (af : Z) : config :=
  mkCfg (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)) md2.

Definition ho_base (c : hoC) (fpos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) (k2 : Z) (H2 : list byte)
  (regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  ho_pre c /\ ho_mid c fpos ly2 S2 W2 mem2 md2 k2 H2 /\ ho_sp1 c sp1 /\
  F = frame_addr (c_lyc c) 1 fpos /\ ho_regs_mid c regs2 sp1 F /\ ho_saved c W2 mem2.

Definition ho_shC : list Z := [241;241;241;241;0;0;0;243;243;243;243;243;0;0;0;0].

Definition ho_L (c : hoC) : Z := reac_frame_clean_len_c.reac_frame_clean_len_model (c_len c).
Definition ho_U (c : hoC) : list byte := disco_table_c.sub (c_H c) 412 6.
Definition ho_Lk (c : hoC) : option (list byte) := Some (disco_table_c.sub (c_H c) 400 12).
Definition ho_Lk' (c : hoC) : list byte :=
  match disco_classify_c.cm_lock (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) with
  | Some x => x | None => disco_table_c.sub (c_H c) 400 12 end.
Definition ho_Hcls (c : hoC) : list byte :=
  disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ skipn 412 (c_H c).

Definition ho_svals (c : hoC) : list Z :=
  map (fun j => bv_unsigned (getr (c_regs c) (ho_sreg j))) (List.seq 0 13).

Definition ho_extraM (c : hoC) (FL : Z) : list word :=
  map (Z_to_bv 64) ([SB; FL] ++ ho_svals c ++ repeat 0 12 ++ [as_uar_cell B]).

Definition EHOm (c : hoC) (regs2 : bvmap 5 word) (FL : Z) : env := Eimg (Ereg regs2 (ho_extraM c FL)).

Definition ho_svchunk (j : nat) : YP09.chunk := YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (34 + j) 0)).

Definition ho_saved_region : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 (map ho_svchunk (List.seq 0 13)).

Definition ho_shchunk (SH : list Z) (i : nat) : YP09.chunk :=
  YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i SH 0))).

Definition ho_fshadow_region (SH : list Z) : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 16 0 16 (map (ho_shchunk SH) (List.seq 0 16)).

Definition ho_frame_region : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 33 0))].

Definition ho_sp1_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 56 0 56 [].

Definition ho_hregM : YP09.region := YP09.mkRegion (Some 21%nat) 0 480 0 480 [].

Definition ho_outreg : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 0 24 [].

Definition ho_regionsM (SH : list Z) (wo : bool) : smem :=
  (if wo then [ho_outreg] else []) ++
  [ ho_sp1_region; ho_saved_region; got_regionP; bcell_regionP 32; uar_got_regionP 59; uar_cell_regionP 59;
    ho_frame_region; ho_fshadow_region SH; ho_hregM ].

Definition ho_atomsM (wo : bool) : list (nat * afact) :=
  (if wo then [(19%nat, HPTR 3)] else []) ++
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
    (18%nat, HPTR 5); (21%nat, HPTR 3); (24%nat, mkAF (SB + 512) (SB + 17592186044416) 2);
    (25%nat, HPTR 5); (32%nat, mkAF SB SB 0); (33%nat, HPTR 0);
    (59%nat, mkAF YImgTop.IMG_LO YImgTop.IMG_TOP 2) ].

Definition ss_hoM (SH : list Z) (wo : bool) (af : Z) : sstate :=
  mkSS af sr_atoms (ho_regionsM SH wo) None (mkFacts (ho_atomsM wo) [] []).

Definition ho_seg_C_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (c_H c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 22 = w64 (c_f c) -> getr regs2 23 = w64 (c_len c) -> getr regs2 26 = w64 SB ->
  ho_fsh W2 mem2 F ho_shC ->
  (exists ch, achain ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x730c) (ho_post c).

Definition ho_seg_E_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (ho_Hcls c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 26 = w64 SB ->
  ho_fsh W2 mem2 F ho_shC ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  hunt_c.hunt_ok (ho_Hcls c) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x73b4) (ho_post c).

Definition ho_seg_F_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' ret,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 10 = w64 ret -> 0 <= ret < 2 ^ 64 ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 22 = w64 (c_h c + 384) -> getr regs2 23 = w64 (F + 32) ->
  getr regs2 27 = w64 (SB + (c_h c + 384) / 8) -> getr regs2 26 = w64 SB ->
  ho_fsh W2 mem2 F ho_shC -> hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  reac_disco_table_observe_c.observe_model (disco_table_c.sub (c_H c) 0 400)
    (disco_classify_c.sight (c_FB c) (ho_L c)) 0 (c_now c) T' ret ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  skipn 400 H2 = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
    (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
     then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ++ skipn 432 (c_H c) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x73fc) (ho_post c).

Definition ho_seg_G_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 19 = w64 (48 * nn) -> getr regs2 20 = w64 (2 ^ 64 - 1 - c_h c) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 26 = w64 432 -> getr regs2 27 = w64 (48 * ii) ->
  ho_fsh W2 mem2 F ho_shC -> hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  nn = disco_table_c.n_of T' -> 0 <= ii < nn -> 0 < nn <= 8 ->
  (r = 0 \/ r = 1) ->
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 8) = Some SB ->
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 16) = Some (c_out c) ->
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 24) = Some r ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) ->
  length G = 24%nat -> G = disco_classify_c.sight (c_FB c) (ho_L c) ->
  (forall j, 0 <= j < ii -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G) ->
  c_out c <> 0 ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) ->
  (forall A, reac_hunt_observe_c.ho_answer T' G A ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = A)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7448) (ho_post c).

Definition ho_seg_T_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 r,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 20 = w64 r -> (r = -1 \/ r = 0 \/ r = 1) ->
  ho_fsh W2 mem2 F ho_shC ->
  hunt_c.hunt_ok H2 ->
  tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
    (fun A => garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
       (map (fun b : byte => bv_unsigned b) A)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7344) (ho_post c).
Definition ho_seg_A_stmt : Prop := ho_seg_C_stmt -> treac_hunt_observe_spec.

Definition ho_SHM (wo : bool) : list shent := (if wo then [mkSHE 19 0 24] else []) ++ [mkSHE 21 0 480].
Lemma hoT_aview_frame : forall E rs (Wx : world SEGS) ma mb a,
  frame_of E rs (mrestrict (w_H Wx) ma) (mrestrict (w_H Wx) mb) -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a.
Proof.
intros E rs Wx ma mb a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.

Lemma hoT_garr_kept : forall (Wx : world SEGS) ma mb a l,
  (forall i, a <= i < a + Z.of_nat (length l) -> aview SEGS (w_H Wx) mb i = aview SEGS (w_H Wx) ma i) ->
  garr8 SEGS (mrestrict (w_H Wx) ma) a l -> garr8 SEGS (mrestrict (w_H Wx) mb) a l.
Proof.
intros Wx ma mb a l HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. rewrite <- (Hv kk Hk). apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Definition hoG_box (P : Prop) : Prop := P.

Definition hoG_sp1R : YP09.region := YP09.mkRegion (Some 9%nat) 0 56 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 19 0)); YP09.mkChunk 24 (CVal 8 (SOff 61 0))].
Definition hoG_rowR : YP09.region := YP09.mkRegion (Some 22%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 62 0)); YP09.mkChunk 12 (CVal 1 (SOff 63 0)); YP09.mkChunk 13 (CVal 1 (SOff 64 0));
   YP09.mkChunk 14 (CVal 1 (SOff 65 0)); YP09.mkChunk 15 (CVal 1 (SOff 66 0)); YP09.mkChunk 16 (CVal 1 (SOff 67 0));
   YP09.mkChunk 20 (CVal 4 (SOff 68 0))].
Definition hoG_outA : YP09.region := YP09.mkRegion (Some 19%nat) 8 17 8 17 [].
Definition hoG_outB : YP09.region := YP09.mkRegion (Some 19%nat) 20 24 20 24 [].
Definition hoG_ws (nn r ii : Z) (H2 : list byte) : list word :=
  map (Z_to_bv 64) [48 * nn; r;
    bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 8) 4); bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 12) 1);
    bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 13) 1); bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 14) 1);
    bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 15) 1); bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 16) 1);
    bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 20) 4)].

Definition hoG_pre (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem2 md2 k2 (regs2 : bvmap 5 word) sp1 F
  (H2 T' G : list byte) (r nn ii : Z) : Prop :=
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F /\
  getr regs2 19 = w64 (48 * nn) /\ getr regs2 20 = w64 (2 ^ 64 - 1 - c_h c) /\
  getr regs2 23 = w64 (F + 32) /\ getr regs2 26 = w64 432 /\ getr regs2 27 = w64 (48 * ii) /\
  ho_fsh W2 mem2 F ho_shC /\ hunt_c.hunt_ok H2 /\
  H2 = T' ++ skipn 400 H2 /\ length T' = 400%nat /\
  nn = disco_table_c.n_of T' /\ 0 <= ii < nn /\ 0 < nn <= 8 /\
  (r = 0 \/ r = 1) /\
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 8) = Some SB /\
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 16) = Some (c_out c) /\
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 24) = Some r /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) /\
  length G = 24%nat /\ G = disco_classify_c.sight (c_FB c) (ho_L c) /\
  (forall j, 0 <= j < ii -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G) /\
  c_out c <> 0 /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) /\
  (forall A, reac_hunt_observe_c.ho_answer T' G A ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = A)).

Definition hoG_head_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii,
  hoG_pre c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii ->
  (forall regs4 mem4 md4 (v : word),
     hoG_pre c fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii ->
     getr regs4 10 = v -> (v = w64 0 <-> disco_table_c.mac_of T' ii = disco_table_c.s_mac G) ->
     getr regs4 22 = w64 (c_h c + 48 * ii) ->
     SRr SEGS W2 (ho_cfg c regs4 mem4 md4 0x7464) (ho_post c)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7448) (ho_post c).

Definition hoG_ret_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii (v : word),
  hoG_pre c fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii ->
  getr regs4 10 = v -> (v = w64 0 <-> disco_table_c.mac_of T' ii = disco_table_c.s_mac G) ->
  getr regs4 22 = w64 (c_h c + 48 * ii) ->
  (ii + 1 < nn -> forall regs5 mem5 md5,
     hoG_pre c fpos ly2 S2 W2 mem5 md5 k2 regs5 sp1 F H2 T' G r nn (ii + 1) ->
     SRr SEGS W2 (ho_cfg c regs5 mem5 md5 0x7448) (ho_post c)) ->
  SRr SEGS W2 (ho_cfg c regs4 mem4 md4 0x7464) (ho_post c).

Definition ho_setfq (c : hoC) (fx : YK11.FPState) : hoC :=
  mkHoC fx (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) (c_own c)
    (c_lyc c) (c_Sc c) (c_W c) (c_memc c) (c_k c) (c_regs c) (c_h c) (c_f c) (c_len c) (c_now c)
    (c_out c) (c_hb c) (c_hn c) (c_H c) (c_FB c) (c_O c).

Lemma hoEF_awr_mid : forall STK sp0 FP bl0 blc blc' ly ly' own x a,
  (forall p : Z * Z, In p blc -> In p blc') ->
  (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own x a Hb Hfa
  [H | [(HFP & b & m & Hin & Hr) | [(b & m & Hin & Hni & Hr) | (cid & pos & Hin & Hr)]]].
- left; exact H.
- right; left. split; [exact HFP|]. exists b, m. split; [apply Hb; exact Hin | exact Hr].
- right; right; left. exists b, m. split; [apply Hb; exact Hin|]. split; [exact Hni | exact Hr].
- right; right; right. exists cid, pos. split; [right; exact Hin|]. rewrite (Hfa cid pos). exact Hr.
Qed.

Lemma hoEF_region_win : forall E m (nn : nat) lo hi wlo whi cs wlo' whi',
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo' whi' cs).
Proof.
intros E m nn lo hi wlo whi cs wlo' whi' (A1 & A2 & A3 & A4) HW.
split; [exact A1|]. split; [exact A2|]. split; [|exact A4].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in A3 |- *.
intros o Ho. apply A3. destruct HW as [HW | [HW1 HW2]]; lia.
Qed.

Lemma hoEF_region_wc : forall E m (nn : nat) lo hi wlo whi cs wlo' whi' ch,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  YP09.chunk_ok SEGS E m (base_val E (Some nn)) ch ->
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo' whi' (ch :: cs)).
Proof.
intros E m nn lo hi wlo whi cs wlo' whi' ch HR HW Hch.
destruct (hoEF_region_win E m nn lo hi wlo whi cs wlo' whi' HR HW) as (A1 & A2 & A3 & A4).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
apply Forall_cons; [exact Hch | exact A4].
Qed.

Lemma hoF_e32 : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 32 = Z_to_bv 64 SB.
Proof.
intros c regs2 FL. unfold EHOm. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 _ 0).
Qed.

Lemma hoF_u_shadow : forall E (n m : nat) p off b,
  ew E n = Z_to_bv 64 p -> ew E m = Z_to_bv 64 b ->
  0 <= p -> 0 <= off -> p + off < 2 ^ 64 -> 0 <= b -> b + (p + off) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n off) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (b + (p + off) / 8).
Proof.
intros E n m p off b En Em Hp Ho Hpo Hb Hs.
pose proof (Z.div_pos (p + off) 8 ltac:(lia) ltac:(lia)) as Hd.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit, En, Em.
rewrite !unsigned_lit_small by lia.
cbn [zalu_raw].
change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.add_0_r.
rewrite (zcanon_id (p + off)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + off) / 8)) by (unfold M64; lia).
rewrite (zcanon_id b) by (unfold M64; lia).
transitivity ((p + off) / 8 + b); [apply zcanon_id; unfold M64; lia | lia].
Qed.

Lemma hoF_val_mem_ext : forall (Wx : world SEGS) ma mb a (n : nat) v,
  (forall k, (k < n)%nat -> aview SEGS (w_H Wx) mb (a + Z.of_nat k) = aview SEGS (w_H Wx) ma (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H Wx) ma) a n v -> val_mem SEGS (mrestrict (w_H Wx) mb) a n v.
Proof.
intros Wx ma mb a n v HE Hv k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview SEGS). exact (HE k Hk).
Qed.

Lemma hoF_garr_ext : forall (Wx : world SEGS) ma mb a l,
  (forall i, a <= i < a + Z.of_nat (length l) -> aview SEGS (w_H Wx) mb i = aview SEGS (w_H Wx) ma i) ->
  garr8 SEGS (mrestrict (w_H Wx) ma) a l -> garr8 SEGS (mrestrict (w_H Wx) mb) a l.
Proof.
intros Wx ma mb a l HE HGa j Hj. destruct (HGa j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. rewrite <- (Hv kk Hk). apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Lemma hoF_aview_frame : forall E rs (Wx : world SEGS) ma mb a,
  frame_of E rs (mrestrict (w_H Wx) ma) (mrestrict (w_H Wx) mb) -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a.
Proof.
intros E rs Wx ma mb a HFo Ha Hn. unfold aview, mbyte.
rewrite (HFo (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.

Lemma hoF_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

End h.
End f.
End d.

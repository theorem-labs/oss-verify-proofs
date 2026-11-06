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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntObserve.v; 33 of its 165 lines of code are new or changed and 210 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen ReacHuntObserveSeg_ent ReacHuntObserveSeg_mid ReacHuntObserveSeg_T ReacHuntObserveSeg_G ReacHuntObserveSeg_Cc ReacHuntObserveSeg_C ReacHuntObserveSeg_F ReacHuntObserveSeg_E ReacHuntObserveSeg_A.
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

#[local] Notation ho_entry := (@ReacHuntObserveSeg_ent.ho_entry rc SK PI B LAWS TL TLF).
#[local] Notation ho_mid_entry := (@ReacHuntObserveSeg_mid.ho_mid_entry rc SK PI B LAWS TL TLF FFL).
#[local] Notation ho_shokM := (@ReacHuntObserveSeg_mid.ho_shokM rc SK PI B LAWS FFL).
#[local] Notation ho_segT := (@ReacHuntObserveSeg_T.ho_segT rc SK PI B LAWS TLF ML ASF FFL ho_mid_entry).
#[local] Notation ho_segG := (@ReacHuntObserveSeg_G.ho_segG rc SK PI B LAWS ABCMP ho_mid_entry ho_shokM ho_segT).
#[local] Notation hoF_ereg := (@ReacHuntObserveSeg_F.hoF_ereg rc PI B).
#[local] Notation ho_segF := (@ReacHuntObserveSeg_F.ho_segF rc SK PI B LAWS AMEMCPY ho_mid_entry ho_shokM ho_segT ho_segG).
#[local] Notation ho_segE := (@ReacHuntObserveSeg_E.ho_segE rc SK PI PX B LAWS TOBS ho_mid_entry hoF_ereg ho_segF).
#[local] Notation hoC_call := (@ReacHuntObserveSeg_Cc.hoC_call rc SK PI B LAWS TCOS).
#[local] Notation ho_seg_C := (@ReacHuntObserveSeg_C.ho_seg_C rc SK PI PX PO B LAWS hoC_call).
#[local] Notation ho_segA := (@ReacHuntObserveSeg_A.ho_segA rc SK PI PO PW PV B LAWS TL TLF ML ASM1 SMP FFL HRO ho_entry).

Theorem pb_reac_hunt_observe : treac_hunt_observe_spec.
Proof. exact (ho_segA (ho_seg_C ho_segE ho_segT)). Qed.

End h.
End f.
End d.

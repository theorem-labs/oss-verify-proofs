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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
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
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.

Definition tho_out (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp out : Z) (O : list byte) : Prop :=
  out mod 8 = 0 /\ out + 24 <= 2 ^ 63 /\ amem_range out 24 /\
  (sp <= out \/ out + 24 <= sp - REAC_HUNT_OBSERVE_STK) /\ cls_sep B lyc Sc out 24 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF out 24 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) out 24 /\
  (forall a, out <= a < out + 24 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  length O = 24%nat /\ garr8 SEGS (mrestrict (w_H W) memc) out (map (fun b : byte => bv_unsigned b) O) /\
  ((exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= out /\ out + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_hunt_observe) regs memc mdc)
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

Definition HOx : sv := SOff 32 0.
Definition HOspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ho_extra (n : Z) : list word := map (Z_to_bv 64) [SB; n].
Definition EHO (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (ho_extra n)).
Definition ho_regions : smem :=
  [ stack_region REAC_HUNT_OBSERVE_FRAME; got_regionP; bcell_regionP 32;
    uar_got_regionP (A_OBJ 67); uar_cell_regionP (A_OBJ 67);
    YP09.mkRegion (Some 10%nat) 0 480 0 480 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))] ].
Definition ho_facts0 : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3);
            (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0) ] [] [].
Definition ss_ho : sstate := mkSS AF_reac_hunt_observe sr_atoms ho_regions None ho_facts0.
Definition ho_SH : list shent := [ mkSHE 10 0 480 ].

Lemma regs_ok_EHO : forall regs n, regs_ok (EHO regs n) sr_atoms regs.
Proof.
intros. unfold EHO. apply (regs_ok_agree 32 (Ereg regs (ho_extra n))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.

Lemma ho_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) (h n hb hn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 h ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> h mod 8 = 0 -> 0 <= n <= 8 ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (EHO regs n) ss_ho
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_hunt_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HOx ho_SH (EHO regs n) (mrestrict (w_H W) memc).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs h n hb hn
HJ H10 Hal16 Hwin Hsp Hin Hhb Hhe Hh0 Hh8 Hn HV.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfr : REAC_HUNT_OBSERVE_STK = REAC_HUNT_OBSERVE_FRAME + CLS_STK) by reflexivity.
assert (Hcls : 0 <= CLS_STK)
by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia).
assert (Hfr0 : REAC_HUNT_OBSERVE_FRAME = 176) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
pose proof (pa_obj_img 0%nat ltac:(unfold disco_nobj; lia)) as Hob0.
pose proof (pa_obj_img 1%nat ltac:(unfold disco_nobj; lia)) as Hob1.
pose proof (pa_obj_img 66%nat ltac:(unfold disco_nobj; lia)) as Hob66.
pose proof (palf_uar_img B TL) as Huar. rewrite (pal_uar_cell B TL) in Huar.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := EHO regs n).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (ho_extra n)) m)
by (intros m Hm; subst E; unfold EHO; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO67 : ew E (A_OBJ 67) = Z_to_bv 64 (VAL (A_OBJ 67)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 66)) as VR66.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
unfold off_img, IMG_LO, IMG_TOP in *.
split.
- unfold ss_ho, ho_regions. apply pa_entry_st_ok_full.
  + apply regs_ok_EHO.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp, Hfr0.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite EO66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 HOx SB);
      [cbn [sv_denot HOx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 67) 0) (VAL (A_OBJ 67)));
      [cbn [sv_denot]; rewrite EO67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    * rewrite (VB (A_OBJ 67) (VAL (A_OBJ 67)) EO67) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 67)) 0 4 (SLit 1) 1); [reflexivity | lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
    * rewrite (VB 10%nat h E10) by lia.
      split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (apresent_writable SEGS). apply (fun Hq => proj1 (Hbpres (h + o) Hq)). lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ h 384 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         change (N.to_nat 4) with 4%nat. exact HV.
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat h E10) by lia. rewrite (VB (A_OBJ 67) (VAL (A_OBJ 67)) EO67) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
    cbn [base_val]. rewrite Usp, Hfr0.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + unfold ho_facts0. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
            split; [lia|]; split; [exact Hal16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; split; [lia|]; split; [exact Hh8 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
            rewrite Z.pow_0_r; split; [unfold SB; lia|]; split; [apply Z.mod_1_r | unfold SB; lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    exact I.
- unfold ho_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
  assert (HU10 : U E (SOff 10 0) = h) by (shent_U_norm; reflexivity).
  assert (HUB : U E HOx = SHADOW_OFF) by (unfold HOx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU10, HUB. split.
  + replace (h + 0) with h by lia. replace (480 - 0) with 480 by lia.
    apply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn h 480 HAR Hin); lia.
  + intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia.
Qed.
End h.
End f.
End d.

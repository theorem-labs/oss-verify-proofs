(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 227 of its 280 lines of code are new or changed and 3287 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Definition SB_DEC_STK : Z := 112 + ESTACK.
Definition tsb_dec_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (A v md p cap n over : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
       ~ (A + 16 <= a < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
       ~ (A + 16 <= b + i < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= b + i < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ (A + 16 <= a < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - SB_DEC_STK <= a < spZ regs -> apresent (w_H W2) mem2 a) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) A 8 p /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 8) 8 cap /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 24) 4
      (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else over) /\
    (0 < sb_dec_c.sb_dec_room cap n ->
       garr8 SEGS (mrestrict (w_H W2) mem2) (p + n)
         (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md))).
Definition tsb_dec_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (A v md p cap n over : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 A -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 9 ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  A mod 8 = 0 -> (in_app A 28 \/ (sp0 - STK <= A /\ A + 28 <= sp0)) -> A + 28 <= 2 ^ 63 -> (A + 28 <= IMG_LO \/ IMG_TOP <= A) ->
  (spZ regs <= A \/ A + 28 <= spZ regs - SB_DEC_STK) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < 2 ^ 64 - 3 -> 0 <= over < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 over ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  (forall a, A <= a < A + 28 -> apresent (w_H W) memc a) ->
  (forall a, A <= a < A + 28 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (0 < sb_dec_c.sb_dec_room cap n ->
     p + cap <= 2 ^ 64 /\ in_app (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= IMG_LO \/ IMG_TOP <= p + n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= A \/ A + 28 <= p + n) /\
     (spZ regs <= p + n \/ p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (forall a, p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec) regs memc mdc)
    (tsb_dec_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A v md p cap n over).
Definition sbd_regions : smem :=
  [ stack_region 112; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33;
    YP09.mkRegion (Some 10%nat) 0 28 16 28
      [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0));
       YP09.mkChunk 16 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 4 (SOff 37 0))] ].
Definition sbd_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737488355300 3);
            (32%nat, mkAF SB SB 0); (34%nat, mkAF 0 18446744073709551615 0);
            (35%nat, mkAF 0 18446744073709551615 0); (36%nat, mkAF 0 18446744073709551615 0);
            (37%nat, mkAF 0 4294967295 0) ] [] [].
Definition ss_sbd : sstate := mkSS AF_sb_dec sr_atoms sbd_regions None sbd_facts.
Definition SBx : sv := SOff 32 0.
Definition SBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sbd_SH : list shent := [ mkSHE 10 0 28 ].
Definition sbd_extra (p cap n over : Z) : list word := map (Z_to_bv 64) [SB; as_uar_cell B; p; cap; n; over].
Definition ESB (regs : bvmap 5 word) (p cap n over : Z) : env := Eimg (Ereg regs (sbd_extra p cap n over)).
Lemma regs_ok_ESB : forall regs p cap n over, regs_ok (ESB regs p cap n over) sr_atoms regs.
Proof.
intros. unfold ESB. apply (regs_ok_agree 32 (Ereg regs (sbd_extra p cap n over))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma sbd_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A p cap n over : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 A ->
  A mod 8 = 0 -> (in_app A 28 \/ (sp0 - STK <= A /\ A + 28 <= sp0)) -> A + 28 <= 2 ^ 63 -> (A + 28 <= IMG_LO \/ IMG_TOP <= A) ->
  (spZ regs <= A \/ A + 28 <= spZ regs - SB_DEC_STK) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= over < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 over ->
  (forall a, A <= a < A + 28 -> apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  st_ok_pi SEGS VAL (ESB regs p cap n over) ss_sbd
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_sb_dec)) memc (seg_rom SEGS))) /\
  sh_ok SEGS SBx sbd_SH (ESB regs p cap n over) (mrestrict (w_H W) memc).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n over
HJ H10 HA8 HAapp HA63 HAimg HAsp Rp Rcap Rn Rover Mp Mcap Mn Mover HApres HRA Hal16 Hbud Hsp.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL) in Kguar.
pose proof (pa_obj_img 0%nat ltac:(unfold disco_nobj; lia)) as Hob0.
pose proof (pa_obj_img 1%nat ltac:(unfold disco_nobj; lia)) as Hob1.
pose proof (pa_obj_img 66%nat ltac:(unfold disco_nobj; lia)) as Hob66.
pose proof (palf_uar_img B TL) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := ESB regs p cap n over).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (sbd_extra p cap n over)) m)
by (intros m Hm; subst E; unfold ESB; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 A)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 over) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold ESB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold ESB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
by (subst E; unfold ESB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 66)) as VR66.
assert (HAr : 4096 <= A /\ A + 28 <= 2 ^ 47 /\ (A + 28 <= 2147446784 \/ 17594333495296 <= A)).
{ destruct HAapp as [HAapp | HAapp]; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HAapp; lia | lia]. }
clear HAapp. rename HAr into HAapp.
unfold IMG_LO, IMG_TOP in *.
split.
- unfold ss_sbd, sbd_regions. apply pa_entry_st_ok_full.
  + apply regs_ok_ESB.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
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
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 SBx SB);
      [cbn [sv_denot SBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    * rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
      [reflexivity | lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
    * rewrite (VB 10%nat A E10) by lia.
      split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (apresent_writable SEGS). apply HApres. lia.
      -- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
         ++ apply (chunk_ok_val SEGS E _ A 0 8 _ p);
            [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
            change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Mp.
         ++ apply (chunk_ok_val SEGS E _ A 8 8 _ cap);
            [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
            change (N.to_nat 8) with 8%nat. exact Mcap.
         ++ apply (chunk_ok_val SEGS E _ A 16 8 _ n);
            [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
            change (N.to_nat 8) with 8%nat. exact Mn.
         ++ apply (chunk_ok_val SEGS E _ A 24 4 _ over);
            [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
            change (N.to_nat 4) with 4%nat. exact Mover.
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat A E10) by lia. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + unfold sbd_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
            split; [lia|]; split; [exact Hal16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; split; [lia|]; split; [exact HA8 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
            rewrite Z.pow_0_r; split; [unfold SB; lia|]; split; [apply Z.mod_1_r | unfold SB; lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    exact I.
- unfold sbd_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
  assert (HU10 : U E (SOff 10 0) = A) by (shent_U_norm; reflexivity).
  assert (HUB : U E SBx = SHADOW_OFF) by (unfold SBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU10, HUB. split.
  + replace (A + 0) with A by lia. replace (28 - 0) with 28 by lia. exact HRA.
  + intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *.
    lia.
Qed.

End h.
End f.
End d.

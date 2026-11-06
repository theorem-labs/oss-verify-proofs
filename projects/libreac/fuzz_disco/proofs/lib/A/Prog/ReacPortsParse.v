(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 1355 of its 1430 lines of code are new or changed and 3265 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC88 ACj1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcLeaf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_PORTS_PARSE_STK : Z := 16 + ESTACK.
Definition treac_ports_parse_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p q : Z) (bs : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 = w64 (if ports_ok p q bs then 0 else -1) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs) ->
       ~ (q <= a < q + 12) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (q <= b + i < q + 12) ->
       aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ (q <= a < q + 12) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs -> apresent (w_H W2) mem2 a) /\
    (if ports_ok p q bs
     then val_mem SEGS (mrestrict (w_H W2) mem2) q 4 (4 * n_in bs) /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (q + 4) 4 (4 * n_out bs) /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (q + 8) 4 (16 * bt bs 7)
     else forall a, q <= a < q + 12 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
Definition treac_ports_parse_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  q + 12 <= 2 ^ 63 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (p <> 0 -> q <> 0 ->
     length bs = 20%nat /\ p + 20 <= 2 ^ 47 /\ off_img p 20 /\
     (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) /\
     (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 /\
     (forall a, p <= a < p + 20 -> apresent (w_H W) memc a) /\
     garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) /\
     q mod 4 = 0 /\ (q + 12 <= p \/ p + 20 <= q) /\
     (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12 /\
     (forall a, q <= a < q + 12 ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Section z.
Context {fx : YK11.FPState}.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Definition PP_Bx : sv := SOff 32 0.
Definition pp_extra (bs : list byte) : list word :=
  Z_to_bv 64 SB :: map (fun b : byte => Z_to_bv 64 (bv_unsigned b)) bs.
Definition PPE (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (pp_extra bs)).
Definition pp_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_pp0 : sstate := mkSS AF_reac_ports_parse sr_atoms [stack_region 16] None pp_facts0.
Lemma pp_ew : forall (regs : bvmap 5 word) (bs : list byte), length bs = 20%nat ->
  ew (PPE regs bs) 32 = Z_to_bv 64 SB /\
  (forall j, (j < 20)%nat -> ew (PPE regs bs) (33 + j) = Z_to_bv 64 (bt bs j)) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (PPE regs bs) n = getr regs r).
Proof.
intros regs bs HL. split; [|split].
- unfold PPE. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
- intros j Hj. unfold PPE. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold pp_extra.
  cbn [nth].
  rewrite (nth_indep _ (Z_to_bv 64 0) ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)))
    by (first [rewrite length_map | rewrite map_length]; lia).
  rewrite (map_nth (fun b : byte => Z_to_bv 64 (bv_unsigned b)) bs (Z_to_bv 8 0) j). reflexivity.
- intros n r Hn. unfold PPE. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.
Lemma pp_pres_grows : forall (m m' : word -> option byte) (H : word -> bool) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros m m' H a HG (Hh & b & Hb). split; [exact Hh|].
assert (Hne : mrestrict H m' (Z_to_bv 64 a) <> None).
{ apply HG. unfold mrestrict. rewrite Hh, Hb. discriminate. }
unfold mrestrict in Hne. rewrite Hh in Hne. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. apply Hne. reflexivity.
Qed.
Lemma pp_sp_facts : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  alloc_ceiling <= spZ regs - REAC_PORTS_PARSE_STK /\ spZ regs <= 2 ^ 47 /\
  (forall a, spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
split; [lia|]. split; [lia|]. intros a Ha. apply Hpres. lia.
Qed.
Lemma pp_div8_add : forall x y, 0 <= x -> 0 <= y -> x / 8 + y / 8 <= (x + y) / 8.
Proof.
intros x y Hx Hy. apply Z.div_le_lower_bound; [lia|].
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as My.
lia.
Qed.
Lemma pp_shadow_rng : forall x n a, 0 <= x -> x + n <= alloc_ceiling ->
  shadow_addr x <= a < shadow_addr x + n / 8 -> kLowMemEnd <= a < kHighShadowEnd.
Proof.
intros x n a Hx Hxn Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Z_le_gt_dec 0 n) as [Hn | Hn].
- pose proof (pp_div8_add x n Hx Hn) as Hd.
  pose proof (YCbq.shadow_addr_bounds x ltac:(lia)) as Hb1.
  pose proof (YCbq.shadow_addr_bounds (x + n) ltac:(lia)) as Hb2.
  unfold shadow_addr in *. lia.
- exfalso. assert (Hd : n / 8 <= 0) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma pp_post_build : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word) (Ex : Z -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  0 <= q -> q + 12 <= 2 ^ 63 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (forall a, Ex a -> q <= a < q + 12) ->
  (forall a, Ex a -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ Ex a ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (if ports_ok p q bs then 0 else -1) ->
  (if ports_ok p q bs
   then val_mem SEGS (mrestrict (w_H W) mem2) q 4 (4 * n_in bs) /\
        val_mem SEGS (mrestrict (w_H W) mem2) (q + 4) 4 (4 * n_out bs) /\
        val_mem SEGS (mrestrict (w_H W) mem2) (q + 8) 4 (16 * bt bs 7)
   else forall a, ~ Ex a) ->
  treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs W
    (mkCfg (mkst (fx := fx) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs mem2 md2 regs2 Ex
  HJc HJ2 Hlo Hhi Hq0 Hq63 Hqw HEx HExI HK HP HRP H10 Hres.
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct (pp_sp_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as (HspL & HspH & Hwin).
pose proof (proj1 HJc) as HAR.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HRP|]. split; [reflexivity|].
split; [apply Permutation_refl|]. split; [exact H10|].
split; [intros a Ha Hw Hq; apply HK; [lia | lia | intros HE; exact (Hq (HEx a HE))]|].
split.
{ intros b m i Hb Hi Hq.
  destruct (al_blocks _ _ LAWS lyc Sc W mem2 md2 b m (proj1 HJ2) Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
  apply HK; [lia | lia | intros HE; exact (Hq (HEx _ HE))]. }
split.
{ intros a Himg Hown Herr. pose proof (Hsegs a Himg) as Hlow.
  apply HK; [lia | lia | intros HE; exact (HExI a HE Himg)]. }
split.
{ intros cid pos a Hf Hr Hq.
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem2 md2 cid pos (proj1 HJ2) Hf) as (Hf4096 & Hfceil & Happ).
  assert (Hab : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (pp_shadow_rng (frame_addr lyc cid pos) (fs_frame_bytes cid) a ltac:(lia) ltac:(lia) Hr).
    lia. }
  apply HK; [lia | lia | intros HE; exact (Hq (HEx a HE))]. }
split; [intros a Ha Hw Hp; exact (HP a Hp)|].
split; [intros a Ha; apply Hpres2; lia|].
destruct (ports_ok p q bs); [exact Hres|].
intros a Ha. apply HK; [lia | lia | exact (Hres a)].
Qed.
Ltac pp_ewnormg :=
  rewrite ?ew_havoc_old by lia;
  cbn [ew ewset havoc extK Eimg Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
  rewrite ?ew_ewset_other by lia.
Ltac pp_ewnorm H :=
  rewrite ?ew_havoc_old in H by lia;
  cbn [ew ewset havoc extK Eimg Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in H;
  rewrite ?ew_ewset_other in H by lia.
Ltac pp_awr d Uspx :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fp b0 bc lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ d);
    [ reflexivity
    | pp_ewnormg; rewrite Uspx; lia
    | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; lia
    | ] ].
Ltac pp_nowin Uspx :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      pp_ewnorm Hb; rewrite ?Uspx in Hb; lia
    | ]);
  destruct Hr.
Ltac pp_keep Uspx :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB),
    HGr : mem_grows (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB),
    KP : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview ?Sx (w_H ?Wx) ?mA a = aview _ _ ?mC a,
    PR : forall a : Z, apresent (w_H ?Wx) ?mC a -> apresent (w_H ?Wx) ?mA a |- _ =>
    let K := fresh "Knew" in let P := fresh "Pnew" in
    assert (K : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
              aview Sx (w_H Wx) mB a = aview Sx (w_H Wx) mC a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
          intros a Ha Hw;
          rewrite (aview_kept_out Ex rs (w_H Wx) mA mB HFr a Ha ltac:(pp_nowin Uspx));
          exact (KP a Ha Hw));
    assert (P : forall a : Z, apresent (w_H Wx) mC a -> apresent (w_H Wx) mB a)
      by (let a := fresh "a" in let Hp := fresh "Hp" in
          intros a Hp; exact (pp_pres_grows mA mB (w_H Wx) a HGr (PR a Hp)));
    clear KP PR HFr HGr; rename K into KP; rename P into PR
  end.
Ltac pp_ret_fail Hpo HJ0x HJx Hlox Hhix Hq63x Hqwx KPx PRx HAEx E1x Hrax :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ecur ?ssx (restrict _ ?msc) |- _ =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in
    prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
    eapply (RET _ _ _ _ _ _ HS eq_refl); [vm_compute; reflexivity | ];
    let mat := fresh "mat" in intros mat;
    cbn [ms_regs ms_mem];
    rewrite R1; pp_ewnormg; rewrite E1x, Hrax;
    eapply (pp_post_build _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ : Z => False));
    [ exact HJ0x
    | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx
    | exact Hlox | exact Hhix | lia | exact Hq63x | exact Hqwx
    | let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; destruct Hx
    | let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; destruct Hx
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw _; exact (KPx a Ha Hw)
    | let a := fresh "a" in let Hpr := fresh "Hpr" in intros a Hpr; exact (PRx a Hpr)
    | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
      [ eapply env_agree_trans;
        [ exact HAEx | split; [ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; pp_ewnormg;
          repeat match goal with |- context [Nat.eqb n ?c] =>
            replace (Nat.eqb n c) with false by (symmetry; apply Nat.eqb_neq; lia) end;
          reflexivity | reflexivity] ]
      | vm_compute; reflexivity ]
    | rewrite R10; rewrite Hpo; apply bv_eq; vm_compute; reflexivity
    | rewrite Hpo; let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; destruct Hx ]
  end.
Definition PP_HD : Z := AF_reac_ports_parse + 0xac.
Definition PP_TAIL : Z := AF_reac_ports_parse + 0xfc.
Definition PP_CS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma pp_nth_bt : forall (bl : list byte) j, (j < length bl)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) bl) 0 = bt bl j.
Proof.
intros bl j Hj. unfold bt.
rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)))
  by (first [rewrite length_map | rewrite map_length]; lia).
rewrite (map_nth (fun b : byte => bv_unsigned b) bl (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma pp_sll : forall E n v s, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= s < 8 ->
  v * 2 ^ s < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit s)) = Z_to_bv 64 (v * 2 ^ s).
Proof.
intros E n v s Hn Hv Hs Hvs. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n v Hn ltac:(lia)).
rewrite (zcanon_id s) by (unfold M64; lia).
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small s) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma pp_zero : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  q + 12 <= 2 ^ 63 -> (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (p = 0 \/ q = 0) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs
  HJ Hra H10 H11 Hp Hq Hsp16 Hlo Hhi Hq63 Hqw Hz.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct (pp_sp_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi)
  as (HspL & HspH & Hwin).
pose proof HJ as HJ0.
remember (PPE regs bs) as E eqn:HE.
assert (HEI : img_env pa_val A_LIM E) by (subst E; unfold PPE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (pp_extra bs)) n)
  by (intros n Hn; subst E; unfold PPE; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (pp_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HS : st_ok_pi SEGS pa_val E ss_pp0
        (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ports_parse)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pp0. apply pa_entry_st_ok_full.
  - subst E. unfold PPE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hwin. lia.
  - apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold pp_facts0. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp16 | lia]. }
assert (SHOK : sh_ok SEGS PP_Bx (@nil shent) E (mrestrict (w_H W) memc)) by apply Forall_nil.
assert (KP : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
assert (PR : forall a : Z, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a H; exact H).
unfold cfg_at. change (w64 (BASE + AF_reac_ports_parse)) with (Z_to_bv 64 (BASE + AF_reac_ports_parse)).
paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
pp_keep Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB1 end.
  assert (Hp0 : p = 0).
  { rewrite branch_eq_U in HB1. apply Z.eqb_eq in HB1.
    rewrite (U_atom _ 10 p ltac:(pp_ewnormg; exact E10) ltac:(lia)) in HB1.
    rewrite U_lit in HB1 by lia. exact HB1. }
  assert (Hpo : ports_ok p q bs = false)
    by (unfold ports_ok; rewrite Hp0, Z.eqb_refl; reflexivity).
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
  pp_keep Usp.
  pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE E1 Hra.
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB1 end.
  assert (Hp0 : p <> 0).
  { rewrite branch_eq_U in HB1. apply Z.eqb_neq in HB1.
    rewrite (U_atom _ 10 p ltac:(pp_ewnormg; exact E10) ltac:(lia)) in HB1.
    rewrite U_lit in HB1 by lia. exact HB1. }
  assert (Hq0 : q = 0) by (destruct Hz as [Hz | Hz]; [exfalso; exact (Hp0 Hz) | exact Hz]).
  assert (Hpo : ports_ok p q bs = false)
    by (unfold ports_ok; rewrite Hq0, Z.eqb_refl; cbn [negb];
        rewrite Bool.andb_false_r; reflexivity).
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
  pp_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
    pp_keep Usp.
    pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE E1 Hra.
  + exfalso.
    lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SOff 11 0)) _ = _ |- _ =>
      rename Hb into HB2 end.
    rewrite branch_eq_U in HB2. apply Z.eqb_neq in HB2.
    rewrite (U_atom _ 11 q ltac:(pp_ewnormg; exact E11) ltac:(lia)) in HB2.
    rewrite U_lit in HB2 by lia. exact (HB2 Hq0).
Qed.
Section m.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (p q : Z) (bs : list byte).
Hypothesis HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis H10 : getr regs 10 = w64 p.
Hypothesis H11 : getr regs 11 = w64 q.
Hypothesis Hpr : 0 <= p < 2 ^ 64.
Hypothesis Hqr : 0 <= q < 2 ^ 64.
Hypothesis Hsp16 : spZ regs mod 16 = 0.
Hypothesis Hlo : sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK.
Hypothesis Hhi : spZ regs <= sp0.
Hypothesis Hq63 : q + 12 <= 2 ^ 63.
Hypothesis Hqw : spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK.
Hypothesis Hp0 : p <> 0.
Hypothesis Hq0 : q <> 0.
Hypothesis Hlen : length bs = 20%nat.
Hypothesis Hp47 : p + 20 <= 2 ^ 47.
Hypothesis Hpimg : off_img p 20.
Hypothesis Hpapp : p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p.
Hypothesis Hpwin : spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK.
Hypothesis Hpra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20.
Hypothesis Hppres : forall a, p <= a < p + 20 -> apresent (w_H W) memc a.
Hypothesis Hgarr : garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hq4 : q mod 4 = 0.
Hypothesis Hqp : q + 12 <= p \/ p + 20 <= q.
Hypothesis Hqapp : q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q.
Hypothesis Hqra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12.
Hypothesis Hqawr : forall a, q <= a < q + 12 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Lemma pp_sp : alloc_ceiling <= spZ regs - REAC_PORTS_PARSE_STK /\ spZ regs <= 2 ^ 47 /\
  (forall a, spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs -> apresent (w_H W) memc a).
Proof. exact (pp_sp_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ0 Hlo Hhi). Qed.
Lemma pp_qb : forall a, q <= a < q + 12 -> 4096 <= a < 2 ^ 47 /\
  (a + 1 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a).
Proof.
intros a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (Hqawr a Ha) as [Hw _].
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ0 Hw)
  as (_ & [ (Hc1 & Hc2) | [ (Happ & b & n & Hin & Hr & _) | (cid & pos & Hown & [ (Happ & Hr) | (Hsh & Hr) ]) ] ]).
- split; [lia|]. right. unfold YImgTop.IMG_TOP. lia.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _).
  pose proof (blk_off_imgP _ _ _ _ _ _ b n HAR Hin) as Hbimg.
  pose proof (app_addr_below_ceil a Happ) as Hab.
  unfold off_img in Hbimg. split; [lia|]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
- pose proof (app_addr_below_ceil a Happ) as Hab.
  assert (Hinf : In (cid, pos) (frames Sc)).
  { pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hown. }
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hinf) as (Hf4096 & Hfceil & Happf).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hinf) as Hfimg.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold off_img in Hfimg.
  split; [lia|]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
- split; [lia|]. right. unfold YImgTop.IMG_TOP. lia.
Qed.
Lemma pp_cnt_bound : forall f bl kk, 0 <= cnt f bl kk <= Z.of_nat kk.
Proof.
intros f bl kk. induction kk as [|kk IH]; cbn [cnt]; [lia|].
destruct (f (bt bl (8 + kk))); lia.
Qed.
Lemma pp_sh_out : forall x, 0 <= x < 2 ^ 47 ->
  0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ (spZ regs - 16 <= shadow_of_addr SHADOW_OFF x < spZ regs).
Proof.
intros x Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct pp_sp as (HspL & HspH & _). assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
assert (Hd : x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.
Lemma pp_ra_kept : forall (m' : word -> option byte) (x n : Z),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a) ->
  0 <= x -> x + n <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W) m') SHADOW_OFF x n.
Proof.
intros m' x n HK Hx Hxn HR y Hy. destruct (HR y Hy) as (s & Hs & Hok).
exists s. split; [|exact Hok].
destruct (pp_sh_out y ltac:(lia)) as (Hb & Hw). rewrite HK; [exact Hs | lia | exact Hw].
Qed.
Definition pp_extraT (regsT : bvmap 5 word) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (bt bs 7); Z_to_bv 64 (n_in bs); Z_to_bv 64 (n_out bs);
   getr regsT 5; getr regsT 6; getr regsT 7; getr regsT 12; getr regsT 16; getr regsT 17;
   getr regsT 28; getr regsT 29; getr regsT 30; getr regsT 31].
Definition PPET (regsT : bvmap 5 word) : env := Eimg (Ereg regs (pp_extraT regsT)).
Definition pp_srT :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set
    (sr_set (sr_set sr_atoms 2%bv (SOff 2 (-16))) 14%bv (SOff 32 0))
    15%bv (SOff 34 0)) 13%bv (SOff 35 0)) 5%bv (SOff 36 0)) 6%bv (SOff 37 0))
    7%bv (SOff 38 0)) 12%bv (SOff 39 0)) 16%bv (SOff 40 0)) 17%bv (SOff 41 0))
    28%bv (SOff 42 0)) 29%bv (SOff 43 0)) 30%bv (SOff 44 0)) 31%bv (SOff 45 0).
Definition pp_rgT : smem :=
  [ YP09.mkRegion (Some 2%nat) (-16) 0 0 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
    YP09.mkRegion (Some 11%nat) 0 12 0 12 [];
    YP09.mkRegion (Some 10%nat) 0 20 0 0 [YP09.mkChunk 7 (CVal 1 (SOff 33 0))] ].
Definition pp_factsT : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
           (10%nat, mkAF 1 (2 ^ 47 - 20) 0); (11%nat, mkAF 1 (2 ^ 47 - 12) 2);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 12 0); (35%nat, mkAF 0 12 0)] [] [].
Definition pp_SHT : list shent := [mkSHE 11 0 12; mkSHE 10 0 20].
Definition pp_ssT : sstate := mkSS PP_TAIL pp_srT pp_rgT None pp_factsT.
Lemma pp_tail : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
     aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memT a) ->
  getr regsT 1 = getr regs 1 -> getr regsT 2 = Z_to_bv 64 (spZ regs - 16) ->
  getr regsT 10 = Z_to_bv 64 p -> getr regsT 11 = Z_to_bv 64 q ->
  getr regsT 13 = Z_to_bv 64 (n_out bs) -> getr regsT 14 = Z_to_bv 64 SB ->
  getr regsT 15 = Z_to_bv 64 (n_in bs) ->
  (forall r, In r PP_CS -> getr regsT r = getr regs r) ->
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  decl bs = true ->
  SRr SEGS W (cfg_at SEGS (BASE + PP_TAIL) regsT memT mdT)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros regsT memT mdT HJT HKT HPT HT1 HT2 HT10 HT11 HT13 HT14 HT15 HCS HRA Hdecl.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct pp_sp as (HspL & HspH & Hwin).
assert (Hqlo : 4096 <= q) by (destruct (pp_qb q ltac:(lia)); lia).
assert (Hqhi : q + 12 <= 2 ^ 47) by (destruct (pp_qb (q + 11) ltac:(lia)); lia).
assert (HnI : 0 <= n_in bs <= 12)
  by (unfold n_in; pose proof (pp_cnt_bound is_in bs 12) as Hc; change (Z.of_nat 12) with 12 in Hc; exact Hc).
assert (HnO : 0 <= n_out bs <= 12)
  by (unfold n_out; pose proof (pp_cnt_bound is_out bs 12) as Hc; change (Z.of_nat 12) with 12 in Hc; exact Hc).
assert (Hb7 : 0 <= bt bs 7 < 256).
{ destruct (Hgarr 7%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [_ Hr].
  rewrite pp_nth_bt in Hr by lia. exact Hr. }
assert (HKq : forall a, q <= a < q + 12 -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a)
  by (intros a Ha; apply HKT; lia).
assert (HKp : forall a, p <= a < p + 20 -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a)
  by (intros a Ha; apply HKT; lia).
assert (HgarrT : garr8 SEGS (mrestrict (w_H W) memT) p (map (fun b : byte => bv_unsigned b) bs)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc memT p _); [|exact Hgarr].
  intros a Ha. apply HKp. first [rewrite length_map in Ha | rewrite map_length in Ha]. lia. }
assert (HV7 : val_mem SEGS (mrestrict (w_H W) memT) (p + 7) 1 (bt bs 7)).
{ destruct (HgarrT 7%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [Hv _].
  rewrite pp_nth_bt in Hv by lia. exact Hv. }
assert (HraT : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF p 20)
  by (apply (pp_ra_kept memT p 20 HKT); [lia | lia | exact Hpra]).
assert (HqraT : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF q 12)
  by (apply (pp_ra_kept memT q 12 HKT); [lia | lia | exact Hqra]).
remember (PPET regsT) as E eqn:HE.
assert (HEI : img_env pa_val A_LIM E) by (subst E; unfold PPET; apply Eimg_env).
assert (ETn : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold PPET; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ETx : forall j : nat, (j < 14)%nat -> ew E (32 + j) = nth j (pp_extraT regsT) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold PPET; rewrite Eimg_low by (unfold A_TEXT; lia);
      apply ew_Ereg_extra).
assert (ET32 : ew E 32 = Z_to_bv 64 SB) by (exact (ETx 0%nat ltac:(lia))).
assert (ET33 : ew E 33 = Z_to_bv 64 (bt bs 7)) by (exact (ETx 1%nat ltac:(lia))).
assert (ET34 : ew E 34 = Z_to_bv 64 (n_in bs)) by (exact (ETx 2%nat ltac:(lia))).
assert (ET35 : ew E 35 = Z_to_bv 64 (n_out bs)) by (exact (ETx 3%nat ltac:(lia))).
assert (ET36 : ew E 36 = getr regsT 5) by (exact (ETx 4%nat ltac:(lia))).
assert (ET37 : ew E 37 = getr regsT 6) by (exact (ETx 5%nat ltac:(lia))).
assert (ET38 : ew E 38 = getr regsT 7) by (exact (ETx 6%nat ltac:(lia))).
assert (ET39 : ew E 39 = getr regsT 12) by (exact (ETx 7%nat ltac:(lia))).
assert (ET40 : ew E 40 = getr regsT 16) by (exact (ETx 8%nat ltac:(lia))).
assert (ET41 : ew E 41 = getr regsT 17) by (exact (ETx 9%nat ltac:(lia))).
assert (ET42 : ew E 42 = getr regsT 28) by (exact (ETx 10%nat ltac:(lia))).
assert (ET43 : ew E 43 = getr regsT 29) by (exact (ETx 11%nat ltac:(lia))).
assert (ET44 : ew E 44 = getr regsT 30) by (exact (ETx 12%nat ltac:(lia))).
assert (ET45 : ew E 45 = getr regsT 31) by (exact (ETx 13%nat ltac:(lia))).
assert (ET1 : ew E 1 = getr regs 1) by (exact (ETn 1%nat 1%bv eq_refl)).
assert (ET2 : ew E 2 = getr regs 2) by (exact (ETn 2%nat 2%bv eq_refl)).
assert (ET10 : ew E 10 = Z_to_bv 64 p) by (rewrite (ETn 10%nat 10%bv eq_refl); exact H10).
assert (ET11 : ew E 11 = Z_to_bv 64 q) by (rewrite (ETn 11%nat 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite ET2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (pp_extraT regsT)) E)
  by (split; [intros n Hn; subst E; unfold PPET; apply Eimg_low; unfold A_TEXT; lia
             | subst E; reflexivity]).
assert (HUB : U E PP_Bx = SHADOW_OFF)
  by (unfold PP_Bx, U; cbn [sv_denot]; rewrite ET32, Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite unsigned_lit_small by (unfold SB; lia); exact SB_SHADOW_OFF).
assert (HS : st_ok_pi SEGS pa_val E pp_ssT
        (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + PP_TAIL)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pp_ssT. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?rr) =>
          let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
        cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first
        [ symmetry; assumption
        | rewrite getr_zero; reflexivity
        | rewrite ET32; exact HT14
        | rewrite ET34; exact HT15
        | rewrite ET35; exact HT13
        | rewrite ET2, HT2; unfold spZ; f_equal; lia
        | lazymatch goal with
          | |- getr _ ?rr = ew _ ?nn => rewrite (ETn nn rr eq_refl)
          end;
          first [ reflexivity | exact HT1 | rewrite H10; exact HT10 | rewrite H11; exact HT11
                | apply HCS; cbv [PP_CS In];
                  solve [repeat first [left; reflexivity | right]] ]
        | match goal with |- ?g => idtac "REGFAIL" g; fail end ]
      | ]); destruct Hr.
  - vm_compute. reflexivity.
  - unfold pp_rgT. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (spZ regs) (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
      [ cbn [sv_denot]; rewrite ET1, Z.add_0_r; reflexivity
      | pose proof (u64_range (getr regs 1)); zside | zside | exact HRA ].
    + rewrite ET11, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). destruct (Hqawr (q + o) ltac:(lia)) as [_ Hpres].
      apply HPT. exact Hpres.
    + rewrite ET10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 7 1 (SOff 33 0) (bt bs 7));
      [ cbn [sv_denot]; rewrite ET33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside | exact HV7 ].
  - apply pairwise_disjoint_of_extents. unfold pp_rgT, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, ET10, ET11, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - unfold pp_factsT. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, ET32, ET10, ET11, ET33, ET34, ET35, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PP_Bx pp_SHT E (mrestrict (w_H W) memT)).
{ unfold pp_SHT. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H W) memT E PP_Bx 11 q 12 q 0 12 HqraT HUB);
    [ unfold U; cbn [sv_denot]; rewrite ET11, Z.add_0_r, Z_to_bv_bv_unsigned;
      apply unsigned_lit_small; lia
    | lia | lia
    | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ].
  - apply (shent_ok_of_range SEGS (w_H W) memT E PP_Bx 10 p 20 p 0 20 HraT HUB);
    [ unfold U; cbn [sv_denot]; rewrite ET10, Z.add_0_r, Z_to_bv_bv_unsigned;
      apply unsigned_lit_small; lia
    | lia | lia
    | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]. }
unfold cfg_at. change (w64 (BASE + PP_TAIL)) with (Z_to_bv 64 (BASE + PP_TAIL)).
paj_run_tok RUN HS HJT SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fp b0 bc lyx ownx) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 11%nat q);
  [ reflexivity | rewrite ET11; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (Hqawr a ltac:(lia)))
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] ]. }
assert (Hpok : ports_ok p q bs = true)
  by (unfold ports_ok; rewrite (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq q 0) Hq0), Hdecl; reflexivity).
lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict (w_H W) memT) (mrestrict (w_H W) ?mB),
  HGr : mem_grows (mrestrict (w_H W) memT) (mrestrict (w_H W) ?mB) |- _ =>
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (q <= a < q + 12) ->
            aview SEGS (w_H W) mB a = aview SEGS (w_H W) memc a);
  [ intros a Ha Hw Hq;
    rewrite (aview_kept_out Ex rs (w_H W) memT mB HFr a Ha);
    [ exact (HKT a Ha Hw)
    | let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
      intros (r & Hr & Hb);
      lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
      cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
          rewrite ?Usp, ?ET11, ?ET10 in Hb; rewrite ?unsigned_lit_small in Hb by lia; lia
        | ]);
      destruct Hr ]
  | ];
  assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mB a)
    by (intros a Hp; exact (pp_pres_grows memT mB (w_H W) a HGr (HPT a Hp)));
  clear HFr HGr
end.
lazymatch goal with
| HS : st_ok_pi _ _ ?Ecur ?ssx (restrict _ ?msc) |- _ =>
  let R10 := fresh "R10" in let R1 := fresh "R1" in
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  let rq := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let HRq := fresh "HRq" in
  pose proof (st_ok_pi_region_nth Ecur ssx (restrict (w_H W) msc) 1 rq HS ltac:(vm_compute; reflexivity)) as HRq;
  cbn [ms_mem restrict mkst] in HRq;
  assert (EC11 : bv_unsigned (ew Ecur 11) = q) by (pp_ewnormg; rewrite ET11; apply unsigned_lit_small; lia);
  assert (EC34 : ew Ecur 34 = Z_to_bv 64 (n_in bs)) by (pp_ewnormg; exact ET34);
  assert (EC35 : ew Ecur 35 = Z_to_bv 64 (n_out bs)) by (pp_ewnormg; exact ET35);
  assert (EC33 : ew Ecur 33 = Z_to_bv 64 (bt bs 7)) by (pp_ewnormg; exact ET33);
  assert (V0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 0) (N.to_nat 4) (4 * n_in bs));
  [ eapply (field_of_region _ _ 11 q _ 0 12 0 12 0 4%N (SAlu ALU_SLL (SOff 34 0) (SLit 2)) (4 * n_in bs) HRq);
    [ exact EC11 | cbn [In]; tauto
    | replace (4 * n_in bs) with (n_in bs * 2 ^ 2) by lia; apply pp_sll; [exact EC34 | lia | lia | lia]
    | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | change (Z.of_N 4) with 4; lia ]
  | ];
  assert (V4 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 4) (N.to_nat 4) (4 * n_out bs));
  [ eapply (field_of_region _ _ 11 q _ 0 12 0 12 4 4%N (SAlu ALU_SLL (SOff 35 0) (SLit 2)) (4 * n_out bs) HRq);
    [ exact EC11 | cbn [In]; tauto
    | replace (4 * n_out bs) with (n_out bs * 2 ^ 2) by lia; apply pp_sll; [exact EC35 | lia | lia | lia]
    | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | change (Z.of_N 4) with 4; lia ]
  | ];
  assert (V8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 8) (N.to_nat 4) (16 * bt bs 7));
  [ eapply (field_of_region _ _ 11 q _ 0 12 0 12 8 4%N (SAlu ALU_SLL (SOff 33 0) (SLit 4)) (16 * bt bs 7) HRq);
    [ exact EC11 | cbn [In]; tauto
    | replace (16 * bt bs 7) with (bt bs 7 * 2 ^ 4) by lia; apply pp_sll; [exact EC33 | lia | lia | lia]
    | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | change (Z.of_N 4) with 4; lia ]
  | ];
  rewrite Z.add_0_r in V0; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V4, V8;
  eapply (RET _ _ _ _ _ _ HS eq_refl); [vm_compute; reflexivity | ];
  let mat := fresh "mat" in intros mat;
  cbn [ms_regs ms_mem];
  rewrite R1; pp_ewnormg; rewrite ET1, Hra;
  eapply (pp_post_build _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a : Z => q <= a < q + 12));
  [ exact HJ0
  | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJT
  | exact Hlo | exact Hhi | lia | exact Hq63 | exact Hqw
  | intros a Ha; exact Ha
  | intros a Ha Himg; destruct (pp_qb a Ha) as [_ Hoff]; pose proof (pa_img_range a Himg) as Hir;
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
  | intros a Ha Hw Hq; exact (KP2 a Ha Hw Hq)
  | exact PR2
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
    [ eapply env_agree_trans;
      [ exact HAE | split; [ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; pp_ewnormg;
          repeat match goal with |- context [Nat.eqb n ?c] =>
            replace (Nat.eqb n c) with false by (symmetry; apply Nat.eqb_neq; lia) end;
          reflexivity | reflexivity] ]
    | vm_compute; reflexivity ]
  | rewrite R10, Hpok; reflexivity
  | rewrite Hpok; split; [exact V0 | split; [exact V4 | exact V8]] ]
end.
Qed.
Definition ppl_extra (regsE : bvmap 5 word) (i : nat) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (bt bs (8 + i)); Z_to_bv 64 (p + 8 + Z.of_nat i);
   Z_to_bv 64 (cnt is_in bs i); Z_to_bv 64 (cnt is_out bs i); Z_to_bv 64 (12 - Z.of_nat i);
   getr regsE 7; getr regsE 28; getr regsE 29; getr regsE 30; getr regsE 31].
Definition ppl_E (regsE : bvmap 5 word) (i : nat) : env := Eimg (Ereg regs (ppl_extra regsE i)).
Definition ppl_sr :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    2%bv (SOff 2 (-16))) 5%bv (SLit 2)) 6%bv (SLit 1)) 7%bv (SOff 38 0))
    12%bv (SOff 34 0)) 13%bv (SOff 36 0)) 14%bv (SOff 32 0)) 15%bv (SOff 35 0))
    16%bv (SOff 34 0)) 17%bv (SOff 37 0)) 28%bv (SOff 39 0)) 29%bv (SOff 40 0))
    30%bv (SOff 41 0)) 31%bv (SOff 42 0).
Definition ppl_rg : smem := [YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]].
Definition ppl_facts : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 9 (2 ^ 47 - 1) 0)] [] [].
Definition ppl_SH : list shent := [mkSHE 34 0 1].
Definition ppl_ss : sstate := mkSS PP_HD ppl_sr ppl_rg None ppl_facts.
Definition ppl_inv (i : nat) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memE a) /\
  getr regsE 1 = getr regs 1 /\ getr regsE 2 = Z_to_bv 64 (spZ regs - 16) /\
  getr regsE 10 = Z_to_bv 64 p /\ getr regsE 11 = Z_to_bv 64 q /\
  getr regsE 12 = Z_to_bv 64 (p + 8 + Z.of_nat i) /\ getr regsE 16 = Z_to_bv 64 (p + 8 + Z.of_nat i) /\
  getr regsE 13 = Z_to_bv 64 (cnt is_out bs i) /\ getr regsE 15 = Z_to_bv 64 (cnt is_in bs i) /\
  getr regsE 17 = Z_to_bv 64 (12 - Z.of_nat i) /\ getr regsE 5 = Z_to_bv 64 2 /\ getr regsE 6 = Z_to_bv 64 1 /\
  getr regsE 14 = Z_to_bv 64 SB /\
  (forall r, In r PP_CS -> getr regsE r = getr regs r) /\
  val_mem SEGS (mrestrict (w_H W) memE) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)).
Lemma ppl_cnt_S : forall (f : Z -> bool) (j : nat),
  cnt f bs (Datatypes.S j) = cnt f bs j + (if f (bt bs (8 + j)) then 1 else 0).
Proof. intros f j. reflexivity. Qed.
Lemma ppl_U_off : forall (E : env) (n : nat) (v c : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
intros E n v c H Hv Hvc. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ppl_Ex : forall (regsE : bvmap 5 word) (i j : nat), (j < 11)%nat ->
  ew (ppl_E regsE i) (32 + j) = nth j (ppl_extra regsE i) (Z_to_bv 64 0).
Proof. intros regsE i j Hj. unfold ppl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma ppl_Er : forall (regsE : bvmap 5 word) (i n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ppl_E regsE i) n = getr regs r.
Proof. intros regsE i n r Hn. unfold ppl_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ppl_next : forall (i : nat) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model)
    (E Ecur : env) (ssx : sstate) (ms : machine_state) (md : Model) (dI dO : bool),
  (i < 12)%nat -> E = ppl_E regsE i ->
  st_ok_pi SEGS pa_val Ecur ssx (restrict (w_H W) ms) ->
  env_agree 43 E Ecur ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (1%bv :: 10%bv :: 11%bv :: PP_CS) = true ->
  sr_get (ss_regs ssx) 2%bv = SOff 2 (-16) -> sr_get (ss_regs ssx) 5%bv = SLit 2 ->
  sr_get (ss_regs ssx) 6%bv = SLit 1 -> sr_get (ss_regs ssx) 12%bv = SOff 34 1 ->
  sr_get (ss_regs ssx) 16%bv = SOff 34 1 -> sr_get (ss_regs ssx) 13%bv = SOff 36 (if dO then 1 else 0) ->
  sr_get (ss_regs ssx) 15%bv = SOff 35 (if dI then 1 else 0) -> sr_get (ss_regs ssx) 17%bv = SOff 37 (-1) ->
  sr_get (ss_regs ssx) 14%bv = SOff 32 0 ->
  cnt is_in bs (Datatypes.S i) = cnt is_in bs i + (if dI then 1 else 0) ->
  cnt is_out bs (Datatypes.S i) = cnt is_out bs i + (if dO then 1 else 0) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memE a) ->
  (forall a, apresent (w_H W) memE a -> apresent (w_H W) (ms_mem ms) a) ->
  ppl_inv i regsE memE mdE ->
  ppl_inv (Datatypes.S i) (ms_regs ms) (ms_mem ms) md.
Proof.
intros i regsE memE mdE E Ecur ssx ms md dI dO Hi HE HS HA HL S2 S5 S6 S12 S16 S13 S15 S17 S14
  HIN HOUT HJ KA PA HI.
subst E.
destruct HI as (_ & KP & PR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRA).
destruct pp_sp as (HspL & HspH & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
pose proof (pp_cnt_bound is_in bs i) as HcI. pose proof (pp_cnt_bound is_out bs i) as HcO.
assert (BI : 0 <= (if dI then 1 else 0) <= 1) by (destruct dI; lia).
assert (BO : 0 <= (if dO then 1 else 0) <= 1) by (destruct dO; lia).
assert (V : forall n, (n < 43)%nat -> ew Ecur n = ew (ppl_E regsE i) n) by (intros n Hn; exact (proj1 HA n Hn)).
assert (V2 : ew Ecur 2 = getr regs 2)
  by (rewrite (V 2%nat ltac:(lia)); exact (ppl_Er regsE i 2 2%bv eq_refl)).
assert (V32 : ew Ecur 32 = Z_to_bv 64 SB)
  by (rewrite (V 32%nat ltac:(lia)); exact (ppl_Ex regsE i 0 ltac:(lia))).
assert (V34 : ew Ecur 34 = Z_to_bv 64 (p + 8 + Z.of_nat i))
  by (rewrite (V 34%nat ltac:(lia)); exact (ppl_Ex regsE i 2 ltac:(lia))).
assert (V35 : ew Ecur 35 = Z_to_bv 64 (cnt is_in bs i))
  by (rewrite (V 35%nat ltac:(lia)); exact (ppl_Ex regsE i 3 ltac:(lia))).
assert (V36 : ew Ecur 36 = Z_to_bv 64 (cnt is_out bs i))
  by (rewrite (V 36%nat ltac:(lia)); exact (ppl_Ex regsE i 4 ltac:(lia))).
assert (V37 : ew Ecur 37 = Z_to_bv 64 (12 - Z.of_nat i))
  by (rewrite (V 37%nat ltac:(lia)); exact (ppl_Ex regsE i 5 ltac:(lia))).
assert (HA32 : env_agree 32 (Ereg regs (ppl_extra regsE i)) Ecur).
{ split; [intros n Hn; rewrite (V n ltac:(lia)); unfold ppl_E; apply Eimg_low; unfold A_TEXT; lia|].
  rewrite (proj2 HA). reflexivity. }
assert (HK : forall r, In r (1%bv :: 10%bv :: 11%bv :: PP_CS) -> getr (ms_regs ms) r = getr regs r)
  by exact (regs_kept_of_st_ok_pi Ecur ssx (restrict (w_H W) ms) regs (ppl_extra regsE i) _ HS HA32 HL).
assert (G : forall r, getr (ms_regs ms) r = sv_denot Ecur (sr_get (ss_regs ssx) r))
  by (intros r; exact (st_ok_pi_restrict_reg (w_H W) Ecur ssx ms r HS)).
unfold ppl_inv.
split; [exact HJ|].
split; [intros a Ha Hw; rewrite (KA a Ha); exact (KP a Ha Hw)|].
split; [intros a Hp; exact (PA a (PR a Hp))|].
split; [apply HK; left; reflexivity|].
split; [rewrite G, S2; cbn [sv_denot]; rewrite V2; unfold spZ; f_equal; lia|].
split; [rewrite (HK 10%bv ltac:(right; left; reflexivity)); exact H10|].
split; [rewrite (HK 11%bv ltac:(right; right; left; reflexivity)); exact H11|].
split; [rewrite G, S12; cbn [sv_denot]; rewrite V34, unsigned_lit_small by lia; f_equal; lia|].
split; [rewrite G, S16; cbn [sv_denot]; rewrite V34, unsigned_lit_small by lia; f_equal; lia|].
split; [rewrite G, S13; cbn [sv_denot]; rewrite V36, unsigned_lit_small, HOUT by lia; reflexivity|].
split; [rewrite G, S15; cbn [sv_denot]; rewrite V35, unsigned_lit_small, HIN by lia; reflexivity|].
split; [rewrite G, S17; cbn [sv_denot]; rewrite V37, unsigned_lit_small by lia; f_equal; lia|].
split; [rewrite G, S5; reflexivity|].
split; [rewrite G, S6; reflexivity|].
split; [rewrite G, S14; cbn [sv_denot]; rewrite V32, unsigned_lit_small by (unfold SB; lia); f_equal; lia|].
split; [intros r Hr; apply HK; right; right; right; exact Hr|].
apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem ms) (spZ regs - 8) 8%nat _); [|exact HRA].
intros kk Hkk. apply KA. lia.
Qed.
Ltac ppl_keep Uspx :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB),
    HGr : mem_grows (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB),
    KA : forall a : Z, 0 <= a < 2 ^ 64 -> aview ?Sx (w_H ?Wx) ?mA a = aview _ _ ?mC a,
    PA : forall a : Z, apresent (w_H ?Wx) ?mC a -> apresent (w_H ?Wx) ?mA a |- _ =>
    let K := fresh "Knew" in let P := fresh "Pnew" in
    assert (K : forall a : Z, 0 <= a < 2 ^ 64 -> aview Sx (w_H Wx) mB a = aview Sx (w_H Wx) mC a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha;
          rewrite (aview_kept_out Ex rs (w_H Wx) mA mB HFr a Ha ltac:(pp_nowin Uspx));
          exact (KA a Ha));
    assert (P : forall a : Z, apresent (w_H Wx) mC a -> apresent (w_H Wx) mB a)
      by (let a := fresh "a" in let Hp := fresh "Hp" in
          intros a Hp; exact (pp_pres_grows mA mB (w_H Wx) a HGr (PA a Hp)));
    clear KA PA HFr HGr; rename K into KA; rename P into PA;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end
  end.
Ltac ppl_fin i regsE memE E dI dO Hi HE HS HJ HI0 HIN HOUT KA PA :=
  eapply (ppl_next i regsE memE _ E _ _ _ _ dI dO Hi HE HS);
  [ split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in
            intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity | reflexivity]
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | exact HIN | exact HOUT | exact HJ | exact KA | exact PA | exact HI0 ].
Ltac ppl_e4 i regsE memE E dI dO Hi HE HS HJ SHOK HI0 HIN HOUT KA PA Usp E37 KH KT :=
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr 0 Usp |];
  ppl_keep Usp;
  psrr_branch_tok RUN BR HS SHOK Bspan;
  [ let Hc4 := fresh "Hc4" in let Hi11 := fresh "Hi11" in
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hc4 end;
    rewrite branch_eq_U in Hc4; apply Z.eqb_eq in Hc4;
    lazymatch type of Hc4 with U ?Ec _ = _ =>
      rewrite (ppl_U_off Ec 37 (12 - Z.of_nat i) (-1) ltac:(pp_ewnormg; exact E37) ltac:(lia) ltac:(lia)),
        U_lit in Hc4 by lia end;
    assert (Hi11 : i = 11%nat) by lia; clear Hc4;
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PP_TAIL; [pp_awr 0 Usp |];
    ppl_keep Usp; pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?md) ?Qx =>
      change (SRr SEGS W (cfg_at SEGS (BASE + PP_TAIL) rr mm md) Qx) end;
    apply (KT Hi11);
    ppl_fin i regsE memE E dI dO Hi HE HS HJ HI0 HIN HOUT KA PA
  | let Hc4 := fresh "Hc4" in let Hlt := fresh "Hlt" in
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hc4 end;
    rewrite branch_eq_U in Hc4; apply Z.eqb_neq in Hc4;
    lazymatch type of Hc4 with U ?Ec _ <> _ =>
      rewrite (ppl_U_off Ec 37 (12 - Z.of_nat i) (-1) ltac:(pp_ewnormg; exact E37) ltac:(lia) ltac:(lia)),
        U_lit in Hc4 by lia end;
    assert (Hlt : (i < 11)%nat) by lia; clear Hc4;
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PP_HD; [pp_awr 0 Usp |];
    ppl_keep Usp; pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?md) ?Qx =>
      change (SRr SEGS W (cfg_at SEGS (BASE + PP_HD) rr mm md) Qx) end;
    apply (KH Hlt);
    ppl_fin i regsE memE E dI dO Hi HE HS HJ HI0 HIN HOUT KA PA ].
Lemma ppl_iter : forall (i : nat) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model)
    (Q : world SEGS -> config -> Prop),
  (i < 12)%nat -> ppl_inv i regsE memE mdE ->
  ((i < 11)%nat -> forall regsN memN mdN, ppl_inv (Datatypes.S i) regsN memN mdN ->
     SRr SEGS W (cfg_at SEGS (BASE + PP_HD) regsN memN mdN) Q) ->
  (i = 11%nat -> forall regsN memN mdN, ppl_inv (Datatypes.S i) regsN memN mdN ->
     SRr SEGS W (cfg_at SEGS (BASE + PP_TAIL) regsN memN mdN) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + PP_HD) regsE memE mdE) Q.
Proof.
intros i regsE memE mdE Q Hi HI KH KT.
pose proof HI as HI0.
destruct HI as (HJ & KP & PR & R1 & R2 & R10 & R11 & R12 & R16 & R13 & R15 & R17 & R5 & R6 & R14 & RCS & HRA).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct pp_sp as (HspL & HspH & Hwin).
pose proof (pp_cnt_bound is_in bs i) as HcI. pose proof (pp_cnt_bound is_out bs i) as HcO.
assert (HKp : forall a, p <= a < p + 20 -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha; apply KP; lia).
assert (HgarrE : garr8 SEGS (mrestrict (w_H W) memE) p (map (fun b : byte => bv_unsigned b) bs)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc memE p _); [|exact Hgarr].
  intros a Ha. apply HKp. first [rewrite length_map in Ha | rewrite map_length in Ha]. lia. }
assert (Hb : 0 <= bt bs (8 + i) < 256).
{ destruct (Hgarr (8 + i)%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [_ Hr].
  rewrite pp_nth_bt in Hr by lia. exact Hr. }
assert (HVb : val_mem SEGS (mrestrict (w_H W) memE) (p + 8 + Z.of_nat i + 0) 1 (bt bs (8 + i))).
{ destruct (HgarrE (8 + i)%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [Hv _].
  rewrite pp_nth_bt in Hv by lia. replace (p + 8 + Z.of_nat i + 0) with (p + Z.of_nat (8 + i)) by lia.
  exact Hv. }
assert (HraE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF p 20)
  by (apply (pp_ra_kept memE p 20 KP); [lia | lia | exact Hpra]).
remember (ppl_E regsE i) as E eqn:HE.
assert (HEI : img_env pa_val A_LIM E) by (subst E; unfold ppl_E; apply Eimg_env).
assert (ETn : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ppl_Er; exact Hn).
assert (ETx : forall j : nat, (j < 11)%nat -> ew E (32 + j) = nth j (ppl_extra regsE i) (Z_to_bv 64 0))
  by (intros j Hj; subst E; apply ppl_Ex; exact Hj).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (ETx 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (bt bs (8 + i))) by (exact (ETx 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (p + 8 + Z.of_nat i)) by (exact (ETx 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (cnt is_in bs i)) by (exact (ETx 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (cnt is_out bs i)) by (exact (ETx 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (12 - Z.of_nat i)) by (exact (ETx 5%nat ltac:(lia))).
assert (E38 : ew E 38 = getr regsE 7) by (exact (ETx 6%nat ltac:(lia))).
assert (E39 : ew E 39 = getr regsE 28) by (exact (ETx 7%nat ltac:(lia))).
assert (E40 : ew E 40 = getr regsE 29) by (exact (ETx 8%nat ltac:(lia))).
assert (E41 : ew E 41 = getr regsE 30) by (exact (ETx 9%nat ltac:(lia))).
assert (E42 : ew E 42 = getr regsE 31) by (exact (ETx 10%nat ltac:(lia))).
clear ETx.
assert (E2 : ew E 2 = getr regs 2) by (exact (ETn 2%nat 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HUB : U E PP_Bx = SHADOW_OFF)
  by (unfold PP_Bx, U; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite unsigned_lit_small by (unfold SB; lia); exact SB_SHADOW_OFF).
assert (HS : st_ok_pi SEGS pa_val E ppl_ss
        (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + PP_HD)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ppl_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?rr) =>
          let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
        cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first
        [ symmetry; assumption
        | assumption
        | rewrite getr_zero; reflexivity
        | rewrite E32; exact R14
        | rewrite E34; first [exact R12 | exact R16]
        | rewrite E35; exact R15
        | rewrite E36; exact R13
        | rewrite E37; exact R17
        | rewrite E2, R2; unfold spZ; f_equal; lia
        | lazymatch goal with
          | |- getr _ ?rr = ew _ ?nn => rewrite (ETn nn rr eq_refl)
          end;
          first [ reflexivity | exact R1 | rewrite H10; exact R10 | rewrite H11; exact R11
                | apply RCS; cbv [PP_CS In];
                  solve [repeat first [left; reflexivity | right]] ]
        | match goal with |- ?g => idtac "REGFAIL" g; fail end ]
      | ]); destruct Hr.
  - vm_compute. reflexivity.
  - unfold ppl_rg. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (p + 8 + Z.of_nat i) 0 1 (SOff 33 0) (bt bs (8 + i)));
    [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; exact Hb | zside | exact HVb ].
  - apply pairwise_disjoint_of_extents. unfold ppl_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ppl_facts. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PP_Bx ppl_SH E (mrestrict (w_H W) memE)).
{ unfold ppl_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memE E PP_Bx 34 p 20 (p + 8 + Z.of_nat i) 0 1 HraE HUB);
  [ unfold U; cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned;
    apply unsigned_lit_small; lia
  | lia | lia
  | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) memE a)
  by (intros; reflexivity).
assert (PA : forall a, apresent (w_H W) memE a -> apresent (w_H W) memE a) by (intros a Hx; exact Hx).
unfold cfg_at. change (w64 (BASE + PP_HD)) with (Z_to_bv 64 (BASE + PP_HD)).
paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr 0 Usp |].
ppl_keep Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
- lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hc1 end.
  rewrite branch_eq_U in Hc1. apply Z.eqb_eq in Hc1.
  lazymatch type of Hc1 with U ?Ec _ = _ =>
    rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc1 by lia end.
  assert (HIN : cnt is_in bs (Datatypes.S i) = cnt is_in bs i + 1) by (rewrite ppl_cnt_S, Hc1; reflexivity).
  assert (HOUT : cnt is_out bs (Datatypes.S i) = cnt is_out bs i + 0) by (rewrite ppl_cnt_S, Hc1; reflexivity).
  clear Hc1.
  ppl_e4 i regsE memE E true false Hi HE HS HJ SHOK HI0 HIN HOUT KA PA Usp E37 KH KT.
- lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hc1 end.
  rewrite branch_eq_U in Hc1. apply Z.eqb_neq in Hc1.
  lazymatch type of Hc1 with U ?Ec _ <> _ =>
    rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc1 by lia end.
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr 0 Usp |].
  ppl_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hc2 end.
    rewrite branch_eq_U in Hc2. apply Z.eqb_eq in Hc2.
    lazymatch type of Hc2 with U ?Ec _ = _ =>
      rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc2 by lia end.
    assert (HIN : cnt is_in bs (Datatypes.S i) = cnt is_in bs i + 0) by (rewrite ppl_cnt_S, Hc2; reflexivity).
    assert (HOUT : cnt is_out bs (Datatypes.S i) = cnt is_out bs i + 1) by (rewrite ppl_cnt_S, Hc2; reflexivity).
    clear Hc1 Hc2.
    ppl_e4 i regsE memE E false true Hi HE HS HJ SHOK HI0 HIN HOUT KA PA Usp E37 KH KT.
  + lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hc2 end.
    rewrite branch_eq_U in Hc2. apply Z.eqb_neq in Hc2.
    lazymatch type of Hc2 with U ?Ec _ <> _ =>
      rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc2 by lia end.
    paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr 0 Usp |].
    ppl_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hc3 end.
      rewrite branch_ne_U in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc3.
      lazymatch type of Hc3 with U ?Ec _ <> _ =>
        rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc3 by lia end.
      assert (HIN : cnt is_in bs (Datatypes.S i) = cnt is_in bs i + 0)
        by (rewrite ppl_cnt_S; unfold is_in;
            rewrite (proj2 (Z.eqb_neq _ _) Hc3), (proj2 (Z.eqb_neq _ _) Hc1); reflexivity).
      assert (HOUT : cnt is_out bs (Datatypes.S i) = cnt is_out bs i + 0)
        by (rewrite ppl_cnt_S; unfold is_out; rewrite (proj2 (Z.eqb_neq _ _) Hc2); reflexivity).
      clear Hc1 Hc2 Hc3.
      ppl_e4 i regsE memE E false false Hi HE HS HJ SHOK HI0 HIN HOUT KA PA Usp E37 KH KT.
    * lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hc3 end.
      rewrite branch_ne_U in Hc3. apply Bool.negb_false_iff, Z.eqb_eq in Hc3.
      lazymatch type of Hc3 with U ?Ec _ = _ =>
        rewrite (U_atom Ec 33 (bt bs (8 + i)) ltac:(pp_ewnormg; exact E33) ltac:(lia)), U_lit in Hc3 by lia end.
      assert (HIN : cnt is_in bs (Datatypes.S i) = cnt is_in bs i + 1) by (rewrite ppl_cnt_S, Hc3; reflexivity).
      assert (HOUT : cnt is_out bs (Datatypes.S i) = cnt is_out bs i + 0) by (rewrite ppl_cnt_S, Hc3; reflexivity).
      clear Hc1 Hc2 Hc3.
      ppl_e4 i regsE memE E true false Hi HE HS HJ SHOK HI0 HIN HOUT KA PA Usp E37 KH KT.
Qed.
Lemma pp_loop : forall (n i : nat) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model),
  (i + Datatypes.S n = 12)%nat ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  (forall a, 0 <= a < 2^64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memE a) ->
  getr regsE 1 = getr regs 1 -> getr regsE 2 = Z_to_bv 64 (spZ regs - 16) ->
  getr regsE 10 = Z_to_bv 64 p -> getr regsE 11 = Z_to_bv 64 q ->
  getr regsE 12 = Z_to_bv 64 (p + 8 + Z.of_nat i) -> getr regsE 16 = Z_to_bv 64 (p + 8 + Z.of_nat i) ->
  getr regsE 13 = Z_to_bv 64 (cnt is_out bs i) -> getr regsE 15 = Z_to_bv 64 (cnt is_in bs i) ->
  getr regsE 17 = Z_to_bv 64 (12 - Z.of_nat i) -> getr regsE 5 = Z_to_bv 64 2 -> getr regsE 6 = Z_to_bv 64 1 ->
  getr regsE 14 = Z_to_bv 64 SB ->
  (forall r, In r PP_CS -> getr regsE r = getr regs r) ->
  val_mem SEGS (mrestrict (w_H W) memE) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  decl bs = true ->
  SRr SEGS W (cfg_at SEGS (BASE + PP_HD) regsE memE mdE)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros n. induction n as [|n IH];
  intros i regsE memE mdE Hn HJ KP PR R1 R2 R10 R11 R12 R16 R13 R15 R17 R5 R6 R14 RCS HRA Hdecl.
- apply (ppl_iter i regsE memE mdE _ ltac:(lia)).
  + unfold ppl_inv. repeat (split; [assumption|]). assumption.
  + intros Hlt. exfalso. lia.
  + intros Hi11 regsN memN mdN HN.
    destruct HN as (HJN & KPN & PRN & R1N & R2N & R10N & R11N & _ & _ & R13N & R15N & _ & _ & _ & R14N & RCSN & HRAN).
    subst i.
    exact (pp_tail regsN memN mdN HJN KPN PRN R1N R2N R10N R11N R13N R14N R15N RCSN HRAN Hdecl).
- apply (ppl_iter i regsE memE mdE _ ltac:(lia)).
  + unfold ppl_inv. repeat (split; [assumption|]). assumption.
  + intros Hlt regsN memN mdN HN.
    destruct HN as (HJN & KPN & PRN & R1N & R2N & R10N & R11N & R12N & R16N & R13N & R15N & R17N & R5N & R6N &
      R14N & RCSN & HRAN).
    exact (IH (Datatypes.S i) regsN memN mdN ltac:(lia) HJN KPN PRN R1N R2N R10N R11N R12N R16N R13N R15N R17N
      R5N R6N R14N RCSN HRAN Hdecl).
  + intros Hi11. exfalso. lia.
Qed.
Definition pp_extraA : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (bt bs 0); Z_to_bv 64 (bt bs 1); Z_to_bv 64 (bt bs 4)].
Definition PPEA : env := Eimg (Ereg regs pp_extraA).
Definition pp_rgA : smem :=
  [ stack_region 16; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 10%nat) 0 20 0 0
      [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0));
       YP09.mkChunk 4 (CVal 1 (SOff 35 0))] ].
Definition pp_factsA : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 20) 0);
           (11%nat, mkAF 1 (2 ^ 47 - 12) 2); (32%nat, mkAF SB SB 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] [] [].
Definition pp_SHA : list shent := [mkSHE 10 0 20].
Definition pp_ssA : sstate := mkSS AF_reac_ports_parse sr_atoms pp_rgA None pp_factsA.
Lemma pp_zcanon_neg : forall z, - (2 ^ 64) <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
intros z Hz. unfold zcanon, M64.
rewrite <- (Z.mod_add z 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pp_entry :
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct pp_sp as (HspL & HspH & Hwin).
assert (Hqlo : 4096 <= q) by (destruct (pp_qb q ltac:(lia)); lia).
assert (Hqhi : q + 12 <= 2 ^ 47) by (destruct (pp_qb (q + 11) ltac:(lia)); lia).
pose proof HJ0 as HJ.
pose proof (proj1 HJ0) as HAR.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 1 ltac:(cbv [disco_nobj]; lia)) as HgotR.
pose proof (pa_obj_img 66 ltac:(cbv [disco_nobj]; lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HgotR, HcellR.
assert (Hb0 : 0 <= bt bs 0 < 256).
{ destruct (Hgarr 0%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [_ Hr].
  rewrite pp_nth_bt in Hr by lia. exact Hr. }
assert (Hb1 : 0 <= bt bs 1 < 256).
{ destruct (Hgarr 1%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [_ Hr].
  rewrite pp_nth_bt in Hr by lia. exact Hr. }
assert (Hb4 : 0 <= bt bs 4 < 256).
{ destruct (Hgarr 4%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [_ Hr].
  rewrite pp_nth_bt in Hr by lia. exact Hr. }
assert (HV0 : val_mem SEGS (mrestrict (w_H W) memc) (p + 0) 1 (bt bs 0)).
{ destruct (Hgarr 0%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [Hv _].
  rewrite pp_nth_bt in Hv by lia. exact Hv. }
assert (HV1 : val_mem SEGS (mrestrict (w_H W) memc) (p + 1) 1 (bt bs 1)).
{ destruct (Hgarr 1%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [Hv _].
  rewrite pp_nth_bt in Hv by lia. exact Hv. }
assert (HV4 : val_mem SEGS (mrestrict (w_H W) memc) (p + 4) 1 (bt bs 4)).
{ destruct (Hgarr 4%nat ltac:(first [rewrite length_map | rewrite map_length]; lia)) as [Hv _].
  rewrite pp_nth_bt in Hv by lia. exact Hv. }
remember PPEA as E eqn:HE.
assert (HEI : img_env pa_val A_LIM E) by (subst E; unfold PPEA; apply Eimg_env).
assert (ETn : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold PPEA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ETx : forall j : nat, (j < 4)%nat -> ew E (32 + j) = nth j pp_extraA (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold PPEA; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (ET32 : ew E 32 = Z_to_bv 64 SB) by (exact (ETx 0%nat ltac:(lia))).
assert (ET33 : ew E 33 = Z_to_bv 64 (bt bs 0)) by (exact (ETx 1%nat ltac:(lia))).
assert (ET34 : ew E 34 = Z_to_bv 64 (bt bs 1)) by (exact (ETx 2%nat ltac:(lia))).
assert (ET35 : ew E 35 = Z_to_bv 64 (bt bs 4)) by (exact (ETx 3%nat ltac:(lia))).
assert (ET1 : ew E 1 = getr regs 1) by (exact (ETn 1%nat 1%bv eq_refl)).
assert (ET2 : ew E 2 = getr regs 2) by (exact (ETn 2%nat 2%bv eq_refl)).
assert (ET10 : ew E 10 = Z_to_bv 64 p) by (rewrite (ETn 10%nat 10%bv eq_refl); exact H10).
assert (ET11 : ew E 11 = Z_to_bv 64 q) by (rewrite (ETn 11%nat 11%bv eq_refl); exact H11).
assert (ETo1 : ew E (A_OBJ 1) = Z_to_bv 64 (pa_val (A_OBJ 1)))
  by (subst E; unfold PPEA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (ETo66 : ew E (A_OBJ 66) = Z_to_bv 64 (pa_val (A_OBJ 66)))
  by (subst E; unfold PPEA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite ET2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs pp_extraA) E)
  by (split; [intros n Hn; subst E; unfold PPEA; apply Eimg_low; unfold A_TEXT; lia
             | subst E; reflexivity]).
assert (HUB : U E PP_Bx = SHADOW_OFF)
  by (unfold PP_Bx, U; cbn [sv_denot]; rewrite ET32, Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite unsigned_lit_small by (unfold SB; lia); exact SB_SHADOW_OFF).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (HS : st_ok_pi SEGS pa_val E pp_ssA
        (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ports_parse)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pp_ssA. apply pa_entry_st_ok_full.
  - subst E. unfold PPEA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pp_rgA, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hwin. lia.
    + rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) ETo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (pa_val (A_OBJ 66)));
      [ cbn [sv_denot]; rewrite ETo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 66) (pa_val (A_OBJ 66)) ETo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 66)) 0 8 (SOff 32 0) SB);
      [ cbn [sv_denot]; rewrite ET32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite (VB 10%nat p ET10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) (bt bs 0));
        [ cbn [sv_denot]; rewrite ET33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside | exact HV0 ].
      * apply (chunk_ok_val SEGS E _ p 1 1 (SOff 34 0) (bt bs 1));
        [ cbn [sv_denot]; rewrite ET34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside | exact HV1 ].
      * apply (chunk_ok_val SEGS E _ p 4 1 (SOff 35 0) (bt bs 4));
        [ cbn [sv_denot]; rewrite ET35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside | exact HV4 ].
  - apply pairwise_disjoint_of_extents.
    unfold pp_rgA, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat p ET10) by lia.
    rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) ETo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (pa_val (A_OBJ 66)) ETo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    repeat split; lia.
  - unfold pp_factsA. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, ET32, ET10, ET11, ET33, ET34, ET35, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PP_Bx pp_SHA E (mrestrict (w_H W) memc)).
{ unfold pp_SHA. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E PP_Bx 10 p 20 p 0 20 Hpra HUB);
  [ unfold U; cbn [sv_denot]; rewrite ET10, Z.add_0_r, Z_to_bv_bv_unsigned;
    apply unsigned_lit_small; lia
  | lia | lia
  | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]. }
assert (KP : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
assert (PR : forall a : Z, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Hx; exact Hx).
unfold cfg_at. change (w64 (BASE + AF_reac_ports_parse)) with (Z_to_bv 64 (BASE + AF_reac_ports_parse)).
paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
pp_keep Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB end.
  rewrite branch_ne_U in HB. apply (proj1 (negb_true_iff _)) in HB. apply Z.eqb_neq in HB.
  rewrite (U_atom _ 33 (bt bs 0) ltac:(pp_ewnormg; exact ET33) ltac:(lia)) in HB.
  rewrite U_lit in HB by lia.
  assert (Hdf : decl bs = false)
    by (unfold decl; rewrite (proj2 (Z.eqb_neq (bt bs 0) 1) HB); reflexivity).
  assert (Hpo : ports_ok p q bs = false)
    by (unfold ports_ok; rewrite Hdf; apply Bool.andb_false_r).
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
  pp_keep Usp.
  pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE ET1 Hra.
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB end.
  rewrite branch_ne_U in HB. apply (proj1 (negb_false_iff _)) in HB. apply Z.eqb_eq in HB.
  rewrite (U_atom _ 33 (bt bs 0) ltac:(pp_ewnormg; exact ET33) ltac:(lia)) in HB.
  rewrite U_lit in HB by lia.
  paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
  pp_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 34 0)) _ = _ |- _ => rename Hb into HB2 end.
    rewrite branch_ne_U in HB2. apply (proj1 (negb_true_iff _)) in HB2. apply Z.eqb_neq in HB2.
    rewrite (U_atom _ 34 (bt bs 1) ltac:(pp_ewnormg; exact ET34) ltac:(lia)) in HB2.
    rewrite U_lit in HB2 by lia.
    assert (Hdf : decl bs = false)
      by (unfold decl; rewrite (proj2 (Z.eqb_neq (bt bs 1) 3) HB2), Bool.andb_false_r; reflexivity).
    assert (Hpo : ports_ok p q bs = false)
      by (unfold ports_ok; rewrite Hdf; apply Bool.andb_false_r).
    paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
    pp_keep Usp.
    pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE ET1 Hra.
  + lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 34 0)) _ = _ |- _ => rename Hb into HB2 end.
    rewrite branch_ne_U in HB2. apply (proj1 (negb_false_iff _)) in HB2. apply Z.eqb_eq in HB2.
    rewrite (U_atom _ 34 (bt bs 1) ltac:(pp_ewnormg; exact ET34) ltac:(lia)) in HB2.
    rewrite U_lit in HB2 by lia.
    paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
    pp_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * lazymatch goal with Hb : branch_taken BC_LTU _ _ = _ |- _ => rename Hb into HB3 end.
      rewrite branch_ltu_U in HB3. apply Z.ltb_lt in HB3.
      rewrite U_lit in HB3 by lia.
      rewrite (U_SOff _ 35 (-128)) in HB3.
      lazymatch type of HB3 with context [ew ?Ex 35] =>
        assert (EC35 : bv_unsigned (ew Ex 35) = bt bs 4)
          by (pp_ewnormg; rewrite ET35; apply unsigned_lit_small; lia);
        rewrite EC35 in HB3 end.
      assert (Hpo : ports_ok p q bs = false).
      { unfold ports_ok, decl.
        assert (Hne : (bt bs 4 =? 128) = false /\ (bt bs 4 =? 130) = false /\ (bt bs 4 =? 132) = false).
        { destruct (Z_le_gt_dec 128 (bt bs 4)) as [Hge | Hlt].
          - rewrite zcanon_id in HB3 by (unfold M64; lia).
            repeat split; apply Z.eqb_neq; lia.
          - rewrite pp_zcanon_neg in HB3 by lia.
            repeat split; apply Z.eqb_neq; lia. }
        destruct Hne as (N1 & N2 & N3). rewrite N1, N2, N3.
        cbn [orb]. rewrite Bool.andb_false_r. apply Bool.andb_false_r. }
      paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
      pp_keep Usp.
      pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE ET1 Hra.
    * lazymatch goal with Hb : branch_taken BC_LTU _ _ = _ |- _ => rename Hb into HB3 end.
      rewrite branch_ltu_U in HB3. apply Z.ltb_ge in HB3.
      rewrite U_lit in HB3 by lia.
      rewrite (U_SOff _ 35 (-128)) in HB3.
      lazymatch type of HB3 with context [ew ?Ex 35] =>
        assert (EC35 : bv_unsigned (ew Ex 35) = bt bs 4)
          by (pp_ewnormg; rewrite ET35; apply unsigned_lit_small; lia);
        rewrite EC35 in HB3 end.
      assert (Hge : 128 <= bt bs 4 <= 132).
      { destruct (Z_le_gt_dec 128 (bt bs 4)) as [Hge | Hlt].
        - rewrite zcanon_id in HB3 by (unfold M64; lia). lia.
        - rewrite pp_zcanon_neg in HB3 by lia. lia. }
      paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
      pp_keep Usp.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- lazymatch goal with Hb : branch_taken BC_EQ _ _ = _ |- _ => rename Hb into HB4 end.
         rewrite branch_eq_U in HB4. apply Z.eqb_eq in HB4.
         rewrite U_SAlu in HB4. cbn [zalu_raw] in HB4. rewrite U_SAlu in HB4. cbn [zalu_raw] in HB4.
         rewrite !U_SLit in HB4.
         rewrite (U_SOff _ 35 (-128)) in HB4.
         lazymatch type of HB4 with context [ew ?Ex 35] =>
           assert (EC35b : bv_unsigned (ew Ex 35) = bt bs 4)
             by (pp_ewnormg; rewrite ET35; apply unsigned_lit_small; lia);
           rewrite EC35b in HB4 end.
         assert (Hpo : ports_ok p q bs = false).
         { unfold ports_ok, decl.
           assert (Hd : bt bs 4 = 129 \/ bt bs 4 = 131).
           { assert (Hcase : bt bs 4 = 128 \/ bt bs 4 = 129 \/ bt bs 4 = 130 \/ bt bs 4 = 131 \/ bt bs 4 = 132)
               by lia.
             destruct Hcase as [Hc | [Hc | [Hc | [Hc | Hc]]]]; rewrite Hc in HB4;
             try (vm_compute in HB4; discriminate HB4); tauto. }
           destruct Hd as [Hd | Hd]; rewrite Hd; cbn [Z.eqb orb];
           rewrite Bool.andb_false_r; apply Bool.andb_false_r. }
         paj_run_tok RUN HS HJ SHOK Bspan; [pp_awr (spZ regs - sp0) Usp |].
         pp_keep Usp.
         pp_ret_fail Hpo HJ0 HJ Hlo Hhi Hq63 Hqw KP PR HAE ET1 Hra.
      -- lazymatch goal with Hb : branch_taken BC_EQ _ _ = _ |- _ => rename Hb into HB4 end.
         rewrite branch_eq_U in HB4. apply Z.eqb_neq in HB4.
         rewrite U_SAlu in HB4. cbn [zalu_raw] in HB4. rewrite U_SAlu in HB4. cbn [zalu_raw] in HB4.
         rewrite !U_SLit in HB4.
         rewrite (U_SOff _ 35 (-128)) in HB4.
         lazymatch type of HB4 with context [ew ?Ex 35] =>
           assert (EC35b : bv_unsigned (ew Ex 35) = bt bs 4)
             by (pp_ewnormg; rewrite ET35; apply unsigned_lit_small; lia);
           rewrite EC35b in HB4 end.
         assert (Hdecl : decl bs = true).
         { unfold decl. rewrite HB, HB2. cbn [Z.eqb andb].
           assert (Hd : bt bs 4 = 128 \/ bt bs 4 = 130 \/ bt bs 4 = 132).
           { assert (Hcase : bt bs 4 = 128 \/ bt bs 4 = 129 \/ bt bs 4 = 130 \/ bt bs 4 = 131 \/ bt bs 4 = 132)
               by lia.
             destruct Hcase as [Hc | [Hc | [Hc | [Hc | Hc]]]]; try tauto;
             exfalso; apply HB4; rewrite Hc; vm_compute; reflexivity. }
           destruct Hd as [Hd | [Hd | Hd]]; rewrite Hd; reflexivity. }
         paj_run_to_tok RUNTO HS HJ SHOK Bspan PP_HD; [pp_awr (spZ regs - sp0) Usp |].
         pp_keep Usp.
         lazymatch goal with
         | HS : st_ok_pi _ _ ?Ecur ?ssx (restrict _ ?msc) |- _ =>
           let rst := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
           let HRs := fresh "HRs" in
           pose proof (st_ok_pi_region_nth Ecur ssx (restrict (w_H W) msc) 0 rst HS
                        ltac:(vm_compute; reflexivity)) as HRs;
           cbn [ms_mem restrict mkst] in HRs;
           assert (EC2 : bv_unsigned (ew Ecur 2) = spZ regs) by (pp_ewnormg; exact Usp);
           assert (EC1 : ew Ecur 1 = getr regs 1) by (pp_ewnormg; exact ET1);
           assert (HRA : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (spZ regs + -8) (N.to_nat 8)
                           (bv_unsigned (getr regs 1)));
           [ eapply (field_of_region _ _ 2 (spZ regs) _ (-16) 0 (-16) 0 (-8) 8%N (SOff 1 0)
                       (bv_unsigned (getr regs 1)) HRs);
             [ exact EC2 | cbn [In]; tauto
             | cbn [sv_denot]; rewrite EC1, Z.add_0_r; reflexivity
             | pose proof (u64_range (getr regs 1)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
             | change (Z.of_N 8) with 8; lia ]
           | ];
           cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HRA;
           replace (spZ regs + -8) with (spZ regs - 8) in HRA by lia;
           let R1 := fresh "RR1" in let R2 := fresh "RR2" in let R10 := fresh "RR10" in
           let R11 := fresh "RR11" in let R12 := fresh "RR12" in let R13 := fresh "RR13" in
           let R14 := fresh "RR14" in let R15 := fresh "RR15" in let R16 := fresh "RR16" in
           let R17 := fresh "RR17" in let R5 := fresh "RR5" in let R6 := fresh "RR6" in
           prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (10%bv : bv 5) R10;
           prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12; prreg HS (13%bv : bv 5) R13;
           prreg HS (14%bv : bv 5) R14; prreg HS (15%bv : bv 5) R15; prreg HS (16%bv : bv 5) R16;
           prreg HS (17%bv : bv 5) R17; prreg HS (5%bv : bv 5) R5; prreg HS (6%bv : bv 5) R6;
           pose proof pp_loop as HL; unfold cfg_at in HL;
           pmkst HS;
           apply (HL 11%nat 0%nat (ms_regs msc) (ms_mem msc) _ ltac:(reflexivity));
           [ exact HJ
           | exact KP | exact PR
           | rewrite R1; pp_ewnormg; exact ET1
           | rewrite R2; pp_ewnormg; rewrite ET2;
             first [reflexivity | f_equal; unfold spZ; lia]
           | rewrite R10; pp_ewnormg; exact ET10
           | rewrite R11; pp_ewnormg; exact ET11
           | rewrite R12; pp_ewnormg; rewrite ET10, unsigned_lit_small by lia;
             f_equal; cbn [Z.of_nat]; lia
           | rewrite R16; pp_ewnormg; rewrite ET10, unsigned_lit_small by lia;
             f_equal; cbn [Z.of_nat]; lia
           | rewrite R13; first [reflexivity | f_equal; cbn [cnt]; lia]
           | rewrite R15; first [reflexivity | f_equal; cbn [cnt]; lia]
           | rewrite R17; first [reflexivity | f_equal; cbn [Z.of_nat]; lia]
           | rewrite R5; first [reflexivity | f_equal; lia]
           | rewrite R6; first [reflexivity | f_equal; lia]
           | rewrite R14; pp_ewnormg; exact ET32
           | let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
             eapply (regs_kept_of_st_ok_pi Ecur ssx (restrict (w_H W) msc) regs pp_extraA PP_CS HS);
             [ eapply env_agree_trans;
               [ exact HAE | split; [ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; pp_ewnormg;
                   repeat match goal with |- context [Nat.eqb n ?c] =>
                     replace (Nat.eqb n c) with false by (symmetry; apply Nat.eqb_neq; lia) end;
                   reflexivity | reflexivity] ]
             | vm_compute; reflexivity
             | exact Hr ]
           | exact HRA
           | exact Hdecl ]
         end.
Qed.
End m.
End z.
Theorem pb_reac_ports_parse : treac_ports_parse_spec.
Proof.
unfold treac_ports_parse_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch p q bs
  HJ HRO Hra Hra4 Hgp Htp H10 H11 Hp Hq Hch Hsp16 Hlo Hhi Hq63 Hqw Hcond.
destruct (Z.eqb_spec p 0) as [Hp0 | Hp0];
  [ eapply pp_zero; try eassumption; left; exact Hp0 | ].
destruct (Z.eqb_spec q 0) as [Hq0 | Hq0];
  [ eapply pp_zero; try eassumption; right; exact Hq0 | ].
destruct (Hcond Hp0 Hq0) as (Hlen & Hp47 & Hpimg & Hpapp & Hpwin & Hpra & Hppres & Hgarr &
                             Hq4 & Hqp & Hqapp & Hqra & Hqawr).
eapply pp_entry; eassumption.
Qed.
End h.
End f.
End d.

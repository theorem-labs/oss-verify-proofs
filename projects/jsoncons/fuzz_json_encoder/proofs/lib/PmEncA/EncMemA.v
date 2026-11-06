(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EMA.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Lemma aacc_of_shz : forall (M : mem) q g p m, shadow_zero M q g -> q mod 8 = 0 -> q <= p -> p + m <= q + 8 * g -> aacc M p m.
Proof.
  intros M q g p m SZ Q8 H1 H2 a Ha. left. unfold shadow_zero, byte_at in SZ |- *.
  assert (E : S a = S q + (a / 8 - q / 8)) by (unfold S; lia).
  assert (Q : a / 8 - q / 8 = (a - q) / 8).
  { apply Z.mod_divide in Q8; [|lia]. destruct Q8 as [k ->]. replace (a - k * 8) with ((a - k * 8) + 0) by lia. rewrite Z.div_mul by lia.
    replace (a - k * 8 + 0) with (a + (- k) * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite E, Q. apply SZ. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section Rt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Variable FPI : FPState -> Prop.
Variable onmax : Z.

(* [comment removed for export] *)
Definition mem_dstX (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (M : mem) (dst n : Z) : Prop :=
  0 <= n <= onmax /\ aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF sp scr (dst + i)) /\ L5.writable (hl_segs L) M dst n /\ app_rng ar dst n.

Lemma amem_preX_of : forall scr fx (R : bvmap 5 word) (M : mem) model LB FF LK cr A dst n sp r K,
  0 <= hl_scr_mem L <= scr ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> CHA.astk ar M sp scr ->
  getr R 10%bv = Z_to_bv 64 dst -> getr R 12%bv = Z_to_bv 64 n -> mem_dstX LB FF sp scr M dst n ->
  PMESA.amem_preX L ar HI onmax fx R M model LB FF LK cr A dst n K.
Proof.
  intros scr fx R M model LB FF LK cr A dst n sp r K Hscr HH Hmo HK Hra Hraok Hsp Htp Hstk Ha0 Ha2 (D1 & D2 & D3 & D4 & D5).
  pose proof (CRC.usp ar R M sp scr ltac:(lia) Hsp Hstk) as USP. unfold PMESA.amem_preX. rewrite USP.
  split; [exact HH|]. split; [exact (proj1 Hmo)|]. split; [exact (proj2 Hmo)|]. split; [exact Ha0|]. split; [exact Ha2|]. split; [exact D1|]. split; [exact Htp|].
  split; [exact (CRC.ret_ok_of_ra R r Hra Hraok)|]. split; [exact (CRC.astack_ok_of_astk L ar M sp scr _ Hscr Hstk)|]. split; [exact D2|].
  split; [intros i Hi; exact (CRC.aclientw_scr0 L ar _ _ _ _ _ _ Hscr (D3 i Hi))|]. split; [exact D4|]. split; [exact HK | exact D5].
Qed.

Definition memcpy_preX (LB : list (Z * Z)) (FF : list fframe) (sp scr dst src n : Z) (bs : list byte) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 11%bv = Z_to_bv 64 src /\ getr R 12%bv = Z_to_bv 64 n /\
  mem_dstX LB FF sp scr M dst n /\ CRC.mem_src L ar LB FF sp scr M src n bs /\ (dst + n <= src \/ src + n <= dst).

(* [comment removed for export] *)
Lemma memcpy_cpsX : forall pc, PMESA.amemcpy_x_spec_at L ar HI onmax pc false ->
  forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (memcpy_preX LB FF sp scr dst src n bs) (CRC.memcpy_post LB cr dst n bs).
Proof.
  intros pc SPEC scr LB FF LK cr A dst src n bs sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Ha1 & Ha2 & HD & (S1 & S2 & S3 & S4 & S5) & Hov) CONT.
  pose proof (CRC.usp ar R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (SPEC fx R M model LB FF LK cr A dst src n bs K (amem_preX_of scr fx R M model LB FF LK cr A dst n sp r K Hscr HH Hmo HK Hra Hraok Hsp Htp Hstk Ha0 Ha2 HD) Ha1 S1 S2 S3).
  - rewrite USP. intros i Hi. destruct (S4 i Hi) as [X|X]; [left; exact X | right; exact (CRC.aclient_scr0 L ar _ _ _ _ _ _ Hscr X)].
  - exact S5.
  - intros _. exact Hov.
  - apply (CRC.amem_post_of L ar HI FPI scr fx R M model LB FF LK cr A dst n sp r K _ Hscr Hmo HFP Hra Hsp Hstk). exact CONT.
Qed.

(* [comment removed for export] *)
Lemma dst_in_blockX : forall LB FF LK cr A (M : mem) V sp scr u m dst n,
  ri_inv HI LB FF LK cr A M V -> In (u, m) LB -> shadow_blk M u m -> u <= dst -> dst + n <= u + m -> 0 <= n <= onmax ->
  mem_dstX LB FF sp scr M dst n.
Proof.
  intros LB FF LK cr A M V sp scr u m dst n HH Hin Hsh H1 H2 Hn.
  destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
  destruct (WF (u, m) Hin) as (HBR & HDF & _). cbn [fst snd] in HBR, HDF. destruct HBR as (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)).
  assert (U8 : u mod 8 = 0) by (apply CHA.mod8_of_16; exact B3).
  split; [exact Hn|]. split; [exact (CRC.aacc_blk M u m dst n Hsh U8 ltac:(lia) H1 H2)|]. split; [|split].
  - intros i Hi. left. exists (u, m). split; [exact Hin | cbn [fst snd]; lia].
  - assert (D : L5.defined M dst n) by (intros i Hi; replace (dst + i) with (u + (dst - u + i)) by lia; apply HDF; lia).
    exact (L5C.writable_of_defined (hl_segs L) M _ _ D ltac:(lia) ltac:(lia)).
  - unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; [lia|]. split; [lia|]. left.
    destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _). lia.
Qed.

(* [comment removed for export] *)
Lemma img_aacc_of_global : forall IL g sz q k, rt_globals IL HI -> In (g, sz) (icl_globals IL) -> g mod 8 = 0 -> 0 <= g -> g <= q -> q + k <= g + sz ->
  PMESA.img_aacc HI q k.
Proof.
  intros IL g sz q k RG Hin G8 G0 H1 H2 LB FF LK cr A M V HH.
  pose proof (proj1 (proj1 (Forall_forall _ _) (RG _ _ _ _ _ _ _ HH) (g, sz) Hin)) as SB. cbn [fst snd] in SB.
  exact (CRC.aacc_blk M g sz q k SB G8 G0 H1 H2).
Qed.
Lemma img_aacc_of_img_shadow : forall IL q k, rt_img_shadow L IL HI -> hl_img_lo L <= q - q mod 8 -> q - q mod 8 + 8 * ((q mod 8 + k + 7) / 8) <= hl_img_hi L -> 0 <= q -> 0 <= k ->
  Forall (fun r => q - q mod 8 + 8 * ((q mod 8 + k + 7) / 8) <= fst r \/ snd r <= q - q mod 8) (icl_poison IL) ->
  PMESA.img_aacc HI q k.
Proof.
  intros IL q k ISH Hlo Hhi Hq Hk POI LB FF LK cr A M V HH a Ha. left.
  set (g := (q mod 8 + k + 7) / 8) in *.
  assert (Hg : 0 < g) by (unfold g; apply Z.div_str_pos; pose proof (Z.mod_pos_bound q 8 ltac:(lia)); lia).
  destruct (ISH _ _ _ _ _ _ _ HH (q - q mod 8) (8 * g) Hlo Hhi ltac:(lia) POI) as [BZ _].
  apply BZ. unfold in_shadow_of, S. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as MB. pose proof (Z_div_mod_eq_full q 8) as DQ.
  assert (D1 : (q - q mod 8) / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : a / 8 <= (q - q mod 8 + 8 * g - 1) / 8).
  { apply Z.div_le_mono; [lia|]. assert (a - (q - q mod 8) < 8 * g); [|lia]. unfold g.
    pose proof (Z.mul_div_le (q mod 8 + k + 7) 8 ltac:(lia)) as X. pose proof (Z_div_mod_eq_full (q mod 8 + k + 7) 8). pose proof (Z.mod_pos_bound (q mod 8 + k + 7) 8 ltac:(lia)). lia. }
  lia.
Qed.
End Rt.
End EMA.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LibIface AllocCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BSegs BakeStackRep BsShadow BsConst BsIface BsCXXHeap BXXRep LbB_Conv LbB_Bridge.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HRep HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint c8log (b : expr) (off : Z) (vs : list expr) : list sentry :=
  match vs with
  | [] => []
  | v :: vs' => SE (SA b off) 8 v :: c8log b (off + 8) vs'
  end.

Lemma cells_size_map_C8 : forall (f : expr -> word) vs, cells_size (map (fun v => C8 (f v)) vs) = (8 * length vs)%nat.
Proof. intros f vs. induction vs as [|v vs IH]; [reflexivity|]. cbn [map cells_size csize]. rewrite IH. cbn [length]. lia. Qed.

Lemma estart_off : forall E b off d, estart E (SA b (off + d)) = estart E (SA b off) + d.
Proof. intros. unfold estart. cbn [a_base a_off]. lia. Qed.

Lemma rw_cells_c8log : forall E m b vs off A,
  log_flat E (c8log b off vs) -> estart E (SA b off) = A ->
  wr_at asegs m A (8 * Z.of_nat (length vs)) ->
  rw_cells asegs (mem_denot E m (c8log b off vs)) A (map (fun v => C8 (edenot E v)) vs).
Proof.
  intros E m b vs. induction vs as [|v vs IH]; intros off A Hf HA HW.
  - cbn [c8log map mem_denot]. split; [split|].
    + exact I.
    + cbn [cells_bytes]. destruct HW as (W1 & W2 & _). split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
    + cbn [cells_size]. destruct HW as (W1 & W2 & _). split; [lia|]. split; [lia|]. intros i Hi; cbn in Hi; lia.
  - pose proof Hf as Hf0. cbn [c8log log_flat] in Hf0. destruct Hf0 as (_ & Hfl & Hfr).
    change (map (fun v0 => C8 (edenot E v0)) (v :: vs)) with ([C8 (edenot E v)] ++ map (fun v0 => C8 (edenot E v0)) vs).
    apply rw_cells_app. split.
    + change (c8log b off (v :: vs)) with ([] ++ SE (SA b off) 8 v :: c8log b (off + 8) vs).
      eapply (rw_cells_mem_denot_w E m [] (SA b off) 8 v (c8log b (off + 8) vs) A (C8 (edenot E v)));
        [exact Hf | apply Forall_nil | exact HA | | reflexivity | exact I | reflexivity].
      cbn [length] in HW. destruct HW as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
    + cbn [cells_size csize]. change (Z.of_nat (8 + 0)) with 8.
      change (mem_denot E m (c8log b off (v :: vs))) with (mem_denot E (mem_denot E m (c8log b (off + 8) vs)) [SE (SA b off) 8 v]).
      eapply rw_cells_transport.
      * apply (IH (off + 8) (A + 8)); [exact Hfr | rewrite estart_off; lia |].
        cbn [length] in HW. destruct HW as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi.
        replace (A + 8 + i) with (A + (8 + i)) by lia. apply W. lia.
      * apply (munch_mem_denot [(A, A + 8)]); [cbn [log_flat]; split; [lia|]; split; [exact Hfl | exact I]|].
        apply Forall_cons; [|apply Forall_nil]. cbn [e_addr e_width]. rewrite HA. cbn. lia.
      * apply wmono_mem_denot.
      * cbn [disjoint_from]. split; [|exact I]. rewrite cells_size_map_C8. lia.
Qed.

Lemma seg_rom_hiA : forall x : word, AIMG_TOP <= bv_unsigned x -> PropExec.seg_rom asegs x = None.
Proof.
  intros x Hx. unfold PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1%Z. unfold AIMG_TOP in Hx.
  change AsanUbsan.M.loaded_segments with asegs. rewrite BakeStackRep.find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x91000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x91000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x17e000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x17e000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x186000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x186000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x6e8000); cbn [andb]; try lia; reflexivity.
Qed.

Lemma wa_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (wa z) = z.
Proof. intros z Hz. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia. Qed.

Lemma wr_at_of_bytes_hi : forall m a bs,
  bytes_at asegs m a bs -> AIMG_TOP <= a -> wr_at asegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (B0 & B1 & B) Ha. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (B (Z.to_nat i) ltac:(lia)) as Bi. rewrite Z2Nat.id in Bi by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  rewrite (BakeStackRep.wview_high m (wa (a + i))) by (rewrite wa_unsigned by lia; lia).
  unfold mrd in Bi. destruct (m (wa (a + i))) as [b'|] eqn:E; [discriminate|].
  change (BLPropExec.seg_rom asegs (wa (a + i))) with (PropExec.seg_rom asegs (wa (a + i))) in Bi.
  rewrite seg_rom_hiA in Bi by (rewrite wa_unsigned by lia; lia). discriminate.
Qed.

Lemma rw_cells_of_cellw8 : forall M a v, HRep.cellw asegs M a 8 v -> AIMG_TOP <= a -> a + 8 <= 2 ^ 64 ->
  rw_cells asegs M a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v [Hv Hr] Ha Ha8. pose proof Ha as Ha0. unfold AIMG_TOP in Ha0.
  assert (BA : bytes_at asegs M a (word_to_le_bytes 8 (Z_to_bv 64 v))).
  { apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; lia | rewrite CatExec.length_N_to_le_bytes; exact Hr]. }
  split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA]|].
  pose proof (wr_at_of_bytes_hi M a _ BA Ha) as W. rewrite CatExec.length_N_to_le_bytes in W. exact W.
Qed.

Lemma rw_cells_of_cellw4 : forall M a v, HRep.cellw asegs M a 4 v -> AIMG_TOP <= a -> a + 4 <= 2 ^ 64 ->
  rw_cells asegs M a [C4 (Z_to_bv 64 v)].
Proof.
  intros M a v [Hv Hr] Ha Ha8. pose proof Ha as Ha0. unfold AIMG_TOP in Ha0.
  assert (BA : bytes_at asegs M a (word_to_le_bytes 4 (Z_to_bv 64 v))).
  { apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; lia | rewrite CatExec.length_N_to_le_bytes; exact Hr]. }
  split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA]|].
  pose proof (wr_at_of_bytes_hi M a _ BA Ha) as W. rewrite CatExec.length_N_to_le_bytes in W. exact W.
Qed.

Definition log_ivs (E : env) (lg : list sentry) : list (Z * Z) :=
  map (fun se => (estart E (e_addr se), estart E (e_addr se) + Z.of_nat (e_width se))) lg.

Lemma munch_log : forall E m lg, log_flat E lg -> munch (log_ivs E lg) m (mem_denot E m lg).
Proof.
  intros E m lg Hf. apply munch_mem_denot; [exact Hf|].
  induction lg as [|[a w v] lg IH]; [apply Forall_nil|]. cbn [log_flat] in Hf. destruct Hf as (_ & _ & Hf).
  apply Forall_cons.
  - cbn [e_addr e_width log_ivs map inside]. left. lia.
  - eapply Forall_impl; [|exact (IH Hf)]. intros se Hse. cbn [log_ivs map inside]. right. exact Hse.
Qed.

Ltac rwc_norm := unfold estart; evs; rewrite ?w_mul, ?w_add, ?w_addm, ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia.
Ltac rwc_new Hlf WR :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m ?lg) ?A [?c] =>
    let rec go pre post :=
      lazymatch post with
      | SE ?a ?w ?v :: ?post' =>
          first [ eapply (rw_cells_mem_denot_w E m pre a w v post' A c);
                  [ exact Hlf
                  | repeat (apply Forall_cons; [cbn [e_addr e_width]; rwc_norm|]); apply Forall_nil
                  | rwc_norm
                  | exact WR | reflexivity | exact I | evs; reflexivity ]
                | let pre' := eval cbn [app] in (pre ++ [SE a w v]) in go pre' post' ]
      end in
    go (@nil sentry) lg
  end.
Ltac rwc_keep H Hlf :=
  eapply rw_cells_transport; [exact H | apply munch_log; exact Hlf | apply wmono_mem_denot |
    unfold log_ivs; cbn [map disjoint_from e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
    cbn [a_off a_base Z.of_nat cells_size csize]; repeat split; lia].

Section SRms.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Lemma sr_ms : forall (Q : config -> Prop) s msF mo ms ms',
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> CatSim.msteps asegs ms ms' ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_VIS H s msF' = ms' -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q s msF mo ms ms' KR VIS Hms K.
    eapply (ahh_evt_then H HH (fun x => x = ms')); [exact KR | exact VIS | eapply evt_of_msteps_done; [exact Hms | reflexivity] |].
    intros msF' mo' KR' MP' HV. apply K; assumption.
  Qed.
End SRms.

Definition hdr40 (m : mem) (o : Z) (bl bc fst sz : word) (mlf : word) (pad : list byte) : Prop :=
  rw_cells asegs m o [C8 bl; C8 bc; C8 fst; C8 sz; C4 mlf; CB 4 pad].

Lemma rw_cells_addr : forall m a a' cs, rw_cells asegs m a cs -> a = a' -> rw_cells asegs m a' cs.
Proof. intros m a a' cs H ->. exact H. Qed.

Lemma hdr40_split : forall m o bl bc fst sz mlf pad,
  hdr40 m o bl bc fst sz mlf pad ->
  rw_cells asegs m o [C8 bl] /\ rw_cells asegs m (o + 8) [C8 bc] /\ rw_cells asegs m (o + 16) [C8 fst]
  /\ rw_cells asegs m (o + 24) [C8 sz] /\ rw_cells asegs m (o + 32) [C4 mlf] /\ rw_cells asegs m (o + 36) [CB 4 pad].
Proof.
  intros m o bl bc fst sz mlf pad Hh. unfold hdr40 in Hh.
  change [C8 bl; C8 bc; C8 fst; C8 sz; C4 mlf; CB 4 pad] with ([C8 bl] ++ [C8 bc] ++ [C8 fst] ++ [C8 sz] ++ [C4 mlf] ++ [CB 4 pad]) in Hh.
  apply rw_cells_app in Hh. destruct Hh as [H0 Hh]. cbn [cells_size csize] in Hh.
  apply rw_cells_app in Hh. destruct Hh as [H1 Hh]. cbn [cells_size csize] in Hh.
  apply rw_cells_app in Hh. destruct Hh as [H2 Hh]. cbn [cells_size csize] in Hh.
  apply rw_cells_app in Hh. destruct Hh as [H3 Hh]. cbn [cells_size csize] in Hh.
  apply rw_cells_app in Hh. destruct Hh as [H4 H5]. cbn [cells_size csize] in H5.
  split; [exact H0|]. split; [eapply rw_cells_addr; [exact H1 | lia]|]. split; [eapply rw_cells_addr; [exact H2 | lia]|].
  split; [eapply rw_cells_addr; [exact H3 | lia]|]. split; [eapply rw_cells_addr; [exact H4 | lia]|]. eapply rw_cells_addr; [exact H5 | lia].
Qed.

Lemma hdr40_join : forall m o bl bc fst sz mlf pad,
  rw_cells asegs m o [C8 bl] -> rw_cells asegs m (o + 8) [C8 bc] -> rw_cells asegs m (o + 16) [C8 fst] ->
  rw_cells asegs m (o + 24) [C8 sz] -> rw_cells asegs m (o + 32) [C4 mlf] -> rw_cells asegs m (o + 36) [CB 4 pad] ->
  hdr40 m o bl bc fst sz mlf pad.
Proof.
  intros m o bl bc fst sz mlf pad H0 H1 H2 H3 H4 H5. unfold hdr40.
  change [C8 bl; C8 bc; C8 fst; C8 sz; C4 mlf; CB 4 pad] with ([C8 bl] ++ [C8 bc] ++ [C8 fst] ++ [C8 sz] ++ [C4 mlf] ++ [CB 4 pad]).
  apply rw_cells_app. split; [exact H0|]. cbn [cells_size csize]. replace (o + Z.of_nat (8 + 0)) with (o + 8) by lia.
  apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. replace (o + 8 + Z.of_nat (8 + 0)) with (o + 16) by lia.
  apply rw_cells_app. split; [exact H2|]. cbn [cells_size csize]. replace (o + 16 + Z.of_nat (8 + 0)) with (o + 24) by lia.
  apply rw_cells_app. split; [exact H3|]. cbn [cells_size csize]. replace (o + 24 + Z.of_nat (8 + 0)) with (o + 32) by lia.
  apply rw_cells_app. split; [exact H4|]. cbn [cells_size csize]. replace (o + 32 + Z.of_nat (4 + 0)) with (o + 36) by lia.
  exact H5.
Qed.

Section Rehost.
  Context {AC : AllocCeil.AllocCeiling}.
  Variable SEGS : list Segment.
  Variable L : LibIface.Layout.
  Variable MI : LibIface.MallocIface SEGS L.
  Variables (NS : Z) (V : Type) (nval : LibIface.mem -> Z -> V -> Prop).
  Hypothesis HNS : 24 <= NS.
  Hypothesis nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v.

  Lemma umapx_rehost : forall (A A' : LibIface.AS MI) M M' obj obj' bl bc (ents : list (Z * (Z * V))),
    HRep.umapx MI NS nval A M obj bl bc ents ->
    HRep.cell8 SEGS M' obj' bl -> HRep.cell8 SEGS M' (obj' + 8) bc -> HRep.cell8 SEGS M' (obj' + 16) (HRep.hdaddr ents) ->
    HRep.cell8 SEGS M' (obj' + 24) (HRep.Zlength ents) -> HRep.cell4 SEGS M' (obj' + 32) 0x3f800000 -> HRep.defined M' obj' 40 ->
    obj' mod 8 = 0 -> 0 < obj' -> obj' + 40 <= 2 ^ 47 ->
    (forall p k v, In (p, (k, v)) ents -> HRepFacts.agree_on M M' p NS) ->
    (forall i, 0 <= i < bc -> (ents = [] \/ i <> HRep.hmod (HRep.hdkey ents) bc) -> HRepFacts.agree_on M M' (bl + 8 * i) 8) ->
    (ents <> [] -> HRep.cell8 SEGS M' (bl + 8 * HRep.hmod (HRep.hdkey ents) bc) (obj' + 16)) ->
    (bc <> 0 -> HRep.apart bl (8 * bc) obj' 40) -> (forall p, In p (map fst ents) -> HRep.apart p NS obj' 40) ->
    (forall p n, In (p, n) (HRep.umap_blocks NS bl bc ents) -> In (p, n) (LibIface.live MI A) -> In (p, n) (LibIface.live MI A')) ->
    HRep.umapx MI NS nval A' M' obj' bl bc ents.
  Proof.
    intros A A' M M' obj obj' bl bc ents U Cbl Cbc Cp1 Csz Cmlf Cdef Hal Hlo Hhi Hnd Hbk Hsent Hapb Hapn Hlive.
    destruct U as [HD Hoal Holo Hohi Hbseq Hload Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
    constructor; try assumption.
    - constructor; assumption.
    - destruct Hblive as [[Hbc0 Hbl0] | [Hbc1 Hin]]; [left; split; assumption | right].
      split; [exact Hbc1|]. apply Hlive; [|exact Hin]. unfold HRep.umap_blocks.
      destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - intros i Hi. destruct (Hbkt i Hi) as (b & Hcell & Hok).
      assert (Hcase : ents = [] \/ i <> HRep.hmod (HRep.hdkey ents) bc \/ (ents <> [] /\ i = HRep.hmod (HRep.hdkey ents) bc)).
      { destruct ents; [left; reflexivity|]. destruct (Z.eq_dec i (HRep.hmod (HRep.hdkey (p :: ents)) bc)); [right; right; split; [discriminate| assumption] | right; left; assumption]. }
      destruct Hcase as [Hc | [Hc | [Hne Hc]]].
      + exists b. split; [| destruct Hok as [H|[H|(H1 & H2 & H3)]]; [left; exact H | right; left; exact H | exfalso; exact (H2 Hc)]].
        eapply HRepFacts.cellw_agree; [exact Hcell | apply Hbk; [exact Hi | left; exact Hc] | lia | cbn; lia].
      + exists b. split; [| destruct Hok as [H|[H|(H1 & H2 & H3)]]; [left; exact H | right; left; exact H | exfalso; exact (Hc H3)]].
        eapply HRepFacts.cellw_agree; [exact Hcell | apply Hbk; [exact Hi | right; exact Hc] | lia | cbn; lia].
      + exists (obj' + 16). subst i. split; [exact (Hsent Hne)|]. right; right. split; [reflexivity|]. split; [exact Hne | reflexivity].
    - eapply HRepFacts.chain_agree; [exact Hch|]. intros p k v Hin. destruct (Hnode p k v Hin) as (_ & Hp0 & Hp1 & _).
      split; [|lia]. eapply HRepFacts.agree_on_sub; [eapply Hnd; exact Hin | lia | lia].
    - intros p k v Hin. destruct (Hnode p k v Hin) as (Hlv & Hp0 & Hp1 & Hpal & Hh & Hk & Hkr & Hv & Hap1 & Hap2).
      pose proof (Hnd p k v Hin) as Hag.
      split; [|split; [exact Hp0|split; [exact Hp1|split; [exact Hpal|split; [|split; [|split; [exact Hkr|split; [|split; [|exact Hap2]]]]]]]]].
      + apply Hlive; [|exact Hlv]. unfold HRep.umap_blocks. apply in_app_iff. right.
        apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
      + eapply HRepFacts.cellw_agree; [exact Hh | eapply HRepFacts.agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply HRepFacts.cellw_agree; [exact Hk | eapply HRepFacts.agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply nval_agree; [exact Hv | eapply HRepFacts.agree_on_sub; [exact Hag | lia | lia] | lia | lia].
      + apply Hapn. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
  Qed.
End Rehost.

Lemma cellw8_of_rw_cells : forall m a v, rw_cells asegs m a [C8 (Z_to_bv 64 v)] -> 0 <= v < 2 ^ 64 -> 0 <= a ->
  HRep.cellw asegs m a 8 v.
Proof.
  intros m a v Hc Hv Ha. split; [cbn; lia|].
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma cellw4_of_rw_cells : forall m a v, rw_cells asegs m a [C4 (Z_to_bv 64 v)] -> 0 <= v < 2 ^ 32 -> 0 <= a ->
  HRep.cellw asegs m a 4 v.
Proof.
  intros m a v Hc Hv Ha. split; [cbn; lia|].
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma defined_of_rw_cells_hi : forall m A cs, rw_cells asegs m A cs -> AIMG_TOP <= A ->
  HRep.defined m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf HB] _] Ha i Hi. pose proof HB as (B0 & B1 & B).
  rewrite (cells_bytes_length cs Hwf) in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat i)) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; rewrite (cells_bytes_length cs Hwf) in Eb; lia].
  unfold mrd in B. change (wa (A + i)) with (Z_to_bv 64 (A + i)) in B.
  destruct (m (Z_to_bv 64 (A + i))) as [b'|] eqn:E; [discriminate|].
  change (BLPropExec.seg_rom asegs (Z_to_bv 64 (A + i))) with (PropExec.seg_rom asegs (Z_to_bv 64 (A + i))) in B.
  rewrite seg_rom_hiA in B by (change (Z_to_bv 64 (A + i)) with (wa (A + i)); rewrite wa_unsigned; unfold AIMG_TOP in *; lia).
  discriminate.
Qed.

Section XP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Lemma agree_of_xpres : forall LB SP X m0 m a n,
    xpres H LB SP X m0 m -> (forall i, 0 <= i < n -> xclient H LB SP X (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 ->
    HRepFacts.agree_on m0 m a n.
  Proof.
    intros LB SP X m0 m a n XP HC Ha Han i Hi. destruct (XP (a + i) ltac:(lia) (HC i Hi)) as [E _]. exact E.
  Qed.
End XP.

Lemma sh_below_ahi : forall x, 0 <= x < 2 ^ 47 -> ASHADOW_BASE <= sh x < AHI_LO.
Proof. intros x Hx. unfold sh, ASHADOW_BASE, AHI_LO. split; [pose proof (Z.div_pos x 8); lia | apply Z.lt_add_lt_sub_l; apply Z.div_lt_upper_bound; lia]. Qed.

Lemma nodup_app_disj : forall (T : Type) (l1 l2 : list T) (a : T), List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
  intros T l1. induction l1 as [|x l1 IH]; intros l2 a ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst. destruct H1 as [<-|H1].
  - apply NI. apply in_or_app. right. exact H2.
  - exact (IH l2 a ND' H1 H2).
Qed.

Section BlkW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma xpres_blk_write : forall s LB LB0 LBr SP X m0 m m' a n q A N,
    xpres H LB0 SP X m0 m -> as_RHEAP H s LB m -> Permutation LB (LB0 ++ LBr) -> In (q, A, N) LBr ->
    A <= a -> a + n <= A + N -> aceil <= SP ->
    munch [(a, a + n)] m m' -> wmono asegs m m' ->
    xpres H LB0 SP X m0 m'.
  Proof.
    intros s LB LB0 LBr SP X m0 m m' a n q A N XP RH PE INq Ha Han HSP MU WM x Hx [Hc Hnx].
    destruct (XP x Hx (conj Hc Hnx)) as [E W].
    assert (INqL : In (q, A, N) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact INq).
    pose proof (ah_blocks H HH _ _ _ _ RH INqL) as (B0 & B16 & Bn & BI & BC & BF & BA). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    assert (OUT : ~ (a <= x < a + n) -> m' (wa x) = m (wa x)).
    { intros Hn. apply MU. rewrite wa_unsigned by lia. cbn. split; [lia | exact I]. }
    split; [| intros Hw; apply WM; apply W; exact Hw].
    rewrite <- E. destruct (Z.lt_ge_cases x a) as [Lx|Lx]; [apply OUT; lia|].
    destruct (Z.lt_ge_cases x (a + n)) as [Ux|Ux]; [|apply OUT; lia].
    exfalso.
    assert (XAPP : x < ALOWSH_LO \/ AHI_LO <= x).
    { unfold aapp, aapp_lo, aapp_hi in BA. lia. }
    assert (SHR : forall y, 0 <= y < 2 ^ 47 -> ASHADOW_BASE <= sh y < AHI_LO) by exact sh_below_ahi.
    unfold ALOWSH_LO, AHI_LO, ASHADOW_BASE, AFS_SIZE in *. unfold AIMG_TOP in BI, FB1.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hbr)|[(b & Hb & Hbr)|[Hc|[Hc|Hc]]]]]].
    - lia.
    - unfold aimg_client in Hc. lia.
    - assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
      destruct (Z.eq_dec (blk_id b) q) as [Eq|Ne].
      + pose proof (ah_nodup H HH _ _ _ RH) as ND.
        pose proof (Stdlib.Sorting.Permutation.Permutation_NoDup (Permutation_map blk_id PE) ND) as ND'. rewrite map_app in ND'.
        apply (nodup_app_disj _ _ _ q ND').
        * apply in_map_iff. exists b. split; [exact Eq | exact Hb].
        * apply in_map_iff. exists (q, A, N). split; [reflexivity | exact INq].
      + pose proof (ah_disj H HH _ _ _ _ _ RH HbL INqL Ne) as D. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D. lia.
    - assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
      pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (C0 & C16 & Cn & CI & CC & CF & CA).
      pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(lia) Cn ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      pose proof (SHR (blk_addr b) ltac:(lia)) as S1. lia.
    - unfold AFS_SIZE in Hc. lia.
    - unfold AFS_SIZE in Hc. pose proof (SHR (as_FSB H) ltac:(lia)) as S1.
      pose proof (sh_nsh_high (as_FSB H) 0xb09000 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      assert (sh (as_FSB H + 0xb09000) <= sh (as_FSB H) + nsh 0xb09000) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
    - unfold AHI_LO in Hc. assert (AC0 : 0 <= aceil < 2 ^ 47) by (clear - ACF1 ACF2; lia). pose proof (SHR aceil AC0) as S1. clear - S1 Hc XAPP Lx Ux Ha Han. lia.
  Qed.
End BlkW.

Lemma rw_cells_zero16 : forall m A, rw_cells asegs m A [CB 16 (poison_bytes 16 0)] ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf HB] HW]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in HB. rewrite app_nil_r.
    replace (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) with (poison_bytes 16 0) by (vm_compute; reflexivity). exact HB.
  - cbn [cells_size csize] in *. exact HW.
Qed.

Ltac arith_leaf T :=
  lazymatch T with
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | Peano.le _ _ => idtac | Peano.lt _ _ => idtac | Peano.ge _ _ => idtac | Peano.gt _ _ => idtac
  | N.le _ _ => idtac | N.lt _ _ => idtac
  | False => idtac
  end.

Ltac has_arith T :=
  lazymatch T with
  | ?A /\ ?B => first [has_arith A | has_arith B]
  | ?A \/ ?B => first [has_arith A | has_arith B]
  | ?A <-> ?B => first [has_arith A | has_arith B]
  | ~ ?A => has_arith A
  | ?A -> ?B => first [has_arith A | has_arith B]
  | _ => arith_leaf T
  end.
Ltac clear_nonarith :=
  repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop => tryif has_arith T then fail else clear H end
  end.
Ltac lia_walk := clear_nonarith; Zify.zify; xlia zchecker.

Section LbRm.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma lb_remove_perm : forall LB p A n,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB -> Permutation LB ((p, A, n) :: as_lb_remove H p LB).
  Proof.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB as [|b LB IH]; intros p A n ND IN; [destruct IN|].
    cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
    destruct (Z.eq_dec (blk_id b) p) as [E|NE].
    - destruct IN as [->|IN].
      + rewrite L1; [apply Permutation_refl | exact NI].
      + exfalso. apply NI. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact IN].
    - rewrite (L2 p b LB NE). destruct IN as [->|IN]; [cbn in NE; lia|].
      eapply perm_trans; [apply perm_skip; exact (IH p A n ND' IN) | apply perm_swap].
  Qed.

  Lemma lb_remove_perm_app : forall LB LB0 LBr p A n,
    List.NoDup (map blk_id LB) -> Permutation LB (LB0 ++ (p, A, n) :: LBr) ->
    Permutation (as_lb_remove H p LB) (LB0 ++ LBr).
  Proof.
    intros LB LB0 LBr p A n ND PE.
    assert (IN : In (p, A, n) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; left; reflexivity).
    pose proof (lb_remove_perm LB p A n ND IN) as P1.
    apply (Permutation_cons_inv (a := (p, A, n))).
    eapply perm_trans; [exact (Permutation_sym P1)|]. eapply perm_trans; [exact PE|].
    apply Permutation_sym. apply Permutation_middle.
  Qed.
End LbRm.

Set Printing Implicit.
Section XPM.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition wmix (LBr : list block) (SP : Z) (X : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)
    \/ (exists q A N, In (q, A, N) LBr /\ A <= fst iv /\ snd iv <= A + N).

  Lemma xpres_munch_mixed : forall s LB LBx LBr SP X W m0 m m',
    xpres H LBx SP X m0 m -> as_RHEAP H s LB m -> Permutation LB (LBx ++ LBr) -> aceil <= SP ->
    munch W m m' -> wmono asegs m m' -> Forall (wmix LBr SP X) W ->
    xpres H LBx SP X m0 m'.
  Proof.
    intros s LB LBx LBr SP X W m0 m m' XP RH PE HSP MU WM FW x Hx [Hc Hnx].
    destruct (XP x Hx (conj Hc Hnx)) as [E Wv].
    split; [| intros Hw; apply WM; apply Wv; exact Hw].
    rewrite <- E.
    assert (OUTW : outside W x \/ exists iv, In iv W /\ fst iv <= x < snd iv).
    { clear - W. induction W as [|[l h] W IH]; [left; exact I|]. cbn [outside].
      destruct (Z_le_dec l x); destruct (Z_lt_dec x h).
      - right. exists (l, h). split; [left; reflexivity | cbn; lia].
      - destruct IH as [IH|(iv & Hi & Hr)]; [left; split; [lia | exact IH] | right; exists iv; split; [right; exact Hi | exact Hr]].
      - destruct IH as [IH|(iv & Hi & Hr)]; [left; split; [lia | exact IH] | right; exists iv; split; [right; exact Hi | exact Hr]].
      - destruct IH as [IH|(iv & Hi & Hr)]; [left; split; [lia | exact IH] | right; exists iv; split; [right; exact Hi | exact Hr]]. }
    destruct OUTW as [OUT|(iv & Hiv & Hr)].
    { apply MU. rewrite wa_unsigned by lia. exact OUT. }
    exfalso. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as Wi.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    assert (SHR : forall y, 0 <= y < 2 ^ 47 -> ASHADOW_BASE <= sh y < AHI_LO) by exact sh_below_ahi.
    destruct Wi as [(S1 & S2)|[Xw|(q & A & N & Hq & QA & QN)]].
    -
      destruct Hc as [Hc|[Hc|[(b & Hb & Hbr)|[(b & Hb & Hbr)|[Hc|[Hc|Hc]]]]]];
        unfold ASHADOW_BASE, AHI_LO, AIMG_TOP, AFS_SIZE in *.
      + lia.
      + unfold aimg_client in Hc. lia.
      + assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
        pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (_ & _ & _ & _ & CC & _). lia.
      + assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
        pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (C0 & _ & Cn & _ & CC & _).
        pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(lia) Cn ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN. lia.
      + lia.
      + assert (AC0 : 0 <= aceil < 2 ^ 47) by lia.
        pose proof (sh_mono (as_FSB H + 0xb09000) aceil FB2) as SM. pose proof (SHR aceil AC0) as S3.
        unfold ASHADOW_BASE, AHI_LO in S3. lia.
      + assert (AC0 : 0 <= aceil < 2 ^ 47) by lia. pose proof (SHR aceil AC0) as S3. unfold ASHADOW_BASE, AHI_LO in S3. unfold AHI_LO in Hc. lia.
    - exact (Hnx (Xw x Hr)).
    -
      assert (INqL : In (q, A, N) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH INqL) as (B0 & B16 & Bn & BI & BC & BF & BA). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      assert (XAPP : x < ALOWSH_LO \/ AHI_LO <= x) by (unfold aapp, aapp_lo, aapp_hi in BA; lia).
      destruct Hc as [Hc|[Hc|[(b & Hb & Hbr)|[(b & Hb & Hbr)|[Hc|[Hc|Hc]]]]]];
        unfold ALOWSH_LO, AHI_LO, ASHADOW_BASE, AFS_SIZE in *; unfold AIMG_TOP in BI, FB1.
      + lia.
      + unfold aimg_client in Hc. lia.
      + assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
        destruct (Z.eq_dec (blk_id b) q) as [Eq|Ne].
        * pose proof (ah_nodup H HH _ _ _ RH) as ND.
          pose proof (Stdlib.Sorting.Permutation.Permutation_NoDup (Permutation_map blk_id PE) ND) as ND'. rewrite map_app in ND'.
          apply (nodup_app_disj _ _ _ q ND').
          -- apply in_map_iff. exists b. split; [exact Eq | exact Hb].
          -- apply in_map_iff. exists (q, A, N). split; [reflexivity | exact Hq].
        * pose proof (ah_disj H HH _ _ _ _ _ RH HbL INqL Ne) as D. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D. lia.
      + assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
        pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (C0 & C16 & Cn & CI & CC & CF & CA).
        pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(lia) Cn ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
        pose proof (SHR (blk_addr b) ltac:(lia)) as S1. unfold ASHADOW_BASE, AHI_LO in S1. lia.
      + unfold AFS_SIZE in Hc. lia.
      + unfold AFS_SIZE in Hc. pose proof (SHR (as_FSB H) ltac:(lia)) as S1.
        pose proof (sh_nsh_high (as_FSB H) 0xb09000 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
        assert (sh (as_FSB H + 0xb09000) <= sh (as_FSB H) + nsh 0xb09000) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        unfold ASHADOW_BASE, AHI_LO in S1. lia.
      + unfold AHI_LO in Hc. assert (AC0 : 0 <= aceil < 2 ^ 47) by (clear - ACF1 ACF2; lia).
        pose proof (SHR aceil AC0) as S1. unfold ASHADOW_BASE, AHI_LO in S1. clear - S1 Hc XAPP Hr QA QN. cbn in Hr. lia.
  Qed.
End XPM.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (#102 pin d663f82d7f48, asan-ubsan; unstripped twin c90d4fa54d43),
   ex_value walk: the DISCHARGE of EXV_HYP's (ExvB_Stmt.v) closed image-fact fields and instance fields at the
   instance of record. Proves nothing about the program (no function walked).
   Instance: B := TfibB of lib/Reusable/YD2l.v (blob 95803a8b9493, the B'-generated record), ARx := ARcf rsegs TfibB at
   CfParams_preset (h-mani-a8's second allocator instance, lib/Reusable/YG0ncf.v), the head length cf_head of
   CfParams_preset (lib/A/CfParamsPreset.v). EXV_HYP at this base takes no CfImg (its implicit arguments are rc, cp and
   RL, the compiler's own list), so none is passed. The run ceiling rc stays a parameter.
   Each lemma exvi_<field> states EXACTLY the field's type at that instance; exvi_fields_typed (end of file) checks
   each one against the projection of EXV_HYP at the instance.
   Every image value is computed from the B' record files (YD2l.v, YF0m.v, PAImg_prog.v of this tree): the closed
   facts close by vm_compute on the closed record (never on a goal with an evar), and each typed numeral below is
   checked against its table by computation.
   Dischargers cited (all on this branch):
   - eh_tp: strtod_row_sat.strtod_sat_tp_B (B/Prog/strtod_row_sat.v:28);
   - eh_errno_B: YF0m.ts_errno of YD2l.TfibB_syms (Reusable/YD2l.v:71);
   - eh_errno_own: strtod_row_sat.strtod_sat_owned_B (B/Prog/strtod_row_sat.v:40);
   - eh_got_const: the GOT-guard cell of Tfib_const_abs (Reusable/YF0m.v:202);
   - eh_errno / eh_palib / eh_head / eh_laws: PALibB.exvi_eh_* (B/PALibB.v, blob 5baa19c890f7), cited, not restated;
  - eh_blk32: ablock_n_lt_max_cf (Reusable/YGcfBlockRange.v), with cf_malloc_max < 2 ^ 32 at CfParams_preset closed by vm_compute (no typed value);
   - eh_blk_amem8: block_amem_range8_cf (Reusable/YGcfBlockRange.v), through ablocks = map (sptr_addr ..) blocks;
   - eh_fpos / eh_frames_cid: frame_facts_cf (Reusable/YG0scf.v:299), conjuncts 2 / 1, on ARcf's ARmcf;
   - eh_frame_hull: ARx_frame_hull_vis_cf_ok (Reusable/YGcfFsVis.v) restricted by shadow_hull_vis_sub_cf
     (Reusable/YGcfHeadSh.v);
   - eh_stk_hull: alx_zshadow of eh_laws on the head range of zero_shadow_ranges (the real stack), and layout_ok's
     lo_top (both stack bounds page-aligned, Reusable/YG0f.v);
   - eh_litsh: alx_const_cells (Tfib_const_shadow's cells 0..11, Reusable/YF0m.v:1076-1087) and alx_zshadow (the first
     range of Tfib_zero_shadow, (IMG_LO_B, 0x20f60 - IMG_LO_B), Reusable/YF0m.v:1784) of eh_laws;
   - eh_ownlow: ARx_owned_low_law_cf_x (Reusable/YGcallcf.v) of AR_laws_ok_cf;
   - eh_smx / eh_sfx: stack_malloc_x_any / stack_free_x_any (Reusable/YGcallScf.v, at any relation);
   - eh_asfx: astack_free_law_ok_cf (Reusable/YG0tcf.v; its statement astack_free_law_cf is the field at ARcf);
   - eh_fflx: put together from AR_flag_law_ok_cf (YG0scf.v:477), AR_client_img_law_ok_cf (YG0scf.v:552, flag arm),
     lo_img (fst (ly_img ly) = kImgLo) and amc_static_img (YG0ncf.v:108) on Tfib_zero_shadow's last range
     (0x5dde20, IMG_TOP_B - 0x5dde20), which puts B''s image top IMG_TOP_B inside ly_img; the field's zone2 is then
     reached from the B' bound by exvi_zone2_B (see the note there);
   - eh_pst_own / eh_uar_cell / eh_lit_own / eh_sm1_pc / eh_got_uar: by computation on the record.
   NOT here (callee texts, not image facts): eh_string, eh_ws, eh_strcmp, eh_strlen, eh_bcmp, eh_memcpy, eh_sm1.
   Numerals (each re-read from the B' tables of this tree):
   0x7fffc1ec-0x7fffc1f7 (ADDRESS: the shadow cells of the three word literals, Tfib_const_shadow indices 0-11,
   YF0m.v:1076-1087, values 5 f9 f9 f9 6 f9 f9 f9 5 f9 f9 f9); 0x7fffc1e8-0x7fffc1eb (ADDRESS: the hull granule below,
   cells 0x21e8-0x21eb of Tfib_zero_shadow's first range, whose shadow starts at 0x7fffa000 = shadow_of_addr IMG_LO_B;
   0x21ec = that range's cell count); 0x41ec / 0x41f0 / 0x41f4 (ADDRESS / 8: the literals' granules); 0x7fffc1f0 /
   0x7fffc1f8 (ADDRESS: hull bounds); 0x20f60 (ADDRESS: end of Tfib_zero_shadow's first range, YF0m.v:1784);
   169 (index of the GOT-guard cell z8 (ANum 0xa34d8) 0x5fe770 in Tfib_const_abs, YF0m.v:202);
   17 and 0x5dde20 (index and start of Tfib_zero_shadow's last range, YF0m.v:1784); 0x10f60 / 0x10f80 / 0x10fa0
   (exvd_lit's offsets, ExvB_Stmt.v:327-329); 5 / 6 / 0xf9 (VALUE: the literal shadow bytes above); 4 (LENGTH: the
   zero-shadow cells under the first hull); 8, 512, 4096 (LENGTH: granule, shadow bytes of a page, page);
  (cf_malloc_max is not typed here: its bound below 2 ^ 32 is vm_computed from CfParams_preset). The uar cell, the GOT / shadow-cell objects and
   B_prog_val (A_OBJ 2) carry no typed numeral here: they are vm_computed from YD2l.v / PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YGcallx YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_row_sat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0scf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfBlockRange YGcfFsVis YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- generic helpers (no address) ---- *)
Definition exvi_disj_b (l1 l2 : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))%bool l2) l1.

Lemma exvi_disj_b_sound : forall l1 l2, exvi_disj_b l1 l2 = true ->
  forall a, Exists (in_zr a) l1 -> ~ Exists (in_zr a) l2.
Proof.
intros l1 l2 H a H1 H2. apply Exists_exists in H1 as (r & Hr & Ar). apply Exists_exists in H2 as (r' & Hr' & Ar').
unfold exvi_disj_b in H. rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
specialize (H r' Hr'). apply Bool.orb_true_iff in H. unfold in_zr in Ar, Ar'.
destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma exvi_div8 : forall y q, 8 * q <= y < 8 * q + 8 -> y / 8 = q.
Proof. intros y q H. symmetry. apply Z.div_unique with (r := y - 8 * q); lia. Qed.

Lemma exvi_mod8 : forall y q, 8 * q <= y < 8 * q + 8 -> y mod 8 = y - 8 * q.
Proof. intros y q H. symmetry. apply Z.mod_unique with (q := q); lia. Qed.

(* a one-byte constant cell's byte, before arithmetic: the callers instantiate a and v by numerals, where
   a + Z.of_nat 0 and le_byte v 1 0 compute *)
Lemma exvi_z1 : forall (B : asyms) ly (rd : reader) a v, cell_holds B ly rd (z1 (ANum a) v) ->
  rd (a + Z.of_nat 0) = Some (le_byte v 1 0).
Proof. intros B ly rd a v H. exact (H 0%nat (Nat.lt_0_succ 0)). Qed.

(* one granule [8 g, 8 g + 8) holds [w, w + len), and its shadow byte v admits the whole range *)
Lemma exvi_ra_of : forall (rd : reader) w len g v, 8 * g <= w -> w + len <= 8 * g + 8 ->
  rd (SHADOW_OFF + g) = Some v -> v = 0 \/ (w + len - 8 * g <= v /\ v < 8) ->
  range_addressable rd SHADOW_OFF w len.
Proof.
intros rd w len g v H1 H2 Hr Hv x Hx. exists v. split.
- unfold shadow_of_addr. rewrite (exvi_div8 x g) by lia. exact Hr.
- unfold saddr_ok. destruct Hv as [->|[Hv1 Hv2]]; [left; reflexivity|].
  right. rewrite (exvi_mod8 x g) by lia. lia.
Qed.

Lemma exvi_hull_of : forall (rd : reader) x n lo hi, shadow_addr x / 8 * 8 = lo ->
  shadow_addr (x + n - 1) / 8 * 8 + 8 = hi -> (forall s, lo <= s < hi -> rd s <> None) -> shadow_hull_vis rd x n.
Proof. intros rd x n lo hi E1 E2 H s Hs. apply H. lia. Qed.

(* the engine's zone2 (YCbq.zone2 = off_img over the engine's own image bounds, YCbq.zone2_A) holds at an address
   outside image B''s bounds [IMG_LO_B, IMG_TOP_B): B''s image top IMG_TOP_B is at or above the engine's, its low
   bound the same. At B' the engine's zone2 is the WEAKER claim (h-rw-pre-1 / ExValueB 2026-10-29: kept as the engine
   states it, the premise of YGcallSx's aj_flag_store_x) *)
Lemma exvi_zone2_B : forall a n, zone2_at YImgTop.IMG_LO_B YImgTop.IMG_TOP_B a n -> zone2 a n.
Proof.
intros a n H. rewrite zone2_A. unfold zone2_at, off_img_at in *.
pose proof YImgTop.IMG_LO_val as L. pose proof YImgTop.IMG_TOP_val as T.
pose proof YImgTop.IMG_LO_B_val as LB. pose proof YImgTop.IMG_TOP_B_val as TB.
lia.
Qed.

Section i. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).

(* ---- closed image facts of B' ---- *)
Lemma exvi_eh_tp : as_tp TB = STRTOD_TP.
Proof. exact strtod_row_sat.strtod_sat_tp_B. Qed.

Lemma exvi_eh_errno_B : as_errno TB = YF0m.TFIB_ERRNO.
Proof. exact (YF0m.ts_errno _ YD2l.TfibB_syms). Qed.

Lemma exvi_eh_errno_own : forall a, as_errno TB <= a < as_errno TB + 4 -> ~ Exists (in_zr a) (as_owned_static TB).
Proof. exact strtod_row_sat.strtod_sat_owned_B. Qed.

Lemma exvi_eh_pst_own : forall a, Exists (in_zr a) prh_pst -> ~ Exists (in_zr a) (as_owned_static TB).
Proof.
assert (D : exvi_disj_b prh_pst (as_owned_static TB) = true) by (vm_compute; reflexivity).
exact (exvi_disj_b_sound _ _ D).
Qed.

(* the uar cell and the three objects, each computed from the record (YD2l.v as_uar_cell, PAImg_prog.v B_prog_obj) *)
Lemma exvi_eh_uar_cell : 4096 <= as_uar_cell TB /\ as_uar_cell TB + 4 <= kLowMemEnd /\
    (as_uar_cell TB + 4 <= B_prog_val (A_OBJ 0) \/ B_prog_val (A_OBJ 0) + 8 <= as_uar_cell TB) /\
    (as_uar_cell TB + 4 <= B_prog_val (A_OBJ 1) \/ B_prog_val (A_OBJ 1) + 8 <= as_uar_cell TB) /\
    (as_uar_cell TB + 4 <= B_prog_val (A_OBJ 12) \/ B_prog_val (A_OBJ 12) + 8 <= as_uar_cell TB).
Proof.
let v := eval vm_compute in (as_uar_cell TB) in assert (U : as_uar_cell TB = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (B_prog_val (A_OBJ 0)) in assert (V0 : B_prog_val (A_OBJ 0) = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (B_prog_val (A_OBJ 1)) in assert (V1 : B_prog_val (A_OBJ 1) = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (B_prog_val (A_OBJ 12)) in
  assert (V12 : B_prog_val (A_OBJ 12) = v) by (vm_compute; reflexivity).
rewrite U, V0, V1, V12. unfold kLowMemEnd. lia.
Qed.

Lemma exvi_eh_got_const : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const TB ly).
Proof.
intros ly. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. left.
apply (nth_error_In YF0m.Tfib_const_abs 169). vm_compute. reflexivity.
Qed.

(* each literal's bytes and NUL, [w, w + length wl], lie outside the owned statics: computed over exvd_lit's own ranges *)
Lemma exvi_eh_lit_own : forall c w ty wl u, exvd_lit c w ty wl u ->
    forall a, w <= a <= w + Z.of_nat (length wl) -> ~ Exists (in_zr a) (as_owned_static TB).
Proof.
intros c w ty wl u HL a Ha. apply (exvi_disj_b_sound [(w, Z.of_nat (length wl) + 1)] (as_owned_static TB)).
- destruct HL as [(-> & -> & -> & -> & ->) | [(-> & -> & -> & -> & ->) | (-> & -> & -> & -> & ->)]];
  vm_compute; reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma exvi_eh_sm1_pc : B_prog_sigma AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TB) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma exvi_eh_got_uar : as_got_uar TB = B_prog_val (A_OBJ 1).
Proof. vm_compute. reflexivity. Qed.

(* PALibB.exvi_eh_errno, PALibB.exvi_eh_palib, PALibB.exvi_eh_head, PALibB.exvi_eh_laws: their one home is
   lib/B/PALibB.v (blob 5baa19c890f7, one text for every pin), cited below as PALibB.exvi_eh_* *)

(* ---- instance fields: state facts at ARcf ---- *)
Lemma exvi_eh_blk32 : forall ly S Hp W mem md p n, ARI ly S Hp W mem md -> In (p, n) (ablocks TB ly S) -> n < 2 ^ 32.
Proof.
intros ly S Hp W mem md p n HA Hin.
destruct (YGcfBlockRange.ablock_n_lt_max_cf rsegs TB ly S Hp W mem md p n HA Hin) as [_ Hn].
assert (Hmax : @cf_malloc_max CP < 2 ^ 32) by (vm_compute; reflexivity). lia.
Qed.

Lemma exvi_eh_blk_amem8 : forall ly S Hp W mem md p n k, ARI ly S Hp W mem md -> In (p, n) (ablocks TB ly S) ->
    0 <= k <= n -> YGcallMx.amem_range8 p (k + 1).
Proof.
intros ly S Hp W mem md p n k HA Hin Hk. unfold ablocks in Hin.
apply in_map_iff in Hin as ([p0 n0] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
exact (YGcfBlockRange.block_amem_range8_cf rsegs TB ly S Hp W mem md p0 n0 k HA Hin Hk).
Qed.

Lemma exvi_eh_fpos : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    0 <= pos < fs_frames cid.
Proof.
intros ly S Hp W mem md cid pos HA Hin.
exact (proj1 (proj2 (YG0scf.frame_facts_cf TB ly S Hp _ cid pos (proj1 HA) Hin))).
Qed.

Lemma exvi_eh_frames_cid : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    0 <= cid <= 10.
Proof.
intros ly S Hp W mem md cid pos HA Hin.
exact (proj1 (YG0scf.frame_facts_cf TB ly S Hp _ cid pos (proj1 HA) Hin)).
Qed.

Lemma exvi_eh_frame_hull : forall ly S Hp W mem md cid pos x n, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    frame_addr ly cid pos <= x -> x + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
    shadow_hull_vis (aview rsegs (w_H W) mem) x n.
Proof.
intros ly S Hp W mem md cid pos x n HA Hin H1 H2 _.
apply (YGcfHeadSh.shadow_hull_vis_sub_cf _ (frame_addr ly cid pos) (fs_frame_bytes cid)); [|exact H1|exact H2].
exact (YGcfFsVis.ARx_frame_hull_vis_cf_ok rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)
  ly S Hp W mem md cid pos HA Hin).
Qed.

Lemma exvi_eh_stk_hull : forall ly S Hp W mem md x n, ARI ly S Hp W mem md ->
    ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> shadow_hull_vis (aview rsegs (w_H W) mem) x n.
Proof.
intros ly S Hp W mem md x n HA H1 H2.
pose proof (alx_zshadow _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HA
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow in HZ.
destruct (lo_top _ (YG0ncf.amc_layout _ _ _ _ _ (proj1 HA))) as (_ & _ & _ & _ & PL & PH & _).
unfold page_aligned in PL, PH.
apply Z.mod_divide in PL as [a Ha]; [|lia]. apply Z.mod_divide in PH as [b Hb]; [|lia].
unfold shadow_hull_vis. intros s Hs.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by ring.
rewrite HZ; [discriminate|].
assert (E1 : ly_stk_lo ly / 8 = a * 512).
{ rewrite Ha. replace (a * 4096) with (a * 512 * 8) by ring. apply Z.div_mul. lia. }
assert (E2 : (ly_stk_hi ly - ly_stk_lo ly) / 8 = (b - a) * 512).
{ rewrite Ha, Hb. replace (b * 4096 - a * 4096) with ((b - a) * 512 * 8) by ring. apply Z.div_mul. lia. }
unfold shadow_of_addr. rewrite E1, E2. unfold shadow_addr in Hs.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold SHADOW_OFF in *. lia.
Qed.

(* the three word literals' shadow at B' (.str / .str.1 / .str.2 at 0x20f60 / 0x20f80 / 0x20fa0): their shadow bytes
   0x7fffc1ec..0x7fffc1f7 are const cells Tfib_const_shadow 0..11; the first hull's lower granule 0x7fffc1e8..0x7fffc1eb
   is the tail of Tfib_zero_shadow's first range (IMG_LO_B, 0x20f60 - IMG_LO_B) *)
Lemma exvi_eh_litsh : forall ly S Hp W mem md, ARI ly S Hp W mem md -> forall c w ty wl u, exvd_lit c w ty wl u ->
    range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF w (Z.of_nat (length wl) + 1) /\
    shadow_hull_vis (aview rsegs (w_H W) mem) w (Z.of_nat (length wl) + 1).
Proof.
intros ly S Hp W mem md HA c w ty wl u HL.
pose proof (alx_const_cells _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md HA) as HC.
pose proof (alx_zshadow _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md (YImgTop.IMG_LO_B, 0x20f60 - YImgTop.IMG_LO_B) HA
  (or_intror (or_introl eq_refl))) as HZ.
set (rd := aview rsegs (w_H W) mem) in *.
cbn [fst snd] in HZ. unfold zero_shadow in HZ.
assert (CELL : forall k a v, nth_error YF0m.Tfib_const_shadow k = Some (z1 (ANum a) v) ->
  rd (a + Z.of_nat 0) = Some (le_byte v 1 0)).
{ intros k a v Hk. apply (exvi_z1 TB ly). apply (proj1 (Forall_forall _ _) HC).
  change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact (nth_error_In _ k Hk). }
assert (R0 : rd 0x7fffc1ec = Some 5) by exact (CELL 0%nat 0x7fffc1ec 5 eq_refl).
assert (R1 : rd 0x7fffc1ed = Some 0xf9) by exact (CELL 1%nat 0x7fffc1ed 0xf9 eq_refl).
assert (R2 : rd 0x7fffc1ee = Some 0xf9) by exact (CELL 2%nat 0x7fffc1ee 0xf9 eq_refl).
assert (R3 : rd 0x7fffc1ef = Some 0xf9) by exact (CELL 3%nat 0x7fffc1ef 0xf9 eq_refl).
assert (R4 : rd 0x7fffc1f0 = Some 6) by exact (CELL 4%nat 0x7fffc1f0 6 eq_refl).
assert (R5 : rd 0x7fffc1f1 = Some 0xf9) by exact (CELL 5%nat 0x7fffc1f1 0xf9 eq_refl).
assert (R6 : rd 0x7fffc1f2 = Some 0xf9) by exact (CELL 6%nat 0x7fffc1f2 0xf9 eq_refl).
assert (R7 : rd 0x7fffc1f3 = Some 0xf9) by exact (CELL 7%nat 0x7fffc1f3 0xf9 eq_refl).
assert (R8 : rd 0x7fffc1f4 = Some 5) by exact (CELL 8%nat 0x7fffc1f4 5 eq_refl).
assert (R9 : rd 0x7fffc1f5 = Some 0xf9) by exact (CELL 9%nat 0x7fffc1f5 0xf9 eq_refl).
assert (R10 : rd 0x7fffc1f6 = Some 0xf9) by exact (CELL 10%nat 0x7fffc1f6 0xf9 eq_refl).
assert (R11 : rd 0x7fffc1f7 = Some 0xf9) by exact (CELL 11%nat 0x7fffc1f7 0xf9 eq_refl).
assert (Z4 : forall i, 0 <= i < 4 -> rd (0x7fffc1e8 + i) = Some 0).
{ intros i Hi.
  assert (E0 : shadow_of_addr SHADOW_OFF YImgTop.IMG_LO_B = 0x7fffa000) by (vm_compute; reflexivity).
  assert (E1 : (0x20f60 - YImgTop.IMG_LO_B) / 8 = 0x21ec) by (vm_compute; reflexivity).
  replace (0x7fffc1e8 + i) with (shadow_of_addr SHADOW_OFF YImgTop.IMG_LO_B + (0x21e8 + i)) by (rewrite E0; ring).
  apply HZ. rewrite E1. lia. }
assert (ALL : forall s, 0x7fffc1e8 <= s < 0x7fffc1f8 -> rd s <> None).
{ intros s Hs. destruct (Z_lt_dec s 0x7fffc1ec) as [D|D].
  - replace s with (0x7fffc1e8 + (s - 0x7fffc1e8)) by ring. rewrite Z4 by lia. discriminate.
  - assert (E : s = 0x7fffc1ec \/ s = 0x7fffc1ed \/ s = 0x7fffc1ee \/ s = 0x7fffc1ef \/ s = 0x7fffc1f0 \/
      s = 0x7fffc1f1 \/ s = 0x7fffc1f2 \/ s = 0x7fffc1f3 \/ s = 0x7fffc1f4 \/ s = 0x7fffc1f5 \/ s = 0x7fffc1f6 \/
      s = 0x7fffc1f7) by lia.
    repeat (destruct E as [E|E]; [subst s; congruence|]). subst s. congruence. }
let v := eval vm_compute in (B_prog_val (A_OBJ 2)) in assert (V2 : B_prog_val (A_OBJ 2) = v) by (vm_compute; reflexivity).
destruct HL as [(-> & -> & -> & -> & ->) | [(-> & -> & -> & -> & ->) | (-> & -> & -> & -> & ->)]]; rewrite V2.
- change (Z.of_nat (length PjGrammar.w_true) + 1) with 5. split.
  + apply (exvi_ra_of rd _ _ 0x41ec 5); [lia | lia | exact R0 | right; lia].
  + apply (exvi_hull_of rd _ _ 0x7fffc1e8 0x7fffc1f0); [vm_compute; reflexivity | vm_compute; reflexivity |].
    intros s Hs. apply ALL. lia.
- change (Z.of_nat (length PjGrammar.w_false) + 1) with 6. split.
  + apply (exvi_ra_of rd _ _ 0x41f0 6); [lia | lia | exact R4 | right; lia].
  + apply (exvi_hull_of rd _ _ 0x7fffc1f0 0x7fffc1f8); [vm_compute; reflexivity | vm_compute; reflexivity |].
    intros s Hs. apply ALL. lia.
- change (Z.of_nat (length PjGrammar.w_null) + 1) with 5. split.
  + apply (exvi_ra_of rd _ _ 0x41f4 5); [lia | lia | exact R8 | right; lia].
  + apply (exvi_hull_of rd _ _ 0x7fffc1f0 0x7fffc1f8); [vm_compute; reflexivity | vm_compute; reflexivity |].
    intros s Hs. apply ALL. lia.
Qed.

(* ---- the frame laws (YGcallSx.v's SMX, ASFX, FFLX, SFX) and the owned-low law at ARcf ---- *)
Lemma exvi_eh_ownlow : YGcallx.ARx_owned_low_law rsegs TB ARI.
Proof. exact (YGcallcf.ARx_owned_low_law_cf_x (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)). Qed.

Lemma exvi_eh_smx : forall ly S Hp W mem md cid, ARI ly S Hp W mem md -> 0 <= cid <= 10 ->
    count_cid cid (frames S) < fs_frames cid ->
    exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
      frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof.
intros ly S Hp W mem md cid HA Hc Hcnt.
exact (YGcallScf.stack_malloc_x_any rsegs ARI ly S Hp W mem md cid HA Hc Hcnt).
Qed.

Lemma exvi_eh_asfx : forall ly S Hp W mem md mem' md' cid pos,
    ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aview rsegs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aowned TB ly S a -> a <> flag_addr ly cid pos ->
       aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
    (forall a, aview rsegs (w_H W) mem a <> None -> aview rsegs (w_H W) mem' a <> None) ->
    m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
    (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
    ARI ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YG0tcf.astack_free_law_ok_cf (cp := CP) rsegs TB). Qed.

(* the flag cell is outside ly_img, which at B' reaches IMG_TOP_B (Tfib_zero_shadow's last range ends there), so the
   flag is below kImgLo or at or above IMG_TOP_B. The field's zone2 is the ENGINE's predicate (YCbq.zone2 = off_img
   over the engine's IMG_LO / IMG_TOP, the premise of YGcallSx's aj_flag_store_x): it is reached from the B' bound by
   exvi_zone2_B (YCbq.zone2_A with YImgTop's generated IMG_TOP_val / IMG_TOP_B_val), a weaker claim at B' *)
Lemma exvi_eh_fflx : forall ly S Hp (W : world rsegs) mem md cid pos,
    ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned TB ly S (flag_addr ly cid pos) /\
    (app_addr (flag_addr ly cid pos) /\ ~ in_img rsegs (flag_addr ly cid pos)) /\
    (4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling).
Proof.
intros ly S Hp W mem md cid pos HA Hin.
destruct (YG0scf.AR_flag_law_ok_cf (cp := CP) rsegs TB ly S Hp W mem md cid pos HA Hin) as (PR & OW & IA & LT).
destruct (YG0scf.AR_client_img_law_ok_cf (cp := CP) rsegs TB ly S Hp W mem md (flag_addr ly cid pos) HA
  (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl)))))) as [NZ NI].
pose proof (lo_img _ (YG0ncf.amc_layout _ _ _ _ _ (proj1 HA))) as (I0 & _ & _ & _).
assert (HL : In (0x5dde20, YImgTop.IMG_TOP_B - 0x5dde20) (as_owned_static TB ++ as_zero_shadow TB)).
{ apply in_or_app. right. apply (nth_error_In _ 17). vm_compute. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (YG0ncf.amc_static_img _ _ _ _ _ (proj1 HA)) _ HL) as [S1 S2].
cbn [fst snd] in S1, S2.
split; [exact PR|]. split; [exact OW|].
split; [split; [exact (in_app_addr (flag_addr ly cid pos) 1 (flag_addr ly cid pos) IA ltac:(lia)) | exact NI]|].
unfold in_app in IA. split; [lia|]. split; [|exact LT].
apply exvi_zone2_B. unfold zone2_at, off_img_at. unfold in_zr in NZ. unfold kImgLo in I0.
unfold kLowShadowBeg, kHighMemBeg in IA.
pose proof YImgTop.IMG_LO_B_val as LB. pose proof YImgTop.IMG_TOP_B_val as TB'. lia.
Qed.

Lemma exvi_eh_sfx : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
    exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof.
intros ly S Hp W mem md cid pos HA Hin.
exact (YGcallScf.stack_free_x_any rsegs ARI ly S Hp W mem md cid pos HA Hin).
Qed.

End i.

(* ---- each lemma's statement is its field's type at the instance (checked by conversion against the projection) ---- *)
Ltac exvi_same P L := let T := type of P in let c := constr:(L : T) in idtac.

Section chk. Context {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
Lemma exvi_fields_typed :
  EXV_HYP (rc := rc) (cp := CfParamsPreset.CfParams_preset) (RL := RL) YD2l.TfibB
    (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB) SK -> True.
Proof.
intros H.
exvi_same (eh_tp _ _ _ H) exvi_eh_tp.
exvi_same (eh_errno_B _ _ _ H) exvi_eh_errno_B.
exvi_same (eh_got_const _ _ _ H) exvi_eh_got_const.
exvi_same (eh_errno_own _ _ _ H) exvi_eh_errno_own.
exvi_same (eh_blk32 _ _ _ H) exvi_eh_blk32.
exvi_same (eh_blk_amem8 _ _ _ H) exvi_eh_blk_amem8.
exvi_same (eh_litsh _ _ _ H) exvi_eh_litsh.
exvi_same (eh_pst_own _ _ _ H) exvi_eh_pst_own.
exvi_same (eh_head _ _ _ H) PALibB.exvi_eh_head.
exvi_same (eh_uar_cell _ _ _ H) exvi_eh_uar_cell.
exvi_same (eh_stk_hull _ _ _ H) exvi_eh_stk_hull.
exvi_same (eh_frame_hull _ _ _ H) exvi_eh_frame_hull.
exvi_same (eh_fpos _ _ _ H) exvi_eh_fpos.
exvi_same (eh_frames_cid _ _ _ H) exvi_eh_frames_cid.
exvi_same (eh_lit_own _ _ _ H) exvi_eh_lit_own.
exvi_same (eh_sm1_pc _ _ _ H) exvi_eh_sm1_pc.
exvi_same (eh_laws _ _ _ H) PALibB.exvi_eh_laws.
exvi_same (eh_errno _ _ _ H) PALibB.exvi_eh_errno.
exvi_same (eh_ownlow _ _ _ H) exvi_eh_ownlow.
exvi_same (eh_smx _ _ _ H) exvi_eh_smx.
exvi_same (eh_asfx _ _ _ H) exvi_eh_asfx.
exvi_same (eh_fflx _ _ _ H) exvi_eh_fflx.
exvi_same (eh_sfx _ _ _ H) exvi_eh_sfx.
exvi_same (eh_palib _ _ _ H) PALibB.exvi_eh_palib.
exvi_same (eh_got_uar _ _ _ H) exvi_eh_got_uar.
exact I.
Qed.
End chk.

Print Assumptions exvi_zone2_B.
Print Assumptions exvi_eh_tp.
Print Assumptions exvi_eh_errno_B.
Print Assumptions exvi_eh_got_const.
Print Assumptions exvi_eh_errno_own.
Print Assumptions exvi_eh_pst_own.
Print Assumptions exvi_eh_uar_cell.
Print Assumptions exvi_eh_lit_own.
Print Assumptions exvi_eh_sm1_pc.
Print Assumptions exvi_eh_got_uar.
Print Assumptions PALibB.exvi_eh_errno.
Print Assumptions PALibB.exvi_eh_palib.
Print Assumptions PALibB.exvi_eh_head.
Print Assumptions PALibB.exvi_eh_laws.
Print Assumptions exvi_eh_blk32.
Print Assumptions exvi_eh_blk_amem8.
Print Assumptions exvi_eh_fpos.
Print Assumptions exvi_eh_frames_cid.
Print Assumptions exvi_eh_frame_hull.
Print Assumptions exvi_eh_stk_hull.
Print Assumptions exvi_eh_litsh.
Print Assumptions exvi_eh_ownlow.
Print Assumptions exvi_eh_smx.
Print Assumptions exvi_eh_asfx.
Print Assumptions exvi_eh_fflx.
Print Assumptions exvi_eh_sfx.
Print Assumptions exvi_fields_typed.

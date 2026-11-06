(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the `Ltac ... ::=` overrides made #[local], the DELTA of commit 432757103df6 (a Theorem Labs lane's fix) applied 3-way; no other text of that commit taken. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG0ncf.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG0ncf.v at commit 5034424e29db (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t + pf_cells_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the RELATIONAL LAYER.
   ARmcf / ARcf are FRESH records, never a wrapper around cgif's ARm / AR: a wrapper would inherit am_wf : Wf,
   which is false for both units (preset's class 17 maps 3,584 MiB against cgif's 2 GiB bound).
   Three things change and nothing else does:
     1. am_wf    -> am_wf_cf : Wf_cf                              (the event-free invariant)
     2. am_cells -> over acells_cf: cgif pins the per-class exhausted byte RI+68 to 0 (YG0n.v:38), which the
        class-full arm sets, so that cell leaves the pinned set; ARmcf's amc_exh_cell pins it to exh_mem_cf at the
        state instead (field round 2), and it is NOT junk.
     3. am_shadow -> shadow_ok_cf over the ghost set Hp: a harness that hides a block's head breaks cgif's
        shadow_ok, which demands shadow 0 over every live block's user bytes.
   plus TWO added fields: am_hp_live, without which a stale base in Hp makes malloc_cf's own post unprovable, and
   amc_xs_placed (2026-10-29), the errbuf slot's placement, which a call premise must give (xs_placed_of_ARcf).
   The frame-area fields (fs_cells, fs_flags_ok), am_areas, am_const, am_layout and am_tsd are VERBATIM.
   cgif's YG0n.v is NOT edited. No address: every numeral is a cgif content constant. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YGcfImgRows.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The allocator instance object __asan::instance (_ZN6__asanL8instanceE): its .symtab size, 3632 at all five images
   (reply A / B, preset A / AU: the pinned unstripped ELFs; cgif: the asan twin's recovered symbol table), read by
   the measurement script, the internal file inst_apart.py (output, the internal file inst_apart.out). The extent YG0f.asyms_areas and the row
   YGcfImgRows.ERRB_QAPART state as (as_inst B, 3632). *)
Definition kInstObjSize : Z := 3632.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section Y.
Variable B : asyms.
Variable ly : alayout.
Local Notation "e +! d" := (aoff e d) (at level 50, left associativity).

(* ---------------------------------------------------------------------------- *)
(* 1. The cells. cgif's region_cells (YG0n.v:34-38) ends with `z1 (R +! 68) 0`,   *)
(*    which pins the exhausted byte to 0. The arm sets that byte, so the cf       *)
(*    version drops the cell; the byte is pinned by ARmcf's amc_exh_cell to       *)
(*    exh_mem_cf at the state (field round 2, Main 2026-10-30, after a Theorem Labs lane's    *)
(*    review), so it is NOT in the junk: region_junk (YG0n.v:39-40) skips offset  *)
(*    68, listing (R+!64,4), (R+!69,3) and (R+!72,56), and the cf junk is cgif's. *)
Definition region_cells_cf (S : astate) (c : Z) : list acell := removelast (region_cells S c).
Definition region_junk_cf (c : Z) : list (aexp * Z) := region_junk c.

Lemma region_cells_cf_incl : forall S c, incl (region_cells_cf S c) (region_cells S c).
Proof.
intros S c. unfold region_cells_cf, region_cells. cbn [removelast].
intros x Hx. cbn in Hx |- *. tauto.
Qed.

Definition acells_cf (S : astate) : list acell :=
flat_map (region_cells_cf S) (zseq 1 31) ++ flat_map (cache_cells S) (zseq 1 31)
++ flat_map chunk_cells (st_chunks S) ++ sec_cells S ++ quar_cells S ++ fs_cells S ++ depot_cells ly S
++ ialloc_cells B S ++ thread_cells.

Definition ajunk_cf (S : astate) : list (aexp * Z) :=
(ASp kRegionInfoOff, 128) :: (ASp (kRegionInfoOff + 128 * 32), 0) ::
flat_map region_junk_cf (zseq 1 31) ++ flat_map (cache_junk S) (zseq 1 31)
++ flat_map chunk_junk (st_chunks S) ++ sec_junk S ++ quar_junk S ++ thread_junk
++ [(ANum (as_oom_byte B), 1); (ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8)]
++ as_junk B ly.

Lemma flat_map_incl {X Y : Type} : forall (f g : X -> list Y) l,
(forall c, incl (f c) (g c)) -> incl (flat_map f l) (flat_map g l).
Proof.
intros f g l H x Hx. apply in_flat_map in Hx as (c & Hc & Hin).
apply in_flat_map. exists c. split; [exact Hc | apply H, Hin].
Qed.

Lemma acells_cf_incl : forall S, incl (acells_cf S) (acells B ly S).
Proof.
intros S. unfold acells_cf, acells.
apply incl_app; [apply incl_appl; apply flat_map_incl; apply region_cells_cf_incl
| apply incl_appr, incl_refl].
Qed.

(* The cf junk IS cgif's (region_junk_cf = region_junk): both inclusions are the identity. *)
Lemma ajunk_incl_cf : forall S, incl (ajunk B ly S) (ajunk_cf S).
Proof. intros S x Hx. exact Hx. Qed.

(* The errbuf extent and its placement, here before the record because ARmcf's last field states the placement.
   The live error-message-buffer extent: the CURRENT capacity entry of st_secs, at its
   own ly_sec slot (the last entry tagged ERRB_CAP_TAG, matching errb_e in YG00cf.v), with
   length errb_cap_cf S. 0 or 1 entries. It is the one mapped extent the ledger covers
   besides lazy_zones and sec_extents (the errbuf map, errb_map_cf, is a KMmapSec with no
   chunk), i.e. c-asan's placement xs (SecGrantP.v:114 at 820536849e5). Its length is
   at most cf_nob by Wf_cf's wsc_lens, since it is an st_secs entry's sm_len. *)
Fixpoint last_cap_idx (l : list secmap) (i : nat) (acc : option nat) : option nat :=
match l with
| [] => acc
| sm :: t => last_cap_idx t (S i) (if is_errb_cap sm then Some i else acc)
end.
Definition xs_cf (S : astate) : list (Z * Z) :=
match last_cap_idx (st_secs S) 0 None with
| Some i => [(ly_sec ly i, errb_cap_cf S)]
| None => []
end.
Lemma xs_cf_length : forall S, (length (xs_cf S) <= 1)%nat.
Proof. intros S. unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None); cbn; lia. Qed.
Definition errb_zone (S : astate) : list (Z * Z) := xs_cf S.

(* The errbuf slot is placed like a live secondary: page-aligned, in the application range,
   below the ceiling, and disjoint from every secondary extent, the static extents and the
   layout's extra extents. It is ARmcf's last field amc_xs_placed (xs_placed_of_ARcf projects it);
   malloc_leaf_cf's post also states it, proved by the Allocate walk from the granted
   KMmapSec answer on a remap. page_aligned a is a mod 4096 = 0 (YG0f.v:293), i.e.
   fst e mod kPage = 0. Lemmas in YGcfXs.v. *)
Definition xs_placed_cf (S : astate) : Prop :=
Forall (fun e => page_aligned (fst e) /\ in_app (fst e) (snd e) /\ fst e + snd e <= alloc_ceiling /\
Forall (zdisjoint e) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)) (xs_cf S).

(* The two machine-cell facts (Main 02:4xZ; text agreed with a Theorem Labs lane; moved here from YGcfInstBase.v,
   field round 2, Main 2026-10-30): the per-class exhausted byte and the error-message buffer's object. Both write
   sets are already inside AOX_cf = aowned \/ xs_cf: the buffer [data, data + cap) IS xs_cf ly S (section 1), the
   object cells are in aowned through as_owned_static (the per-unit image row errb_obj_owned_t, YGcfInstBase.v), and
   the exhausted byte is in the RegionInfo slot of the primary reserve (owned; pinned by amc_exh_cell, not junk).
   errb_cells_cf's last two conjuncts are the buffer's
   model shape (Main 02:5xZ): size <= cap and cap a whole number of pages. *)
Definition errb_data_cf (S : astate) : Z :=
match last_cap_idx (st_secs S) 0 None with Some i => ly_sec ly i | None => 0 end.

Definition errb_cells_cf (S : astate) (rd : reader) : Prop :=
let O := cf_errbuf_obj in
cell_holds B ly rd (z8 (ANum O) (if errb_mapped_cf S then O + 32 else 0)) /\
cell_holds B ly rd (z8 (ANum (O + 16)) 0) /\
cell_holds B ly rd (z8 (ANum (O + 32)) (errb_data_cf S)) /\
cell_holds B ly rd (z8 (ANum (O + 40)) (errb_cap_cf S)) /\
cell_holds B ly rd (z8 (ANum (O + 48)) (errb_size_cf S)) /\
(forall a, errb_data_cf S <= a < errb_data_cf S + errb_cap_cf S -> rd a <> None) /\
errb_size_cf S <= errb_cap_cf S /\ errb_cap_cf S mod kPage = 0.

Definition exh_cell_cf (S : astate) (rd : reader) : Prop :=
(forall c, 1 <= c <= 31 ->
  cell_holds B ly rd (z1 (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) (if exh_mem_cf S c then 1 else 0))) /\
exh_mem_cf S kBatchClass = false.

(* The per-unit image row the errbuf object's ownership needs (moved here from YGcfInstBase.v, field round 2). *)
Definition errb_obj_owned_t : Prop :=
forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> Exists (in_zr a) (as_owned_static B).

(* The per-unit image row that keeps the errbuf object out of the internal allocator's arena and its flag (field
   round 3, Main 2026-10-30): the third conjunct of amc_cells_owned. Measured at the five images (cgif, reply A / B,
   preset A / AU): every errbuf object lies below as_ialloc_lo. *)
Definition errb_ial_apart_t : Prop :=
forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).

(* Field round 3 (Main 2026-10-30): Printf's two writable image cells, the tool-name pointer and the Printf callback
   cell, at the values start-up leaves in them (CfImg's cf_toolname_cell / cf_toolname_val, cf_pfcb_cell /
   cf_pfcb_val). No walk writes them (Round3Measure2, 13 refs), so every relation builder keeps them by frame. The
   silent GOT word ReportFile::Write tests is NOT a row: it stays an image fact of the report walk, with VSNPrintf's
   read-only bytes (Main's decision (b), 2026-10-30). *)
Definition pf_cells_cf (rd : reader) : Prop :=
cell_holds B ly rd (z8 (ANum cf_toolname_cell) cf_toolname_val) /\
cell_holds B ly rd (z8 (ANum cf_pfcb_cell) cf_pfcb_val).

(* The per-unit image row the two cells need (field round 3), like errb_obj_owned_t: their 16 bytes are in the owned
   static data, and apart from the allocator's instance object [as_inst B, + kInstObjSize) (ERRB_QAPART's twin, so
   that the drain walks, whose writes touch that object's quarantine words, keep them; measured apart at all five
   images by the measurement script, the internal file inst_apart.py: instance cgif 0xa2c18, reply A 0xa2a58 / B 0xa2fd8, preset
   A 0xa7858 / AU 0xa8098, each below every pfcb cell and above every toolname cell). *)
Definition pf_cells_static_t : Prop :=
forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
Exists (in_zr a) (as_owned_static B) /\ ~ (as_inst B <= a < as_inst B + kInstObjSize).

(* The per-unit image row that keeps the two cells out of the internal allocator's arena and its flag (field round 3,
   Main 2026-10-30, row by a Theorem Labs lane): the twin of errb_ial_apart_t, and the third conjunct of the unit row
   pf_cells_owned_t (after the static and instance-object parts above). Why: ARmcf's rebuild at a reader that equals
   the old one only outside DI (the IAL range [as_ialloc_lo B, as_ialloc_hi B) and the 4-byte flag; DI is owned
   static data, so pf_cells_static_t alone does not keep the cells out of it) must keep the cells, as it keeps the
   errbuf object. Measured at the five images (cgif, reply A / B, preset A / AU, from the pinned ELFs' .symtab):
   every toolname cell lies below as_ialloc_lo, every pfcb cell above as_ialloc_hi and the flag's 4 bytes. *)
Definition pf_ial_apart_t : Prop := forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) -> ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).

(* The per-unit image row that keeps the two cells apart from the depot's static zone, the oom byte and the errbuf
   object (field round 3, Main's decision 2026-10-30, follow-up 2). The cells lie below the image's static depot zone:
   at every unit the static lo of DZONE (the walks' depot zone, dg_dzone) is TFIB_STORE = as_store B. They are not the
   oom byte as_oom_byte B. And they are apart from the errbuf object [cf_errbuf_obj, + 56): `a < as_store B` does NOT
   exclude that object, because it also lies below as_store B at every unit, and the report walk's Append writes it
   (the vector pointer, the Mutex at + 0x10, the placeholder data / cap / size at + 0x20). No other row separates the
   cells from it, so the third conjunct exists. It is NOT an ARmcf field, and pf_cells_owned_t does not carry it.
   Why: the walks' PF_APART / PF_SEP / PF_AG premises are each proved FROM it at the instance where the zone is a
   concrete Definition (short lemmas, 6-12 lines: the izone half also uses pf_ial_apart_t, and DZONE's
   layout-relative NB / SB blocks use the owned-static row with img_cover / lo_disj, since those blocks are off the
   image (DGgm.LYB) and the cells are image bytes). The errbuf conjunct is for the report walk. Measured at the five
   images (cgif, reply A / B, preset A / AU,
   from each unit's TfibSyms rows and CfImg): every pfcb cell + 8 is below TFIB_STORE, and every oom byte and every
   errbuf object lies above the toolname cell and below the pfcb cell. *)
Definition pf_cells_apart_t : Prop := forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) -> a < as_store B /\ a <> as_oom_byte B /\ ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).

(* The unit row ARmcf carries for the two cells (amc_pf_owned): the static row and the IAL row, as amc_cells_owned
   carries errb_obj_owned_t and errb_ial_apart_t. A user that needs a cell byte's ownership projects proj1. *)
Definition pf_cells_owned_t : Prop := pf_cells_static_t /\ pf_ial_apart_t.

(* ---------------------------------------------------------------------------- *)
(* 2. The record. Nineteen fields of cgif's ARm (YG0n.v:205-225) verbatim, three  *)
(*    changed, seven added (amc_hp_live, amc_xs_placed, amc_exh_cell,             *)
(*    amc_errb_cells, amc_cells_owned, amc_pf_cells, amc_pf_owned): 26 fields.    *)
Record ARmcf (S : astate) (Hp : list Z) (rd : reader) : Prop := {
amc_wf : Wf_cf (as_universe B) S;
amc_universe : universe_ok (as_universe B);
amc_syms : asyms_ok B;
amc_layout : layout_ok ly;
amc_placed : sec_placed ly S;
amc_const : Forall (cell_holds B ly rd) (as_const B ly);
amc_const_owned : Forall (cell_owned B ly) (as_const B ly);
amc_cells : Forall (cell_holds B ly rd) (acells_cf S);
amc_fa : fa_entries_ok ly rd S;
amc_flags : fs_flags_ok ly rd S;
amc_depot : depot_ok B ly rd S;
amc_shadow : shadow_ok_cf B ly Hp rd S;
amc_zshadow : zshadow_ok B ly rd;
amc_junk : Forall (range_vis B ly rd) (ajunk_cf S);
amc_areas : Forall (range_vis B ly rd) (aareas S);
amc_client : Forall (range_vis B ly rd) (aclient S);
amc_zero : Forall (range_zero B ly rd) (ialloc_zero B);
amc_tsd : ly_tsd ly = as_tsd B;
amc_static_img : Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B);
(* THE ADDED FIELD. Every hidden base is the user base of a LIVE block whose size is at
   least cf_head. Without it a base left in Hp after a free would survive, and when the
   allocator handed the same address out again malloc_cf's post would be unprovable: the
   head is 0 there and the clause would demand 0xf7. With it, "the new block is not in
   Hp" is derived, never assumed. *)
amc_hp_live : Forall (fun p => exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\
p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k) Hp;
(* The errbuf slot's placement (xs_placed_cf above). The walks carry it between calls and every allocator call
   keeps it (malloc_leaf_cf's xs_placed_cf conjunct, YG0dcf.v), so it is an invariant of the relation: a call
   premise derives it (xs_placed_of_ARcf) and no walk states it beside ARcf (Main, 2026-10-29). *)
amc_xs_placed : xs_placed_cf S;
(* ADDED (field round 2, Main 2026-10-30): the two machine cells, formerly ARX_cf's conjuncts. Every relation
   builder keeps them by exh_cell_cf_frame / errb_cells_cf_frame (YGcfInstBase.v); the walks that change the exhausted
   bits or the errbuf (errb_append / errb_map / errb_retire / errb_set_size / set_exh / clear_exh) re-establish them. *)
amc_exh_cell : exh_cell_cf S rd;
amc_errb_cells : errb_cells_cf S rd;
(* ADDED (field round 2, Main 2026-10-30): the two unit image rows the cells' ownership needs, by their ONE names
   (YGcfImgRows.EXH_OFF_t; errb_obj_owned_t above). STATE-INDEPENDENT: a builder that starts from an old ARmcf carries
   it (try assumption); only the fresh builders (the conversion, YGcfNil.v / YGcfNilInit.v) take it from the unit's
   rows. It is a field, not a premise of the laws, so that the four laws that rebuild ARmcf over a changed reader
   (YG0qcf.AR_frame_law_ok_cf; YG0tcf.v astack_free_law_ok_cf, astack_malloc_law_ok_cf, AR_head_frame_law_ok_cf) project
   it to own the cells' bytes, and AR_laws_ok_cf and its callers keep their statements. Field round 3 adds the third
   row errb_ial_apart_t (the errbuf object is apart from the internal allocator's arena and flag). *)
amc_cells_owned : EXH_OFF_t /\ errb_obj_owned_t /\ errb_ial_apart_t;
(* ADDED (field round 3, Main 2026-10-30): Printf's two writable image cells (pf_cells_cf above), and the unit image
   row that owns their 16 bytes and keeps them apart from the internal allocator's arena and flag (pf_cells_owned_t:
   pf_cells_static_t /\ pf_ial_apart_t, no field of its own for the IAL part). The row is STATE-INDEPENDENT, like
   amc_cells_owned: a builder that starts from an old ARmcf carries it; the fresh builders take it from the unit's
   rows. *)
amc_pf_cells : pf_cells_cf rd;
amc_pf_owned : pf_cells_owned_t
}.
End Y.

(* ---------------------------------------------------------------------------- *)
(* 2b. Class 1's shadow band. __asan_poison_memory_region (p, cf_head) and        *)
(*     __asan_unpoison_memory_region (p, cf_head) read the shadow byte of         *)
(*     p + cf_head. For a block of request 16 (chunk_class 16 = 1: a 32-byte      *)
(*     chunk, 16 bytes of redzone) p + cf_head is at most the chunk's end, which  *)
(*     is at most region_base ly 1 + rg_mapped_user (reg S 1); for the last chunk *)
(*     of a full class it is region_base ly 1 + kFreeArrayOffset, so the band is  *)
(*     CLOSED at the top. ahs_pres gives that byte, because no vis0 zone holds it  *)
(*     (frontier_not_vis0_cf); the band, abudget_ok_cf's third conjunct, makes it *)
(*     visible. The band reads only ly and the hidden set: hsub keeps it          *)
(*     (cls1_band_vis_hsub_cf, so every SRr step does, wle being hsub) and so     *)
(*     does layout_le (cls1_band_vis_layout_cf). The conversion exposes it once   *)
(*     (YGcfNilInit.v): the page-aligned interval [cls1_band_lo_cf,               *)
(*     cls1_band_hi_cf) of cls1_band_bytes_cf bytes (cls1_band_iv_cf).            *)
Definition cls1_band_vis_cf (ly : alayout) (H : word -> bool) : Prop :=
forall a, shadow_addr (region_base ly 1) <= a <= shadow_addr (region_base ly 1 + kFreeArrayOffset) ->
H (w64 a) = false.
Definition cls1_band_lo_cf (ly : alayout) : Z := shadow_addr (region_base ly 1).
Definition cls1_band_hi_cf (ly : alayout) : Z := shadow_addr (region_base ly 1 + kFreeArrayOffset) + kPage.
Definition cls1_band_bytes_cf : Z := kFreeArrayOffset / 8 + kPage.

Lemma cls1_band_bytes_cf_val : cls1_band_bytes_cf = 469766144.
Proof. reflexivity. Qed.

Lemma cls1_band_vis_hsub_cf : forall ly H H', hsub H' H -> cls1_band_vis_cf ly H -> cls1_band_vis_cf ly H'.
Proof.
intros ly H H' Hs HB a Ha. destruct (H' (w64 a)) eqn:E; [|reflexivity].
pose proof (Hs _ E) as X. rewrite (HB a Ha) in X. discriminate X.
Qed.

Lemma cls1_band_vis_layout_cf : forall n ly ly' H, layout_le n ly ly' -> cls1_band_vis_cf ly H -> cls1_band_vis_cf ly' H.
Proof.
intros n ly ly' H (_ & Esp & _) HB a Ha. unfold region_base in Ha. rewrite Esp in Ha. exact (HB a Ha).
Qed.

Lemma cls1_band_iv_cf : forall ly, layout_ok ly ->
cls1_band_lo_cf ly mod 4096 = 0 /\ cls1_band_hi_cf ly mod 4096 = 0 /\
cls1_band_hi_cf ly - cls1_band_lo_cf ly = cls1_band_bytes_cf /\ 0 <= cls1_band_lo_cf ly /\ cls1_band_hi_cf ly < 2 ^ 64.
Proof.
intros ly LO. pose proof (lo_space_al _ LO) as SA. pose proof (lo_space_in _ LO) as [S1 S2].
pose proof (lo_high _ LO) as [H1 H2]. pose proof (@ASAN_CEIL_range _) as [CR _].
apply Z.mod_divide in SA as [q Hq]; [|lia].
unfold cls1_band_lo_cf, cls1_band_hi_cf, cls1_band_bytes_cf, region_base, region_off, shadow_addr.
change (Z.shiftl 1 32) with 4294967296. rewrite Hq.
replace (q * 65536 + 4294967296) with ((q * 8192 + 536870912) * 8) by ring.
replace ((q * 8192 + 536870912) * 8 + kFreeArrayOffset) with ((q * 8192 + 536870912 + 469762048) * 8)
by (unfold kFreeArrayOffset; ring).
rewrite !Z.div_mul by lia.
unfold SHADOW_OFF, kPage, kFreeArrayOffset.
replace (2147450880 + (q * 8192 + 536870912)) with ((524280 + 2 * q + 131072) * 4096) by ring.
replace (2147450880 + (q * 8192 + 536870912 + 469762048) + 4096) with ((524280 + 2 * q + 131072 + 114688 + 1) * 4096) by ring.
rewrite !Z.mod_mul by lia.
unfold in_high, kHighMemBeg, kPrimResvSize, kSpaceSize, ASAN_CEIL in *. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

(* pairwise over an append relates every element of the left list to every element of the right one *)
Lemma cfb_pairwise_app {X : Type} (R : X -> X -> Prop) : forall l1 l2 x y,
pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
induction l1 as [|h t IH]; intros l2 x y P Hx Hy; [destruct Hx|].
cbn [app pairwise] in P. destruct P as [F P]. destruct Hx as [<-|Hx].
- exact (proj1 (Forall_forall _ _) F y (in_or_app _ _ _ (or_intror Hy))).
- exact (IH l2 x y P Hx Hy).
Qed.

(* The frontier granule's shadow byte is in no vis0 zone. Every vis0 entry lies in the shadow of a
   vis0_zones zone (lo_vis0); every zone is disjoint from the primary reservation (lo_disj for the
   owned extents and the image, lo_ctx for the context map, lo_extra for the extra ranges) or is the
   region-info page at ly_space + kRegionInfoOff, above region 1; and region 1 up to
   kFreeArrayOffset lies inside the reservation (lo_space_in). The shadow map is monotone and the
   reservation's base is page-aligned, so the two shadow ranges cannot meet. *)
Lemma frontier_not_vis0_cf : forall ly g, layout_ok ly ->
region_base ly 1 <= g <= region_base ly 1 + kFreeArrayOffset -> ~ in_vis0 ly (shadow_addr g).
Proof.
intros ly g LO Hg Hv. unfold in_vis0 in Hv. apply Exists_exists in Hv as (v & Hv & Hin).
pose proof (proj1 (Forall_forall _ _) (lo_vis0 _ LO) v Hv) as Hz. apply Exists_exists in Hz as (z & Hz & Z1 & Z2).
unfold in_zr in Hin.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_prim_al _ LO) as PA. unfold page_aligned in PA.
assert (D : fst z + snd z <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= fst z \/ fst z = ly_space ly + kRegionInfoOff).
{ pose proof (lo_disj _ LO) as PD. unfold static_extents, owned_extents in PD. cbn [app pairwise] in PD.
  destruct PD as [F0 _]. rewrite !Forall_cons_iff in F0.
  destruct F0 as (DQ & DT & DF & DNB & DSB & _ & DD & _ & DI & _).
  unfold zdisjoint in DQ, DT, DF, DNB, DSB, DD, DI. cbn [fst snd] in DQ, DT, DF, DNB, DSB, DD, DI.
  unfold vis0_zones in Hz. apply in_app_iff in Hz as [Hz|Hz].
  - cbn [In] in Hz.
    destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd]; try lia.
    pose proof (lo_ctx _ LO) as DC. unfold zdisjoint in DC. cbn [fst snd] in DC. lia.
  - pose proof (lo_extra _ LO) as (_ & _ & PX).
    assert (Hp : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; left; reflexivity).
    pose proof (cfb_pairwise_app zdisjoint _ _ z _ PX Hz Hp) as DX. unfold zdisjoint in DX. cbn [fst snd] in DX. lia. }
unfold region_base, region_off in Hg. change (Z.shiftl 1 32) with 4294967296 in Hg.
unfold shadow_addr in Z1, Z2, Hin. unfold kPrimResvSize, kSpaceSize, kRegionInfoOff, kFreeArrayOffset in *.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The budget, on live state.                                                  *)
Section A0.
Variable segs : list Segment.
Variable B : asyms.
Variable ly : alayout.

(* sec_live_hulls (the live secondaries' hulls) is YGcfNames.v's (moved there for CfParams's hull laws). *)

(* The A side of the budget. A_BASE_CF absorbs cgif's whole event credit (YGcfNames.v);
   prim_committed, 8 * st_sec_reserved and sec_live_bytes are cgif's own live quantities
   (YG01.v:216-220); prim_committed / 8 is the primary's SHADOW (each grant, kUserMapSize or
   kFreeArrayMapSize = 262144, exposes its map and 262144 / 8 bytes of shadow at wallow, so a
   primary grant raises the budget by exactly what it adds to w_A; abudget_grant_fa_cf /
   abudget_grant_user_cf, YGcfAbudget.v); errb_cap_cf is our error-message buffer (YG00cf.v).
   THE HULLS are the unit's cf_hull (YGcfNames.v CfParams, Main 2026-10-30): the hulls the world's
   allowance holds for the secondaries. On wle the world can NOT refund a recycled secondary's hull
   (wrefund, YFfn.v:148, drops only (MAP, MAP + LEN); AI_refund_gen, YFfn.v:182-199, needs an interval
   with no lazy page; frame the internal file SHADOW-REFUND.md section 2), so preset's cf_hull is sec_hulls_cf, cgif's sec_hulls over
   the user entries of st_secs (append-only, a recycle keeps the slot with its sm_len); reply's (after F1, which re-hides
   the interior) is the live hulls + 16384 per recycled secondary. By cf_hull_recycle a recycle lowers
   abudget_cf by the map + at most what the world drops beyond it. NO EV_A * st_nev term. *)
Definition abudget_cf (S : astate) : Z :=
A_BASE_CF + prim_committed S + prim_committed S / 8 + 8 * st_sec_reserved S + sec_live_bytes S
+ cf_hull S + errb_cap_cf S.

(* ---- The run's ALLOCATION METER (Main 2026-10-30, route (B) counting): FUNCTIONS of st_secs, no new state field.
   st_secs is append-only (sec_alloc appends at a GRANTED map only, its z = 0 branch appends nothing; errb_map_cf
   appends a capacity entry; errb_set_size updates its size entry in place or appends it once; sec_dealloc keeps the
   slot), so N counts every entry ever made and T sums their MAPPED lengths sm_len (sec_map_size n for a secondary, the
   capacity / size for the errbuf's control entries). T counts sm_len, never sm_size, so the control entries' negative
   sm_size tags do not enter it. A REQUESTED-byte T would be unsound against 8192 * N (sm_len <= n + 12294; a Theorem Labs lane).
   nsec_cf and sec_T_cf are YGcfNames.v's (moved there for CfParams's hull laws, unchanged). *)

(* Preset's hull term: cgif's sec_hulls (YG01.v:287) restricted to the user entries. *)
Definition sec_hulls_cf (S : astate) : Z :=
fold_right (fun sm acc => (if sec_user_cf sm then sm_len sm / 8 + 8192 else 0) + acc) 0 (st_secs S).

(* The unit's driver proves this from the input length (both bounds are CfParams fields with measured values). *)
Definition sec_meter_ok_cf (S : astate) : Prop := nsec_cf S <= cf_kmax /\ sec_T_cf S <= cf_T_max.

(* The hull sum is at most T / 8 + 8192 * N, by the floor's superadditivity, whatever the entries' signs. *)
Lemma sec_hulls_le_meter : forall S, sec_hulls_cf S <= sec_T_cf S / 8 + 8192 * nsec_cf S.
Proof.
intros S. unfold sec_hulls_cf, sec_T_cf, nsec_cf. induction (st_secs S) as [|sm t IH]; [cbn; lia|].
cbn [fold_right]. set (T := fold_right (fun sm acc => (if sec_user_cf sm then sm_len sm else 0) + acc) 0 t) in *.
destruct (sec_user_cf sm).
- assert (D' : sm_len sm / 8 + T / 8 <= (sm_len sm + T) / 8).
  { pose proof (Z.div_mod (sm_len sm) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sm_len sm) 8 ltac:(lia)).
    pose proof (Z.div_mod T 8 ltac:(lia)). pose proof (Z.mod_pos_bound T 8 ltac:(lia)).
    apply Z.div_le_lower_bound; lia. }
  lia.
- replace (0 + T) with T by lia. lia.
Qed.

Lemma sec_hulls_le_total : forall S, sec_meter_ok_cf S -> sec_hulls_cf S <= cf_sec_total.
Proof.
intros S [HN HT]. pose proof (sec_hulls_le_meter S) as M. unfold cf_sec_total.
assert (D : sec_T_cf S / 8 <= cf_T_max / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* The eager part of the meter (the terms of alc_eager_x below): the primary's committed maps,
   the pointer-array reservation, and the eager bytes of the live secondaries AND of the errbuf
   extent (errb_zone, at most one extent, xs_cf_length), counted by esec (YG0n.v:309), so a remap
   of the errbuf moves the bound by exactly what eager_used_mmap_model / eager_used_munmap
   (YG0j.v:104, :125) move eager_used. The room is E_BASE + eager_cf + abudget_kit_cf + CF_HEAD
   (YGcfRoomCf.v room_rec_cf, in the kit's allowance form; CF_HEAD in YGcfAbudget.v). *)
Definition eager_cf (S : astate) (md : Model) : Z :=
prim_committed S + 8 * st_sec_reserved S
+ esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S ++ errb_zone ly S).

(* The third conjunct, cls1_band_vis_cf (section 2b), is about the world like asecA: a visible
   lazy page is an allowed one (lazy_cover, YK04.v:519), so the band is allowance paid once, at
   the conversion (YGcfNilInit.v). *)
Definition abudget_ok_cf (S : astate) (W : world segs) : Prop :=
A_bytes (w_A W) <= abudget_cf S /\ asecA ly S (w_A W) /\ cls1_band_vis_cf ly (w_H W).

(* Unlike cgif's ameter (YG0n.v:542), which adds prim_committed, 8 * st_sec_reserved and
   sec_live_bytes BESIDE abudget and so counts sec_live_bytes twice, abudget_cf already
   carries them, so the meter is just E_BASE + abudget_cf and nothing is double-counted.
   mroom_cf is then exactly abudget_cf S <= CF_MAX. *)
Definition ameter_cf (S : astate) : Z := E_BASE + abudget_cf S.
Definition mroom_cf (S : astate) : Prop := ameter_cf S + VM_HEAD <= ASAN_VM_LMIN.
Definition qmeter_cf (S : astate) : Prop := qtight S /\ mroom_cf S.

Lemma mroom_cf_CF_MAX : forall S, mroom_cf S <-> abudget_cf S <= CF_MAX.
Proof. intros S. unfold mroom_cf, ameter_cf, CF_MAX. lia. Qed.

(* A step that touches neither the regions, the pointer-array reservation, st_chunks nor st_secs (the tick, the
   internal-allocator flag, a fakestack step) keeps the budget: cf_hull by cf_hull_frame, the other terms read only
   those fields. *)
Lemma abudget_cf_frame : forall S S', st_regions S' = st_regions S -> st_sec_reserved S' = st_sec_reserved S ->
st_chunks S' = st_chunks S -> st_secs S' = st_secs S -> abudget_cf S' = abudget_cf S.
Proof.
intros S S' HR HV HC HS.
assert (EH : cf_hull S' = cf_hull S) by (apply cf_hull_frame; [exact HS | unfold sec_live_hulls; rewrite HC; reflexivity]).
unfold abudget_cf, prim_committed, sec_live_bytes, errb_cap_cf, errb_e. rewrite EH, HR, HV, HC, HS. reflexivity.
Qed.

Lemma mroom_cf_frame : forall S S', st_regions S' = st_regions S -> st_sec_reserved S' = st_sec_reserved S ->
st_chunks S' = st_chunks S -> st_secs S' = st_secs S -> mroom_cf S -> mroom_cf S'.
Proof.
intros S S' HR HV HC HS H. apply mroom_cf_CF_MAX. rewrite (abudget_cf_frame S S' HR HV HC HS).
apply mroom_cf_CF_MAX. exact H.
Qed.

Lemma abudget_ok_cf_frame : forall S S' W, st_regions S' = st_regions S -> st_sec_reserved S' = st_sec_reserved S ->
st_chunks S' = st_chunks S -> st_secs S' = st_secs S -> abudget_ok_cf S W -> abudget_ok_cf S' W.
Proof.
intros S S' W HR HV HC HS (B1 & B2 & B3). split; [rewrite (abudget_cf_frame S S' HR HV HC HS); exact B1|].
split; [|exact B3]. unfold asecA, sec_extents in *. rewrite HC. exact B2.
Qed.


(* ---- The free path's free-array growth is FUNDED. ----
   prim_committed (YG01.v:327-328) sums rg_mapped_fa, so every free-array map the free
   path makes (return_to_allocator, YG00.v:462-467) RAISES abudget_cf, by the map and its
   shadow (prim_committed / 8): what the map needs is mroom_cf AFTER it. Each class's free
   array is capped at kFreeArrayMax, so over the at most 32 regions the growth adds at most
   FA_GROW_MAX + FA_GROW_MAX / 8, and a headroom `abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8
   <= CF_MAX` keeps mroom_cf for every reachable growth.
   The LPS map is then funded, fo_dead_commit3 (YF8e.v:791) removes its ENOMEM outcome,
   and the refused branch (a spin) has no LPS step: afree_realizes_cf's post has none. *)
(* The region-wise relation the free path keeps: user mapping unchanged, old free array
   non-negative, new free array within kFreeArrayMax. *)
Definition fa_grow_rel (r r' : region) : Prop :=
rg_mapped_user r' = rg_mapped_user r /\ 0 <= rg_mapped_fa r /\ rg_mapped_fa r' <= kFreeArrayMax.

Lemma prim_fold_fa_grow : forall rs rs', Forall2 fa_grow_rel rs rs' ->
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 rs'
<= fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 rs + kFreeArrayMax * Z.of_nat (length rs).
Proof.
intros rs rs' H. induction H as [|r r' t t' [U [Z0 M0]] _ IH]; cbn [fold_right length].
- (* kFreeArrayMax is a constant definition, an opaque atom to lia: unfold it first *)
unfold kFreeArrayMax. lia.
- unfold kFreeArrayMax in *. lia.
Qed.

Lemma abudget_cf_fa_grow : forall S S',
Forall2 fa_grow_rel (st_regions S) (st_regions S') -> (length (st_regions S) <= 32)%nat ->
st_sec_reserved S' = st_sec_reserved S -> st_chunks S' = st_chunks S -> st_secs S' = st_secs S ->
abudget_cf S' <= abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8.
Proof.
intros S S' HF H32 HR HC HS.
assert (E1 : sec_live_bytes S' = sec_live_bytes S) by (unfold sec_live_bytes; rewrite HC; reflexivity).
assert (E2 : cf_hull S' = cf_hull S)
by (apply cf_hull_frame; [exact HS | unfold sec_live_hulls; rewrite HC; reflexivity]).
assert (E3 : errb_cap_cf S' = errb_cap_cf S) by (unfold errb_cap_cf, errb_e; rewrite HS; reflexivity).
pose proof (prim_fold_fa_grow (st_regions S) (st_regions S') HF) as P.
assert (L32 : kFreeArrayMax * Z.of_nat (length (st_regions S)) <= FA_GROW_MAX)
by (unfold FA_GROW_MAX, kFreeArrayMax; lia).
assert (PG : prim_committed S' <= prim_committed S + FA_GROW_MAX) by (unfold prim_committed; lia).
assert (PD : prim_committed S' / 8 <= prim_committed S / 8 + FA_GROW_MAX / 8).
{ change (FA_GROW_MAX / 8) with 2147483648.
  rewrite <- (Z.div_add (prim_committed S) 2147483648 8) by lia.
  apply Z.div_le_mono; [lia|]. change FA_GROW_MAX with 17179869184 in PG. lia. }
unfold abudget_cf. rewrite E1, E2, E3, HR. lia.
Qed.

Lemma free_fa_grow_funded_cf : forall S S',
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX ->
abudget_cf S' <= abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 -> mroom_cf S'.
Proof. intros S S' H1 H2. apply mroom_cf_CF_MAX. lia. Qed.
Lemma qmeter_cf_tight : forall S, qmeter_cf S -> qtight S.
Proof. intros S [H _]. exact H. Qed.
Lemma qmeter_cf_room : forall S, qmeter_cf S -> mroom_cf S.
Proof. intros S [_ H]. exact H. Qed.

Lemma sec_live_hulls_nonneg : forall S, 0 <= sec_live_hulls S.
Proof.
intros S. unfold sec_live_hulls. induction (st_chunks S) as [|k t IH]; cbn [fold_right]; [lia|].
destruct (ck_beg k); try exact IH. pose proof (Z.le_max_l 0 (sec_map_size (ck_req k) / 8 + 8192)). lia.
Qed.

(* cgif's historical hull sum dominates the live one, which is what makes cgif's budget
   imply ours at the conversion point. *)
Definition sec_refund_obligation : Prop :=
forall S S', (forall k, In k (st_chunks S') -> In k (st_chunks S)) ->
sec_live_hulls S' <= sec_live_hulls S.

(* ---------------------------------------------------------------------------- *)
(* 4. The ledger. Two fields of cgif's ALedger (YG0n.v:311-333) are WEAKENED, so   *)
(*    cgif's implies ours with no premise: al_cover gains the errbuf extent as an  *)
(*    extra permitted zone, and al_eager_x's esec also counts the errbuf extent    *)
(*    (errb_zone; esec_app, esec_nonneg). Form (A) (Main 2026-10-30): a remap maps *)
(*    the new buffer before it unmaps the old one (a Theorem Labs lane's RepF4Append), so *)
(*    the bound moves with eager_used's own esec steps, never by cap_new - cap_old. *)
Record ALedger_cf (S : astate) (md : Model) : Prop := {
alc_img : forall sg, In sg segs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly);
alc_limit : ASAN_VM_LMIN <= vm_limit (m_vmmaps md);
alc_reserved : vm_reserved (m_vmmaps md) = segments_reserved segs;
alc_prim : exists pieces, prim_pieces_ok ly S pieces /\
(forall p, In p pieces <-> (In (wiv p) (vm_maps (m_vmmaps md)) /\ 0 < snd p /\ ly_prim ly <= fst p /\
fst p + snd p <= ly_prim ly + kPrimResvSize));
alc_Q : In (wiv (ly_Q ly, kPtrArrayResv)) (vm_maps (m_vmmaps md));
alc_hs : In (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)) (vm_maps (m_vmmaps md));
alc_sec : forall e, In e (sec_extents ly S) -> In (wiv e) (vm_maps (m_vmmaps md));
alc_cover : forall e, In e (vm_maps (m_vmmaps md)) ->
Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
(lazy_zones ly ++ sec_extents ly S ++ errb_zone ly S);
alc_eager_x : eager_used md <= E_BASE + eager_cf S md;
alc_perm : forall z, In z (perm_maps ly) -> In (wiv z) (vm_maps (m_vmmaps md));
alc_band : forall z, In z band_maps -> In (wiv z) (vm_maps (m_vmmaps md));
alc_secx : forall e z, In e (sec_extents ly S) -> In z (perm_maps ly) -> zdisjoint e z;
alc_top : YM05.ceil_of_top (alloc_top (m_vmmaps md));
alc_imgcov : forall a, in_zr a (ly_img ly) ->
exists e, In e (segments_reserved segs) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e);
alc_shna : region_free (vm_noaccess (m_vmmaps md)) (w64 kLowShadowBeg) (w64 (kLowShadowEnd - kLowShadowBeg)) = true /\
region_free (vm_noaccess (m_vmmaps md)) (w64 kHighShadowBeg) (w64 (kHighShadowEnd - kHighShadowBeg)) = true;
(* ADDED (Main 2026-10-30, from a Theorem Labs lane's RepF4Append 7th finding): every noaccess or lazy address is
   mapped. Nothing else in ARcf relates m_vm_lazy / vm_noaccess to vm_maps (alc_cover ranges over vm_maps
   only), so a walk could not show that a fresh eager grant has no lazy page (commit_expose's premise). TRUE of
   the machine: noaccess_model adds to both lists (YK13.v:193-198), the lazy arm adds a new map's interior,
   munmap_model subtracts from all; keep lemmas and the init witness in YGcfLazyMaps.v. *)
alc_lazy_in_maps : forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
YK0g.covered (vm_maps (m_vmmaps md)) x = true;
(* ADDED (Main 2026-10-30, from a Theorem Labs lane): the errbuf extent is mapped, alc_sec's twin for xs_cf. It is
   YGcfXs.xs_mapped_cf's body, so the relation carries it (YGcfXs.ARcf_xsm) and no walk states it beside ARcf. *)
alc_xs : forall e, In e (xs_cf ly S) -> In (wiv e) (vm_maps (m_vmmaps md))
}.

Lemma ALedger_cf_of_ALedger : forall S md, ALedger segs ly S md -> xs_cf ly S = [] ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
 YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
ALedger_cf S md.
Proof.
intros S md L HX LM. constructor;
try (exact (al_img _ _ _ _ L)); try (exact (al_limit _ _ _ _ L)); try (exact (al_reserved _ _ _ _ L));
try (exact (al_prim _ _ _ _ L)); try (exact (al_Q _ _ _ _ L)); try (exact (al_hs _ _ _ _ L));
try (exact (al_sec _ _ _ _ L)); try (exact (al_perm _ _ _ _ L)); try (exact (al_band _ _ _ _ L));
try (exact (al_secx _ _ _ _ L)); try (exact (al_top _ _ _ _ L)); try (exact (al_imgcov _ _ _ _ L));
try (exact (al_shna _ _ _ _ L)); try (exact LM).
- intros e He. pose proof (al_cover _ _ _ _ L e He) as H. apply Exists_exists in H as (z & Hz & Hb).
apply Exists_exists. exists z. split; [|exact Hb].
apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left; exact Hz | right; apply in_app_iff; left; exact Hz].
- pose proof (al_eager_x _ _ _ _ L) as HE. unfold eager_cf. rewrite esec_app.
pose proof (esec_nonneg (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (errb_zone ly S)) as Hn. lia.
- intros e He. rewrite HX in He. destruct He.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. ARcf: cgif's AR (YG0n.v:490-491) with every part re-pointed at the cf one.  *)
(*    ahs (YG0n.v:449) is cgif's UNCHANGED: the error-message buffer is an        *)
(*    anonymous map outside sec_extents that is never poisoned, so ahz's claim    *)
(*    that every granule outside the known extents has shadow 0 stays true.       *)
Definition ARcf (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
ARmcf B ly S Hp (aview segs (w_H W) mem) /\ ALedger_cf S md /\ abudget_ok_cf S W /\ amwf md
/\ ahs B ly S (w_H W) mem.

(* The errbuf slot's placement from the relation (ARmcf's last field). *)
Lemma xs_placed_of_ARcf : forall S Hp W mem md, ARcf S Hp W mem md -> xs_placed_cf ly S.
Proof. intros S Hp W mem md [M _]. exact (amc_xs_placed _ _ _ _ _ M). Qed.

(* The two machine cells from the relation (ARmcf's fields, field round 2). *)
Lemma ARcf_exh_cell : forall S Hp W mem md, ARcf S Hp W mem md -> exh_cell_cf B ly S (aview segs (w_H W) mem).
Proof. intros S Hp W mem md [M _]. exact (amc_exh_cell _ _ _ _ _ M). Qed.

Lemma ARcf_errb_cells : forall S Hp W mem md, ARcf S Hp W mem md -> errb_cells_cf B ly S (aview segs (w_H W) mem).
Proof. intros S Hp W mem md [M _]. exact (amc_errb_cells _ _ _ _ _ M). Qed.

(* Printf's two writable image cells from the relation (ARmcf's field, field round 3). *)
Lemma ARcf_pf_cells : forall S Hp W mem md, ARcf S Hp W mem md -> pf_cells_cf B ly (aview segs (w_H W) mem).
Proof. intros S Hp W mem md [M _]. exact (amc_pf_cells _ _ _ _ _ M). Qed.

(* The START WITNESS of the two cells (a Theorem Labs lane's condition, field round 2): ONE named premise of the conversion
   at init (YGcfNilInit.ARcf_nil_init), supplied by each unit's start-up row (the RegionInfo + 68 byte of every class
   and the errbuf object [cf_errbuf_obj, + 56) as start-up leaves them; YGcfInstBase.exh_cell_cf_init /
   errb_cells_cf_init turn the raw zero bytes into it). Over every world the conversion may move to. *)
Definition start_cells_cf (S : astate) (W : world segs) (mem : word -> option byte) : Prop :=
forall W' : world segs, wle W W' ->
exh_cell_cf B ly S (aview segs (w_H W') mem) /\ errb_cells_cf B ly S (aview segs (w_H W') mem).

(* The START WITNESS of Printf's two cells (field round 3): ONE named premise of the conversion at init beside
   start_cells_cf, supplied by each unit's start-up row (the two 8-byte words __asan::AsanInitInternal stores, e.g.
   cgif's start-up band KWords at YB01.v:14 / YB03.v:12). State-free; over every world the conversion may move to. *)
Definition start_pf_cf (W : world segs) (mem : word -> option byte) : Prop :=
forall W' : world segs, wle W W' -> pf_cells_cf B ly (aview segs (w_H W') mem).

(* Field round 3's two unit image rows behind arodata_ok_cf's keep (YG0dcf.v; YGcfRodata.v): the RELRO range
   [cf_relro_lo, cf_relro_hi) lies in one segment of the image (so in ly_img, by ALedger_cf's alc_img), and errno's
   four bytes are apart from it (cgif: 0x5d916c against [0x9dc70, 0x9f000)).  Part 3c: the same two facts for each
   range of cf_ro_reads (the class-full report's read-only reads), which arodata_ok_cf covers too. *)
Definition relro_seg_t : Prop :=
(exists sg, In sg segs /\ Z.of_N (seg_base sg) <= cf_relro_lo /\ cf_relro_hi <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) /\
Forall (fun r => exists sg, In sg segs /\ Z.of_N (seg_base sg) <= fst r /\
  fst r + snd r <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) cf_ro_reads.
Definition errno_relro_t : Prop :=
(as_errno B + 4 <= cf_relro_lo \/ cf_relro_hi <= as_errno B) /\
Forall (fun r => as_errno B + 4 <= fst r \/ fst r + snd r <= as_errno B) cf_ro_reads.

End A0.
End U.

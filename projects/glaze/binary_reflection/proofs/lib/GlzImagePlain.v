(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs. Export OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuHexScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition APLAIN : atable :=
  {| img_lo := 0x10000; img_hi := 0xa7000; n_res := 4; shadow_off := 0;
     a_entry := 0x2e240; rw_lo := 0x71000; rw_len := 0x17000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 10;
     x_imemset := 0; x_imemcpy := 0; x_memset := 0; x_memcpy := 0; x_memiszero := 0;
     x_istrncpy := 0; x_sealed := 0; x_popfree := 0; x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0; x_envscan_k := 0; x_pnscan := 0; x_pnscan_k := 0; stops_more := [] |}.

(* [comment removed for export] *)
Definition GPLAIN : gtable :=
  {| g_ro_lo := 0x10000; g_ro_hi := 0x71000; g_img_lo := 0x10000; g_img_hi := 0xa7000;
     g_newh_got := 0x74630; g_newh_cell := 0x859e0; g_newh_val := 0;   (* [comment removed for export] *)
     g_priv := [(0x859e8, 0x86478); (0x8647c, 0xa6564); (0xa6820, 0xa6bd0)];
     g_tp := 0x86520; g_malloc := 0x61c60; g_free := 0x61b20; g_malloc_thunk := 0x61c60; g_free_thunk := 0x61b20;   (* [comment removed for export] *)
     g_opnew := 0x70334; g_opdel := 0x55f34; g_opdel_sized := 0x55f30; g_memcpy := 0x6ec40; g_memset := 0x6f1c0; g_memmove := 0x6f044;
     g_strlen := 0x6f2f0; g_hello := 0x128d1; g_str_resize := 0x57b68 |}.
Lemma GPLAIN_priv : forall lo hi, In (lo, hi) (g_priv GPLAIN) -> g_ro_hi GPLAIN <= lo /\ hi <= g_img_hi GPLAIN.
Proof. intros lo hi H. cbn in H. destruct H as [H|[H|[H|[]]]]; injection H as <- <-; cbn; lia. Qed.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma plain_segs_in_hull : segs_in_hull_b PSEGS (img_lo APLAIN) (img_hi APLAIN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plain_in_hull : forall a : word,
  APS.in_hull APLAIN (bv_unsigned a) = false -> find_segment PSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside PSEGS (img_lo APLAIN) (img_hi APLAIN)); [exact plain_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma plain_hull_ok : APS.hull_ok APLAIN.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi APLAIN]. unfold KHI. repeat split; reflexivity || lia. Qed.

(* [comment removed for export] *)
Lemma plain_hex0 : scanN Plain_seg_bytes_000 64 0 0x1e000 = true.
Proof. apply PuHexScan.scanN_of_data. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plain_len0 : Z.to_N (Uint63.to_Z (PrimString.length Plain_seg_bytes_000) / 2) = 0x1e000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma plain_hex1 : scanN Plain_seg_bytes_001 64 0 0x43000 = true.
Proof. apply PuHexScan.scanN_of_data. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plain_len1 : Z.to_N (Uint63.to_Z (PrimString.length Plain_seg_bytes_001) / 2) = 0x43000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma plain_segs_eq : PSEGS = [Plain_segment_000; Plain_segment_001;
                               Plain_segment_002; Plain_segment_003].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma plain_rom_ok' : forall x : word,
  0x10000 <= bv_unsigned x -> bv_unsigned x < 0x71000 -> seg_rom PSEGS x <> None.
Proof.
  intros x Hlo Hhi. unfold seg_rom, memory_read.
  destruct (Z_lt_ge_dec (bv_unsigned x) 0x2e000) as [Hlt|Hge].
  - replace (find_segment PSEGS (bv_unsigned x) (Z.of_N 1)) with (Some Plain_segment_000).
    2:{ rewrite plain_segs_eq. cbn [find_segment Plain_segment_000 seg_base seg_size].
        replace (Z.of_N 65536 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 122880) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms Plain_segment_000 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [Plain_seg_bytes_000] (Z.to_N (bv_unsigned x - Z.of_N 65536))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0x1e000); [exact plain_hex0 | rewrite plain_len0; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
  - replace (find_segment PSEGS (bv_unsigned x) (Z.of_N 1)) with (Some Plain_segment_001).
    2:{ rewrite plain_segs_eq. cbn [find_segment Plain_segment_000 Plain_segment_001 seg_base seg_size].
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 122880) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r.
        replace (Z.of_N 188416 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 188416 + Z.of_N 274432) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms Plain_segment_001 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [Plain_seg_bytes_001] (Z.to_N (bv_unsigned x - Z.of_N 188416))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0x43000); [exact plain_hex1 | rewrite plain_len1; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma plain_rom_ok : forall x : word,
  g_ro_lo GPLAIN <= bv_unsigned x -> bv_unsigned x < g_ro_hi GPLAIN -> seg_rom PSEGS x <> None.
Proof.
  intros x Hlo Hhi. cbn [g_ro_lo g_ro_hi GPLAIN] in Hlo, Hhi. apply plain_rom_ok'; lia.
Qed.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AzHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition BSEGS : list Segment := AsanUbsan_loaded_segments.

(* [comment removed for export] *)
Definition ABOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x663000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4b350; rw_lo := 0x102000; rw_len := 0x561000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x809a8; x_imemcpy := 0x8092c; x_memset := 0xfc38c; x_memcpy := 0xfbf88; x_memiszero := 0x80ed8;
     x_istrncpy := 0x80dd4; x_sealed := 0x11aae; x_popfree := 0x51a00;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xed2e0; x_envscan_k := 0xed2ec; x_pnscan := 0xed3a4; x_pnscan_k := 0xed3b0;
     stops_more := [] |}.

(* [comment removed for export] *)
Definition GBOTH : gtable :=
  {| g_ro_lo := 0x10000; g_ro_hi := 0x102000; g_img_lo := 0x10000; g_img_hi := 0x663000;
     g_newh_got := 0x106bc8; g_newh_cell := 0x640840; g_newh_val := 0;   (* [comment removed for export] *)
     g_priv := [(0x107e98, 0x10a568); (0x10ab58, 0x10b9b8); (0x10ba38, 0x10e1b8); (0x10e1c8, 0x10ee98); (0x10ee9a, 0x19fce8);
                (0x19fe08, 0x1a0060); (0x1a0061, 0x630810); (0x641328, 0x641330); (0x641370, 0x641394); (0x662728, 0x662730)];
               (* [comment removed for export] *)
     g_tp := 0x641380; g_errno := 0x6412dc;   (* [comment removed for export] *)
     g_malloc := 0x6ef3c; g_free := 0x6ed6c; g_malloc_thunk := 0x6ed60; g_free_thunk := 0x6ed5c;
     g_opnew := 0x1017a8; g_opdel := 0xe1c80; g_opdel_sized := 0xe1c84;
     g_memcpy := 0x6e3d8; g_memset := 0x6dc28; g_memmove := 0x6df18; g_strlen := 0x5cf48; g_hello := 0x22b00;
     g_str_resize := 0xe38b8; g_amemcpy := 0x6d1dc; g_amemset := 0x6d678; g_amemmove := 0x6d8b8;
     g_stkmal := fun k => match k with 0 => 0x57bdc | 1 => 0x57d50 | 2 => 0x57ee0 | _ => 0x5807c end;
     (* [comment removed for export] *)
     g_opnew_kn := [] |}.

Lemma GBOTH_priv : forall lo hi, In (lo, hi) (g_priv GBOTH) -> g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH.
Proof. intros lo hi H. cbn in H. repeat (destruct H as [H|H]; [injection H as <- <-; cbn; lia|]). destruct H. Qed.
Lemma GBOTH_errno : g_ro_hi GBOTH <= g_errno GBOTH /\ g_errno GBOTH + 4 <= g_img_hi GBOTH.   (* [comment removed for export] *)
Proof. cbn. lia. Qed.

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

Lemma both_segs_in_hull : segs_in_hull_b BSEGS (img_lo ABOTH) (img_hi ABOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_in_hull : forall a : word,
  APS.in_hull ABOTH (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside BSEGS (img_lo ABOTH) (img_hi ABOTH)); [exact both_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma both_hull_ok : APS.hull_ok ABOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ABOTH]. unfold KHI. repeat split; reflexivity || lia. Qed.

(* [comment removed for export] *)
Lemma both_segs_wx_b : wx_segs_nowrap_b BSEGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_segs_wx : wx_segs_nowrap BSEGS.
Proof. apply wx_segs_nowrap_of_b. exact both_segs_wx_b. Qed.

(* [comment removed for export] *)
Lemma both_segs_hi : forall a : word, g_img_hi GBOTH <= bv_unsigned a -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside BSEGS (img_lo ABOTH) (img_hi ABOTH)); [exact both_segs_in_hull|].
  right. cbn [g_img_hi GBOTH] in H. cbn. lia.
Qed.
Lemma both_segs_out : forall a : word,
  ~ (g_img_lo GBOTH <= bv_unsigned a < g_img_hi GBOTH) -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a Ha. apply both_in_hull. unfold APS.in_hull. cbn [img_lo img_hi ABOTH g_img_lo g_img_hi GBOTH] in *.
  destruct (Z_lt_ge_dec (bv_unsigned a) 0x10000) as [H|H].
  - apply Bool.andb_false_iff. left. apply Z.leb_gt. exact H.
  - apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma both_hex0 : scanN AsanUbsan_seg_bytes_000 64 0 0x3b000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma both_len0 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_000) / 2) = 0x3b000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex1 : scanN AsanUbsan_seg_bytes_001 64 0 0xb7000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma both_len1 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_001) / 2) = 0xb7000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_segs_eq : BSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001; AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rom_ok : forall x : word,
  g_ro_lo GBOTH <= bv_unsigned x -> bv_unsigned x < g_ro_hi GBOTH -> seg_rom BSEGS x <> None.
Proof.
  intros x Hlo Hhi. cbn [g_ro_lo g_ro_hi GBOTH] in Hlo, Hhi. unfold seg_rom, memory_read.
  destruct (Z_lt_ge_dec (bv_unsigned x) 0x4b000) as [Hlt|Hge].
  - replace (find_segment BSEGS (bv_unsigned x) (Z.of_N 1)) with (Some AsanUbsan_segment_000).
    2:{ rewrite both_segs_eq. cbn [find_segment AsanUbsan_segment_000 seg_base seg_size].
        replace (Z.of_N 65536 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 241664) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms AsanUbsan_segment_000 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [AsanUbsan_seg_bytes_000] (Z.to_N (bv_unsigned x - Z.of_N 65536))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0x3b000); [exact both_hex0 | rewrite both_len0; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
  - replace (find_segment BSEGS (bv_unsigned x) (Z.of_N 1)) with (Some AsanUbsan_segment_001).
    2:{ rewrite both_segs_eq. cbn [find_segment AsanUbsan_segment_000 AsanUbsan_segment_001 seg_base seg_size].
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 241664) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r.
        replace (Z.of_N 307200 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 307200 + Z.of_N 749568) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms AsanUbsan_segment_001 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [AsanUbsan_seg_bytes_001] (Z.to_N (bv_unsigned x - Z.of_N 307200))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0xb7000); [exact both_hex1 | rewrite both_len1; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
Qed.

Lemma both_ro_hi : g_ro_hi GBOTH < 2 ^ 64.
Proof. reflexivity. Qed.

Lemma both_G_ro_img2 : g_img_lo GBOTH <= g_ro_lo GBOTH /\ g_ro_lo GBOTH <= g_ro_hi GBOTH <= g_img_hi GBOTH.
Proof. cbn. lia. Qed.



Lemma both_A_img_hi : img_hi ABOTH = g_img_hi GBOTH.
Proof. reflexivity. Qed.
Lemma both_A_img_lo : img_lo ABOTH = g_img_lo GBOTH.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma both_thunk_step : forall fx R M (p t : Z) rd (imm : bv 21) w,
  fetch_word BSEGS (Z_to_bv 64 p) = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) -> bv_eqb rd 0%bv = true ->
  (Z.leb 0 p && Z.ltb p (2 ^ 64) && Z.eqb t (p + bv_signed imm))%bool = true ->
  RiscvSemantics.step BSEGS (GPS.mkstF fx R (Z_to_bv 64 p) M (seg_rom BSEGS)) = MachineOk (GPS.mkstF fx R (Z_to_bv 64 t) M (seg_rom BSEGS)).
Proof.
  intros fx R M p t rd imm w Hf Hec Hd Hrd Hb. apply andb_prop in Hb as [Hb Ht]. apply andb_prop in Hb as [Hp1 Hp2].
  apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. apply Z.eqb_eq in Ht. subst t.
  unfold GPS.mkstF. rewrite <- !mkstR_None.
  rewrite (stepR_jal_link fx BSEGS R _ M (seg_rom BSEGS) None w rd imm Hf Hec Hd). rewrite Hrd.
  unfold btgt, v_addi. rewrite u64_lit by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma both_thunk_strlen_step : forall fx R M,
  RiscvSemantics.step BSEGS (GPS.mkstF fx R (Z_to_bv 64 (g_strlen GBOTH)) M (seg_rom BSEGS))
  = MachineOk (GPS.mkstF fx R (Z_to_bv 64 0x5cfec) M (seg_rom BSEGS)).
Proof.
  intros. eapply (both_thunk_step fx R M 0x5cf48 0x5cfec);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.


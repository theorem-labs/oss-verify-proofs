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
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AzHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS : list Segment := Asan_loaded_segments.

(* [comment removed for export] *)
Definition AASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x65d000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4a8e0; rw_lo := 0xfb000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x7ff38; x_imemcpy := 0x7febc; x_memset := 0xf56e4; x_memcpy := 0xf52e0; x_memiszero := 0x80468;
     x_istrncpy := 0x80364; x_sealed := 0x11abe; x_popfree := 0x50f90;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xe6638; x_envscan_k := 0xe6644; x_pnscan := 0xe66fc; x_pnscan_k := 0xe6708;
     stops_more := [] |}.

(* [comment removed for export] *)
Definition GASAN : gtable :=
  {| g_ro_lo := 0x10000; g_ro_hi := 0xfb000; g_img_lo := 0x10000; g_img_hi := 0x65d000;
     g_newh_got := 0xfff20; g_newh_cell := 0x639c00; g_newh_val := 0;   (* [comment removed for export] *)
     g_priv := [(0x1011f0, 0x1038c0); (0x103f18, 0x104d78); (0x104df8, 0x107578); (0x107588, 0x108258); (0x10825a, 0x1990a8);
                (0x1991c8, 0x199420); (0x199421, 0x629bd0); (0x63a6e8, 0x63a6f0); (0x63a730, 0x63a754); (0x65bae8, 0x65baf0)];
               (* [comment removed for export] *)
     g_tp := 0x63a740; g_errno := 0x63a69c;   (* [comment removed for export] *)
     g_malloc := 0x6e4cc; g_free := 0x6e2fc; g_malloc_thunk := 0x6e2f0; g_free_thunk := 0x6e2ec;
     g_opnew := 0xfab00; g_opdel := 0xdafd8; g_opdel_sized := 0xdafdc;
     g_memcpy := 0x6d968; g_memset := 0x6d1b8; g_memmove := 0x6d4a8; g_strlen := 0x5c4d8; g_hello := 0x22b40;
     g_str_resize := 0xdcc10; g_amemcpy := 0x6c76c; g_amemset := 0x6cc08; g_amemmove := 0x6ce48;
     g_stkmal := fun k => match k with 0 => 0x5716c | 1 => 0x572e0 | 2 => 0x57470 | _ => 0x5760c end;
     (* [comment removed for export] *)
     g_opnew_kn := [] |}.

Lemma GASAN_priv : forall lo hi, In (lo, hi) (g_priv GASAN) -> g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN.
Proof. intros lo hi H. cbn in H. repeat (destruct H as [H|H]; [injection H as <- <-; cbn; lia|]). destruct H. Qed.
Lemma GASAN_errno : g_ro_hi GASAN <= g_errno GASAN /\ g_errno GASAN + 4 <= g_img_hi GASAN.   (* [comment removed for export] *)
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

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo AASAN) (img_hi AASAN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull AASAN (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo AASAN) (img_hi AASAN)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok AASAN.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi AASAN]. unfold KHI. repeat split; reflexivity || lia. Qed.

(* [comment removed for export] *)
Lemma asan_segs_wx_b : wx_segs_nowrap_b ASEGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_segs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. exact asan_segs_wx_b. Qed.

(* [comment removed for export] *)
Lemma asan_segs_hi : forall a : word, g_img_hi GASAN <= bv_unsigned a -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo AASAN) (img_hi AASAN)); [exact asan_segs_in_hull|].
  right. cbn [g_img_hi GASAN] in H. cbn. lia.
Qed.
Lemma asan_segs_out : forall a : word,
  ~ (g_img_lo GASAN <= bv_unsigned a < g_img_hi GASAN) -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a Ha. apply asan_in_hull. unfold APS.in_hull. cbn [img_lo img_hi AASAN g_img_lo g_img_hi GASAN] in *.
  destruct (Z_lt_ge_dec (bv_unsigned a) 0x10000) as [H|H].
  - apply Bool.andb_false_iff. left. apply Z.leb_gt. exact H.
  - apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma asan_hex0 : scanN Asan_seg_bytes_000 64 0 0x3a000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma asan_len0 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_000) / 2) = 0x3a000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex1 : scanN Asan_seg_bytes_001 64 0 0xb1000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma asan_len1 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_001) / 2) = 0xb1000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_segs_eq : ASEGS = [Asan_segment_000; Asan_segment_001; Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rom_ok : forall x : word,
  g_ro_lo GASAN <= bv_unsigned x -> bv_unsigned x < g_ro_hi GASAN -> seg_rom ASEGS x <> None.
Proof.
  intros x Hlo Hhi. cbn [g_ro_lo g_ro_hi GASAN] in Hlo, Hhi. unfold seg_rom, memory_read.
  destruct (Z_lt_ge_dec (bv_unsigned x) 0x4a000) as [Hlt|Hge].
  - replace (find_segment ASEGS (bv_unsigned x) (Z.of_N 1)) with (Some Asan_segment_000).
    2:{ rewrite asan_segs_eq. cbn [find_segment Asan_segment_000 seg_base seg_size].
        replace (Z.of_N 65536 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 237568) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms Asan_segment_000 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [Asan_seg_bytes_000] (Z.to_N (bv_unsigned x - Z.of_N 65536))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0x3a000); [exact asan_hex0 | rewrite asan_len0; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
  - replace (find_segment ASEGS (bv_unsigned x) (Z.of_N 1)) with (Some Asan_segment_001).
    2:{ rewrite asan_segs_eq. cbn [find_segment Asan_segment_000 Asan_segment_001 seg_base seg_size].
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 237568) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r.
        replace (Z.of_N 303104 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 303104 + Z.of_N 724992) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    cbn [seg_readable seg_perms Asan_segment_001 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at [Asan_seg_bytes_001] (Z.to_N (bv_unsigned x - Z.of_N 303104))) as [b|] eqn:Hb; [discriminate|].
    exfalso. revert Hb. apply (segment_byte_at_some1 _ 0xb1000); [exact asan_hex1 | rewrite asan_len1; lia | ].
    rewrite Z2N.id by lia. cbn. lia.
Qed.

Lemma asan_ro_hi : g_ro_hi GASAN < 2 ^ 64.
Proof. reflexivity. Qed.

Lemma asan_G_ro_img2 : g_img_lo GASAN <= g_ro_lo GASAN /\ g_ro_lo GASAN <= g_ro_hi GASAN <= g_img_hi GASAN.
Proof. cbn. lia. Qed.



Lemma asan_A_img_hi : img_hi AASAN = g_img_hi GASAN.
Proof. reflexivity. Qed.
Lemma asan_A_img_lo : img_lo AASAN = g_img_lo GASAN.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_thunk_step : forall fx R M (p t : Z) rd (imm : bv 21) w,
  fetch_word ASEGS (Z_to_bv 64 p) = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) -> bv_eqb rd 0%bv = true ->
  (Z.leb 0 p && Z.ltb p (2 ^ 64) && Z.eqb t (p + bv_signed imm))%bool = true ->
  RiscvSemantics.step ASEGS (GPS.mkstF fx R (Z_to_bv 64 p) M (seg_rom ASEGS)) = MachineOk (GPS.mkstF fx R (Z_to_bv 64 t) M (seg_rom ASEGS)).
Proof.
  intros fx R M p t rd imm w Hf Hec Hd Hrd Hb. apply andb_prop in Hb as [Hb Ht]. apply andb_prop in Hb as [Hp1 Hp2].
  apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. apply Z.eqb_eq in Ht. subst t.
  unfold GPS.mkstF. rewrite <- !mkstR_None.
  rewrite (stepR_jal_link fx ASEGS R _ M (seg_rom ASEGS) None w rd imm Hf Hec Hd). rewrite Hrd.
  unfold btgt, v_addi. rewrite u64_lit by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma asan_thunk_strlen_step : forall fx R M,
  RiscvSemantics.step ASEGS (GPS.mkstF fx R (Z_to_bv 64 (g_strlen GASAN)) M (seg_rom ASEGS))
  = MachineOk (GPS.mkstF fx R (Z_to_bv 64 0x5c57c) M (seg_rom ASEGS)).
Proof.
  intros. eapply (asan_thunk_step fx R M 0x5c4d8 0x5c57c);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.


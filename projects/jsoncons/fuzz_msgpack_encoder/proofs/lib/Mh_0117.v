(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.
Module Na0DefsK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x6b6000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x57f60; rw_lo := 0x150000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x92388; x_imemcpy := 0x9230c; x_memset := 0x14916c; x_memcpy := 0x148d68; x_memiszero := 0x928d4;
     x_istrncpy := 0x927b4; x_sealed := 0x11bd7; x_popfree := 0x5e610;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x13721c; x_envscan_k := 0x137228; x_pnscan := 0x1372e0; x_pnscan_k := 0x1372ec;
     stops_more := [0x5c284; 0x5d8a8; 0x81f04; 0x88a4c; 0x88a60; 0x88a74; 0x8e404; 0x8e4d4; 0x9ba1c; 0x9c928; 0x9cab8; 0xa6810] |}.
Definition ASAN0_TEXT_LO : Z := 0x57f60.
Definition ASAN0_TEXT_N : nat := 253531%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x81ab8 0x156da0 0x156da8 0x156db0 0x160768 0x160770 0x160760.
Definition X_MAXVA_ASAN0 : Z := 0x939ec.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

End Na0DefsK.
From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.
Module Na0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanPlanSoundSumsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034.AsanHexScan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.
Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.   (* [comment removed for export] *)
Import ListNotations.
Import AX2K. Import APCK. Import APK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition Asan0_top : Z := 0x6b6000.

(* [comment removed for export] *)
Lemma Asan0_wx_nowrap : wx_segs_nowrap ASEGS0.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan0_segs_below : segs_below_b ASEGS0 Asan0_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan0_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan0_top <= bv_unsigned a)%Z) -> H_off_segments ASEGS0 H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan0_segs_below Ha). Qed.
Lemma Asan0_H_off_mkH : forall L A, ranges_from_b L Asan0_top = true -> H_off_segments ASEGS0 (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan0_segs_below HL). Qed.

(* [comment removed for export] *)
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

Lemma asan0_segs_in_hull : segs_in_hull_b ASEGS0 (img_lo ASAN0) (img_hi ASAN0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_in_hull : forall a : word,
  APSK.in_hull ASAN0 (bv_unsigned a) = false -> find_segment ASEGS0 (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS0 (img_lo ASAN0) (img_hi ASAN0)); [exact asan0_segs_in_hull|].
  unfold APSK.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan0_res_len : APSK.res_len_ok ASEGS0 ASAN0.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_res_eq : segments_reserved ASEGS0 = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x47000); (Z_to_bv 64 0x57000, Z_to_bv 64 0xf9000);
                                            (Z_to_bv 64 0x150000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x158000, Z_to_bv 64 0x55e000)].
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_res_hull : Forall (fun iv => img_lo ASAN0 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN0) (segments_reserved ASEGS0).
Proof.
  rewrite asan0_res_eq. cbn [img_lo img_hi ASAN0].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan0_hull_ok : APSK.hull_ok ASAN0.
Proof. unfold APSK.hull_ok. cbn [img_lo img_hi ASAN0]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan0_shadow_ok : APSK.shadow_ok ASAN0.
Proof. unfold APSK.shadow_ok. cbn [shadow_off ASAN0]. lia. Qed.

Lemma asan0_res_sizes : APSK.sum_sizes (segments_reserved ASEGS0) = 0x6a6000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan0_hex2 : scanN Asan_seg_bytes_002 64 0 32768 = true.
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_hex3 : scanN Asan_seg_bytes_003 64 0 5627904 = true.
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5627904%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_segs_eq : ASEGS0 = [Asan_segment_000; Asan_segment_001;
                                Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan0_rw_window : forall m (x : word),
  0x150000 <= bv_unsigned x < 0x6b6000 -> wview ASEGS0 m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS0 (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan0_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact asan0_hex2 | rewrite asan0_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5627904); [exact asan0_hex3 | rewrite asan0_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x158000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma asan0_hull_tiled : forall z, img_lo ASAN0 <= z < img_hi ASAN0 -> APSK.in_ivs z (segments_reserved ASEGS0) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi ASAN0] in Hz. rewrite asan0_res_eq. unfold APSK.in_ivs. cbn [existsb fst snd].
  rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x57000) as [H1|H1].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  destruct (Z.lt_ge_cases z 0x150000) as [H2|H2].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  destruct (Z.lt_ge_cases z 0x158000) as [H3|H3].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma asan0_hull_lt : img_lo ASAN0 < img_hi ASAN0.
Proof. cbn [img_lo img_hi ASAN0]. lia. Qed.

(* [comment removed for export] *)
Lemma segs_wr_of_forallb : forall segs,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSXK.segs_wr_ok segs.
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma asan0_segs_wr : APSXK.segs_wr_ok ASEGS0.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan0_img_facts : img_facts ASEGS0 ASAN0 APH0.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN0]. lia.
  - vm_compute. reflexivity.
  - exact asan0_res_hull.
  - rewrite asan0_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN0]. split; [lia|]. intros m x Hx. apply asan0_rw_window. lia.
  - exact asan0_shadow_ok.
Qed.

End Na0PlanImagesK.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.
Module AsanPopFreeAsanK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPopFree. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

#[local] Notation ASEGS0 := Asan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0x5e610.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS0 (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec Asan.M.loaded_segments asan_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok ASEGS0 mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps ASEGS0 (mkst regs (Z_to_bv 64 asan_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (asan_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  apply (popfree_loop_run ASEGS0 asan_popfree_head); [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

End AsanPopFreeAsanK.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.
Module Na0ArtCellsK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1426456 + 40, 4%nat, 0xffffffff); (1426456 + 56, 1%nat, 0); (0x10448, 8%nat, 0xafffff00000fffff); (0x156d78, 8%nat, 0x1ef520); (0x1ef520, 8%nat, 4096);
    (0x1f15a8 + 260, 1%nat, 0); (0x1f15a8 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x156d98, 8%nat, 0x15fa78); (0x15fa78, 8%nat, 0x7fff8000); (0x156da0, 8%nat, 0x160768); (0x160768, 8%nat, 0); (0x156da8, 8%nat, 0x160770); (0x160770, 8%nat, 0);
    (0x156db0, 8%nat, 0x160760); (0x160760, 8%nat, 2 ^ 47 - 1); (0x156d90, 8%nat, 0x15d278); (0x15d278 + 78, 1%nat, 1); (0x156db8, 8%nat, 0x158da8); (0x158da8, 8%nat, 0x14916c);
    (0x156d88, 8%nat, 0x1f15a8); (0x1f15a8 + 120, 8%nat, 18446744073709551615); (0x15f2dc, 1%nat, 1);
    (* [comment removed for export] *)
    (0x15f2e0, 1%nat, 1); (0x15f2e4, 4%nat, 0); (0x693b00 - 88, 8%nat, 0x6b4fb8);
    (* [comment removed for export] *)
    (0x10468, 8%nat, 0x218a392cd3d5dbf); (0x104ec, 1%nat, 3); (0x10380, 8%nat, 0xcc6e96b9cc6e96b9); (0x105f0, 1%nat, 4); (0x10619, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10328, 8%nat, 0x35253c9ade8f4ca8); (0x10440, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x160758, 1%nat, 1); (0x1e1ce2, 1%nat, 0); (1426456 + 3616, 8%nat, 2 ^ 40); (1426456 + 3624, 2%nat, 16); (1426456 + 3626, 2%nat, 2048);
    (0x1f1540, 8%nat, 0); (0x1f1548, 8%nat, 0); (0x15d278 + 44, 4%nat, 4096); (0x15d278 + 48, 4%nat, 0); (0x15d278 + 52, 4%nat, 190); (0x15d278 + 85, 1%nat, 1);
    (0x1579f8, 8%nat, 0x10); (0x16077c, 4%nat, 30); (0x1f15a8 + 34, 1%nat, 1); (0x15c6f0 + 80, 8%nat, 2 ^ 20); (0x15c6f0 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x158d50, 8%nat, 0x14988c); (0x158be0, 8%nat, 0x148c6c);
    (* [comment removed for export] *)
    (0x158c30, 8%nat, 0x14686c); (0x158be8, 8%nat, 0x13b8b8);
    (* [comment removed for export] *)
    (0x693b00 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1426456 + 64, 8%nat, 4096); (1426456 + 64 + 56, 8%nat, 0); (1426456 + 64 + 48, 8%nat, 0); (1426456 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x15c6f0 + 160, 8%nat, 0); (0x15c6f0 + 168, 8%nat, 0); (0x15c6f0 + 176, 8%nat, 0); (0x15c6f0 + 184, 8%nat, 0); (0x15c6f0 + 152, 1%nat, 0); (0x15c6f0 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1ef508, 1%nat, 0); (0x1ef509, 1%nat, 0);
    (* [comment removed for export] *)
    (0x641958, 4%nat, 1);
    (* [comment removed for export] *)
    (1426456 + 64 + 617, 3%nat, 0); (0x15c6f0 + 154, 2%nat, 0); (0x1ef508, 4%nat, 0);
    (0x156d80, 8%nat, 0x158de0); (0x158de0, 8%nat, 0x1a96d); (0x160759, 1%nat, 1); (0x1f16a3, 1%nat, 1); (0x1f1631, 1%nat, 1); (0x1f15a8 + 84, 1%nat, 1);
    (0x1ef518, 4%nat, 0); (0x15fa80, 4%nat, 1); (0x158da0, 8%nat, 0x148d68);
    (* [comment removed for export] *)
    (0x15c6f0 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x156dd8, 8%nat, 1);
    (0x158d38, 8%nat, 0x12fbf0); (0x157900, 8%nat, 0x160759); (0x158c98, 8%nat, 0x149d4c); (0x156de8, 8%nat, 0x1ef518); (0x157ba0, 8%nat, 8);
    (0x1f15fc, 1%nat, 1); (0x158bf0, 8%nat, 0x14f76c); (0x158bf8, 8%nat, 0x140154); (0x158c20, 8%nat, 0x146850); (0x158c28, 8%nat, 0x14056c);
    (0x158ba8, 8%nat, 0x158ba8); (0x15c3c0, 8%nat, 1); (0x15c410, 1%nat, 0); (0x15d290, 4%nat, 1); (0x15d330, 8%nat, 0); (0x1f1920, 1%nat, 0);
    (0x693af8, 8%nat, 0x693b20); (0x693b28, 8%nat, 0x694300);
    (* [comment removed for export] *)
    (0x158bb0, 8%nat, 0x149650); (0x158c78, 8%nat, 0x137900); (0x158c80, 8%nat, 0x1495b8);
    (* [comment removed for export] *)
    (0x104f0, 1%nat, 4);
    (* [comment removed for export] *)
    (0x15d294, 1%nat, 0);
    (* [comment removed for export] *)
    (0x158d48, 8%nat, 0x137ae8);
    (* [comment removed for export] *)
    (0x15d2d8, 1%nat, 1);
    (* [comment removed for export] *)
    (0x158bd0, 8%nat, 0x148d38); (0x1f16a6, 1%nat, 1); (0x1f16a7, 1%nat, 1);
    (* [comment removed for export] *)
    (0x103a8, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

Definition chk_lit1 (k : list kentry) (c : Z * nat * Z) : bool :=
  let '(a, w, v) := c in
  (chk_sub k a w v || chk_img ASEGS0 ASAN0 k a w v || (chk_zero k (ELit 0) a (Z.of_nat w) && Z.eqb v 0 && Nat.leb w 8 && Z.leb 0 a))%bool.
Definition art_lits_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) ART_LITW.

Section Lits.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Lemma art_lit1 : forall E cs R FULL model c, CSOK E cs R FULL model -> chk_lit1 (kn cs) c = true ->
    cell ASEGS0 FULL (fst (fst c)) (snd (fst c)) (snd c).
  Proof.
    intros E cs R FULL model [[a w] v] HC H. cbn [fst snd]. unfold chk_lit1 in H. unfold cell.
    apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - exact (hc_sub ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model a w v HC H).
    - exact (hc_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model a w v HC H).
    - apply andb_prop in H as [H Ha]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hv].
      apply Z.eqb_eq in Hv. subst v. apply Nat.leb_le in Hw. apply Z.leb_le in Ha.
      apply (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (ELit 0) a (Z.of_nat w) HC H a w Hw);
        unfold uE; cbn [edenot]; rewrite u64_lit by lia; lia.
  Qed.

  Lemma art_lit : forall E cs R FULL model, CSOK E cs R FULL model -> art_lits_chk cs = true ->
    forall a w v, In (a, w, v) ART_LITW -> cell ASEGS0 FULL a w v.
  Proof.
    intros E cs R FULL model HC H a w v Hin.
    exact (art_lit1 E cs R FULL model (a, w, v) HC (proj1 (forallb_forall _ _) H _ Hin)).
  Qed.
End Lits.

(* [comment removed for export] *)
Lemma cell0_cat : forall (M : word -> option byte) a (w1 w2 : nat), 0 <= a -> a + Z.of_nat w1 < 2 ^ 64 -> (w1 + w2 <= 8)%nat ->
  cell ASEGS0 M a w1 0 -> cell ASEGS0 M (a + Z.of_nat w1) w2 0 -> cell ASEGS0 M a (w1 + w2) 0.
Proof.
  intros M a w1 w2 Ha Hn Hw H1 H2. unfold cell in *. rewrite wleb_zero in * by lia.
  assert (H2' : rdn ASEGS0 M (Z_to_bv 64 a + nat_to_word w1)%bv w2 = Some (repeat (Z_to_bv 8 0) w2)).
  { replace (Z_to_bv 64 a + nat_to_word w1)%bv with (Z_to_bv 64 (a + Z.of_nat w1)); [exact H2|].
    apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (Z.of_nat w1)) by lia. reflexivity. }
  rewrite (rdn_app ASEGS0 M w1 w2 (Z_to_bv 64 a) _ _ H1 H2'). rewrite repeat_app. reflexivity.
Qed.

End Na0ArtCellsK.
From LinuxProcessSemantics.Riscv Require Instr. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.
Module Na0HandoffK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* [comment removed for export] *)
Definition M_KSPACE : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 224); am_len := ELit 0x2000011000; am_kind := KRW |}.
Definition M_PTRARR : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 250); am_len := ELit 0x800000; am_kind := KNONELAZY |}.
Definition RESm0 : list amap := [M_KSPACE; M_PTRARR].

(* [comment removed for export] *)
Definition as0_chk (cs : acs) : bool :=
  (no_fog (a_maps cs) && hops_in_maps (a_maps cs) (a_hna cs) && hops_in_maps (a_maps cs) (a_hlz cs)
   && forallb (vis_sh_wr ASAN0 (kn cs)) (a_vis cs) && forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs)
   && existsb (amap_eqb M_LOW) (a_maps cs) && existsb (amap_eqb M_GAP) (a_maps cs) && existsb (amap_eqb M_HIGH) (a_maps cs)
   && forallb (fun m => existsb (amap_eqb m) (a_maps cs)) RESm0
   && forallb (fun m => match xlo (kn cs) (am_base m) with Some lo => Z.ltb 0 lo | None => false end) RESm0)%bool.

Lemma asan0_resv_pos : forall b s, In (b, s) (segments_reserved ASEGS0) -> 0 < bv_unsigned s.
Proof.
  intros b s H. rewrite asan0_res_eq in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; rewrite u64_lit by lia; lia.
Qed.

Section As0Handoff.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK : as0_chk cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_chk_parts :
    no_fog (a_maps cs) = true /\ hops_in_maps (a_maps cs) (a_hna cs) = true /\ hops_in_maps (a_maps cs) (a_hlz cs) = true
    /\ forallb (vis_sh_wr ASAN0 (kn cs)) (a_vis cs) = true /\ forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true
    /\ In M_LOW (a_maps cs) /\ In M_GAP (a_maps cs) /\ In M_HIGH (a_maps cs)
    /\ (forall m, In m RESm0 -> In m (a_maps cs))
    /\ (forall m, In m RESm0 -> exists lo, xlo (kn cs) (am_base m) = Some lo /\ 0 < lo).
  Proof.
    unfold as0_chk in CHK. repeat (apply andb_prop in CHK as [CHK ?]).
    repeat split; try assumption; try (apply hl_in_amapb; assumption).
    - intros m Hm. apply hl_in_amapb. exact (proj1 (forallb_forall _ _) H0 m Hm).
    - intros m Hm. pose proof (proj1 (forallb_forall _ _) H m Hm) as Hx. cbn beta in Hx.
      destruct (xlo (kn cs) (am_base m)) as [lo|]; [|discriminate]. exists lo. split; [reflexivity | apply Z.ltb_lt; exact Hx].
  Qed.

  Definition as0_RES (E : env) : list (Z * Z) := RES_of RESm0 E.
  Definition as0_BASE : Z := BASE_of cs EXTRA.
  Definition as0_A0 (E : env) : list (Z * Z) := A0_of ASAN0 cs EXTRA E.

  Theorem as0_bridge_static : forall E R FULL model, CSOK E cs R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    exact (hb_bridge_static ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok ltac:(cbn; unfold SHB_LO; lia) asan0_res_hull asan0_resv_pos
             cs C1 C6 C7 C8 RESm0 C9 C10 BUDGET LENMAX KMAX BUD GAP E R FULL model HC).
  Qed.

  Theorem as0_binv_main : forall E R FULL model, CSOK E cs R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) as0_BASE BUDGET [] (as0_A0 E) FULL model.
  Proof.
    intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    exact (hb_binv_main ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok asan0_shadow_ok AH ltac:(cbn; unfold SHB_LO; lia)
             cs C1 C2 C3 C4 C5 C6 C8 BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf BUD_le E R FULL model HC).
  Qed.
End As0Handoff.

End Na0HandoffK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module Na0DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0ArtCellsK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MuslStrlen. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition KE_SPK (k : Z) : expr := EAlu ALU_ADD e_sp0 (ELit k).
(* [comment removed for export] *)
Definition KE_ENVP : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1))
     (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))) (ELit 16).
(* [comment removed for export] *)
Definition KE_P0 : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
     (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10)))))) (ELit 184).
(* [comment removed for export] *)
Definition KE_P1X : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
     (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))))) (ELit 185).
Definition KE_P1 : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar 1)) KE_P1X.

(* [comment removed for export] *)
Definition DRV_REGS : list (Z * expr) :=
  [(1, ELit 0x137500); (2, KE_SPK (-48)); (3, ELit 0x10800); (4, ELit 0x693b00); (8, KE_SPK 8); (9, EVar 1); (10, EVar 1); (11, KE_SPK 8);
   (12, KE_ENVP); (18, ELit 0xaea2c); (19, KE_ENVP); (20, ELit 0); (21, ELit 0); (22, ELit 0); (23, ELit 0); (24, ELit 0); (25, ELit 0);
   (26, ELit 0); (27, ELit 0)].

Definition opt_eqb (o : option expr) (e : expr) : bool := match o with Some v => expr_eqb v e | None => false end.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end)%bool k.

(* [comment removed for export] *)
Definition DRV_IMG : list (Z * Z) := [(0x10000, 0x158de8); (0x158e04, 0x15c3a0); (0x6820ca, 0x693a30); (0x6b3dc8, 0x6b3df8)].   (* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition drv_chk (cs : acs) : bool :=
  (Z.eqb (pc cs) 0xaea2c
   && forallb (fun p => expr_eqb (sr_get (s_regs (a_ss cs)) (Z_to_bv 5 (fst p))) (snd p)) DRV_REGS
   && lin_nowrapR (kn cs) e_sp0 && lin_nowrapR (kn cs) (KE_SPK (-48)) && lin_nowrapR (kn cs) (KE_SPK 8) && lin_nowrapR (kn cs) KE_ENVP
   && lin_nowrapR (kn cs) KE_P0 && lin_nowrapR (kn cs) KE_P1X
   && opt_eqb (kfind_word (kn cs) e_sp0 0 8) (EVar 1) && opt_eqb (kfind_word (kn cs) e_sp0 8 8) KE_P0
   && opt_eqb (kfind_word (kn cs) e_sp0 16 8) KE_P1
   && opt_eqb (kfind_wr (kn cs) e_sp0 (-8388608)) (ELit 8388608)
   && match kfind_word (kn cs) (ELit 0) 0x6b3b40 8 with Some v => opt_eqb (kfind_word (kn cs) (ELit 0) 0x693af0 8) v | None => false end
   && forallb (fun r => img_cover (kn cs) (fst r) (snd r)) DRV_IMG
   && match a_fd cs with FdStd => true | _ => false end)%bool.

(* [comment removed for export] *)
Definition KE_AUX : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
    (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))).
Definition KE_RND : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
    (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10)))))).
Definition AUX_OFFS : list Z := [24; 32; 40; 48; 56; 64; 72; 80; 88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176].
Definition is_some {X} (o : option X) : bool := match o with Some _ => true | None => false end.
Definition kfind_blob16 (k : list kentry) (b : expr) (off : Z) : option nat :=
  match List.find (fun K => match K with
                            | KBlob a n _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off && expr_eqb n (ELit 16))%bool
                            | _ => false end) k with
  | Some (KBlob _ _ i) => Some i
  | _ => None
  end.
Lemma kfind_blob16_In : forall k b off i, kfind_blob16 k b off = Some i -> In (KBlob (SA b off) (ELit 16) i) k.
Proof.
  intros k b off i H. unfold kfind_blob16 in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | |a n i'| | | | | | | ]; try discriminate.
  injection H as <-. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply expr_eqb_eq in H3. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Definition stk_chk (cs : acs) : bool :=
  (forallb (fun off => is_some (kfind_word (kn cs) KE_AUX off 8)) AUX_OFFS
   && lin_nowrapR (kn cs) KE_AUX && lin_nowrapR (kn cs) KE_RND
   && is_some (kfind_blob16 (kn cs) KE_RND 184))%bool.


(* [comment removed for export] *)
Definition KE_RNDP : expr := EAlu ALU_ADD KE_RND (ELit 184).
Definition KE_AUXP : expr := EAlu ALU_ADD KE_AUX (ELit 24).
Definition AUXV_EXP : list (Z * expr) :=
  combine AUX_OFFS [ELit 3; ELit 0x10040; ELit 4; ELit 56; ELit 5; ELit 11; ELit 16; EVar 9; ELit 6; ELit 4096; ELit 11; EVar 8; ELit 12; EVar 8;
                    ELit 23; ELit 0; ELit 25; KE_RNDP; ELit 0; ELit 0].
Definition lib_chk (cs : acs) : bool :=
  (opt_eqb (kfind_word (kn cs) (ELit 0) 0x693a38 8) (ELit 0x693a38)
   && match kfind_word (kn cs) (ELit 0) 0x693a58 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x693ad0 8) (ELit 0x6b3dc8)
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x6b3d98 8) KE_AUXP
   && lin_nowrapR (kn cs) KE_AUXP
   && forallb (fun p => opt_eqb (kfind_word (kn cs) KE_AUX (fst p) 8) (snd p)) AUXV_EXP
   && existsb (kentry_eqb (KRange (EVar 8) 0 4294967294)) (kn cs))%bool.

(* [comment removed for export] *)
Definition XC9K : list (Z * nat * Z) :=
  [(7028080, 4%nat, 0); (7028115, 1%nat, 0); (7027552, 8%nat, 7027560); (7027544, 4%nat, 1); (7027568, 8%nat, 1277044); (7027824, 8%nat, 648332); (7027540, 4%nat, 0); (7027560, 8%nat, 0);
   (7029512, 8%nat, 0); (7027536, 1%nat, 0); (7028336, 4%nat, 0)].      (* [comment removed for export] *)
Definition xc_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) XC9K.

Lemma all_andb_split : forall a b, (a && b)%bool = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Section Entry.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation A0 := (as0_A0 EXTRA cs E).
  #[local] Notation Hx := (ahid A0 model).
  #[local] Notation MV := (mrestrict Hx FULL).
  #[local] Notation HIDK := (hid ASAN0 argH E cs model).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  Lemma drv_chk_parts :
    pc cs = 0xaea2c
    /\ (forall r e, In (r, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 r) = e)
    /\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
    /\ lin_nowrapR (kn cs) KE_ENVP = true /\ lin_nowrapR (kn cs) KE_P0 = true /\ lin_nowrapR (kn cs) KE_P1X = true
    /\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar 1) /\ kfind_word (kn cs) e_sp0 8 8 = Some KE_P0
    /\ kfind_word (kn cs) e_sp0 16 8 = Some KE_P1
    /\ kfind_wr (kn cs) e_sp0 (-8388608) = Some (ELit 8388608)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x6b3b40 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x693af0 8 = Some v)
    /\ (forall lo hi, In (lo, hi) DRV_IMG -> img_cover (kn cs) lo hi = true)
    /\ a_fd cs = FdStd.
  Proof.
    pose proof CHKD as H. unfold drv_chk in H.
    apply andb_prop in H as [H Cfd]. apply andb_prop in H as [H Cimg]. apply andb_prop in H as [H Cg]. apply andb_prop in H as [H Cwr]. apply andb_prop in H as [H Cp1].
    apply andb_prop in H as [H Cp0]. apply andb_prop in H as [H Cac]. apply andb_prop in H as [H L6]. apply andb_prop in H as [H L5].
    apply andb_prop in H as [H L4]. apply andb_prop in H as [H L3]. apply andb_prop in H as [H L2]. apply andb_prop in H as [H L1].
    apply andb_prop in H as [H Creg].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply Z.eqb_eq; exact H|].
    split; [intros r e Hin; pose proof (proj1 (forallb_forall _ _) Creg (r, e) Hin) as Hb; cbn [fst snd] in Hb; apply expr_eqb_eq; exact Hb|].
    do 6 (split; [assumption|]).
    do 4 (split; [apply OE; assumption|]).
    split.
    - destruct (kfind_word (kn cs) (ELit 0) 0x6b3b40 8) as [v|]; [|discriminate]. exists v. split; [reflexivity | apply OE; assumption].
    - split; [intros lo hi Hin; exact (proj1 (forallb_forall _ _) Cimg (lo, hi) Hin)|].
      destruct (a_fd cs); first [reflexivity | discriminate].
  Qed.

  (* [comment removed for export] *)
  Ltac LINEQ e Hn H :=
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  Lemma ent_vals : VZ E 1 = Z.of_nat (length argv) /\ VZ E 2 = Z.of_nat (length envp) /\ VZ E 3 = Z.of_nat (length (nth 0 argv []))
                   /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof.
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & U1 & U2 & U3 & _).
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    auto.
  Qed.

  Lemma sp0_val : uE E e_sp0 = usp.
  Proof.
    destruct drv_chk_parts as (_ & _ & L1 & _). destruct ent_vals as (_ & _ & _ & U0).
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L1 H. rewrite <- Es in H. lia.
  Qed.

  Lemma sp_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma ent_binv : BInv ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
                        (uE E e_sp0 - 8388608) (as0_BASE EXTRA cs) BUDGET [] A0 FULL model.
  Proof. exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf cs CHK0 BUD_le GAP E R FULL model HC). Qed.

  (* [comment removed for export] *)
  Lemma hx_le : forall a : word, Hx a = true -> HIDK a = true.
  Proof.
    intros a Ha. destruct (HIDK a) eqn:Hh; [reflexivity|]. exfalso.
    unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl Hn]. apply negb_true_iff in Hn.
    pose proof (lazy_cover_cs ASEGS0 ASAN0 AsanInitK.LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                  asan0_hull_ok SINV argH fs 0%nat E cs R FULL model HC a Hl Hh) as Hc.
    unfold as0_A0, A0_of in Hn. rewrite (page_allowedb_app_l _ _ _ Hc) in Hn. discriminate.
  Qed.

  Lemma avoid_x : forall a n, range_avoids HIDK a n -> range_avoids Hx a n.
  Proof. intros a n Hr k Hk. destruct (Hx (woff a k)) eqn:Hh; [|reflexivity]. pose proof (hx_le _ Hh) as Hc. rewrite (Hr k Hk) in Hc. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma ent_lz : H_off_segments ASEGS0 Hx /\ lazy_cover Hx (m_vm_lazy model) A0 /\ A_wf A0 /\ MInv A0 model /\ m_halted model = None.
  Proof.
    pose proof ent_binv as B.
    split; [intros a Ha; unfold ahid, mkH in Ha; apply andb_prop in Ha as [Hl _]; exact (proj2 (bi_lazy_in _ _ _ _ _ _ _ _ _ _ _ B a Hl))|].
    split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
    split; [exact (bi_awf _ _ _ _ _ _ _ _ _ _ _ B)|].
    split; [exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B) | exact (bi_halt _ _ _ _ _ _ _ _ _ _ _ B)].
  Qed.

  Lemma ent_model : m_fds model = fds_std /\ m_fs model = fs.
  Proof.
    split; [|exact (hb_fs ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC)].
    apply (hb_fds_std ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC).
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 drv_chk_parts)))))))))))))).
  Qed.

  (* [comment removed for export] *)
  Variables a0s path : list byte.
  Hypothesis Hargv : argv = [a0s; path].
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Lemma ent_vals2 : VZ E 1 = 2 /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. destruct ent_vals as (U1 & U2 & U3 & U0). rewrite Hargv in U1, U3. cbn [length nth] in U1, U3. auto. Qed.

  Lemma word_of_u : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
  Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Lemma val_spk48 : edenot E (KE_SPK (-48)) = Z_to_bv 64 (usp - 48).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & L2 & _). destruct ent_vals2 as (_ & _ & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_spk8 : edenot E (KE_SPK 8) = Z_to_bv 64 (usp + 8).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & L3 & _). destruct ent_vals2 as (_ & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_envp : edenot E KE_ENVP = Z_to_bv 64 (usp + 32).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & L4 & _). destruct ent_vals2 as (U1 & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_ENVP)) as x eqn:Ex. LINEQ KE_ENVP L4 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_p0 : edenot E KE_P0 = Z_to_bv 64 (usp + 8 * envc + 200).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & L5 & _). destruct ent_vals2 as (U1 & U2 & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_P0)) as x eqn:Ex. LINEQ KE_P0 L5 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_p1x : edenot E KE_P1X = Z_to_bv 64 (usp + 8 * envc + L0 + 201).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & L6 & _). destruct ent_vals2 as (U1 & U2 & U3 & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_P1X)) as x eqn:Ex. LINEQ KE_P1X L6 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_argc : edenot E (EVar 1) = Z_to_bv 64 2.
  Proof. destruct ent_vals2 as (U1 & _). apply word_of_u. exact U1. Qed.
  Lemma val_p1 : edenot E KE_P1 = Z_to_bv 64 (usp + 8 * envc + L0 + 201).
  Proof.
    unfold KE_P1. cbn [edenot]. fold (edenot E KE_P1X). rewrite val_p1x. apply word_of_u.
    rewrite u_mul64, u_sltu64. destruct ent_vals2 as (U1 & _). unfold VZ in U1. rewrite U1.
    rewrite (u64_lit 1) by lia. change (1 <? 2) with true. cbv iota.
    pose proof sp_rng. pose proof (Zle_0_nat (length envp)). pose proof (Zle_0_nat (length a0s)).
    assert (Hb : 0 <= usp + 8 * envc + L0 + 201 < 2 ^ 64).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). rewrite Hargv in Hfa. inversion Hfa as [|x l Hx _]; subst. lia. }
    rewrite u64_lit by exact Hb. rewrite Z.mul_1_l. apply Z.mod_small. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma ent_reg : forall r e, In (r, e) DRV_REGS -> getr R (Z_to_bv 5 r) = edenot E e.
  Proof.
    intros r e Hin. destruct drv_chk_parts as (_ & HRg & _). rewrite <- (HRg r e Hin).
    exact (hb_reg ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC).
  Qed.

  Definition DRV_REGV : list (Z * Z) :=
    [(1, 0x137500); (2, usp - 48); (3, 0x10800); (4, 0x693b00); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xaea2c); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Theorem ent_regs : forall r v, In (r, v) DRV_REGV -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Proof.
    intros r v Hin. unfold DRV_REGV in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 1 (ELit 0x137500)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 4 (ELit 0x693b00)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 18 (ELit 0xaea2c)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 19 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma adr_sp : forall off n, flat E (SA e_sp0 off) n -> adenot E (SA e_sp0 off) = Z_to_bv 64 (usp + off).
  Proof. intros off n Hf. rewrite (hb_adenot E _ _ Hf), hb_estart. fold (uE E e_sp0). rewrite sp0_val. reflexivity. Qed.

  Lemma ent_stkword : forall off v, kfind_word (kn cs) e_sp0 off 8 = Some v ->
    rdn ASEGS0 MV (Z_to_bv 64 (usp + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof.
    intros off v Hk.
    destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 off 8 v HC Hk)
      as (_ & Hf & Hr & Hav).
    rewrite (adr_sp off _ Hf) in Hr, Hav. rewrite (rdn_mrestrict_eq ASEGS0 Hx 8 FULL _ (avoid_x _ _ Hav)). exact Hr.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_stack_words :
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 200)))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + L0 + 201))).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    pose proof (ent_stkword 0 _ K0) as H0. pose proof (ent_stkword 8 _ K8) as H8. pose proof (ent_stkword 16 _ K16) as H16.
    rewrite Z.add_0_r, val_argc in H0. rewrite val_p0 in H8. rewrite val_p1 in H16. auto.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_window : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok ASEGS0 MV (Z_to_bv 64 (usp - 8388608 + d)) m = true.
  Proof.
    intros d m Hd Hm. destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KW & _).
    destruct (hb_wr_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 (-8388608) _ HC KW)
      as (Hf & HW).
    assert (EL : elenZ E (ELit 8388608) = 8388608) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    destruct (HW d m Hd ltac:(rewrite EL; exact Hm)) as (Hs & Hav).
    rewrite hb_estart in Hs, Hav. fold (uE E e_sp0) in Hs, Hav. rewrite sp0_val in Hs, Hav.
    replace (usp + -8388608 + d) with (usp - 8388608 + d) in Hs, Hav by ring.
    rewrite (store_ok_mrestrict_eq ASEGS0 Hx m FULL _ (avoid_x _ _ Hav)). exact Hs.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_guard : exists can : word,
    rdn ASEGS0 MV (Z_to_bv 64 0x6b3b40) 8 = Some (word_to_le_bytes 8 can) /\ rdn ASEGS0 MV (Z_to_bv 64 0x693af0) 8 = Some (word_to_le_bytes 8 can).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v & G1 & G2) & _).
    exists (edenot E v).
    assert (HW : forall a, kfind_word (kn cs) (ELit 0) a 8 = Some v -> 0 <= a < 2 ^ 63 ->
                 rdn ASEGS0 MV (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E v))).
    { intros a Hk Ha.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model (ELit 0) a 8 v HC Hk)
        as (_ & Hf & Hr & Hav).
      rewrite (hb_adenot E _ _ Hf), hb_estart in Hr, Hav. cbn [edenot] in Hr, Hav. rewrite (u64_lit 0) in Hr, Hav by lia. rewrite Z.add_0_l in Hr, Hav.
      rewrite (rdn_mrestrict_eq ASEGS0 Hx 8 FULL _ (avoid_x _ _ Hav)). exact Hr. }
    split; apply HW; first [assumption | lia].
  Qed.

  (* [comment removed for export] *)
  Theorem ent_img : forall lo hi i, In (lo, hi) DRV_IMG -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Proof.
    intros lo hi i Hin Hi.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HI & _).
    pose proof (HI lo hi Hin) as Hc. unfold img_cover in Hc. apply existsb_exists in Hc as (K & HK & Hb).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    assert (Hh : in_hull ASAN0 i = true).
    { unfold DRV_IMG in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]]; injection Hin as <- <-; unfold in_hull; cbn [img_lo img_hi ASAN0];
        apply andb_true_intro; split; first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    pose proof (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC HK i ltac:(lia) Hh) as Hn.
    unfold mrestrict. destruct (Hx (Z_to_bv 64 i)); [reflexivity | exact Hn].
  Qed.

  (* [comment removed for export] *)
  Lemma vis_high : forall x : word, usp - 8388608 <= bv_unsigned x -> Hx x = false.
  Proof.
    intros x Hxx. destruct (Hx x) eqn:Hh; [exfalso | reflexivity].
    unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
    destruct (bi_lazy_in _ _ _ _ _ _ _ _ _ _ _ ent_binv x Hl) as [Hc _].
    unfold BackingAlgebra.covered in Hc. apply existsb_exists in Hc as (q & Hq & Hin).
    unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S in Hin. apply andb_prop in Hin as [I1 I2].
    apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    destruct (hl_maps_pos ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model q HC Hq) as [_ Hle].
    rewrite sp0_val in Hle. lia.
  Qed.

  Lemma wsb_eq : 8 * Wsb APH0 sp rdraw argv envp uid hw
                 = Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 - (8 * 2 + 8 * envc + 184).
  Proof.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [_ Hm]. unfold Wsb. rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *.
    set (n := Z.of_nat (length (build_stack_bytes APH0 sp [a0s; path] envp uid hw rdraw)) - 16 - (8 * 2 + 8 * envc + 184)) in *.
    pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite Hm in D. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_strblock : forall x : word,
    usp + 8 * envc + 200 <= bv_unsigned x < usp + Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 ->
    MV x = wrap_mem APH0 sp argv envp uid hw rdraw x.
  Proof.
    intros x Hxr. pose proof sp_rng as SR. unfold mrestrict. rewrite (vis_high x ltac:(lia)).
    apply (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC).
    rewrite hbi_argH. rewrite sp0_val. pose proof wsb_eq as W. rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.   (* [comment removed for export] *)
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str : forall k, (k < 2)%nat ->
    rdn ASEGS0 MV (cat_argv_ptr sp argv envp k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr sp argv envp k) = usp + 8 * envc + 200 + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    assert (CS : Z.of_nat (cat_struct_size argv envp) = 8 * envc + 200).
    { unfold cat_struct_size, auxv_size. rewrite Hargv. cbn [length]. lia. }
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    pose proof (bsb_nw APH0 sp argv envp uid hw rdraw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    split; [|rewrite Hu; lia].
    rewrite <- (read_argv_cstr_k APH0 ASEGS0 sp argv envp k uid hw rdraw Hk' Hnw).
    rewrite <- (rdn_wmem_stack ASEGS0 APH0 sp argv envp uid hw rdraw) by lia.
    apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply ent_strblock. lia.
  Qed.
  (* [comment removed for export] *)
  Hypothesis CHKS : stk_chk cs = true.

  Lemma stk_chk_parts :
    (forall off, In off AUX_OFFS -> exists v, kfind_word (kn cs) KE_AUX off 8 = Some v)
    /\ lin_nowrapR (kn cs) KE_AUX = true /\ lin_nowrapR (kn cs) KE_RND = true
    /\ exists i, kfind_blob16 (kn cs) KE_RND 184 = Some i.
  Proof.
    pose proof CHKS as H. unfold stk_chk in H.
    apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    split.
    { intros off Hin. pose proof (proj1 (forallb_forall _ _) C1 off Hin) as Hb. cbv beta in Hb.
      destruct (kfind_word (kn cs) KE_AUX off 8) as [v|]; [exists v; reflexivity | discriminate]. }
    split; [exact C2|]. split; [exact C3|].
    destruct (kfind_blob16 (kn cs) KE_RND 184) as [i|]; [exists i; reflexivity | discriminate].
  Qed.

  #[local] Notation SIMGx := (entry_stack_image APH0 sp argv envp uid hw rdraw).
  #[local] Notation LBx := (Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw))).

  Lemma simg_top : usp + Z.of_nat (length SIMGx) <= 2 ^ 47 /\ LBx <= Z.of_nat (length SIMGx)
                   /\ (usp + Z.of_nat (length SIMGx)) mod 4096 = 0.
  Proof.
    pose proof (entry_stack_image_top APH0 sp argv envp uid hw rdraw) as T.
    pose proof (entry_page_top_within_window APH0 sp argv envp uid hw rdraw Hfit) as W. rewrite <- T in W. unfold sp_window_hi in W.
    split; [lia|]. split.
    - unfold entry_stack_image. cbv zeta. rewrite length_app. lia.
    - rewrite T. unfold entry_page_top, page_round_up_Z, page_size. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str_hi : forall k, (k < 2)%nat ->
    bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1 + 16 <= 2 ^ 47.
  Proof.
    intros k Hk. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct simg_top as (T1 & T2 & _). rewrite Hu. lia.
  Qed.

  Lemma argH_defined : forall x : word, usp <= bv_unsigned x < usp + Z.of_nat (length SIMGx) -> argH E x = true -> FULL x <> None.
  Proof.
    intros x Hx Ha.
    rewrite (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC x Ha).
    rewrite wrap_above_sp by lia. unfold stack_to_mem.
    replace (usp <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned x - usp <? Z.of_nat (length SIMGx)) with true by (symmetry; apply Z.ltb_lt; lia).
    apply nth_error_Some. lia.
  Qed.

  Lemma mr_defined : forall (x : word) b, Mr ASAN0 argH E cs model FULL x = Some b -> FULL x <> None.
  Proof. intros x b H. rewrite (hb_mr_some ASAN0 argH E cs model FULL x b H). discriminate. Qed.

  Theorem ent_stack_defined : forall i, 0 <= i < Z.of_nat (length SIMGx) -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros i Hi. pose proof sp_rng as SR. destruct simg_top as (T1 & T2 & _).
    destruct stk_chk_parts as (CA & LA & LR & (bi & CB)).
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0).
    pose proof wsb_eq as WE. assert (AC : Z.of_nat (length argv) = 2) by (rewrite Hargv; reflexivity).
    assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
    (* [comment removed for export] *)
    assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v -> lin_nowrapR (kn cs) b = true ->
                 (flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
    { intros b off v d Hk Hl Hst Hd.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
      apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
      - rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
      - rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    destruct (Z_lt_le_dec i 24) as [C1|C1].
    { (* [comment removed for export] *)
      assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
        by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite sp0_val; reflexivity).
      destruct drv_chk_parts as (_ & _ & L1 & _).
      destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
      destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
    destruct (Z_lt_le_dec i (8 * envc + 40)) as [C2|C2].
    { apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX, AC.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. left.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i (8 * envc + 200)) as [C3|C3].
    { (* [comment removed for export] *)
      assert (UA : uE E KE_AUX = usp + 16 + 8 * envc).
      { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
      assert (ST : forall off, flat E (SA KE_AUX off) 8 -> estart E (SA KE_AUX off) = usp + (16 + 8 * envc + off))
        by (intros off _; rewrite hb_estart; fold (uE E KE_AUX); rewrite UA; ring).
      set (k := (i - (16 + 8 * envc)) / 8).
      assert (Hk : i - (16 + 8 * envc) = 8 * k + (i - (16 + 8 * envc)) mod 8) by (apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound (i - (16 + 8 * envc)) 8 ltac:(lia)) as Hm.
      assert (Hin : In (8 * k) AUX_OFFS).
      { assert (Hk3 : 3 <= k < 23) by lia. unfold AUX_OFFS.
        assert (Hc : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
                     \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22) by lia.
        repeat (destruct Hc as [->|Hc]; [cbn [In]; tauto|]). subst k. rewrite Hc. cbn [In]. tauto. }
      destruct (CA _ Hin) as (v & Hv).
      apply (KW KE_AUX (8 * k) v (16 + 8 * envc + 8 * k) Hv LA (ST (8 * k))). lia. }
    destruct (Z_lt_le_dec i (LBx - 16)) as [C4|C4].
    { apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX, AC.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i LBx) as [C5|C5].
    { (* [comment removed for export] *)
      assert (UR : uE E KE_RND = usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
      { unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
      pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hf & _ & Hb).
      assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
      rewrite EL in Hb. rewrite hb_estart in Hb. fold (uE E KE_RND) in Hb. rewrite UR in Hb.
      specialize (Hb (i - (LBx - 16)) ltac:(lia)).
      replace (usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw + 184 + (i - (LBx - 16))) with (usp + i) in Hb by lia.
      exact (mr_defined _ _ Hb). }
    apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Corollary ent_stack_defined_top : forall top, top mod 4096 = 0 -> top <= usp + 4096 ->
    forall i, 0 <= i < top - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros top Hm Hle i Hi. apply ent_stack_defined. destruct simg_top as (T1 & T2 & T3).
    pose proof (bsb_ge APH0 sp rdraw argv envp uid hw) as [G _].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str_defined : forall k, (k < 2)%nat ->
    forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 16 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp argv envp k) + i)) <> None.
  Proof.
    intros k Hk i Hi. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct simg_top as (_ & T2 & _).
    set (q := bv_unsigned (cat_argv_ptr sp argv envp k)) in *.
    replace (q + i) with (usp + (q - usp + i)) by ring.
    apply ent_stack_defined. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CHKLIB : lib_chk cs = true.

  Lemma lib_chk_parts :
    kfind_word (kn cs) (ELit 0) 0x693a38 8 = Some (ELit 0x693a38)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x693a58 4 = Some v /\ existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) = true)
    /\ kfind_word (kn cs) (ELit 0) 0x693ad0 8 = Some (ELit 0x6b3dc8)
    /\ kfind_word (kn cs) (ELit 0) 0x6b3d98 8 = Some KE_AUXP
    /\ lin_nowrapR (kn cs) KE_AUXP = true
    /\ (forall off e, In (off, e) AUXV_EXP -> kfind_word (kn cs) KE_AUX off 8 = Some e)
    /\ existsb (kentry_eqb (KRange (EVar 8) 0 4294967294)) (kn cs) = true.
  Proof.
    pose proof CHKLIB as H. unfold lib_chk in H.
    apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply OE; exact C1|]. split.
    { destruct (kfind_word (kn cs) (ELit 0) 0x693a58 4) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact C2]. }
    split; [apply OE; exact C3|]. split; [apply OE; exact C4|]. split; [exact C5|]. split; [|exact C7].
    intros off e Hin. apply OE. exact (proj1 (forallb_forall _ _) C6 (off, e) Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma ent_litcell : forall a (w : nat) v, kfind_word (kn cs) (ELit 0) a w = Some v -> 0 <= a < 2 ^ 63 ->
    rdn ASEGS0 MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
  Proof.
    intros a w v Hk Ha.
    destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model (ELit 0) a w v HC Hk)
      as (_ & Hf & Hr & Hav).
    rewrite (hb_adenot E _ _ Hf), hb_estart in Hr, Hav. cbn [edenot] in Hr, Hav. rewrite (u64_lit 0) in Hr, Hav by lia. rewrite Z.add_0_l in Hr, Hav.
    rewrite (rdn_mrestrict_eq ASEGS0 Hx w FULL _ (avoid_x _ _ Hav)). exact Hr.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_xcells : xc_chk cs = true ->
    Forall (fun c : Z * nat * Z => rdn ASEGS0 MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9K.
  Proof.
    intros CHKX. unfold xc_chk in CHKX. rewrite forallb_forall in CHKX. apply Forall_forall. intros c Hin.
    pose proof (art_lit1 sp brk0 rdraw argv envp uid hw fs Hsp Hva E cs R FULL model c HC (CHKX c Hin)) as CELL. unfold ArtMem.cell in CELL.
    destruct ent_lz as (HOFF & _).
    rewrite rdn_mrestrict_eq; [exact CELL|].
    intros k Hk. destruct (Hx (woff (Z_to_bv 64 (fst (fst c))) k)) eqn:Hh; [exfalso | reflexivity].
    pose proof (HOFF _ Hh) as X. clear - Hin Hk X. unfold XC9K in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst c; cbn [fst snd] in *; do 8 (destruct k as [|k]; [exfalso; lazymatch type of X with find_segment ?S ?a ?n = None =>
        assert (Hs : match find_segment S a n with Some _ => true | None => false end = true) by (vm_compute; reflexivity); rewrite X in Hs; discriminate Hs end|]); lia|]).   (* [comment removed for export] *) destruct Hin.
  Qed.

  Lemma val_auxp : edenot E KE_AUXP = Z_to_bv 64 (usp + 8 * envc + 40).
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & LN & _). destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E KE_AUXP)) as x eqn:Ex. LINEQ KE_AUXP LN H0. rewrite <- Ex in H0. lia.
  Qed.

  Theorem ent_libcells : exists tid : word,
    1 <= bv_unsigned tid <= 4194303
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x693a38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x693a38))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x693a58) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x693ad0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6b3dc8))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x6b3d98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40))).
  Proof.
    destruct lib_chk_parts as (K1 & (v & K2 & K2r) & K3 & K4 & _).
    exists (edenot E v).
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC K2r) as RG. cbn [kentry_ok] in RG.
    split; [exact RG|].
    split; [exact (ent_litcell _ _ _ K1 ltac:(lia))|].
    split; [exact (ent_litcell _ _ _ K2 ltac:(lia))|].
    split; [exact (ent_litcell _ _ _ K3 ltac:(lia))|].
    pose proof (ent_litcell _ _ _ K4 ltac:(lia)) as X. rewrite val_auxp in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Definition auxv_list (uidz rnd hwz : Z) : list Z := [3; 0x10040; 4; 56; 5; 11; 16; hwz; 6; 4096; 11; uidz; 12; uidz; 23; 0; 25; rnd; 0; 0].
  Theorem ent_auxv : exists uidz rnd hwz : Z,
    (forall j, (j < 20)%nat ->
       rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * envc + 40 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j (auxv_list uidz rnd hwz) 0))))
    /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & _ & KA & KU).
    destruct stk_chk_parts as (_ & LA & LR & (bi & CB)).
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0). pose proof sp_rng as SR. pose proof wsb_eq as WE.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [BG _].
    assert (UA : uE E KE_AUX = usp + 16 + 8 * envc).
    { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
    assert (UR : uE E KE_RND = usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
    { unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hfb & _ & _).
    assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    rewrite EL in Hfb. destruct Hfb as (FB1 & FB2 & _ & FB4). rewrite hb_estart in FB1, FB2, FB4. fold (uE E KE_RND) in FB1, FB2, FB4.
    assert (AC : Z.of_nat (length argv) = 2) by (rewrite Hargv; reflexivity). rewrite AC in BG. pose proof (Zle_0_nat (length envp)) as EN.
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC KU) as RGU. cbn [kentry_ok edenot] in RGU.
    set (rnd := uE E KE_RND + 184).
    assert (VR : edenot E KE_RNDP = Z_to_bv 64 rnd).
    { unfold KE_RNDP. cbn [edenot]. fold (edenot E KE_RND). rewrite alu_add. unfold v_add. apply bv_eq.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold (uE E KE_RND). rewrite (Z.mod_small 184) by lia. reflexivity. }
    exists (bv_unsigned (ev E 8)), rnd, (bv_unsigned (ev E 9)).
    split; [|split; [lia|]; split; [pose proof (u64_range (ev E 9)); lia|]; split; [unfold rnd; rewrite UR; lia | unfold rnd; lia]].
    (* [comment removed for export] *)
    assert (CELL : forall off e, In (off, e) AUXV_EXP ->
               rdn ASEGS0 FULL (Z_to_bv 64 (usp + 16 + 8 * envc + off)) 8 = Some (word_to_le_bytes 8 (edenot E e))).
    { intros off e Hin.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model KE_AUX off 8 e HC (KA off e Hin))
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), hb_estart in Hr. fold (uE E KE_AUX) in Hr. rewrite UA in Hr. exact Hr. }
    intros j Hj.
    assert (EV : forall n, edenot E (EVar n) = Z_to_bv 64 (bv_unsigned (ev E n))) by (intros n; cbn [edenot]; symmetry; apply Z_to_bv_bv_unsigned).
    do 20 (destruct j as [|j];
           [ match goal with |- rdn _ _ (Z_to_bv 64 (_ + 8 * Z.of_nat ?k)) 8 = _ =>
               let o := eval cbv in (24 + 8 * Z.of_nat k) in
               let e := eval cbv in (nth k (map snd AUXV_EXP) (ELit 0)) in
               pose proof (CELL o e ltac:(unfold AUXV_EXP, AUX_OFFS, KE_RNDP; cbn [combine In]; tauto)) as X end;
             cbn [nth auxv_list]; rewrite ?EV, ?VR in X; cbn [edenot] in X;
             match type of X with rdn _ _ (Z_to_bv 64 ?a) _ = _ => match goal with |- rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace b with a by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end end;
             exact X |]).
    lia.
  Qed.
End Entry.

End Na0DrvEntryK.
Module Na0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0MainTableK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition HSA (h : nat) : acs := match h with O => HS_0 | _ => HS_1 end.
Lemma HSA_some : forall h, (h < 2)%nat -> HS_as0 h = Some (HSA h).
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.
Lemma HSA_none : forall h, (2 <= h)%nat -> HS_as0 h = None.
Proof. intros [|[|h]] H; [lia|lia|reflexivity]. Qed.
Lemma HSA_nofog : forall h, (h < 2)%nat -> no_fog (a_maps (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_mapslin : forall h, (h < 2)%nat -> amaps_lin (kn (HSA h)) (a_maps (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_vislin : forall h, (h < 2)%nat -> vis_lin (kn (HSA h)) (a_vis (HSA h) ++ a_ghost (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_brklin : forall h, (h < 2)%nat -> lin_nowrapR (kn (HSA h)) (a_brk (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_fd : forall h, (h < 2)%nat -> a_fd (HSA h) = FdStd.
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.

Lemma as0_chk_0 : as0_chk HS_0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_1 : as0_chk HS_1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_HSA : forall h, (h < 2)%nat -> as0_chk (HSA h) = true.
Proof. intros [|[|h]] H; [exact as0_chk_0 | exact as0_chk_1 | lia]. Qed.

(* [comment removed for export] *)
Lemma HSA_numbers : forall h, (h < 2)%nat ->
  a_totsz (HSA h) <= 17729665331200 /\ a_eager (HSA h) <= 16515072 /\ a_abytes (HSA h) <= 2461477888 /\ length (a_maps (HSA h)) = 17%nat.
Proof. intros [|[|h]] H; [vm_compute; repeat split; discriminate || reflexivity | vm_compute; repeat split; discriminate || reflexivity | lia]. Qed.

Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461477888 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665331200 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_inst_bud : forall h, (h < 2)%nat -> a_eager (HSA h) + a_abytes (HSA h) + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Proof. intros h Hh. destruct (HSA_numbers h Hh) as (_ & N2 & N3 & _). lia. Qed.
  Lemma as0_inst_gap : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + LENMAX + (a_totsz (HSA h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps (HSA h))) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros h Hh. destruct (HSA_numbers h Hh) as (N1 & _ & _ & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add].
    change (Z.of_nat 21) with 21. assert (0 <= LENMAX + 4095) by lia. nia.
  Qed.

  Theorem as0_handoff_static : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros h Hh E R FULL model HC.
    eapply as0_bridge_static; try eassumption.
    - exact (as0_chk_HSA h Hh).
    - exact (as0_inst_gap h Hh).
  Qed.

  Theorem as0_handoff_binv : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) (as0_BASE EXTRA (HSA h)) BUDGET [] (as0_A0 EXTRA (HSA h) E) FULL model.
  Proof.
    intros h Hh E R FULL model HC.
    eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := KMAX); try eassumption.
    - exact (as0_chk_HSA h Hh).
    - exact (as0_inst_bud h Hh).
    - exact (as0_inst_gap h Hh).
  Qed.
End Inst.

End Na0HandoffInstK.
Module Na0ResK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanNodesExtraDefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x57f58, 102%nat); (0x58250, 85%nat); (0x5a520, 395%nat); (0x5b730, 73%nat); (0x5edc0, 55%nat); (0x5f378, 62%nat); (0x63ff0, 50%nat); (0x647b4, 16%nat); (0x653f8, 980%nat); (0x66de0, 352%nat); (0x67474, 12%nat); (0x67628, 251%nat); (0x681c8, 24%nat); (0x6891c, 176%nat); (0x68dfc, 17%nat); (0x69608, 15%nat); (0x6a174, 108%nat); (0x71fb4, 35%nat); (0x749c0, 85%nat); (0x758b4, 6626%nat); (0x7e58c, 91%nat); (0x7eba8, 7%nat); (0x7f600, 134%nat); (0x7fdb0, 103%nat); (0x803a0, 25%nat); (0x805c8, 91%nat); (0x80fb4, 5%nat); (0x81a34, 245%nat); (0x81f54, 31%nat); (0x823e0, 109%nat); (0x82e08, 145%nat); (0x870f4, 10%nat); (0x8788c, 29%nat); (0x87d50, 190%nat); (0x88270, 57%nat); (0x884e0, 45%nat); (0x88848, 178%nat); (0x88cfc, 128%nat); (0x899d0, 18%nat); (0x89cb0, 35%nat); (0x8a268, 7%nat); (0x8a3f4, 100%nat); (0x8a804, 726%nat); (0x8c3e0, 151%nat); (0x8cbc4, 127%nat); (0x8e3c0, 7%nat); (0x8ea64, 30%nat); (0x8ed20, 40%nat); (0x8f174, 23%nat); (0x8f484, 46%nat); (0x8f668, 14%nat); (0x8fcc0, 93%nat); (0x9016c, 1206%nat); (0x918e8, 342%nat); (0x91fc4, 44%nat); (0x92304, 144%nat); (0x92738, 144%nat); (0x92b7c, 18%nat); (0x92e64, 25%nat); (0x939b0, 76%nat); (0x93de4, 27%nat); (0x94008, 6%nat); (0x9425c, 130%nat); (0x947a4, 136%nat); (0x94f48, 21%nat); (0x95098, 14%nat); (0x9570c, 7%nat); (0x97308, 36%nat); (0x97544, 91%nat); (0x977f0, 19%nat); (0x97e64, 272%nat); (0x984d0, 317%nat); (0x992ac, 253%nat); (0x99e8c, 26%nat); (0x9a098, 7%nat); (0x9a7b4, 37%nat); (0x9ac00, 123%nat); (0x9af98, 36%nat); (0x9b20c, 152%nat); (0x9b840, 5%nat); (0x9bb08, 118%nat); (0x9c060, 64%nat); (0x9c2d8, 74%nat); (0x9c9ec, 46%nat); (0x9cc38, 8%nat); (0x9e440, 21%nat); (0x9e8e8, 147%nat); (0x9f3f4, 42%nat); (0xa0bfc, 22%nat); (0xa0ee4, 173%nat); (0xa1678, 203%nat); (0xa1ecc, 74%nat); (0xa8968, 265%nat); (0xa904c, 43%nat); (0xab820, 7%nat); (0xae780, 174%nat); (0xd5630, 18%nat); (0x136b04, 66%nat); (0x136d0c, 7%nat); (0x1371d8, 455%nat); (0x137ba8, 53%nat); (0x138018, 123%nat); (0x13a044, 5%nat); (0x13a6fc, 431%nat); (0x13af24, 162%nat); (0x13b2c0, 290%nat); (0x13de18, 81%nat); (0x148d60, 6%nat); (0x148e74, 32%nat); (0x149120, 83%nat); (0x149a20, 7%nat); (0x149c18, 135%nat); (0x14b98c, 11%nat); (0x14baf8, 57%nat); (0x14c544, 159%nat); (0x14cde0, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.

End Na0ResK.
Module Na0BssZeroK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.   (* [comment removed for export] *)
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.

Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Definition DEP_LO : Z := 0x241958.
Definition DEP_HI : Z := 0x641958.
Lemma as0_dep_zscan : zscanN Asan_seg_bytes_003 64 0xe9958 0x400000 = true.
Proof. apply (FxHexScan.FXH.zscan_ok zscanN byte_zero (fun _ _ _ _ => eq_refl) (fun _ _ H => H)); [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.

Open Scope Z_scope.
Lemma as0_dep_rom_zero : forall a, DEP_LO <= a < DEP_HI -> seg_rom ASEGS0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. unfold DEP_LO, DEP_HI in Ha. unfold seg_rom, memory_read. rewrite u64_lit by lia.
  rewrite asan0_segs_eq. cbn [find_segment].
  cbn [seg_base seg_size Asan_segment_000 Asan_segment_001 Asan_segment_002 Asan_segment_003].
  replace (Z.leb (Z.of_N 65536) a && Z.leb (a + Z.of_N 1) (Z.of_N 65536 + Z.of_N 290816))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 356352) a && Z.leb (a + Z.of_N 1) (Z.of_N 356352 + Z.of_N 1019904))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 1376256) a && Z.leb (a + Z.of_N 1) (Z.of_N 1376256 + Z.of_N 32768))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 1409024) a && Z.leb (a + Z.of_N 1) (Z.of_N 1409024 + Z.of_N 5627904))%bool with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  assert (Hr : seg_readable Asan_segment_003 = true) by (vm_compute; reflexivity).
  rewrite Hr. cbn [seg_bytes seg_base Asan_segment_003].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
  rewrite asan0_len3.
  replace (Z.to_N (a - Z.of_N 1409024) <? 5627904)%N with true by (symmetry; apply N.ltb_lt; lia).
  pose proof (zscanN_sound _ _ _ _ as0_dep_zscan (Z.to_N (a - 0x241958)) ltac:(lia)) as Hz.
  replace (0xe9958 + Z.to_N (a - 0x241958))%N with (Z.to_N (a - Z.of_N 1409024)) in Hz by lia.
  rewrite Hz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma as0_dep_rdn_zero : forall (M : word -> option byte) n a, DEP_LO <= a -> a + Z.of_nat n <= DEP_HI ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M x = None) ->
  rdn ASEGS0 M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros M n. induction n as [|n IH]; intros a Ha Hb HM; [reflexivity|].
  assert (Hr : DEP_LO <= a < DEP_HI) by lia. unfold DEP_LO, DEP_HI in Ha, Hb.
  cbn [rdn repeat]. rewrite (HM (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite (as0_dep_rom_zero a Hr).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  - rewrite IH; [reflexivity | unfold DEP_LO; lia | unfold DEP_HI; lia | intros x Hx; apply HM; lia].
  - apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    change (bv_unsigned (1 : word)) with 1. rewrite Z.mod_small by lia. reflexivity.
Qed.

End Na0BssZeroK.

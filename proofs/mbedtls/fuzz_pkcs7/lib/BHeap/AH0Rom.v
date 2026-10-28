(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Import Uint63 PrimString PrimStringAxioms.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Rom () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "romwz1"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "romwz"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "romwzK"; "Stdlib.ZArith.BinInt.Z.mul"; "BSS_LO"; "BSS_HI"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"].


(* [comment removed for export] *)
Definition romwz1 (segs : list Segment) (z : Z) : bool :=
  match find_segment segs z 1 with
  | Some seg => (seg_readable seg && seg_writable seg &&
       match segment_byte_at (seg_bytes seg) (Z.to_N (z - Z.of_N (seg_base seg))) with
       | Some b => Z.eqb (bv_unsigned b) 0 | None => false end)%bool
  | None => false
  end.
(* [comment removed for export] *)
Fixpoint romwz (segs : list Segment) (z : Z) (n : nat) : bool :=
  match n with O => true | S n' => if romwz1 segs z then romwz segs (z + 1) n' else false end.
Fixpoint romwzK (segs : list Segment) (z : Z) (k : nat) : bool :=
  match k with O => true | S k' => if romwz segs z 1024 then romwzK segs (z + 1024) k' else false end.

Lemma romwz1_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Rom ()) "Psegs,(0.$1.)Pz,$2.P,(3.(4.=R1.)(5.R1.(6.+2.+40.)))P,(7.$8.(9.R3.R2.)$:.)(3.(7.(;.(<.&8.))(=.R4.L,(<.&40.)(>.(<.&8.))(?.&40.R3.))(10.(<.&8.)(?.&8.=)))(7.(;.(<.&8.))(11.R4.(?.&40.R3.))(10.(<.&8.)(?.&8.=))))")
(* [comment removed for export] *).
Proof.
  intros segs z Hz H. unfold romwz1 in H.
  assert (U : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; apply Z.mod_small; exact Hz).
  unfold wview, Lib.PropExec.seg_rom, memory_read. cbn beta iota. rewrite U. change (Z.of_N 1) with 1.
  destruct (find_segment segs z 1) as [seg|]; [|discriminate H].
  destruct (seg_readable seg); [|discriminate H]. destruct (seg_writable seg); [|discriminate H]. cbn [andb] in H.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (z - Z.of_N (seg_base seg)))) as [b|]; [|discriminate H].
  apply Z.eqb_eq in H. assert (Hb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite H; reflexivity). subst b. split; reflexivity.
Qed.

Lemma romwz_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Rom ()) "Psegs,(0.$1.)Pn,$12.Pz,$2.P,(7.$8.(13.R3.R1.R2.)$:.)P,(4.=R2.)P,(4.(14.R3.(15.R4.))(6.+2.+40.))Pi,$2.P,(3.(4.=R1.)(5.R1.(15.R6.)))(3.(7.(;.(<.&8.))(=.R8.L,(<.&40.)(>.(<.&8.))(?.&40.(14.R6.R2.)))(10.(<.&8.)(?.&8.=)))(7.(;.(<.&8.))(11.R8.(?.&40.(14.R6.R2.)))(10.(<.&8.)(?.&8.=))))")
(* [comment removed for export] *).
Proof.
  intros segs n. induction n as [|n IH]; intros z H Hz Hhi i Hi; [lia|].
  cbn [romwz] in H. destruct (romwz1 segs z) eqn:H1; [rename H into H2 | discriminate H].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. apply romwz1_sound; [lia | exact H1].
  - replace (z + i) with ((z + 1) + (i - 1)) by lia. apply (IH (z + 1) H2); lia.
Qed.

Lemma romwzK_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Rom ()) "Psegs,(0.$1.)Pk,$12.Pz,$2.P,(7.$8.(16.R3.R1.R2.)$:.)P,(4.=R2.)P,(4.(14.R3.(17.+400.(15.R4.)))(6.+2.+40.))Pi,$2.P,(3.(4.=R1.)(5.R1.(17.+400.(15.R6.))))(3.(7.(;.(<.&8.))(=.R8.L,(<.&40.)(>.(<.&8.))(?.&40.(14.R6.R2.)))(10.(<.&8.)(?.&8.=)))(7.(;.(<.&8.))(11.R8.(?.&40.(14.R6.R2.)))(10.(<.&8.)(?.&8.=))))")
(* [comment removed for export] *).
Proof.
  intros segs k. induction k as [|k IH]; intros z H Hz Hhi i Hi; [lia|].
  cbn [romwzK] in H. destruct (romwz segs z 1024) eqn:H1; [rename H into H2 | discriminate H].
  destruct (Z_lt_le_dec i 1024) as [Hlt|Hge].
  - apply (romwz_sound segs 1024 z H1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
  - replace (z + i) with ((z + 1024) + (i - 1024)) by lia. apply (IH (z + 1024) H2); lia.
Qed.

(* [comment removed for export] *)
Fixpoint seg_scan (segs : list Segment) (lo hi : Z) : option Segment :=
  match segs with
  | [] => None
  | s :: rest =>
      let b := Z.of_N (seg_base s) in let t := b + Z.of_N (seg_size s) in
      if (Z.leb b lo && Z.leb hi t)%bool then Some s
      else if (Z.leb t lo || Z.leb hi b)%bool then seg_scan rest lo hi
      else None
  end.
Definition zero_chars (ch : PrimString.string) (off len : Z) : bool :=
  match PrimString.compare (PrimString.sub ch (Uint63.of_Z off) (Uint63.of_Z len)) (PrimString.make (Uint63.of_Z len) 48%uint63) with
  | Eq => true | _ => false end.
Definition bss_check (segs : list Segment) (lo hi : Z) : bool :=
  match seg_scan segs lo hi with
  | Some s =>
      let b := Z.of_N (seg_base s) in
      (seg_readable s && seg_writable s && Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 63) &&
       match seg_bytes s with
       | [ch] => Z.leb (2 * (hi - b)) (Uint63.to_Z (PrimString.length ch)) && Z.leb (2 * (hi - b)) 16777211
                 && zero_chars ch (2 * (lo - b)) (2 * (hi - lo))
       | _ => false
       end)%bool
  | None => false
  end.

Lemma seg_scan_find : forall segs lo hi s z, seg_scan segs lo hi = Some s -> lo <= z -> z + 1 <= hi ->
  find_segment segs z 1 = Some s /\ Z.of_N (seg_base s) <= lo /\ hi <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  intros segs lo hi s z. induction segs as [|s0 rest IH]; intros H Hlo Hhi; [discriminate H|].
  cbn [seg_scan] in H. cbn [find_segment].
  destruct (Z.leb_spec0 (Z.of_N (seg_base s0)) lo) as [B|B]; destruct (Z.leb_spec0 hi (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) as [T|T]; cbn [andb] in H.
  - injection H as ->. replace (Z.of_N (seg_base s) <=? z) with true by (symmetry; apply Z.leb_le; lia).
    replace (z + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. split; [reflexivity| split; [exact B| exact T]].
  - destruct (Z.leb_spec0 (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo) as [D|D]; cbn [orb] in H.
    + replace (z + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite Bool.andb_false_r. apply IH; assumption.
    + destruct (Z.leb_spec0 hi (Z.of_N (seg_base s0))) as [D'|D']; [| discriminate H]. exfalso. lia.
  - destruct (Z.leb_spec0 (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo) as [D|D]; cbn [orb] in H; [exfalso; lia|].
    destruct (Z.leb_spec0 hi (Z.of_N (seg_base s0))) as [D'|D']; [| discriminate H].
    replace (Z.of_N (seg_base s0) <=? z) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply IH; assumption.
  - destruct (Z.leb_spec0 (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo) as [D|D]; cbn [orb] in H; [exfalso; lia|].
    destruct (Z.leb_spec0 hi (Z.of_N (seg_base s0))) as [D'|D']; [| discriminate H].
    replace (Z.of_N (seg_base s0) <=? z) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply IH; assumption.
Qed.

Lemma c63_compare_refl : forall c1 c2 : PrimString.char63, PrimInt63.compare c1 c2 = Eq <-> c1 = c2.
Proof.
  intros c1 c2. rewrite Uint63.compare_spec, Z.compare_eq_iff.
  split; [apply Uint63.to_Z_inj| intros ->; reflexivity].
Qed.
Lemma pstr_compare_eq : forall s1 s2, PrimString.compare s1 s2 = Eq -> PrimStringAxioms.to_list s1 = PrimStringAxioms.to_list s2.
Proof. intros s1 s2. rewrite PrimStringAxioms.compare_spec, (List.list_compare_refl _ c63_compare_refl). exact (fun H => H). Qed.
Lemma to_Z_of_Z_small : forall z, 0 <= z <= 16777215 -> Uint63.to_Z (Uint63.of_Z z) = z.
Proof. intros z Hz. rewrite Uint63.of_Z_spec. apply Z.mod_small. unfold Uint63.wB, Uint63.size. cbn. lia. Qed.
Lemma nth_firstn_lt : forall {A} (l : list A) n i d, (i < n)%nat -> List.nth i (List.firstn n l) d = List.nth i l d.
Proof. intros A l n i d H. rewrite List.nth_firstn. destruct (Nat.ltb_spec i n); [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Lemma zero_chars_get : forall ch off len j, zero_chars ch off len = true -> 0 <= off -> 0 <= len -> off + len <= 16777211 ->
  off <= j < off + len -> PrimString.get ch (Uint63.of_Z j) = 48%uint63.
Proof.
  intros ch off len j ZC Ho Hl Hm Hj. unfold zero_chars in ZC.
  destruct (PrimString.compare _ _) eqn:C; try discriminate ZC. clear ZC.
  apply pstr_compare_eq in C. rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec in C.
  rewrite !to_Z_of_Z_small in C by lia.
  change (Uint63.to_Z PrimString.max_length) with 16777211 in C.
  change (PrimInt63.land 48 255)%uint63 with 48%uint63 in C.
  rewrite Nat.min_l in C by lia.
  rewrite PrimStringAxioms.get_spec. rewrite to_Z_of_Z_small by lia.
  replace (Z.to_nat j) with (Z.to_nat off + (Z.to_nat j - Z.to_nat off))%nat by lia.
  rewrite <- List.nth_skipn. rewrite <- (nth_firstn_lt _ (Z.to_nat len)) by lia.
  rewrite C. apply List.nth_repeat_lt. lia.
Qed.

Theorem bss_check_sound : forall segs lo hi, bss_check segs lo hi = true ->
  forall z, lo <= z < hi ->
  wview segs (fun _ => None) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)
  /\ Lib.PropExec.seg_rom segs (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
Proof.
  intros segs lo hi CK z Hz. unfold bss_check in CK.
  destruct (seg_scan segs lo hi) as [s|] eqn:SC; [| discriminate CK].
  destruct (seg_readable s) eqn:RD; [| discriminate CK]. destruct (seg_writable s) eqn:WR; [| discriminate CK].
  destruct (Z.leb_spec0 0 lo) as [L0|]; [| discriminate CK]. destruct (Z.ltb_spec0 lo hi) as [LH|]; [| discriminate CK].
  destruct (Z.leb_spec0 hi (2 ^ 63)) as [H63|]; [| discriminate CK]. cbn [andb] in CK.
  destruct (seg_bytes s) as [|ch [|ch' more]] eqn:BY; try discriminate CK.
  destruct (Z.leb_spec0 (2 * (hi - Z.of_N (seg_base s))) (Uint63.to_Z (PrimString.length ch))) as [LEN|]; [| discriminate CK].
  destruct (Z.leb_spec0 (2 * (hi - Z.of_N (seg_base s))) 16777211) as [MAXL|]; [| discriminate CK]. cbn [andb] in CK.
  pose proof (seg_scan_find segs lo hi s z SC ltac:(lia) ltac:(lia)) as (FS & B0 & T0).
  assert (Hz64 : 0 <= z < 2 ^ 64) by lia.
  assert (U : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; apply Z.mod_small; exact Hz64).
  assert (BYTE : segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s))) = Some (Z_to_bv 8 0)).
  { rewrite BY. unfold segment_byte_at.
    replace (Z.to_N (z - Z.of_N (seg_base s)) <? Z.to_N (Uint63.to_Z (PrimString.length ch) / 2))%N with true.
    2:{ symmetry. apply N.ltb_lt.
        assert (hi - Z.of_N (seg_base s) <= Uint63.to_Z (PrimString.length ch) / 2) by (apply Z.div_le_lower_bound; lia). lia. }
    unfold hex_byte_at. cbv zeta.
    replace (Uint63.ltb (Uint63.of_Z (Z.of_N (2 * Z.to_N (z - Z.of_N (seg_base s)) + 1))) (PrimString.length ch)) with true.
    2:{ symmetry. apply Uint63.ltb_spec. rewrite to_Z_of_Z_small by lia. lia. }
    cbn [orb].
    rewrite !(zero_chars_get ch (2 * (lo - Z.of_N (seg_base s))) (2 * (hi - lo))); [reflexivity | exact CK | lia | lia | lia | lia | exact CK | lia | lia | lia | lia]. }
  unfold wview, Lib.PropExec.seg_rom, memory_read. cbn beta iota. rewrite U. change (Z.of_N 1) with 1.
  rewrite FS. rewrite RD, WR. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite BYTE. split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition BSS_LO : Z := 0x1db8e8.
Definition BSS_HI : Z := 0x62b8e8.
Lemma bss_scan : bss_check ASEGS BSS_LO BSS_HI = true.
Proof. vm_compute. reflexivity. Qed.

Theorem bss_zero : ltac2:(CDefT.buildp (gd_tbl_AH0Rom ()) "Pz,$2.P,(3.(4.$18.R1.)(5.R1.$19.))(3.(7.(;.(<.&8.))(=.$1:.L,(<.&40.)(>.(<.&8.))(?.&40.R2.))(10.(<.&8.)(?.&8.=)))(7.(;.(<.&8.))(11.$1:.(?.&40.R2.))(10.(<.&8.)(?.&8.=))))")
(* [comment removed for export] *).
Proof. exact (bss_check_sound ASEGS BSS_LO BSS_HI bss_scan). Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngHeap MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz AXF_efz AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1mz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_asrnz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_nenz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_efrnz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition gbits (last j maplen : Z) : Z := last + 32 + 64 * j + 4096 * maplen.

Lemma gbits_class0 : forall last j, 0 <= last <= 31 -> 0 <= j <= 47 -> Z.shiftr (gbits last j 0) 6 = j.
Proof.
  intros last j H1 H2. unfold gbits. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
  replace (last + 32 + 64 * j + 4096 * 0) with ((last + 32) + j * 64) by ring. rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring.
Qed.

Lemma gbits_classm : forall last j maplen, 0 <= last <= 31 -> 0 <= j <= 47 -> 0 <= maplen ->
  Z.land (Z.shiftr (gbits last j maplen) 5) 126 = 2 * j.
Proof.
  intros last j maplen H1 H2 H3. unfold gbits. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  replace (last + 32 + 64 * j + 4096 * maplen) with ((last + 32) + (2 * j + 128 * maplen) * 32) by ring.
  rewrite Z.div_add by lia. replace ((last + 32) / 32) with 1 by (apply (Z.div_unique _ _ _ last); lia).
  change 126 with (Z.ones 7 - 1).
  assert (E : Z.land (1 + (2 * j + 128 * maplen)) 126 = Z.land (2 * j + 1) 126).
  { change 126 with (Z.land 127 126). rewrite !Z.land_assoc. f_equal. change 127 with (Z.ones 7). rewrite !Z.land_ones by lia.
    replace (1 + (2 * j + 128 * maplen)) with ((2 * j + 1) + maplen * 2^7) by ring. rewrite Z.mod_add by lia. reflexivity. }
  change (Z.ones 7 - 1) with 126. rewrite E.
  assert (F : forall x, 0 <= x <= 47 -> Z.land (2 * x + 1) 126 = 2 * x).
  { intros x Hx. assert (C : forallb (fun x => Z.land (2 * x + 1) 126 =? 2 * x) (zseq 0 48) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in C. specialize (C x ltac:(apply In_zseq; lia)). apply Z.eqb_eq in C. exact C. }
  apply F. exact H2.
Qed.

Lemma ef_offv_whole : forall sz ctr h3 h16, 1 <= sz -> ef_offv sz (16 * sz - 4) ctr h3 h16 = 0.
Proof.
  intros sz ctr h3 h16 Hsz. unfold ef_offv, ef_slack. replace (16 * sz - (16 * sz - 4) - 4) with 0 by ring. change (Z.shiftr 0 4) with 0.
  unfold ef_off. pose proof (land255_range (if h3 =? 0 then ctr else h16 + 1)) as H. unfold ef_off0.
  destruct (Z.land (if h3 =? 0 then ctr else h16 + 1) 255 <=? 0) eqn:E; [apply Z.leb_le in E; lia|].
  unfold ef_mask. change (Z.lor (Z.lor (Z.lor 0 (Z.shiftr 0 1)) (Z.shiftr (Z.lor 0 (Z.shiftr 0 1)) 2))
                       (Z.shiftr (Z.lor (Z.lor 0 (Z.shiftr 0 1)) (Z.shiftr (Z.lor 0 (Z.shiftr 0 1)) 2)) 4)) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.

Lemma wa_mod64' : forall v, wa v = wa (v mod 2^64).
Proof. intros v. apply bv_eq. rewrite !u_wa. rewrite Z.mod_mod by lia. reflexivity. Qed.

Section AG9.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_nenf : forall R m rom idx j G sz ctr last maplen mem h3 h16,
  getr R 1 = wa 0x54488 -> getr R 10 = wa idx -> getr R 18 = wa j -> getr R 22 = wa 621712 -> getr R 25 = wa 98984 ->
  0 <= idx <= last -> 0 <= last <= 31 -> 0 <= j <= 47 -> 0 <= maplen <= 2^40 -> (maplen <> 0 -> last <> 0) ->
  1 <= G <= 2^63-1 -> G mod 8 = 0 -> 1 <= sz <= 4096 -> 1 <= mem -> mem + 16 + 16 * sz * (last + 1) <= 2^63 ->
  0 <= ctr <= 2^32-1 -> 0 <= h3 <= 255 -> 0 <= h16 <= 65535 ->
  rdn SEGS m (wa (8 * j + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ->
  rdn SEGS m (wa (2 * j + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ->
  rdn SEGS m (wa (0 + 621732)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ->
  rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa (gbits last j maplen))) ->
  rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ->
  rdn SEGS m (wa (mem + 16 * sz * idx + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  rdn SEGS m (wa (mem + 16 * sz * idx + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ->
  rdn SEGS m (wa (mem + 16 * sz * idx + 14)) 2 = Some (word_to_le_bytes 2 (wa h16)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 * sz -> store_ok SEGS m (wa (ef_st mem sz idx - 4 + d)) k = true) ->
  (G + 16 + 8 <= ef_st mem sz idx - 4 \/ ef_st mem sz idx - 4 + 16 * sz <= G + 16) ->
  exists R', msteps SEGS (mkst R (wa 0x54944) m rom)
                   (mkst R' (wa 0x544b8) (efb_mem m idx (16 * sz - 4) mem sz (ef_st mem sz idx) 0) rom) /\
    getr R' 10 = wa (ef_st mem sz idx) /\ getr R' 1 = wa 0x544b8 /\ getr R' 18 = wa (2 * j + 98984) /\
    (forall k, In k [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom idx j G sz ctr last maplen mem h3 h16 R1 R10 R18 R22 R25 Hidx Hlast Hj Hml Hml' HG AG Hsz Hmem Hend Hctr Hh3 Hh16
    MA Msz Mctr MW Mmem M12 M13 M14 Wok D.
  destruct (asrn_pasrn R m rom 0 ltac:(constructor; [exact R1 | lia]) ltac:(constructor)) as (R1' & Hms1 & A1 & AK).
  unfold asrn_mem_pasrn in Hms1.
  assert (P2 : nen_pre R1' m idx j G sz ctr).
  { constructor; [regk AK 10%nat; exact R10 | regk AK 18%nat; exact R18 | regk AK 22%nat; exact R22 | regk AK 25%nat; exact R25
                 | lia | lia | lia | lia | lia | exact MA | exact Msz | exact Mctr]. }
  destruct (nen_pnen R1' m rom idx j G sz ctr P2 ltac:(constructor)) as (R2 & Hms2 & B1 & B10 & B11 & B12 & B13 & B18 & B22 & B25 & BK).
  unfold nen_mem_pnen in Hms2.
  set (ctr' := (ext_Z true 0 4 ctr) mod 2^64).
  assert (B13' : getr R2 13 = wa ctr') by (rewrite B13; apply wa_mod64').
  assert (Rctr' : 0 <= ctr' <= 2^64-1) by (unfold ctr'; pose proof (Z.mod_pos_bound (ext_Z true 0 4 ctr) (2^64) ltac:(lia)); lia).
  assert (Rend : ef_st mem sz idx + 16 * sz <= 2^63) by (unfold ef_st; clear - Hend Hidx Hsz; nia).
  assert (RSLOT : 1 <= mem + 16 * sz * idx <= 2^63-1) by (clear - Hmem Hend Hidx Hsz; nia).
  assert (EF : exists R3, msteps SEGS (mkst R2 (wa 0x5494c) m rom) (mkst R3 (wa 0x54a98) (efb_mem m idx (16 * sz - 4) mem sz (ef_st mem sz idx) 0) rom) /\
                 getr R3 10 = wa (ef_st mem sz idx) /\
                 (forall k, In k callee_regs -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.eq_dec maplen 0) as [E0|E0].
    - subst maplen.
      assert (P : ef_pre R2 m G idx (16 * sz - 4) ctr' (gbits last j 0) mem sz h3 h16).
      { constructor; [|exact Rend | exact Wok | exact D].
        constructor; [exact B10 | exact B11 | exact B12 | exact B13' | lia | exact AG | lia | lia | exact Rctr' | unfold gbits; lia | lia | lia | lia | lia
                     | exact RSLOT | exact MW | exact Mmem | rewrite gbits_class0 by lia; exact Msz | exact M12 | exact M13 | exact M14 | lia]. }
      destruct (ef_class0_arm R2 m rom G idx (16 * sz - 4) ctr' (gbits last j 0) mem sz h3 h16 P) as (R3 & Hms3 & C10 & CK).
      rewrite ef_offv_whole in Hms3, C10 by lia. rewrite Z.mul_0_r, Z.add_0_r in C10.
      exists R3. split; [exact Hms3|]. split; [exact C10 | exact CK].
    - assert (Wl : Z.land (gbits last j maplen) 31 <> 0).
      { unfold gbits. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
        replace (last + 32 + 64 * j + 4096 * maplen) with (last + (1 + 2 * j + 128 * maplen) * 2^5) by ring. rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia. exact (Hml' E0). }
      assert (P : efm_pre R2 m G idx (16 * sz - 4) ctr' (gbits last j maplen) mem sz h3 h16).
      { constructor; [|exact Rend | exact Wok | exact D].
        constructor; [exact B10 | exact B11 | exact B12 | exact B13' | lia | exact AG | lia | lia | exact Rctr' | unfold gbits; lia | exact Wl | lia | lia | lia | lia
                     | exact RSLOT | exact MW | exact Mmem | rewrite gbits_classm by lia; exact Msz | exact M12 | exact M13 | exact M14 | lia]. }
      destruct (ef_classm_arm R2 m rom G idx (16 * sz - 4) ctr' (gbits last j maplen) mem sz h3 h16 P) as (R3 & Hms3 & C10 & CK).
      rewrite ef_offv_whole in Hms3, C10 by lia. rewrite Z.mul_0_r, Z.add_0_r in C10.
      exists R3. split; [exact Hms3|]. split; [exact C10 | exact CK]. }
  destruct EF as (R3 & Hms3 & C10 & CK).
  destruct (efrn_pefrn R3 (efb_mem m idx (16 * sz - 4) mem sz (ef_st mem sz idx) 0) rom 0 ltac:(constructor; [regk CK 1%nat; exact B1 | lia]) ltac:(constructor)) as (R4 & Hms4 & D1 & DK).
  unfold efrn_mem_pefrn in Hms4.
  exists R4. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 Hms4)))|].
  split; [regk DK 10%nat; exact C10|]. split; [exact D1|]. split; [regk DK 18%nat; regk CK 18%nat; exact B18|].
  intros k Hk. destruct (Nat.eq_dec k 22) as [->|N22]; [regk DK 22%nat; regk CK 22%nat; litr2 B22; symmetry; litr2 R22; reflexivity|].
  destruct (Nat.eq_dec k 25) as [->|N25]; [regk DK 25%nat; regk CK 25%nat; litr2 B25; symmetry; litr2 R25; reflexivity|].
  assert (Hk' : In k [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 26; 27]%nat) by (clear - Hk N22 N25; cbn [In] in *; intuition congruence).
  rewrite (DK k ltac:(clear - Hk'; klist Hk')), (CK k ltac:(clear - Hk'; cbn [callee_regs In] in *; klist Hk')), (BK k ltac:(clear - Hk'; klist Hk')).
  apply AK. clear - Hk'. klist Hk'.
Qed.
End AG9.

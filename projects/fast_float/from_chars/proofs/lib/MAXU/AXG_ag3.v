(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngHeap MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM AxTry AXG_ag1 AXG_ag2 AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.AXF_mmrz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.AXF_mmbz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_aiz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_ai0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_ins1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.AXF_ins2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition mm_plan (sc cnt0 u0 u1 b req : Z) : Z * Z :=
  let u := ua_u sc u0 u1 in
  let ns := ab_ns sc b in
  iv_plan (rd_cnt sc cnt0 u ns (class_size sc * cnt0)) (class_size sc) ns req u.

(* [comment removed for export] *)
Definition mmw_frame (m : word -> option byte) (spm : Z) (sc mt len s4 s5 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (spm + -8)) (word_to_le_bytes 8 (wa 345944)))
    (wa (spm + -16)) (word_to_le_bytes 8 (wa sc))) (wa (spm + -24)) (word_to_le_bytes 8 (wa mt)))
    (wa (spm + -32)) (word_to_le_bytes 8 (wa 18446744073709551615))) (wa (spm + -40)) (word_to_le_bytes 8 (wa len)))
    (wa (spm + -48)) (word_to_le_bytes 8 (wa s4))) (wa (spm + -56)) (word_to_le_bytes 8 (wa s5)).

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

Lemma page_round_ge : forall x, 1 <= x -> 4096 <= page_round x.
Proof. intros x H. unfold page_round, PGSZ. assert (1 <= (x + 4096 - 1) / 4096) by (apply Z.div_le_lower_bound; lia). lia. Qed.

Lemma page_round_le : forall x, 0 <= x -> page_round x <= x + 4095.
Proof. intros x H. unfold page_round, PGSZ. pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma grows_wb' : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. exact (mem_grows_trans _ _ _ H (wbytes_grows _ _ _)). Qed.

Section AG3.
Context {fx : FPState}.

#[using="Type"] Theorem seg_mpre : forall R m rom sp0 sc mt u0 cnt0 req seq b useq u1,
  getr R 2 = wa (sp0 + -144) -> getr R 8 = wa sc -> getr R 9 = wa mt -> getr R 10 = wa u0 -> getr R 11 = wa 4096 ->
  getr R 12 = wa (class_size sc + 16) -> getr R 14 = wa (class_size sc * cnt0) -> getr R 18 = wa req -> getr R 19 = wa cnt0 ->
  getr R 20 = wa 621568 -> getr R 21 = wa (8 * sc + 621800) -> getr R 22 = wa 621712 -> getr R 23 = wa (8 * sc + 621712) ->
  getr R 24 = wa (class_size sc) ->
  2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 -> stk_ok SEGS m (wa (sp0 + -144)) 1088 ->
  0 <= sc <= 47 -> 1 <= mt <= 2^63-1 -> 0 <= u0 <= 2^60 -> 1 <= cnt0 <= 32 -> 0 <= req <= 2^26 ->
  0 <= seq <= 255 -> 0 <= b <= 255 -> 0 <= useq <= 255 -> 0 <= u1 <= 2^60 ->
  class_size sc * cnt0 <= 2^23 ->
  rdn SEGS m (wa (0 + 622632)) 1 = Some (word_to_le_bytes 1 (wa seq)) ->
  (ab_tr sc = true -> rdn SEGS m (wa (sc + 622593)) 1 = Some (word_to_le_bytes 1 (wa b)) /\
     rdn SEGS m (wa (sc + 622561)) 1 = Some (word_to_le_bytes 1 (wa useq)) /\
     (forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (sc + 622593 + d)) k = true)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 622568 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 622632 + d)) k = true) ->
  (sc <= 31 -> rdn SEGS m (wa (8 * sc + 622192)) 8 = Some (word_to_le_bytes 8 (wa u1))) ->
  exists R', msteps SEGS (mkst R (wa 0x54374) m rom)
                     (mkst R' (wa 0x551a4) (mmw_frame (sq_mem (ab_mem m sc b useq seq) seq) (sp0 + -144) sc mt (snd (mm_plan sc cnt0 u0 u1 b req))
                                                 621568 (8 * sc + 621800)) rom) /\
    getr R' 17 = wa 222 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (snd (mm_plan sc cnt0 u0 u1 b req)) /\ getr R' 12 = wa 3 /\
    getr R' 13 = wa 34 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 16 = wa 0 /\
    getr R' 2 = wa (sp0 + -144 + -64) /\ getr R' 22 = wa 621712 /\ getr R' 23 = wa (8 * sc + 621712) /\ getr R' 24 = wa (class_size sc) /\
    getr R' 25 = wa (fst (mm_plan sc cnt0 u0 u1 b req)) /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 sc mt u0 cnt0 req seq b useq u1 R2 R8 R9 R10 R11 R12 R14 R18 R19 R20 R21 R22 R23 R24 Hsp Asp STK
    Hsc Hmt Hu0 Hc0 Hreq Hseq Hb Hus Hu1 Hsz Mseq Mtr Wun Wseq Mu1.
  pose proof (size_classes_range sc ltac:(lia)) as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 131056) by (rewrite Ecs; lia).
  (* [comment removed for export] *)
  destruct (seg_ab R m rom sc b useq seq R8 R22 Hsc Hb Hus Hseq Mseq Mtr) as (R1 & Hms1 & A8 & A13 & A16 & A22 & AK).
  set (m1 := ab_mem m sc b useq seq) in *.
  assert (Wun1 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m1 (wa (0 + 622568 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m1); [unfold m1, ab_mem; destruct (ab_hit sc useq seq); [apply wbytes_grows | apply mem_grows_refl] | exact (Wun d k Hd Hk)]. }
  assert (Wseq1 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m1 (wa (0 + 622632 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m1); [unfold m1, ab_mem; destruct (ab_hit sc useq seq); [apply wbytes_grows | apply mem_grows_refl] | exact (Wseq d k Hd Hk)]. }
  (* [comment removed for export] *)
  destruct (seg_sq R1 m1 rom seq A16 A22 Hseq Wun1 Wseq1) as (R2' & Hms2 & B15 & B22 & BK).
  set (m2 := sq_mem m1 seq) in *.
  assert (G12 : mem_grows m m2).
  { apply (mem_grows_trans m m1 m2).
    - unfold m1, ab_mem. destruct (ab_hit sc useq seq); [apply wbytes_grows | apply mem_grows_refl].
    - unfold m2, sq_mem. destruct (seq =? 255); repeat apply grows_wb'; apply mem_grows_refl. }
  assert (OUT2 : forall x, 0 <= x < 2^64 -> ~ (622568 <= x < 622640) -> m2 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m2, sq_mem. destruct (seq =? 255); rewrite ?MngWb.wbytes_out by side;
      unfold m1, ab_mem; destruct (ab_hit sc useq seq) eqn:Eh; rewrite ?MngWb.wbytes_out by (unfold ab_hit, ab_tr in Eh; cbn [length word_to_le_bytes Z_to_le_bytes];
        rewrite ?u_wa_small by lia; destruct (7 <=? sc) eqn:E1; destruct (sc <? 39) eqn:E2; cbn [andb] in Eh; try discriminate Eh;
        apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia); reflexivity. }
  assert (Mu1' : sc <= 31 -> rdn SEGS m2 (wa (8 * sc + 622192)) 8 = Some (word_to_le_bytes 8 (wa u1))).
  { intros S. rewrite (rdn_frame_n m m2 (8 * sc + 622192) 8) by (first [lia | intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply OUT2; lia]). exact (Mu1 S). }
  (* [comment removed for export] *)
  destruct (seg_ua R2' m2 rom sc u0 u1 ltac:(regk BK 8%nat; exact A8) ltac:(regk BK 10%nat; regk AK 10%nat; exact R10) B15
              ltac:(regk BK 23%nat; regk AK 23%nat; exact R23) Hsc Hu0 Hu1 Mu1') as (R3 & Hms3 & C8 & C10 & C23 & CK).
  set (u := ua_u sc u0 u1) in *. assert (Hu : 0 <= u <= 2^61) by (unfold u, ua_u; destruct (_ && _); lia).
  set (ns := ab_ns sc b) in *. assert (Hns : 0 <= ns <= 1) by (unfold ns, ab_ns; destruct (ab_tr sc); [destruct (b <? 100)|]; lia).
  destruct (seg_rd R3 m2 rom sc cnt0 u ns (class_size sc * cnt0) C8 C10 ltac:(regk CK 11%nat; regk BK 11%nat; regk AK 11%nat; exact R11)
              ltac:(regk CK 13%nat; regk BK 13%nat; exact A13) ltac:(regk CK 14%nat; regk BK 14%nat; regk AK 14%nat; exact R14)
              ltac:(regk CK 19%nat; regk BK 19%nat; regk AK 19%nat; exact R19) Hsc Hc0 Hu Hns ltac:(nia)) as (R4 & Hms4 & D25 & D8 & D10 & D11 & D13 & D14 & DK).
  set (cnt := rd_cnt sc cnt0 u ns (class_size sc * cnt0)) in *.
  assert (Hcnt : 1 <= cnt <= 32) by (unfold cnt, rd_cnt; repeat (destruct (_ && _)); lia).
  destruct (seg_iv R4 m2 rom cnt (class_size sc) ns req u D10 D11 ltac:(regk DK 12%nat; regk CK 12%nat; regk BK 12%nat; regk AK 12%nat; exact R12)
              D13 ltac:(regk DK 18%nat; regk CK 18%nat; regk BK 18%nat; regk AK 18%nat; exact R18)
              ltac:(regk DK 24%nat; regk CK 24%nat; regk BK 24%nat; regk AK 24%nat; exact R24) D25 Hcnt Hsize Hns Hreq Hu)
    as (R5 & Hms5 & E1 & E10 & E11 & E12 & E13 & E14 & E15 & E18 & E19 & E24 & E25 & EK).
  set (pl := iv_plan cnt (class_size sc) ns req u) in *.
  assert (Hlen : 4096 <= snd pl <= 2^40).
  { unfold pl, iv_plan. pose proof (page_round_range (req + 20) ltac:(lia)). pose proof (page_round_range (class_size sc * cnt + 16) ltac:(nia)).
    pose proof (page_round_ge (req + 20) ltac:(lia)). pose proof (page_round_ge (class_size sc * cnt + 16) ltac:(nia)).
    pose proof (page_round_le (req + 20) ltac:(lia)). pose proof (page_round_le (class_size sc * cnt + 16) ltac:(nia)).
    assert (class_size sc * cnt <= 131056 * 32) by nia.
    destruct (_ && _); [destruct (_ || _)|]; cbn [snd]; lia. }
  assert (G5 : forall k, In k [2; 3; 4; 9; 20; 21; 26; 27]%nat -> getr R5 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (EK k ltac:(clear - Hk; klist Hk)), (DK k ltac:(clear - Hk; klist Hk)), (CK k ltac:(clear - Hk; klist Hk)),
      (BK k ltac:(clear - Hk; klist Hk)). apply AK. clear - Hk. klist Hk. }
  assert (STK2 : stk_ok SEGS m2 (wa (sp0 + -144)) 1024) by (apply (stk_ok_mono' m2 _ 1088 1024); [exact (stk_ok_grows SEGS m m2 _ 1088 STK G12) | lia]).
  assert (P6 : mmw_pre R5 m2 (sp0 + -144) 0 (snd pl) 3 34).
  { constructor; [regk G5 2%nat; exact R2 | exact E10 | exact E11 | exact E12 | exact E13 | exact E14 | exact E15 | exact STK2 | lia | lia | lia | lia | lia |].
    apply Z.mod_divide in Asp; [|lia]. destruct Asp as (k & ->). replace (k * 16 + -144) with ((k - 9) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mmw_pnf R5 m2 rom (sp0 + -144) 0 (snd pl) 3 34 P6) as (R6 & Hms6 & F2 & F5 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & FK).
  { scs_go; zats. reflexivity. }
  assert (EM : mmw_mem_pnf m2 R5 (sp0 + -144) 0 (snd pl) 3 34 = mmw_frame m2 (sp0 + -144) sc mt (snd pl) 621568 (8 * sc + 621800)).
  { unfold mmw_mem_pnf, mmw_frame.
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 1))) with (wa 345944) by (symmetry; litr2 E1; reflexivity).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 8))) with (wa sc) by (symmetry; regk EK 8%nat; exact D8).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 9))) with (wa mt) by (symmetry; regk G5 9%nat; exact R9).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 18))) with (wa 18446744073709551615) by (symmetry; litr2 E18; reflexivity).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 19))) with (wa (snd pl)) by (symmetry; litr2 E19; reflexivity).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 20))) with (wa 621568) by (symmetry; regk G5 20%nat; exact R20).
    replace (getr R5 (Z_to_bv 5 (Z.of_nat 21))) with (wa (8 * sc + 621800)) by (symmetry; regk G5 21%nat; exact R21).
    rewrite !u_wa_small by lia. reflexivity. }
  rewrite EM in Hms6.
  exists R6. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3
                          (msteps_trans SEGS _ _ _ Hms4 (msteps_trans SEGS _ _ _ Hms5 Hms6)))))|].
  change (mm_plan sc cnt0 u0 u1 b req) with pl.
  split; [exact F17|]. split; [exact F10|]. split; [exact F11|]. split; [exact F12|]. split; [exact F13|]. split; [exact F14|].
  split; [exact F15|]. split; [exact F16|]. split; [exact F2|].
  split; [regk FK 22%nat; regk EK 22%nat; regk DK 22%nat; regk CK 22%nat; exact B22|].
  split; [regk FK 23%nat; regk EK 23%nat; regk DK 23%nat; exact C23|].
  split; [regk FK 24%nat; exact E24|].
  split; [regk FK 25%nat; exact E25|].
  intros k Hk. rewrite (FK k ltac:(clear - Hk; klist Hk)). apply G5. clear - Hk. klist Hk.
Qed.
End AG3.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim MemsetLib As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatPoisonRun_b BatPoison3_b BatAllocC_b BatAllocD_b BatAllocE_b BatAllocV_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatCellEx_b
     BatAllocSecC_b BatAllocSecD_b BatAllocSecE_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0SumsMemset_code_b Ba0SumsMemset_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_postL_fp (sp t ab rz q : Z) : list (Z * Z) :=
  [ (sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 16 + 4096); (2147450880 + ab / 8, 512 * q); (t + 2800, 112) ].

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_div8_add : forall a b, a mod 8 = 0 -> 0 <= a -> 0 <= b -> (a + b) / 8 = a / 8 + b / 8.
Proof.
  intros a b Ha H0 Hb. pose proof (Z.div_mod a 8 ltac:(lia)) as E. rewrite Ha in E.
  replace (a + b) with (b + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

#[using="Type"] Theorem art_allocate_post_sec : forall r8 (M8 rom : word -> option byte) (raw : word)
    (sp n qn m8 rs qr rz qz nd q ab spb t tp loff key tsd ctx id b1 f120 f112 f104 f96 f88 f80 f72 f64 f56 f48 f40 f32 f24 : Z),
  f120 = U raw -> ret_ok raw ->
  getr r8 2 = Z_to_bv 64 (sp - 128) -> getr r8 4 = Z_to_bv 64 tp -> getr r8 8 = Z_to_bv 64 0 -> getr r8 9 = Z_to_bv 64 n -> getr r8 10 = Z_to_bv 64 id ->
  getr r8 18 = Z_to_bv 64 ab -> getr r8 19 = Z_to_bv 64 nd -> getr r8 20 = Z_to_bv 64 (ab + rz) -> getr r8 21 = Z_to_bv 64 (ab + rz - 16) ->
  getr r8 22 = Z_to_bv 64 1295832 -> getr r8 24 = Z_to_bv 64 0 -> getr r8 25 = Z_to_bv 64 (ab + rz + n) ->
  (* [comment removed for export] *)
  4096 <= n < 2 ^ 39 -> n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> rz = 16 * qz -> 32 <= rz <= 2048 ->
  nd = rs + rz + rz -> 65536 < nd -> 4096 * (q - 1) < nd <= 4096 * q ->
  (* [comment removed for export] *)
  0x10007fff8000 + 4096 <= sp -> sp + 2144 <= 2 ^ 47 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> apart t 4096 (sp - 1952) 6048 -> apart t 4096 0x7fff8000 0x100000000000 ->
  apart ctx 4096 (sp - 1952) 6048 -> (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 -> apart ctx 4096 0x7fff8000 0x100000000000 ->
  0 <= loff -> 0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tp + loff -> tp + loff + 4 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 ->
  ab mod 4096 = 0 -> 0x696000 + 4096 <= ab -> (ab + 4096 * q < 0x7fff8000 \/ 0x10007fff8000 + 4096 <= ab) -> ab + 4096 * q < 2 ^ 47 ->
  apart (ab - 4096) (4096 * q + 4096) (sp - 1952) 6048 -> apart (ab - 4096) (4096 * q + 4096) t 4096 -> apart (ab - 4096) (4096 * q + 4096) ctx 4096 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 48 -> (ab < spb \/ spb + 2 ^ 37 <= ab) ->
  0 <= id < 2 ^ 32 -> 0 <= b1 < 256 ->
  0 <= f120 < 2 ^ 64 -> 0 <= f112 < 2 ^ 64 -> 0 <= f104 < 2 ^ 64 -> 0 <= f96 < 2 ^ 64 -> 0 <= f88 < 2 ^ 64 -> 0 <= f80 < 2 ^ 64 -> 0 <= f72 < 2 ^ 64 ->
  0 <= f64 < 2 ^ 64 -> 0 <= f56 < 2 ^ 64 -> 0 <= f48 < 2 ^ 64 -> 0 <= f40 < 2 ^ 64 -> 0 <= f32 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  (* [comment removed for export] *)
  wrA M8 (sp - 1952) 1952 -> wrA M8 ab (4096 * q) -> wrA M8 (2147450880 + ab / 8) (512 * q) -> wrA M8 t 4096 ->
  art_layout M8 -> art_tsd M8 tp key tsd ctx t ->
  cellA M8 (1295832 + 32) 8 spb -> cellA M8 (1295832 + 64) 8 4096 -> cellA M8 (ab - 4096 + 16) 8 nd ->
  cellA M8 (0x13d438 + 85) 1 1 -> cellA M8 (0x13d438 + 44) 4 4096 -> cellA M8 (0x13d438 + 52) 4 190 ->
  cellA M8 0x138120 8 loff -> cellA M8 (tp + loff) 4 0 -> cellA M8 0x1d1700 8 0 -> cellA M8 0x10360 8 0xcc6e96b9cc6e96b9 ->
  cellA M8 (ab + rz - 15) 1 b1 -> cellA M8 (ab + rz - 12) 4 n -> cellA M8 (ab + rz - 14) 2 0 ->
  cellA M8 (sp - 128 + 8) 8 1 ->
  cellA M8 (sp - 128 + 120) 8 f120 -> cellA M8 (sp - 128 + 112) 8 f112 -> cellA M8 (sp - 128 + 104) 8 f104 -> cellA M8 (sp - 128 + 96) 8 f96 -> cellA M8 (sp - 128 + 88) 8 f88 -> cellA M8 (sp - 128 + 80) 8 f80 -> cellA M8 (sp - 128 + 72) 8 f72 -> cellA M8 (sp - 128 + 64) 8 f64 -> cellA M8 (sp - 128 + 56) 8 f56 -> cellA M8 (sp - 128 + 48) 8 f48 -> cellA M8 (sp - 128 + 40) 8 f40 -> cellA M8 (sp - 128 + 32) 8 f32 -> cellA M8 (sp - 128 + 24) 8 f24 ->
  exists regs' M',
    msteps ASEGS (mkst r8 (0x52990 : word) M8 rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 f112 /\ getr regs' 9 = Z_to_bv 64 f104 /\ getr regs' 18 = Z_to_bv 64 f96 /\ getr regs' 19 = Z_to_bv 64 f88
    /\ getr regs' 20 = Z_to_bv 64 f80 /\ getr regs' 21 = Z_to_bv 64 f72 /\ getr regs' 22 = Z_to_bv 64 f64 /\ getr regs' 23 = Z_to_bv 64 f56
    /\ getr regs' 24 = Z_to_bv 64 f48 /\ getr regs' 25 = Z_to_bv 64 f40 /\ getr regs' 26 = Z_to_bv 64 f32 /\ getr regs' 27 = Z_to_bv 64 f24
    /\ mem_grows M8 M'
    /\ art_agree (art_postL_fp sp t ab rz q) M8 M'
    /\ cellA M' (ab + rz - 16) 1 2 /\ cellA M' (ab + rz - 12) 4 n /\ cellA M' (ab + rz - 15) 1 (Z.land b1 243) /\ cellA M' (ab + rz - 14) 2 0
    /\ cellA M' (ab + rz - 8) 8 id /\ cellA M' ab 8 0xcc6e96b9cc6e96b9 /\ cellA M' (ab + 8) 8 (ab + rz - 16)
    /\ (forall j, 0 <= j < qn -> cellA M' (2147450880 + ab / 8 + 2 * qz + j) 1 0) /\ (m8 <> 0 -> cellA M' (2147450880 + ab / 8 + 2 * qz + qn) 1 m8)
    /\ getr regs' 3 = getr r8 3 /\ getr regs' 4 = getr r8 4.
Proof.
  intros r8 M8 rom raw sp n qn m8 rs qr rz qz nd q ab spb t tp loff key tsd ctx id b1 f120 f112 f104 f96 f88 f80 f72 f64 f56 f48 f40 f32 f24.
  intros Ef120 Hret Q2 Q4 Q8 Q9 Q10 Q18 Q19 Q20 Q21 Q22 Q24 Q25.
  intros Hn En Hm8 Ers Hrs Erz Hrz End Hnd Hq.
  intros Hsp Hsp' Ht Ht' Timg Atsp Atsh Acsp Cimg Atc Acsh Hloff Htp Htp8 Htpl Htpl' Htsd Htsd'.
  intros Hab4 Hab Hmem Hab' Absp Abt Abc Hspb Hspb' OUT Hid Hb1.
  intros B120 B112 B104 B96 B88 B80 B72 B64 B56 B48 B40 B32 B24.
  intros W Wab Wsh Wt L TSD Cspb Cpg Cnd Cpp Cmax Cfb Cg Clsan Chook Cmag Bh1 Bh12 Bh14 Ccf F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in Timg. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in Cimg.
  change (hid (ab + 4096 * q < 0x7fff8000 \/ 0x10007fff8000 + 4096 <= ab)) in Hmem. change (hid (ab < spb \/ spb + 2 ^ 37 <= ab)) in OUT.
  (* [comment removed for export] *)
  assert (Eka : ab = 4096 * (ab / 4096)) by (pose proof (Z.div_mod ab 4096 ltac:(lia)); lia).
  set (ka := ab / 4096) in *.
  assert (Hab8 : ab / 8 = 512 * ka). { rewrite Eka. replace (4096 * ka) with (512 * ka * 8) by lia. apply Z.div_mul. lia. }
  assert (Mab8 : ab mod 8 = 0). { rewrite Eka. replace (4096 * ka) with (512 * ka * 8) by lia. apply Z_mod_mult. }
  assert (Mab16 : ab mod 16 = 0). { rewrite Eka. replace (4096 * ka) with (256 * ka * 16) by lia. apply Z_mod_mult. }
  assert (Mrz16 : rz mod 16 = 0). { rewrite Erz, Z.mul_comm. apply Z_mod_mult. }
  assert (Hub8 : (ab + rz) / 8 = 512 * ka + 2 * qz). { rewrite Eka, Erz. replace (4096 * ka + 16 * qz) with ((512 * ka + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
  assert (Mub8 : (ab + rz) mod 8 = 0). { rewrite Eka, Erz. replace (4096 * ka + 16 * qz) with ((512 * ka + 2 * qz) * 8) by lia. apply Z_mod_mult. }
  assert (Hn8 : n / 8 = qn). { symmetry. apply (Z.div_unique n 8 qn m8); lia. }
  assert (Hnm : n mod 8 = m8). { symmetry. apply (Z.mod_unique n 8 qn m8); lia. }
  assert (Hn88 : n / 8 * 8 = 8 * qn) by lia.
  assert (Hn888 : n / 8 * 8 / 8 = qn). { rewrite Hn88. rewrite Z.mul_comm, Z.div_mul; lia. }
  assert (Etb : (ab + rz + n + 7) / 8 * 8 = ab + rz + rs).
  { assert (E : (ab + rz + n + 7) / 8 = 512 * ka + 2 * qz + qr).
    { symmetry. apply (Z.div_unique _ 8 _ (n + 7 - rs)); lia. }
    rewrite E. lia. }
  set (tb := ab + rz + rs) in *.
  assert (Htl : 4096 * q - rz - rs = 8 * (512 * q - 2 * qz - qr)) by lia.
  assert (Htl8 : (ab + 4096 * q - tb) / 8 = 512 * q - 2 * qz - qr). { unfold tb. replace (ab + 4096 * q - (ab + rz + rs)) with ((512 * q - 2 * qz - qr) * 8) by lia. apply Z.div_mul. lia. }
  assert (Htb8 : tb / 8 = 512 * ka + 2 * qz + qr). { unfold tb. rewrite Eka, Erz, Ers. replace (4096 * ka + 16 * qz + 8 * qr) with ((512 * ka + 2 * qz + qr) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hqz : 2 <= qz <= 128) by lia.
  assert (Hrz8 : rz / 8 = 2 * qz). { rewrite Erz. replace (16 * qz) with (2 * qz * 8) by lia. apply Z.div_mul. lia. }
  pose proof L as LL. destruct LL as (G48 & Csb & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  assert (PAP1 : apart (sp - 128 - 64) 64 0x1366c8 0xc000) by (unfold apart; lia).
  assert (PAP2 : apart (sp - 128 - 64) 64 0x1d1768 256) by (unfold apart; lia).
  (* [comment removed for export] *)
  destruct (art_alloc_csec1 r8 M8 rom 1295832 ab n rz id nd q spb Q10 Q8 Q9 Q18 Q20 Q21 Q22 Q24 Q25
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hab4 ltac:(lia) ltac:(lia) ltac:(lia) Hid Hq Hspb Hspb' OUT
              ltac:(eapply wr_sub; [exact Wab|lia|lia]) Cspb Cpg Cnd ltac:(unfold apart; lia) ltac:(unfold apart; lia))
    as (r9 & RUN9 & P9_1 & P9_10 & P9_11 & P9_12 & P9_8 & P9_22 & K9).
  set (M9 := Wn 8 M8 (ab + rz - 8) id) in RUN9.
  rewrite Etb in P9_22.
  assert (KK9 : forall x v, x <> 1%bv -> x <> 8%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 22%bv -> x <> 25%bv -> getr r8 x = v -> getr r9 x = v).
  { intros x v N1 N8 N10 N11 N12 N22 N25 E. rewrite K9 by assumption. exact E. }
  assert (A89 : art_agree [(ab + rz - 8, 8)] M8 M9). { unfold M9. eapply art_agree_sub; [zagree|]. clear - Hab Hab' Hrz. zsub. }
  assert (G89 : mem_grows M8 M9) by (unfold M9; zgrows).
  (* [comment removed for export] *)
  assert (MEMab : art_poison_lo_ok ab rz \/ art_poison_hi_ok ab rz).
  { clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab'. unfold hid in Hmem. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
  assert (L9 : art_layout M9). { eapply art_layout_fp; [exact A89| |exact L]. intros z Hz. clear - Hz Hab Hrz. cbn [art_out fst snd]. repeat split; try exact I; lia. }
  assert (W9f : wrA M9 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G89|]; eapply wr_sub; [exact W|lia|lia]).
  assert (W9s : wrA M9 (SB + ab / 8) (rz / 8)). { eapply wr_grows; [exact G89|]. eapply wr_sub; [exact Wsh|unfold SB; lia|unfold SB; clear - Hrz8 Hqz Hq Hnd End Hrs Hn Erz; lia]. }
  destruct (art_poison3_run r9 M9 rom (0x52a68 : bv 64)%bv (sp - 128) ab rz 250 P9_1 ltac:(unfold ret_ok; bveq)
              ltac:(apply KK9; try discriminate; exact Q2) P9_10 P9_11 P9_12 ltac:(lia) ltac:(lia) W9f PAP1 PAP2 L9 MEMab Mab8
              ltac:(clear - Erz; rewrite Erz; replace (16 * qz) with (2 * qz * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E) W9s)
    as (r10 & RUN10 & _ & P10_1 & P10_2 & P10_8 & P10_9 & P10_18 & P10_19 & P10_20 & P10_21 & K10).
  lazymatch type of RUN10 with msteps _ _ (mkst _ _ ?MM _) => set (M10 := MM) in RUN10 end.
  assert (KK10 : forall x v, art_poison_kept x -> getr r9 x = v -> getr r10 x = v). { intros x v Kx E. rewrite K10 by exact Kx. exact E. }
  #[local] Ltac pk := unfold art_poison_kept; repeat split; discriminate.
  assert (A910 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M10).
  { unfold M10, art_poison_frame, SB. rewrite Hrz8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz. eapply art_agree_sub; [zagree|].
    intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
  assert (G910 : mem_grows M9 M10) by (unfold M10, art_poison_frame; zgrows).
  (* [comment removed for export] *)
  assert (R10_18 : getr r10 18 = Z_to_bv 64 ab) by (rewrite P10_18; apply KK9; try discriminate; exact Q18).
  assert (R10_22 : getr r10 22 = Z_to_bv 64 tb) by (apply KK10; [pk|exact P9_22]).
  assert (R10_8 : getr r10 8 = Z_to_bv 64 (4096 * q)) by (rewrite P10_8; exact P9_8).
  pose proof (art_alloc_csec2 r10 M10 rom ab tb q R10_18 R10_22 R10_8 ltac:(lia) ltac:(unfold tb; lia) ltac:(unfold tb; lia) ltac:(lia)) as RUN11a.
  lazymatch type of RUN11a with msteps _ _ (mkst ?R _ _ _) => set (R11a := R) in RUN11a end.
  assert (MEMtb : art_poison_lo_ok tb (ab + 4096 * q - tb) \/ art_poison_hi_ok tb (ab + 4096 * q - tb)).
  { clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab'. unfold hid in Hmem. unfold tb, art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
  assert (G810 : mem_grows M8 M10) by (eapply mem_grows_trans; [exact G89|exact G910]).
  assert (L10 : art_layout M10).
  { eapply art_layout_fp; [exact (art_agree_trans _ _ _ _ _ A89 A910)| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
  assert (W10f : wrA M10 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G810|]; eapply wr_sub; [exact W|lia|lia]).
  assert (W10s : wrA M10 (SB + tb / 8) ((ab + 4096 * q - tb) / 8)).
  { eapply wr_grows; [exact G810|]. rewrite Htl8, Htb8. eapply wr_sub; [exact Wsh|unfold SB; clear - Hab8 Hqz Hrs Ers Hn; lia|unfold SB; clear - Hab8; lia]. }
  destruct (art_poison3_run R11a M10 rom (0x52a7c : bv 64)%bv (sp - 128) tb (ab + 4096 * q - tb) 250 ltac:(unfold R11a; gres; reflexivity) ltac:(unfold ret_ok; bveq)
              ltac:(unfold R11a; gres; exact P10_2) ltac:(unfold R11a; gres; reflexivity) ltac:(unfold R11a; gres; reflexivity) ltac:(unfold R11a; gres; reflexivity)
              ltac:(lia) ltac:(lia) W10f PAP1 PAP2 L10 MEMtb
              ltac:(unfold tb; clear - Eka Erz Ers; rewrite Eka, Erz, Ers; replace (4096 * ka + 16 * qz + 8 * qr) with ((512 * ka + 2 * qz + qr) * 8) by lia; apply Z_mod_mult)
              ltac:(unfold tb; clear - Htl; replace (ab + 4096 * q - (ab + rz + rs)) with ((512 * q - 2 * qz - qr) * 8) by lia; apply Z_mod_mult)
              ltac:(unfold tb; lia) ltac:(lia) ltac:(intros E; discriminate E) W10s)
    as (r11 & RUN11 & _ & P11_1 & P11_2 & P11_8 & P11_9 & P11_18 & P11_19 & P11_20 & P11_21 & K11).
  lazymatch type of RUN11 with msteps _ _ (mkst _ _ ?MM _) => set (M11 := MM) in RUN11 end.
  assert (KK11 : forall x v, art_poison_kept x -> getr R11a x = v -> getr r11 x = v). { intros x v Kx E. rewrite K11 by exact Kx. exact E. }
  assert (A1011 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M10 M11).
  { unfold M11, art_poison_frame, SB. rewrite Htl8, Htb8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz Ers. eapply art_agree_sub; [zagree|].
    intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
  assert (G1011 : mem_grows M10 M11) by (unfold M11, art_poison_frame; zgrows).
  (* [comment removed for export] *)
  assert (R11_9 : getr r11 9 = Z_to_bv 64 n). { rewrite P11_9. unfold R11a. gres. rewrite P10_9. apply KK9; try discriminate. exact Q9. }
  assert (R11_20 : getr r11 20 = Z_to_bv 64 (ab + rz)). { rewrite P11_20. unfold R11a. gres. rewrite P10_20. apply KK9; try discriminate. exact Q20. }
  pose proof (art_alloc_csec3 r11 M11 rom ab n rz R11_9 R11_20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RUN12a.
  lazymatch type of RUN12a with msteps _ _ (mkst ?R _ _ _) => set (R12a := R) in RUN12a end.
  assert (MEMub : art_poison_lo_ok (ab + rz) (n / 8 * 8) \/ art_poison_hi_ok (ab + rz) (n / 8 * 8)).
  { rewrite Hn88. clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab' En Hm8. unfold hid in Hmem. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
  assert (G811 : mem_grows M8 M11) by (eapply mem_grows_trans; [exact G810|exact G1011]).
  assert (A811 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M11)
    by (exact (art_agree_trans _ _ _ _ _ A89 (art_agree_trans _ _ _ _ _ A910 A1011))).
  assert (L11 : art_layout M11).
  { eapply art_layout_fp; [exact A811| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
  assert (W11f : wrA M11 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G811|]; eapply wr_sub; [exact W|lia|lia]).
  assert (W11s : wrA M11 (SB + (ab + rz) / 8) (n / 8 * 8 / 8)).
  { eapply wr_grows; [exact G811|]. rewrite Hn888, Hub8.
    eapply wr_sub; [exact Wsh|unfold SB; clear - Hab8 Hqz; lia|unfold SB; clear - Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. }
  destruct (art_poison3_run R12a M11 rom (0x52a9c : bv 64)%bv (sp - 128) (ab + rz) (n / 8 * 8) 0 ltac:(unfold R12a; gres; reflexivity) ltac:(unfold ret_ok; bveq)
              ltac:(unfold R12a; gres; exact P11_2) ltac:(unfold R12a; gres; reflexivity) ltac:(unfold R12a; gres; reflexivity) ltac:(unfold R12a; gres; reflexivity)
              ltac:(lia) ltac:(lia) W11f PAP1 PAP2 L11 MEMub Mub8
              ltac:(apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(intros _; rewrite Hn888; lia) W11s)
    as (r12 & RUN12 & _ & P12_1 & P12_2 & P12_8 & P12_9 & P12_18 & P12_19 & P12_20 & P12_21 & K12).
  lazymatch type of RUN12 with msteps _ _ (mkst _ _ ?MM _) => set (M12 := MM) in RUN12 end.
  assert (KK12 : forall x v, art_poison_kept x -> getr R12a x = v -> getr r12 x = v). { intros x v Kx E. rewrite K12 by exact Kx. exact E. }
  assert (A1112 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M11 M12).
  { unfold M12, art_poison_frame, SB. rewrite Hn888, Hub8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz Ers En Hm8. eapply art_agree_sub; [zagree|].
    intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
  assert (G1112 : mem_grows M11 M12) by (unfold M12, art_poison_frame; zgrows).
  (* [comment removed for export] *)
  #[local] Ltac r12hop P12 K12 R12a P11 K11 R11a P10 K10 :=
    first [rewrite P12 | rewrite K12 by pk]; unfold R12a; gres; first [reflexivity | (first [rewrite P11 | rewrite K11 by pk]; unfold R11a; gres; first [reflexivity | (first [rewrite P10 | rewrite K10 by pk])])].
  assert (R12_2 : getr r12 2 = Z_to_bv 64 (sp - 128)) by exact P12_2.
  assert (R12_4 : getr r12 4 = Z_to_bv 64 tp). { rewrite K12 by pk. unfold R12a. gres. rewrite K11 by pk. unfold R11a. gres. rewrite K10 by pk. apply KK9; try discriminate. exact Q4. }
  assert (R12_3 : getr r12 3 = getr r8 3). { rewrite K12 by pk. unfold R12a. gres. rewrite K11 by pk. unfold R11a. gres. rewrite K10 by pk. apply KK9; try discriminate. reflexivity. }
  assert (R12_8 : getr r12 8 = Z_to_bv 64 (4096 * q)). { rewrite P12_8. unfold R12a. gres. rewrite P11_8. unfold R11a. gres. exact R10_8. }
  assert (R12_9 : getr r12 9 = Z_to_bv 64 n). { rewrite P12_9. unfold R12a. gres. exact R11_9. }
  assert (R12_18 : getr r12 18 = Z_to_bv 64 ab). { rewrite P12_18. unfold R12a. gres. rewrite P11_18. unfold R11a. gres. exact R10_18. }
  assert (R12_19 : getr r12 19 = Z_to_bv 64 nd). { rewrite P12_19. unfold R12a. gres. rewrite P11_19. unfold R11a. gres. rewrite P10_19. apply KK9; try discriminate. exact Q19. }
  assert (R12_20 : getr r12 20 = Z_to_bv 64 (ab + rz)). { rewrite P12_20. unfold R12a. gres. exact R11_20. }
  assert (R12_21 : getr r12 21 = Z_to_bv 64 (ab + rz - 16)). { rewrite P12_21. unfold R12a. gres. rewrite P11_21. unfold R11a. gres. rewrite P10_21. apply KK9; try discriminate. exact Q21. }
  assert (R12_22 : getr r12 22 = Z_to_bv 64 (n / 8 * 8)). { rewrite K12 by pk. unfold R12a. gres. reflexivity. }
  (* [comment removed for export] *)
  assert (A912 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M12).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A910 (art_agree_trans _ _ _ _ _ A1011 A1112))|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  assert (G812 : mem_grows M8 M12) by (eapply mem_grows_trans; [exact G811|exact G1112]).
  assert (A812 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M12) by (exact (art_agree_trans _ _ _ _ _ A89 A912)).
  (* [comment removed for export] *)
  assert (Hd1 : art_d1_addr ab rz n = 2147450880 + 512 * ka + 2 * qz + qn).
  { unfold art_d1_addr. rewrite Hn88. replace (ab + rz + 8 * qn) with ((512 * ka + 2 * qz + qn) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (L12 : art_layout M12).
  { eapply art_layout_fp; [exact A812| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8 Eka. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
  assert (GI : forall a n0, 0x10000 <= a -> 0 <= n0 -> a + n0 <= 0x696000 -> art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) a n0).
  { intros a n0 Ha Hn0 Hn1. clear - Ha Hn0 Hn1 Hab Hrz Hsp Hab8 Eka. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (Cpp12 : cellA M12 (0x13d438 + 85) 1 1) by (apply (art_cell_tr1 _ M8 M12 _ _ _ A812); [split; [apply GI; cbn; lia|cbn; lia]|exact Cpp]).
  destruct (art_alloc_d1_any r12 M12 rom ab n rz R12_9 R12_20 R12_22 ltac:(lia) ltac:(clear - Hab' Hq Hnd End Hrs Hn Hrz; lia)
              ltac:(clear - Hmem Hq Hnd End Hrs Hn Hrz; unfold hid in Hmem; unfold SB, kHighMemBeg; lia) ltac:(lia) ltac:(lia) L12 Cpp12
              ltac:(intros _; rewrite Hd1; eapply wr_grows; [exact G812|]; eapply wr_sub; [exact Wsh|clear - Hab8 Hqz Hn En Hm8; lia|clear - Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]))
    as (r13 & RUN13 & K13).
  set (M13 := art_d1_mem M12 ab rz n) in RUN13.
  #[local] Ltac dk := unfold art_d1_kept; repeat split; discriminate.
  assert (A1213 : art_agree [(2147450880 + ab / 8, 512 * q)] M12 M13).
  { intros x Hx. unfold M13. apply art_d1_outside; [rewrite Hd1; clear - Eka Hab Hqz Hn En Hm8; lia|rewrite Hd1; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia|].
    intros _. rewrite Hd1. cbn [art_out fst snd] in Hx. clear - Hx Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia. }
  assert (G1213 : mem_grows M12 M13) by (unfold M13; apply art_d1_grows).
  assert (A913 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M13).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A912 A1213)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  assert (G813 : mem_grows M8 M13) by (eapply mem_grows_trans; [exact G812|exact G1213]).
  assert (A813 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M13) by (exact (art_agree_trans _ _ _ _ _ A89 A913)).
  (* [comment removed for export] *)
  assert (GT : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) t 4096).
  { clear - Atsp Atsh Abt Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GC : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) ctx 4096).
  { clear - Acsp Acsh Abc Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GF : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) (sp - 128) 128).
  { clear - Absp Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (T13 : art_tsd M13 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A813| | |exact Htp|exact Htp8|exact Htsd|exact Htsd'|exact TSD].
    - intros z Hz. eapply art_gap_out; [apply (GI 0x10000 (0x696000 - 0x10000)); lia|lia].
    - intros z Hz. eapply art_gap_out; [exact GC|lia]. }
  assert (L13 : art_layout M13).
  { eapply art_layout_fp; [exact A813| |exact L]. intros z Hz. eapply art_gap_out; [apply (GI 0x10000 (0x696000 - 0x10000)); lia|lia]. }
  assert (Wt13 : wrA M13 t 4096) by (eapply wr_grows; [exact G813|exact Wt]).
  assert (Toff : forall d, 0 <= d -> d + 8 <= 4096 -> t + d + Z.of_nat 8 <= 0x10000 \/ 0x696000 <= t + d) by (intros d Hd0 Hd1'; unfold hid in Timg; cbn; clear - Timg Hd0 Hd1'; lia).
  destruct (art_cell_exists M13 (t + 2800) 8 ltac:(lia) (Toff 2800 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mc & Hmc & Cmc).
  destruct (art_cell_exists M13 (t + 2800 + 8) 8 ltac:(lia) ltac:(replace (t + 2800 + 8) with (t + 2808) by lia; exact (Toff 2808 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mb & Hmb & Cmb).
  destruct (art_cell_exists M13 (t + 2800 + 16) 8 ltac:(lia) ltac:(replace (t + 2800 + 16) with (t + 2816) by lia; exact (Toff 2816 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mr & Hmr & Cmr).
  destruct (art_cell_exists M13 (t + 2800 + 104) 8 ltac:(lia) ltac:(replace (t + 2800 + 104) with (t + 2904) by lia; exact (Toff 2904 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (ml & Hml & Cml).
  assert (Ccf13 : cellA M13 (sp - 128 + 8) 8 1) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [eapply art_gap_sub; [exact GF|lia|cbn; lia]|cbn; lia]|exact Ccf]).
  assert (Cmax13 : cellA M13 (0x13d438 + 44) 4 4096) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [apply GI; cbn; lia|cbn; lia]|exact Cmax]).
  assert (Cfb13 : cellA M13 (0x13d438 + 52) 4 190) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [apply GI; cbn; lia|cbn; lia]|exact Cfb]).
  destruct (art_alloc_d2_large_fn r13 M13 rom (sp - 128) ab n nd rz tp key tsd ctx t mc mb mr ml
              ltac:(rewrite K13 by dk; exact R12_2) ltac:(rewrite K13 by dk; exact R12_4) ltac:(rewrite K13 by dk; exact R12_9)
              ltac:(rewrite K13 by dk; exact R12_19) ltac:(rewrite K13 by dk; exact R12_20)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - End Hrs Hrz; lia) ltac:(clear - Hnd End Hrs Hrz Hn; lia) ltac:(lia) Hmc Hmb Hmr Hml
              ltac:(eapply wr_grows; [exact G813|]; eapply wr_sub; [exact W|lia|lia]) T13 Ht ltac:(lia) Timg
              ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(clear - Acsp; unfold apart in *; lia)
              ltac:(clear - Atsp; unfold apart in *; lia)
              Cmc Cmb Cmr Cml ltac:(eapply wr_sub; [exact Wt13|lia|lia]) Ccf13 L13 Cmax13 Cfb13)
    as (r14 & RUN14 & P14_1 & P14_10 & P14_11 & P14_12 & K14).
  set (M14 := art_d2_large_mem M13 (sp - 128) t n nd mc mb mr ml) in RUN14.
  #[local] Ltac d2k := unfold art_d2_kept; repeat split; discriminate.
  assert (A1314 : art_agree [(sp - 128 - 64, 64); (t + 2800, 112)] M13 M14).
  { unfold M14, art_d2_large_mem. clear - Hsp Hsp' Ht Ht'. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G1314 : mem_grows M13 M14) by (unfold M14, art_d2_large_mem; zgrows).
  assert (A914 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112)] M9 M14).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A913 A1314)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  assert (G814 : mem_grows M8 M14) by (eapply mem_grows_trans; [exact G813|exact G1314]).
  (* [comment removed for export] *)
  assert (OK14 : store_ok ASEGS M14 (Z_to_bv 64 (ab + rz)) (Z.to_nat 4096) = true).
  { apply (wr_wok _ _ _ _ ltac:(eapply wr_grows; [exact G814 | exact Wab])); [lia|]. rewrite Z2Nat.id by lia. clear - Hq Hnd End Hrs Hn Hrz. lia. }
  destruct (memset_summary M14 (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 190) (0x52cc4 : bv 64)%bv 4096 rom
             ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK14 ltac:(unfold ret_ok; bveq) r14 P14_10 P14_11 P14_12 P14_1)
    as (r15 & RUN15 & P15_10 & AG15).
  rewrite cbyte_cbz in RUN15. unfold cbz in RUN15. rewrite art_u_lit in RUN15 by lia. change (190 mod 256) with 190 in RUN15.
  replace (Z_to_bv 64 ms_base) with (0x129d04 : bv 64)%bv in RUN15 by (apply bv_eq; vm_compute; reflexivity).
  change (wbytes M14 (Z_to_bv 64 (ab + rz)) (repeat (Z_to_bv 8 190) (Z.to_nat 4096))) with (Wf M14 (ab + rz) (Z.to_nat 4096) 190) in RUN15.
  set (M15 := Wf M14 (ab + rz) (Z.to_nat 4096) 190) in RUN15.
  #[local] Ltac mk := cbn; intuition discriminate.
  assert (R15 : forall x v, ~ In x ms_clob -> art_d2_kept x -> art_d1_kept x -> getr r12 x = v -> getr r15 x = v).
  { intros x v C1 C2 C3 E. rewrite (AG15 x C1). rewrite K14 by exact C2. rewrite K13 by exact C3. exact E. }
  assert (A1415 : art_agree [(ab + rz, 4096)] M14 M15).
  { unfold M15. clear - Hab Hab' Hrz Hq Hnd. eapply art_agree_sub; [zagree|]. intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
  assert (G1415 : mem_grows M14 M15) by (unfold M15; zgrows).
  assert (A915 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)] M9 M15).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A914 A1415)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  assert (G815 : mem_grows M8 M15) by (eapply mem_grows_trans; [exact G814|exact G1415]).
  assert (A815 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) M8 M15) by (exact (art_agree_trans _ _ _ _ _ A89 A915)).
  (* [comment removed for export] *)
  assert (GI5 : forall a n0, 0x10000 <= a -> 0 <= n0 -> a + n0 <= 0x696000 ->
                  art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) a n0).
  { intros a n0 Ha Hn0 Hn1. unfold hid in Timg. clear - Ha Hn0 Hn1 Hab Hrz Hsp Hab8 Eka Timg Ht. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GF5 : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) (sp - 128) 128).
  { clear - Absp Atsp Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GH5 : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) (ab + rz - 16) 8).
  { unfold hid in Hmem. clear - Absp Abt Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (TI : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> cellA M8 a k v -> cellA M15 a k v).
  { intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [apply GI5; lia|lia]|exact Cc]. }
  assert (TF : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M8 a k v -> cellA M15 a k v).
  { intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [eapply art_gap_sub; [exact GF5|lia|lia]|lia]|exact Cc]. }
  assert (TH : forall a (k : nat) v, ab + rz - 16 <= a -> a + Z.of_nat k <= ab + rz - 8 -> cellA M8 a k v -> cellA M15 a k v).
  { intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [eapply art_gap_sub; [exact GH5|lia|lia]|lia]|exact Cc]. }
  assert (L15 : art_layout M15).
  { eapply art_layout_fp; [exact A815| |exact L]. intros z Hz. eapply art_gap_out; [apply (GI5 0x10000 (0x696000 - 0x10000)); lia|lia]. }
  pose proof (art_alloc_e32_sec_fn r15 M15 rom raw (sp - 128) ab n rz b1 tp loff (4096 * q) f112 f104 f96 f88 f80 f72 f64 f56 f48 f40 f32 f24
                ltac:(apply R15; [mk|d2k|dk|exact R12_2]) ltac:(apply R15; [mk|d2k|dk|exact R12_4]) ltac:(apply R15; [mk|d2k|dk|exact R12_8])
                ltac:(clear - Hq Hnd Hab Hab'; lia)
                ltac:(apply R15; [mk|d2k|dk|exact R12_9]) ltac:(apply R15; [mk|d2k|dk|exact R12_18]) ltac:(apply R15; [mk|d2k|dk|exact R12_20])
                ltac:(apply R15; [mk|d2k|dk|exact R12_21])
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hab' Hq Hnd End Hrs Hn Hrz; lia) Mab16 ltac:(lia) Hb1 ltac:(lia) ltac:(lia) Hloff ltac:(lia) Hret
                ltac:(apply TI; [lia|cbn; lia|exact Cg]) ltac:(apply TI; [lia|cbn; lia|exact Clsan])
                ltac:(unfold apart; clear - Htpl' Hab Hrz; lia)
                ltac:(apply TH; [lia|cbn; lia|]; replace (ab + rz - 16 + 1) with (ab + rz - 15) by lia; exact Bh1)
                ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact Wab|lia|clear - Hq Hnd End Hrs Hn Hrz; lia])
                ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact W|lia|lia])
                L15 ltac:(apply TI; [lia|cbn; lia|exact Chook])
                ltac:(clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia) ltac:(clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia)
                ltac:(apply TF; [lia|cbn; lia|]; rewrite <- Ef120; exact F120)
                ltac:(apply TF; [lia|cbn; lia|exact F112]) ltac:(apply TF; [lia|cbn; lia|exact F104]) ltac:(apply TF; [lia|cbn; lia|exact F96])
                ltac:(apply TF; [lia|cbn; lia|exact F88]) ltac:(apply TF; [lia|cbn; lia|exact F80]) ltac:(apply TF; [lia|cbn; lia|exact F72])
                ltac:(apply TF; [lia|cbn; lia|exact F64]) ltac:(apply TF; [lia|cbn; lia|exact F56]) ltac:(apply TF; [lia|cbn; lia|exact F48])
                ltac:(apply TF; [lia|cbn; lia|exact F40]) ltac:(apply TF; [lia|cbn; lia|exact F32]) ltac:(apply TF; [lia|cbn; lia|exact F24])
                Hrz Mrz16 ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact Wab|lia|clear - Hq Hnd; lia])
                ltac:(apply TI; [lia|cbn; lia|exact Cmag])) as RUN16.
  lazymatch type of RUN16 with msteps _ _ (mkst ?R _ ?MM _) => set (R16 := R) in RUN16; set (M16 := MM) in RUN16 end.
  (* [comment removed for export] *)
  assert (A1516 : art_agree [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)] M15 M16).
  { unfold M16. clear - Hsp Hsp' Hab Hab' Hrz Hq Hnd. eapply art_agree_sub; [zagree|]. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  assert (G1516 : mem_grows M15 M16) by (unfold M16; zgrows).
  assert (Bh12_15 : cellA M15 (ab + rz - 12) 4 n) by (apply TH; [lia|cbn; lia|exact Bh12]).
  assert (Bh14_15 : cellA M15 (ab + rz - 14) 2 0) by (apply TH; [lia|cbn; lia|exact Bh14]).
  assert (Bid_15 : cellA M15 (ab + rz - 8) 8 id).
  { apply (art_cell_tr1 _ M9 M15 _ _ _ A915); [|unfold M9; apply cell_Wn_hit; [lia|cbn; lia]].
    unfold hid in Hmem. clear - Absp Abt Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; cbn; lia. }
  assert (APH : apart (sp - 128 - 64) 64 ab (rz + 16)) by (clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia).
  exists R16, M16.
  split. { eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11a|]. eapply msteps_trans; [exact RUN11|].
           eapply msteps_trans; [exact RUN12a|]. eapply msteps_trans; [exact RUN12|]. eapply msteps_trans; [exact RUN13|]. eapply msteps_trans; [exact RUN14|].
           eapply msteps_trans; [exact RUN15|]. exact RUN16. }
  split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; f_equal; lia|]. split; [unfold R16; gres; reflexivity|].
  split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
  split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
  split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
  split; [eapply mem_grows_trans; [exact G815|exact G1516]|].
  split. { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A815 A1516)|]. unfold art_postL_fp. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
  split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - Bh12_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - Bh14_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - Bid_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
  assert (A1316 : art_agree ([(sp - 128 - 64, 64); (t + 2800, 112)] ++ [(ab + rz, 4096)] ++ [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)]) M13 M16)
    by (exact (art_agree_trans _ _ _ _ _ A1314 (art_agree_trans _ _ _ _ _ A1415 A1516))).
  assert (GSH : forall y, 0 <= y < 512 * q ->
            art_gap ([(sp - 128 - 64, 64); (t + 2800, 112)] ++ [(ab + rz, 4096)] ++ [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)]) (2147450880 + ab / 8 + y) 1).
  { intros y Hy. unfold hid in Hmem. clear - Hy Atsh Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
  split.
  - intros j Hj.
    assert (C12 : cellA M12 (2147450880 + ab / 8 + 2 * qz + j) 1 0).
    { unfold M12. rewrite Hn888, Hub8. unfold SB. replace (2147450880 + ab / 8 + 2 * qz + j) with (2147450880 + (512 * ka + 2 * qz) + j) by (rewrite Hab8; lia).
      apply cell_Wf_in; [clear - Eka Hab Hqz; lia|rewrite Z2Nat.id by lia; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia|rewrite Z2Nat.id by lia; lia|lia]. }
    apply (art_cell_tr1 _ M13 M16 _ _ _ A1316).
    + split; [|cbn; clear - Hab8 Eka Hab Hab' Hqz Hj Hq Hnd End Hrs Hn En Hm8 Erz; lia]. replace (2147450880 + ab / 8 + 2 * qz + j) with (2147450880 + ab / 8 + (2 * qz + j)) by lia.
      apply GSH. clear - Hj Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia.
    + unfold M13. apply cell_d1_other; [rewrite Hd1; clear - Eka Hab Hqz Hn En Hm8; lia|rewrite Hd1; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia
                                       |clear - Hab8 Eka Hab Hqz Hj; lia|cbn; clear - Hab8 Eka Hab' Hqz Hj Hq Hnd End Hrs Hn En Hm8 Erz; lia
                                       |intros _; rewrite Hd1, Hab8; unfold apart; cbn; clear - Hj; lia|exact C12].
  - split; [|split; [unfold R16; gres; apply R15; [mk|d2k|dk|exact R12_3]|unfold R16; gres; rewrite Q4; apply R15; [mk|d2k|dk|exact R12_4]]].
    intros Hm. 
    assert (C13 : cellA M13 (2147450880 + ab / 8 + 2 * qz + qn) 1 m8).
    { unfold M13, art_d1_mem. rewrite Hnm. destruct (Z.eqb_spec m8 0) as [E|NE]; [contradiction|]. rewrite Hd1.
      replace (2147450880 + ab / 8 + 2 * qz + qn) with (2147450880 + 512 * ka + 2 * qz + qn) by (rewrite Hab8; lia).
      apply cell_Wn_hit; [clear - Eka Hab Hqz Hn En Hm8; lia|cbn; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. }
    apply (art_cell_tr1 _ M13 M16 _ _ _ A1316); [|exact C13].
    split; [|cbn; clear - Hab8 Eka Hab Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. replace (2147450880 + ab / 8 + 2 * qz + qn) with (2147450880 + ab / 8 + (2 * qz + qn)) by lia.
    apply GSH. clear - Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia.
Qed.
End FPX.

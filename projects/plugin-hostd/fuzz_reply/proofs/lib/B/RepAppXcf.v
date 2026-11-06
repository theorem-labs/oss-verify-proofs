(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppXcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 e2ac69863a2e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); 1 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, the class-full report walk, slice F4 / RepF4Append.AppendWalk's H_apart):
   app_apart_of_pre, the layer facts the Append walk uses at an errbuf call (RepAppWcf.v's Hypothesis H_apart, the
   same text), from RepIFcf.errb_call_pre and errb_call_regs APP_STK.
   rule 24: proves no function (kind: invariant lemma, no machine code runs in this file; the lane's reuse search is
   `proof-index UnmapOrDie internal_memset internal_memcpy internal_strlen GetNamedMappingFd IncreaseTotalMmap`,
   2026-10-30T02:55Z, 0 released lemmas).
   - The stack and the grants: RepGluecf's rep_grant_apart / rep_grant_below_ceil and layout_ok (lo_stk_ceil,
     lo_top).
   - The buffer: RepGluecf's rep_buf_apart.  When the buffer is mapped its capacity is positive: the capacity entry
     is the errbuf extent xs_cf ly S, which xs_mapped_cf puts among the model's maps, and every map has a positive
     length (amwf, ARcf's fourth part).
   - The six image words: RepAppcf's rep_pagesize_cells / rep_mmap_cells over the relation's memory held_mem lk mem,
     moved to the machine memory: the held lock word is RegionInfo's, in the primary (above kHighMemBeg), far from
     the image words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG06bcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK13 YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RepIFcf RepAppcf RepGluecf.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* the held lock word is in the primary, so a low cell reads the same through held_mem *)
Lemma held_mem_val_low : forall (ly : alayout) (lk : option Z) (mem : word -> option byte) (H : word -> bool) (a : Z) (n : nat) (v : Z),
layout_ok ly -> lk_ok ly lk -> 0 <= a -> a + Z.of_nat n <= 2 ^ 40 ->
val_mem tfibsegs (mrestrict H (held_mem lk mem)) a n v -> val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros ly lk mem H a n v LO LK Ha Hn V. destruct LK as [->|(c & Hc & ->)]; [exact V|].
intros k Hk. specialize (V k Hk).
pose proof (lo_high ly LO) as [P1 _]. pose proof (lo_space_in ly LO) as [S1 _].
assert (E : in8 (region_lock_addr ly c) (Z_to_bv 64 (a + Z.of_nat k)) = false).
{ unfold in8, region_lock_addr. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  apply Bool.andb_false_intro1, Z.leb_gt. unfold kRegionInfoOff, kHighMemBeg in *. lia. }
unfold mbyte, mrestrict in V |- *. cbn [held_mem] in V. rewrite E in V. exact V.
Qed.

Lemma existsb_filter_ne : forall {X} (f : X -> bool) (l : list X), existsb f l = true -> List.filter f l <> [].
Proof.
intros X f l H E. apply existsb_exists in H as (x & Hx & Hf).
assert (Hin : In x (List.filter f l)) by (apply filter_In; split; assumption). rewrite E in Hin. destruct Hin.
Qed.

Lemma app_apart_of_pre : forall lk Hp ly S W mem md regs,
  errb_call_pre B lk Hp ly S W mem md -> errb_call_regs B APP_STK ly W regs mem ->
  let d := YG0ncf.errb_data_cf ly S in let cap := errb_cap_cf S in let m := mrestrict (w_H W) mem in
  TFIB_IMG_END + APP_STK <= spZ regs /\ ly_stk_hi ly < 2 ^ 64 /\ 0 <= errb_size_cf S /\ cf_nob < 2 ^ 47 /\ cap < 2 ^ 47 /\
  0 <= d /\ d + cap <= TASK_SIZE /\ d + cap < 2 ^ 64 /\
  (errb_mapped_cf S = true -> 0 < cap /\ 0 < d /\ d mod 4096 = 0 /\ In (w64 d, w64 cap) (vm_maps (m_vmmaps md))) /\
  (forall i, 0 <= i < cap -> off_img (d + i) /\ (d + i < spZ regs - APP_STK \/ ly_stk_hi ly <= d + i)) /\
  (forall (a : word) n, 0 < n -> n mod 4096 = 0 -> YK13.grant_ok_na_pin md a n = true ->
     (bv_unsigned a + n <= TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned a) /\
     (bv_unsigned a + n <= spZ regs - APP_STK \/ ly_stk_hi ly <= bv_unsigned a)) /\
  val_mem tfibsegs m 0x103a0 8 0xafffff00000fffff /\
  val_mem tfibsegs m 0x9df30 8 0x1360e0 /\ val_mem tfibsegs m 0x1360e0 8 4096 /\
  val_mem tfibsegs m 0x9df40 8 0x138168 /\ val_mem tfibsegs m 0x13826c 1 0 /\ val_mem tfibsegs m 0x1381f8 8 0.
Proof.
intros lk Hp ly S W mem md regs PRE REGS. cbv zeta.
pose proof PRE as (_ & _ & LO & IC & TS & _ & (LKOK & AR & _) & XM & WFS & _ & _ & _).
pose proof REGS as (_ & _ & _ & _ & _ & HLO & HHI & _).
pose proof AR as (_ & _ & _ & MW & _).
pose proof (lo_stk_ceil ly LO) as STK. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & _). ceil.
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
pose proof (u64_range (getr regs 2)) as Usp. fold (spZ regs) in Usp.
pose proof (rep_buf_apart B lk Hp ly S W mem md (spZ regs) APP_STK PRE HLO) as BA. cbv zeta in BA.
destruct BA as (_ & _ & _ & BC).
pose proof (errb_cap_cf_nonneg S) as C0.
pose proof (errb_size_nonneg_cf _ _ _ _ S WFS) as SZ0.
pose proof cf_nob_ok as NOB.
assert (DB : 0 <= YG0ncf.errb_data_cf ly S /\ YG0ncf.errb_data_cf ly S + errb_cap_cf S <= ASAN_CEIL).
{ destruct BC as [[E1 E2]|(_ & D2 & _ & D4 & _)]; unfold ASAN_CEIL in *; lia. }
(* mapped: the capacity entry is the errbuf extent, one of the model's maps, so its length is positive *)
assert (MP : errb_mapped_cf S = true -> 0 < errb_cap_cf S).
{ intros HM. destruct (last_cap_idx (st_secs S) 0 None) as [i|] eqn:E.
  - assert (INX : In (ly_sec ly i, errb_cap_cf S) (xs_cf ly S)) by (unfold xs_cf; rewrite E; left; reflexivity).
    pose proof (XM _ INX) as MAP. pose proof (proj2 MW _ MAP) as P. unfold wiv, w64 in P. cbn [snd] in P.
    rewrite Z_to_bv_unsigned, bv_wrap_small in P by (unfold bv_modulus, ASAN_CEIL in *; lia). exact P.
  - exfalso. destruct (rg_last_cap_none _ _ _ E) as [_ F]. exact (existsb_filter_ne _ _ HM F). }
assert (LOWV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 40 ->
  val_mem tfibsegs (mrestrict (w_H W) (held_mem lk mem)) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem) a n v)
  by (intros a n v Ha Hn V; exact (held_mem_val_low ly lk mem (w_H W) a n v LO LKOK Ha Hn V)).
destruct (rep_pagesize_cells B Hp ly S W (held_mem lk mem) md TS AR) as (VP1 & VP2 & VP3).
destruct (rep_mmap_cells B Hp ly S W (held_mem lk mem) md TS AR) as (VM1 & VM2 & VM3).
unfold spZ, APP_STK, TFIB_IMG_END, ASAN_CEIL, kHighMemEnd in *.
split; [lia|]. split; [lia|]. split; [exact SZ0|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [rewrite HT; lia|]. split; [lia|].
split.
{ intros HM. pose proof (MP HM) as CP. destruct BC as [[E1 E2]|(D1 & D2 & D3 & D4 & D5)]; [lia|].
  split; [exact CP|]. split; [lia|]. split; [exact D1 | exact D5]. }
split.
{ intros i Hi. destruct BC as [[E1 E2]|(D1 & D2 & D3 & D4 & D5)]; [lia|].
  split; [unfold off_img, TFIB_IMG_LO, TFIB_IMG_END in *; lia | left; lia]. }
split.
{ intros a n Hn Hal G.
  assert (G' : YK13.grant_ok_na_pin md (w64 (bv_unsigned a)) n = true) by (unfold w64; rewrite Z_to_bv_bv_unsigned; exact G).
  pose proof (u64_range a) as Ua.
  destruct (rep_grant_apart B lk Hp ly S W mem md n (bv_unsigned (getr regs 2)) 512 PRE Hn Hal HLO ltac:(lia) (bv_unsigned a) G') as (GI & _ & _).
  destruct (rep_grant_below_ceil B lk Hp ly S W mem md n PRE Hn Hal (bv_unsigned a) Ua G') as (GC & _).
  split; [exact GI | left; unfold ASAN_CEIL in GC; lia]. }
split; [eapply LOWV; [lia | cbn; lia | exact VP3]|].
split; [eapply LOWV; [lia | cbn; lia | exact VP1]|].
split; [eapply LOWV; [lia | cbn; lia | exact VP2]|].
split; [eapply LOWV; [lia | cbn; lia | exact VM1]|].
split; [eapply LOWV; [lia | cbn; lia | exact VM2]|].
eapply LOWV; [lia | cbn; lia | exact VM3].
Qed.
End a.

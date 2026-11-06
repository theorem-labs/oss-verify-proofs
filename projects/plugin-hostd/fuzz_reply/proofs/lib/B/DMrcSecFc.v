(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecFc.v (commit 6fdbdd538bcf, H4 flag-free secondary Recycle walk set; file sha256 fc38cbf5add2) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 26 image addresses moved by code-verified function pairs (27 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; 1 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecFc.v at commit edc7f827e38, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (27 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; interface DMwalkIF.v at dc3949af11c): the CUT-READ record of the
   SECONDARY arm of __asan::QuarantineCallback::Recycle (0x33e88), i.e. LargeMmapAllocator::Deallocate's walk.
   rule 24: no function proved here (kind: field statements; the walk is DMrcSec.v).
   WHY.  cgif derives every fact the secondary walk reads from ARm (YFfc.v, plus YFf4's MAPX / SX / SECX / LST): the layout,
   the map's geometry and header, the secondaries array and its last slot, the allocator / thread / TLS words, the presence
   of the read bytes and the first segment's premise record (YFgu.free_hyps).  Over an opaque cut relation those are READ
   FIELDS: [sec_cut] collects them with YFfc's own statements (so the walk's glue is YFfc's, unchanged), except that the
   cgif-only size bounds are gone: the map length's 2 ^ 29 and the user size's 2 ^ 28 come from DMwalkIF.lmaxd_ok /
   nmaxd_ok at the use (DMrcSecF6.v, ...), never from the cut.  At cgif these are YFfc's lemmas; at cf CfF2b discharges
   them at ARXr_cf. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFgx YFgv YFg8 YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFfc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, YFgu.GFRAME, YFgx.GFRAME, GDEPTH in *.
Section f.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Local Notation sp0 := (bv_unsigned (getr regs 2)).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation arr := (st_sec_arr X).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation hdr := (YFfc.hdr B ly k).
Local Notation HWv := (YFfc.HWv B ly k W mem).
Local Notation j1 := (YFfc.j1 ly W mem).
Local Notation j2 := (YFfc.j2 ly W mem).
Local Notation ji1 := (YFfc.ji1 W mem).
Local Notation ji2 := (YFfc.ji2 W mem).
Local Notation ji3 := (YFfc.ji3 W mem).
Local Notation ji4 := (YFfc.ji4 W mem).
Local Notation j5 := (YFfc.j5 ly W mem).
Local Notation j6 := (YFfc.j6 ly W mem).
Local Notation lastr := (last (st_sec_arr X) r).
Local Notation lst := (YFg8.lst ly X r).
Local Notation own := (YFg8.own X i).
Record sec_cut : Prop := SecCut {
sc_LO : layout_ok ly;
sc_IMG : img_cover ly;
sc_Hk : In k (st_chunks X);
sc_HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly;
sc_HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 Q kPtrArrayResv /\ Q + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ ASAN_CEIL <= ly_stk_lo ly /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ as_inst B = TFIB_INST /\
Q mod 4096 = 0 /\ T mod 4096 = 0 /\ ly_C ly mod 8 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\ (ly_C ly + 256 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= ly_C ly) /\
(Q + kPtrArrayResv <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= Q) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (T + kThreadObjSize <= Q \/ Q + kPtrArrayResv <= T) /\ (ly_C ly + 256 <= Q \/ Q + kPtrArrayResv <= ly_C ly);
sc_ARRF : In r arr /\ (i < length arr)%nat /\ List.NoDup arr /\ 1 <= nA <= 16384 /\ 0 <= Z.of_nat i < nA;
sc_GEOM : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\ 8192 <= LEN /\ LEN mod 4096 = 0 /\
ck_base B ly k = MAP + kPage /\ ck_extent k = LEN - kPage;
sc_hdr : hdr = MAP + 6128 /\ hdr + 16 + ck_n k <= MAP + LEN /\ hdr mod 16 = 0 /\ 0 <= ck_req k;
sc_slot_geom : forall j rj, nth_error arr j = Some rj ->
exists y, In y (st_chunks X) /\ ck_beg y = PSec rj kPage /\ In (ly_sec ly rj, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 (ly_sec ly rj) (sec_map_size (ck_req y)) /\ ly_sec ly rj + sec_map_size (ck_req y) <= ASAN_CEIL /\ ly_sec ly rj mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(ly_sec ly rj <> MAP -> ly_sec ly rj + sec_map_size (ck_req y) <= MAP \/ MAP + LEN <= ly_sec ly rj);
sc_slot_val : forall j rj, nth_error arr j = Some rj ->
val_mem tfibsegs m0 (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj) /\ (forall a, Q + 8 * Z.of_nat j <= a < Q + 8 * Z.of_nat j + 8 -> apresent H0 mem a);
sc_ELEN : LEN = sec_map_size (ck_req k) /\ o = kPage /\ sm_live sm = true;
sc_const_vals : val_mem tfibsegs m0 0x9df40 8 0x138168 /\ val_mem tfibsegs m0 0x1381e0 8 0xffffffffffffffff /\ val_mem tfibsegs m0 0x1381f8 8 0 /\
val_mem tfibsegs m0 0x9df50 8 0xa6638 /\ val_mem tfibsegs m0 0xa6638 8 0x7fff8000 /\
val_mem tfibsegs m0 0x9df58 8 0xa7328 /\ val_mem tfibsegs m0 0x9df60 8 0xa7330 /\ val_mem tfibsegs m0 0x9df68 8 0xa7320 /\
val_mem tfibsegs m0 0xa7320 8 0x7fffffffffff /\ val_mem tfibsegs m0 0xa7328 8 0 /\ val_mem tfibsegs m0 0xa7330 8 0 /\
val_mem tfibsegs m0 0x9df70 8 0x9fdf0 /\ val_mem tfibsegs m0 0x9fdf0 8 0x96e80 /\
val_mem tfibsegs m0 0x9df30 8 0x1360e0 /\ val_mem tfibsegs m0 0x1360e0 8 4096 /\ val_mem tfibsegs m0 0x9df90 8 1;
sc_inst_vals : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfibsegs m0 (A_ALLOCATOR + 64) 8 4096 /\
val_mem tfibsegs m0 (A_ALLOCATOR + 72) 8 Q /\ val_mem tfibsegs m0 (A_ALLOCATOR + 120) 8 nA;
sc_junkD_vals : (0 <= ji1 < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 144) 8 ji1) /\ (0 <= ji2 < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 152) 8 ji2) /\
(0 <= ji3 < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 704) 8 ji3) /\ (0 <= ji4 < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 712) 8 ji4) /\
(0 <= j5 < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 88) 8 j5) /\ (0 <= j6 < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 96) 8 j6);
sc_last_facts : nth_error arr (length arr - 1) = Some lastr /\
val_mem tfibsegs m0 (Q + 8 * (nA - 1)) 8 lst /\ (forall a, Q + 8 * (nA - 1) <= a < Q + 8 * (nA - 1) + 8 -> apresent H0 mem a) /\
val_mem tfibsegs m0 (lst + 24) 8 (nA - 1) /\ (forall a, lst + 24 <= a < lst + 32 -> apresent H0 mem a) /\
zone3 lst 8192 /\ lst + 8192 <= ASAN_CEIL /\ lst mod 4096 = 0 /\
(if own then Z.of_nat i = nA - 1 /\ lst = MAP else lst + 4096 <= MAP \/ MAP + LEN <= lst);
sc_maph_vals : val_mem tfibsegs m0 MAP 8 MAP /\ val_mem tfibsegs m0 (MAP + 8) 8 LEN /\ val_mem tfibsegs m0 (MAP + 16) 8 (needed_size (ck_req k)) /\
val_mem tfibsegs m0 (MAP + 24) 8 (Z.of_nat i) /\ (forall a, MAP <= a < MAP + 32 -> apresent H0 mem a);
sc_qi_val : val_mem tfibsegs m0 (Q + 8 * Z.of_nat i) 8 MAP /\ (forall a, Q + 8 * Z.of_nat i <= a < Q + 8 * Z.of_nat i + 8 -> apresent H0 mem a);
sc_shadow_present : forall a, SHAv MAP <= a < SHAv MAP + CNTv LEN -> apresent H0 mem a;
sc_thread_present : forall a, T <= a < T + kThreadObjSize -> apresent H0 mem a;
sc_tls_vals : val_mem tfibsegs m0 0xa5ea0 1 1 /\ val_mem tfibsegs m0 0xa5ea4 4 0 /\ val_mem tfibsegs m0 (TFIB_TP - 88) 8 TFIB_TSD /\
val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly) /\ val_mem tfibsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfibsegs m0 (ly_C ly + 152) 8 T;
sc_hw_val : val_mem tfibsegs m0 hdr 4 HWv /\ val_mem tfibsegs m0 (hdr + 4) 4 (ck_n k) /\ (forall a, hdr <= a < hdr + 8 -> apresent H0 mem a) /\ 0 <= HWv < 65536;
sc_junk_vals : (0 <= j1 < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 40) 8 j1) /\ (0 <= j2 < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 48) 8 j2);
sc_MAPX : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint (YFf4.MAP ly r, YFf4.LEN k) y;
sc_SX : forall i0 j x0 y, nth_error (static_extents ly) i0 = Some x0 -> nth_error (static_extents ly) j = Some y -> i0 <> j -> zdisjoint x0 y;
sc_SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y;
sc_LST : exists y, In y (st_chunks X) /\ ck_beg y = PSec (YFf4.lastr X r) kPage /\ In (YFf4.lst ly X r, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 (YFf4.lst ly X r) (sec_map_size (ck_req y)) /\ YFf4.lst ly X r + sec_map_size (ck_req y) <= ASAN_CEIL /\ YFf4.lst ly X r mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(YFf4.own X i = false -> zdisjoint (YFf4.lst ly X r, sec_map_size (ck_req y)) (YFf4.MAP ly r, YFf4.LEN k));
sc_FH_A : YFgu.free_hyps W ly regs mem hdr nA Q
}.
End f.
Section w.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis SC : sec_cut B ly X k W regs mem r o sm i.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation hdr := (YFfc.hdr B ly k).
(* YFfc.GEOM with the map length bounded through lmaxd_ok (ck_extent k = LEN - kPage <= LMAXD <= 2 ^ 30). *)
Lemma GEOMw : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\ 8192 <= LEN < 2 ^ 31 /\ LEN mod 4096 = 0 /\
ck_base B ly k = MAP + kPage /\ ck_extent k = LEN - kPage.
Proof.
pose proof (sc_GEOM _ _ _ _ _ _ _ _ _ _ _ SC) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
unfold DMwalkIF.lmaxd_ok in LOK.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [split; [exact G4|]|].
{ rewrite G7 in HE. unfold kPage in HE. lia. }
split; [exact G5|]. split; [exact G6 | exact G7].
Qed.
(* YFfc.hdr_facts with the user size bounded through nmaxd_ok (ck_n k = req_size (ck_req k) < NMAXD <= 2 ^ 30). *)
Lemma hdr_factsw : hdr = MAP + 6128 /\ 1 <= ck_n k < 2 ^ 31 /\ hdr + 16 + ck_n k <= MAP + LEN /\ hdr mod 16 = 0 /\ 0 <= ck_req k < 2 ^ 31.
Proof.
pose proof (sc_hdr _ _ _ _ _ _ _ _ _ _ _ SC) as (D1 & D2 & D3 & D4).
unfold DMwalkIF.nmaxd_ok in NOK.
assert (R : 1 <= ck_n k /\ ck_req k <= ck_n k) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
split; [exact D1|]. split; [lia|]. split; [exact D2|]. split; [exact D3|]. lia.
Qed.
End w.
End c.

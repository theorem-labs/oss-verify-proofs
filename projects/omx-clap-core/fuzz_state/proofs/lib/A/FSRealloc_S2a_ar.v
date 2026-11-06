(* fuzz_state image A (projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan,
   sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0): the ALLOCATOR-INVARIANT side of the
   realloc thin segment S2a (FSRealloc_inst.FS_seg_mid_a: Allocate's return 0x32994 -> `jalr a3` 0x32a08 ->
   musl memcpy 0x98a20).  FSRealloc_S2a.v consumes these lemmas; the machine walk is FSRealloc_S2a_walk.v.

   Rule 24 (released-proof lookup): a Theorem Labs lane (internal path; ossv proof
   index v5, 2026-10-28T21:58:24Z, ossv/recipes@566eb6ffa5df) answered CONFIRM: no released ASan-image proof of any
   fuzz_state function.  The released donor of this step is cgif_rgb_fuzzer's lib/YF78.v:220-249 (`hdr_facts`, over
   YF1w's hw_val / hb1_facts / p_zone / cell_lit).  The facts here are fs's own in-tree lemmas, lifted; where the
   in-tree lemma sits in a file that Requires lib/A/AFex.v (AFf0, AFfu, AFg1), which does not build at this tree
   (AFex.v:244 batch_geom), its proof script is restated inline over the same lib/Reusable / AF0x facts:
     - the chunk of a live block and its header cells: lib/A/AFg1.v:63-72 (kk, kk_facts, KF, Epa, Enn),
       :116-117 (hdr_In), :128-140 (hw_val's V0 / V2 / V4); the same block is lib/A/AFfu.v:112-121, :171-172,
       :183-195.  Its parts: lib/Reusable/YG03.v:48 find_user_block, lib/Reusable/YG0s.v:226 cfacts / :240
       chunk_facts, lib/Reusable/YG0n.v:49-53 hdr_state / chunk_cells, :118 acells, ARm's am_cells / am_wf,
       lib/A/AF0x.v:106 cell_holds_val_mem; the address of a header cell is lib/A/AFf0.v:286-295 (EA / EA2, as
       AFg1.v:123, :132, :134 use them), restated inline.
     - the zone of the header + user bytes: lib/A/AFf0.v:97-104 ZCH (zone3 of the chunk's extent, from
       lib/A/AF0x.v:66 zone3_intro + lib/Reusable/YG0s.v:287 chunk_apart + AFf0.v:92-96 zdisjoint_of_pointwise),
       restated inline, narrowed to [pa - 16, pa + req_size n) as lib/A/AFg1.v:269-273 / lib/A/AFfu.v:379-385
       (p_zone) narrow it; img_cover from lib/A/AF0x.v:55 img_cover_of_ledger, as lib/A/AFfu.v:325-326 (IMG).
     - the two image cells: lib/A/AF0x.v:207 tfib_const_lookup, the pattern of lib/A/AFg1.v:88-89 (cell_lit), over
       the start-up certificate rows lib/A/AF0m.v:180 (`z8 (ANum 0x9f718) 0xa1568`) and :96
       (`z8 (ANum 0xa1568) 0x98a20`), used where they stand.
     - the unpoison bridge: lib/A/FSupoison.v:136 ush_facts (every user-poisoned shadow address is in
       [SHADOW_OFF, kHighMemBeg)), :65 unpoison_out, :164 ARU_view_out, :63 wz.

   DISASSEMBLY of the pinned image A (python3 + capstone 5.0.7, CS_ARCH_RISCV / CS_MODE_RISCV64, no compressed
   instructions), Reallocate's S2a window:
     0x32994 `mv s4, a0`            (00050a13)  Allocate's return value (the new block) kept in s4
     0x3299c `lb a0, -0x10(s1)`     (ff048503)  the old chunk's state byte, s1 = old user pointer pa: pa - 16
     0x329a0 `addi a1, zero, 2`     (00200593)  CHUNK_ALLOCATED
     0x329a8 `beq a0, a1, 0x2c`     (02b50663)  -> 0x329d4 when the state byte is 2
     0x329d4 `auipc a0, 0x6d`       (0006d517)  a0 = 0x329d4 + 0x6d000 = 0x9f9d4
     0x329d8 `ld a0, -0x2bc(a0)`    (d4453503)  GOT slot 0x9f9d4 - 0x2bc = 0x9f718 (.got), holds 0xa1568
     0x329dc `ld a3, 0(a0)`         (00053683)  REAL(memcpy) cell 0xa1568 (.data), holds 0x98a20
     0x329e4 `lhu a0, -0xe(s1)`     (ff24d503)  UsedSize high half: pa - 14, 2 bytes
     0x329e8 `lwu a1, -0xc(s1)`     (ff44e583)  UsedSize low half: pa - 12, 4 bytes
     0x32a08 `jalr a3`              (000680e7)  REAL(memcpy)
     0x98a20 `andi a3, a1, 3`       (0035f693)  musl memcpy's entry (.text): the source-alignment test
   The image bytes at 0x9f718 (LE u64) are 0xa1568 and at 0xa1568 are 0x98a20, as AF0m.v:180 / :96 state.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
(* A range none of whose points lies in [e] is disjoint from [e]: lib/A/AFf0.v:92-96 (zdisjoint_of_pointwise), restated
   here because AFf0.v Requires lib/A/AFex.v, which does not build at this tree (AFex.v:244 batch_geom). *)
Lemma s2a_zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) ->
  zdisjoint (a, s) e.
Proof.
intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* The chunk header of a live block: state byte 2 = CHUNK_ALLOCATED at pa-16 (0x3299c `lb a0, -0x10(s1)`), the
   UsedSize halves at pa-14 (0x329e4 `lhu a0, -0xe(s1)`) and pa-12 (0x329e8 `lwu a1, -0xc(s1)`), and the header +
   user bytes off the image.  AFg1.v:63-72, :116-117, :128-140 and AFf0.v:97-104 (ZCH) / :286-295 (EA, EA2), lifted
   out of their sections and restated inline (AFf0 / AFg1 / AFfu Require AFex.v, which does not build here). *)
Lemma s2a_hdr : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (blocks S) ->
  AF0x.zone3 (sptr_addr B ly p - 16) (req_size n + 16) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 1 2 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 14) 2 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n).
Proof using TB.
intros ly S W mem md p n HAR HBLK.
pose proof (proj1 HAR) as M.
assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly S md (proj1 (proj2 HAR))).
pose proof (am_wf B ly S _ M) as WF.
destruct (find_user_block _ 0 0 0 S p n WF HBLK) as (k & _ & Hk & Hst & Hu & Hr).
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (Epa : sptr_addr B ly p = ck_base B ly k + ck_rz k) by (rewrite <- Hu; exact G4).
assert (Enn : req_size n = ck_n k) by (unfold ck_n; rewrite Hr; reflexivity).
assert (HIN : forall c, In c (chunk_cells k) -> In c (acells B ly S)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk | exact Hc]. }
assert (CS : forall c e (w : nat) x, In c (chunk_cells k) -> c = ACell e w (AV (ANum x)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w x).
{ intros c e w x Hc ->. apply (cell_holds_val_mem B ly (w_H W) mem e w (ANum x)).
  exact (proj1 (Forall_forall _ _) (am_cells B ly S _ M) _ (HIN _ Hc)). }
(* AFf0.v:286-295 (EA / EA2): ck_beg is PPrim or PSec (cfacts), so the header-cell expressions evaluate to
   ck_base + offset; the YG0f.v:252 aeval_aoff side condition (not ASh) holds by construction. *)
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. clear - GG. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c q]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. clear - GG. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c q]; try solve [destruct GG]; cbn; lia. }
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = sptr_addr B ly p - 16).
{ rewrite EA, Epa. unfold kChunkHeaderSize. lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = sptr_addr B ly p - 16 + d).
{ intros d. rewrite EA2, Epa. unfold kChunkHeaderSize. lia. }
(* AFf0.v:97-104 (ZCH): the chunk's extent is a zone3 range. *)
assert (ZK : zone3 (ck_base B ly k) (ck_extent k)).
{ pose proof (am_layout B ly S _ M) as LO.
  pose proof (req_size_bounds (ck_req k) ltac:(clear - G7; lia)) as (_ & Q1 & _).
  apply (zone3_intro ly (ck_base B ly k) (ck_extent k) IMG ltac:(clear - G5 G8 Q1; lia) G1).
  apply s2a_zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
  intros y Hy. exact (proj1 (chunk_apart B ly S _ k y M Hk Hy)). }
split; [|split; [|split]].
- rewrite Epa, Enn. unfold ck_n. clear - ZK G5 G8.
  unfold zone3, zone3cases in *. lia.
- rewrite <- EH. eapply CS; [unfold chunk_cells; apply in_app_iff; left; left; reflexivity|].
  unfold z1, c1, hdr_state. rewrite Hst. reflexivity.
- replace (sptr_addr B ly p - 14) with (sptr_addr B ly p - 16 + 2) by lia. rewrite <- (EH2 2).
  eapply CS; [unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity|]. reflexivity.
- replace (sptr_addr B ly p - 12) with (sptr_addr B ly p - 16 + 4) by lia. rewrite <- (EH2 4), Enn.
  eapply CS; [unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity|]. reflexivity.
Qed.

(* The GOT slot and the REAL(memcpy) cell: 0x329d4 `auipc a0, 0x6d` (0006d517) + 0x329d8 `ld a0, -0x2bc(a0)`
   (d4453503) read the .got slot 0x9f718, which holds 0xa1568; 0x329dc `ld a3, 0(a0)` (00053683) reads the .data cell
   0xa1568, which holds 0x98a20 (musl memcpy, 0x98a20 `andi a3, a1, 3` (0035f693)).  Rows AF0m.v:180 and :96 of fs's
   start-up certificate, read by AF0x.v:207 tfib_const_lookup as AFg1.v:88-89 (cell_lit) reads them. *)
Lemma s2a_cells : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9f718 8 0xa1568 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1568 8 0x98a20.
Proof.
intros ly S W mem md HAR. pose proof (proj1 HAR) as M.
split; apply (tfib_const_lookup B TB ly S (w_H W) mem _ _ _ M); vm_compute; reflexivity.
Qed.

(* User poison lives in the shadow band only (FSupoison.v:136 ush_facts: [SHADOW_OFF, kHighMemBeg)), so no address
   below kLowShadowBeg or at / above kHighMemBeg is a user-poisoned shadow byte. *)
Lemma s2a_ush_out : forall ly S Up (W : world tfibsegs) mem md s,
  FSupoison.ARU tfibsegs B ly S Up W mem md -> (s < kLowShadowBeg \/ kHighMemBeg <= s) ->
  FSupoison.in_ush Up s = false.
Proof.
intros ly S Up W mem md s H Hs. destruct (FSupoison.in_ush Up s) eqn:E; [|reflexivity]. exfalso.
pose proof (FSupoison.ush_facts tfibsegs B ly S Up W mem md s H E) as (_ & L1 & L2).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The memory-level bridge: application memory reads the same through `unpoison` (FSupoison.v:24, :65). *)
Lemma s2a_unpoison_mem : forall ly S Up (W : world tfibsegs) mem md (x : word),
  FSupoison.ARU tfibsegs B ly S Up W mem md ->
  (bv_unsigned x < kLowShadowBeg \/ kHighMemBeg <= bv_unsigned x) ->
  FSupoison.unpoison Up mem x = mem x.
Proof.
intros ly S Up W mem md x H Hx. apply FSupoison.unpoison_out. exact (s2a_ush_out ly S Up W mem md _ H Hx).
Qed.

(* The reader-level bridge (FSupoison.v:164 ARU_view_out). *)
Lemma s2a_unpoison_view : forall ly S Up (W : world tfibsegs) mem md a,
  FSupoison.ARU tfibsegs B ly S Up W mem md -> 0 <= a < 2 ^ 64 ->
  (a < kLowShadowBeg \/ kHighMemBeg <= a) ->
  aview tfibsegs (w_H W) (FSupoison.unpoison Up mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S Up W mem md a H Ha Hz. symmetry. apply (FSupoison.ARU_view_out tfibsegs B ly S Up W mem md a H).
rewrite (FSupoison.wz a Ha). exact (s2a_ush_out ly S Up W mem md a H Hz).
Qed.
End A.

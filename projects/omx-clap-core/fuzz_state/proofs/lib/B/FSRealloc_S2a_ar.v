(* fuzz_state image B (projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan-ubsan,
   sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the ALLOCATOR-INVARIANT side of the
   realloc thin segment S2a (lib/B/FSRealloc_inst.v FS_seg_mid_a: Allocate's return 0x32a04 -> `jalr a3` 0x32a78 ->
   musl memcpy 0x98f3c).  FSRealloc_S2a.v consumes these lemmas; the machine walk is FSRealloc_S2a_walk.v.

   The B twin of lib/A/FSRealloc_S2a_ar.v (a working branch 98113525978), which is the template: the
   same statements and scripts over image B's modules (lib/B/YB1v, YF0m, YF0x for A's AB1v, AF0m, AF0x) and B's two
   REAL(memcpy) cells.  A's file restates in-tree lemmas of lib/A/AFg1.v / AFfu.v / AFf0.v; their B twins are
   lib/B/YFg1.v:61-65 (kk, kk_facts), :86-87 (cell_lit), :114-115 (hdr_In) and lib/B/YFfu.v:111-115, :142-143,
   :170-171, which Require lib/B/YFex.v; the restatement keeps this file off that chain, as A's keeps off AFex.v.
   The released donor of this step is cgif_rgb_fuzzer's lib/YF78.v:220-249 (`hdr_facts`, over YF1w's hw_val /
   hb1_facts / p_zone / cell_lit).

   Rule 24 (released-proof lookup): proof-index by NAME and by the B addresses 0x530e8 / 0x534e4, unpiped,
   2026-10-29 03:50-03:56Z (internal path, 0x534e4.txt): 0 named, 0 by
   address, 0 related, 0 lemmas; named cold branches (r24/1029/cold-search.md, 725 refs): the only other holder is
   fs's pre-ruling bespoke line, a template only (owner ruling a Theorem Labs lane 04:50Z).

   CLOSURE: the only lib/A file Required is FSupoison.v (image-free).

   The parts used:
     - the chunk of a live block and its header cells: lib/Reusable/YG03.v find_user_block, lib/Reusable/YG0s.v
       cfacts / chunk_facts, lib/Reusable/YG0n.v hdr_state / chunk_cells / acells, ARm's am_cells / am_wf,
       lib/B/YF0x.v:104 cell_holds_val_mem; the address of a header cell (EA / EA2), restated inline.
     - the zone of the header + user bytes: lib/B/YF0x.v:64 zone3_intro + lib/Reusable/YG0s.v chunk_apart +
       s2a_zdisjoint_of_pointwise below, narrowed to [pa - 16, pa + req_size n); img_cover from lib/B/YF0x.v:53
       img_cover_of_ledger.
     - the two image cells: lib/B/YF0x.v:205 tfib_const_lookup over B's start-up certificate rows (lib/B/YF0m.v:183
       `z8 (ANum 0x9fc38) 0xa1a88` and :99 `z8 (ANum 0xa1a88) 0x98f3c`).  B's table of record, a Theorem Labs lane's
       startup/regenB/YF0m.new4.v (sha256 263176a3615f3579...), carries the same two rows (:181 and :97).
     - the unpoison bridge: lib/A/FSupoison.v ush_facts (every user-poisoned shadow address is in
       [SHADOW_OFF, kHighMemBeg)), unpoison_out, ARU_view_out, wz.

   DISASSEMBLY of the pinned image B (python3 + capstone 5.0.7, CS_ARCH_RISCV / CS_MODE_RISCV64, no compressed
   instructions), Reallocate's S2a window:
     0x32a04 `mv s4, a0`            (00050a13)  Allocate's return value (the new block) kept in s4
     0x32a0c `lb a0, -0x10(s1)`     (ff048503)  the old chunk's state byte, s1 = old user pointer pa: pa - 16
     0x32a10 `addi a1, zero, 2`     (00200593)  CHUNK_ALLOCATED
     0x32a18 `beq a0, a1, 0x2c`     (02b50663)  -> 0x32a44 when the state byte is 2
     0x32a44 `auipc a0, 0x6d`       (0006d517)  a0 = 0x32a44 + 0x6d000 = 0x9fa44
     0x32a48 `ld a0, 0x1f4(a0)`     (1f453503)  GOT slot 0x9fa44 + 0x1f4 = 0x9fc38 (.got), holds 0xa1a88
     0x32a4c `ld a3, 0(a0)`         (00053683)  REAL(memcpy) cell 0xa1a88 (.data), holds 0x98f3c
     0x32a54 `lhu a0, -0xe(s1)`     (ff24d503)  UsedSize high half: pa - 14, 2 bytes
     0x32a58 `lwu a1, -0xc(s1)`     (ff44e583)  UsedSize low half: pa - 12, 4 bytes
     0x32a78 `jalr a3`              (000680e7)  REAL(memcpy)
     0x98f3c `andi a3, a1, 3`       (0035f693)  musl memcpy's entry (.text): the source-alignment test
   The image bytes at 0x9fc38 (LE u64) are 0xa1a88 and at 0xa1a88 are 0x98f3c, as YF0m.v:183 / :99 state.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
(* A range none of whose points lies in [e] is disjoint from [e] (lib/B/YFf0.v's zdisjoint_of_pointwise, restated
   here because YFf0.v Requires lib/B/YFex.v; A's template restates AFf0.v:92-96 for the same reason). *)
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

(* The chunk header of a live block: state byte 2 = CHUNK_ALLOCATED at pa-16 (0x32a0c `lb a0, -0x10(s1)`), the
   UsedSize halves at pa-14 (0x32a54 `lhu a0, -0xe(s1)`) and pa-12 (0x32a58 `lwu a1, -0xc(s1)`), and the header +
   user bytes off the image (the template's script, A's FSRealloc_S2a_ar.v:75-122). *)
Lemma s2a_hdr : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (blocks S) ->
  YF0x.zone3 (sptr_addr B ly p - 16) (req_size n + 16) /\
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
(* EA / EA2: ck_beg is PPrim or PSec (cfacts), so the header-cell expressions evaluate to ck_base + offset; the
   YG0f.v aeval_aoff side condition (not ASh) holds by construction. *)
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. clear - GG. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c q]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. clear - GG. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c q]; try solve [destruct GG]; cbn; lia. }
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = sptr_addr B ly p - 16).
{ rewrite EA, Epa. unfold kChunkHeaderSize. lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = sptr_addr B ly p - 16 + d).
{ intros d. rewrite EA2, Epa. unfold kChunkHeaderSize. lia. }
(* ZCH: the chunk's extent is a zone3 range. *)
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

(* The GOT slot and the REAL(memcpy) cell: 0x32a44 `auipc a0, 0x6d` (0006d517) + 0x32a48 `ld a0, 0x1f4(a0)`
   (1f453503) read the .got slot 0x9fc38, which holds 0xa1a88; 0x32a4c `ld a3, 0(a0)` (00053683) reads the .data cell
   0xa1a88, which holds 0x98f3c (musl memcpy, 0x98f3c `andi a3, a1, 3` (0035f693)).  Rows YF0m.v:183 and :99 of B's
   start-up certificate (new4 :181 and :97), read by YF0x.v:205 tfib_const_lookup as YFg1.v:86-87 (cell_lit) reads
   them. *)
Lemma s2a_cells : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9fc38 8 0xa1a88 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1a88 8 0x98f3c.
Proof.
intros ly S W mem md HAR. pose proof (proj1 HAR) as M.
split; apply (tfib_const_lookup B TB ly S (w_H W) mem _ _ _ M); vm_compute; reflexivity.
Qed.

(* User poison lives in the shadow band only (FSupoison.v ush_facts: [SHADOW_OFF, kHighMemBeg)), so no address
   below kLowShadowBeg or at / above kHighMemBeg is a user-poisoned shadow byte. *)
Lemma s2a_ush_out : forall ly S Up (W : world tfibsegs) mem md s,
  FSupoison.ARU tfibsegs B ly S Up W mem md -> (s < kLowShadowBeg \/ kHighMemBeg <= s) ->
  FSupoison.in_ush Up s = false.
Proof.
intros ly S Up W mem md s H Hs. destruct (FSupoison.in_ush Up s) eqn:E; [|reflexivity]. exfalso.
pose proof (FSupoison.ush_facts tfibsegs B ly S Up W mem md s H E) as (_ & L1 & L2).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The memory-level bridge: application memory reads the same through `unpoison` (FSupoison.v unpoison_out). *)
Lemma s2a_unpoison_mem : forall ly S Up (W : world tfibsegs) mem md (x : word),
  FSupoison.ARU tfibsegs B ly S Up W mem md ->
  (bv_unsigned x < kLowShadowBeg \/ kHighMemBeg <= bv_unsigned x) ->
  FSupoison.unpoison Up mem x = mem x.
Proof.
intros ly S Up W mem md x H Hx. apply FSupoison.unpoison_out. exact (s2a_ush_out ly S Up W mem md _ H Hx).
Qed.

(* The reader-level bridge (FSupoison.v ARU_view_out). *)
Lemma s2a_unpoison_view : forall ly S Up (W : world tfibsegs) mem md a,
  FSupoison.ARU tfibsegs B ly S Up W mem md -> 0 <= a < 2 ^ 64 ->
  (a < kLowShadowBeg \/ kHighMemBeg <= a) ->
  aview tfibsegs (w_H W) (FSupoison.unpoison Up mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S Up W mem md a H Ha Hz. symmetry. apply (FSupoison.ARU_view_out tfibsegs B ly S Up W mem md a H).
rewrite (FSupoison.wz a Ha). exact (s2a_ush_out ly S Up W mem md a H Hz).
Qed.
End A.

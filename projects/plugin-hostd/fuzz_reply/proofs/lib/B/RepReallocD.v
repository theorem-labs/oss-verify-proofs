(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepReallocD.v (commit f01d79f3fb5, cf refill round 3; file sha256 741f9c69e26c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 15 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 14 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 11 pcs named in comments; 1 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, slice F4 of a Theorem Labs lane's class-full report walk, sub-slice Realloc):
   the definitions of the __sanitizer::InternalMmapVectorNoCtor<char, true>::Realloc (0x59e3c) walk of
   cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605): its decode table, its seed state, the premise bundle
   realloc_pre, the post realloc_post, and the statement realloc_tail_spec of the walk's tail (from MmapOrDie's
   return 0x59eac to Realloc's return), which RepReallocBcf.v proves and RepReallocf.v composes.
   rule 24: no function proved here (kind: statement heads and helpers of the Realloc walk; the reuse search of the
   walk is in RepReallocf.v's header: 0 released lemmas for Realloc, MmapOrDie, UnmapOrDie, internal_memcpy).

   The vector object is three words at v: data (v + 0), capacity in bytes (v + 8), size (v + 16).  The body:
   CHECK(new_size) (0x59e50, dead: 0 < nb), CHECK_LE(size, new_size) (0x59e60, dead: sz <= nb), the page-size cache
   0x9e1e8 -> 0x135d20 = 4096 (GetPageSize skipped, the power-of-two check at 0x59e84 dead), ncap = round_up nb 4096,
   MmapOrDie(ncap, "InternalMmapVector", true) (0x6712c), internal_memcpy(new, data, size) (0x651e0),
   UnmapOrDie(data, capacity, true) (0x672ac), data := new, capacity := ncap.  After the grant the fresh map is
   exposed in the world with YG0b.allow_expose (the route of the secondary grant, YFjs.v:604): this needs budget
   room for it (GBUD below). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB15 YFff.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YG0b YFfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RepMmapcf RepUnmapcf RepMemKcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.

(* The decode table of Realloc's 63 instructions (0x59e3c .. 0x59f38). *)
Definition tbl_rea_build : ctable := build_table tfibsegs 0x59e3c 63%nat TEmpty.
Definition tbl_rea : ctable := Eval vm_compute in tbl_rea_build.
Lemma tbl_rea_eq : tbl_rea = tbl_rea_build.
Proof. vm_cast_no_check (@eq_refl ctable tbl_rea). Qed.
Lemma tbl_rea_ok : table_ok tfibsegs tbl_rea.
Proof. rewrite tbl_rea_eq. unfold tbl_rea_build. apply build_table_ok0. cbv. discriminate. Qed.

Definition A_REALLOC : Z := 0x59e3c.
Definition A_MOD : Z := 0x6712c.
(* Stack windows: Realloc's frame 0x20; MmapOrDie 0x30 + GetNamedMappingFd 0x110 (RepMmapcf.MOD_STK = 0x140);
   UnmapOrDie 0x30 (RepUnmapcf.UOD_STK = 48). *)
Definition REALLOC_FRAME : Z := 0x20.
Definition REALLOC_STK : Z := REALLOC_FRAME + RepMmapcf.MOD_STK.

(* The seed: Realloc's frame, the vector object (read-only until the two final stores) and the page-size cells.
   Atoms 32 / 33 / 34 are the object's data, capacity and size words. *)
Definition rSTKr : YP09.region := YP09.mkRegion (Some 2%nat) (- REALLOC_FRAME) 0 (- REALLOC_FRAME) 0 [].
Definition rVEC : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition rVECw : YP09.region := YP09.mkRegion (Some 10%nat) 0 16 0 16 [].
Definition IFR : facts := mkFacts [ (2%nat, mkAF (TFIB_IMG_END + REALLOC_STK) (2 ^ 64 - 1) 4);
  (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (10%nat, mkAF 0 (2 ^ 64 - 24) 3); (34%nat, mkAF 0 (2 ^ 47 - 1) 0) ] [] [].
Definition SS_R : sstate := mkSS A_REALLOC sr_atoms [rSTKr; rVEC; rPSP; rPS] None IFR.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma md_wvb_ext : forall l X (m : Model), m_vmmaps (with_vm_backing l X m) = m_vmmaps m /\ m_vm_lazy (with_vm_backing l X m) = l.
Proof. intros l X m. split; reflexivity. Qed.
Lemma eager_used_ext : forall m m' : Model, m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> eager_used m' = eager_used m.
Proof. intros m m' E1 E2. unfold eager_used. rewrite E1, E2. reflexivity. Qed.
Lemma wmb34 : forall a n (m : Model), with_mmap_backing (w64 34) a n m = m.
Proof. intros a n m. unfold with_mmap_backing. replace (mmap_noreserve_b (w64 34)) with false by (vm_compute; reflexivity). reflexivity. Qed.
Lemma mmap_wvb : forall a n l X (m : Model), mmap_model a n (with_vm_backing l X m) = with_vm_backing l X (mmap_model a n m).
Proof. intros a n l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma wvb_mmap_collapse : forall a n X Y (m : Model),
  with_vm_backing (m_vm_lazy (mmap_model a n (with_vm_backing (m_vm_lazy m) Y m))) X (mmap_model a n (with_vm_backing (m_vm_lazy m) Y m)) =
  mmap_model a n (with_vm_backing (m_vm_lazy m) X m).
Proof. intros a n X Y [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma region_kept_pt : forall (E : env) (ma mb : word -> option byte) (r : YP09.region),
(forall z, (base_val E (YP09.r_base r) + YP09.r_lo r <= z < base_val E (YP09.r_base r) + YP09.r_hi r \/
base_val E (YP09.r_base r) + YP09.r_wlo r <= z < base_val E (YP09.r_base r) + YP09.r_whi r) ->
mb (Z_to_bv 64 z) = ma (Z_to_bv 64 z)) ->
region_kept tfibsegs E ma mb r.
Proof.
intros E ma mb r Hm. split; intros z Hz.
- unfold mbyte. rewrite (Hm z (or_introl Hz)). reflexivity.
- unfold writable_at, wview. rewrite (Hm z (or_intror Hz)). intros Hw. exact Hw.
Qed.
Lemma mrestrict_same_at : forall (H H' : word -> bool) (mem mem' : word -> option byte) (x : word),
  H' x = H x -> mem' x = mem x -> mrestrict H' mem' x = mrestrict H mem x.
Proof. intros H H' mem mem' x E1 E2. unfold mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma sdo0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma MWF_ext : forall m m' : Model, m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> MWF m -> MWF m'.
Proof. intros m m' E1 E2 HW. unfold MWF, YK0g.model_ivs_wf in *. rewrite E1, E2. exact HW. Qed.
Lemma md1_collapse : forall (md : Model) (mat1 mat' : list word) (a n : word),
  with_vm_backing (m_vm_lazy (with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)))) mat'
    (with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)))
  = with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat' md)).
Proof. intros md mat1 mat' a n. rewrite !wmb34. destruct md as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sio_trans : forall m1 m2 m3, YG0d.same_io m1 m2 -> YG0d.same_io m2 m3 -> YG0d.same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold YG0d.same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma sio_wvb : forall l X m, YG0d.same_io m (with_vm_backing l X m).
Proof. intros. repeat split; reflexivity. Qed.
Lemma grant_apart_map : forall md a n b s, grant_ok_na_pin md (w64 a) n = true ->
  0 <= a < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> In (w64 b, w64 s) (vm_maps (m_vmmaps md)) -> 0 <= b < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  a + n <= b \/ b + s <= a.
Proof.
intros md a n b s H Ha Hn Hin Hb Hs. unfold grant_ok_na_pin in H.
apply andb_true_iff in H as [_ H4]. rewrite YK13.region_free_app in H4. apply andb_true_iff in H4 as [_ H4].
pose proof (YK13.region_free_In _ _ _ _ _ H4 Hin) as R. unfold w64 in R.
rewrite !unsigned_lit_small in R by lia. lia.
Qed.

(* The premises of a Realloc call (entry sp, ra and arguments in regs; the object at v; the old buffer [d, d+cap)
   with sz bytes used; the image cells Realloc, MmapOrDie and UnmapOrDie read; the grant facts). *)
Definition realloc_pre (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (v nb d cap sz : Z) : Prop :=
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
let ncap := page_round_up_Z nb in
getr regs 10 = w64 v /\ getr regs 11 = w64 nb /\ YK0s.ret_ok (getr regs 1) /\
amwf md /\ 0 < nb /\ nb < 2 ^ 47 /\ 0 <= sz <= nb /\ sz <= cap /\
0 <= v /\ v + 24 <= 2 ^ 64 /\ v mod 8 = 0 /\
val_mem tfibsegs m v 8 d /\ val_mem tfibsegs m (v + 8) 8 cap /\ val_mem tfibsegs m (v + 16) 8 sz /\
(forall x, v <= x < v + 16 -> writable_at tfibsegs m x) /\
(v + 24 <= sp - REALLOC_STK \/ sp <= v) /\
(v + 24 <= 0x9df30 \/ 0x9df30 + 8 <= v) /\ (v + 24 <= 0x1360e0 \/ 0x1360e0 + 8 <= v) /\
0 <= d /\ d + cap <= TASK_SIZE /\
(cap = 0 \/ (0 < d /\ (d + cap <= TFIB_IMG_LO \/ TFIB_IMG_END <= d) /\ d mod 4096 = 0 /\ cap mod 4096 = 0 /\
   In (w64 d, w64 cap) (vm_maps (m_vmmaps md)))) /\
(forall i, 0 <= i < sz -> apresent H mem (d + i)) /\
(d + cap <= sp - REALLOC_STK \/ sp <= d) /\ (d + cap <= v \/ v + 24 <= d) /\
val_mem tfibsegs m 0x9df30 8 0x1360e0 /\ val_mem tfibsegs m 0x1360e0 8 4096 /\
val_mem tfibsegs m 0x9df40 8 0x138168 /\ val_mem tfibsegs m 0x13826c 1 0 /\ val_mem tfibsegs m 0x1381f8 8 0 /\
(forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
   mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) ncap = false) /\
(forall a : word, grant_ok_na_pin md a ncap = true ->
   (bv_unsigned a + ncap <= TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned a) /\
   (bv_unsigned a + ncap <= sp - REALLOC_STK \/ sp <= bv_unsigned a) /\
   (bv_unsigned a + ncap <= v \/ v + 24 <= bv_unsigned a)) /\
(forall (a2 : Z) (p : word), grant_ok_na_pin md (w64 a2) ncap = true ->
   a2 <= bv_unsigned p -> bv_unsigned p + page_size <= a2 + ncap -> page_in_ranges p (m_vm_lazy md) = false) /\
eager_used md + A_bytes (w_A W) + ncap <= vm_limit (m_vmmaps md) /\
sp mod 16 = 0 /\ TFIB_IMG_END <= sp - REALLOC_STK /\ (forall b, sp - REALLOC_STK <= b < sp -> apresent H mem b).

(* The post of Realloc entered at [regs] (sp, ra) in world W with model md: the new buffer a (granted for ncap bytes,
   exposed in the post world), the object's data / capacity words set, the old buffer unmapped (cap <> 0). *)
Definition realloc_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (v nb d cap sz : Z) (W' : world tfibsegs) (c' : config) : Prop :=
let H := w_H W in let sp := bv_unsigned (getr regs 2) in let ncap := page_round_up_Z nb in
exists (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat mat2 : list word),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) mdN) in
  let mdU := if cap =? 0 then md1 else munmap_model (w64 d) (w64 cap) md1 in
  let m' := mrestrict (w_H W') mem' in
  wle W W' /\ w_A W' = w_A W /\
  (forall x : word, a <= bv_unsigned x < a + ncap -> w_H W' x = false) /\
  (forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W' x = H x) /\
  grant_ok_na_pin md (w64 a) ncap = true /\ 0 < a /\ a + ncap < 2 ^ 64 /\
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdU) mat2 mdU) /\
  regs_preserved regs regs' /\
  val_mem tfibsegs m' v 8 a /\ val_mem tfibsegs m' (v + 8) 8 ncap /\ val_mem tfibsegs m' (v + 16) 8 sz /\
  (forall i, 0 <= i < sz -> mem' (w64 (a + i)) = mem (w64 (d + i))) /\
  (forall i, sz <= i < ncap -> mem' (w64 (a + i)) = Some (Z_to_bv 8 0)) /\
  (forall x : word, d <= bv_unsigned x < d + cap -> mem' x = None) /\
  (forall x : word, ~ (sp - REALLOC_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + ncap) ->
     ~ (d <= bv_unsigned x < d + cap) -> ~ (v <= bv_unsigned x < v + 16) -> mem' x = mem x) /\
  (forall b, 0 <= b < 2 ^ 64 -> apresent H mem b -> ~ (d <= b < d + cap) -> ~ (v <= b < v + 16) -> apresent (w_H W') mem' b) /\
  (forall b, a <= b < a + ncap -> apresent (w_H W') mem' b) /\
  YG0d.same_io md (cfg_model c') /\ amwf (cfg_model c').

(* The tail of the walk: from MmapOrDie's return (0x59eac) in the exposed world W2, with Realloc's frame below sp
   holding ra / s0 / s1 / s2 of the entry, s0 = v, s1 = ncap, a0 = a, to realloc_post at Realloc's return. *)
Definition realloc_tail_spec : Prop :=
forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (v nb d cap sz : Z)
  (W2 : world tfibsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (a : Z) (mat1 : list word),
let H := w_H W in let sp := bv_unsigned (getr regs 2) in let ncap := page_round_up_Z nb in
let md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat1 md)) in
let m1 := mrestrict (w_H W2) mem1 in
realloc_pre W regs mem md v nb d cap sz ->
wle W W2 -> w_A W2 = w_A W ->
(forall x : word, a <= bv_unsigned x < a + ncap -> w_H W2 x = false) ->
(forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W2 x = H x) ->
grant_ok_na_pin md (w64 a) ncap = true -> 0 < a -> a + ncap < 2 ^ 64 ->
(a + ncap <= TFIB_IMG_LO \/ TFIB_IMG_END <= a) -> (a + ncap <= sp - REALLOC_STK \/ sp <= a) -> (a + ncap <= v \/ v + 24 <= a) ->
(cap = 0 \/ d + cap <= a \/ a + ncap <= d) ->
amwf md1 -> YG0d.same_io md md1 ->
bv_unsigned (getr regs1 2) = sp - REALLOC_FRAME ->
getr regs1 8 = w64 v -> getr regs1 9 = w64 ncap -> getr regs1 10 = w64 a ->
(forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem tfibsegs m1 (sp - 8) 8 (bv_unsigned (getr regs 1)) -> val_mem tfibsegs m1 (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs m1 (sp - 24) 8 (bv_unsigned (getr regs 9)) -> val_mem tfibsegs m1 (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs m1 v 8 d -> val_mem tfibsegs m1 (v + 8) 8 cap -> val_mem tfibsegs m1 (v + 16) 8 sz ->
(forall b, sp - REALLOC_STK <= b < sp -> apresent (w_H W2) mem1 b) ->
(forall x : word, ~ (sp - REALLOC_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + ncap) -> mem1 x = mem x) ->
(forall x : word, a <= bv_unsigned x < a + ncap -> mem1 x = Some (Z_to_bv 8 0)) ->
(forall b, 0 <= b < 2 ^ 64 -> ~ (sp - REALLOC_STK <= b < sp) -> apresent H mem b -> apresent (w_H W2) mem1 b) ->
SRr tfibsegs W2 (mkCfg (mkst regs1 (w64 0x59eac) mem1 (seg_rom tfibsegs)) md1) (realloc_post W regs mem md v nb d cap sz).

End r.

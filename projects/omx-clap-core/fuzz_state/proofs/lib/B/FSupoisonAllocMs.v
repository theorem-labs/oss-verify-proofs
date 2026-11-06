(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFk0.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: KDEP's depot check tag is 14 (label 469488), the tag the kit's YG00.depot_put carries; malloc_K_some proves KDEP equal to malloc_K by reflexivity, so the two texts must agree. *)
(* Modified by Theorem Labs, 2026-10: Htr is areq_ok S (KDepot tr), the depot walk's trace-length premise; the depot id bound after the insertion is 20482, from depot_ids_bound on wf_depot (depot_inv). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/AFk0.v, with its module paths and module names changed; 1173 of its 2422 lines of code are new or changed and 106 lines of the source are left out. *)
(* Threads UP through the donor secondary-malloc walk lib/A/AF0w.v -> AFio.v malloc_sec: AFjh.v seg0 (seed AFjx.v SEED_ok), AFjj.v segR, AFjs.v nodeS, AFju.v D1W_ok, AFjz.v LEAF_S (AFjy.v AR_transport at the unpoisoned memories), AFk0.v refuseS and Section h (grantS_ne, grantS_eq), AFio.v malloc_sec; with the secondary walk's region lemmas. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The low shadow band of the constant cells ends at 0x800b3844 in image B, the bound of B's abs_cell checks in YFix / YFjb / YFju / YFkm / YFkz (lib/B/YFju.v:584); B's last constant shadow cell ends at 0x800b3564 (lib/B/YF0m.v:1141, Tfib_const_shadow). *)
(* The trace premises follow S0 946ad86dc9f: Htr is areq_ok S (KDepot tr) in the depot and grant sections (as AFju / AFk0) and tr_admit (as_universe B) S tr in malloc_secU_walk and malloc_secU (as AFio.malloc_sec); the grant leaves get the trace length (tr_admit_len); the depot id bound after the insertion is 20482. *)
(* Modified by Theorem Labs, 2026-10: image-B port (fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d) of lib/A/FSupoisonAllocMs.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), the kit is lib/B/FSupoisonAllocR / Rf / Rt, every statement is over B's tfibsegs (lib/B/YB1v.v); the constant cells' low shadow band ends at 0x800b3844, the bound of B's own abs_cell checks (lib/B/YFju.v:584, YFix.v:288); the walk's stations are named (PC_PS_*, PC_AL_*, PC_LMA_0BC, PC_IM_RET, PC_UNWIND, PC_MMAP_ECALL, CSTAT16 / CSTAT24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YB1q YFhy YFhz YFi0 YFi4 YFi9 YB1h YFjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h YG0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFia YFib YFic YFid YFie YFif YFig.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFjv YFjw YFjx YFjh YFji YFjj YFjn YFjo YFjk YFjl YFjp YFjq YFjr YFjs YFjt YFju YFjy YFjz.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YF05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFih YFii YFk1 YFi3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0g.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFk0 YFio FSupoisonAllocR.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* Constants kept from the A template are image-independent; each is verbatim in a B donor: the thread-object words
   T + 2784 .. 2904 (lib/B/YFio.v:141-144), the frame offsets 2128 / 2120 / 2112 / 133 / 266 (YFjh.v:470, 568, 565, 494,
   499) and 2272 / 142 / 264 (YFju.v:629, 790, 786), the ecall bound 0x7ffffff0 (YFjh.v:324), 64513 (YFio.v:75),
   131072 (YFjz.v:1012), the tree's spin ids 12 / 13 / 14 (labels 449860 / 460508 / 469488; YFk0.v:1036, 1033, 1032), 20482 (YFju.v:686),
   6144 (YFjz.v:673), 768 (YFjz.v:840), 222 (YFjs.v:488), 120 (YFjj.v:563), 4095 (YFjs.v:447); 247 is FSupoison's
   user-poison byte (lib/A/FSupoison.v:33). *)
(* B's addresses by name, each evaluated to its literal so that the terms are the YF donors' own: the code table
   Tfib_code (lib/B/YF0l.v), lib/B/YF0m.v's TFIB_INST, and a function entry of lib/B/YB1w.v plus the offset of the
   instruction in that function (the offset image A has; read off the unstripped B image with pyelftools + capstone). *)
Local Notation "'zlit' x" := ltac:(let v := eval vm_compute in (x : Z) in exact v) (at level 10, x at level 0, only parsing).
Local Notation PC_WRAP_MALLOC := (zlit (pc_wrap_malloc Tfib_code)) (only parsing).
Local Notation PC_MALLOC_RA0 := (zlit (pc_malloc_ra0 Tfib_code)) (only parsing).
(* The return address of Allocate's StackDepotPut call (the instruction after its jal). *)
Local Notation RA_DEPOT_PUT := (zlit (tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3ac)) (only parsing).
(* The secondary walk's stations: PoisonShadow's shadow-store ladder, Allocate's ladder over the secondary map,
   LargeMmapAllocator::Allocate after its mmap call, __interceptor_malloc's ret, the unwinder's entry, and the ecall
   of internal_mmap ("li a7, 222; ecall; ret"). *)
Local Notation PC_PS_098 := (zlit (tfib_A__ZN6__asan12PoisonShadowEmmh + 0x98)) (only parsing).
Local Notation PC_PS_240 := (zlit (tfib_A__ZN6__asan12PoisonShadowEmmh + 0x240)) (only parsing).
Local Notation PC_PS_27C := (zlit (tfib_A__ZN6__asan12PoisonShadowEmmh + 0x27c)) (only parsing).
Local Notation PC_PS_280 := (zlit (tfib_A__ZN6__asan12PoisonShadowEmmh + 0x280)) (only parsing).
Local Notation PC_AL_520 := (zlit (tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x520)) (only parsing).
Local Notation PC_AL_524 := (zlit (tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x524)) (only parsing).
Local Notation PC_LMA_0BC := (zlit (tfib_A__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc)) (only parsing).
Local Notation PC_IM_RET := (zlit (tfib_A___interceptor_malloc + 0x158)) (only parsing).
Local Notation PC_UNWIND := (zlit tfib_A__ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj) (only parsing).
Local Notation PC_MMAP_ECALL := (zlit (tfib_A__ZN11__sanitizer13internal_mmapEPvmiiiy + 4)) (only parsing).
(* Two words of the combined allocator's stats (YG0f.o_comb_stats), which the walk reads as junk. *)
Local Notation CSTAT16 := (zlit (TFIB_INST + o_comb_stats + 16)) (only parsing).
Local Notation CSTAT24 := (zlit (TFIB_INST + o_comb_stats + 24)) (only parsing).
Set Printing Depth 50. Set Printing Width 180.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Region lemmas (to move to FSupoisonAllocR.v at integration)                                                       *)
(* The secondary walk's region conditions: every byte a transferred fact reads or a write touches is off UP. UP's    *)
(* bytes are shadow bytes of whole user granules of live blocks (FSupoison.ush_facts): application memory (zone3,    *)
(* the image) is off UP; the new extent's shadow is the shadow of granules outside every live block (newmap_off_ush);*)
(* the image's constant cells in the low shadow read neither 0 nor 0xf7 (const_off_check_ok).                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed's regions (YFi9.v SREG0): the stack window (base 2), the thread object (aT = 32), the context map
   (aC = 33), the instance's BSL slot (aBSL = 55) and image literals (no base). *)
Definition seed_cls (r : YP09.region) : bool :=
  match YP09.r_base r with
  | None => (TFIB_IMG_LO <=? YP09.r_lo r) && (YP09.r_hi r <=? TFIB_IMG_END)
  | Some k =>
      if Nat.eqb k 2 then (- ASTACK <=? YP09.r_lo r) && (YP09.r_hi r <=? 0)
      else if Nat.eqb k 32 then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? kThreadObjSize)
      else if Nat.eqb k 33 then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 256)
      else if Nat.eqb k 55 then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8)
      else false
  end.
Lemma seed_cls_ok : forallb seed_cls YFi9.SREG0 = true.
Proof. vm_compute. reflexivity. Qed.
(* The image's absolute constant cells (Tfib_const_abs, Tfib_const_shadow): in the image, or in the low shadow of the
   image with every byte neither 0 nor 0xf7. *)
Definition const_off_check (c : acell) : bool :=
  match c_at c with
  | ANum a =>
      (TFIB_IMG_LO <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x800b3844) &&
      ((a + Z.max 1 (Z.of_nat (c_w c)) <=? TFIB_IMG_END) ||
       match c_val c with
       | AV (ANum v) => (1 <=? c_w c)%nat &&
           forallb (fun k : nat => negb (YG0f.le_byte v (c_w c) k =? 0) && negb (YG0f.le_byte v (c_w c) k =? 247)) (seq 0 (c_w c))
       | _ => false
       end)
  | _ => false
  end.
Lemma const_off_check_ok : forallb const_off_check (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (B : asyms) (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (mem0 : word -> option byte) (md0 : Model).
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem0 md0.
(* Application memory (zone3: the low or the high application range) is off UP. *)
Lemma zone3_offU : forall x sz a, zone3 x sz -> x <= a < x + sz -> FAR.offU UP a.
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof (proj1 (@ASAN_CEIL_range rc)) as CR.
apply (FAR.offU_app B ly S UP W mem0 md0 a HARU); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.
(* The image is off UP. *)
Lemma img_offU : forall a, 0 <= a < TFIB_IMG_END -> FAR.offU UP a.
Proof. intros a Ha. apply (FAR.offU_low B ly S UP W mem0 md0 a HARU). unfold TFIB_IMG_END, SHADOW_OFF in *. lia. Qed.
(* malloc_sec's region condition for the new extent (mb, msz), apart from the static extents (the primary reservation
   among them) and every secondary extent (YFia.grant_apart): the shadow of each of its bytes is off UP, since no live
   block meets the extent. *)
Lemma newmap_off_ush : forall mb msz,
  Forall (zdisjoint (mb, msz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
  forall g, 0 <= g < 2 ^ 64 -> mb <= g < mb + msz -> FAR.offU UP (shadow_addr g).
Proof.
intros mb msz GAP g Rg Hg.
apply (FAR.offU_shadow_nonlive B ly S UP W mem0 md0 g HARU Rg).
intros p nn Hb Hin.
pose proof (FSP.ARU_ARm tfibsegs B ly S UP W mem0 md0 HARU) as M.
destruct (FAR.ablock_in_user B ly S _ p nn M Hb) as [(c & Hc & R1 & R2 & R3 & R4)|(e & He & E1 & E2)].
- pose proof (region_in_prim ly c (am_layout B ly S _ M) ltac:(lia)) as (P1 & P2 & _).
  assert (Hp : In (ly_prim ly, kPrimResvSize) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S))
    by (apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto).
  pose proof (proj1 (Forall_forall _ _) GAP _ Hp) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  unfold kFreeArrayOffset in *. lia.
- assert (He' : In e (static_extents ly ++ vis0_zones ly ++ sec_extents ly S))
    by (apply in_app_iff; right; apply in_app_iff; right; exact He).
  pose proof (proj1 (Forall_forall _ _) GAP _ He') as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* malloc_sec's seed region condition (YFjx.v SEED_ok's st_ok fixes the regions SREG0): every byte is off UP. *)
Lemma seed_regions_off_ush : forall regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb,
  ly_stk_lo ly + ASTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  zone3 (ly_T ly) kThreadObjSize -> zone3 (ly_C ly) 256 ->
  0 <= YFjm.BSLv n -> YFjm.BSLv n + 8 <= TFIB_IMG_END ->
  FAR.regions_offU UP (YFjm.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) YFi9.SREG0.
Proof.
intros regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb S1 S3 ZT ZC B1 B2 r a Hr Ha.
pose proof (proj1 (forallb_forall _ _) seed_cls_ok r Hr) as Hc. unfold seed_cls in Hc.
pose proof (proj1 (@ASAN_CEIL_range rc)) as CR.
set (E := YFjm.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) in *.
destruct (YP09.r_base r) as [k|] eqn:Eb; cbn [base_val] in Ha.
- destruct (Nat.eqb_spec k 2) as [->|N2].
  { apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (E2' : ew E 2 = getr regs0 2) by exact (YFjm.E2 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
    rewrite E2' in Ha. apply (FAR.stack_offU B ly S UP W mem0 md0 a HARU). unfold ASTACK in *. lia. }
  destruct (Nat.eqb_spec k 32) as [->|N32].
  { apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof ZT as (T0 & T1 & _).
    assert (UT : bv_unsigned (ew E 32) = ly_T ly) by (change (ew E 32) with (Z_to_bv 64 (ly_T ly)); apply unsigned_lit_small; lia).
    rewrite UT in Ha. apply (zone3_offU (ly_T ly) kThreadObjSize a ZT). lia. }
  destruct (Nat.eqb_spec k 33) as [->|N33].
  { apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof ZC as (C0 & C1 & _).
    assert (UC : bv_unsigned (ew E 33) = ly_C ly) by (change (ew E 33) with (Z_to_bv 64 (ly_C ly)); apply unsigned_lit_small; lia).
    rewrite UC in Ha. apply (zone3_offU (ly_C ly) 256 a ZC). lia. }
  destruct (Nat.eqb_spec k 55) as [->|N55].
  { apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (UB : bv_unsigned (ew E 55) = YFjm.BSLv n)
      by (change (ew E 55) with (Z_to_bv 64 (YFjm.BSLv n)); apply unsigned_lit_small; unfold TFIB_IMG_END in *; lia).
    rewrite UB in Ha. apply img_offU. lia. }
  discriminate Hc.
- apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply img_offU. unfold TFIB_IMG_LO in *. lia.
Qed.
End rg.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; zlia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := eval vm_compute in (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
eq_refl eq_refl ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS
end.
Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@YFjm.R8v n).
Local Abbreviation N8D := (@YFjm.N8D n).
Local Abbreviation NDv := (@YFjm.NDv n).
Local Abbreviation MSv := (@YFjm.MSv n).
Local Abbreviation SHBv := (@YFjm.SHBv).
Local Abbreviation QSv := (@YFjm.QSv ly idx).
Local Abbreviation Kv := (@YFjm.Kv mb).
Local Abbreviation Uv := (@YFjm.Uv mb).
Local Abbreviation ENDv := (@YFjm.ENDv n mb).
Local Abbreviation TLv := (@YFjm.TLv n).
Local Abbreviation UEv := (@YFjm.UEv n mb).
Local Abbreviation RLv := (@YFjm.RLv n).
Local Abbreviation SMv := (@YFjm.SMv mb).
Local Abbreviation PBv := (@YFjm.PBv n mb).
Local Abbreviation LGv := (@YFjm.LGv n).
Local Abbreviation BSLv := (@YFjm.BSLv n).
Local Abbreviation tr := (@YFjm.tr ly regs0 ch).
Local Abbreviation XW := (@YFjm.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E0 := (@YFjm.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Er := (@YFjm.Er ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@YFjm.E1 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@YFjm.E2 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E4 := (@YFjm.E4 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E8 := (@YFjm.E8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@YFjm.E10 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@YFjm.EaT ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@YFjm.EaC ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@YFjm.EaSB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@YFjm.EaTOP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaR8 := (@YFjm.EaR8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQ := (@YFjm.EaQ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRES := (@YFjm.EaRES ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaNCH := (@YFjm.EaNCH ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@YFjm.EaMS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@YFjm.EaMAP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaEND := (@YFjm.EaEND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSHB := (@YFjm.EaSHB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTL := (@YFjm.EaTL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQS := (@YFjm.EaQS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaBSL := (@YFjm.EaBSL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSM := (@YFjm.EaSM ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaUE := (@YFjm.EaUE ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaND := (@YFjm.EaND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRL := (@YFjm.EaRL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaN8D := (@YFjm.EaN8D ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaPB := (@YFjm.EaPB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@YFjm.mod0_of_mul).
Local Abbreviation size_facts := (@YFjm.size_facts n Nrange).
Local Abbreviation tr_length := (@YFjm.tr_length ly regs0 ch idx res Hidx).
Local Abbreviation high_facts := (@YFjm.high_facts _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation stack_ivs := (@YFjm.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YFjm.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@YFjm.map_facts _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@YFjm.map_zone _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@YFjm.map_zoneN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@YFjm.map_in_band _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YFjm.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@YFjm.WINT ly).
Local Abbreviation WINI := (@YFjm.WINI n).
Local Abbreviation WINM := (@YFjm.WINM ly n idx mb).
Local Abbreviation WIN := (@YFjm.WIN ly regs0 n idx mb).
Local Abbreviation WINN := (@YFjm.WINN ly regs0).
Local Abbreviation WINP := (@YFjm.WINP ly regs0 n).
Local Abbreviation WINP_WIN := (@YFjm.WINP_WIN ly regs0 n idx mb).
Local Abbreviation WIN1P := (@YFjm.WIN1P ly regs0 n).
Local Abbreviation WIN1 := (@YFjm.WIN1 ly regs0 n idx mb).
Local Abbreviation WIN1P_WINP := (@YFjm.WIN1P_WINP ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1_WIN := (@YFjm.WIN1_WIN ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1P_WIN1 := (@YFjm.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@YFjm.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@YFjm.BSLv_range ly regs0 n idx res mb Nrange Hidx).
Local Abbreviation WSKELP := (@YFjm.WSKELP).
Local Abbreviation WSKEL1P := (@YFjm.WSKEL1P).
Local Abbreviation WMAP := (@YFjm.WMAP).
Local Abbreviation WSKEL := (@YFjm.WSKEL).
Local Abbreviation WSKEL1 := (@YFjm.WSKEL1).
Local Abbreviation win_sub := (@YFjm.win_sub).
Local Abbreviation win_sub_sound := (@YFjm.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@YFjm.in_win).
Local Abbreviation WSKELP_WINP := (@YFjm.WSKELP_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@YFjm.WSKEL1P_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@YFjm.WMAP_WINM _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@YFjm.WSKEL_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@YFjm.WSKEL1_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@YFjm.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (@YFjm.windows_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@YFjm.windows_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@YFjm.windows_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@YFjm.windows_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@YFjm.frame_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@YFjm.frame_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@YFjm.WINP_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@YFjm.WIN_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YFjm.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@YFjm.img_rw_writable ly regs0 idx res mb Hidx).
Local Abbreviation kept_of_frame := (@YFjm.kept_of_frame W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@YFjm.SKEL_TAIL).
Local Abbreviation blocks_facts := (@YFjm.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@YFjm.off_T _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_C := (@YFjm.off_C _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_Q := (@YFjm.off_Q _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_NB := (@YFjm.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@YFjm.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@YFjm.off_shadow ly regs0 idx res mb Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation DZONE := (@YFjm.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := (@YFjm.DZONE_disj _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@YFjm.RFACTS ly regs0).
Local Abbreviation zone_lit := (@YFjm.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@YFjm.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@YFjm.zone_T _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := (@YFjm.zone_C _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (@YFjm.tail_ext_ok _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@YFjm.RFACTS_map _ ly regs0 n idx res mb LY IMG Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@YFjm.at_ST _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@YFjm.memset_stretch _ _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@YFjm.at_S _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@YFjm.at_N _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@YFjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@YFjm.pstable).
Local Abbreviation stack_shaped := (@YFjm.stack_shaped).
Local Abbreviation window_present := (@YFjm.window_present ly regs0 idx res Hidx).
Local Abbreviation stack_present_of := (@YFjm.stack_present_of _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (@YFjm.mid_not_WIN1P _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1 := (@YFjm.mid_not_WIN1 _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation wins_ok := (@YFjm.wins_ok).
Local Abbreviation at_S_run_gen := (@YFjm.at_S_run_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := (@YFjm.at_S_run_ecall_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_runP := (@YFjm.at_S_runP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@YFjm.at_S_runM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@YFjm.at_S_run_ecallP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@YFjm.at_S_run_ecallM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@YFjm.at_S_pin _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@YFjm.at_S_arm _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@YFjm.at_S_forget _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@YFjm.at_S_noconds _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_weaken := (@YFjm.at_S_weaken _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts := (@YFjm.at_S_facts _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_strengthen := (@YFjm.at_S_strengthen _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@YFjm.at_S_eq _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_open := (@YFjm.at_S_open _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation CSAVEDS := (@YFjm.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YFjm.sv_denot_SOff0).
Local Abbreviation at_S_ret := (@YFjm.at_S_ret _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@YFjm.kept_of_frame2 ly regs0 idx res Hidx).
Local Abbreviation at_N_cont := (@YFjm.at_N_cont _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Variable UP : list (Z * Z).
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem0 md0.
Local Abbreviation mem0u := (FSP.unpoison UP mem0).
Let HAR : AR tfibsegs B ly S W mem0u md0 := FSP.ARU_AR tfibsegs B ly S UP W mem0 md0 HARU.
Let HARm : ARm B ly S (aview tfibsegs (w_H W) mem0u) := proj1 HAR.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4.
Hypothesis Hj5 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5.
Hypothesis Hj9 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9.
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) CSTAT16 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) CSTAT24 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Local Abbreviation vis_present := (@YFjv.vis_present _ W ly regs0 mem0u idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YFjv.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YFjv.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YFjv.in_as_junk ly B S).
Local Abbreviation junk_word := (@YFjv.junk_word _ W ly regs0 mem0u idx res LY IMG Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@YFjv.cell_sym _ W ly mem0u B S TS HARm).
Local Abbreviation cell_lit := (@YFjv.cell_lit _ W ly mem0u B S TS HARm).
Local Abbreviation cell_state := (@YFjv.cell_state _ W ly mem0u B S HARm).
Local Abbreviation In_acells_sec := (@YFjv.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YFjv.sec_vals _ W ly mem0u idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@YFjv.unwinding_val _ W ly mem0u B S HARm).
Local Abbreviation rw_writable := (@YFjv.rw_writable ly regs0 idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@YFjv.val_mem_mod8 W ly regs0 mem0 idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (@YFjv.chunk_lit W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@YFjv.chunk_lit_at W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@YFjv.chunk_atom W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx DPOST S).
Local Abbreviation PAIRS_ok := (@YFjx.PAIRS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@YFjx.FACTS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation PBUF := (@YFjh.PBUF W ly regs0 ch).
Local Abbreviation PBUF_stableP := (@YFjh.PBUF_stableP _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@YFjh.PBUF_stableM _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation seg1 := (@YFji.seg1 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres).
Local Abbreviation PNULL := (@YFjj.PNULL W ly regs0 ch).
Local Abbreviation PNULLX := (@YFjj.PNULLX W ly regs0 n ch idx res).
Local Abbreviation tail_lits_apart := (@YFjj.tail_lits_apart).
Local Abbreviation appregs := (@YFjn.appregs).
Local Abbreviation st_ok_appregs := (@YFjn.st_ok_appregs _).
Local Abbreviation at_S_app := (@YFjn.at_S_app _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@YFjn.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@YFjn.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@YFjn.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@YFjn.WIN1N_WINPN ly regs0 n idx res mb Hidx).
Local Abbreviation windows_WIN1N := (@YFjn.windows_WIN1N _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1N := (@YFjn.mid_not_WIN1N _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@YFjn.at_S_runN _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@YFjn.PBUF_stableN _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_val := (@YFjn.at_S_val _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@YFjn.memset_stretchW _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@YFjn.at_S_memset _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@YFjn.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@YFjn.WIN1T_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@YFjn.windows_WIN1T _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@YFjn.WIN1T_WIN1_aux _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1T := (@YFjn.mid_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@YFjn.at_S_runT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@YFjn.at_S_run_ecallT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@YFjn.PBUFW ly regs0 ch).
Local Abbreviation PBUFW_stableT := (@YFjn.PBUFW_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@YFjo.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@YFjo.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@YFjo.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@YFjo.WIN1S_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@YFjo.windows_WIN1S _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1S := (@YFjo.mid_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@YFjo.at_S_runS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@YFjo.at_S_run_ecallS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@YFjo.brun).
Local Abbreviation run_ok := (@YFjo.run_ok n mb).
Local Abbreviation PS := (@YFjo.PS ly regs0 n ch mb).
Local Abbreviation runs_not_WIN1S := (@YFjo.runs_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@YFjo.runs_not_stack _ ly regs0 n idx res mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@YFjo.PS_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@YFjo.cut1).
Local Abbreviation cut := (@YFjo.cut).
Local Abbreviation cut_sound := (@YFjo.cut_sound _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@YFjo.cut_ok ly regs0 mem0 n idx res mb Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@YFjo.at_S_memsetS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@YFjo.skel_okb).
Local Abbreviation skel_cases := (@YFjo.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@YFjo.skel_apart _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@YFjo.skel_u64 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@YFjo.memset_ext_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@YFjo.memset_u64_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@YFjo.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@YFjo.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@YFjo.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@YFjo.WIN1R_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@YFjo.windows_WIN1R _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1R := (@YFjo.mid_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@YFjo.at_S_runR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@YFjo.at_S_run_ecallR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@YFjo.PSR ly regs0 n ch mb).
Local Abbreviation rstable := (@YFjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@YFjo.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@YFjo.PSR_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@YFjo.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@YFjo.QS_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@YFjo.QSP_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@YFjo.at_S_memsetSR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@YFjo.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@YFjo.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YFjo.subregionb).
Local Abbreviation subregionb_sound := (@YFjo.subregionb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@YFjo.submemb).
Local Abbreviation submemb_sound := (@YFjo.submemb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@YFjo.at_S_submem _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@YFjo.at_S_addreg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@YFjk.PSR_runs _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@YFjk.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@YFjk.SH0 n mb).
Local Abbreviation SH1 := (@YFjk.SH1 n mb).
Local Abbreviation SH2 := (@YFjk.SH2 n mb).
Local Abbreviation SH_ok := (@YFjk.SH_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@YFjk.segG1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RX_stableS := (@YFjl.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@YFjl.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@YFjl.pstable_and).
Local Abbreviation PSR_stableS' := (@YFjl.PSR_stableS' _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@YFjl.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@YFjl.at_S_setchunks _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@YFjl.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@YFjl.RES2T_ne ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@YFjl.RES2T_eq ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@YFjl.sv_denot_eq_of_U ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@YFjl.skel_apart_QS _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@YFjl.QSPX ly idx).
Local Abbreviation segNE := (@YFjl.segNE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@YFjl.segEQa _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@YFjl.zev_SAlu).
Local Abbreviation zev_SLit := (@YFjl.zev_SLit).
Local Abbreviation zev_SOff := (@YFjl.zev_SOff).
Local Abbreviation segJ2 := (@YFjl.segJ2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@YFjl.segJ _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@YFjp.QR ly res).
Local Abbreviation segT1 := (@YFjp.segT1 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@YFjp.DX ly regs0).
Local Abbreviation PD := (@YFjp.PD ly mem0 DPOST).
Local Abbreviation PD_rstable := (@YFjp.PD_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PD_stableT := (@YFjp.PD_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PSR_stableS := (@YFjp.PSR_stableS _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@YFjp.PD_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX := (@YFjp.PDX ly mem0 DPOST).
Local Abbreviation PDX_rstable := (@YFjp.PDX_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableT := (@YFjp.PDX_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableS := (@YFjp.PDX_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation dx_okb := (@YFjp.dx_okb).
Local Abbreviation skel_apart_DX := (@YFjp.skel_apart_DX _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@YFjp.skel_apart_stk _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@YFjp.at_S_depot _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH3 := (@YFjp.SH3 n mb).
Local Abbreviation SH4 := (@YFjp.SH4 n mb).
Local Abbreviation shadow_marks := (@YFjp.shadow_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@YFjp.SH34_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@YFjp.segT2b _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@YFjp.segT2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH5 := (@YFjq.SH5 n mb).
Local Abbreviation SH6 := (@YFjq.SH6 n mb).
Local Abbreviation user_marks := (@YFjq.user_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH56_ok := (@YFjq.SH56_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segU1 := (@YFjq.segU1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH6_of_cut := (@YFjq.SH6_of_cut _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segUe := (@YFjq.segUe _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation PT := (@YFjq.PT ly regs0 n ch mb).
Local Abbreviation run_okT := (@YFjq.run_okT n mb).
Local Abbreviation SH5o := (@YFjq.SH5o n mb).
Local Abbreviation SH6o := (@YFjq.SH6o n mb).
Local Abbreviation SH56o_ok := (@YFjq.SH56o_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation PT_stableT := (@YFjq.PT_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segUo := (@YFjq.segUo _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation E0_at := (@YFjr.E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3).
Local Abbreviation map_atom := (@YFjr.map_atom).
Local Abbreviation E0_at_other := (@YFjr.E0_at_other ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation ed_E0_at := (@YFjr.ed_E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation st_ok_ecall_agree_on := (@YFjr.st_ok_ecall_agree_on _).
Local Abbreviation Esw := (@YFjr.Esw ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_agree := (@YFjr.Esw_agree ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_on := (@YFjr.Esw_on ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts_atoms := (@YFjr.at_S_facts_atoms _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation atoms_ok_app := (@YFjr.atoms_ok_app).
Local Abbreviation FS2_ok := (@YFjr.FS2_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation at_S_addreg_cfg := (@YFjr.at_S_addreg_cfg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation S_N_apart := (@YFjr.S_N_apart _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation S_N_nomap := (@YFjr.S_N_nomap).
Local Abbreviation grant_cont := (@YFjr.grant_cont _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation SHLO := (@YFjs.SHLO).
Local Abbreviation SHHI := (@YFjs.SHHI n).
Local Abbreviation SH_hull := (@YFjs.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@YFjs.lit_m1).
Local Abbreviation lit_enomem := (@YFjs.lit_enomem).
Local Abbreviation nores34 := (@YFjs.nores34).
Local Abbreviation core34 := (@YFjs.core34).
Local Abbreviation pru_MS := (@YFjs.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@YFjs.grant_anon_shape).
Local Abbreviation Hcut_out := (@YFjs.Hcut_out).
Local Abbreviation slackS := (@YFjs.slackS _ W ly mem0u md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@YFjs.S_N_facts).
Local Abbreviation S_N_ext64 := (@YFjs.S_N_ext64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation S_N_win64 := (@YFjs.S_N_win64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation S_VG := (@YFjt.S_VG).
Local Abbreviation TQ := (@YFjt.TQ).
Local Abbreviation S_V_facts := (@YFjt.S_V_facts).
Local Abbreviation ZQF := (@YFjt.ZQF ly res).
Local Abbreviation ZQ := (@YFjt.ZQ ly idx res).
Local Abbreviation QR_facts := (@YFjt.QR_facts _ ly regs0 idx res mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@YFjt.ZQ_of_ZQF ly idx res).
Local Abbreviation QR_not_WIN1T := (@YFjt.QR_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableT := (@YFjt.ZQ_stableT _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_rstable := (@YFjt.ZQ_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableD := (@YFjt.ZQ_stableD _ ly regs0 idx res mb LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := (@YFjt.skel_apart_Q _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation TQ_val := (@YFjt.TQ_val _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@YFjt.nores50).
Local Abbreviation core50 := (@YFjt.core50).
Local Abbreviation pru17 := (@YFjt.pru17).
Local Abbreviation grant_piece_shape := (@YFjt.grant_piece_shape).
Local Abbreviation nodeV := (@YFjt.nodeV _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RZF := (@YFjt.RZF ly res).
Local Abbreviation RZ := (@YFjt.RZ ly idx res).
Local Abbreviation ZQF_rstable := (@YFjt.ZQF_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation segV := (@YFjt.segV _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation CZI := (@YFju.CZI).
Local Abbreviation CZ := (@YFju.CZ ly).
Local Abbreviation abs_cell_okS := (@YFju.abs_cell_okS).
Local Abbreviation abs_cells_okS := (@YFju.abs_cells_okS).
Local Abbreviation MPAD := (@YFju.MPAD).
Local Abbreviation padb := (@YFju.padb).
Local Abbreviation const_cells_CZ := (@YFju.const_cells_CZ ly regs0 n idx res mb Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := (@YFju.CZ_untouched _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation cell_holds_agree := (@YFju.cell_holds_agree ly regs0 mem0 idx res Hidx Hres DPOST B S).
Local Abbreviation aview_agreeW := (@YFju.aview_agreeW W).
Local Abbreviation rd_ext_Wy := (@YFju.rd_ext_Wy W).
Local Abbreviation depot_ids_bound := (@YFju.depot_ids_bound B TS).
Local Abbreviation depot_mem_ok_agree := (@YFju.depot_mem_ok_agree ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@YFju.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := (@YFju.depot_at0 _ W ly regs0 mem0u n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation DPOSTS := (@YFju.DPOSTS ly regs0 ch B S).
Local Abbreviation lyF := (@YFjy.lyF ly mb S).
Local Abbreviation SFS := (@YFjy.SFS ly regs0 n ch S).
Local Abbreviation KSc := (@YFjy.KSc n S).
Local Abbreviation lyF_le := (@YFjy.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@YFjy.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@YFjy.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@YFjy.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@YFjy.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := (@YFjy.val_mem_cell ly regs0 res B S).
Local Abbreviation le_byte_1_0 := (@YFjy.le_byte_1_0 ly regs0 res S).
Local Abbreviation find_chunk_at_app1 := (@YFjy.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@YFjy.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@YFjy.In_combine_seq_app).
Local Abbreviation combine_seq_last := (@YFjy.combine_seq_last ly regs0 res S).
Local Abbreviation in_combine_seq := (@YFjy.in_combine_seq ly regs0 res S).
Local Abbreviation combine_seq_in := (@YFjy.combine_seq_in ly regs0 res S).
Local Abbreviation index_of_app_old := (@YFjy.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@YFjy.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (@YFjy.index_of_app_new ly regs0 res S).
Local Abbreviation index_ofZ_app_new := (@YFjy.index_ofZ_app_new ly regs0 res S).
Local Abbreviation fin_facts := (@YFjy.fin_facts ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation wz_facts := (@YFjy.wz_facts _ W ly regs0 n ch res mb S).
Local Abbreviation S_AR_final := (@YFjy.S_AR_final _ W ly regs0 mem0u md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation SF_parts := (@YFjy.SF_parts ly regs0 n ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (@YFjy.rS_not_in_arr _ W ly regs0 mem0u n res mb B S HARm).
Local Abbreviation len_arr := (@YFjy.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@YFjy.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := (@YFjy.SEF _ W ly regs0 mem0u n ch res mb Nrange B S HARm Hres_def).
Local Abbreviation staticF := (@YFjy.staticF ly mb S).
Local Abbreviation placed_finalG := (@YFjy.placed_finalG _ W ly regs0 mem0u md0 n ch idx res mb Nrange Hidx Hres Hmap B S HARm Hres_def).
Local Abbreviation sec_live_final := (@YFjy.sec_live_final ly regs0 n ch res mb Nrange S Hres_def).
Local Abbreviation FQ := (@YFjz.FQ ly n idx res mb).
Local Abbreviation OWN_T := (@YFjz.OWN_T _ W ly regs0 mem0u n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_I := (@YFjz.OWN_I _ W ly regs0 mem0u n idx res mb Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation OWN_Q := (@YFjz.OWN_Q _ W ly regs0 mem0u n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_D := (@YFjz.OWN_D _ W ly regs0 mem0u n idx res Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation band_core := (@YFjz.band_core ly B S).
Local Abbreviation OWN_SH := (@YFjz.OWN_SH _ W ly regs0 mem0u n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation OWN_BANDhid := (@YFjz.OWN_BANDhid _ W ly mem0u md0 LY B S HARm).
Local Abbreviation NEWOWN := (@YFjz.NEWOWN _ W ly regs0 mem0u n ch idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm Hres_def).
Local Abbreviation fin_pack := (@YFjz.fin_pack ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb DPOST B S).
Local Abbreviation fin_post := (@YFjz.fin_post _ ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation finE := (@YFjz.finE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation finO := (@YFjz.finO _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation BCELLS := (@YFk1.BCELLS W mem0).
Local Abbreviation PGBv := (@YFk1.PGBv mb).
Local Abbreviation PGEv := (@YFk1.PGEv n mb).
Local Abbreviation big_marks := (@YFk1.big_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation sm_bounds := (@YFk1.sm_bounds _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHBT := (@YFk1.U_SHBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHET := (@YFk1.U_SHET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGBT := (@YFk1.U_PGBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGET := (@YFk1.U_PGET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHB_X := (@YFk1.U_SHB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHE_X := (@YFk1.U_SHE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation in_bimg := (@YFk1.in_bimg).
Local Abbreviation in_bimg_facts := (@YFk1.in_bimg_facts _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation val_mem_xfer_bimg := (@YFk1.val_mem_xfer_bimg _ W ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation can_word := (@YFk1.can_word W ly regs0 mem0 n idx res Hidx DPOST S).
Local Abbreviation zcanon_m1 := (@YFk1.zcanon_m1).
Local Abbreviation U_PGB_X := (@YFk1.U_PGB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGE_X := (@YFk1.U_PGE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation brun_refill := (@YFk1.brun_refill ly regs0 n idx res Hres S Hidx_def).
Local Abbreviation SH4_head := (@YFk1.SH4_head _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation SH4_tail := (@YFk1.SH4_tail _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation segB1a := (@YFk1.segB1a _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation zc_m1 := (@YFk1.zc_m1).
Local Abbreviation zc_idem := (@YFk1.zc_idem).
Local Abbreviation zc_add_l := (@YFk1.zc_add_l).
Local Abbreviation zc_sub_l := (@YFk1.zc_sub_l).
Local Abbreviation zc_sub_r := (@YFk1.zc_sub_r).
Local Abbreviation land_page_id := (@YFk1.land_page_id).
Local Abbreviation U_KA0 := (@YFk1.U_KA0 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_KA1 := (@YFk1.U_KA1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM1 := (@YFk1.U_REM1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM2 := (@YFk1.U_REM2 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation segB1b := (@YFk1.segB1b _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation nores4032 := (@YFk1.nores4032).
Local Abbreviation core4032 := (@YFk1.core4032).
Local Abbreviation lit4032 := (@YFk1.lit4032).
Local Abbreviation S_K_facts := (@YFk1.S_K_facts).
Local Abbreviation nodeK := (@YFk1.nodeK _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation submemb2 := (@YFk1.submemb2).
Local Abbreviation submemb2_sound := (@YFk1.submemb2_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem2 := (@YFk1.at_S_submem2 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation SH5_of_SH4 := (@YFk1.SH5_of_SH4 _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segB2 := (@YFk1.segB2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation allow_of_hull := (@YFk1.allow_of_hull _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Ltac s_station HR ss' :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_eq Wx md X P ss ss' W' c' HR ltac:(vm_compute; reflexivity)) as H2; clear HR; rename H2 into HR end.
Local Ltac s_runP HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runP Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_runM HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runM Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_ecallP HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallP Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac s_ecallM HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallM Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac unfold_atoms := unfold aT, aC, aSB, aTOP, aLEN, aJ0, aR8, aQ, aRES, aNCH, aMS, aMAP, aEND, aSHB, aTL, aQS, aBSL, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aSM, aUE, aND, aRL, aN8DS, aPBS.
Local Ltac pin_zevS := apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_pin HR r e :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := eval vm_compute in (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | let H2 := fresh "HR" in
pose proof (at_S_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HU) as H2;
clear HU HR; rename H2 into HR ] end.
Local Ltac s_arm HR cnd tk a b :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | let H2 := fresh "HR" in
pose proof (at_S_arm Wx md X P ss W' c' cnd tk a b HR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB) as H2;
clear HB HR; rename H2 into HR ] end.
Local Ltac s_forget HR k clob :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_forget Wx md X P ss W' c' k clob HR ltac:(unfold sHAV; cbv; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HR; rename H2 into HR end.
Local Ltac s_noconds HR :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_S_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Local Ltac arm_zevS := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (vm_compute; reflexivity); cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac U_zevS := rewrite U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_armR HR cnd tk r1 r2 :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let a := eval vm_compute in (sr_get (ss_regs ss) r1) in
let b := eval vm_compute in (sr_get (ss_regs ss) r2) in
s_arm HR cnd tk a b end.
Local Ltac ladder_arith Z :=
let MF := fresh "MF" in let SF := fresh "SF" in let NRx := fresh "NRx" in
pose proof map_facts as MF; pose proof size_facts as SF; pose proof Nrange as NRx;
arm_zevS; rewrite ?EaSHB, ?EaMAP, ?EaEND, ?EaTL, ?EaUE, ?EaRL, ?EaN8D, ?EaND, ?EaMS; unfold w64;
clear - Z MF SF NRx;
destruct MF as (M1x & M2x & M3x & K4x & U5x & E6x & UE7x & E8x & UE9x & MTx & MUx & SM1x & SM2x & SM3x & PBx & SMAx);
destruct SF as (Z1x & Z2x & Z3x & Z4x & Z5x & Z6x & Z7x & Z8x & Z9x & Z10x & Z11x & Z12x & Z13x & Z14x);
unfold YFjm.SHBv, YFjm.Kv, YFjm.Uv, YFjm.SMv, YFjm.PBv, MALLOC_MAX,
kLowShadowBeg, kHighShadowEnd, TFIB_IMG_END in *;
rewrite !unsigned_lit_small by zlia; zcanon_simp;
first [ rewrite (proj2 (Z.ltb_ge _ _)) by zlia | rewrite (proj2 (Z.ltb_lt _ _)) by zlia ]; reflexivity.
Local Ltac s_join HR k clob SJ := s_forget HR k clob; s_noconds HR; s_station HR SJ; apply SRr_ret; exact HR.
Local Ltac s_ladder RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok constr:(PC_PS_240) Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_098) Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_240) Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_280) Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderW RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3a Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok constr:(PC_PS_240) Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_098) Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_240) Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_27C) Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_PS_280) Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderM RUN HR tbl tblok STOP Slo Sh Sh2 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_AL_520) Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok constr:(PC_AL_524) Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.

Let rd0 : reader := aview tfibsegs (w_H W) mem0u.
Let WF := am_wf B ly S rd0 HARm.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* Where UP is not, in this walk's terms (the region lemmas above at this section's layout).                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma img_offU' : forall a, 0 <= a < TFIB_IMG_END -> FAR.offU UP a.
Proof. exact (img_offU B ly S UP W mem0 md0 HARU). Qed.
Lemma T_offU : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a.
Proof. intros a Ha. pose proof high_facts as (F1 & _). exact (zone3_offU B ly S UP W mem0 md0 HARU _ _ a F1 Ha). Qed.
Lemma Q_offU : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> FAR.offU UP a.
Proof. intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). exact (zone3_offU B ly S UP W mem0 md0 HARU _ _ a F9 Ha). Qed.
Lemma stk_offU : forall a, bv_unsigned (getr regs0 2) - ASTACK <= a < bv_unsigned (getr regs0 2) -> FAR.offU UP a.
Proof. intros a Ha. pose proof Hsp as (S1 & _ & S3 & _). unfold sp0 in S1, S3. apply (FAR.stack_offU B ly S UP W mem0 md0 a HARU). unfold ASTACK in *. lia. Qed.
Lemma map_offU : forall a, mb <= a < mb + MSv -> FAR.offU UP a.
Proof. intros a Ha. exact (zone3_offU B ly S UP W mem0 md0 HARU _ _ a (mzone_zone3 _ _ (proj2 Hmap)) Ha). Qed.
Lemma DZ_offU : forall a, DZONE a -> FAR.offU UP a.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE in Ha.
destruct Ha as [Ha|[Ha|Ha]].
- apply img_offU'. unfold TFIB_IMG_END. lia.
- exact (zone3_offU B ly S UP W mem0 md0 HARU _ _ a NBhi Ha).
- exact (zone3_offU B ly S UP W mem0 md0 HARU _ _ a SBhi Ha).
Qed.
(* The new extent's shadow [SMv, SMv + MSv / 8) is off UP (newmap_off_ush). *)
Lemma mapsh_offU : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
  forall a, SMv <= a < SMv + MSv / 8 -> FAR.offU UP a.
Proof.
intros GAP a Ha.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
set (g := mb + 8 * (a - SMv)).
assert (Hg : shadow_addr g = a).
{ subst g. rewrite SMA. unfold shadow_addr. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp.
replace (p * 4096) with (p * 512 * 8) by zlia. rewrite (Z.div_mul (p * 512) 8) by zlia.
replace (p * 512 * 8 + 8 * (a - (SHADOW_OFF + p * 512))) with ((p * 512 + (a - (SHADOW_OFF + p * 512))) * 8) by zlia.
rewrite Z.div_mul by zlia. zlia. }
pose proof (Z.mul_div_le MSv 8 ltac:(lia)) as DL.
rewrite <- Hg. apply (newmap_off_ush B ly S UP W mem0 md0 HARU mb MSv GAP g).
- subst g. clear - Ha M1 M2 DL MZ. zlia.
- subst g. clear - Ha DL. lia.
Qed.
(* A shadow byte of UP is in no region shown off UP. *)
Lemma ush_not : forall s (P : Prop), FSP.in_ush UP s = true -> (P -> FAR.offU UP s) -> ~ P.
Proof.
intros s P Hs F HP. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem0 md0 s HARU Hs) as (_ & L1 & L2).
pose proof (F HP) as O. unfold FAR.offU in O. rewrite Z.mod_small in O by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
rewrite O in Hs. discriminate Hs.
Qed.
(* The image's constant cells (as_const) are off UP: the symbolic ones lie in the thread object, the context map, the
   depot page, the TLS / TP words and the instance; the absolute ones by const_off_check_ok (their low-shadow bytes
   read neither 0 nor 0xf7 in the unpoisoned reading, FSupoisonAllocR.offU_nonzero). *)
Lemma const_offU : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  FAR.offU UP (aeval B ly (c_at c) + k).
Proof.
intros c k Hc Hk. pose proof Hc as Hc0. rewrite (ts_const B TS ly) in Hc0. unfold Tfib_const in Hc0.
apply in_app_iff in Hc0 as [Hs|Hc0].
- pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof HTSD as ETSD.
  pose proof high_facts as (F1 & _ & _ & _ & _ & _ & F7 & _).
  pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH.
  pose proof (pairwise_ij _ _ 7 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as DIMG.
  pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(zlia) DH DIMG) as DZ3.
  clear Hc. unfold Tfib_const_sym in Hs. cbn [In] in Hs.
  repeat match type of Hs with
  | _ \/ _ => destruct Hs as [<-|Hs];
      [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD;
       first [ apply img_offU'; unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, TFIB_IMG_END in *; lia
             | apply T_offU; unfold kThreadObjSize in *; lia
             | apply (zone3_offU B ly S UP W mem0 md0 HARU _ _ _ F7); lia
             | apply (zone3_offU B ly S UP W mem0 md0 HARU _ _ _ DZ3); lia ] |]
  | False => destruct Hs
  end.
- pose proof (proj1 (forallb_forall _ _) const_off_check_ok c Hc0) as CK. unfold const_off_check in CK.
  destruct (c_at c) eqn:Ea; try discriminate CK. cbn [aeval].
  apply andb_prop in CK as [CK CV]. apply andb_prop in CK as [CA1 CA2]. apply Z.leb_le in CA1. apply Z.leb_le in CA2. unfold TFIB_IMG_LO in CA1.
  apply orb_prop in CV as [CI|CV].
  + apply Z.leb_le in CI. apply img_offU'. lia.
  + destruct (c_val c) as [e|mk vv] eqn:Ev; [|discriminate CV]. destruct e; try discriminate CV.
    apply andb_prop in CV as [CW CB]. apply Nat.leb_le in CW.
    assert (Hk' : (Z.to_nat k < c_w c)%nat) by lia.
    pose proof (proj1 (forallb_forall _ _) CB (Z.to_nat k) ltac:(apply in_seq; lia)) as CBk.
    apply andb_prop in CBk as [V1 V2]. apply negb_true_iff, Z.eqb_neq in V1. apply negb_true_iff, Z.eqb_neq in V2.
    pose proof (proj1 (Forall_forall _ _) (am_const B ly S rd0 HARm) c Hc) as HOLD.
    unfold cell_holds in HOLD. cbv zeta in HOLD. rewrite Ev, Ea in HOLD. cbn [aeval] in HOLD.
    specialize (HOLD (Z.to_nat k) Hk'). rewrite Z2Nat.id in HOLD by lia.
    refine (FAR.offU_nonzero B ly S UP W mem0 md0 _ _ HARU _ HOLD V1 V2). lia.
Qed.
(* unpoison is pointwise. *)
Lemma unp_eq : forall (m1 m2 : word -> option byte) (x : word), m1 x = m2 x -> FSP.unpoison UP m1 x = FSP.unpoison UP m2 x.
Proof. intros m1 m2 x E. unfold FSP.unpoison. rewrite E. reflexivity. Qed.
(* A visible byte stays visible across unpoison of both memories. *)
Lemma vis_unp : forall (Hh : word -> bool) (m m' : word -> option byte),
  (forall a, aview tfibsegs Hh m a <> None -> aview tfibsegs Hh m' a <> None) ->
  forall a, aview tfibsegs Hh (FSP.unpoison UP m) a <> None -> aview tfibsegs Hh (FSP.unpoison UP m') a <> None.
Proof.
intros Hh m m' V a Hv. destruct (FSP.in_ush UP (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- rewrite (FSP.aview_unpoison_in tfibsegs Hh UP m' m a E). exact Hv.
- assert (O : FAR.offU UP a) by (unfold FAR.offU; rewrite <- FAR.bvu_mod; exact E).
  rewrite (FAR.aview_unpoison Hh UP m' a O). rewrite (FAR.aview_unpoison Hh UP m a O) in Hv. exact (V a Hv).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed: YFjx.v:496 SEED_ok at the unpoisoned memory (presence and junk words moved there), then moved back to   *)
(* the real memory by its region condition (seed_regions_off_ush). seg0U is YFjh.v:456 seg0 with this seed.        *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma SEED_okU : st_ok tfibsegs E0 S0 (restrict (w_H W) (YK11.mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (YK11.seg_rom tfibsegs))).
Proof.
pose proof Hsp as (Sp1 & _ & Sp3 & _). pose proof high_facts as (F1 & _ & _ & _ & _ & _ & F7 & _). pose proof BSLv_range as HB.
assert (PRu : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0u a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (Hpres0 a Ha)).
assert (OT : forall o, 0 <= o -> o + 8 <= kThreadObjSize -> forall k, (k < 8)%nat -> FAR.offU UP (T + o + Z.of_nat k))
  by (intros o O1 O2 k Hk; apply T_offU; unfold T; lia).
assert (OL : forall a, 0 <= a -> a + 8 <= TFIB_IMG_END -> forall k, (k < 8)%nat -> FAR.offU UP (a + Z.of_nat k))
  by (intros a A1 A2 k Hk; apply img_offU'; lia).
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2784) 8 _ (OT 2784 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj0) as Hj0u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2800) 8 _ (OT 2800 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj1) as Hj1u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2808) 8 _ (OT 2808 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj2) as Hj2u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2816) 8 _ (OT 2816 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj3) as Hj3u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2872) 8 _ (OT 2872 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj4) as Hj4u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2880) 8 _ (OT 2880 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj5) as Hj5u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2904) 8 _ (OT 2904 ltac:(lia) ltac:(unfold kThreadObjSize; lia)) Hj9) as Hj9u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 CSTAT16 8 _ (OL CSTAT16 ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hj6) as Hj6u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 CSTAT24 8 _ (OL CSTAT24 ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hj7) as Hj7u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (BSLv) 8 _ (OL (BSLv) ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hj8) as Hj8u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (TFIB_INST + o_sec_stats) 8 _ (OL (TFIB_INST + o_sec_stats) ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hi1) as Hi1u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (TFIB_INST + o_sec_stats + 16) 8 _ (OL (TFIB_INST + o_sec_stats + 16) ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hi2) as Hi2u.
pose proof (FAR.val_mem_to_unpoison (w_H W) UP mem0 (TFIB_INST + o_sec_stats + 24) 8 _ (OL (TFIB_INST + o_sec_stats + 24) ltac:(unfold TFIB_INST, o_sec_stats in *; lia) ltac:(unfold TFIB_INST, o_sec_stats, TFIB_IMG_END in *; lia)) Hi3) as Hi3u.
apply (proj1 (FAR.st_ok_unpoison_iff UP E0 S0 (w_H W) regs0 (w64 PC_WRAP_MALLOC) mem0 (YK11.seg_rom tfibsegs)
  (seed_regions_off_ush B ly S UP W mem0 md0 HARU regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Sp1 Sp3 F1 F7
     ltac:(unfold TFIB_INST in *; lia) ltac:(unfold TFIB_INST, TFIB_IMG_END in *; lia)))).
exact (@YFjx.SEED_ok _ _ W ly regs0 mem0u n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Nrange Hidx Hres PRu DPOST B S TS HTSD HARm Hidx_def Hres_def
  Hj0u Hj1u Hj2u Hj3u Hj4u Hj5u Hj9u Hj6u Hj7u Hj8u Hi1u Hi2u Hi3u).
Qed.
Lemma seg0U : SRr tfibsegs W cfg0 (at_S W md0 WINP PBUF S_1).
Proof.
clearP. pose proof Hwx_tfa as Hwx. pose proof SEED_okU as HS.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
srr_run_to_sh tfibtbl_rtA_ok HS constr:(PC_UNWIND).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape.
rewrite Hshape.
eapply SRr_bind.
{ pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, kHighMemEnd, kThreadObjSize, kPrimResvSize, kSpaceSize, kPtrArrayResv in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, T1, T2, T4, T7.
assert (U64 : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (intros r; apply u64_range).
pose proof (U64 2%bv) as Usp.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
apply (U1 W ly (ms_regs ms) (ms_mem ms) _ (sp0 - 2128) PC_MALLOC_RA0 sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R10; rewrite R10, E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R11; rewrite R11. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R12; rewrite R12, E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R13; rewrite R13. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R14; rewrite R14. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R15; rewrite R15. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R4; rewrite R4. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R1; rewrite R1. apply ret_ok_even. reflexivity. }
1:{ zlia. }
1:{ memv HS 1%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 6%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 7%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 34%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 35%nat 0%nat; [reflexivity | denot_tac | zlia]. }
1:{ memv HS 36%nat 1%nat; [addr_tac | denot_tac | zlia]. }
1:{ memv HS 37%nat 3%nat; [addr_tac | denot_tac | zlia]. }
1:{ memv HS 37%nat 1%nat; [addr_tac | denot_tac | zlia]. }
1:{ memv HS 37%nat 2%nat; [addr_tac | denot_tac | zlia]. }
1:{ memv HS 39%nat 0%nat; [addr_tac | denot_tac | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 39 _ _ HS); [reflexivity | addr_tac | off_by ltac:(addr_tac) ]. }
1:{ memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac.
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia.
rewrite Z_mod_plus_full. exact Hal. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. rewrite R2 in Ha. rewrite unsigned_lit_small in Ha by addr_tac.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | addr_tac | off_by ltac:(addr_tac) ]. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. apply (Znumtheory.Zdivide_mod). apply (Z.divide_trans _ 16); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [zlia | exact Hal]. }
1:{ addr_tac. }
1:{ right. rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | addr_tac | off_by ltac:(addr_tac) ]. }
1:{ addr_tac. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ unfold sp0. apply (Znumtheory.Zdivide_mod). apply (Z.divide_trans _ 16); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [zlia | exact Hal]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 11%nat;
[addr_tac | cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 10%nat;
[addr_tac | cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hch']. split; [exact H16|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Z.ltb_lt in Hf0.
eapply fpchain_ext2; [exact Hch' | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (HF (Z_to_bv 64 (a + i))). intros Hw. rewrite unsigned_lit_small in Hw by zlia.
refine (WINP_not_high (a + i) _ (windows_WINP E0 (ss_mem S0) (a + i) (fun k _ => eq_refl) _ Hw)); [zlia | vm_compute; reflexivity]. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & Hfr & Hpr & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2. rreg HS (1%bv : bv 5) R1.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
apply Hfr; unfold sp0, ASTACK in *; zlia. }
jafter_call2 HS 80%nat regs1 (mrestrict (w_H W) mem1) HP (-64) (seq 0 57) HS1.
assert (Hfr'' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
apply Hfr; unfold sp0, ASTACK in *; zlia. }
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr'' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, sp0, ASTACK, TFIB_IMG_END, kHighMemBeg, kHighMemEnd in *; intros a Ha; cbn beta; [zlia | left; zlia]
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_ext_ok E0 r (fun k _ => eq_refl) Hr) as (X1 & X2 & X3 & X4 & X5 & X6);
eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0) _ Hfr' Hpr); intros a Ha; cbn beta; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *;
[ clear - X1 X2 X3 Ha; zlia | clear - X4 Ha; zlia ] ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | addr_tac | off_by ltac:(addr_tac) ]. }
set (En1 := havoc E0 80 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < sHAV)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; unfold IFRAME;
split; [addr_tac|]; split; [addr_tac|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(addr_tac) | apply PRES1; addr_tac] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK in *; unfold sp0 in *; clear - X1; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac|].
memv HS 0%nat 2%nat; [addr_tac | denot_tac | addr_tac]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2120) 8 (Z.of_nat (length tr))).
{ replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
pose proof tr_length as LEN.
apply val_mem_4_4; [zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | addr_tac].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120) 8 0) by (memv HS 0%nat 1%nat; [addr_tac | reflexivity | zlia]).
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac| exact Z4]. }
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- 2128) (- 2112) 0 0
[YP09.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YP09.mkChunk (- 2120) (CVal 8 (SOff aLEN 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
split; [addr_tac|]; split; [addr_tac|]; split; [intros o Ho; zlia |];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ eapply (chunk_ok_val tfibsegs En1 _ _ (-2128) 8 (SOff 2 (-2112)) (sp0 - 2112));
[cbn [sv_denot]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; denot_tac | addr_tac | cbn; zlia | eapply val_mem_addr; [exact OBJ0 | addr_tac]]
| eapply (chunk_ok_val tfibsegs En1 _ _ (-2120) 8 (SOff aLEN 0) (Z.of_nat (length tr)));
[cbn [sv_denot]; rewrite (HEn1 aLEN (ltHAV aLEN eq_refl)); unfold aLEN; rewrite (eq_refl : ew E0 36 = w64 (Z.of_nat (length tr))); denot_tac
| pose proof tr_length; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); zlia
| cbn; zlia | eapply val_mem_addr; [exact OBJ1 | addr_tac]] ]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME, ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK in *; unfold sp0 in *; clear - X1; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with S_1 in HS by (vm_compute; reflexivity) end.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg ?msf _] => exists msf, mat1, En1 end.
split; [reflexivity|].
split. { split; [exact HEn1 | subst En1; apply ed_havoc]. }
split; [exact HS|].
split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hfr' by (intros Hs; apply Hx; left; exact Hs). apply HF. intros Hw. apply Hx.
exact (windows_WINP E0 (ss_mem S0) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw). }
split; [exact PRES1|].
intros i Hi. cbn [ms_mem mkst]. exact (Ht2 i Hi).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The ENOMEM return: YFjj.v:486 segR, whose one fact (the image's OOM flag cell) is read through cell_litU.         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFjv.v:482 cell_lit at the unpoisoned memory, for an image cell (checked by computation), on the real memory. *)
Lemma cell_litU : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
  ((0 <=? a) && (a + Z.of_nat w <=? TFIB_IMG_END))%bool = true -> val_mem tfibsegs (mrestrict (w_H W) mem0) a w x.
Proof.
intros a w x E R. apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
apply (FAR.val_mem_of_unpoison (w_H W) UP mem0 a w x); [|exact (cell_lit a w x E)].
intros k Hk. apply img_offU'. lia.
Qed.
Local Ltac s_runN HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runN Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma segRU : forall W' c',
at_S W md0 WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W' c' ->
SRr tfibsegs W' c' (at_RETS W (w64 0) md0 WINPN PNULLX).
Proof.
clearP. intros W1 c1 HR. pose proof PBUF_stableN as HP. pose proof WIN1N_WINPN as HX.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _).
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_OOM + 1) 1 1) by (apply cell_litU; vm_compute; reflexivity).
s_noconds HR.
apply (at_S_weaken W md0 WINP WINPN PBUF PBUF _ W1 c1) in HR; [| intros a Ha; left; exact Ha | intros m Hm; exact Hm].
apply (at_S_app W md0 WINPN PBUF _ W1 c1 NREGS) in HR; [| reflexivity |].
2:{ intros E' m HE MEQ PRS HPm HM. pose proof (proj1 HE) as HEn.
assert (OOM1' : val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_OOM + 1) 1 1).
{ eapply val_mem_frame; [|exact OOM1]. intros k Hk. apply MEQ. rewrite unsigned_lit_small by (unfold TFIB_OOM; zlia).
pose proof BSLv_range as HB. clear - Hk F1 F2 S1 T7 HB. unfold WINPN, WINP, WINT, WINI. numconst. unfold TFIB_OOM, TFIB_ERRNO, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. try unfold T in *. zlia. }
split; [|split].
- unfold NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; zlia|]. split; [unfold TFIB_OOM; zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia |]. rewrite Z.add_0_l. exact OOM1'.
+ unfold region_ok, oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; zlia|]. split; [unfold TFIB_OOM; zlia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply img_rw_writable. unfold TFIB_OOM in *. zlia.
+ unfold region_ok, errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_ERRNO; zlia|]. split; [unfold TFIB_ERRNO; zlia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply img_rw_writable. unfold TFIB_ERRNO in *. zlia.
- unfold NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. clear. unfold TFIB_OOM, TFIB_ERRNO. repeat split; zlia.
- intros r1 r2 Hr1 Hr2.
assert (B2 : base_val E' (Some 2%nat) = sp0) by (cbn [base_val]; rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2; reflexivity).
assert (L2' : YP09.r_base r2 = None /\ ((YP09.r_lo r2 = TFIB_OOM + 1 /\ YP09.r_hi r2 = TFIB_OOM + 2) \/ (YP09.r_lo r2 = TFIB_OOM /\ YP09.r_hi r2 = TFIB_OOM + 1) \/ (YP09.r_lo r2 = TFIB_ERRNO /\ YP09.r_hi r2 = TFIB_ERRNO + 4))).
{ unfold NREGS, lit1, oomR, errR in Hr2. destruct Hr2 as [<-|[<-|[<-|[]]]]; cbn; [split; [reflexivity|left; zlia] | split; [reflexivity|right; left; zlia] | split; [reflexivity|right; right; zlia]]. }
destruct L2' as [Hb2 L2].
unfold extent_disjoint. rewrite Hb2. cbn [base_val].
lazymatch type of Hr1 with In _ ?l =>
let m3 := eval vm_compute in (firstn 3 l) in
let tl3 := eval vm_compute in (skipn 3 l) in
assert (SPLIT : In r1 m3 \/ In (skel r1) SKEL_TAIL)
by (change l with (m3 ++ tl3) in Hr1; apply in_app_iff in Hr1 as [Hr1|Hr1]; [left; exact Hr1 | right];
apply (in_map skel) in Hr1; replace (map skel tl3) with SKEL_TAIL in Hr1 by (vm_compute; reflexivity); exact Hr1) end.
clear Hr1. destruct SPLIT as [Hr1|Hr1].
+ destruct Hr1 as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite B2;
clear - L2 S1 T7 U2; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_OOM, TFIB_ERRNO, kHighMemBeg, ASTACK, IFRAME in *; unfold sp0 in *; zlia.
+ pose proof (tail_ext_ok E' r1 HEn Hr1) as (X1 & X2 & X3 & X4 & X5 & X6).
destruct (YP09.r_base r1) as [b|] eqn:Eb.
*
clear X1 X2 X3 X4 X5 X6. destruct r1 as [bs lo hi wlo whi cs]. cbn [YP09.r_base] in Eb. subst bs. unfold skel in Hr1.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hr1 |- *.
let sk := eval vm_compute in SKEL_TAIL in change SKEL_TAIL with sk in Hr1. cbn [In] in Hr1.
repeat match type of Hr1 with _ \/ _ => destruct Hr1 as [Hr1|Hr1]; [first [discriminate Hr1 | injection Hr1 as <- <- <- <- <-] |] | False => destruct Hr1 end.
all: pose proof BSLv_range as HB; cbn [base_val]; rewrite ?(HEn 32%nat ltac:(unfold sHAV; zlia)), ?(HEn 33%nat ltac:(unfold sHAV; zlia)), ?(HEn 55%nat ltac:(unfold sHAV; zlia)); rewrite ?EaT, ?EaC, ?EaBSL; unfold w64;
rewrite unsigned_lit_small by (clear - F1 F2 F7 F8 HB; numconst; unfold TFIB_INST in *; try unfold T in *; zlia); clear - L2 F1 F7 HB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_OOM, TFIB_ERRNO, kHighMemBeg, TFIB_INST in *; try unfold T in *; zlia.
* pose proof (tail_lits_apart r1 Hr1 Eb) as [A1 A2]. cbn [base_val]. clear - L2 A1 A2. unfold TFIB_OOM, TFIB_ERRNO in *. zlia. }
s_station HR S_R0.
s_runN HR tfibtbl_rtC tfibtbl_rtC_ok constr:(PC_LMA_0BC) S_R1 HX HP.
s_runN HR tfibtbl_rtA tfibtbl_rtA_ok constr:(PC_IM_RET) S_RET HX HP.
apply (at_S_facts W md0 WINPN PBUF (fun m => (val_mem tfibsegs (mrestrict (w_H W) m) TFIB_OOM 1 1 /\ val_mem tfibsegs (mrestrict (w_H W) m) TFIB_ERRNO 4 12) /\
(val_mem tfibsegs (mrestrict (w_H W) m) (T + t_unwinding) 1 0 /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_reserved) 8 res /\
val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_n) 8 idx /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_mutex) 4 0 /\
(forall a, WINT a -> apresent (w_H W) m a) /\ (forall a, WINI a -> aview tfibsegs (w_H W) m a <> None))) S_RET) in HR.
2:{ intros E' ms HE HS. pose proof (proj1 HE) as HEn. pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof BSLv_range as HB.
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; clear - F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; unfold TFIB_INST in *; zlia).
split; [split; [memv HS 61%nat 0%nat; [reflexivity | reflexivity | zlia] | memv HS 62%nat 0%nat; [reflexivity | reflexivity | zlia]]|].
split; [memv HS 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UT; unfold t_unwinding; zlia | reflexivity | zlia]|].
split; [memv HS 49%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | rewrite sv_denot_SOff0, (HEn 40%nat ltac:(unfold sHAV; zlia)), EaRES; reflexivity | unfold kMaxNumChunks in *; zlia]|].
split; [memv HS 50%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; reflexivity | unfold kMaxNumChunks in *; zlia]|].
split; [memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]|].
split.
- intros a Hw. unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 40%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 41%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; unfold t_unwinding in *; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, t_unwinding in *; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
- intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB; unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia).
apply (YFib.writable_visible (w_H W) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
+ destruct (Z_lt_le_dec a (TFIB_INST + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (TFIB_INST + 128)) as [A2|A2]].
* eapply (st_ok_window_writable (w_H W) E' _ _ 49%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_reserved in *; zlia].
* eapply (st_ok_window_writable (w_H W) E' _ _ 50%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST in *; zlia].
* eapply (st_ok_window_writable (w_H W) E' _ _ 51%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_sorted in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 52%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_stats in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 59%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_mutex in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; zlia]. }
apply (at_S_weaken W md0 WINPN WINPN _ PNULLX S_RET) in HR; [| intros a Ha; exact Ha | intros m [H1 [H2 H3]]; exact (conj (conj H1 H2) H3)].
change (w64 0) with (sv_denot E0 (SLit 0)).
eapply (at_S_ret W md0 WINPN PNULLX S_RET _ _ (SLit 0) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
repeat constructor.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The mmap node: YFjs.v:512 nodeS; its AR premise is AR of the unpoisoned memory (it reads only the ledger, the     *)
(* model and the Wf of the abstract state from it).                                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma nodeSU : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop) (c1 : config),
aregime S   ->
at_N W md0 WINP PBUF S_N W c1 -> AI tfibsegs (w_H W) (w_A W) (cfg_model c1) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMmapSec MSv) z) ->
(forall c', at_S W (cfg_model c1) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
ALedger tfibsegs ly S (cfg_model c1) -> amwf (cfg_model c1) -> same_io md0 (cfg_model c1) ->
amreal tfibsegs (K 0) W c' Q) ->
(forall (a : word) (W3 : world tfibsegs) (ms : machine_state) (E' : env),
let A := bv_unsigned a in let md2 := mmap_model a (w64 MSv) (cfg_model c1) in
grant_ok_na_pin (cfg_model c1) a MSv = true ->
ALedger tfibsegs ly S (cfg_model c1) -> amwf (cfg_model c1) ->
wle W W3 -> hsub (w_H W3) (w_H W) -> (forall x : word, w_H W x = false -> w_H W3 x = false) ->
w_A W3 = (SHLO A, SHHI A) :: (A, A + MSv) :: w_A W ->
(forall x : word, A <= bv_unsigned x < A + MSv -> w_H W3 x = false) ->
(forall x : word, SHLO A <= bv_unsigned x < SHHI A -> w_H W3 x = false) ->
(forall x : word, ~ (A <= bv_unsigned x < A + MSv) -> ~ (SHLO A <= bv_unsigned x < SHHI A) -> w_H W3 x = w_H W x) ->
AI tfibsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md0 md2 -> eager_used md2 <= eager_used (cfg_model c1) + MSv ->
vm_maps (m_vmmaps md2) = (a, w64 MSv) :: vm_maps (m_vmmaps (cfg_model c1)) /\
vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
env_agree sHAV E0 E' -> st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms) ->
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall y, sp0 - ASTACK <= y < sp0 -> apresent (w_H W) (ms_mem ms) y) -> PBUF (ms_mem ms) ->
amreal tfibsegs (K 1) W3 (mkCfg (mkst (regupd (ms_regs ms) 10%bv a) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill a (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md2) Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W) (w_A W) (cfg_model c1) -> AI tfibsegs (w_H W) (w_A W) (cfg_model (nx i))) /\
(forall i, aok sN (KMmapSec MSv) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W) (w_A W) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) W (nx i) Q).
Proof.
clearP. intros RT sN K Q c1 Hev HN HAI Haok KEEP GRANT IO0.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof HAR as (MA & L0 & BUD & MW & HS0).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md0) mat md0) in *.
assert (EcM : cfg_model c1 = mdN) by (rewrite Ec; reflexivity). rewrite EcM in *.
assert (LN : ALedger tfibsegs ly S mdN) by (exact (ALedger_same tfibsegs ly S md0 mdN L0 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWN : amwf mdN) by (exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW)).
assert (MWF0 : MWF mdN) by (apply (proj1 (amwf_MWF mdN)); exact (proj1 MWN)).
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E' S_N ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
pose proof S_N_facts as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (rewrite (Hregs 17%bv), H17; reflexivity).
assert (R10 : getr regs 10 = Z_to_bv 64 0) by (rewrite (Hregs 10%bv), H10; reflexivity).
assert (R11 : getr regs 11 = Z_to_bv 64 MSv).
{ rewrite (Hregs 11%bv), H11, sv_denot_SOff0. unfold aMS. rewrite (HEn 42%nat ltac:(unfold sHAV; zlia)). exact EaMS. }
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (rewrite (Hregs 12%bv), H12; reflexivity).
assert (R13 : getr regs 13 = Z_to_bv 64 34) by (rewrite (Hregs 13%bv), H13; reflexivity).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; apply lit_m1).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (rewrite (Hregs 15%bv), H15; reflexivity).
assert (MSB : 0 < MSv <= MALLOC_MAX + 4 * 4096) by (clear - Z8 Z1 Z2 Z3; unfold MALLOC_MAX in *; zlia).
destruct (sec_grant_exists_AR B ly S _ mdN MSv HARm LN MWN ltac:(clear - MSB; unfold YF06.NOB, MALLOC_MAX in *; zlia)) as [a0 Ha0].
assert (SL0 : eager_used mdN + A_bytes (w_A W) + 2 ^ 30 <= vm_limit (m_vmmaps mdN)).
{ apply (slackS mdN W 0 HAR Hev L0); [unfold mdN; rewrite m_vmmaps_wvb; reflexivity | unfold mdN; rewrite eager_used_wvb; clear; zlia | clear; zlia | clear; zlia | clear; zlia]. }
assert (PER : forall a : word, grant_ok_na_pin mdN a MSv = true ->
(AI tfibsegs (w_H W) (w_A W) (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) /\ MWF (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)) /\
mmap_noreserve_backed_ok (Z_to_bv 64 34) mdN MSv = true /\
eager_used (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) <= eager_used mdN + MSv /\
maps_nonempty (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)).
{ intros a Ha. pose proof (YFia.grant_parts mdN a MSv Ha) as (Pal & Ppos & Pce & Prf & Ppl).
assert (CE : bv_unsigned a + page_round_up_Z MSv <= alloc_top (m_vmmaps mdN)) by (rewrite pru_MS; exact Pce).
assert (PL' : region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) a (Z_to_bv 64 (page_round_up_Z MSv)) = true) by (rewrite pru_MS; exact Prf).
assert (SL1 : eager_used mdN + A_bytes (w_A W) + page_round_up_Z MSv <= vm_limit (m_vmmaps mdN)) by (rewrite pru_MS; clear - SL0 MSB; unfold MALLOC_MAX in MSB; zlia).
pose proof (commit_AI tfibsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34 ltac:(unfold page_size; exact Pal) (proj1 MSB) CE PL' SL1) as [CG BUDg].
pose proof (commit_eager tfibsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34 ltac:(unfold page_size; exact Pal) (proj1 MSB) CE PL' SL1) as EG.
pose proof (commit_nonempty true (Z_to_bv 64 34) a (Z_to_bv 64 (page_round_up_Z MSv)) mdN ltac:(rewrite pru_MS; unfold w64; rewrite unsigned_lit_small by (clear - MSB; unfold MALLOC_MAX in MSB; zlia); exact (proj1 MSB)) (proj2 MWN)) as NZg.
rewrite pru_MS in CG, BUDg, EG, NZg. fold (w64 MSv) in CG, EG, NZg. exact (conj CG (conj BUDg (conj EG NZg))). }
destruct (PER a0 Ha0) as (_ & BUD0 & _).
destruct (anon_node tfibsegs regs (Z_to_bv 64 PC_MMAP_ECALL) mem (seg_rom tfibsegs) mdN (Z_to_bv 64 34) MSv
(AI_halted _ _ _ _ HAI) R17 R10 R11 ltac:(clear - MSB; unfold MALLOC_MAX in MSB; zlia) R12 R13 core34 R14 R15
ltac:(rewrite pru_MS; exists a0; exact Ha0) ltac:(rewrite pru_MS; exact BUD0)) as (I & nx & bit & ga & i0 & NODE & Bi0 & OUT).
rewrite pru_MS in OUT. fold (w64 MSv) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, bit, (fun _ => false), i0.
split. { rewrite Ec, Hms, Hpc. exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & _ & Hg & -> & ->); cbn [cfg_model]; exact (proj1 (proj1 (PER (ga i) Hg))). }
split. { intros i. apply Haok. destruct (OUT i) as (md_i & _ & _ & Bv & _); clear - Bv; zlia. }
split; [reflexivity|]. split; [exact Bi0|]. split; [intros i _; destruct (OUT i) as (md_i & _ & _ & Bv & _); exact Bv|].
split; [intros i E; discriminate E|].
intros i _. destruct (OUT i) as (md_i & Hh_i & IO_i & Bv & Hg & NX & MD); rewrite Bv, NX; rewrite MD in IO_i |- *.
-
set (a := ga i) in *. set (A := bv_unsigned a) in *.
destruct (PER a Hg) as ([AIg MWFg] & _ & EG & NZg).
pose proof (grant_anon_shape a (w64 MSv) mdN) as (SH1 & SH2 & SH3 & SH4 & SH5).
set (md2 := grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) in *.
pose proof (YFia.grant_parts mdN a MSv Hg) as (Pal & Ppos & Pce & Prf & Ppl).
fold A in Pal, Ppos, Pce.
pose proof (SH_hull A) as (U1' & U2 & U3 & U4 & U5 & U6).
assert (AL1 : A <= A + MSv) by (clear - MSB; zlia).
assert (AL2 : A mod page_size = 0) by (unfold page_size; exact Pal).
assert (AL3 : (A + MSv) mod page_size = 0).
{ unfold page_size. clear - Pal Z9. apply Z.mod_divide in Pal as [q' Hq]; [|zlia]. apply Z.mod_divide in Z9 as [r' Hr]; [|zlia]. rewrite Hq, Hr. apply Z.mod_divide; [zlia|]. exists (q' + r'). zlia. }
destruct (allow_expose tfibsegs W md2 A (A + MSv) AL1 AL2 AL3 AIg ltac:(rewrite SH3; clear - EG SL0 MSB; unfold MALLOC_MAX in MSB; zlia))
as (LE2 & A2 & AB2 & VIS2 & MON2 & AI2).
set (W2 := wallow tfibsegs W A (A + MSv) AL1 AL2 AL3) in *.
assert (SL2 : SHLO A mod page_size = 0) by (unfold page_size; exact U4).
assert (SL3 : SHHI A mod page_size = 0) by (unfold page_size; exact U5).
assert (BUD3 : eager_used md2 + A_bytes (w_A W2) + (SHHI A - SHLO A) <= vm_limit (m_vmmaps md2)).
{ rewrite SH3, AB2. assert (D8 : MSv / 8 <= MSv) by (apply Z.div_le_upper_bound; clear - MSB; zlia). clear - EG SL0 MSB U3 D8. unfold MALLOC_MAX in MSB. zlia. }
destruct (allow_expose tfibsegs W2 md2 (SHLO A) (SHHI A) U6 SL2 SL3 AI2 BUD3)
as (LE3 & A3 & AB3 & VIS3 & MON3 & AI3).
set (W3 := wallow tfibsegs W2 (SHLO A) (SHHI A) U6 SL2 SL3) in *.
assert (MON : forall x : word, w_H W x = false -> w_H W3 x = false) by (intros x Hx; apply MON3, MON2, Hx).
assert (SUB : hsub (w_H W3) (w_H W)).
{ intros x Hx. destruct (w_H W x) eqn:Ex; [reflexivity|]. rewrite (MON x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfibsegs _ W W3); [exact (wle_trans _ _ _ _ LE2 LE3) | intros _; exact AI3 |].
change (with_mmap_backing (Z_to_bv 64 34) a (w64 MSv) (mmap_model a (w64 MSv) mdN)) with md2.
pose proof (GRANT a W3 ms E' Hg LN MWN (wle_trans _ _ _ _ LE2 LE3) SUB MON) as G. cbv zeta in G. rewrite <- SH5 in G. fold md2 in G. fold A in G.
rewrite Hms in G. cbn [ms_regs ms_mem pend_at] in G. apply G; clear G.
+ rewrite A3, A2. reflexivity.
+ intros x Hx. apply MON3. apply VIS2. exact Hx.
+ exact VIS3.
+ intros x N1 N2. unfold W3, W2, wallow. cbn [w_H]. rewrite (Hcut_out _ (SHLO A) (SHHI A) x) by exact N2. apply Hcut_out. exact N1.
+ exact AI3.
+ split; [apply (proj2 (amwf_MWF md2)); exact MWFg | exact NZg].
+ exact (IOtr _ IO_i).
+ exact EG.
+ rewrite SH1, SH2, SH3, SH4. repeat split; reflexivity.
+ exact HE.
+ rewrite Hms in HS. exact HS.
+ intros x Hx. rewrite <- (MEQ x Hx), Hms. reflexivity.
+ intros y Hy. rewrite Hms in PRS. exact (PRS y Hy).
+ rewrite Hms in HPm. exact HPm.
Qed.

(* YFjv.v:422 vis_present at the unpoisoned memory, on the real memory for a byte off UP. *)
Lemma vis_presentU : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
  aeval B ly e <= a < aeval B ly e + len -> off_img a -> FAR.offU UP a -> apresent (w_H W) mem0 a.
Proof.
intros e len a Hin Ha Hhi O. apply (FAR.apresent_of_unpoison (w_H W) UP mem0 a O). exact (vis_present e len a Hin Ha Hhi).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFk0.v Section f: the ENOMEM leaf refuseSU (YFk0.v:797 refuseS) and QLEAFU, the any-U form of YFk0.v QLEAF.     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Local Abbreviation S1 := (@YFk0.S1 S).
Local Abbreviation sec_body := (@YFk0.sec_body n).
Local Abbreviation KSEC := (@YFk0.KSEC ly regs0 n ch S).
Definition QLEAFU (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
Wf (as_universe B) (snd r) /\ qtight (snd r) -> FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W' c'.
Local Open Scope am_scope.
Lemma at_S_wvb : forall (Wx : world tfibsegs) md mat X P ss W' c',
at_S Wx (with_vm_backing (m_vm_lazy md) mat md) X P ss W' c' -> at_S Wx md X P ss W' c'.
Proof. clear. intros Wx md mat X P ss W' c' (-> & ms & mat' & E' & -> & HE & HS & MEQ & PRS & HP). split; [reflexivity|]. exists ms, mat', E'. rewrite wvb_collapse. split; [reflexivity|]. repeat (split; [assumption|]). exact HP. Qed.
Lemma errno_not_ownedU : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
clearP. intros a Ha O.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. change tfibsegs with YB1h.TSEGS. unfold YB1h.TSEGS. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. zlia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S W mem0u md0 a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]). cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; zlia|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S TFIB_OOM.
Proof. clearP. apply (own_area B ly S _ (as_oom_byte B, 1) TFIB_OOM HARm); [unfold asyms_areas; cbn; tauto|]. cbn [fst snd]. rewrite (ts_oom B TS). zlia. Qed.
Lemma val_mem_aview : forall (Hh : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict Hh m) a w v -> (k < w)%nat ->
aview tfibsegs Hh m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
clear. intros Hh m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Theorem refuseSU : forall (mat : list word) c',
aregime S   ->
at_S W (with_vm_backing (m_vm_lazy md0) mat md0) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfibsegs (KSEC 0) W c' QLEAFU.
Proof.
clearP. intros mat c' Hev HR. change (amreal tfibsegs (KSEC 0) W c' QLEAFU) with (SRr tfibsegs W c' (QLEAFU (PNull, S1))).
apply at_S_wvb in HR. eapply SRr_mono; [exact (segRU _ _ HR)|].
intros W2 c2 _ (-> & regs' & mem' & mat2 & -> & R10 & RCS & MEQ & PRS & ((HB & VOOM & VERR) & (Vunw & Vres & Vnch & Vmtx & PRT & VISI))) [WF1 QT1]. cbn [fst snd] in WF1, QT1.
pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof BSLv_range as HB'.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof (ts_inst B TS) as EI.
set (md' := with_vm_backing (m_vm_lazy md0) mat2 md0).
assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> ~ WINT a -> ~ WINI a -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3 N4 N5. apply MEQ. rewrite unsigned_lit_small by exact Ra. unfold WINPN, WINP. clear - N1 N2 N3 N4 N5. intros [[X|[X|X]]|[X|X]]; try tauto; zlia. }
assert (ARF : AR tfibsegs B ly S W (FSP.unpoison UP mem') md').
{ apply (YFic.AR_snull B ly S W mem0u (FSP.unpoison UP mem') md0 md' BSLv HB' TS HAR).
-
intros a Ra Ho NX. apply aview_same. apply unp_eq. apply NW; [exact Ra | | | | |].
+ intros ST. exact (AR_stack_law_ok tfibsegs B ly S W mem0u md0 a HAR ltac:(clear - ST S1' S3'; unfold ASTACK in *; try unfold sp0 in *; zlia) Ho).
+ intros X. apply NX. unfold YFic.XN. unfold WINT, t_unwinding in X. unfold T in X. clear - X. zlia.
+ intros X. apply NX. unfold YFic.XN. unfold WINI in X. clear - X. zlia.
+ intros ->. apply NX. unfold YFic.XN. left. zlia.
+ intros X. exact (errno_not_ownedU a X Ho).
-
apply vis_unp.
intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
assert (AV : forall (Hh : word -> bool) m, aview tfibsegs Hh m a0 = aview tfibsegs Hh m a) by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
assert (PRES : forall u, apresent (w_H W) mem' u -> aview tfibsegs (w_H W) mem' u <> None) by (clear; intros u [Hh [b Hb]]; unfold aview, mbyte, mrestrict; rewrite Hh, Hb; cbn; discriminate).
assert (VAL : forall u base (w : nat) v, val_mem tfibsegs (mrestrict (w_H W) mem') base w v -> base <= u < base + Z.of_nat w -> aview tfibsegs (w_H W) mem' u <> None).
{ clear. intros u base w v HV Hu. replace u with (base + Z.of_nat (Z.to_nat (u - base))) by zlia. rewrite (val_mem_aview (w_H W) mem' base w v (Z.to_nat (u - base)) HV ltac:(zlia)). discriminate. }
destruct (zr_dec (sp0 - ASTACK) sp0 a) as [D1|D1]; [apply PRES; apply PRS; exact D1|].
assert (DT : WINT a \/ ~ WINT a) by (clear; unfold WINT; zlia). destruct DT as [D2|D2]; [apply PRES; apply PRT; exact D2|].
assert (DI : WINI a \/ ~ WINI a) by (clear; unfold WINI; zlia). destruct DI as [D3|D3]; [exact (VISI a D3)|].
destruct (Z.eq_dec a TFIB_OOM) as [->|D4]; [apply (VAL _ _ _ _ VOOM); cbn; zlia|].
destruct (zr_dec TFIB_ERRNO (TFIB_ERRNO + 4) a) as [D5|D5]; [apply (VAL _ _ _ _ VERR); cbn; zlia|].
rewrite (aview_same (w_H W) mem0 mem' a (NW a Ra D1 D2 D3 D4 D5)). exact HV0.
-   rewrite FAR.aview_unpoison by (apply T_offU; unfold t_unwinding, kThreadObjSize; lia).
pose proof (val_mem_aview _ _ _ _ _ 0%nat Vunw ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold T in X. exact X.
- intros k Hk. rewrite FAR.aview_unpoison by (apply img_offU'; unfold TFIB_INST, o_sec_reserved, TFIB_IMG_END; lia). rewrite <- Hres_def. exact (val_mem_aview _ _ _ _ _ k Vres Hk).
- intros k Hk. rewrite FAR.aview_unpoison by (apply img_offU'; unfold TFIB_INST, o_sec_n, TFIB_IMG_END; lia). rewrite <- Hidx_def. exact (val_mem_aview _ _ _ _ _ k Vnch Hk).
- intros k Hk. rewrite FAR.aview_unpoison by (apply img_offU'; unfold TFIB_INST, o_sec_mutex, TFIB_IMG_END; lia). replace k with (Z.of_nat (Z.to_nat k)) by zlia. rewrite (val_mem_aview _ _ _ _ _ (Z.to_nat k) Vmtx ltac:(zlia)). f_equal.
clear - Hk. unfold YG0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
- unfold md'. apply m_vmmaps_wvb.
- unfold md'. apply m_vm_lazy_wvb.
- unfold md'. apply eager_used_wvb.
-   intros a Ha _. unfold YG0n.w64. apply unp_eq. apply NW.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd in Ha. zlia.
+ clear - Ha S1' T7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. try unfold sp0 in *. zlia.
+ clear - Ha F1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, WINT, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_unwinding in *. try unfold T in *. zlia.
+ clear - Ha HB'. unfold WINI, kHighShadowBeg, kHighShadowEnd, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. zlia. }
exists ly, regs', mem', md'.
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [| split; [rewrite R10; cbn [fst sptr_addr sptr_exp aeval]; reflexivity | exact QT1]].
apply (FAR.acall_postU_intro B ASTACK ly S UP W regs0 mem0 md0 _ ly (snd (PNull, S1)) W regs' mem' md' HARU).
{ exact (AR_tick B ly S W (FSP.unpoison UP mem') md' ARF Hev). }
{ apply layout_le_refl. }
{ apply wle_refl. }
{ intros r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
{ unfold md'; apply YG0b.same_io_with_vm_backing. }
{ intros a Ra NO NO' NS NE. apply aview_same. apply NW; [exact Ra | | | | |].
- intros ST. apply NS. unfold ascratch, spZ. left. exact ST.
- intros X. exact (NO (OWN_T a X)).
- intros X. exact (NO (OWN_I a X)).
- intros ->. exact (NO oom_owned).
- intros X. apply NS. unfold ascratch. right. rewrite (ts_errno B TS). exact X.
}
{ exact PRS. }
{ exact (FAR.upoison_ok_keep B ly S ly (snd (PNull, S1)) UP (FSP.ARU_ok tfibsegs B ly S UP W mem0 md0 HARU) (fun r p nn _ Hb _ _ => Hb)). }
{ apply (FAR.upoisoned_keep UP W W mem0 mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem0 md0 HARU)).
  intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem0 md0 s HARU Hs) as (_ & L1 & L2).
  apply aview_same. apply NW.
  - clear - L1 L2. unfold SHADOW_OFF, kHighMemBeg in *. lia.
  - apply (ush_not s _ Hs). exact (stk_offU s).
  - apply (ush_not s _ Hs). intros X. apply T_offU. unfold WINT in X. unfold t_unwinding, kThreadObjSize in *. lia.
  - apply (ush_not s _ Hs). intros X. apply img_offU'. pose proof BSLv_range as HBs. unfold WINI in X. unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_END in *. lia.
  - intros ->. unfold TFIB_OOM, SHADOW_OFF in *. lia.
  - intros X. unfold TFIB_ERRNO, SHADOW_OFF in *. lia. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot call: YFju.v:730 D1W_ok. Its depot and constant-cell preconditions come from AR of the unpoisoned       *)
(* memory and move to the real one: the depot zone and every constant cell are off UP (DZ_offU, const_offU).         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section dw.
Variable Wy : world tfibsegs.
Hypothesis MONy : forall x : word, w_H W x = false -> w_H Wy x = false.
Hypothesis Htr : areq_ok S (KDepot tr).
Hypothesis HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Hypothesis HDPOST' : forall z m, DPOSTS Wy z m -> DPOST z m.
Lemma rd_ext_WyU : forall mem, rd_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H Wy) mem).
Proof.
intros mem. apply aview_ext; [apply w_Hoff|]. intros x Hx. destruct (w_H W x) eqn:E; [reflexivity|]. rewrite (MONy x E) in Hx. discriminate Hx.
Qed.
Lemma D1W_okU : tfib_depot_spec B ->
forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 RA_DEPOT_PUT ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
PBUFW Wy mem -> (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (TFIB_INST + o_sec_mutex + k) = Some 0) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 RA_DEPOT_PUT) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Proof.
intros HD1 X regs mem md HXQ R10 R11 R3 R4 R1 Rsp BUF PRES MEQ MUT0.
destruct Hsp as (S1 & S2 & S3 & S4). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (MEQ' : forall a, 0 <= a < 2 ^ 64 -> ~ WIN a -> ~ QR a -> mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply MEQ. rewrite unsigned_lit_small by exact Ha. intros HX. destruct (HXQ a HX) as [H|H]; [exact (N1 H) | exact (N2 H)]. }
assert (CST : Forall (cell_holds B ly (aview tfibsegs (w_H Wy) mem)) (as_const B ly)).
{ apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly S rd0 HARm) c Hc) as HOLD.
pose proof (const_cells_CZ c) as CCZ. destruct (padb c) eqn:Ep.
-
pose proof Hc as Hc'. rewrite (ts_const B TS ly) in Hc'. unfold Tfib_const in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
{ exfalso. revert Ep Hc'. clear. intros Ep Hc'. unfold Tfib_const_sym in Hc'. cbn [In] in Hc'.
repeat match type of Hc' with _ \/ _ => destruct Hc' as [<-|Hc']; [discriminate Ep|] | False => destruct Hc' end. }
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => negb (padb c) || match c_val c with AV (ANum 0) => true | _ => false end) (Tfib_const_abs ++ Tfib_const_shadow) = true) c Hc') as CK.
cbn beta in CK. rewrite Ep in CK. cbn [negb orb] in CK.
unfold padb in Ep. unfold cell_holds. destruct (c_at c) eqn:Ea; try discriminate Ep. cbn [aeval] in CCZ |- *.
destruct (c_val c) as [e|mk vv]; [|discriminate CK]. destruct e; try discriminate CK.
lazymatch goal with |- context [aeval _ _ (ANum ?zz)] => destruct zz; try discriminate CK end.
intros k Hk. cbn [aeval]. pose proof (CCZ (Z.of_nat k) Hc ltac:(zlia)) as Pk. unfold MPAD in Pk.
lazymatch goal with |- _ (?a + Z.of_nat k) = _ =>
replace (a + Z.of_nat k) with (TFIB_INST + o_sec_mutex + (a + Z.of_nat k - (TFIB_INST + o_sec_mutex))) by zlia end.
rewrite MUT0 by zlia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; zlia). rewrite Z.shiftr_0_l. reflexivity.
-
apply (Forall_inv (l := [])). apply (Forall_cell_holds_ext B ly _ _ _ (rd_ext_WyU mem)). apply Forall_cons; [|apply Forall_nil].
apply (cell_holds_agree rd0); [| exact HOLD].
intros k Hk. pose proof (CZ_untouched HmapD _ (CCZ k Hc Hk)) as (Ra & N1 & N2 & _). unfold rd0. apply aview_agreeW; [exact Ra|]. rewrite (MEQ' _ Ra N1 N2). symmetry. exact (FAR.unpoison_offU UP mem0 _ (const_offU c k Hc Hk)). }
assert (DEP : depot_mem_ok B ly S (aview tfibsegs (w_H Wy) mem)).
{ apply (depot_mem_ok_ext S _ _ (rd_ext_WyU mem)). apply (depot_mem_ok_agree S rd0); [| | exact depot_at0].
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S _ (conj ND INC)). zlia. }
intros a Ha. pose proof (DZONE_disj a Ha) as (N1 & _). pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _).
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof Hres as [HRS _]. pose proof Hidx as HI.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia).
unfold rd0. apply aview_agreeW; [exact Ra|]. rewrite (FAR.unpoison_offU UP mem0 a (DZ_offU a Ha)). apply (MEQ' _ Ra N1).
unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB. unfold QR. clear - Ha QNB QSB F9 HRS HI.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia. }
eapply SRr_mono.
{ apply (HD1 Wy ly S regs mem md (sp0 - IFRAME + 16) tr LY IMG WF Htr CST DEP R10 R11).
- rewrite R3, Hgp. reflexivity.
- exact R4.
- rewrite R1. apply ret_ok_even. reflexivity.
- exact BUF.
- unfold IFRAME. apply Z.mod_divide; [zlia|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (2 * q - 264). zlia.
- unfold IFRAME, ASTACK in *. zlia.
- unfold IFRAME, ASTACK in *. zlia.
- right. rewrite Rsp. unfold IFRAME. zlia.
- rewrite Rsp. apply Z.mod_divide; [zlia|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (q - 142). zlia.
- rewrite Rsp. unfold DEP_STK, ASTACK in *. zlia.
- rewrite Rsp. zlia.
- rewrite Rsp. intros a Ha. apply PRES. unfold DEP_STK, ASTACK in *. zlia. }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [rewrite R1; reflexivity|]. split; [exact RP|]. split; [|split; [exact PR'| apply HDPOST'; exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [rewrite Rsp; exact N1|].
intros FP. apply N2. unfold depot_footprint, DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. zlia.
Qed.
End dw.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The grant leaf: YFjz.v:1013 LEAF_S. AR_transport (YFjy.v:1771, S_AR_final) is applied at the unpoisoned memories: *)
(* fin_facts_unp moves the leaf's facts there (every byte they read is off UP: the thread object, the instance, the   *)
(* pointer array, the depot zone, the constant cells, the new extent and its shadow); the frame and the presence are  *)
(* the donor's on the real memories; UP stays inside live blocks (ablocks_lyF) and keeps its 0xf7 bytes.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma mapsh_in : forall x, (SMv <= x < SMv + 768 \/ SHBv + UEv / 8 <= x < SMv + MSv / 8) -> SMv <= x < SMv + MSv / 8.
Proof.
intros x Hx. pose proof size_facts as (Z1 & _ & _ & _ & _ & _ & _ & Z8 & _).
assert (D : SMv <= SHBv + UEv / 8).
{ unfold YFjm.SMv, YFjm.UEv. apply Z.add_le_mono_l. apply Z.div_le_mono; [lia|]. unfold YFjm.R8v in *. lia. }
assert (M : 768 <= MSv / 8) by (apply Z.div_le_lower_bound; lia).
lia.
Qed.
Lemma fin_facts_unp : forall grow z Wz regs' mem' memD,
  Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
  fin_facts grow z Wz regs' mem' memD ->
  YFjy.fin_facts ly regs0 mem0u n ch idx res mb B S grow z Wz regs' (FSP.unpoison UP mem') (FSP.unpoison UP memD).
Proof.
intros grow z Wz regs' mem' memD GAP HF.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & M7 & _ & _ & _ & _ & SM1 & SM2 & _ & M15 & SMA).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).
pose proof Hidx as HI. pose proof Hres as [HRS _].
destruct HF as [AOK DEPD CSTD PRD EQD MEQF PRS PRmap PRsh PRq PRW VISW R10 RCS Vsh Vzs Vpb Vunw Vres Vnch Vmtx Vpad Vslot
  Vh0 Vh8 Vh16 Vh24 Vmag Vbk Vst Vb1 Vb2 Vn Vfill].
assert (MAPB : forall a (w : nat), mb <= a -> a + Z.of_nat w <= mb + MSv -> forall k, (k < w)%nat -> FAR.offU UP (a + Z.of_nat k))
  by (intros a w A1 A2 k Hk; apply map_offU; lia).
assert (IMGB : forall a (w : nat), 0 <= a -> a + Z.of_nat w <= TFIB_IMG_END -> forall k, (k < w)%nat -> FAR.offU UP (a + Z.of_nat k))
  by (intros a w A1 A2 k Hk; apply img_offU'; lia).
assert (NDM : 769 + N8D / 8 <= MSv / 8).
{ clear - Z3 Z4 Z7 Z10. replace (769 + N8D / 8) with ((N8D + 769 * 8) / 8) by (rewrite Z.div_add by lia; lia).
  apply Z.div_le_mono; lia. }
constructor.
- exact AOK.
- apply (depot_mem_ok_agree _ (aview tfibsegs (w_H Wz) memD)); [| | exact DEPD].
  + pose proof (wf_depot _ _ _ _ _ WF) as [ND INCL]. pose proof (depot_ids_bound S _ (conj ND INCL)) as IB. unfold depot_after. destruct (z =? 0); [zlia|].
    unfold depot_ids in *. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. zlia.
  + intros a Ha. apply FAR.aview_unpoison. exact (DZ_offU a Ha).
- apply Forall_forall. intros c Hc. apply (cell_holds_agree (aview tfibsegs (w_H Wz) memD)); [|exact (proj1 (Forall_forall _ _) CSTD c Hc)].
  intros k Hk. apply FAR.aview_unpoison. exact (const_offU c k Hc Hk).
- intros a Ha Hp. apply FAR.apresent_to_unpoison. apply (PRD a Ha). exact (FAR.apresent_of_unpoison _ UP mem0 a (DZ_offU a Ha) Hp).
- intros x Hx. unfold FSP.unpoison. rewrite (EQD x Hx). reflexivity.
- intros x N1 N2 N3. unfold FSP.unpoison. rewrite (MEQF x N1 N2 N3). reflexivity.
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRS a Ha).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRmap a Ha).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRsh a Ha).
- intros G a Ha. apply FAR.apresent_to_unpoison. exact (PRq G a Ha).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRW a Ha).
- intros a Ha. rewrite FAR.aview_unpoison; [exact (VISW a Ha)|]. apply img_offU'. pose proof BSLv_range as HB.
  unfold WINI in Ha. unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_END in *. lia.
- exact R10.
- exact RCS.
- intros x Hx. rewrite FAR.unpoison_offU_w; [exact (Vsh x Hx)|]. exact (mapsh_offU GAP _ (mapsh_in _ Hx)).
- intros x Hx. rewrite FAR.unpoison_offU_w; [exact (Vzs x Hx)|]. apply (mapsh_offU GAP). clear - Hx NDM. lia.
- intros H8. apply FAR.val_mem_to_unpoison; [|exact (Vpb H8)]. intros k Hk. apply (mapsh_offU GAP). rewrite M15. assert (N8P : 0 <= N8D / 8) by (apply Z.div_pos; lia). clear - Hk NDM N8P. lia.
- apply FAR.val_mem_to_unpoison; [|exact Vunw]. intros k Hk. apply T_offU. try unfold T. unfold t_unwinding, kThreadObjSize. lia.
- apply FAR.val_mem_to_unpoison; [|exact Vres]. apply IMGB; simpl Z.of_nat; unfold TFIB_INST, o_sec_reserved, TFIB_IMG_END; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vnch]. apply IMGB; simpl Z.of_nat; unfold TFIB_INST, o_sec_n, TFIB_IMG_END; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vmtx]. apply IMGB; simpl Z.of_nat; unfold TFIB_INST, o_sec_mutex, TFIB_IMG_END; lia.
- intros k Hk. rewrite FAR.aview_unpoison; [exact (Vpad k Hk)|]. apply img_offU'. unfold TFIB_INST, o_sec_mutex, TFIB_IMG_END. lia.
- apply FAR.val_mem_to_unpoison; [|exact Vslot]. intros k Hk. apply Q_offU. unfold YFjm.QSv in *. unfold kPtrArrayResv, kMaxNumChunks in *. lia.
- apply FAR.val_mem_to_unpoison; [|exact Vh0]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vh8]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vh16]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vh24]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vmag]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vbk]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vst]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vb1]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vb2]. apply MAPB; simpl Z.of_nat; lia.
- apply FAR.val_mem_to_unpoison; [|exact Vn]. apply MAPB; simpl Z.of_nat; lia.
- intros x Hx. rewrite FAR.unpoison_offU_w; [exact (Vfill x Hx)|]. apply map_offU. lia.
Qed.
(* Every live block of S keeps its address under the new layout and stays live in the leaf state. *)
Lemma ablocks_lyF : forall grow z p nn, In (p, nn) (ablocks B ly S) -> In (p, nn) (ablocks B lyF (SFS grow z)).
Proof.
intros grow z p nn Hb. pose proof (SF_parts grow z) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _).
unfold ablocks, blocks in *. apply in_map_iff in Hb as ([q m] & E & Hb). apply in_map_iff in Hb as (k & E2 & Hk).
apply filter_In in Hk as [Hk Ha]. injection E2 as E3 E4. subst q m. cbn [fst snd] in E.
apply in_map_iff. exists (ck_user k, ck_req k). split.
- cbn [fst snd]. rewrite <- E. f_equal.
  unfold ck_user. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (YFib.padd_lt S _ _ (YFib.chunk_lt S _ _ _ _ WF k Hk))). reflexivity.
- apply (in_map (fun k0 => (ck_user k0, ck_req k0)) _ k). apply filter_In. split; [rewrite Rck; apply in_or_app; left; exact Hk | exact Ha].
Qed.
(* The windows of the grant walk (WIN, the grown pointer array QR, the depot DX) are off UP. *)
Lemma WIN_offU : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
  forall a, WIN a -> FAR.offU UP a.
Proof.
intros GAP a Hw. pose proof BSLv_range as HB. pose proof Hidx as HI.
unfold WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- exact (stk_offU a Hw).
- apply T_offU. unfold WINT in Hw. unfold t_unwinding, kThreadObjSize in *. lia.
- apply img_offU'. unfold WINI in Hw. unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_END in *. lia.
- unfold WINM in Hw. destruct Hw as [Hw|[Hw|Hw]].
  + apply Q_offU. unfold YFjm.QSv in *. unfold kPtrArrayResv, kMaxNumChunks in *. lia.
  + exact (map_offU a Hw).
  + exact (mapsh_offU GAP a Hw).
Qed.
Lemma QR_offU : forall a, QR a -> FAR.offU UP a.
Proof. intros a Hq. pose proof Hidx as HI. pose proof Hres as [HRS _]. apply Q_offU. unfold YFjp.QR in Hq. unfold kPtrArrayResv in *. lia. Qed.
Lemma DX_offU : forall a, DX a -> FAR.offU UP a.
Proof.
intros a Hd. unfold YFjp.DX in Hd. destruct Hd as [Hd|Hd]; [| exact (DZ_offU a Hd)]. apply stk_offU. unfold DEP_STK, ASTACK in *. lia.
Qed.
Section lf.
Variables (grow : bool) (z : Z) (Wz : world tfibsegs) (mdl : Model).
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis LEz : wle W Wz.
Hypothesis IOz : same_io md0 mdl.
Hypothesis HWZ : forall mat, wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdl) mat mdl).
Hypothesis HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x.
Theorem LEAF_SU : forall regs' mem' memD mat,
Wf (as_universe B) (SFS grow z) /\ qtight (SFS grow z) ->
fin_facts grow z Wz regs' mem' memD ->
FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n (ck_user KSc, SFS grow z) Wz
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdl) mat mdl)).
Proof.
intros regs' mem' memD mat MP HF. set (mdf := with_vm_backing (m_vm_lazy mdl) mat mdl).
pose proof (HWZ mat) as HW. fold mdf in HW.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hsp as (S1 & S2 & S3 & S4). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof HW as [MONf _ _ _ _ _ _ _ _ _ GAP]. pose proof blocks_facts as (NBhi & SBhi & _).
pose proof HF as [_ _ _ _ _ fMEQF fPRS _ _ _ _ _ fR10 fRCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
exists lyF, regs', mem', mdf.
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [| split; [| exact (proj2 MP)]].
2:{ rewrite fR10. cbn [fst]. unfold ck_user. cbn [YG00.ck_beg KSc YFib.KS padd sptr_addr sptr_exp aeval].
change (YG00.ck_rz (YFib.KS S n)) with (ck_rz KSc). rewrite KR, lyF_sec. unfold Uv, YG0d.w64, w64, kPage. f_equal; zlia. }
apply (FAR.acall_postU_intro B ASTACK ly S UP W regs0 mem0 md0 _ lyF (SFS grow z) Wz regs' mem' mdf HARU).
{ exact (S_AR_final grow z Wz mdf regs' (FSP.unpoison UP mem') (FSP.unpoison UP memD) HAR Hgrow MP (fin_facts_unp grow z Wz regs' mem' memD GAP HF) HW). }
{ exact lyF_le. }
{ exact LEz. }
{ intros r Hr. apply fRCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - H18 MZ.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
{ unfold mdf. eapply YG0b.same_io_trans; [exact IOz | apply YG0b.same_io_with_vm_backing]. }
{ intros a Ra NO NO' NS NE. cbn [fst] in NE.
assert (NE' : ~ (Uv <= a < Uv + n)).
{ intros Hu. apply NE. split; [discriminate|]. unfold ck_user. cbn [YG00.ck_beg KSc YFib.KS padd sptr_addr sptr_exp aeval].
change (YG00.ck_rz (YFib.KS S n)) with (ck_rz KSc). rewrite KR, RS, lyF_sec. unfold Uv in Hu. unfold kPage. clear - Hu MZ. zlia. }
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros Hs; apply NS; unfold ascratch, spZ; left; exact Hs).
set (x := Z_to_bv 64 a). assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ra).
assert (MEQa : mem' x = mem0 x).
{ apply fMEQF; rewrite Ux.
- intros Hw. unfold WIN, WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
+ exact (NST Hw).
+ exact (NO (OWN_T a Hw)).
+ exact (NO (OWN_I a Hw)).
+ apply NO, OWN_Q. unfold QSv in Hw. clear - Hw HI HRS MZ. try unfold Qb in *. unfold kPtrArrayResv, kMaxNumChunks in *. zlia.
+ exact (NO' (NEWOWN grow z GAP a Hw NE')).
+ exact (NO (OWN_SH GAP a Hw)).
- intros [_ Hq]. apply NO, OWN_Q. unfold QR in Hq. clear - Hq HRS HI MZ. try unfold Qb in *. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. zlia.
- intros [Hs|Hd]; [apply NST; clear - Hs MZ; unfold DEP_STK, ASTACK in *; zlia | exact (NO (OWN_D a Hd))]. }
destruct (w_H W x) eqn:EhW.
-
destruct (w_H Wz x) eqn:EhZ.
+ unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ. reflexivity.
+ exfalso. destruct (zr_dec mb (mb + MSv) a) as [D1|D1]; [exact (NO' (NEWOWN grow z GAP a D1 NE'))|].
destruct (zr_dec (SHLO mb) (SHHI mb) a) as [D2|D2].
{ apply NO. apply (OWN_BANDhid HAR a); [| subst x; exact EhW]. clear - D2 H1 H2 SM1 SM2 H3 M1 M2 M3 Z8 SMA MZ.
unfold SHLO, SHHI, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(zlia)).
pose proof (Z.div_mod (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)).
pose proof (Z.div_mod MSv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)). zlia. }
destruct grow eqn:Eg.
* destruct (zr_dec QSv (QSv + 131072) a) as [D3|D3].
{ apply NO, OWN_Q. pose proof (proj1 Hgrow eq_refl) as EIR. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ (proj1 MP))) as WR.
pose proof (SF_parts true z) as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _). rewrite Rarr, Rres in WR.
unfold QSv in D3. clear - D3 HI HRS EIR WR MZ. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. zlia. }
rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | rewrite Ux; intros [_ Hq]; exact (D3 Hq)].
* rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | intros [E _]; discriminate E].
-
pose proof (MONf x EhW) as EhZ. unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ, MEQa. reflexivity.
}
{ exact fPRS. }
{ apply (FAR.upoison_ok_keep B ly S lyF (SFS grow z) UP (FSP.ARU_ok tfibsegs B ly S UP W mem0 md0 HARU)).
  intros r p nn _ Hb _ _. exact (ablocks_lyF grow z p nn Hb). }
{ apply (FAR.upoisoned_keep UP W Wz mem0 mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem0 md0 HARU)).
  intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem0 md0 s HARU Hs) as (_ & L1 & L2).
  assert (Rs : 0 <= s < 2 ^ 64) by (clear - L1 L2; unfold SHADOW_OFF, kHighMemBeg in *; lia).
  destruct (FAR.ush_present B ly S UP W mem0 md0 s HARU Hs) as [Hh [b Hb]].
  assert (MEQs : mem' (Z_to_bv 64 s) = mem0 (Z_to_bv 64 s)).
  { apply fMEQF; rewrite unsigned_lit_small by exact Rs.
    - apply (ush_not s _ Hs). exact (WIN_offU GAP s).
    - apply (ush_not s _ Hs). intros [_ Hq]. exact (QR_offU s Hq).
    - apply (ush_not s _ Hs). exact (DX_offU s). }
  unfold aview, mbyte, mrestrict. rewrite Hh, (MONf _ Hh), MEQs. reflexivity. }
Qed.
End lf.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The grant leaves: YFk0.v Section h (grantS_ne :1200, grantS_eq :1267) over the section's HAR (AR of the           *)
(* unpoisoned memory). SHZ reads the new extent's shadow on the real memory (mapsh_offU); QSP3 reads the pointer     *)
(* array on the real memory (vis_presentU); the depot call is D1W_okU; the leaf is LEAF_SU.                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Local Ltac step HR e :=
eapply SRr_bind; [exact e | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR].
Section h.
Variables (W3 : world tfibsegs) (mat : list word) (ms : machine_state) (E' : env) (mb0 : Z).
Let mdN : Model := with_vm_backing (m_vm_lazy md0) mat md0.
Let md2 : Model := mmap_model (w64 mb) (w64 MSv) mdN.
Let ccont : config := mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md2.
Hypothesis Hev : aregime S.
Hypothesis Htr : areq_ok S (KDepot tr).
Hypothesis D1 : tfib_depot_spec B.
Hypothesis HBC : BCELLS.
Hypothesis HDP : forall z m, DPOST z m <-> DPOSTS W3 z m.
Hypothesis GOK : grant_ok_na_pin mdN (w64 mb) MSv = true.
Hypothesis LE3 : wle W W3.
Hypothesis SUB3 : hsub (w_H W3) (w_H W).
Hypothesis MON3 : forall x : word, w_H W x = false -> w_H W3 x = false.
Hypothesis A3 : w_A W3 = (SHLO mb, SHHI mb) :: (mb, mb + MSv) :: w_A W.
Hypothesis VISM3 : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H W3 x = false.
Hypothesis VISH3 : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb -> w_H W3 x = false.
Hypothesis OUT3 : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> w_H W3 x = w_H W x.
Hypothesis AI2 : AI tfibsegs (w_H W3) (w_A W3) md2.
Hypothesis MW2 : amwf md2.
Hypothesis IO2 : same_io md0 md2.
Hypothesis EG2 : eager_used md2 <= eager_used mdN + MSv.
Hypothesis VM2 : vm_maps (m_vmmaps md2) = (w64 mb, w64 MSv) :: vm_maps (m_vmmaps mdN) /\ vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps mdN) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps mdN) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps mdN).
Hypothesis HE' : env_agree sHAV (E0_at mb0) E'.
Hypothesis HS : st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms).
Hypothesis MEQ : forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x.
Hypothesis PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Hypothesis HB : PBUF (ms_mem ms).
Let MA : ARm B ly S rd0 := proj1 HAR.
Lemma LN : ALedger tfibsegs ly S mdN.
Proof. exact (ALedger_same tfibsegs ly S md0 mdN (proj1 (proj2 HAR)) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)). Qed.
Lemma MWN : amwf mdN.
Proof. exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (proj1 (proj2 (proj2 (proj2 HAR))))). Qed.
Lemma MSB : 0 < MSv <= MALLOC_MAX + 4 * 4096.
Proof. clearP. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). clear - Z8 Z1 Z2 Z3. unfold MALLOC_MAX in *. zlia. Qed.
Lemma Umb : bv_unsigned (w64 mb) = mb.
Proof. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). unfold w64. apply unsigned_lit_small. clear - M1 M2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia. Qed.
Lemma GAP : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof (YFia.grant_apart B ly S rd0 mdN (w64 mb) MSv MA LN MSB ltac:(pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _); exact Z9) GOK) as X.
rewrite Umb in X. exact X.
Qed.
Lemma SHZ : forall a, SMv <= a < SMv + MSv / 8 -> w_H W3 (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof (SH_hull mb) as (H1 & H2 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
split; [apply VISH3; unfold w64; rewrite unsigned_lit_small by exact Ra; rewrite SMA in Ha; clear - Ha H1 H2 MZ; zlia|].
set (g := mb + 8 * (a - SMv)).
assert (Hg : shadow_addr g = a).
{ subst g. rewrite SMA. unfold shadow_addr. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp.
replace (p * 4096) with (p * 512 * 8) by zlia. rewrite (Z.div_mul (p * 512) 8) by zlia.
replace (p * 512 * 8 + 8 * (a - (SHADOW_OFF + p * 512))) with ((p * 512 + (a - (SHADOW_OFF + p * 512))) * 8) by zlia.
rewrite Z.div_mul by zlia. zlia. }
rewrite <- Hg. unfold w64. rewrite MEQ.
- pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. assert (M8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
rewrite <- (FAR.unpoison_offU UP mem0 (shadow_addr g) ltac:(rewrite Hg; exact (mapsh_offU GAP a Ha))).
apply (YFia.grant_shadow_zero B ly S rd0 mdN (w64 mb) MSv MA LN MSB Z9 GOK mem0u g (proj2 (proj2 (proj2 (proj2 (proj2 HAR)))))).
+ subst g. apply Z.mod_divide; [zlia|]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. exists (p * 512 + (a - SMv)). zlia.
+ rewrite Umb. subst g. clear - Ha MZ. zlia.
+ rewrite Umb. subst g. clear - Ha DM8 M8 MZ. zlia.
- rewrite unsigned_lit_small by (rewrite Hg; exact Ra). rewrite Hg. intros Hw. unfold WINP, WINT, WINI in Hw. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _).
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - Hw Ha SM1 SM2 F1 S1' T7 HBS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold sp0 in *. try unfold T in *. zlia.
Qed.
Lemma VISM : forall a, mb <= a < mb + MSv -> w_H W3 (w64 a) = false.
Proof. intros a Ha. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. apply VISM3. unfold w64. rewrite unsigned_lit_small; [exact Ha | clear - Ha M1 M2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia]. Qed.
Lemma WZ3 : forall z mat', ALedger tfibsegs lyF (SFS false z) md2 -> wz_facts false z W3 (with_vm_backing (m_vm_lazy md2) mat' md2).
Proof.
intros z mat' L2. pose proof (SH_hull mb) as (H1 & H2 & H3 & _). constructor.
- exact MON3.
- exact VISM3.
- exact VISH3.
- intros E; discriminate E.
- rewrite A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A3. cbn. right; right. exact Hi.
- rewrite A3. cbn. right; left. reflexivity.
- rewrite A3. cbn. left. reflexivity.
- exact (ALedger_same tfibsegs lyF (SFS false z) md2 _ L2 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- exact (amwf_same md2 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2).
- exact GAP.
Qed.
Lemma LED0 : forall z, ALedger tfibsegs lyF (SFS false z) md2.
Proof.
intros z. pose proof (SF_parts false z) as (Rreg & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & Rsecs & Rnev & Rregs).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (UMS : bv_unsigned (w64 MSv) = MSv) by (unfold w64; apply unsigned_lit_small; clear - Z8; unfold MALLOC_MAX in Z8; zlia).
unfold md2. apply (YG0j.ALedger_anon tfibsegs (as_universe B) 0 0 0 ly S (SFS false z) mdN (w64 mb) (w64 MSv) (rS S) mb LY WF (am_placed _ _ _ _ MA) MWN LN).
- rewrite UMS. exact GOK.
- exact Hev.
- rewrite UMS. exact MSB.
- rewrite UMS. exact Z9.
- intros c Hc. exact (Rreg c).
- unfold prim_committed. rewrite Rregs. reflexivity.
- rewrite Umb, UMS. exact (SEF false z).
- exact Rnev.
- rewrite Rres, <- Hres_def. reflexivity.
Qed.
Lemma COV_Q : forall mdV, amwf mdV -> idx = res ->
forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0g.covered (vm_noaccess (m_vmmaps (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) ++ m_vm_lazy (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) x
= YK0g.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x.
Proof.
intros mdV [(W1 & W2 & W3' & _ & W5) _] Heq x Hx.     pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
assert (UQa : bv_unsigned (w64 QSv) = QSv) by (unfold w64; apply unsigned_lit_small; clear - F9 Q5 F10; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
assert (UQb : bv_unsigned (w64 131072) = 131072) by (unfold w64; apply unsigned_lit_small; zlia).
apply (YG0j.cov_grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV x).
- unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact W5]]]; intros q Hq; [exact (W1 q Hq) | exact (W2 q Hq) | exact (W3' q Hq)].
- rewrite UQa, UQb. clear - F9 Q5 F10. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *. try unfold Qb in *. zlia.
- rewrite UQa, UQb. intros Hin. apply Hx. clear - Hin F9 Q5. unfold kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma grant50_isp : forall (a k : word) md, vm_init_sp (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = vm_init_sp (m_vmmaps md).
Proof.
clear. intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite YFjt.nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn; reflexivity.
Qed.
Lemma LED1 : forall z mdV md5, idx = res -> ALedger tfibsegs lyF (SFS false z) mdV ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps mdV) -> vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps mdV) ->
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps mdV) -> vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps mdV) ->
vm_init_sp (m_vmmaps md5) = vm_init_sp (m_vmmaps mdV) ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0g.covered (vm_noaccess (m_vmmaps md5) ++ m_vm_lazy md5) x = YK0g.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x) ->
eager_used md5 <= eager_used mdV + 131072 ->
(forall lo n, region_free (vm_noaccess (m_vmmaps mdV)) lo n = true -> region_free (vm_noaccess (m_vmmaps md5)) lo n = true) ->
ALedger tfibsegs lyF (SFS true z) md5.
Proof.
intros z mdV md5 Heq LV VM RES LIM MMB ISP COV EG NAF.
pose proof (SF_parts false z) as (Rreg0 & _ & _ & _ & _ & _ & _ & _ & _ & Rres0 & _ & _ & _ & Rnev0 & Rregs0).
pose proof (SF_parts true z) as (Rreg1 & _ & _ & _ & _ & _ & _ & _ & _ & Rres1 & _ & _ & _ & Rnev1 & Rregs1).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
apply (YG0j.ALedger_qcommit' tfibsegs lyF (SFS false z) (SFS true z) mdV md5).
- exact lyF_ok.
- rewrite (SEF false z). apply Forall_app. split; [exact (YG08.sec_extents_sizes64P _ 0 0 0 ly S WF)|]. constructor; [|constructor]. cbn [snd]. clear - Z8 Z9. unfold MALLOC_MAX in Z8. zlia.
- exact (placed_finalG false z HAR GAP).
- exact LV.
- exact VM.
- exact RES.
- exact LIM.
- exact MMB.
- exact ISP.
- intros x Hx. apply COV. exact Hx.
- clear - EG. unfold kPtrArrayEntriesPerCommit. zlia.
- intros c Hc. rewrite (Rreg1 c), (Rreg0 c). reflexivity.
- rewrite (SEF true z), (SEF false z). reflexivity.
- unfold prim_committed. rewrite Rregs1, Rregs0. reflexivity.
- rewrite Rnev1, Rnev0. reflexivity.
- rewrite Rres1, Rres0. reflexivity.
- exact NAF.
Qed.
Definition KDEP (s : astate) (beg : sptr) (z : Z) : itree astate (sptr * astate) :=
((if z =? 0 then YG00.ret tt
else (s' <- YG00.get ;;
mcheck (depot_ids s' + 1 <? kDepotIdsPerBlock) 14 ;;
mcheck (kStartFramesMax + depot_frames s' + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock) 13 ;;
YG00.put (set_depot (st_depot s' ++ [tr]) s'))) ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;; if aGranted z then YG00.ret tt else spin 12 else YG00.ret tt) ;;
YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;;
YG00.ret (ck_user k))) s.
Lemma malloc_K_some : forall beg s (Wx : world tfibsegs) c Q,
amreal tfibsegs (malloc_K n tr (Some beg) s) Wx c Q = SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot tr) z /\ amreal tfibsegs (KDEP s beg z) W1 c1 Q).
Proof. clearP. intros. reflexivity. Qed.
Lemma NR : N8D / 8 < 18446744073709551615 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = false.
Proof.
intros Hsmall. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_gt.
clear - Hsmall Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hsmall by zlia. zlia.
Qed.
Lemma NRb : 18446744073709551615 <= N8D / 8 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = true.
Proof.
intros Hbig. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_le.
clear - Hbig Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hbig by zlia. zlia.
Qed.
Lemma KS_user : ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) = PSec (length (st_secs S1)) 6144 /\
8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8) = N8D.
Proof.
pose proof sizes_model as (_ & _ & RS & RZ & _). unfold ck_user, ck_rz, ck_n, N8D, padd. cbn [YG00.ck_req YG00.ck_beg]. rewrite RS, RZ.
split; [reflexivity | clear; zlia].
Qed.
Lemma TAILg : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs ((YG00.ret tt ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAFU.
Proof.
intros Hsmall grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal].
assert (LEAF : forall W' c', fin_post Wz mdz grow z W' c' ->
QLEAFU (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & mat' & memD' & -> & HF) MP.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = SFS grow z).
{ pose proof (YFib.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)
(YFib.KS_fresh S (as_universe B) 0 0 0 WF)) as UF.
clear HR. destruct s4; cbn in *. subst. unfold SFS, YFib.sfinal, YFib.depF, YFib.resF, YFib.KS, YFib.rS. cbn. cbn in UF. rewrite UF.
rewrite MS, ND. unfold depot_after. destruct grow; destruct (z =? 0); reflexivity. }
rewrite EQS in MP |- *. change (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) with (ck_user KSc).
exact (LEAF_SU grow z Wz mdz Hgrow LEz IOz HWZ HOUT regs' mem' memD' mat' MP HF). }
assert (HDPOST : forall zz m, DPOST zz m -> aok S (KDepot tr) zz /\ depot_mem_ok B ly (depot_after zz tr S) (aview tfibsegs (w_H Wz) m) /\ Forall (cell_holds B ly (aview tfibsegs (w_H Wz) m)) (as_const B ly)).
{ intros zz m Hd. exact (HDPz zz m Hd). }
step HR (segT2 Wz mdz RX RXs RXt Xd z HXW _ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segU1 Wz mdz RX RXs RXt Xd z HXW Hsmall _ _ HR). pose proof (proj1 HR) as EW. subst W0.
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- step HR (segUe Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (finE Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR)|].
intros W' c' _ HP. exact (LEAF W' c' HP).
- step HR (segUo Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (finO Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR)|].
intros W' c' _ HP. exact (LEAF W' c' HP).
Qed.
Lemma SRr_with_AI : forall (Wx : world tfibsegs) cx (Q : world tfibsegs -> config -> Prop),
SRr tfibsegs Wx cx Q -> SRr tfibsegs Wx cx (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. clear. intros Wx cx Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma amreal_askV : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (sptr * astate)) (Wx : world tfibsegs) (cx : config)
(Q : sptr * astate -> world tfibsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfibsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfibsegs (IAsk q sN Kc) Wx cx Q.
Proof. clear. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; exact H. Qed.
Lemma same_io_wvb : forall md mat', same_io md0 md -> same_io md0 (with_vm_backing (m_vm_lazy md) mat' md).
Proof. clear. intros md mat' (X1 & X2 & X3 & X4). unfold same_io in *. rewrite <- X1, <- X2, <- X3, <- X4. repeat split; reflexivity. Qed.
Lemma TAILgB : 18446744073709551615 <= N8D / 8 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin 12)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAFU.
Proof.
intros Hbig. exfalso. clear - Hbig Nrange. unfold YFjm.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(clear; lia) ltac:(clear - Nrange; lia)) as HH. clear Nrange. lia.
Qed.
Lemma after_depot : forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfibsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAFU.
Proof.
intros grow Wz mdz RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
-
pose proof (fun s4 => TAILg Hsm grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR) as TAIL.
rewrite (NR Hsm).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
-
pose proof (fun s4 => TAILgB Hbg grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR) as TAIL.
rewrite (NRb Hbg).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
Qed.
Lemma QSP3 : idx <> res -> QSP W3 (zfill (w64 mb) (w64 MSv) (ms_mem ms)).
Proof.
intros NE u Hu. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRA].
assert (Ru : TFIB_IMG_END <= u < 2 ^ 64) by (clear - Hu F9 F10 HI HRS MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
assert (P0 : apresent (w_H W) mem0 u).
{ apply (vis_presentU (AQ 0) (8 * st_sec_reserved S) u); [right; unfold aareas; apply in_app_iff; right; left; reflexivity | cbn [aeval]; rewrite <- Hres_def; unfold QSv in Hu; try unfold Qb in Hu; clear - Hu HI HRS NE MZ; zlia | off_by ltac:(exact Ru)
  | apply Q_offU; unfold QSv in Hu; try unfold Qb in Hu; clear - Hu HI HRS NE MZ; unfold kPtrArrayResv, kMaxNumChunks in *; zlia ]. }
destruct P0 as [Hh [b Hb']]. split; [exact (MON3 _ Hh)|]. exists b. rewrite zfill_out.
- rewrite MEQ; [exact Hb'|]. rewrite unsigned_lit_small by (clear - Ru MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ru; zlia). unfold WINP, WINT, WINI. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _). destruct Hsp as (S1' & _ & S3' & _).
pose proof stack_ivs as (_ & _ & _ & SI4). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in QT. cbn [fst snd] in QT.
clear - Hu F1 F9 F10 HI HRS HBS S1' S3' SI4 QT MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK, t_unwinding, kThreadObjSize, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite Umb. unfold w64. rewrite !unsigned_lit_small by (clear - Ru M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in *; zlia).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ. clear - Hu MQ HI HRS F9 F10 MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Proof. apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto. Qed.
Theorem grantS_neU : idx <> res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAFU.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA].
pose proof (grant_cont mb0 W3 md2 (QSPX W3 (fun _ => True)) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ (conj (QSP3 NE) I)) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with false by (symmetry; apply Z.eqb_neq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact NE).
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
pose proof (rstable_and (QSP W3) (fun _ => True) (QSP_rstable W3) rstable_true) as RST.
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
assert (RXt : pstable WIN1T (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (RXd : pstable DX (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (HXW : forall a, WIN a -> WIN a) by (clear; intros a H; exact H).
assert (HXQ : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
pose proof (D1W_okU W3 MON3 Htr HmapD (fun z m H => proj2 (HDP z m) H) D1) as D1w.
step HR (segG1 W3 md2 _ RST ccont HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segNE W3 md2 (fun _ => True) RXs NE _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W3 md2 (fun _ => True) D1w RXd WIN HXQ HXW _ HR) | clear HR; intros W4 c4 _ [z HR]].
pose proof (proj1 HR) as EW. subst W4.
pose proof HR as HRc. destruct HRc as (_ & ms4 & mat4 & E4 & Ec4 & HE4 & HS4 & MEQ4 & PRS4 & [HPS4 [HPD4 _]]).
destruct HPD4 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP z memD) DP) as (AOKz & DEPz & CSTz).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : false = true <-> idx = res) by (split; [intros E; discriminate E | intros E; exfalso; exact (NE E)]).
assert (HXsub : forall a, (WIN a \/ DX a) -> WIN a \/ (false = true /\ QR a) \/ DX a) by (clear; intros a [Ha|Ha]; tauto).
assert (HRXQ : false = true -> forall m : word -> option byte, True -> ZQ W3 m) by (intros E; discriminate E).
assert (HXW' : forall a, WIN a -> WIN a \/ DX a) by (clear; intros a H; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (false = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W3 x = w_H W x)
by (intros x N1 N2 _; exact (OUT3 x N1 N2)).
assert (HDP3 : forall zz m, DPOST zz m -> DPOSTS W3 zz m) by (intros zz m Hd; exact (proj1 (HDP zz m) Hd)).
apply (after_depot false W3 md2 (fun _ => True) (fun a => WIN a \/ DX a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub LE3 IO2 (fun mat' => WZ3 z mat' (LED0 z)) HOUT HDP3
ltac:(rewrite A3; left; reflexivity) HR);
unfold S1; cbn; reflexivity.
Qed.
Lemma DPOSTS_Q : forall (W5 : world tfibsegs), idx = res -> hsub (w_H W5) (w_H W3) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) ->
forall z m, DPOSTS W3 z m <-> DPOSTS W5 z m.
Proof.
intros W5 Heq SUB5 OUT5 z m. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (X35 : rd_ext (aview tfibsegs (w_H W3) m) (aview tfibsegs (w_H W5) m)) by (apply aview_ext; [apply w_Hoff | exact SUB5]).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ QR a -> aview tfibsegs (w_H W3) m a = aview tfibsegs (w_H W5) m a).
{ intros a Ha Hq. unfold aview, mrestrict, YP09.mbyte. cbn beta. rewrite (OUT5 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros H'. apply Hq. apply EQR. exact H'. }
assert (AGC : forall c, In c (as_const B ly) -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
aview tfibsegs (w_H W3) m (aeval B ly (c_at c) + k) = aview tfibsegs (w_H W5) m (aeval B ly (c_at c) + k)).
{ intros c Hc k Hk. pose proof (const_cells_CZ c k Hc Hk) as CK. destruct (padb c).
- apply AG; [| intros Hq; apply EQR in Hq]; unfold MPAD in CK; clear - CK F9 Hq || clear - CK F9;
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, o_sec_mutex, kHighMemBeg in *; try unfold Qb in *; zlia.
- pose proof (CZ_untouched HmapD _ CK) as (Ra & _ & NQ & _). exact (AG _ Ra NQ). }
assert (AGD : forall a, DZONE a -> aview tfibsegs (w_H W3) m a = aview tfibsegs (w_H W5) m a).
{ intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia).
apply (AG _ Ra). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB. unfold QR. clear - Ha QNB QSB F9 HRS HI.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia. }
assert (IDS : depot_ids (depot_after z tr S) <= 20482).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S _ (conj ND INC)) as IB. unfold depot_after. destruct (z =? 0); [clear - IB; zlia|].
unfold depot_ids in *. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. clear - IB. zlia. }
split; intros (P1 & P2 & P3); (split; [exact P1|]).
- split; [exact (depot_mem_ok_ext _ _ _ X35 P2) | exact (Forall_cell_holds_ext B ly _ _ _ X35 P3)].
- split.
+ apply (depot_mem_ok_agree (depot_after z tr S) (aview tfibsegs (w_H W5) m)); [exact IDS | exact AGD | exact P2].
+ apply Forall_forall. intros c Hc. apply (cell_holds_agree (aview tfibsegs (w_H W5) m)); [exact (AGC c Hc) | exact (proj1 (Forall_forall _ _) P3 c Hc)].
Qed.
Theorem grantS_eqU : idx = res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAFU.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (grant_cont mb0 W3 md2 (fun _ => True) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ I) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with true by (symmetry; apply Z.eqb_eq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact EQ).
rewrite !bind_assoc_eq. unfold YG00.bind at 1. unfold askz. cbn [ibind].
replace (8 * Z.of_nat (length (st_sec_arr S1))) with (8 * idx) by (unfold S1; cbn; rewrite <- Hidx_def; reflexivity).
lazymatch goal with |- amreal _ (IAsk _ ?s ?Kc) _ _ _ => set (KV := Kc); set (sV := s) end.
apply amreal_askV; [exact I|].
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
step HR (segG1 W3 md2 _ RXs ccont HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (segEQa W3 md2 (fun _ => True) RXs EQ _ HR))|].
clear HR. intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W4.
pose proof HN as HNc. destruct HNc as (_ & msV & matV & EV & EcV & _).
set (mdV := with_vm_backing (m_vm_lazy md2) matV md2) in *.
assert (EcM : cfg_model c4 = mdV) by (rewrite EcV; reflexivity).
assert (LV : forall z, ALedger tfibsegs lyF (SFS false z) mdV) by (intros z; exact (ALedger_same tfibsegs lyF (SFS false z) md2 mdV (LED0 z) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWV : amwf mdV) by (exact (amwf_same md2 mdV (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2)).
pose proof VM2 as (VMa & VMr & VMl & VMb).
apply (nodeV W3 md2 sV KV QLEAFU (fun _ => True) c4 EQ HN HAI).
- clear; intros m m' _ _; exact I.
- rewrite EcM. exact MWV.
- rewrite EcM. exact (al_reserved _ _ _ _ (LV 0)).
- exact (al_img_env tfibsegs lyF (SFS false 0) _ lyF_ok (LV 0)).
- rewrite EcM. exact (al_Q _ _ _ _ (LV 0)).
-
rewrite EcM. apply (slackS mdV W3 (MSv + (MSv / 8 + 8192)) HAR Hev (proj1 (proj2 HAR))).
+ unfold mdV. rewrite m_vmmaps_wvb, VMl. unfold mdN. rewrite m_vmmaps_wvb. reflexivity.
+ unfold mdV. rewrite eager_used_wvb. unfold mdN in EG2. rewrite eager_used_wvb in EG2. clear - EG2 Z8. zlia.
+ rewrite A3. cbn [A_bytes fst snd]. clear - H3 Z8. zlia.
+ clear - Z8 Z9. unfold MALLOC_MAX in Z8. split; [zlia|]. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; zlia). zlia.
+
clear - Z8 Z9. unfold MALLOC_MAX in Z8. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; zlia). zlia.
-   rewrite EcM. exact (al_top _ _ _ _ (LV 0)).
- intros z Hz. exact Hz.
-
intros W5 c5. rewrite EcM. intros md5 LE5 SUB5 MON5 A5 VIS5 OUT5 AI5 MW5 IO5 EG5 VM5 HR5.
subst KV sV. cbv beta. change (aGranted 1) with true. cbn iota.
rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
assert (RS5 : rstable (RZ W5 (fun _ => True))) by (exact (rstable_and _ _ RXs (ZQ_rstable W5))).
assert (RT5 : pstable WIN1T (RZ W5 (fun _ => True))) by (apply pstable_and; [clear; intros m m' _ _; exact I | exact (ZQ_stableT W5)]).
assert (RD5 : pstable DX (RZ W5 (fun _ => True))) by (apply pstable_and; [clear; intros m m' _ _; exact I | exact (ZQ_stableD W5)]).
assert (HXW5 : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
assert (HXQ5 : forall a, (WIN a \/ QR a) -> WIN a \/ QR a) by (clear; intros a H; exact H).
assert (MON35 : forall x : word, w_H W x = false -> w_H W5 x = false) by (intros x Hx; exact (MON5 x (MON3 x Hx))).
assert (OUT5' : forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) by exact OUT5.
pose proof (DPOSTS_Q W5 EQ SUB5 OUT5') as DQ.
assert (HDP5 : forall z m, DPOST z m <-> DPOSTS W5 z m) by (intros z m; rewrite (HDP z m); exact (DQ z m)).
pose proof (D1W_okU W5 MON35 Htr HmapD (fun z m H => proj2 (HDP5 z m) H) D1) as D1w.
assert (LE35 : wle W W5) by (exact (wle_trans _ _ _ _ LE3 LE5)).
pose proof HR5 as HR. clear HR5.
step HR (segV W5 md5 (fun _ => True) RXs EQ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W5 md5 (RZ W5 (fun _ => True)) D1w RD5 (fun a => WIN a \/ QR a) HXQ5 HXW5 _ HR) | clear HR; intros W6 c6 _ [z HR]].
pose proof (proj1 HR) as EW. subst W6.
pose proof HR as HRc. destruct HRc as (_ & ms6 & mat6 & E6 & Ec6 & HE6 & HS6 & MEQ6 & PRS6 & [HPS6 [HPD6 _]]).
destruct HPD6 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP5 z memD) DP) as (AOKz & DEPz & CSTz).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : true = true <-> idx = res) by (split; [intros _; exact EQ | intros _; reflexivity]).
assert (HXsub : forall a, ((WIN a \/ QR a) \/ DX a) -> WIN a \/ (true = true /\ QR a) \/ DX a) by (clear; intros a [[Ha|Ha]|Ha]; tauto).
assert (HRXQ : true = true -> forall m : word -> option byte, RZ W5 (fun _ => True) m -> ZQ W5 m) by (intros _ m [_ Hm]; exact Hm).
assert (HXW' : forall a, WIN a -> (WIN a \/ QR a) \/ DX a) by (clear; intros a H; left; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (true = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W x).
{ intros x N1 N2 N3. rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). exact (OUT3 x N1 N2). }
assert (HDPz : forall zz m, DPOST zz m -> DPOSTS W5 zz m) by (intros zz m Hd; exact (proj1 (HDP5 zz m) Hd)).
assert (WZ5 : forall mat', wz_facts true z W5 (with_vm_backing (m_vm_lazy md5) mat' md5)).
{ intros mat'. constructor.
- exact MON35.
- intros x Hx. exact (MON5 x (VISM3 x Hx)).
- intros x Hx. exact (MON5 x (VISH3 x Hx)).
- intros _ x Hx. apply VIS5. apply EQR. exact Hx.
- rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A5, A3. cbn. right; right; right. exact Hi.
- rewrite A5, A3. cbn. right; right; left. reflexivity.
- rewrite A5, A3. cbn. right; left. reflexivity.
- apply (ALedger_same tfibsegs lyF (SFS true z) md5 _ (LED1 z mdV md5 EQ (LV z) (proj1 VM5) (proj1 (proj2 VM5)) (proj1 (proj2 (proj2 VM5))) (proj2 (proj2 (proj2 VM5))) (grant50_isp _ _ _) (COV_Q mdV MWV EQ) EG5 (YG0g.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV))
(m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- exact (amwf_same md5 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW5).
- exact GAP. }
apply (after_depot true W5 md5 (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub LE35 IO5 WZ5 HOUT HDPz
ltac:(rewrite A5, A3; right; left; reflexivity) HR);
unfold S1; cbn; try reflexivity.
- rewrite EcM. exact (same_io_wvb md2 matV IO2).
Qed.
End h.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* malloc_secU: lib/B/YFio.v:178 malloc_sec, from FSupoisonU.acall_preU, with the twins above. The junk words come    *)
(* from AR of the unpoisoned memory at bytes off UP (junk_atU); the presence and the frame-pointer chain from the      *)
(* kit (stack_present_real, chain_pre_real).                                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section tp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly PC_MALLOC_RA0 regs0 ch.
Hypothesis PRE : FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Htr : tr_admit (as_universe B) S tr.
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let idx : Z := Z.of_nat (length (st_sec_arr S)).
Let res : Z := st_sec_reserved S.
Let mat0 : list word := m_vm_materialized md0.
Local Abbreviation mem0u := (FSP.unpoison UP mem0).
Lemma HARU0 : FSP.ARU tfibsegs B ly S UP W mem0 md0. Proof. exact (FAR.ARU_of_acall_preU B ly S UP W regs0 mem0 md0 ch PRE). Qed.
Lemma PRE0 : acall_pre tfibsegs B ly S W regs0 mem0u md0 ch. Proof. exact (proj1 PRE). Qed.
Lemma HAR0 : AR tfibsegs B ly S W mem0u md0. Proof. exact (proj1 PRE0). Qed.
Lemma HARm0 : ARm B ly S (aview tfibsegs (w_H W) mem0u). Proof. exact (proj1 HAR0). Qed.
Lemma Hev : aregime S. Proof. exact (proj1 (proj2 PRE0)). Qed.
Lemma LY : layout_ok ly. Proof. exact (am_layout _ _ _ _ HARm0). Qed.
Lemma IMG : img_cover ly. Proof. exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0))). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0). exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _). rewrite (ts_tp B TS) in Htp'. exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE0 as (_ & _ & H & _). exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE0 as (_ & _ & _ & Hal & Hlo & Hbot & Hhi & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof.
pose proof Hsp as (H1 & _ & H3 & _). destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & H & _).
apply (FAR.stack_present_real B ly S UP W mem0 md0 (sp0 - ASTACK) sp0 HARU0); [unfold ASTACK in *; lia | lia | exact H].
Qed.
Lemma HQT : qmeter S. Proof. destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [H _] & _). exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof.
pose proof Hsp as (H1 & _). destruct PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C & _).
assert (L : ly_stk_lo ly <= spZ regs0) by (unfold spZ; unfold sp0 in H1; unfold ASTACK in H1; lia).
pose proof (FAR.chain_pre_real B ly S UP W regs0 mem0 md0 ch HARU0 L C) as [_ H]. unfold frame0_ok, spZ, s0Z in H. exact H.
Qed.
Lemma WF0 : Wf (as_universe B) S. Proof. exact (am_wf _ _ _ _ HARm0). Qed.
Lemma Hidx : 0 <= idx < kMaxNumChunks.
Proof. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. unfold idx, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia. Qed.
Lemma Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Proof.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ WF0)) as [_ RA].
unfold idx, res, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. split; [lia | exact RA].
Qed.
Lemma Hidx_def : idx = Z.of_nat (length (st_sec_arr S)). Proof. reflexivity. Qed.
Lemma Hres_def : res = st_sec_reserved S. Proof. reflexivity. Qed.
Lemma FP : from_primary n = false.
Proof. pose proof (YFjy.sizes_model ly regs0 n res Nrange S) as (_ & _ & _ & _ & FP' & _). exact FP'. Qed.
Lemma junk_atU : forall e len a, In (e, len) (ajunk B ly S) -> aeval B ly e <= a -> a + 8 <= aeval B ly e + len ->
(forall k, (k < 8)%nat -> FAR.offU UP (a + Z.of_nat k)) ->
exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w.
Proof.
intros e len a Hin H1 H2 OFF. apply YFio.word_of_bytes. intros k Hk.
destruct (range_vis_mbyte B ly (w_H W) mem0u e len (a + Z.of_nat k - aeval B ly e)
(proj1 (Forall_forall _ _) (am_junk B ly S _ HARm0) _ Hin) ltac:(lia)) as [b Hb].
exists b. replace (aeval B ly e + (a + Z.of_nat k - aeval B ly e)) with (a + Z.of_nat k) in Hb by lia.
rewrite (FAR.mbyte_unpoison (w_H W) UP mem0 _ (OFF k Hk)) in Hb. exact Hb.
Qed.
Lemma TOFF : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a.
Proof.
intros a Ha. pose proof (@YFjm.high_facts _ ly regs0 idx res LY IMG Hidx Hres) as (F1 & _).
exact (zone3_offU B ly S UP W mem0 md0 HARU0 _ _ a F1 Ha).
Qed.
Lemma IOFF : forall a, 0 <= a < TFIB_IMG_END -> FAR.offU UP a.
Proof. exact (img_offU B ly S UP W mem0 md0 HARU0). Qed.
Lemma JUNKU : exists j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3,
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) CSTAT16 8 j6 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) CSTAT24 8 j7 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (YFjm.BSLv n) 8 j8 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Proof.
pose proof (@YFjm.BSLv_range ly regs0 n idx res 0 Nrange Hidx) as HB. pose proof (ts_inst B TS) as EI.
assert (TJ1 : forall a, T + t_cache_stats <= a -> a + 8 <= T + t_stats -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_atU (AT t_cache_stats) (t_stats - t_cache_stats) a); [| cbn [aeval]; unfold T in *; lia | cbn [aeval]; unfold T in *; lia
  | intros k Hk; apply TOFF; unfold T, t_cache_stats, t_stats, kThreadObjSize in *; lia].
unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (TJ2 : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_atU (AT t_stats) (t_unwinding - t_stats) a); [| cbn [aeval]; unfold T in *; lia | cbn [aeval]; unfold T in *; lia
  | intros k Hk; apply TOFF; unfold T, t_stats, t_unwinding, kThreadObjSize in *; lia].
unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (SJ : forall a, TFIB_INST + o_sec_stats <= a -> a + 8 <= TFIB_INST + o_sec_mutex -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_atU (AInst o_sec_stats) (o_sec_mutex - o_sec_stats) a); [| cbn [aeval]; rewrite EI; lia | cbn [aeval]; rewrite EI; lia
  | intros k Hk; apply IOFF; unfold TFIB_INST, o_sec_stats, o_sec_mutex, TFIB_IMG_END in *; lia].
unfold ajunk. right; right. do 3 (apply in_or_app; right). apply in_or_app; left. unfold sec_junk. cbn. tauto. }
assert (CJ : forall a, TFIB_INST + o_comb_stats <= a -> a + 8 <= TFIB_INST + o_comb_stats + 40 -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_atU (ANum (TFIB_INST + o_comb_stats)) 40 a); [| cbn [aeval]; lia | cbn [aeval]; lia
  | intros k Hk; apply IOFF; unfold TFIB_INST, o_comb_stats, TFIB_IMG_END in *; lia].
unfold ajunk. right; right. do 7 (apply in_or_app; right). apply (ts_junk_comb B TS). }
destruct (TJ1 (T + 2784)) as [j0 Hj0]; [unfold t_cache_stats; lia | unfold t_stats; lia |].
destruct (TJ2 (T + 2800)) as [j1 Hj1]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2808)) as [j2 Hj2]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2816)) as [j3 Hj3]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2872)) as [j4 Hj4]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2880)) as [j5 Hj5]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2904)) as [j9 Hj9]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (CJ CSTAT16) as [j6 Hj6]; [unfold TFIB_INST, o_comb_stats; lia | unfold TFIB_INST, o_comb_stats; lia |].
destruct (CJ CSTAT24) as [j7 Hj7]; [unfold TFIB_INST, o_comb_stats; lia | unfold TFIB_INST, o_comb_stats; lia |].
destruct (SJ (YFjm.BSLv n)) as [j8 Hj8]; [unfold o_sec_stats; lia | unfold o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats)) as [i1 Hi1]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats + 16)) as [i2 Hi2]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats + 24)) as [i3 Hi3]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
exists j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, i1, i2, i3. repeat (split; [assumption|]). exact Hi3.
Qed.
Theorem malloc_secU_walk :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
destruct JUNKU as (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & i1 & i2 & i3 & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj9 & Hj6 & Hj7 & Hj8 & Hi1 & Hi2 & Hi3).
pose proof HAR0 as HAR. pose proof HARm0 as HARm. pose proof Hev as HEV. pose proof LY as HLY. pose proof Hsp as HSP. pose proof Hidx as HI. pose proof Hres as HR.
pose proof Htp as HTP. pose proof Hra as HRA. pose proof Hra4096 as HRA4. pose proof Hch as HCH. pose proof Hpres0 as HP0. pose proof HTSD as HTS. pose proof Hgp as HGP. pose proof HQT as HQ.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) WF0 HEV); [lia | exact Hlive | exact Htr]. }
change tr with (YFjm.tr ly regs0 ch). rewrite (YFk0.malloc_secondary_eq ly regs0 n ch S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; lia); reflexivity|].
lazymatch goal with |- amreal _ _ _ ?c ?Q => pose proof (YFk0.sec_ask_eq ly regs0 n ch S W c Q) as EQ end.
unfold YFk0.S1 in EQ. rewrite EQ. clear EQ.
apply (amreal_mono tfibsegs _ _ _ (@QLEAFU fx rc W ly regs0 mem0 md0 n B S UP)).
{ intros [p s'] W' c' H [ns MP]. apply H. cbn [fst snd]. cbn in MP. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQ))). }
cbn [amreal].
pose proof (@seg0U fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HTP HRA4 HSP HCH Nrange HI HR HP0 mat0 U1 (fun _ _ => True) B S TS HTS UP HARU0 Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) as PFX.
unfold cfg_at. replace md0 with (with_vm_backing (m_vm_lazy md0) mat0 md0) at 1 by (unfold mat0; apply with_vm_backing_id).
eapply SRr_bind; [exact PFX|]. clear PFX. intros W1 c1 _ HR1. pose proof (proj1 HR1) as EW. subst W1.
eapply SRr_mono; [exact (YFio.SRr_with_AI _ _ _ (@YFji.seg1 fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HSP Nrange HI HR _ _ HR1))|].
clear HR1 c1. intros W1 c1 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W1.
pose proof HN as HNc. destruct HNc as (_ & ms1 & mat1 & E1 & Ec1 & _).
assert (EcM : cfg_model c1 = with_vm_backing (m_vm_lazy md0) mat1 md0) by (rewrite Ec1; reflexivity).
apply (@nodeSU fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 Nrange B S UP HARU0 HQ _ S1 (YFk0.KSEC ly regs0 n ch S) (@QLEAFU fx rc W ly regs0 mem0 md0 n B S UP) c1 HEV HN HAI).
- intros z Hz. exact Hz.
-
intros c' HRf _ _ _. rewrite EcM in HRf.
exact (@refuseSU fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG HTP HRA HSP Nrange HI HR (fun _ _ => True) B S TS UP HARU0 Hidx_def Hres_def mat1 c' HEV HRf).
-
intros a W3 ms E'. cbv zeta. rewrite EcM.
intros GOK L1 MW1 LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 AI2 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB.
set (A := bv_unsigned a) in *.
assert (EA : a = w64 A) by (unfold w64, A; symmetry; apply Z_to_bv_bv_unsigned).
rewrite EA in GOK, AI2, MW2, IO2, EG2, VM2. rewrite EA.
pose proof (YFjm.size_facts n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
assert (MSB : 0 < YFjm.MSv n <= MALLOC_MAX + 4 * 4096) by (clear - Z1 Z8; unfold MALLOC_MAX in *; lia).
pose proof (YFia.grant_parts _ (w64 A) _ GOK) as (GP1 & GP2 & GP3 & _).
pose proof (YFia.grant_zone B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GH.
pose proof (YFia.grant_apart B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GA.
assert (UA : bv_unsigned (w64 A) = A) by (rewrite <- EA; reflexivity). rewrite UA in GP1, GP2, GP3, GH, GA.
assert (HmapA : A mod 4096 = 0 /\ YFjm.mzone A (YFjm.MSv n)) by (split; [exact GP1 | exact GH]).
assert (GAx : forall e, In e (static_extents ly ++ vis0_zones ly) -> zdisjoint (A, YFjm.MSv n) e).
{ intros e He. apply (proj1 (Forall_forall _ _) GA). rewrite app_assoc. apply in_app_iff. left. exact He. }
assert (HapartA : zdisjoint (A, YFjm.MSv n) (ly_T ly, kThreadObjSize) /\ zdisjoint (A, YFjm.MSv n) (ly_C ly, kCtxMapSize) /\
zdisjoint (A, YFjm.MSv n) (ly_prim ly, kPrimResvSize) /\ zdisjoint (A, YFjm.MSv n) (ly_Q ly, kPtrArrayResv) /\
zdisjoint (A, YFjm.MSv n) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (A, YFjm.MSv n) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (A, YFjm.MSv n) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
{ repeat split; apply GAx; unfold static_extents, owned_extents, vis0_zones; rewrite !in_app_iff; cbn [In]; tauto. }
destruct (Z.eq_dec idx res) as [EQ|NE].
+ exact (@grantS_eqU fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA (@YFju.DPOSTS ly regs0 ch B S W3) B S TS HTS UP HARU0 HGP Hidx_def Hres_def HQ W3 mat1 ms E' 0 HEV (tr_admit_len _ _ _ (ts_universe B TS) Htr) D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB EQ).
+ exact (@grantS_neU fx rc W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA (@YFju.DPOSTS ly regs0 ch B S W3) B S TS HTS UP HARU0 HGP Hidx_def Hres_def W3 mat1 ms E' 0 HEV (tr_admit_len _ _ _ (ts_universe B TS) Htr) D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 VM2 HE' HS MEQ PRS HB NE).
- rewrite EcM. apply YFio.same_io_wvb.
Qed.
End f.
Theorem malloc_secU : forall B, TfibSyms B -> tfib_unwind_spec -> tfib_depot_spec B ->
  forall ly S UP W regs0 mem0 md0 n ch, FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch ->
  YK11.getr regs0 10 = w64 n -> 64513 <= n < MALLOC_MAX -> tr_admit (as_universe B) S (call_trace ly PC_MALLOC_RA0 regs0 ch) ->
  blocks_bytes S + n <= LIVE_MAX ->
  amreal tfibsegs (malloc n (call_trace ly PC_MALLOC_RA0 regs0 ch) S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0)
    (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
intros B TS U1 D1 ly S UP W regs0 mem0 md0 n ch PRE Hn Nr Htr Hlive.
exact (malloc_secU_walk B TS U1 D1 ly S UP W regs0 mem0 md0 n ch PRE Hn Nr Htr Hlive).
Qed.
End tp.

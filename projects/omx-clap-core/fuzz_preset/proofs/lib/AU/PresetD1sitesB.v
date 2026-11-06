(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan-ubsan image), the free sites, the printf
   sites and the exit leaf / exit site of the driver of the closed ASan-side walk, restated over the second allocator
   instance ARcf (lib/Reusable/YG0ncf.v), which holds from the allocator's initial state on (the switch from cgif's
   AR is at init_state, a Theorem Labs lane with a Theorem Labs lane, 2026-10-28 22:44Z). Made from proofs/cgif/cgif_file_fuzzer/lib (here
   relocated as lib/Reusable):
     YD1v.v:149-157 drv_pre, YD1w.v:39-48 tail_at (FINV -> PINV too), YD1v.v:300-311 free_site_tfa,
     YD1w.v:104-112 free_null_site_tfa,
     YD1w.v:124-155 printf_pre / printf_post / printf_first_tfa / printf_next_tfa, YD1w.v:157-168 exit_leaf_tfa,
     YD1x.v:93-109 exit_site_tfa,
   and the statements of the results YD1i.v:61 tfib_free_site, YD1i.v:78 tfib_free_null_site and YD27.v:671
   tfib_exit_leaf. This file holds STATEMENTS only; the proofs are in PresetD1sitesBPf.v. Its twin for the asan image
   is lib/A/PresetD1sitesA.v (the same text over the lib/A twins of the donor files).
   Changes from the donor, the same in every item:
   (1) cgif's AR is ARcf at the ghost set Hp = []: no hidden head is outstanding between harness calls, as the
       program interface lib/AU/PresetCfnB.v states (preset_lib_pre_x `Hp = []`, preset_lib_post_x post Hp []);
       cgif's acall_post is acall_post_cf (lib/Reusable/YG0dcf.v);
   (2) cgif's event premise `st_nev S < EV_MAX` is dropped: the cf instance has no event cap (preset makes about
       3e7 allocator events per harness call) and takes its room from live state (YG08cf.v abudget_room_cf);
   (3) drv_pre_cf adds ROOM_cf (lib/Reusable/YGcfRoomPre.v), the three input-driven call premises of acall_pre_cf
       that ARcf does not give (the strict live-secondary count, ERRB_ROOM and batch_room_cf);
   (4) free is free_cf (YG00cf.v); cgif's free law (YG0d.v ml_free) is a8's ml_free_cf (YG03dcf.v:428) and cgif's
       AR_laws_ok is a8's AR_laws_ok_cf (YG0lawscf.v), both cited by the proofs, so neither is a premise here;
   (5) THE ROOM (owner ruling, 2026-10-29, after a Theorem Labs lane's P8): a driver state carries NO headroom number
       and NO P8 conjunct. `ROOM_cf_k S (4 * N_LLVMF + 3)` and every other headroom number of this layer are
       unsatisfiable (K_INIT 14,335 against >= 9,696 room charged per harness call;
       a Theorem Labs lane's note, the internal file n-llvmf.md). In their place a driver state carries NP S, the
       interface's non-primary room (see the Section below). P8 (preset_room / room_at) enters only at the loop
       entry, which is CwRunqm's, not this file's.
   (6) THE MEMNORM KEEP (interface a working branch 446222ec0601): printf_post_cf's continuation takes
       `YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem'`, so the loop keeps the overlay's
       normal form across the printf call between two harness calls. With it, tfib_printf_first_cf_B and
       tfib_printf_next_cf_B take their memcpy / memset premise in the keep form YGcallMxmn.aintrin_realizes_xm
       (see the results below), and the vfprintf walks are re-run in lib/AU/PresetD1sitesBmn.v.
   The image literals are the base's (YD1w.v, YD1x.v, YD1v.v), which a Theorem Labs lane's relocation of lib/Reusable moves.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YD2j YD2i YD1t YD20
YD1v YD2h YD2f YD1w YD1x YD1k YE22 YE23 YE35 YE3m YE2v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild YGcfDepotStep.
(* A18 (the driver's secondary-map base): the image-free count conjunct drv_secs_cf and its step lemmas are lane
   CountDrvA's lib/A/PresetDrvSecsA.v, shared by both images; PresetRoomPos.rp_base is the kit's (A16). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvSecsA CfParamsPreset.
(* the free row under the re-hide: SRr' / wle' at the zone RZ_cf (YA0nH), the primed call post acall_post_cf_rh
   (YGcfRehidePost), the primed free contract (YG0dcfR) and its keep form (YGcfMallocComposeKeep) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YG0dcfR YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* THE RUN LAYER'S ROOM (owner ruling 2026-10-29). A driver state carries NP S and nothing else about room:
   NP is the interface's non-primary room (the secondary count, the error buffer and the batch-class map),
   lib/AU/PresetCfnB.v's Section Variable `iface_room_np` (lane IfacePort, a working branch
   3f83c075b61f). Here it is a Section Variable of the same type, which the driver instantiates with the
   interface's.
   Two laws of NP are used by this file. They are the INTERFACE's definitions, cited, never restated and never
   proved here (a Theorem Labs lane gives them bodies at room_live_cf):
   - PCB.iface_room_np_tail NP (PresetCfnB.v:460): NP S -> ROOM_cf_k S 2, which hands a single call its a8
     premise ROOM_cf S (acall_pre_cf_intro, ml_free_cf);
   - PCB.iface_room_np_step NP (PresetCfnB.v:455-459): the malloc arm and the free arm, each under Wf_cf U S,
     qtight S and length (blocks S) <= 3; the free sites here use the free arm (proj2).
   a Theorem Labs lane's P8 (preset_room, room_at, PCB.iface_room_at_entry) is NOT in this file: it enters at the
   loop entry only, which is CwRunqm's. *)

Variable B : asyms.
Variable NP : astate -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.

(* ---------------------------------------------------------------------- *)
(* 1. The driver's call pre over ARcf. Donor: YD1v.v:149-157 (drv_pre). *)
Definition drv_pre_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S [] W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\
YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ ly_top ly - 4128 <= spZ regs <= ly_top ly + 32 /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
s0Z regs < alloc_ceiling /\
qtight S /\
(* the interface's non-primary room; a site takes its own ROOM_cf from it by iface_room_np_tail *)
NP S /\
(* the error buffer's extent placed (YG0ncf.v xs_placed_cf; every driver stage carries it, ruling of 2026-10-29) *)
xs_placed_cf ly S /\
(* cf layer field round 3's call boundary (YG0dcf.v acall_pre_cf: cf_hull_ok S, arodata_ok_cf): the hull admission at
   the preset instance (A18's bounds give it, PresetDrvHull.drv_cf_hull_ok_preset) and the reader form of the
   read-only bytes (YCeg.arodata_ok), which a driver state holds at any CfImg; the sites turn them into
   acall_pre_cf's forms at this Section's cp / ci by drv_hull_link / drv_aro_link below. Between them the overlay's
   normal form, which no call contract reads since part 3c: the driver carries it to the harness slot's pre
   (PresetCfnB.v header item (8)). *)
@cf_hull_ok CfParamsPreset.CfParams_preset S /\
YAkMemnorm.memnorm tfibsegs mem /\
arodata_ok B (aview tfibsegs (w_H W) mem).

(* The two links from drv_pre_cf's forms to acall_pre_cf's, premises of the site results (section 6): at
   cp := CfParams_preset the first is the identity, and at ci := CfImg_B the reader form gives arodata_ok_cf
   (CfAroPresetB.arodata_ok_cf_preset_AU). *)
Definition drv_hull_link : Prop := forall S, @cf_hull_ok CfParamsPreset.CfParams_preset S -> cf_hull_ok S.
Definition drv_aro_link : Prop :=
forall (W : world tfibsegs) (mem : word -> option byte), arodata_ok B (aview tfibsegs (w_H W) mem) ->
arodata_ok_cf tfibsegs B mem.

(* ---------------------------------------------------------------------- *)
(* 1b. The driver's tail state after the input is read. Donor: YD1w.v:39-48 (tail_at), with FINV -> PINV at the
       start-up ledger (cnt = ran = 0: no harness call has run yet; lib/AU/PresetCfnB.v PINV), ONE room conjunct
       NP S in place of the deleted headroom number (item (5) of the head: no ROOM_cf_k, no P8 conjunct), and
       no event bound: the donor's `st_nev S <= 64` is dropped, and its drv_minv (YD1v.v:158-161) keeps one
       prim_pristine_except S [kBatchClass] for both buffer sizes (RUNQM's payload malloc needs it) and drops
       quar_bytes (a Theorem Labs lane's rulings with CwRunqA / CwRunqm, 2026-10-28 / 29). *)
(* #102 (clause 4b of the kit's batch, the wild count): the last conjunct, every depot trace is a FIXED trace of
   the image's universe. The driver's own allocator calls carry fixed traces (malloc_site_tfa_cf / free_site_cf ask
   `In trc (as_universe B)`, the fixed list), so the depot holds no wild trace up to the first harness call, and the
   loop entry's wild room follows (drv_wild_room_entry below). *)
Definition drv_depot_fixed (S : astate) : Prop := forall t, In t (st_depot S) -> In t (u_fix (as_universe B)).
(* A18 (2026-10-30): the LAST conjunct, PresetDrvSecsA.drv_secs_cf S cap, bounds the secondary-map
   entries the driver has made before its first harness call by the buffer size: under YGcfSecsStep.secs_steps_cf,
   rp_nsec S <= log2 cap - 15 and sec_T_cf S <= 2 cap - 65536 + 8192 (log2 cap - 15). The B' basis (this image's walk):
   the one malloc(65536) from init_state at main + 0x50 (YD1t.v:48, ss_m1 a0 = 65536; return main + 0x54 =
   YImgCellsB.B_MAIN_PC_OFF_54), each grow a malloc(2 cap) at main + 0xa8 then a free of the old buffer at main + 0xcc
   (YD20.v:35 / :37, PresetPinvB23Pf.v gr_grow_cf; no realloc), cap = 2 ^ e from 2 ^ 16 to 2 ^ 26 (tail_at_pinv_B).
   drv_rp_base_B below reads PresetRoomPos.rp_base off it at the loop entry and after the payload malloc. *)
Definition drv_minv_cf (S : astate) (cap dl : Z) : Prop :=
(cap = 65536 \/ 2 ^ 17 <= cap <= 2 * dl) /\ prim_pristine_except S [kBatchClass] /\ frames S = [] /\ qtight S /\
drv_depot_fixed S /\ PresetDrvSecsA.drv_secs_cf S cap.
(* the depot facts at the start state and across one driver allocator call with a fixed trace (YGcfDepotStep.v) *)
Lemma drv_depot_fixed_init : drv_depot_fixed init_state.
Proof. intros t Ht. rewrite YCbqGwild.init_depot_nil in Ht. destruct Ht. Qed.
Lemma drv_depot_fixed_malloc : forall n trc S tr (q : sptr) S', drv_depot_fixed S -> In trc (u_fix (as_universe B)) ->
  apath (malloc_cf n trc S) tr (q, S') -> drv_depot_fixed S'.
Proof.
intros n trc S tr q S' HD Htr Hp t Ht. destruct (in_app_or _ _ _ (YGcfDepotStep.malloc_cf_depot_step n trc S tr q S' Hp t Ht)) as [H|[<-|[]]];
[exact (HD t H) | exact Htr].
Qed.
Lemma drv_depot_fixed_free : forall q trc S tr (u : unit) S', drv_depot_fixed S -> In trc (u_fix (as_universe B)) ->
  apath (free_cf q trc S) tr (u, S') -> drv_depot_fixed S'.
Proof.
intros q trc S tr u S' HD Htr Hp t Ht. destruct (in_app_or _ _ _ (YGcfDepotStep.free_cf_depot_step q trc S tr u S' Hp t Ht)) as [H|[<-|[]]];
[exact (HD t H) | exact Htr].
Qed.
(* THE LOOP ENTRY'S WILD ROOM (lib/Reusable/YCbqGwild.v section 2): a depot of fixed traces has an empty wild part, so
   any k <= u_wmax of room is free (YCbqGwild.wild_room_fixed) *)
Lemma drv_wild_room_entry : forall S k, drv_depot_fixed S -> (k <= u_wmax (as_universe B))%nat ->
  YCbqGwild.wild_room (as_universe B) [] k (st_depot S).
Proof. intros S k HD Hk. apply YCbqGwild.wild_room_fixed; [exact HD | cbn [length]; lia]. Qed.
(* A18's base at the driver's two users of PresetD2eB.iface_room_at_driver: the tail state itself (the empty-payload
   loop entry, PresetD2runQBPf.v) and the state after the payload malloc (PresetD2eBPf.v), a request of at most 2 ^ 26 *)
Lemma drv_rp_base_B : forall S cap dl, drv_minv_cf S cap dl -> 65536 <= cap <= 2 ^ 26 ->
  PresetRoomPos.rp_base S /\
  (forall n trc tr (q : sptr) S', 0 <= n <= 2 ^ 26 -> apath (malloc_cf n trc S) tr (q, S') -> PresetRoomPos.rp_base S').
Proof. intros S cap dl (_ & _ & _ & _ & _ & HS) Hc. exact (PresetDrvSecsA.drv_secs_rp_base S cap HS Hc). Qed.

Definition tail_at_pinv_B (ss : sstate) (E : YP0m.env) (sp : word) (inp : ProcInput) (a0 p data : list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (pb : sptr) (cap : Z) : Prop :=
st_ok tfibsegs E ss (restrict (w_H W) ms) /\
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb /\ bv_unsigned (ew E A_LEN) = dlen data /\
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) /\
AI tfibsegs (w_H W) (w_A W) md /\ ARcf tfibsegs B ly S [] W (ms_mem ms) md /\
NP S /\ top_ok (bv_unsigned sp) ly /\
blocks S = [(pb, cap)] /\ 65536 <= cap <= 2 ^ 26 /\ dlen data < cap /\
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data /\
m_fs md = in_fs inp /\ m_fds md = APSG.fds_std /\ drv_minv_cf S cap (dlen data) /\
PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 /\
xs_placed_cf ly S /\
(* memnorm of the full overlay (lane MnPrefix): the tail carries it from main to the loop head *)
YAkMemnorm.memnorm tfibsegs (ms_mem ms).

(* ---------------------------------------------------------------------- *)
(* 2. The free sites. Donor: YD1v.v:300-311 (free_site_tfa), YD1w.v:104-112 (free_null_site_tfa). The pre
      carries NP S (in drv_pre_cf) and the driver's live bound `length (blocks S) <= 3`; the site pays NO
      headroom. Its own one-call ROOM_cf S comes from iface_room_np_tail NP, and the post's NP S' from
      the free arm of iface_room_np_step NP, so no ROOM_cf_k number and no P8 term appears. The post keeps qtight S'
      and xs_placed_cf ly' S' (a8's YGcfXs.v). *)
(* THE RE-HIDE (the free contract's primed form, YG0dcfR.afree_realizes_cf_rh): a free may hide the shadow of
      the secondaries it recycles again, so the site's realization is SRr' over the zone RZ_cf (the continuation's
      world relation is wle' tfibsegs RZ_cf, not wle) and its call post is YGcfRehidePost.acall_post_cf_rh: the hidden
      set grows only inside dead_shadow_new ly S S', and the view frame excepts that set. *)
Definition free_site_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (n : Z),
drv_pre_cf ly S W regs mem md -> (length (blocks S) <= 3)%nat ->
In (p, n) (blocks S) -> getr regs 10%bv = w64 (sptr_addr B ly p) ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free_cf p trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S [] W regs mem md
(fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' S' W' regs' mem' md' /\
qtight S' /\ NP S' /\ xs_placed_cf ly' S' /\
(* the memnorm keep across the free: the keep row's leaf conjunct (YGcfMallocComposeKeep) *)
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem')).

Definition free_null_site_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
drv_pre_cf ly S W regs mem md -> (length (blocks S) <= 3)%nat -> getr regs 10%bv = w64 0 ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free_cf PNull trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S [] W regs mem md (fun _ => False) ly' S' W' regs' mem' md' /\
qtight S' /\ NP S' /\ xs_placed_cf ly' S').

(* The driver's call pre without its memnorm conjunct, and the two free sites over it (posts as above). The free calls
   whose memnorm is not carried as a fact (after the fwrite diagnostic of the short / overrun leaves and on the exit
   path after the last harness call) take these forms. *)
Definition drv_pre_nomn_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S [] W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\
YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ ly_top ly - 4128 <= spZ regs <= ly_top ly + 32 /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
s0Z regs < alloc_ceiling /\
qtight S /\ NP S /\ xs_placed_cf ly S /\
@cf_hull_ok CfParamsPreset.CfParams_preset S /\
arodata_ok B (aview tfibsegs (w_H W) mem).
Definition free_site_nomn_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (n : Z),
drv_pre_nomn_cf ly S W regs mem md -> (length (blocks S) <= 3)%nat ->
In (p, n) (blocks S) -> getr regs 10%bv = w64 (sptr_addr B ly p) ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free_cf p trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S [] W regs mem md
(fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' S' W' regs' mem' md' /\
qtight S' /\ NP S' /\ xs_placed_cf ly' S' /\
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem')).
Definition free_null_site_nomn_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
drv_pre_nomn_cf ly S W regs mem md -> (length (blocks S) <= 3)%nat -> getr regs 10%bv = w64 0 ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free_cf PNull trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S [] W regs mem md (fun _ => False) ly' S' W' regs' mem' md' /\
qtight S' /\ NP S' /\ xs_placed_cf ly' S').

(* ---------------------------------------------------------------------- *)
(* 3. The printf sites of the per-call loop. Donor: YD1w.v:124-155. printf_post_cf hands the continuation ARcf at
      the SAME layout ly and state S (the printf path makes no allocator call), so a caller keeps qtight S and
      ROOM_cf S across it. *)
Definition printf_pre_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S [] W mem md /\ raZ regs = RA_EMIT /\
spZ regs mod 16 = 0 /\ sp_window_lo - 288 <= spZ regs /\ ly_top ly - 4208 <= spZ regs <= ly_top ly - 128 /\
spZ regs + 288 <= sp_window_hi /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
arodata_ok B (aview tfibsegs (w_H W) mem) /\
(forall a, spZ regs - PF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
getr regs 10%bv = w64 A_FMT_D /\ getr regs 11%bv = w64 (spZ regs + 24) /\
rdword (aview tfibsegs (w_H W) mem) (spZ regs + 24) = Some 0.

Definition printf_post_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k' : nat) (T : TSet) : Prop :=
forall regs' mem' md',
ARcf tfibsegs B ly S [] W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10%bv = w64 2 ->
xst k' (w_H W) mem' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PF_STK <= a < spZ regs) -> ~ STDOUT_MUT a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
(* the MEMNORM KEEP (interface a working branch 446222ec0601, header item (6)): the loop needs the overlay's
   normal form again at the next harness call, and no call rule derives it from a post stated through views
   (YGcallMxmn.v's header), so the printf site hands it on. Lane MnLoop takes exactly this line. *)
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem') ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T.

Definition printf_first_cf : Prop :=
forall ly S (W : world tfibsegs) regs mem md T,
printf_pre_cf ly S W regs mem md -> stdout_img (w_H W) mem ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) ->
AI tfibsegs (w_H W) (w_A W) md ->
printf_post_cf ly S W regs mem md 1%nat T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_vprintf regs mem md) (wr ch_stdout line0 T).

Definition printf_next_cf : Prop :=
forall ly S (W : world tfibsegs) regs mem md T k,
printf_pre_cf ly S W regs mem md -> xst k (w_H W) mem -> (1 <= k <= 3)%nat ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) ->
AI tfibsegs (w_H W) (w_A W) md ->
printf_post_cf ly S W regs mem md (Datatypes.S k) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_vprintf regs mem md) T.

(* ---------------------------------------------------------------------- *)
(* 4. The exit leaf and the exit site. Donor: YD1w.v:157-168 (exit_leaf_tfa), YD1x.v:93-109 (exit_site_tfa). *)
Definition exit_leaf_cf : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs) (code : Z) (k : nat),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 ->
1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) -> spZ regs = usp - 48 ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_L ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_EXIT) mem (seg_rom tfibsegs)) md)
(wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).

Definition exit_site_cf : Prop :=
forall (XI : smem) (E : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp d : Z) (fs : Fs) (code : Z) (k : nat),
(XI = IMG_X /\ k = 0%nat) \/ XI = IMG_XL ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 ->
1 <= bv_unsigned (ew E 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) ->
spZ regs = usp - d -> (d = 48 \/ d = 128) -> YK0s.ret_ok (getr regs 1%bv) ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) XI ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
est (w_H W) mem ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
((1 <= k)%nat -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ->
m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_exit) mem (seg_rom tfibsegs)) md)
(wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).


End S.

(* ---------------------------------------------------------------------- *)
(* 6. The results (closed). Each is proved in PresetD1sitesBPf.v as <name>_holds. *)

(* YD1i.v:61 tfib_free_site, over ARcf. The two links (section 1) turn drv_pre_cf's hull and read-only conjuncts into
   acall_pre_cf's at this cp / ci. The free row is the primed contract in its keep form
   (YGcfMallocComposeKeep.afree_realizes_cf_rh_keep): the site's post carries the memnorm keep. *)
Definition free_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
PCB.iface_room_np_tail NP -> PCB.iface_room_np_step NP -> drv_hull_link -> drv_aro_link B ->
YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs B -> free_site_cf B NP.

(* YD1i.v:78 tfib_free_null_site, over ARcf; its post has no keep, so it takes the primed contract
   YG0dcfR.afree_realizes_cf_rh. *)
Definition free_null_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
PCB.iface_room_np_tail NP -> PCB.iface_room_np_step NP -> drv_hull_link -> drv_aro_link B ->
YG0dcfR.afree_realizes_cf_rh tfibsegs B -> free_null_site_cf B NP.

(* The same two sites over drv_pre_nomn_cf (section 2): the call contracts read no memnorm (field round 3 part 3c),
   so they hold from the same rows. *)
Definition free_site_nomn_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
PCB.iface_room_np_tail NP -> PCB.iface_room_np_step NP -> drv_hull_link -> drv_aro_link B ->
YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs B -> free_site_nomn_cf B NP.

Definition free_null_site_nomn_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
PCB.iface_room_np_tail NP -> PCB.iface_room_np_step NP -> drv_hull_link -> drv_aro_link B ->
YG0dcfR.afree_realizes_cf_rh tfibsegs B -> free_null_site_nomn_cf B NP.

(* YD27.v:671 tfib_exit_leaf, over ARcf: the exit site EXS (exit_site_cf) is a premise, as in the donor. *)
Definition exit_leaf_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
xst_frame_tfa xst -> est_img_tfa est -> est_frame_tfa est ->
exit_site_cf B est xst -> exit_leaf_cf B xst.

(* YD1o.v tfib_printf_first / tfib_printf_next and YD1j.v tfib_exit_site, over ARcf, at YD1k's xst / est.
   The vfprintf and exit walks they consume are CwPreB's B cf copies (a working branch 30644fdd1332:
   YE35cf.tfib_vprintf_icpt_A, YE3mcf.tfib_vfprintf_stdout_first / _next, YE23cf.tfib_exit_pristine / _pristine1 /
   _empty / _flush, and the exit returns YE36cf.x1_realizes / x3_realizes, YE37cf.x2_realizes), cited by the
   proofs; AR_laws_cf is a8's AR_laws_ok_cf.
   THE NAMED REALIZER PREMISE CHANGED WITH THE MEMNORM KEEP (2026-10-29): the two printf results take the memcpy /
   memset texts in a Theorem Labs lane's KEEP FORM, YGcallMxmn.aintrin_realizes_xm (lib/Reusable/YGcallMxmn.v, taken by path
   from a working branch 8e33ecc4965b, blob 87de220caca2), not a8's aintrin_realizes_cf. The keep form
   is aintrin_realizes_cf with ONE more post conjunct, `memnorm segs mem -> memnorm segs mem'`, which the row's
   owner pays from its own run; without it printf_post_cf's keep has no proof (YGcallMxmn.v's header: no call rule
   derives memnorm from a post stated through views). Both tops that name these premises must pass the keep form.
   The walks themselves are re-run with the keep in lib/AU/PresetD1sitesBmn.v. *)
Definition tfib_printf_first_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
TfibSyms B ->
YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)) ->
YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OSet (pc_wrap_memset (as_code B)) ->
printf_first_cf B xst.

Definition tfib_printf_next_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
TfibSyms B ->
YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)) ->
YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OSet (pc_wrap_memset (as_code B)) ->
printf_next_cf B xst.

Definition tfib_exit_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
TfibSyms B -> exit_site_cf B est xst.

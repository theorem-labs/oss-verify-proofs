(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L6A.v, with its module paths changed; 84 of its 345 lines of code are new or changed and 19 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4):
   SEGMENT L6x of LLVMFuzzerTestOneInput (entry 0x815e0), the EXIT LANE: listing slots 113 .. 177 (+0x1c4 .. the one
   `ret` at +0x2c4, no call), proved against lib/A/Ent102CutsA.v's `seg_L6x_stmt` (cut_exit E fk -> cut_ret E).
   The lane poisons the frame's shadow bytes 4 .. 10 with 0xf8, writes the free magic 0x45e0360e at [fk], skips the
   real-stack arm (`beqz s2` not taken: fk <> 0, the engine's range fact on fk), poisons all 16 shadow bytes with 0xf5,
   releases the fake frame INLINE (`ld a0,0x78(s2); sb zero,0(a0)`: the flag byte at flag_addr := 0), sets a0 = 0,
   restores sp = s0 - 0x80, reloads ra and s0 .. s11 from the saved block, pops the frame and returns to the entry ra.
   STATEMENT: lib/A/Ent102CutsA.v (blob 2fb50b636f51, the statements of record at a working branch
   83576a163e5b = CUT STABLE 2ab248e3b164: every segment over `forall E fk, ec_hyps (e_dw E) -> ..`, the decff
   ledger arity `exists most own, prh_ledger .. most own` in ec_inv and cut_ret, ec_at's frm_zero of the cut's float
   state fy; seg_L6x_stmt, cut_exit (its index pair e_os E ++ [trp], e_i0 E + |ec_call_evs E trp|), cut_ret, the
   RECORD ec_hyps read by name - ech_frame_area's astack_free_law_cf and ech_img's ei_pst / ei_sio / ei_sio_frame).
   ec_inv and ec_pre are read BY NAME, never by a positional destruct: lib/A/Prog/Ent102CallA.v's projections (blob
   aefcab75548d, of record: ec_inv_ledger / ec_inv_pre / ec_inv_pay / ec_inv_perm, ec_pre_payload) and, for the
   parts it does not project, this file's l6_inv_* / l6_pre_* (section 1), proved by its type-directed
   ec_conj_pick. The run's data words are the cut context's own e_dw E; this lane reads no DW-dependent part. The
   lane makes NO model event: cut_exit's position is carried to cut_ret's room conjunct at the same trp, the stack
   release keeping it (PresetRoomPosKeep.room_pos_stack_free); the ledger's most / own witnesses are cut_exit's,
   kept (the lane touches neither cell). RE-PROVED on this statement: the earlier Qeds at b82ef77aeac
   (a working branch 1dc8de9a0253), f40892fb5ddb (a working branch a2d6bb26a279) and
   92683b094505 (a working branch 307ac42af035) were against older cuts. The B' twin
   lib/AU/Prog/Ent102L6B.v (a working branch c07214c6429c, green on the same statements) was read
   for the new shapes, not imported.
   LISTING: a Theorem Labs lane's whole-program listing lib/A/Listing_prog.v (blob 7ed1529926bd, v3; slot k = byte offset 4k from
   the entry; the bodies are those of 1ab147923c5d), run with the PAListing PL_102_A of lib/A/Ent102PLA.v (blob
   a55fa7414ddf); the image half stays generic ({PA : PAImg A_prog_listing}; lib/A/PAImg_prog.v is not loaded, no
   vm_compute on pa_val / pa_sigma).
   The kit TEXTS (kit of record f97c8b2f046b): lib/A/PRH_Base.v fdb45545469b (prh_ledger with its most / own fields,
   prh_pst, PrhRoomLive's RL_stack_free; the ledger is moved by lib/A/Prog/S1Ledger.v (blob 8cf15eeb6311)'s
   prh_ledger_kept, no positional destruct), lib/A/PRH_FnPj.v 908f34f0beaa (pj_free is not called in this lane;
   named for the text set).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L6x (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + cold/* lemma index / `proof-index LLVMFuzzerTestOneInput` exit=0, output
   the lane's index output, the internal file idx-llvm-newpin.txt; checker R24CheckLLVMF CONFIRM; NEW walk on the #102 pins).
   FORM: cgif's per-function form over YC80x's runner and YCbqG's ajournal_x at ARx := ec_ARx (ARcf pa_segs B /\
   xs_placed_cf). The whole lane is ONE run of the flag-store rule (lib/A/Prog/Ent102L6AFlag.v aj_flag_store_x_inv =
   YGcallSx.v aj_flag_store_x with YC80x.v's run invariant, at P := YSRrMemnorm.v's memnorm instance), then the `ret` by
   YC1fP.v paj_ret_at. The symbolic state is lib/A/Prog/Ent102L6ADefs.v, the entry state lib/A/Prog/Ent102L6AEnt.v.
   PORTED FROM (by path, image-free shape): lib/B/Prog/EntS7B.v of a working branch c3e54cc5ad62 (image B,
   old pin; its open return, EntS7B.v:263-271, is closed here at this statement's cut_ret).
   NUMERALS: 128 / 120 / 16 / 8 are LENGTHs of this frame (EC_FRAME_BYTES, the flag-pointer slot, the shadow bytes, the
   word); 32768 is LLVMF_STK; 2 ^ 46 / 2 ^ 47 / 2 ^ 64 and kLowMemEnd are the engine's range facts. No ADDRESS.
   WILD BUDGET (the cut file's statements): ec_inv carries the cut's spent wild budget wk and its journal is
   `exists WS, ajournal_xw .. WS /\ YCbqGwild.wbudget [] wk WS`; cut_exit is at ec_wk_exit and cut_ret's journal is
   budgeted at ec_wk_exit too. This lane stores no wild trace (no allocator call), so the flag-store run is on the
   PLAIN journal from the entry with its depot moved to cut_exit's (Ent102CutsA.ec_journal_rebase) and cut_ret's
   journal is that run's at the SAME budget (Ent102CutsA.ec_journal_unbase); the section-1 projections take wk. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102L6ADefs Ent102L6AFlag Ent102L6AEnt.
(* Required, not Imported: ec_inv / ec_pre's projections and ec_conj_pick, used by their qualified names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102CallA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* aregs_preserved from the fifteen callee-saved registers, one by one *)
Lemma l6_aregs : forall regs0 regs' : bvmap 5 word,
  getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 8 -> getr regs' 9 = getr regs0 9 ->
  getr regs' 18 = getr regs0 18 -> getr regs' 19 = getr regs0 19 -> getr regs' 20 = getr regs0 20 ->
  getr regs' 21 = getr regs0 21 -> getr regs' 22 = getr regs0 22 -> getr regs' 23 = getr regs0 23 ->
  getr regs' 24 = getr regs0 24 -> getr regs' 25 = getr regs0 25 -> getr regs' 26 = getr regs0 26 ->
  getr regs' 27 = getr regs0 27 ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
Qed.

Section L6. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
(* the cut file's two budget functions (count and live bytes per cut index): this lane reads neither *)
Variables ec_ccut ec_lcut : @ecx rc A_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
#[local] Notation ECX := (@ecx rc A_prog_listing PA).
#[local] Notation ECPRE := (@ec_pre fx rc ci cp PI RL A_prog_listing PA B EC_RA EC_EMPTY EC_SIO).
(* segment L6x is after check_no_overread's frees (it starts at cut_exitR WLE', Ent102CutsA.v): its invariant and journal
   are at wle' over the fixed zone *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation ECINV := (@ec_invR fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO WLE').

(* ---------------------------------------------------------------------- *)
(* 1. ec_inv's and ec_pre's parts this lane reads that lib/A/Prog/Ent102CallA.v does not project, BY NAME: each is
      picked by its TYPE (Ent102CallA.ec_conj_pick), so no position inside ec_inv / ec_pre is read; E .. i_c are
      implicit, as in Ent102CallA's projections, so a new binder of ec_inv changes only these statements. *)
Lemma l6_inv_journal : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists WS, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l6_inv_own : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_own fk ly W mem own.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l6_inv_sio : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> EC_SIO (aview SEGS (w_H W) mem).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l6_inv_live : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> @room_live_cf RL S.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
(* THE EXACT ROOM POSITION at the cut's own index pair *)
Lemma l6_inv_room : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c i_c (e_H0 E) hist S.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
(* a chained `_ <= _ <= _` is two conjuncts to ec_conj_split *)
Lemma l6_inv_cnt : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> e_cnt E <= cnt <= e_cnt E + LCNT.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_split H.
split; assumption.
Qed.
Lemma l6_inv_memnorm : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> YAkMemnorm.memnorm SEGS mem.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l6_pre_frames : forall {E : ECX}, ECPRE E -> frames (e_S E) = [].
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
(* the entry ra's ret_ok, a conjunct of YCbqG's afn_pre_x (the first conjunct of ec_pre) *)
Lemma l6_pre_retok : forall {E : ECX}, ECPRE E -> YK0s.ret_ok (getr (e_regs E) 1).
Proof. intros E H. unfold ec_pre, afn_pre_x in H. Ent102CallA.ec_conj_pick H. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE SEGMENT. *)

Theorem seg_L6x_A :
  @seg_L6x_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L6x_stmt, ec_laneR.
(* the run's data words are the cut context's own e_dw E (ec_hyps (e_dw E)); this lane reads no DW-dependent part *)
intros E fk HYP W c Hcut.
(* the parts of ec_hyps this lane reads, by name: the frame-area release law and the image facts *)
pose proof (ech_frame_area _ _ _ _ _ _ _ _ _ _ HYP) as (_ & HSFL).
pose proof (ech_img _ _ _ _ _ _ _ _ _ _ HYP) as HIMG.
pose proof (ei_sio _ _ _ _ _ _ HIMG) as Hsio. pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as Hsioframe.
pose proof (ei_pst _ _ _ _ _ _ HIMG) as Hpst.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & peak & cnt & ran & k & trp & Hat & Hinv & HHp & HCB & HLB
  & Hrk & Hfrm).
destruct Hat as (fy & Hfrm0 & Hkept & Hc).
(* ec_inv and ec_pre BY NAME: Ent102CallA's projections, then section 1's *)
(* the journal at cut_exit's wild budget ec_wk_exit; the lane makes no allocator call, so it runs on the PLAIN journal
   with the entry depot moved to the cut's (ec_journal_rebase) and gives cut_ret's at the same budget
   (ec_journal_unbase) *)
destruct (l6_inv_journal Hinv) as (WT & HJW & HWB).
pose proof (ec_journal_rebaseR B SK WLE' E _ _ _ _ _ _ _ _ _ HJW) as HJ.
pose proof (l6_inv_own Hinv) as HOWN.
(* the ledger with its kit decff fields: the harness's g_most / own cells, kept unchanged by this lane *)
pose proof (Ent102CallA.ec_inv_ledgerR B SK EC_RA EC_EMPTY EC_SIO Hinv) as (lmost & lown & HLED).
pose proof (l6_inv_sio Hinv) as HSIO.
pose proof (l6_inv_live Hinv) as HLIVE.
pose proof (l6_inv_room Hinv) as HROOM.
pose proof (l6_inv_cnt Hinv) as HCNT.
pose proof (Ent102CallA.ec_inv_preR B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPRE.
pose proof (Ent102CallA.ec_inv_payR B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPAY.
pose proof (Ent102CallA.ec_inv_permR B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPERM.
pose proof (l6_inv_memnorm Hinv) as HMN.
pose proof (Ent102CallA.ec_pre_payload B EC_RA EC_EMPTY EC_SIO HPRE) as HNC.
pose proof (l6_pre_frames HPRE) as HfrE.
pose proof (l6_pre_retok HPRE) as Hraok.
clear Hinv HPRE.
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & Hflagw).
subst own Hp c.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres
  & Hstk & F5 & HQT).
destruct HAR as (HARcf & HXS).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)).
{ rewrite Hfrs. change (frames (YG00.set_depot (st_depot S) (e_S E))) with (frames (e_S E)).
  rewrite HfrE. left. reflexivity. }
assert (Rsp : YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47) by lia.
destruct (l6_geom B ly S [] W mem md pos fk HARcf Hin Hfkeq)
  as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh & Ggp & Ggo & Ggapp & Ggceil & Gimg & Gnf & Gns).
change (EC_FRAME_BYTES / 8) with 16 in Gsh, Gns.
unfold EC_FRAME_BYTES in Gceil, Gfr, Gapp, Gnf.
pose proof (l6_entry_ok (fx := fy) B E fk ly S [] W regs mem md pos HARcf Hin Hfkeq Hflagw Rsp Hal16 Hrk Hfrm) as HS.
set (fl := flag_addr ly LLVMF_FS_CLASS pos) in *.
(* the lane's environment *)
remember (L6_EI (e_regs E) fl regs) as EE eqn:HEE.
assert (HEI : img_env VAL A_LIM EE) by (rewrite HEE; unfold L6_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew EE n = ew (Ereg regs (l6_extra (e_regs E) fl)) n)
  by (intros n Hn; rewrite HEE; unfold L6_EI; apply Eimg_low; exact Hn).
clear HEE.
destruct Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
assert (E3 : ew EE 3 = getr (e_regs E) 3)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew EE 4 = getr (e_regs E) 4)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew EE 8 = Z_to_bv 64 (e_sp0 E))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E26 : ew EE 26 = Z_to_bv 64 (shadow_addr fk))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew EE 27 = Z_to_bv 64 fk)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew EE 32 = Z_to_bv 64 fl)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew EE 33 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 1)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew EE 34 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 8)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew EE 35 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 9)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew EE 36 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 18)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew EE 37 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 19)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew EE 38 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 20)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew EE 39 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 21)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew EE 40 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 22)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew EE 41 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 23)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew EE 42 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 24)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew EE 43 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 25)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew EE 44 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 26)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew EE 45 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 27)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
assert (Hq0 : 0 <= fk / 8) by (apply Z.div_pos; lia).
assert (Hq8 : 8 * (fk / 8) <= fk) by (apply Z.mul_div_le; lia).
assert (U26 : bv_unsigned (ew EE 26) = shadow_addr fk)
  by (rewrite E26; apply unsigned_lit_small; rewrite Esh; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew EE 27) = fk) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew EE 32) = fl)
  by (rewrite E32; apply unsigned_lit_small; destruct Ggapp as (Hg4096 & _); lia).
assert (SHOK : sh_ok SEGS L6_Bx L6_SH EE (mrestrict (w_H W) mem)) by constructor.
(* the run's write set holds no image byte: the shadow band, the frame and the flag byte are off the image *)
assert (NWR : forall a, in_img SEGS a -> ~ in_wrange EE (ss_mem ss_l6) a).
{ intros a Hi (r & Hr & Ha). pose proof (pa_segs_low a Hi) as Hlo. rewrite C5 in Hlo.
  cbn [ss_mem ss_l6 l6_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [l6_r_saved l6_r_shadow l6_r_hdr l6_r_flagptr l6_r_flag YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - lia.
  - rewrite U26, Esh in Ha. unfold SHADOW_OFF in Ha. lia.
  - rewrite U27 in Ha. exact (proj2 (proj2 (Gfr a ltac:(lia))) Hi).
  - lia.
  - rewrite U32 in Ha. assert (a = fl) by lia. subst a. exact (Gimg Hi). }
(* the allocator side of the flag-store rule at ARc *)
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
assert (ASFX : forall ly1 S1 Hp1 (W1 : world SEGS) mem1 md1 mem1' md1' c1 p1,
  ARc ly1 S1 Hp1 W1 mem1 md1 -> In (c1, p1) (frames S1) ->
  aview SEGS (w_H W1) mem1' (flag_addr ly1 c1 p1) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly1 S1 a -> a <> flag_addr ly1 c1 p1 ->
     aview SEGS (w_H W1) mem1' a = aview SEGS (w_H W1) mem1 a) ->
  (forall a, aview SEGS (w_H W1) mem1 a <> None -> aview SEGS (w_H W1) mem1' a <> None) ->
  m_vmmaps md1' = m_vmmaps md1 -> m_vm_lazy md1' = m_vm_lazy md1 -> eager_used md1' = eager_used md1 ->
  (forall a, in_band_rw a -> w_H W1 (w64 a) = true -> mem1' (w64 a) = mem1 (w64 a)) ->
  ARc ly1 (stack_free_state c1 p1 S1) Hp1 W1 mem1' md1').
{ intros ly1 S1 Hp1 W1 mem1 md1 mem1' md1' c1 p1 [HA1 HX1] Hin1 H0 H1 H2 H3 H4 H5 H6.
  split; [exact (HSFL ly1 S1 Hp1 W1 mem1 md1 mem1' md1' c1 p1 HA1 Hin1 H0 H1 H2 H3 H4 H5 H6)
         | exact (xs_placed_cf_stack_free ly1 S1 c1 p1 HX1)]. }
pose (RUNF := @aj_flag_store_x_invR fy rc SK SEGS B PST ARc cf_head LAWS pa_segs_low ASFX
  (frame_flag_x_xs SEGS B) (stack_free_x_any SEGS ARc) asym pa_wx
  (clookup pa_tbl) VAL pa_sigma A_prog_listing (@pl_tpi _ PL_102_A) (@pl_tw _ PL_102_A) pa_fetch_ok pa_cert pa_B_ok
  A_LIM A_LIM_text (@pl_lim _ PL_102_A) (@pl_len _ PL_102_A) (@pl_tpi_eq _ PL_102_A) (@pl_tw_eq _ PL_102_A)
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) WLE').
unfold cfg_at.
change (w64 EC_EXIT) with (Z_to_bv 64 (BASE + L6_K)).
(* THE LANE, +0x1c4 .. +0x2c4: one run of the flag-store rule, stopped at the `ret` *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict (w_H W) ?ms) =>
let K := eval vm_compute in (run_K A_LIM L6_Bx L6_SH ss) in
let rr := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL_102_A) (@pl_tw _ PL_102_A) K L6_Bx L6_Bspan L6_SH FUEL ss) in
lazymatch rr with (?st', ?rs) =>
assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL_102_A) (@pl_tw _ PL_102_A) K L6_Bx L6_Bspan L6_SH FUEL ss = (st', rs))
  by (vm_compute; reflexivity);
apply (RUNF W FUEL EE K L6_Bx L6_Bspan L6_SH ss st' rs ms LLVMF_STK (e_sp0 E) [] (e_ly E)
  (YG00.set_depot (st_depot S) (e_S E)) []
  (e_W E) (e_mem E) (e_md E) [] ly S [] md k LLVMF_FS_CLASS pos _
  ltac:(unfold A_LIM; cbn; lia) HEI ltac:(unfold LLVMF_FS_CLASS; lia) HS SHOK ltac:(vm_compute; reflexivity)
  Hrun I HJ HMN); clear Hrun
end end.
- (* no shadow obligation *)
  cbn [sh_obls]. apply Forall_nil.
- (* the run writes the frame's shadow bytes and header word (this call's own frame area) and the flag byte *)
  intros a (r & Hr & Ha). cbn [ss_mem ss_l6 l6_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [l6_r_saved l6_r_shadow l6_r_hdr l6_r_flagptr l6_r_flag YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + lia.
  + left. right; right; right. unfold in_frames. exists LLVMF_FS_CLASS, pos. split; [left; reflexivity|].
    right. unfold in_zr; cbn [fst snd]. rewrite U26 in Ha. rewrite <- Hfkeq.
    change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia.
  + left. right; right; right. unfold in_frames. exists LLVMF_FS_CLASS, pos. split; [left; reflexivity|].
    left. unfold in_zr; cbn [fst snd]. rewrite U27 in Ha. rewrite <- Hfkeq.
    change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia.
  + lia.
  + right. rewrite U32 in Ha. lia.
- (* the flag byte is 0 at the end: the flag region's one chunk *)
  intros ws0 msr Hlen0 HSr. cbn [sh_j] in Hlen0. destruct ws0; [|discriminate Hlen0].
  cbn [sh_ss extK length Nat.add] in HSr.
  pose proof (st_ok_mem_ok SEGS _ _ _ HSr) as (_ & HMO & _).
  cbn [ss_mem abs_ss setpc] in HMO.
  do 4 apply Forall_inv_tail in HMO.
  apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCH.
  apply Forall_inv in HCH. destruct (HCH 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [YP09.cbyte c_off YP09.c_val] in Hb1, Hb2. rewrite U32 in Hb2. rewrite !Z.add_0_r in Hb2.
  injection Hb1 as <-. change (flag_addr ly LLVMF_FS_CLASS pos) with fl. rewrite Hb2. f_equal.
- (* THE RETURN *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HMN' HF HFr HG.
  cbn [sh_j] in Hlen. destruct ws; [|discriminate Hlen]. clear Hlen.
  cbn [sh_ss extK length Nat.add] in HS', SHOK', HEI'.
  cbn [ms_mem mkst] in HF, HFr, HG.
  (* the `ret` keeps the world: the plain rule lifted into wle' (YA0nH.SRr_SRrG) *)
  apply (SRr_SRrG SEGS WLE' (wle_wle' SEGS _)).
  eapply (@paj_ret_at fy rc A_prog_listing PL_102_A PA W EE _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2.
  (* the final registers *)
  prreg HS' (1%bv : bv 5) Q1. prreg HS' (2%bv : bv 5) Q2. prreg HS' (3%bv : bv 5) Q3.
  prreg HS' (4%bv : bv 5) Q4. prreg HS' (8%bv : bv 5) Q8. prreg HS' (9%bv : bv 5) Q9.
  prreg HS' (10%bv : bv 5) Q10.
  prreg HS' (18%bv : bv 5) Q18. prreg HS' (19%bv : bv 5) Q19. prreg HS' (20%bv : bv 5) Q20.
  prreg HS' (21%bv : bv 5) Q21. prreg HS' (22%bv : bv 5) Q22. prreg HS' (23%bv : bv 5) Q23.
  prreg HS' (24%bv : bv 5) Q24. prreg HS' (25%bv : bv 5) Q25. prreg HS' (26%bv : bv 5) Q26.
  prreg HS' (27%bv : bv 5) Q27.
  assert (Hpc : v_jalr (getr (ms_regs ms') 1) 0 = w64 (raZ (e_regs E))).
  { rewrite Q1, E33, Z_to_bv_bv_unsigned. rewrite Hraok. unfold w64, raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  (* the bytes the run did not write *)
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange EE (ss_mem ss_l6) a ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a).
  { intros a Ha HWa. apply aview_eq_of. apply HFr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
  rewrite Hpc.
  lazymatch goal with |- cut_ret _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) =>
    exists ly, (stack_free_state LLVMF_FS_CLASS pos S), r, m, d, k, peak, cnt, ran end.
  split; [exists fy; split; [exact Hfrm0|]; split; [exact Hkept | reflexivity]|].
  (* the journal back at cut_exit's own trace budget WT (ec_wk_exit, cut_ret's): the lane stored no wild trace *)
  split.
  { exists WT. split; [|exact HWB].
    eapply ec_journal_unbaseR; [exact HJW|].
    apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS pa_segs_low WLE'). exact HJ'. }
  split.
  { apply l6_aregs.
    - rewrite Q2, E8. unfold e_sp0, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite Q3, E3. reflexivity.
    - rewrite Q4, E4. reflexivity.
    - rewrite Q8, E34. apply Z_to_bv_bv_unsigned.
    - rewrite Q9, E35. apply Z_to_bv_bv_unsigned.
    - rewrite Q18, E36. apply Z_to_bv_bv_unsigned.
    - rewrite Q19, E37. apply Z_to_bv_bv_unsigned.
    - rewrite Q20, E38. apply Z_to_bv_bv_unsigned.
    - rewrite Q21, E39. apply Z_to_bv_bv_unsigned.
    - rewrite Q22, E40. apply Z_to_bv_bv_unsigned.
    - rewrite Q23, E41. apply Z_to_bv_bv_unsigned.
    - rewrite Q24, E42. apply Z_to_bv_bv_unsigned.
    - rewrite Q25, E43. apply Z_to_bv_bv_unsigned.
    - rewrite Q26, E44. apply Z_to_bv_bv_unsigned.
    - rewrite Q27, E45. apply Z_to_bv_bv_unsigned. }
  split; [rewrite Q10; reflexivity|].
  split; [exact HPERM|].
  split.
  { exists lmost, lown.
    apply (prh_ledger_kept B ly S [] W mem ly (stack_free_state LLVMF_FS_CLASS pos S) [] W (ms_mem ms') []
      peak cnt SIZE_MAX ran lmost lown HLED).
    - intros a Ha. destruct (Hpst a Ha) as (_ & Hi).
      pose proof (pa_segs_low a Hi) as Hlo.
      apply (prh_mbyte_of_mrestrict (in_wrange EE (ss_mem ss_l6))); [exact HFr | lia | exact (NWR a Hi)].
    - intros a k0 i Hin0. destruct Hin0.
    - intros a k0 Hin0. destruct Hin0.
    - apply Permutation_refl. }
  split; [exact HCNT|].
  split.
  { apply (Hsioframe (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms'))); [|exact HSIO].
    intros a Ha. destruct (Hsio a Ha) as (_ & Hi & _). pose proof (pa_segs_low a Hi) as Hlo.
    apply KV; [lia | exact (NWR a Hi)]. }
  split; [apply RL_stack_free; exact HLIVE|].
  split.
  { (* no event in this lane: cut_ret's position is cut_exit's, the whole call_evs over e_os ++ [trp] *)
    destruct HROOM as (hist & HR). exists trp, hist.
    exact (PresetRoomPosKeep.room_pos_stack_free _ _ _ _ _ _ S LLVMF_FS_CLASS pos HR). }
  split.
  { intros i Hi.
    destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    destruct HPAY as [Hn0' | Hinp']; [lia|].
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2' & _).
    pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
    apply (F2' (e_p E) (e_n E) i Hinp Hinp' ltac:(lia)).
    intros (r & Hr & _). destruct Hr. }
  exact HMN'.
Qed.

End L6.

Print Assumptions seg_L6x_A.
About seg_L6x_A.

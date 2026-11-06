(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the STATEMENTS of pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24, 136 slots of
   lib/B/Listing_prog.v, 4 * 136 = 544 bytes; preset_file.c :334-350).
   proves no function (kind: statement text).
   WHAT IS STATED HERE
   - THE FREE ORDER is the KIT'S, lib/A/PRH_PjOrder.v (pf_oitemsR, pj_oshapeR, pj_foR: PRH_Reader.v's pj_fdR with the
     list F of the blocks in the order pj_free frees them; taken into the kit by path from an earlier copy of this
     walk, blob e5917626b82b). This file keeps no copy.
   - THE OBSERVER (pf_obs, pf_reach, pf_safe) and THE INSTRUMENTED TEXTS (tfuzz_free_specO PB FX: the fuzz_free
     premises with the room premises abstracted to room_live_cf S /\ PB S and the call's FX added to the post;
     tpj_free_specO PB FX CTX0 n: pj_free's text with pj_foR, `v <> 0 -> pf_safe FX PB F ly S` at entry and
     pf_reach FX F ly S [] ly' S' in the post; pf_K0post) are IMAGE-FREE and have ONE home, lib/A/Prog/PjFreeCommon.v
     (blob 2de257796592; moved there from this file, byte-identical, generic over {L} {PA}; the #102 copy, with most /
     own first in both texts' binders, is by path, blob 9da7fca4fd35). This file keeps no copy. pf_texts (below) pairs
     fuzz_free's instrumented text with __asan_memset's m-form intrinsic text; the kit's tpj_free_specX (lib/A/PRH_FnPj.v,
     blob 3a546f3492c6: tpj_free_specX CTX0 n, no run words, with the premise prh_head_wide) follows at image B
     (pj_free_top.v tpj_free_specX_B) from the kit's own fuzz_free text tfuzz_free_specX (its trace premise `admits
     (as_universe B) (call_trace ..) S` and its post BUDGETED at that trace; tfuzz_free_specO takes the trace in
     u_fix, which pj_free's FIXED traces have, and states the plain post) by PjFreeCommon.v pf_ff_of_kit /
     pf_specX_of_walk.
     (History: at walkkit a3bdeca3920 the kit's fuzz_free premise ccnt24 S <= L24 + DRV was open at every call - the
     STOP the kit owner ruled on by adding the entry premise and the keep to the kit texts; at decff67d721f the walk
     took an earlier fuzz_free text with the entry widened to a bulk sub-position, which f97c's post-implication form made
     unnecessary.)
   - THE CUTS of the walk: the entry record PfEnt (tpj_free_specO's premises, pf_pre), the node record PfNode (v's
     header and its block lists at the entry), the post pf_Q / pf_FIN, and the cut states pf_LH (loop head, +0xa8),
     pf_LX (after the loop, +0x14c), pf_EP (epilogue, +0x1a8), with the segment statements each segment file proves.
   THE RE-HIDING MOVE: a free can hide shadow again, so the walk runs at the relation wle' SEGS RZ_cf (YA0nH.v, the zone
   of YGcfRehidePost.v): pf_FIN is fpostWm's R form at it (PRH_Base fpostWmR), every segment statement concludes
   SRr' SEGS RZ_cf, and every cut after the prologue holds the frame at it (pf_frameR, the copy of pf_frame's body over
   a world relation R; pf_frame is its instance at wle, pf_frame_R_wle).
   The body (B listing slots 5081 .. 5216; pc offsets from pj_free's entry, DERIVED below):
     +0x000 .. +0x034  sp -= 128; ra, s0 .. s11 saved at sp+120 .. sp+24
     +0x038            beqz a0 -> +0x1a8 (v = NULL)
     +0x03c .. +0x044  s0 := v; UBSan alignment `andi a0,a0,7; bnez -> unimp`     NOT TAKEN (pj_rwR: v mod 8 = 0)
     +0x048 .. +0x050  s7 := the shadow offset (GOT slot, then the cell)
     +0x054 .. +0x064  ASan check of v+40 (n)                                       NOT TAKEN (v's shadow)
     +0x068 .. +0x084  n; s3 := v+24, s1 := v+32; (v+24)>>3 at sp+8, (v+32)>>3 at sp+16; beqz n -> +0x14c
     +0x088 .. +0x0a4  s8 = s9 = s10 = 0; s11 := sh(v+24); s5 := 56; s4 := sh(v+32)
     +0x0a8            LOOP HEAD (cut pf_LH): ASan check of v+24; kids; UBSan pointer / product checks on kids + 56 i
     +0x0e8 .. +0x0ec  a0 := kids + 56 i; jal pj_free (B 0x86b10, recursion)
     +0x0f0 .. +0x12c  ASan check of v+32; keys; beqz keys -> +0x130; UBSan checks on keys + 8 i; ASan check of
                       keys + 8 i; keys[i]; jal fuzz_free (B 0x86b50)
     +0x130 .. +0x148  ASan check of v+40; n; i += 1; bltu i, n -> +0xa8
     +0x14c            AFTER THE LOOP (cut pf_LX): ASan check, kids, jal fuzz_free (B 0x86b84); ASan check, keys,
                       jal fuzz_free (B 0x86b9c); ASan check, str, jal fuzz_free (B 0x86bb8); memset (v, 0, 56) by
                       jal __asan_memset (B 0x86bc8, printed as checked_memset)
     +0x1a8            EPILOGUE (cut pf_EP): ra, s0 .. s11 restored, sp += 128, ret
     +0x1e4 ..         unimp (UBSan), the errpath_load8 calls (ASan reports): never reached
   Numerals: 128 / 120 .. 24 / 8 / 16 (LENGTH: frame, slots), 56 / 40 / 32 / 24 / 16 (LENGTH: struct pj, its
   fields), 8 (LENGTH: a key pointer); every pc offset is DERIVED (PJF_PC + 4 * slot). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ================================================================ the walk's cuts, at image B *)
(* pc offsets from pj_free's entry (DERIVED: the listing's slot differences times 4) *)
Definition PJF_PC : Z := B_prog_sigma AS_pj_free - B_prog_base.
Definition PJF_LH : Z := PJF_PC + 168.     (* +0xa8, the loop head `lbu a0, 0(s11)` *)
Definition PJF_LX : Z := PJF_PC + 332.     (* +0x14c, after the loop `ld a0, 8(sp)` *)
Definition PJF_EP : Z := PJF_PC + 424.     (* +0x1a8, the epilogue `ld ra, 120(sp)` *)
Definition PJF_FR : Z := 128.              (* pj_free's frame (prh_img_B's pi_frame F_pj_free) *)

(* the registers pj_free saves, with their frame offsets from the lowered sp (ra, s0 .. s11) *)
Definition PJF_SAVED : list (Z * Z) :=
  [(1, 120); (8, 112); (9, 104); (18, 96); (19, 88); (20, 80); (21, 72); (22, 64); (23, 56); (24, 48); (25, 40);
   (26, 32); (27, 24)].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the callee texts at image B: fuzz_free instrumented (m-form), and __asan_memset's m-form intrinsic text
   (YGcallMxmn.v aintrin_realizes_xm OSet, s1b 459129c18903) *)
Definition pf_texts (PB : astate -> Prop) (FX : pf_obs) : Prop :=
  tfuzz_free_specO (PA := PA) B ARx SK PB FX /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset).

(* ---- the entry ---- *)
Record PfEnt : Type := MkPfEnt {
  fe_ly : alayout; fe_S : astate; fe_Hp : list Z; fe_W : world SEGS; fe_regs : bvmap 5 word;
  fe_mem : word -> option byte; fe_md : Model; fe_ch : list (Z * Z * Z);
  fe_d : Z; fe_v : Z; fe_D : list (Z * Z); fe_F : list (Z * Z); fe_Lam : list (Z * Z);
  fe_peak : Z; fe_cnt : Z; fe_fail : Z; fe_ran : Z; fe_most : Z; fe_own : Z; fe_n : nat }.
Definition fe_sp0 (en : PfEnt) : Z := spZ (fe_regs en).
Definition fe_sp1 (en : PfEnt) : Z := fe_sp0 en - PJF_FR.
Definition fe_FP (en : PfEnt) : list (Z * Z) :=
  if fe_v en =? 0 then [] else (fe_v en, fe_v en + 56) :: ablocks_fp (prhPj_hbl (fe_D en)).

(* tpj_free_specO's premises, verbatim, over the entry record (pf_safe for v <> 0 only, as the class-24 bound) *)
Definition pf_pre (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (en : PfEnt) : Prop :=
  let ly := fe_ly en in let S := fe_S en in let Hp := fe_Hp en in let W := fe_W en in let regs := fe_regs en in
  let mem := fe_mem en in let md := fe_md en in let ch := fe_ch en in let d := fe_d en in let v := fe_v en in
  let D := fe_D en in let F := fe_F en in let Lam := fe_Lam en in let n := fe_n en in
  fpre (PA := PA) B ARx (STK_pj_free n) ly S Hp W regs mem md ch /\
  prh_univ_closure B CTX0 /\ room_live_cf S /\
  getr regs 10 = w64 v /\
  fwin (PA := PA) ly W regs mem d /\
  (v = 0 /\ D = [] /\ F = [] \/
   v <> 0 /\ v < YM05.alloc_ceiling /\ pj_foR SEGS (rdW W mem) (prh_lin Lam) n v D F /\
   prhPj_slot (PA := PA) B (STK_pj_free n) d ly S Lam W regs mem v) /\
  (v <> 0 -> pf_safe FX PB F ly S) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en).

(* the post body over the entry's values *)
Definition pf_Q (FX : pf_obs) (en : PfEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  pf_K0post (PA := PA) B (fe_D en) (fe_v en) (fe_ly en) (fe_S en) (fe_Hp en) (fe_Lam en)
    (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) ly' S' Hp' W' regs' mem' md' /\
  pf_reach FX (fe_F en) (fe_ly en) (fe_S en) [] ly' S'.

(* the walk's goal: the kit's post form at wle' SEGS RZ_cf (PRH_Base fpostWmR) *)
Definition pf_FIN (FX : pf_obs) (en : PfEnt) : world SEGS -> config -> Prop :=
  fpostWmR (PA := PA) B ARx SK (wle' SEGS RZ_cf) (STK_pj_free (fe_n en)) (fe_d en) (fe_FP en)
    (fe_regs en) (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) (pf_Q FX en).

(* the configuration at a cut *)
Definition pf_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS)) md.

(* ---- v's node at the entry (v <> 0): its header and its block lists, pj_oshapeR's witnesses ---- *)
Record PfNode : Type := MkPfNode {
  fn_ty : Z; fn_num : Z; fn_str : Z; fn_kids : Z; fn_keys : Z; fn_n : Z; fn_cap : Z; fn_ks : bool;
  fn_Ds : list (Z * Z); fn_Dk : list (Z * Z); fn_Dy : list (Z * Z); fn_Di : list (Z * Z); fn_Fi : list (Z * Z) }.

(* the node's own blocks, freed after the loop in this order *)
Definition fn_own (nd : PfNode) : list (Z * Z) := fn_Dk nd ++ fn_Dy nd ++ fn_Ds nd.

Definition pf_node (en : PfEnt) (nd : PfNode) : Prop :=
  let m := rdW (fe_W en) (fe_mem en) in let lblk := prh_lin (fe_Lam en) in
  NoDup (fe_D en) /\ pj_apartR (fe_D en) (fe_v en) /\
  pj_hdrR SEGS m (fe_v en) (fn_ty nd) (fn_num nd) (fn_str nd) (fn_kids nd) (fn_keys nd) (fn_n nd) (fn_cap nd) /\
  (fn_str nd = 0 /\ fn_Ds nd = [] \/ exists k, lblk (fn_str nd) k /\ fn_Ds nd = [(fn_str nd, k)]) /\
  (fn_kids nd = 0 /\ fn_n nd = 0 /\ fn_Dk nd = [] \/
   exists k, lblk (fn_kids nd) k /\ 56 * fn_n nd <= k /\ fn_Dk nd = [(fn_kids nd, k)]) /\
  (fn_keys nd = 0 /\ fn_ks nd = false /\ fn_Dy nd = [] \/
   fn_ks nd = true /\ exists k, lblk (fn_keys nd) k /\ 8 * fn_n nd <= k /\ fn_Dy nd = [(fn_keys nd, k)]) /\
  Permutation (fe_D en) (fn_Ds nd ++ fn_Dk nd ++ fn_Dy nd ++ fn_Di nd) /\
  fe_F en = fn_Fi nd ++ fn_own nd /\
  match fe_n en with
  | O => fn_n nd = 0 /\ fn_Di nd = [] /\ fn_Fi nd = []
  | S d' => pf_oitemsR SEGS m lblk (pj_foR SEGS m lblk d') (fn_ks nd) (fn_kids nd) (fn_keys nd) (Z.to_nat (fn_n nd))
              (fn_Di nd) (fn_Fi nd)
  end.

(* ---- what holds at every cut after the prologue ---- *)
(* the frame: the journal from the entry at the widened window, footprint fe_FP; the caller's window outside the
   footprint untouched; sp lowered by 128; the saved ra, s0 .. s11 in their slots; the frame present; gp, tp kept;
   the read-only view; THE MEMNORM KEEP from the entry memory (kit 4f18c75d4900 PRH_Base.v fQmn: every cut carries
   `memnorm mem0 -> memnorm mem`, the P of YSRrMemnorm.srr_inv_laws_imp, so the epilogue closes fpostWm) *)
Definition pf_frame (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  AJ (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md k /\
  (forall a, fe_sp0 en <= a < fe_sp0 en + fe_d en -> ~ inFP (fe_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) /\
  spZ regs = fe_sp1 en /\
  (forall r o, In (r, o) PJF_SAVED ->
     val_mem SEGS (rdW W mem) (fe_sp1 en + o) 8 (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 r)))) /\
  (forall a, fe_sp1 en <= a < fe_sp0 en -> apresent (w_H W) mem a) /\
  getr regs 3 = getr (fe_regs en) 3 /\ getr regs 4 = getr (fe_regs en) 4 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (YAkMemnorm.memnorm SEGS (fe_mem en) -> YAkMemnorm.memnorm SEGS mem).

(* SHARED: the R form beside (a copy of pf_frame's body with the journal at R, ajournal_xR R); every cut after the
   prologue holds it at R := wle' SEGS RZ_cf *)
Definition pf_frameR (R : world SEGS -> world SEGS -> Prop) (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md k /\
  (forall a, fe_sp0 en <= a < fe_sp0 en + fe_d en -> ~ inFP (fe_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) /\
  spZ regs = fe_sp1 en /\
  (forall r o, In (r, o) PJF_SAVED ->
     val_mem SEGS (rdW W mem) (fe_sp1 en + o) 8 (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 r)))) /\
  (forall a, fe_sp1 en <= a < fe_sp0 en -> apresent (w_H W) mem a) /\
  getr regs 3 = getr (fe_regs en) 3 /\ getr regs 4 = getr (fe_regs en) 4 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (YAkMemnorm.memnorm SEGS (fe_mem en) -> YAkMemnorm.memnorm SEGS mem).
Lemma pf_frame_R_wle : forall en ly S Hp W regs mem md k,
  pf_frame en ly S Hp W regs mem md k = pf_frameR (@wle SEGS) en ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* the spilled shadow indices of v+24 and v+32 (sd at +0x078 / +0x080) *)
Definition pf_spill (en : PfEnt) (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rdW W mem) (fe_sp1 en + 8) 8 ((fe_v en + 24) / 8) /\
  val_mem SEGS (rdW W mem) (fe_sp1 en + 16) 8 ((fe_v en + 32) / 8).

(* v's node at a state: its header words str / kids / keys / n as at the entry, its 56 bytes writable, outside the
   allocator's and below alloc_ceiling, its shadow addressable, and where it lives (prhReader_at's four places, never
   one of D's blocks) *)
Definition pf_vnode (en : PfEnt) (nd : PfNode) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world SEGS)
  (mem : word -> option byte) : Prop :=
  let v := fe_v en in let m := rdW W mem in
  4096 <= v /\ v + 56 <= YM05.alloc_ceiling /\ v mod 8 = 0 /\ amem_range v 56 /\
  rd_u64 SEGS m (v + 16) (fn_str nd) /\ rd_u64 SEGS m (v + 24) (fn_kids nd) /\
  rd_u64 SEGS m (v + 32) (fn_keys nd) /\ rd_u64 SEGS m (v + 40) (fn_n nd) /\
  pj_rwR SEGS m v /\ (forall a, v <= a < v + 56 -> ~ aowned B ly S a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 /\ shadow_hull_vis (aview SEGS (w_H W) mem) v 56 /\
  ((exists a k, In (a, k) Lam /\ ~ In (a, k) (fe_D en) /\ a <= v /\ v + 56 <= a + k) \/
   (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= v /\ v + 56 <= b + m) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
   (fe_sp0 en <= v /\ v + 56 <= fe_sp0 en + fe_d en)).

(* the registers holding v's fields (s0 = v, s1 = v+32, s2 = v+40, s3 = v+24) and the shadow offset s7, with s6 its
   cell of v+40 *)
Definition pf_vregs (en : PfEnt) (regs : bvmap 5 word) : Prop :=
  let v := fe_v en in
  getr regs 8 = w64 v /\ getr regs 9 = w64 (v + 32) /\ getr regs 18 = w64 (v + 40) /\
  getr regs 19 = w64 (v + 24) /\ getr regs 23 = w64 SHADOW_OFF /\
  getr regs 22 = w64 ((v + 40) / 8 + SHADOW_OFF).

(* the loop registers at slot i: s4 = cell of v+32, s5 = 56, s8 = 56 i, s9 = 8 i, s10 = i, s11 = cell of v+24 *)
Definition pf_lregs (en : PfEnt) (regs : bvmap 5 word) (i : Z) : Prop :=
  let v := fe_v en in
  getr regs 20 = w64 ((v + 32) / 8 + SHADOW_OFF) /\ getr regs 21 = w64 56 /\
  getr regs 24 = w64 (56 * i) /\ getr regs 25 = w64 (8 * i) /\ getr regs 26 = w64 i /\
  getr regs 27 = w64 ((v + 24) / 8 + SHADOW_OFF).

(* the accounts at a state: the room, the ledger at Lam, the freed blocks Fd off Lam and off the allocator's
   blocks, the order so far (F = Fd ++ Fr, Fd taken off F's front in order) *)
Definition pf_acct (FX : pf_obs) (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (Fd Fr Lam : list (Z * Z)) : Prop :=
  room_live_cf S /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) /\
  Permutation (fe_Lam en) (Fd ++ Lam) /\
  Permutation (ablocks B (fe_ly en) (fe_S en)) (prhPj_hbl Fd ++ ablocks B ly S) /\
  fe_F en = Fd ++ Fr /\
  pf_reach FX (fe_F en) (fe_ly en) (fe_S en) Fr ly S.

(* ---- the cuts (each after the prologue, so the frame at wle' SEGS RZ_cf) ---- *)
(* LOOP HEAD at slot i of a node of depth S d': the slots i .. n-1 still to free, in the current memory and ledger *)
Definition pf_LH (FX : pf_obs) (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_spill en W mem /\ pf_vregs en regs /\
  pf_lregs en regs i /\
  exists Fd Lam Dr Fr,
    pf_acct FX en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam /\
    pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dr ++ fn_own nd) /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * i) (fn_keys nd + 8 * i) (Z.to_nat (fn_n nd - i)) Dr Fr.

(* AFTER THE LOOP: every slot freed; kids, keys, str to free *)
Definition pf_LX (FX : pf_obs) (en : PfEnt) (nd : PfNode) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_spill en W mem /\ pf_vregs en regs /\
  exists Fd Lam,
    pf_acct FX en ly S Hp W mem Fd (fn_own nd) Lam /\
    pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ fn_own nd).

(* EPILOGUE: the post holds; the frame still to pop *)
Definition pf_EP (FX : pf_obs) (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_Q FX en ly S Hp W regs mem md.

(* ---- the segment statements (one file each), at SRr' SEGS RZ_cf ---- *)
Definition pfs_EP (FX : pf_obs) : Prop :=
  forall PB CTX0 en ly S Hp W regs mem md k, pf_pre PB FX CTX0 en ->
  pf_EP FX en ly S Hp W regs mem md k -> SRr' SEGS RZ_cf W (pf_cfg PJF_EP regs mem md) (pf_FIN FX en).
Definition pfs_LX (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) : Prop :=
  forall en nd ly S Hp W regs mem md k, pf_pre PB FX CTX0 en -> pf_node en nd ->
  pf_LX FX en nd ly S Hp W regs mem md k -> SRr' SEGS RZ_cf W (pf_cfg PJF_LX regs mem md) (pf_FIN FX en).
(* the loop body from slot i: to slot i + 1 or out of the loop; d' is the children's depth, whose text the
   recursive call cites *)
Definition pfs_LH (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre PB FX CTX0 en -> pf_node en nd ->
  pf_LH FX en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LH FX en nd d' (i + 1) ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PJF_LH regs1 mem1 md1) (pf_FIN FX en)) ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LX FX en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PJF_LX regs1 mem1 md1) (pf_FIN FX en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PJF_LH regs mem md) (pf_FIN FX en).
Definition pfs_entry (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) : Prop :=
  forall en, pf_pre PB FX CTX0 en ->
  SRr' SEGS RZ_cf (fe_W en) (cfg_at SEGS (pa_sigma AS_pj_free) (fe_regs en) (fe_mem en) (fe_md en)) (pf_FIN FX en).
End d.

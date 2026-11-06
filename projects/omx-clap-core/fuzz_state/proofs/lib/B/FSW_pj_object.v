(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module paths and addresses changed; 440 of its 567 lines of code are new or changed and 1474 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: a re-walk over IMAGE B of the image-A walk lib/A/FSW_pj_object.v
   (a working branch bfa236c8a89), same lemma structure, on lib/B's walk kit (FSW_K / FSW_ret / FSW_rd) and B's
   own code; no lib/A image-content file is Required. *)
(* pj_object 0x83f1c (preset_file.c pf.c:433-437) on fs.asan-ubsan (sha256 5ac5ce0954f8...), 30 words: the ASan walk
   of the READER lane's pj_object_spec (lib/B/FSH_Fn_reader.v:748, Section c, statement unchanged).
   rule 24: no released proof of pj_object over this image exists. Reuse search (a Theorem Labs lane, outputs under
   (internal path)): (1) by name with control, proof-index pj_get pj_free pj_string
   (r24-pj_get-free.txt) and proof-index pj_object pj_get_str pj_string (r24-B3.txt): released hits are the plain
   lib/Prog and ubsan lib/U proofs only, no ASan address in the index; (2) by address, B's pj_object 0x83f1c (.symtab of
   fs.asan-ubsan), a direct jal callee with no trampoline / wrapper / REAL slot; (3) named cold branches, git grep by name
   and address (r24-cold-B3.txt, r24-cold-pjget-free.txt, chk-cold-extra.txt): two working branches
   lib/B/Prog/pj_object.v (a bespoke evt-form proof of B's code: a template, not bridgeable), preset's, S0's B statement
   and the image-A walk. Second-agent check a Theorem Labs lane (chk-B4-summary.txt): `pj_object B: CONFIRM`.

   The code (listing (internal path)): `addi sp,sp,-32; sd ra,24(sp);
   sd s0,16(sp); sd s1,8(sp); auipc a1,0x1c; ld a1,-796(a1); ld s1,0(a1)` (s1 := the shadow base through the .got word
   0x9fc10 = YB1w tfib_D_GOT_asan_shadow_memory_dynamic_address, which holds the cell 0xa8438), `mv s0,a0; li a2,56;
   li a1,0; jal __asan_memset` (0x83f44), then UBSan's two checks of the 4-byte store, `beqz s0,0x83f80` (null) and
   `andi a0,s0,7; bnez a0,0x83f80` (alignment), both to the trap `unimp` 0x83f80; then ASan's inline shadow check
   `srli a1,s0,3; add a1,a1,s1; lb a1,0(a1); bnez a1,0x83f84`, `li a0,6; sw a0,0(s0)`, the epilogue and `ret`
   (0x83f7c); 0x83f84.. is the slow check and `jal __asan_report_store4` 0x83f90.
   The walk (the image-A walk's form, lib/B FSW_K kit):
   - run 1 (FSW_K fsw_aj_run_toU) from fss0T to the entry of __asan_memset PC_memset 0x5222c;
   - the runtime call: the contract aintrin_realizesU OSet PC_memset (Section hypothesis), composed into the journal by
     FSW_K.fsw_intrin_atU;
   - a resume state at 0x83f48 built from the contract's post (pjo_resume_ok: frame + saved ra/s0/s1 as extra atoms
     33/34/35, fss0T's two shadow-base cells, s1 pinned to atom 32, the first 4 bytes of v as the store window, and
     atom 8 = s0 = v with the fact mkAF 4096 PJO_CEIL 3);
   - run 2 with the TOKEN engine (Bx := fs_Bx, Bspan := fs_Bspan, one shent [v, v + 56)). UBSan's branches, each ruled
     out by a named premise: `beqz s0` 0x83f48 by pobj (fsw_pobj_low: 4096 <= v), `bnez a0` 0x83f50 by pobj
     (v mod 8 = 0); the engine decides both from atom 8's fact (YP0m.decide_eq; YP0m.s_and_ptr folds `andi a0,s0,7` to
     0), so the trap 0x83f80 is never reached. ASan's `bnez a1` 0x83f60 is decided by the shent, which pobj's
     range_addressable discharges, so __asan_report_store4 is never reached; the run stops at the `ret`;
   - the return: FSW_ret.fsw_retU.
   The post: v's 56 bytes are le4 6 ++ 52 zeros (the empty object node, plain pj_object_c.v:24), pobj and fs_glob kept
   (the object and the frame are not in the image: AR_client_img_law), ablocks unchanged (no allocation, U' = U).

   THE WRITE RULE. Both arms of pobj go through the core's own awr_byte at FP = [(v, v + 56)] and fr0 = frames S: the
   block arm through awr_byte0's FP-and-block case, the fake-frame arm (check_round_trip's class-3 fake frame, callers
   0x8227c / 0x82284) through awr_byte's frame case. No write-rule hypothesis.

   Section hypotheses (owners):
   - HSS : FsShadowSyms B, B's shadow-base .got word and cell   (S0 lib/B/FSH_Base.v:112)
   - fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset   (POISON-U, lib/A/FSupoisonU.v; lib/B/FSH_Rt.v
                                                                          FsRt fr_memset)
   The frame's shadow hull is lib/B/FSW_rd.v fsw_afobj_hull. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_rd FSH_Fn_reader FSW_pj_object_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the resume state at 0x83f48 (after __asan_memset returns) ----
   regions: the frame [sp, sp + 32) (sp = entry sp - 32, atom 2) with ra / s0 / s1 saved at 24 / 16 / 8 (extra atoms
   33 / 34 / 35 = the entry ra / s0 / s1), fss0T's .got word and shadow-base cell, and the store window [v, v + 4)
   (atom 8 = s0 = v). s1 is pinned to atom 32 (the shadow base, the token engine's Bx = fs_Bx). The token run from here
   decides the two UBSan branches by atom 8's fact (see run 2) and ends at the `ret` 0x83f7c with no obligation left. *)
Definition pjo_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition pjo_vreg : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [].
Definition PJO_CEIL : Z := 140737479966720.         (* 0x7fffff800000, the upper bound of alloc_ceiling (asan_consts) *)
Definition pjo_ret : sstate :=
  mkSS 0x83f48 (sr_set sr_atoms 9%bv (SOff 32 0)) (fsT_ret_regions 32 pjo_cs [pjo_vreg]) None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (8%nat, mkAF 4096 PJO_CEIL 3)]
       [] []).
Definition pjo_SH : list shent := [mkSHE 8 0 56].
Definition pjo_xs (regs : bvmap 5 word) : list word := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9].
(* the callee-saved registers at the `ret`: sp back up by the frame, s0 / s1 reloaded, the rest kept *)
Definition pjo_expect (r : bv 5) : sv :=
  if bv_eqb r 2%bv then SOff 2 32 else if bv_eqb r 8%bv then SOff 34 0 else if bv_eqb r 9%bv then SOff 35 0
  else SOff (Z.to_nat (bv_unsigned r)) 0.

(* ---- image facts used by the walk ---- *)
(* a byte range inside one loaded segment is in the image *)
Lemma pjo_seg_cover : forall a n,
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs
    = true ->
  forall x, a <= x < a + n -> in_img tfibsegs x.
Proof.
intros a n H x Hx. apply existsb_exists in H as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* a run frame leaves every byte outside its write windows *)
Lemma pjo_same_below_wr : forall E rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a) -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E rs m m' lo HF Hw H64 x Hx. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (Hw _ Hin). lia.
Qed.
Lemma pjo_frame_mbyte : forall E rs (H : word -> bool) m m' a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite (wz a Ha). exact Hn.
Qed.
Lemma pjo_frame_aview : forall E rs (H : word -> bool) m m' a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of tfibsegs). apply HF. rewrite (wz a Ha). exact Hn.
Qed.
Lemma pjo_val_keep : forall (m m' : word -> option byte) a n v,
  (forall k, 0 <= k < Z.of_nat n -> mbyte tfibsegs m' (a + k) = mbyte tfibsegs m (a + k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hk Hv k Hk'. rewrite (Hk (Z.of_nat k) ltac:(lia)). exact (Hv k Hk'). Qed.
Lemma pjo_mbyte_of_aview : forall (H : word -> bool) m a z,
  aview tfibsegs H m a = Some z -> mbyte tfibsegs (mrestrict H m) a = Some (Z_to_bv 8 z).
Proof.
intros H m a z E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|]; [|discriminate E].
cbn in E. injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pjo_apresent_unpoison : forall U (H : word -> bool) m m' a,
  (apresent H m a -> apresent H m' a) -> apresent H (unpoison U m) a -> apresent H (unpoison U m') a.
Proof.
intros U H m m' a Hm Hp. unfold apresent, unpoison in *. destruct Hp as [Hh [b Hb]].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))).
- split; [exact Hh | exists (Z_to_bv 8 0); reflexivity].
- exact (Hm (conj Hh (ex_intro _ b Hb))).
Qed.
(* the run windows of the two symbolic states *)
Lemma pjo_wr1 : forall E a sp, bv_unsigned (ew E 2) = sp ->
  in_wrange E (ss_mem (fss0T A_pj_object 32)) a -> sp - 32 <= a < sp.
Proof.
intros E a sp E2 (r & Hin & Hr). cbn [ss_mem fss0T fsT_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma pjo_wr2 : forall E a sp v, bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = v ->
  in_wrange E (ss_mem pjo_ret) a -> sp <= a < sp + 32 \/ v <= a < v + 4.
Proof.
intros E a sp v E2 E8 (r & Hin & Hr). cbn [ss_mem pjo_ret fsT_ret_regions app In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [fstk_ret fs_got_region fs_bcell_region pjo_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.


(* ---- the empty object node from its bytes ---- *)
Lemma pjo_node_ok : forall (m : word -> option byte) v,
  0 <= v -> v + 56 <= 2 ^ 64 -> v mod 8 = 0 ->
  (forall a, v <= a < v + 56 -> writable_at tfibsegs m a) ->
  (forall i, 0 <= i < 56 -> mbyte tfibsegs m (v + i) = Some (Z_to_bv 8 (if i =? 0 then 6 else 0))) ->
  PjStruct.pj_node tfibsegs m (fun a k => In (a, k) []) v (PjTree.JObj []) [].
Proof.
intros m v H0 H64 H8 Hpres Hb.
assert (BA : forall a bs n, length bs = n -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> mbyte tfibsegs m (a + Z.of_nat i) = nth_error bs i) -> Mem.bytes_at tfibsegs m a bs).
{ intros a bs n Hn Ha Hl H. subst n. split; [exact Ha|]. split; [exact Hl|]. intros i Hi. exact (H i Hi). }
assert (U64 : forall k, 1 <= k <= 6 -> PjStruct.pj_u64 tfibsegs m (v + 8 * k) 0).
{ intros k Hk. split; [lia|]. apply (BA _ _ 8%nat); [reflexivity | lia | lia |].
  intros i Hi.
  replace (v + 8 * k + Z.of_nat i) with (v + (8 * k + Z.of_nat i)) by lia.
  rewrite Hb by lia. replace (8 * k + Z.of_nat i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  do 8 (destruct i as [|i]; [reflexivity|]). lia. }
cbn [PjStruct.pj_node]. split; [constructor|]. split; [intros b x Hin; destruct Hin|].
exists 0, 0, 0, 0, 0, 0. split.
- change (PjTree.tag (PjTree.JObj [])) with 6. unfold PjStruct.pj_hdr.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  + split; [exact H8|]. split; [lia|]. split; [lia|]. intros a Ha. split.
    * exact (Hpres a Ha).
    * replace a with (v + (a - v)) by lia. eexists. exact (Hb (a - v) ltac:(lia)).
  + split; [lia|]. apply (BA _ _ 4%nat); [reflexivity | lia | lia |]. intros i Hi.
    rewrite Hb by lia. destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  + exact (U64 1 ltac:(lia)).
  + exact (U64 2 ltac:(lia)).
  + exact (U64 3 ltac:(lia)).
  + exact (U64 4 ltac:(lia)).
  + exact (U64 5 ltac:(lia)).
  + exact (U64 6 ltac:(lia)).
- split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [left; auto|].
  exists []. split; reflexivity.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0 lib/B/FSH_Base.v:112 FsShadowSyms: B's shadow-base .got word FS_GOT_shadow 0x9fc10 and cell FS_shadow_cell
   0xa8438 (owner S0; the B twin of lib/A/FSH_Base.v's, whose owner is RELOC: TfibLib tl_got_shadow / tl_shadow_cell) *)
Hypothesis HSS : FsShadowSyms B.
(* owner POISON-U (a Theorem Labs lane, lib/A/FSupoisonU.v aintrin_realizesU, the ARU form of the donor's __asan_memset
   contract) at B's PC_memset 0x5222c (lib/B/FSH_Base.v:88); lib/B/FSH_Rt.v:118 FsRt fr_memset; named in
   lib/B/FSH_Fn_reader.v:90-92 *)
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.
(* ---- where a pobj lies ---- *)
(* a pobj's bytes: present and not owned at any AR memory of its layout and state, outside the image, application
   bytes; its range is an __asan_memset range and its shadow hull is visible *)
Lemma pjo_place : forall ly S (W : world tfibsegs) mx md m v,
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v ->
  (forall a, v <= a < v + 56 -> apresent (w_H W) mx a /\ ~ aowned B ly S a /\ ~ in_img tfibsegs a /\ app_addr a) /\
  amem_range v 56 /\ shadow_hull_vis (aview tfibsegs (w_H W) mx) v 56.
Proof.
intros ly S W mx md m v HAR ([((cid & pos & Hin & Hc & Hal & H1 & H2) & Hv8 & Hr)|((b & n & Hin & H1 & H2) & Hv8 & Hr)] & Hw).
- pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_frames _ _ LAWS ly S W mx md cid pos HAR Hin) as (_ & Happ & Hb & _).
  destruct (frames_bounds tfibsegs B LAWS ly S W mx md cid pos HAR Hin) as (F1 & F2 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split].
  + intros a Ha. destruct (Hb a ltac:(lia)) as [Hp Hno]. split; [exact Hp|]. split; [exact Hno|]. split.
    * refine (proj2 (al_client_img _ _ LAWS ly S W mx md a HAR _)). right; left. exists cid, pos.
      split; [exact Hin | lia].
    * exact (in_app_addr _ _ a Happ ltac:(lia)).
  + destruct Happ as [Hh Hh2]. zlia.
  + exact (fsw_afobj_hull B ly S W mx md cid pos v 56 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_blocks _ _ LAWS ly S W mx md b n HAR Hin) as (_ & H4096 & Hc & Happ & Hb & _).
  split; [|split].
  + intros a Ha. destruct (Hb a ltac:(unfold HEAD in *; lia)) as [Hp Hno]. split; [exact Hp|]. split; [exact Hno|].
    split.
    * refine (proj2 (al_client_img _ _ LAWS ly S W mx md a HAR _)). left. exists b, n.
      split; [exact Hin | unfold HEAD in *; lia].
    * exact (in_app_addr _ _ a Happ ltac:(unfold HEAD in *; lia)).
  + exact (amem_range_of_block tfibsegs B LAWS ly S W mx md b n v 56 HAR Hin ltac:(unfold HEAD in *; lia) H2).
  + exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W mx md b n v 56 HAR Hin ltac:(unfold HEAD in *; lia) H2
      ltac:(lia)).
Qed.
(* an application byte is no user-poisoned shadow byte *)
Lemma pjo_unpoison_app : forall ly S Uh (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S Uh W mem md -> app_addr a -> unpoison Uh mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S Uh W mem md a HARU Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Ha as [Ha0 [Hl | [Hh1 Hh2]]].
- apply (ARU_mem_low tfibsegs B ly S Uh W mem md (Z_to_bv 64 a) HARU).
  rewrite (wz a ltac:(unfold kLowShadowBeg in Hl; lia)). unfold kLowShadowBeg, SHADOW_OFF in *. lia.
- apply (fsw_unpoison_high B ly S Uh W mem md a HARU). unfold ASAN_CEIL in Hh2. lia.
Qed.
Lemma pjo_apresent_app : forall ly S Uh (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S Uh W mem md -> app_addr a -> apresent (w_H W) (unpoison Uh mem) a -> apresent (w_H W) mem a.
Proof.
intros ly S Uh W mem md a HARU Ha [Hh [b Hb]]. rewrite (pjo_unpoison_app ly S Uh W mem md a HARU Ha) in Hb.
split; [exact Hh | exists b; exact Hb].
Qed.
(* the shadow hull, from the AR memory to the machine's (a user-poisoned shadow byte reads 0xf7, visible) *)
Lemma pjo_hull_raw : forall (W : world tfibsegs) Uh mem mem' x n, upoisoned tfibsegs W mem Uh ->
  same_below mem mem' alloc_ceiling -> 0 <= x -> x + n <= alloc_ceiling -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison Uh mem)) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem') x n.
Proof.
intros W Uh mem mem' x n HP Hs Hx Hn Hn0 Hh s Hsr.
pose proof asan_consts as (C1 & _).
assert (Hs0 : 0 <= s < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF in Hsr; Z.div_mod_to_equations; lia).
rewrite (aview_below (w_H W) mem mem' alloc_ceiling s Hs Hs0).
destruct (in_ush Uh (bv_unsigned (Z_to_bv 64 s))) eqn:Ei.
- rewrite (wz s ltac:(lia)) in Ei. rewrite (HP s Ei). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) Uh mem s Ei). exact (Hh s Hsr).
Qed.
(* fs_glob reads only image cells *)
Lemma pjo_glob_keep : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall a v, (forall k, 0 <= k < 8 -> in_img tfibsegs (a + k)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Hi Hv k Hk8. rewrite (Hk (a + Z.of_nat k) (Hi (Z.of_nat k) ltac:(lia))). exact (Hv k Hk8). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [intros k Hk8; apply (pjo_seg_cover G_LIVE 8 ltac:(vm_compute; reflexivity)); lia | exact G1]|].
split; [apply VB; [intros k Hk8; apply (pjo_seg_cover G_PEAK 8 ltac:(vm_compute; reflexivity)); lia | exact G2]|].
split; [apply VB; [intros k Hk8; apply (pjo_seg_cover G_COUNT 8 ltac:(vm_compute; reflexivity)); lia | exact G3]|].
split; [apply VB; [intros k Hk8; apply (pjo_seg_cover G_FAIL 8 ltac:(vm_compute; reflexivity)); lia | exact G4]|].
exact R.
Qed.

(* ---- the resume state after __asan_memset, on the contract's post ---- *)
Lemma pjo_resume_ok : forall ly S Uh (W : world tfibsegs) regs regs2 mem2 md2 v,
  ARU tfibsegs B ly S Uh W mem2 md2 ->
  spZ regs2 = spZ regs - 32 -> spZ regs mod 16 = 0 -> alloc_ceiling + 4128 <= spZ regs -> spZ regs <= 2 ^ 47 ->
  YK11.getr regs2 9 = Z_to_bv 64 SHADOW_OFF -> YK11.getr regs2 8 = w64 v ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 ->
  (forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
  (forall a, v <= a < v + 4 -> apresent (w_H W) mem2 a /\ ~ in_img tfibsegs a) ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pjo_xs regs)) pjo_ret
    (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 0x83f48) mem2 (YK11.seg_rom tfibsegs))).
Proof.
intros ly S Uh W regs regs2 mem2 md2 v HARU Hsp2 Hal Hceil H47 Hs1 Hs0 Hv0 Hv1 Hv8 Hpres Vra Vs0 Vs1 Hvp.
pose proof HSS as [Hgot Hcell].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HARU as (HAR2 & _ & _).
destruct (fsw_got_shadow B ly S W (unpoison Uh mem2) md2 Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison Uh mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S Uh W mem2 md2 (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v', 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison Uh mem2)) a 8 v' -> val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 v').
{ intros a v' Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison Uh mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison Uh mem2) _ _ Kcell)]. }
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ pjo_xs regs) 2 2%bv eq_refl); exact Hsp2).
assert (E32 : ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (E8 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 8) = v)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ pjo_xs regs) 8 8%bv eq_refl), Hs0; unfold w64; apply wz; lia).
(* the .got word and the cell are image bytes, v's four bytes are not *)
assert (Dgot : v + 4 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/
               tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= v).
{ destruct (Z.le_gt_cases (v + 4) tfib_D_GOT_asan_shadow_memory_dynamic_address) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) v) as [H'|H']; [right; exact H'|].
  exfalso. apply (proj2 (Hvp (Z.max v tfib_D_GOT_asan_shadow_memory_dynamic_address) ltac:(lia))).
  apply (pjo_seg_cover tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)). lia. }
assert (Dcell : v + 4 <= tfib_D_asan_shadow_memory_dynamic_address \/
                tfib_D_asan_shadow_memory_dynamic_address + 8 <= v).
{ destruct (Z.le_gt_cases (v + 4) tfib_D_asan_shadow_memory_dynamic_address) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (tfib_D_asan_shadow_memory_dynamic_address + 8) v) as [H'|H']; [right; exact H'|].
  exfalso. apply (proj2 (Hvp (Z.max v tfib_D_asan_shadow_memory_dynamic_address) ltac:(lia))).
  apply (pjo_seg_cover tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)). lia. }
rewrite restrict_mkst_fx. unfold pjo_ret, fsT_ret_regions. cbn [app]. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |].
  rewrite fsw_SOff0, E32. exact Hs1.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + (* the frame, its three saved registers *)
    unfold region_ok, fstk_ret, pjo_cs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    * constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 33 0) (raZ regs)).
         ++ rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth app fs_extraT pjo_xs].
            unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
         ++ unfold raZ. apply u64_range.
         ++ cbn; lia.
         ++ replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact Vra.
      -- apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff 34 0) (s0Z regs)).
         ++ rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth app fs_extraT pjo_xs].
            unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
         ++ unfold s0Z. apply u64_range.
         ++ cbn; lia.
         ++ replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact Vs0.
      -- apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 35 0) (bv_unsigned (YK11.getr regs 9))).
         ++ rewrite fsw_SOff0. change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra. cbn [nth app fs_extraT pjo_xs].
            symmetry. apply Z_to_bv_bv_unsigned.
         ++ apply u64_range.
         ++ cbn; lia.
         ++ replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact Vs1.
  + (* the .got word of the shadow base, as fsw_entryT *)
    unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + (* the shadow-base cell, as fsw_entryT *)
    unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
  + (* the store window [v, v + 4) *)
    unfold region_ok, pjo_vreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable tfibsegs). refine (proj1 (Hvp _ _)). lia.
- apply pairwise_disjoint_of_extents.
  unfold fstk_ret, fs_got_region, fs_bcell_region, pjo_vreg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, U32, E8. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r.
  split; [split; [lia | split; [rewrite Zminus_mod, Hal; reflexivity | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [|exact I]. split; [unfold PJO_CEIL; lia | split; [exact Hv8 | lia]].
Qed.

(* ---- the walk ---- *)
Lemma pjo_walk : forall ly S Uh W regs mem md ch v live peak cnt fail,
  fpreU tfibsegs B STK_pj_object ly S Uh W regs mem md ch ->
  YK11.getr regs 10 = w64 v ->
  pobj tfibsegs B ly S W mem v ->
  (forall a, v <= a < v + 56 ->
     awr_byte tfibsegs B STK_pj_object (spZ regs) [(v, v + 56)] (ablocks B ly S) (ablocks B ly S) ly [] (frames S) a) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_object regs mem md)
    (fpostU tfibsegs B STK_pj_object (spZ regs) [(v, v + 56)] regs ly S Uh W mem md 0 Uh
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj []) [] /\ pobj tfibsegs B ly' S' W' mem' v /\
          fs_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
intros ly S Uh W regs mem md ch v live peak cnt fail HPRE H10 HPO HWV Hglob.
pose proof HSS as [Hgot Hcell].
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (FS : STK_pj_object = ltac:(let v := eval vm_compute in (STK_pj_object) in exact v)) by (vm_compute; reflexivity).
destruct HPRE as [HAPU _].
pose proof (fsw_sp B _ ly S Uh W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
rewrite FS in Hceil.
pose proof HAPU as (HAP & HOK & HPOI).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S Uh W regs mem md ch HAPU) as HARU.
destruct (fsw_pobj_low B ly S W (unpoison Uh mem) md mem v HAR HPO) as (Hv0 & Hv1).
destruct (pjo_place ly S W (unpoison Uh mem) md mem v HAR HPO) as (HPL & HAMR & HHULL0).
pose proof HPO as [HPL0 HWR0].
assert (Hv8 : v mod 8 = 0) by (destruct HPL0 as [(_ & H & _)|(_ & H & _)]; exact H).
assert (HRA0 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56)
  by (destruct HPL0 as [(_ & _ & H)|(_ & _ & H)]; exact H).
(* every byte of v is an application byte, so its shadow byte is neither in v nor in a stack window *)
assert (HSHO : forall x y, v <= x < v + 56 -> v <= y < v + 56 -> shadow_of_addr SHADOW_OFF x <> y /\
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg).
{ intros x y Hx Hy. destruct (HPL x Hx) as (_ & _ & _ & Hax). destruct (HPL y Hy) as (_ & _ & _ & Hay).
  unfold shadow_of_addr. appn. unfold SHADOW_OFF. Z.div_mod_to_equations. lia. }
(* ---- the entry state and the journal ---- *)
pose proof (fsw_entryT B STK_pj_object 32 ly S Uh W regs mem md ch A_pj_object Hgot Hcell HAPU
  ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_pj_object [(v, v + 56)] ly S W regs (unpoison Uh mem) md ch HAP) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold YG0d.cfg_at. change (w64 A_pj_object) with (Z_to_bv 64 A_pj_object).
(* ---- run 1: 0x83f1c .. `jal __asan_memset` 0x83f44, stopping at the callee's entry 0x5222c (PC_memset) ---- *)
fsw_aj_run_toU pj_object_tbl_ok HS HJ HARU PC_memset.
{ cbn [ss_mem fss0T fsT_regions].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | rewrite FS; cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HS into HSc.
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ apply (pjo_same_below_wr (Ereg regs fs_extraT) _ mem (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjo_wr1 _ a (spZ regs) Usp Ha). lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x83f48 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ _ _ ms 2%bv 2 (-32) (spZ regs) HSc ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 10%bv 10 HSc ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms 9%bv 0 HSc ltac:(vm_compute; reflexivity)) as R9.
cbn [nth fs_extraT] in R9.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 10%bv 10%bv 10 HSc ltac:(vm_compute; reflexivity) eq_refl) as R10.
rewrite H10 in R8, R10.
pose proof (fsw_reg_lit _ _ _ ms 11%bv 0 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ _ _ ms 12%bv 56 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
assert (HspC : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; lia).
(* the three saved registers in the frame *)
pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 1 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)) as Vs0.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0)
  (bv_unsigned (YK11.getr regs 9)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(apply u64_range) ltac:(cbn; lia)) as Vs1.
clear HR0.
(* ---- the call of __asan_memset (v, 0, 56) ---- *)
pose proof (fsw_ecall_preU_at B STK_pj_object (spZ regs) [(v, v + 56)] ly S W (unpoison Uh mem) md [] ly S Uh W
  (ms_mem ms) _ 0 (ms_regs ms) (-32) HJ HARU ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite FS, Hes; lia)
  ltac:(rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)) as HPREc.
assert (HDEST : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) v 56).
{ intros a Ha. split; [|split].
  - replace a with (v + (a - v)) by lia.
    apply (fsw_writable_below (w_H W) mem (ms_mem ms) (v + (a - v)) SB1); [lia|].
    apply HWR0. lia.
  - exact (proj1 (proj2 (HPL a Ha))).
  - rewrite HspC, Hes. lia. }
pose proof (fsw_range_addressable_below (w_H W) mem (ms_mem ms) v 56 SB1 ltac:(lia) Hv1 HRA0) as HRAD.
pose proof (pjo_hull_raw W Uh mem (ms_mem ms) v 56 HPOI SB1 ltac:(lia) Hv1 ltac:(lia) HHULL0) as HHULL.
set (Wr := fun a => v <= a < v + 56 \/ spZ regs - 32 - 4096 <= a < spZ regs - 32).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_pj_object (spZ regs) [(v, v + 56)] ly S W (unpoison Uh mem) md [] ly S Uh W
    (ms_mem ms) _ 0 Uh Wr (Z_to_bv 64 0x83f48) _
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
       (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem' (v + i) = Some (0 mod 256)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a))
    HJ).
  - eapply SRr_mono; [exact (fs_memset_realizesU ly S Uh W (ms_regs ms) (ms_mem ms) _ v 0 56 HPREc R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) HDEST HAMR HRAD (fun _ => HHULL) I)|].
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & Hres & Hbytes & Hfr & Hpr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold YG0d.cfg_at, raZ; rewrite R1, unsigned_lit_small by lia; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
      aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a).
    { intros a Ha HWa. apply Hfr; [exact Ha | intros H'; apply HWa; left; exact H' |].
      rewrite HspC, Hes. intros H'; apply HWa; right; lia. }
    split.
    { intros a Ha HWa. destruct (in_ush Uh (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      - apply (aview_unpoison_in tfibsegs). exact Ei.
      - rewrite !(aview_unpoison_out tfibsegs) by exact Ei. exact (Hfr' a Ha HWa). }
    split; [intros a; apply (pjo_apresent_unpoison Uh (w_H W) (ms_mem ms) mem' a); exact (Hpr a)|].
    split; [exact HP'|]. split; [exact Hbytes | exact Hfr'].
  - intros a [Ha | Ha]; [exact (HWV a Ha)|]. left. left. rewrite FS. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hz2 & Hfr2).
(* ---- back at 0x83f48: the resume state ---- *)
assert (P2 : YK11.getr regs2 2 = YK11.getr (ms_regs ms) 2) by exact (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
assert (P8 : YK11.getr regs2 8 = YK11.getr (ms_regs ms) 8) by exact (fsw_pres _ _ 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
assert (P9 : YK11.getr regs2 9 = YK11.getr (ms_regs ms) 9) by exact (fsw_pres _ _ 9%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
assert (Hsp2 : spZ regs2 = spZ regs - 32) by (unfold spZ at 1; rewrite P2; exact HspC).
assert (KS : forall a, spZ regs - 32 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. unfold Wr. lia. }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HP2s : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem2 a).
{ intros a Ha. apply (fsw_apresent_unpoison B ly S Uh W mem2 md2 a HARU2); [lia|]. apply Hpres2. rewrite FS. lia. }
assert (HPv2 : forall a, v <= a < v + 56 -> apresent (w_H W) mem2 a).
{ intros a Ha. destruct (pjo_place ly S W (unpoison Uh mem2) md2 mem v HAR2 HPO) as (HPL2 & _ & _).
  destruct (HPL2 a Ha) as (Hp & _ & _ & Hap). exact (pjo_apresent_app ly S Uh W mem2 md2 a HARU2 Hap Hp). }
pose proof (pjo_resume_ok ly S Uh W regs regs2 mem2 md2 v HARU2 Hsp2 Hal16 Hceil H47
  ltac:(rewrite P9; exact R9) ltac:(rewrite P8; exact R8) ltac:(lia) Hv1 Hv8 HP2s
  ltac:(apply (pjo_val_keep (mrestrict (w_H W) (ms_mem ms))); [intros k Hk; apply KS; lia
        | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Vra])
  ltac:(apply (pjo_val_keep (mrestrict (w_H W) (ms_mem ms))); [intros k Hk; apply KS; lia
        | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact Vs0])
  ltac:(apply (pjo_val_keep (mrestrict (w_H W) (ms_mem ms))); [intros k Hk; apply KS; lia
        | replace (spZ regs - 24) with (spZ regs + -24) by lia; exact Vs1])
  ltac:(intros a Ha; split; [apply HPv2; lia | exact (proj1 (proj2 (proj2 (HPL a ltac:(lia)))))])) as HS2.
assert (E8' : ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 8 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (U8 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 8) = v) by (rewrite E8'; apply wz; lia).
assert (E32' : ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E2sp : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Hsp2).
(* v's shadow after __asan_memset: unchanged (not in v, not in the stack window) *)
assert (HRA2 : range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF v 56).
{ intros x Hx. destruct (HRAD x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
  destruct (HSHO x x Hx Hx) as (_ & Hs).
  rewrite Hfr2; [exact Es | unfold SHADOW_OFF in *; lia |].
  unfold Wr. intros [Hw | Hw]; [exact (proj1 (HSHO x _ Hx Hw) eq_refl) | lia]. }
assert (SHOK : sh_ok tfibsegs fs_Bx pjo_SH (Ereg regs2 (fs_extraT ++ pjo_xs regs)) (mrestrict (w_H W) mem2)).
{ unfold pjo_SH, sh_ok. constructor; [|constructor]. unfold shent_ok, app_apart, fs_Bx. cbn [she_m she_lo she_hi].
  rewrite (U_atom _ 32 SHADOW_OFF E32' ltac:(unfold SHADOW_OFF; lia)), (U_atom _ 8 v E8' ltac:(lia)).
  split.
  - change (rd_of tfibsegs (mrestrict (w_H W) mem2)) with (aview tfibsegs (w_H W) mem2).
    rewrite Z.add_0_r, Z.sub_0_r. exact HRA2.
  - change (Z.min 0 56) with 0. change (Z.max 0 56) with 56. intros a Ha.
    destruct (HPL a ltac:(lia)) as (_ & _ & _ & Hap). appn. unfold SHADOW_OFF. lia. }
(* ---- run 2 (token engine): 0x83f48 .. the `ret` 0x83f7c ----
   The UBSan checks of the store `sw a0,0(s0)` (pf.c:435) run first, on s0 = atom 8 = v, whose fact is
   mkAF 4096 PJO_CEIL 3 (pjo_ret; discharged in pjo_resume_ok from pobj through fsw_pobj_low and pobj's v mod 8 = 0):
   - 0x83f48 `beqz s0,0x83f80` (the null check, to the trap `unimp` 0x83f80): ruled out by pobj (fsw_pobj_low:
     4096 <= v); the engine decides it by YP0m.decide_eq, atom 8's range [4096, PJO_CEIL] is disjoint from 0;
   - 0x83f4c `andi a0,s0,7` / 0x83f50 `bnez a0,0x83f80` (the alignment check, to the same trap): ruled out by pobj
     (v mod 8 = 0, both arms of pobj); the engine folds the andi to 0 by YP0m.s_and_ptr (af_al2 = 3), so the bnez is
     not taken;
   - 0x83f60 `bnez a1,0x83f84` (the ASan shadow check, to the slow check and `jal __asan_report_store4` 0x83f90): ruled
     out by pobj's range_addressable through the shent pjo_SH (SHOK below), as in image A. *)
lazymatch goal with |- _ =>
  let r := eval vm_compute in (sym_runN_tok tfibsegs pj_object_tbl 36 fs_Bx fs_Bspan pjo_SH FUEL pjo_ret) in
  lazymatch r with (?st', ?rs) =>
    assert (Hrun : sym_runN_tok tfibsegs pj_object_tbl 36 fs_Bx fs_Bspan pjo_SH FUEL pjo_ret = (st', rs))
      by (vm_compute; reflexivity)
  end
end.
eapply (fsw_run_tok_AJU B pj_object_tbl pj_object_tbl_ok W FUEL (Ereg regs2 (fs_extraT ++ pjo_xs regs)) 36 fs_Bx
  fs_Bspan pjo_SH pjo_ret _ _ (YK11.mkst regs2 (Z_to_bv 64 0x83f48) mem2 (YK11.seg_rom tfibsegs))
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS2 SHOK ltac:(vm_compute; reflexivity) Hrun I HARU2 HJ2).
{ cbn [sh_obls]. apply Forall_nil. }
{ intros a Ha. destruct (pjo_wr2 _ a (spZ regs - 32) v E2sp U8 Ha) as [Hs | Hv].
  - left. left. rewrite FS. lia.
  - exact (HWV a ltac:(lia)). }
intros ws msf matf Hlen HSf SHOKf HJf HARUf HFf HFrf HGf.
cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|discriminate Hlen]. cbn [extK sh_ss] in HSf, SHOKf.
cbn [ms_mem YK11.mkst] in HFrf, HFf, HGf.
pose proof (fsw_reg_extra _ regs2 (fs_extraT ++ pjo_xs regs) _ msf 1%bv 1 HSf ltac:(vm_compute; reflexivity)) as R1F.
cbn [nth app fs_extraT pjo_xs] in R1F.
(* the final memory: v's bytes, v present, v's shadow and the image cells kept *)
pose proof HJf as (HARf & _).
assert (HPvf : forall a, v <= a < v + 56 -> apresent (w_H W) (ms_mem msf) a).
{ intros a Ha. destruct (pjo_place ly S W _ _ mem v HARf HPO) as (HPLf & _ & _).
  destruct (HPLf a Ha) as (Hp & _ & _ & Hap). exact (pjo_apresent_app ly S Uh W _ _ a HARUf Hap Hp). }
pose proof (fsw_region_nth _ _ _ 3 _ HSf eq_refl) as HR3. cbn [ms_mem restrict] in HR3.
pose proof (fsw_field (Ereg regs2 (fs_extraT ++ pjo_xs regs)) _ 8 v _ _ _ _ _ 0 4%N (SLit 6) 6 HR3 U8
  ltac:(cbn; tauto) ltac:(reflexivity) ltac:(lia) ltac:(cbn; lia)) as V6.
assert (Hbf : forall i, 0 <= i < 56 ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + i) = Some (Z_to_bv 8 (if i =? 0 then 6 else 0))).
{ intros i Hi. destruct (Z.lt_ge_cases i 4) as [Hl | Hg].
  - assert (Hcase : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hcase as [-> | [-> | [-> | ->]]].
    + pose proof (V6 0%nat ltac:(cbn; lia)) as Hk. replace (v + 0 + Z.of_nat 0) with (v + 0) in Hk by lia. exact Hk.
    + pose proof (V6 1%nat ltac:(cbn; lia)) as Hk. replace (v + 0 + Z.of_nat 1) with (v + 1) in Hk by lia. exact Hk.
    + pose proof (V6 2%nat ltac:(cbn; lia)) as Hk. replace (v + 0 + Z.of_nat 2) with (v + 2) in Hk by lia. exact Hk.
    + pose proof (V6 3%nat ltac:(cbn; lia)) as Hk. replace (v + 0 + Z.of_nat 3) with (v + 3) in Hk by lia. exact Hk.
  - replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (pjo_frame_mbyte _ _ _ _ _ (v + i) HFrf ltac:(lia)).
    + exact (pjo_mbyte_of_aview (w_H W) mem2 (v + i) 0 (Hz2 i Hi)).
    + intros Hin. destruct (pjo_wr2 _ _ (spZ regs - 32) v E2sp U8 Hin); lia. }
assert (HRAf : range_addressable (aview tfibsegs (w_H W) (ms_mem msf)) SHADOW_OFF v 56).
{ intros x Hx. destruct (HRA2 x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
  destruct (HSHO x x Hx Hx) as (_ & Hs).
  rewrite (pjo_frame_aview _ _ _ _ _ _ HFrf); [exact Es | unfold SHADOW_OFF in *; lia |].
  intros Hin. destruct (pjo_wr2 _ _ (spZ regs - 32) v E2sp U8 Hin) as [Hw | Hw]; [lia|].
  exact (proj1 (HSHO x (shadow_of_addr SHADOW_OFF x) Hx ltac:(lia)) eq_refl). }
assert (Hglobf : fs_glob tfibsegs W (ms_mem msf) live peak cnt fail).
{ apply (pjo_glob_keep W mem2).
  - intros a Ha. pose proof (fs_segs_img a Ha) as Hi. unfold FS_IMG_END in Hi.
    apply (pjo_frame_mbyte _ _ _ _ _ _ HFrf); [lia|].
    intros Hin. destruct (pjo_wr2 _ _ (spZ regs - 32) v E2sp U8 Hin) as [Hw | Hw]; [lia|].
    exact (proj1 (proj2 (proj2 (HPL a ltac:(lia)))) Ha).
  - apply (pjo_glob_keep W (ms_mem ms)).
    + intros a Ha. pose proof (fs_segs_img a Ha) as Hi. unfold FS_IMG_END in Hi.
      apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. unfold Wr. intros [Hw | Hw]; [|lia].
      exact (proj1 (proj2 (proj2 (HPL a Hw))) Ha).
    + exact (fs_glob_below W mem (ms_mem ms) live peak cnt fail SB1 Hglob). }
(* ---- the return ---- *)
eapply (fsw_retU B pj_object_tbl pj_object_tbl_ok W (Ereg regs2 (fs_extraT ++ pjo_xs regs)) _ msf _ STK_pj_object
  (spZ regs) [(v, v + 56)] regs ly S Uh W mem md ly S Uh 0 _ HSf eq_refl ltac:(vm_compute; reflexivity)
  ltac:(rewrite R1F; exact Hra) HJf HARUf).
- apply (fsw_preserved _ _ _ msf regs pjo_expect HSf); [vm_compute; reflexivity|].
  fsw_cs_cases pjo_expect HSc HP2 E2sp.
- intros matq. cbv beta. split; [reflexivity|]. split; [|split].
  + split; [|split; [intros a k Hin; destruct Hin | intros x Hx; exact Hx]].
    apply pjo_node_ok; [lia | lia | exact Hv8 | | exact Hbf].
    intros a Ha. apply (apresent_writable tfibsegs). exact (HPvf a Ha).
  + split.
    * destruct HPL0 as [(Hf & Ha & _)|(Hb & Ha & _)]; [left | right];
        (split; [assumption|]; split; [exact Ha | exact HRAf]).
    * intros i Hi. apply (apresent_writable tfibsegs). apply HPvf. lia.
  + exact Hglobf.
Qed.

(* ---- pj_object_spec: both arms of pobj through the core's awr_byte (the heap arm its FP-and-block arm, the
   fake-frame arm its fake-frame arm over frames S) ---- *)
Theorem pj_object_holds : @pj_object_spec fx rc SK tfibsegs B.
Proof.
intros ly S Uh W regs mem md ch v live peak cnt fail HPRE _ H10 HPO _ Hglob.
apply (pjo_walk ly S Uh W regs mem md ch v live peak cnt fail HPRE H10 HPO); [|exact Hglob].
pose proof HPO as [[((cid & pos & Hin & Hc & Hal & H1 & H2) & _ & _) | ((b & n & Hin & H1 & H2) & _ & _)] _].
- intros a Ha. right; right. split; [apply inFP_cons; left; lia|].
  exists cid, pos. split; [exact Hin | unfold in_zr, frame_rng; cbn; lia].
- intros a Ha. left. right; left. split; [apply inFP_cons; left; lia|].
  exists b, n. split; [exact Hin | unfold HEAD in *; lia].
Qed.
End W.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value ENTRY segment (C0): the INVARIANT TRANSPORT the segment lemma
   exvB_entry (lib/B/Prog/ExvB_Entry.v, ExvEntry) cites to move EXV_PRE's facts from the entry state to the C1 cut
   (after frame_alloc_1, the frame stores and the ex_ws call). Pure transport: no symbolic run, no engine file.
   - exve_in_ro_img / exve_rodata_keep: arodata_okP over the image's read-only bytes (a read-only segment's byte is in
     the image by in_img's definition, a relro byte by PAImg_prog.v's B_prog_relro), kept when every image byte outside
     the runtime-owned statics and errno keeps its value.
   - exve_lam_blk: a Lam block's allocator block (prh_hblock) and the user range inside its req_size range.
   - exve_ledger_keep: the ledger across a non-allocator change of state. THIS IS PRH_Keep's shape (the
     prh_ledger_keep / prh_ledger_keep_av, lib/A/PRH_Keep.v on a Theorem Labs lane's branch, not on this base, so
     restated here): the statics prh_pst and every harness head [a - cf_head, a - cf_head + 8) (inside its block, as
     8 <= cf_head) keep their values, the blocks stay live, Hp is unchanged.
   - exve_achain_call: the frame chain at ex_value's call of ex_ws (s0 = the entry sp), YCbq.v's achain_push when the
     entry sp is below ly_top - 16, else achain's empty arm.
   - exve_val_kept / exve_garr8_kept: ex_ws_x.v's exw_val_kept / exw_garr8_kept (cold/h-rw-pre-7-b-ex_ws) restated
     over two worlds; the proofs are the same (YCbq.v mbyte_of_aview). (ex_ws_x.v's exw_ra_kept is not restated:
     ExvB_Open_kt.v exv_ra_keep is its two-reader form.)
   - exve_src_rd_kept / exve_cur_kept: src_rd and prhex_cur from kept bytes (the shadow facts of src_rd at the new
     state are premises: ExvB_Open_sh.v exv_sh_blk gives them).
   - exve_wdest_of_blk: wdest_ok at STK = 0 for a range inside a live block (alx_blocks: present, not runtime-owned,
     below alloc_ceiling; YCbq.v apresent_writable).
   - exve_tree_kept: prhex_tree at a new state, PRH_Reader.v's pj_nodeR_frame over pj_footR (pj_agreeR's mbyte equality
     from YCbq.v mbyte_of_aview). The tree's blocks are Lam blocks: ExvB_Open_kt.v exv_node_D, not restated.
   - exve_writ_keep: off the image a writable byte stays writable when its view is kept. The argument is YCbq.v's
     apresent_transfer (seg_rom is None off the image, so mbyte is the restricted memory itself and writable_at reads
     the same option), stated here for writable_at; apresent_transfer itself is about apresent. It carries
     apresent_transfer's premise 0 <= a < 2 ^ 64 (agreed with ExvEntry: without it the wrapped address of an a >= 2 ^ 64
     can lie in a read-only segment, where writable_at is false).
   Rule 24: proves no function (kind: segment lemma). Numerals: 8, 16 (LENGTH: a harness head's size word, a frame
   record's ra / s0 slots), 36 (LENGTH: the cursor cells of struct ex read by prhex_cur), 56 (LENGTH: tree node), 4, 1
   (LENGTH: cell widths), 0 (LENGTH: STK of wdest_ok), 2 ^ 64 (LENGTH: address-space bound), 4096 (LENGTH: the low
   page). No ADDRESS, no WORD, no DERIVED: the file names no image address (B_prog_relro_lo / _hi are PAImg_prog.v's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section K. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.

(* 1. a read-only byte of the image (a read-only segment, or B's relro band) is an image byte *)
Lemma exve_in_ro_img : forall a, in_roP rsegs B_prog_relro_lo B_prog_relro_hi a -> in_img rsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- hnf. exists s. split; [exact Hs | exact Hr].
- exact (B_prog_relro a Hr).
Qed.

(* 2. the read-only image bytes, kept *)
Lemma exve_rodata_keep : forall (W W' : world rsegs) mem mem',
  (forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
  arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview rsegs (w_H W) mem) ->
  arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview rsegs (w_H W') mem').
Proof.
intros W W' mem mem' HK HR a Hro Ho He.
rewrite (HK a (exve_in_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
Qed.

(* 3. a Lam block: its allocator block is live and its user range lies in the block's req_size range *)
Lemma exve_lam_blk : forall ly S Hp (W : world rsegs) mem Lam peak cnt fail ran most own a k, 8 <= cf_head ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  In (a - cf_head, k + cf_head) (ablocks B ly S) /\ 0 <= k /\
  (forall x, a - cf_head <= x < a + k -> a - cf_head <= x < a - cf_head + req_size (k + cf_head)).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k Hh (_ & _ & HB & _) Hin.
rewrite Forall_forall in HB. destruct (HB (a, k) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
split; [exact Hblk|]. split; [exact Hk0|].
intros x Hx. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* 6. (ex_ws_x.v exw_val_kept over two worlds) a value kept byte for byte *)
Lemma exve_val_kept : forall (W W' : world rsegs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs (w_H W') mem' x = aview rsegs (w_H W) mem x) ->
  val_mem rsegs (mrestrict (w_H W) mem) a n v -> val_mem rsegs (mrestrict (w_H W') mem') a n v.
Proof.
intros W W' mem mem' a n v HE Hv kk Hk.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W') mem mem' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

(* 7. (ex_ws_x.v exw_garr8_kept over two worlds) a byte array kept byte for byte *)
Lemma exve_garr8_kept : forall (W W' : world rsegs) mem mem' p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
  garr8 rsegs (mrestrict (w_H W) mem) p L -> garr8 rsegs (mrestrict (w_H W') mem') p L.
Proof.
intros W W' mem mem' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W') mem mem' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

(* 4. the ledger across a non-allocator change (PRH_Keep's prh_ledger_keep_av shape): statics and harness heads kept,
   blocks still live, Hp unchanged *)
Lemma exve_ledger_keep : forall ly S Hp (W : world rsegs) mem md ly' S' Hp' (W' : world rsegs) mem' Lam peak cnt fail ran most own,
  8 <= cf_head -> ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  incl (ablocks B ly S) (ablocks B ly' S') -> Hp' = Hp ->
  (forall a, Exists (in_zr a) prh_pst -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
  (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
     aview rsegs (w_H W') mem' (b + i) = aview rsegs (w_H W) mem (b + i)) ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' Lam peak cnt fail ran most own Hh _
  ((G1 & G2 & G3 & G4 & G5 & (GM & GMr) & (GO & GOr) & GR) & HND & HF & HP) Hinc -> Hst Hblk.
assert (VS : forall b w v, In (b, Z.of_nat w) prh_pst ->
  val_mem rsegs (mrestrict (w_H W) mem) b w v -> val_mem rsegs (mrestrict (w_H W') mem') b w v).
{ intros b w v Hin Hv. apply (exve_val_kept W W' mem mem' b w v); [|exact Hv].
  intros x Hx. apply Hst. apply Exists_exists. exists (b, Z.of_nat w).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
unfold prh_ledger, prh_glob.
split; [|split; [exact HND | split; [| exact HP]]].
- split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G1]|].
  split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G2]|].
  split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G3]|].
  split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G4]|].
  split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G5]|].
  split; [split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact GM] | exact GMr]|].
  split; [split; [apply VS; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact GO] | exact GOr]|].
  exact GR.
- apply Forall_forall. intros [a k] Hak.
  pose proof (proj1 (Forall_forall _ _) HF (a, k) Hak) as (K0 & K1 & K2 & K3 & K4). cbn [fst snd] in *.
  split; [exact K0|]. split; [exact (Hinc _ K1)|]. split; [exact K2|]. split; [exact K3|].
  apply (exve_val_kept W W' mem mem' (a - cf_head) 8 k); [|exact K4].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (Hblk (a - cf_head) (k + cf_head) (x - (a - cf_head)) K1).
  unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* 5. the frame chain at ex_value's call of ex_ws: s0 = the entry sp, its record (ra, s0) stored below it *)
Lemma exve_achain_call : forall ly (W W' : world rsegs) mem mem' (regs : bvmap 5 word) ch (sp1 : Z),
  achain ly (aview rsegs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> spZ regs <= ly_top ly -> ly_top ly <= 2 ^ 64 ->
  4096 <= raZ regs ->
  (forall a, spZ regs <= a < 2 ^ 64 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
  rdword (aview rsegs (w_H W') mem') (spZ regs - 8) = Some (raZ regs) ->
  rdword (aview rsegs (w_H W') mem') (spZ regs - 16) = Some (s0Z regs) ->
  sp1 + 16 <= spZ regs ->
  exists ch1, achain ly (aview rsegs (w_H W') mem') sp1 (spZ regs) ch1.
Proof.
intros ly W W' mem mem' regs ch sp1 Hc Hceil Hal _ Htop64 Hra HK H8 H16 Hsp1.
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) ch sp1 Hc Htop64 HK H8 H16 Hra Hceil Hal Hlt Hsp1).
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* 9. a read window from kept bytes, its shadow facts at the new state given *)
Lemma exve_src_rd_kept : forall (W W' : world rsegs) mem mem' p l,
  (forall x, p <= x < p + Z.of_nat (length l) -> aview rsegs (w_H W') mem' x = aview rsegs (w_H W) mem x) ->
  range_addressable (aview rsegs (w_H W') mem') SHADOW_OFF p (Z.of_nat (length l)) ->
  (0 < Z.of_nat (length l) -> shadow_hull_vis (aview rsegs (w_H W') mem') p (Z.of_nat (length l))) ->
  src_rd W mem p l -> src_rd W' mem' p l.
Proof.
intros W W' mem mem' p l HE HR HH (Hby & H4096 & Hce & Ham & _ & _).
split; [exact (exve_garr8_kept W W' mem mem' p l HE Hby)|].
split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|]. split; [exact HR | exact HH].
Qed.

(* 10. the cursor cells [q, q + 36) kept *)
Lemma exve_cur_kept : forall (W W' : world rsegs) mem mem' q p e dep scr dl,
  (forall x, q <= x < q + 36 -> aview rsegs (w_H W') mem' x = aview rsegs (w_H W) mem x) ->
  prhex_cur W mem q p e dep scr dl -> prhex_cur W' mem' q p e dep scr dl.
Proof.
intros W W' mem mem' q p e dep scr dl HE (C1 & C2 & C3 & C4 & C5).
split; [apply (exve_val_kept W W' mem mem' q 8 p); [|exact C1]|].
{ intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HE. lia. }
split; [apply (exve_val_kept W W' mem mem' (q + 8) 8 e); [|exact C2]|].
{ intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HE. lia. }
split; [apply (exve_val_kept W W' mem mem' (q + 16) 4 dep); [|exact C3]|].
{ intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply HE. lia. }
split; [apply (exve_val_kept W W' mem mem' (q + 24) 8 scr); [|exact C4]|].
{ intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HE. lia. }
apply (exve_val_kept W W' mem mem' (q + 32) 4 dl); [|exact C5].
intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply HE. lia.
Qed.

(* 11. a write destination inside a live block, at STK = 0 *)
Lemma exve_wdest_of_blk : forall ly S Hp (W : world rsegs) (regs : bvmap 5 word) mem md a n,
  ARx ly S Hp W mem md -> prhex_inblk B ly S Hp a n -> 0 <= n -> amem_range a n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n ->
  (0 < n -> shadow_hull_vis (aview rsegs (w_H W) mem) a n) ->
  wdest_ok B 0 ly S W regs mem a n.
Proof.
intros ly S Hp W regs mem md a n HAR (b & m & Hin & Hba & Ham & _) Hn Hamr HR HH.
destruct (alx_blocks rsegs B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hce & _ & Hpr & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [lia|]. split; [lia|]. split; [exact Hamr|]. split.
- intros x Hx. destruct (Hpr x ltac:(lia)) as (Hp' & Ho).
  split; [exact (apresent_writable rsegs (w_H W) mem x Hp')|]. split; [exact Ho|]. lia.
- split; [exact HR | exact HH].
Qed.

(* 13. a tree at a new state: its footprint's bytes kept and its writable bytes still writable *)
Lemma exve_tree_kept : forall lyc Sc Lam (W W' : world rsegs) (regs' : bvmap 5 word) mem mem' p t D,
  PRH_Reader.pj_nodeR rsegs (mrestrict (w_H W) mem) (prh_lin Lam) p t D ->
  (forall x, PRH_Reader.pj_footR p D x -> aview rsegs (w_H W') mem' x = aview rsegs (w_H W) mem x /\
     (writable_at rsegs (mrestrict (w_H W) mem) x -> writable_at rsegs (mrestrict (w_H W') mem') x)) ->
  prhex_home lyc Sc Lam regs' p 56 ->
  range_addressable (aview rsegs (w_H W') mem') SHADOW_OFF p 56 ->
  shadow_hull_vis (aview rsegs (w_H W') mem') p 56 ->
  prhex_tree lyc Sc Lam W' regs' mem' p t D.
Proof.
intros lyc Sc Lam W W' regs' mem mem' p t D Hnd HK Hhome HR HH.
split; [|split; [exact Hhome | split; [exact HR | exact HH]]].
apply (PRH_Reader.pj_nodeR_frame rsegs t (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') (prh_lin Lam) p D Hnd).
intros x Hx. destruct (HK x Hx) as (He & Hw).
split; [exact (mbyte_of_aview rsegs (w_H W) (w_H W') mem mem' x He) | exact Hw].
Qed.

(* 14. off the image a writable byte whose view is kept stays writable (YCbq.v apresent_transfer's argument) *)
Lemma exve_writ_keep : forall (W W' : world rsegs) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img rsegs a ->
  aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a ->
  writable_at rsegs (mrestrict (w_H W) mem) a -> writable_at rsegs (mrestrict (w_H W') mem') a.
Proof.
intros W W' mem mem' a Ha Hn E Hw.
apply (mbyte_of_aview rsegs) in E. unfold mbyte in E. rewrite (seg_rom_none rsegs a Ha Hn) in E.
unfold writable_at, wview in *.
destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) as [b'|] eqn:E1.
- intros Hc. discriminate Hc.
- destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|] eqn:E2.
  + discriminate E.
  + exact Hw.
Qed.
End K.

Print Assumptions exve_in_ro_img.
Print Assumptions exve_rodata_keep.
Print Assumptions exve_lam_blk.
Print Assumptions exve_ledger_keep.
Print Assumptions exve_achain_call.
Print Assumptions exve_val_kept.
Print Assumptions exve_garr8_kept.
Print Assumptions exve_src_rd_kept.
Print Assumptions exve_cur_kept.
Print Assumptions exve_wdest_of_blk.
Print Assumptions exve_tree_kept.
Print Assumptions exve_writ_keep.

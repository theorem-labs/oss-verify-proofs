(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 874 of its 1464 lines of code are new or changed and 341 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from fuzz_grant's lib/A/Prog/GrantEntrySeat.v (a working branch 51ce2ea10e0) for libreac/fuzz_boxreg A over BoxLxDefs.v: names ge_* -> gb_*, ecx -> bcx, GE_* -> GB_*; module paths fuzz_grant -> fuzz_boxreg, the Grant* imports -> boxreg's (BoxSyms BoxList BoxPa BoxPaLib BoxBase BoxFrame, YC4b for field_of_region); val_mem1_of_aview (grant's YC88.v) is copied here, as boxreg's A layer lacks it. The image numbers are boxreg A's: the side-stack frame is class 3 (512-byte slots, flag word at F + 504, 64 shadow bytes of which the function uses 52); the realigned stack pointer is sp1 = 32 * ((sp0 - 256) / 32), so sp0 - 288 < sp1 <= sp0 - 256; the spill area is [sp1, sp1 + 0x98); the shadow base's GOT word and cell are objects 1 and 12 (BoxPaLib.v PALib), the use-after-return flag's GOT word is object 0 (BoxFrame.v PALibF); the image range is Reusable/YImgTop.v's [IMG_LO, IMG_TOP). The use-after-return flag cell is not an image object that PALibF names (it states only its place in the image), so the cell has an atom of this walk, 530 (GB_UC), which gb_E pins to as_uar_cell B. BoxLxDefs.v's gregs also keeps s2 (the shadow offset) and s8 (the frame's shadow), and its gb_body carries the frame slots gslots_fr, so gb_land also takes x18 / x24 and the frame slots (gb_fr_slots), and gb_gslot_land / gb_slots_land read a slot back from the spill region. Dropped: ge_gfb_keep, ge_gfarr_keep and ge_gtab_keep (BoxLxDefs.v has no gfb, gfarr or gtab); in their place gb_gprev_keep (the frame's copy prev) and gb_greg_keep (the registry block); added gb_slots_keep, gb_gslots_fr_keep, gb_gslots_r_keep, gb_gcursor_keep, gb_slots_fr, gb_slots_app, gb_sp1_al and gb_F_al. *)
(* The seat and the landing of a phase of the walk of fuzz_boxreg's entry function
   LLVMFuzzerTestOneInput on the ASan build, stated once for all of its phases.

   A phase of BoxLxDefs.v carries its machine state as `gb_body` and its own facts; the walk engine wants a
   symbolic state (`st_ok_pi`). `gb_seat` turns the first into the second at the phase's entry pc, and `gb_land`
   turns the symbolic state back into `gb_body` at the phase's exit. The region list in between is `gb_regions`,
   the same for every phase but for the slots and frame chunks a phase knows and the blocks it holds, which it
   passes as `extra`. The spill slots come in two forms: as numbers (`gb_slot_chunks`, `gb_seat`, `gb_land`) and
   as expressions (`gb_slot_chunks_sv`, `gb_seat_sv`, `gb_land_sv`), so that a slot holding an address can keep
   it as an atom plus an offset (the frame's slots over GA_F, `gb_fr_slots_sv`); and the frame carries a write
   window [F + fwlo, F + fwhi) (`gb_frame_region_w`, `gb_seat_csw` / `gb_land_csw` and the _svw forms), since a
   run keeps only the frame bytes outside it: with fwlo = fwhi a phase carries prev and mac across a run
   (`gb_gprev_kept`, `gb_frame_garr8_kept`). All the forms are instances of `gb_seat_csw` / `gb_land_csw`, which
   take any spill chunks and any frame window.

   The atoms: 2 the caller's stack pointer, 32 the shadow base, 60 the realigned stack pointer, 516 the frame on
   the side stack, 528 its flag word, 529 its shadow bytes, 530 the use-after-return flag cell, and 240, 241,
   242 and 253 the image's text and objects 0, 1 and 12. A phase's own atoms go in 33..59, 61..239 or 531 up;
   240..511 are the image. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b BoxFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- a byte of the memory view as a one-byte value (grant's YC88.v) ---- *)
Lemma gb_le_byte_1_0 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
  change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma val_mem1_of_aview : forall segs H m a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
  intros segs H m a v Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate]. injection Hv as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
  rewrite (gb_le_byte_1_0 _ Hr). symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* ---- the atoms of this walk ---- *)
Definition GA_SP : nat := 2%nat.     (* the caller's stack pointer            *)
Definition GA_SB : nat := 32%nat.    (* SHADOW_OFF                            *)
Definition GA_SP1 : nat := 60%nat.   (* the realigned stack pointer, s1       *)
Definition GA_F : nat := 516%nat.    (* the frame on the side stack           *)
Definition GA_FL : nat := 528%nat.   (* its flag word                         *)
Definition GA_FSH : nat := 529%nat.  (* its shadow bytes                      *)
Definition GA_UC : nat := 530%nat.   (* the use-after-return flag cell        *)

(* The saved words of the machine frame: ra at the caller's sp - 8, then s0, s1, s2 .. s11 at sp - 16 - 8j, which
   are the registers x8, x9, x18 .. x27 (0x7ff54 .. 0x7ff84). *)
Definition gb_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1%nat 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8%nat 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9%nat 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18%nat 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19%nat 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 20%nat 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21%nat 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 22%nat 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23%nat 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24%nat 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25%nat 0));
    YP09.mkChunk (-96) (CVal 8 (SOff 26%nat 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27%nat 0)) ].

(* The machine frame's saved words. The body never writes them, so the window is read-only; the epilogue reads
   them back. *)
Definition gb_saved_region : YP09.region :=
  YP09.mkRegion (Some GA_SP) (-104) 0 0 0 gb_saved_chunks.
(* The spill slots above the realigned stack pointer, [sp1, sp1 + 0x98), which the body reads back after every
   call. *)
Definition gb_spill_region (scs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some GA_SP1) 0 0x98 0 0x98 scs.
(* The frame on the side stack, with its flag word at F + 504, and the part [F + fwlo, F + fwhi) of it a phase may
   write: a run keeps every frame byte outside that window (frame_of). fwlo = fwhi: the phase writes no frame
   byte, so a run keeps all of them (gb_frame_kept). *)
Definition gb_frame_region_w (fwlo fwhi : Z) (fcs : list YP09.chunk) : YP09.region :=
  set_window (fframe_region GA_F GA_FL GB_CID fcs) fwlo fwhi.
(* The whole frame writable. *)
Definition gb_frame_region (fcs : list YP09.chunk) : YP09.region := gb_frame_region_w 0 512 fcs.
(* Its 64 shadow bytes; a phase says which of them it may write. *)
Definition gb_shadow_region (wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
  fshadow_region GA_FSH GB_CID wlo whi cs.
(* The GOT word and the cell of the shadow base (objects 1 and 12), and of the use-after-return flag (object 0
   and the flag cell). *)
Definition gb_obj_regions : YP09.smem :=
  [ got_regionP; bcell_regionP GA_SB; uar_got_regionP GA_UC; uar_cell_regionP GA_UC ].

Fixpoint gb_sh_chunks_from (i : Z) (sh : list Z) : list YP09.chunk :=
  match sh with
  | [] => []
  | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: gb_sh_chunks_from (i + 1) t
  end.
(* The frame's shadow bytes as chunks, one per byte. *)
Definition gb_sh_chunks (sh : list Z) : list YP09.chunk := gb_sh_chunks_from 0 sh.

(* A phase's spill slots, as (offset, value) pairs. *)
Definition gb_slot_chunks (l : list (Z * Z)) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (fst p) (CVal 8 (SLit (snd p)))) l.

(* A phase's spill slots with symbolic values, as (offset, expression) pairs: the engine keeps an address as an
   atom plus an offset, which an SLit of an opaque number would hide from its address and shadow-token logic. *)
Definition gb_slot_chunks_sv (l : list (Z * sv)) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (fst p) (CVal 8 (snd p))) l.
(* The frame slots of gslots_fr over the frame's atom: F at 0x18, 0x28 and 0x80, mac at 0x70, prev at 0x78. *)
Definition gb_fr_slots_sv : list (Z * sv) :=
  [(0x18, SOff GA_F 0); (0x28, SOff GA_F 0); (0x70, SOff GA_F GO_MAC); (0x78, SOff GA_F GO_PREV);
   (0x80, SOff GA_F 0)].

Lemma gb_all_disj_app : forall (E : env) r l1 l2,
  YP09.all_disjoint E r l1 -> YP09.all_disjoint E r l2 -> YP09.all_disjoint E r (l1 ++ l2).
Proof.
  intros E r l1. induction l1 as [|x l1 IH]; intros l2 H1 H2; cbn [app YP09.all_disjoint] in *;
    [exact H2|]. destruct H1 as [Hx Hr]. split; [exact Hx | exact (IH l2 Hr H2)].
Qed.

Lemma gb_pwd_app : forall (E : env) l1 l2,
  YP09.pairwise_disjoint E l1 -> YP09.pairwise_disjoint E l2 ->
  Forall (fun r => YP09.all_disjoint E r l2) l1 ->
  YP09.pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|r l1 IH]; intros l2 H1 H2 HF; cbn [app]; [exact H2|].
  cbn [YP09.pairwise_disjoint] in H1 |- *. destruct H1 as [Ha Hp].
  inversion HF as [|x y Hx Ht]; subst.
  split; [apply gb_all_disj_app; [exact Ha | exact Hx] | exact (IH l2 Hp H2 Ht)].
Qed.

Lemma gb_regions_wf_In : forall rs r, YP09.regions_wf rs = true -> In r rs -> YP09.region_wf r = true.
Proof.
  intros rs. induction rs as [|x rs IH]; intros r Hwf Hin; [destruct Hin|].
  cbn [YP09.regions_wf] in Hwf. apply andb_prop in Hwf as [Hx Hr].
  destruct Hin as [<-|Hin]; [exact Hx | exact (IH r Hr Hin)].
Qed.

Lemma gb_all_disj_In : forall (E : env) r rs r',
  YP09.all_disjoint E r rs -> In r' rs -> YP09.extent_disjoint E r r'.
Proof.
  intros E r rs. induction rs as [|x rs IH]; intros r' H Hin; [destruct Hin|].
  cbn [YP09.all_disjoint] in H. destruct H as [Hx Hr].
  destruct Hin as [<-|Hin]; [exact Hx | exact (IH r' Hr Hin)].
Qed.

Lemma gb_pwd_mid : forall (E : env) l1 r l2, YP09.pairwise_disjoint E (l1 ++ r :: l2) ->
  forall r', In r' (l1 ++ l2) -> YP09.extent_disjoint E r r'.
Proof.
  intros E l1. induction l1 as [|x l1 IH]; intros r l2 H r' Hin; cbn [app] in H, Hin.
  - cbn [YP09.pairwise_disjoint] in H. exact (gb_all_disj_In E r l2 r' (proj1 H) Hin).
  - cbn [YP09.pairwise_disjoint] in H. destruct H as [Hx Hp].
    destruct Hin as [He|Hin].
    + subst x. pose proof (gb_all_disj_In E r' (l1 ++ r :: l2) r Hx
        ltac:(apply in_or_app; right; left; reflexivity)) as Hd.
      unfold YP09.extent_disjoint in Hd |- *. lia.
    + exact (IH r l2 Hp r' Hin).
Qed.

(* No byte of a region that has an empty write window, in a well-formed list whose extents are pairwise
   disjoint, is in the list's write range. *)
Lemma gb_not_wrange : forall (E : env) l1 r l2 a,
  YP09.regions_wf (l1 ++ r :: l2) = true -> YP09.pairwise_disjoint E (l1 ++ r :: l2) ->
  YP09.r_whi r <= YP09.r_wlo r ->
  YP09.base_val E (YP09.r_base r) + YP09.r_lo r <= a < YP09.base_val E (YP09.r_base r) + YP09.r_hi r ->
  ~ in_wrange E (l1 ++ r :: l2) a.
Proof.
  intros E l1 r l2 a Hwf Hpd Hw Ha (r' & Hin & Hr').
  pose proof (gb_regions_wf_In _ r' Hwf Hin) as Hwf'.
  unfold YP09.region_wf in Hwf'. apply andb_prop in Hwf' as [Hwf' _]. apply andb_prop in Hwf' as [_ Hwin].
  apply orb_prop in Hwin.
  assert (Hcase : r' = r \/ In r' (l1 ++ l2)).
  { apply in_app_or in Hin. destruct Hin as [Hin | [<- | Hin]];
      [right; apply in_or_app; left; exact Hin | left; reflexivity | right; apply in_or_app; right; exact Hin]. }
  destruct Hcase as [-> | Hin'].
  - lia.
  - pose proof (gb_pwd_mid E l1 r l2 Hpd r' Hin') as Hd. unfold YP09.extent_disjoint in Hd.
    destruct Hwin as [Hwin | Hwin]; [apply Z.leb_le in Hwin; lia|].
    apply andb_prop in Hwin as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma gb_sh_chunks_from_In : forall sh i j, (i < length sh)%nat ->
  In (YP09.mkChunk (j + Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (gb_sh_chunks_from j sh).
Proof.
  intros sh. induction sh as [|v t IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [gb_sh_chunks_from nth].
  - left. rewrite Z.add_0_r. reflexivity.
  - right. replace (j + Z.of_nat (S i)) with (j + 1 + Z.of_nat i) by lia.
    apply IH. cbn [length] in Hi. lia.
Qed.

Lemma gb_sh_chunks_In : forall sh i, (i < length sh)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (gb_sh_chunks sh).
Proof.
  intros sh i Hi. unfold gb_sh_chunks.
  replace (Z.of_nat i) with (0 + Z.of_nat i) by lia. apply gb_sh_chunks_from_In. exact Hi.
Qed.

Lemma gb_slot_chunks_In : forall l off v, In (off, v) l ->
  In (YP09.mkChunk off (CVal 8 (SLit v))) (gb_slot_chunks l).
Proof.
  intros l off v Hin. unfold gb_slot_chunks.
  exact (in_map (fun p => YP09.mkChunk (fst p) (CVal 8 (SLit (snd p)))) l (off, v) Hin).
Qed.

Lemma gb_slot_chunks_sv_In : forall l off e, In (off, e) l ->
  In (YP09.mkChunk off (CVal 8 e)) (gb_slot_chunks_sv l).
Proof.
  intros l off e Hin. unfold gb_slot_chunks_sv.
  exact (in_map (fun p => YP09.mkChunk (fst p) (CVal 8 (snd p))) l (off, e) Hin).
Qed.

(* GSH_it: prev's 36 shadow bytes (8 .. 43) are 0, mac's byte 4 is 6. *)
Lemma gb_GSH_it_len : length GSH_it = GB_NSH.
Proof. reflexivity. Qed.

Lemma gb_GSH_it_prev : forall i, (8 <= i < 44)%nat -> nth i GSH_it 0 = 0.
Proof.
  intros i Hi. unfold GSH_it.
  rewrite app_nth2 by (cbn [length]; lia). cbn [length].
  rewrite app_nth1 by (rewrite repeat_length; lia).
  apply nth_repeat.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the environment a phase runs in ---- *)
Definition gb_E (cx : bcx) (fp : Z) (E : env) : Prop :=
  (forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
  ew E GA_SB = w64 SHADOW_OFF /\
  ew E GA_SP1 = w64 (c_sp1 cx) /\
  ew E GA_F = w64 (gF cx fp) /\
  ew E GA_FL = w64 (gFL cx fp) /\
  ew E GA_FSH = w64 (gSH cx fp) /\
  ew E GA_UC = w64 (as_uar_cell B).

(* ---- the region list of a phase ---- *)
(* With the frame's write window [F + fwlo, F + fwhi) ... *)
Definition gb_regions0w (cx : bcx) (fp : Z) (sh : list Z) (scs : list YP09.chunk) (fwlo fwhi : Z)
  (fcs : list YP09.chunk) (wlo whi : Z) : YP09.smem :=
  gb_saved_region :: gb_spill_region scs :: gb_frame_region_w fwlo fwhi fcs
  :: gb_shadow_region wlo whi (gb_sh_chunks sh) :: gb_obj_regions.
Definition gb_regionsw (cx : bcx) (fp : Z) (sh : list Z) (scs : list YP09.chunk) (fwlo fwhi : Z)
  (fcs : list YP09.chunk) (wlo whi : Z) (extra : YP09.smem) : YP09.smem :=
  gb_regions0w cx fp sh scs fwlo fwhi fcs wlo whi ++ extra.
Definition gb_ssw (cx : bcx) (fp : Z) (pc : Z) (sr : list sv) (sh : list Z) (scs : list YP09.chunk)
  (fwlo fwhi : Z) (fcs : list YP09.chunk) (wlo whi : Z) (extra : YP09.smem) (G : facts) : sstate :=
  mkSS pc sr (gb_regionsw cx fp sh scs fwlo fwhi fcs wlo whi extra) None G.
(* ... and with the whole frame writable. *)
Definition gb_regions0 (cx : bcx) (fp : Z) (sh : list Z) (scs fcs : list YP09.chunk)
  (wlo whi : Z) : YP09.smem :=
  gb_regions0w cx fp sh scs 0 512 fcs wlo whi.
Definition gb_regions (cx : bcx) (fp : Z) (sh : list Z) (scs fcs : list YP09.chunk)
  (wlo whi : Z) (extra : YP09.smem) : YP09.smem :=
  gb_regionsw cx fp sh scs 0 512 fcs wlo whi extra.
Definition gb_ss (cx : bcx) (fp : Z) (pc : Z) (sr : list sv) (sh : list Z)
  (scs fcs : list YP09.chunk) (wlo whi : Z) (extra : YP09.smem) (G : facts) : sstate :=
  gb_ssw cx fp pc sr sh scs 0 512 fcs wlo whi extra G.

(* A phase's spill slots and their values. *)
Definition gb_slots (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) (l : list (Z * Z)) : Prop :=
  Forall (fun p => gslot cx W3 ms3 (fst p) (snd p) /\ 0 <= snd p < 2 ^ 64) l.
(* The same with symbolic values: each slot holds the value its expression has in E. *)
Definition gb_slots_sv (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) (E : env) (l : list (Z * sv)) : Prop :=
  Forall (fun p => rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + fst p) =
                   Some (bv_unsigned (sv_denot E (snd p)))) l.

(* The slots that name the frame and its objects (BoxLxDefs.v gslots_fr), as (offset, value) pairs. *)
Definition gb_fr_slots (cx : bcx) (fp : Z) : list (Z * Z) :=
  [(0x18, gF cx fp); (0x28, gF cx fp); (0x70, gF cx fp + GO_MAC); (0x78, gF cx fp + GO_PREV);
   (0x80, gF cx fp)].

Lemma gb_sv_SOff0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

Section d.
Variable cx : bcx.
Variable fp : Z.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* ---- the chunks of a phase ---- *)

Lemma gb_slot_chunk_ok : forall (E : env) off v,
  gslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E M3 (c_sp1 cx) (YP09.mkChunk off (CVal 8 (SLit v))).
Proof.
  intros E off v Hv Hr.
  apply (chunk_ok_val SEGS E M3 (c_sp1 cx) off 8%N (SLit v) v).
  - reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hr.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hv.
Qed.

Lemma gb_slot_chunks_ok : forall (E : env) l,
  gb_slots cx W3 ms3 l ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) (gb_slot_chunks l).
Proof.
  intros E l. induction l as [|p t IH]; intros H; cbn [gb_slot_chunks map]; [constructor|].
  inversion H as [|x y [Hp Hr] Ht]; subst. constructor.
  - exact (gb_slot_chunk_ok E (fst p) (snd p) Hp Hr).
  - exact (IH Ht).
Qed.

Lemma gb_slots_app : forall l1 l2,
  gb_slots cx W3 ms3 l1 -> gb_slots cx W3 ms3 l2 -> gb_slots cx W3 ms3 (l1 ++ l2).
Proof. intros l1 l2 H1 H2. unfold gb_slots. apply Forall_app. split; [exact H1 | exact H2]. Qed.

Lemma gb_slot_chunks_sv_ok : forall (E : env) l,
  gb_slots_sv cx W3 ms3 E l ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) (gb_slot_chunks_sv l).
Proof.
  intros E l. induction l as [|p t IH]; intros H; cbn [gb_slot_chunks_sv map]; [constructor|].
  inversion H as [|x y Hp Ht]; subst. constructor.
  - apply (chunk_ok_val SEGS E M3 (c_sp1 cx) (fst p) 8%N (snd p) (bv_unsigned (sv_denot E (snd p)))).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hp.
  - exact (IH Ht).
Qed.

Lemma gb_slots_sv_app : forall (E : env) l1 l2,
  gb_slots_sv cx W3 ms3 E l1 -> gb_slots_sv cx W3 ms3 E l2 -> gb_slots_sv cx W3 ms3 E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. unfold gb_slots_sv. apply Forall_app. split; [exact H1 | exact H2]. Qed.

(* A slot with a number as a slot with an expression of that value, and back. *)
Lemma gb_slot_sv_of_gslot : forall (E : env) off e v,
  gslot cx W3 ms3 off v -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some (bv_unsigned (sv_denot E e)).
Proof. intros E off e v Hs He Hv. rewrite He. unfold w64. rewrite unsigned_lit_small by exact Hv. exact Hs. Qed.

Lemma gb_gslot_of_sv : forall (E : env) l off e v,
  gb_slots_sv cx W3 ms3 E l -> In (off, e) l -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  gslot cx W3 ms3 off v.
Proof.
  intros E l off e v Hl Hin He Hv. unfold gb_slots_sv in Hl. rewrite Forall_forall in Hl.
  pose proof (Hl (off, e) Hin) as H. cbn [fst snd] in H.
  unfold gslot. rewrite H, He. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity.
Qed.

Lemma gb_sh_chunks_from_ok : forall (E : env) sh i,
  (forall j, (j < length sh)%nat ->
     aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E M3 (gSH cx fp)) (gb_sh_chunks_from i sh).
Proof.
  intros E sh. induction sh as [|v t IH]; intros i H; cbn [gb_sh_chunks_from]; [constructor|].
  constructor.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
    rewrite Z.add_0_r in H0.
    destruct (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + i) v H0) as [Hm Hb].
    apply (chunk_ok_val SEGS E M3 (gSH cx fp) i 1%N (SLit v) v).
    + reflexivity.
    + cbn [Z.of_N]. change (8 * 1) with 8. exact Hb.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. exact Hm.
  - apply IH. intros j Hj. pose proof (H (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
    replace (gSH cx fp + (i + 1 + Z.of_nat j)) with (gSH cx fp + (i + Z.of_nat (S j))) by lia.
    exact Hs.
Qed.

Lemma gb_sh_chunks_ok : forall (E : env) sh,
  gshadow cx fp W3 ms3 sh ->
  Forall (YP09.chunk_ok SEGS E M3 (gSH cx fp)) (gb_sh_chunks sh).
Proof.
  intros E sh H. apply gb_sh_chunks_from_ok. intros j Hj.
  replace (gSH cx fp + (0 + Z.of_nat j)) with (gSH cx fp + Z.of_nat j) by lia.
  exact (H j Hj).
Qed.

(* ---- the bytes a phase's facts speak about, and what keeps them ---- *)
(* A call that leaves this phase's own memory alone keeps every byte at or above the realigned stack pointer,
   the caller's input block, the frame and its shadow, and the blocks the phase holds (`rs`, as (address, size)
   pairs). *)
Definition gb_keep_at (rs : list (Z * Z)) (a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/
  c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + fs_frame_bytes GB_CID \/
  gSH cx fp <= a < gSH cx fp + fs_frame_bytes GB_CID / 8 \/
  Exists (fun r => fst r <= a < fst r + snd r) rs.
Definition gb_keep (rs : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, gb_keep_at rs a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma gb_keep_refl : forall rs m, gb_keep rs m m.
Proof. intros rs m a _. reflexivity. Qed.

Lemma gb_keep_trans : forall rs m1 m2 m3,
  gb_keep rs m1 m2 -> gb_keep rs m2 m3 -> gb_keep rs m1 m3.
Proof. intros rs m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma gb_keep_pointwise : forall rs m m',
  (forall x, m' x = m x) -> gb_keep rs m m'.
Proof.
  intros rs m m' Hm a _. unfold aview, YP09.mbyte, mrestrict. rewrite Hm. reflexivity.
Qed.

Lemma gb_keep_sub : forall rs rs' m m',
  (forall r, In r rs -> In r rs') -> gb_keep rs' m m' -> gb_keep rs m m'.
Proof.
  intros rs rs' m m' Hin Hk a Ha. apply Hk.
  unfold gb_keep_at in Ha |- *.
  destruct Ha as [H|[H|[H|[H|H]]]]; [left|right;left|right;right;left|right;right;right;left|].
  1-4: exact H.
  right; right; right; right. apply Exists_exists in H as (r & Hr & Hb).
  apply Exists_exists. exists r. split; [exact (Hin r Hr) | exact Hb].
Qed.

Lemma gb_rdword_keep : forall rs m m' a v,
  gb_keep rs m m' -> (forall i, 0 <= i < 8 -> gb_keep_at rs (a + i)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros rs m m' a v Hk Hin Hr.
  assert (K : forall i, 0 <= i < 8 ->
    aview SEGS (w_H W3) m' (a + i) = aview SEGS (w_H W3) m (a + i))
    by (intros i Hi; apply Hk; apply Hin; lia).
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma gb_garr8_keep : forall rs m m' a l,
  gb_keep rs m m' ->
  (forall i, 0 <= i < Z.of_nat (length l) -> gb_keep_at rs (a + i)) ->
  garr8 SEGS (mrestrict (w_H W3) m) a l ->
  garr8 SEGS (mrestrict (w_H W3) m') a l.
Proof.
  intros rs m m' a l Hk Hin Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (a + Z.of_nat j)
             (Hk (a + Z.of_nat j) (Hin (Z.of_nat j) ltac:(lia)))).
  exact Hv0.
Qed.

(* ---- the geometry a phase runs in ---- *)
Section e.
Variable ly3 : alayout.
Variable S3 : astate.
Variable md3 : Model.
Variable k : Z.
Hypothesis HB : gb_base B MT cx.
Hypothesis HJ : ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
  (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].

Lemma gb_fin : In (GB_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

Lemma gb_frame_addr_eq : frame_addr ly3 GB_CID fp = gF cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  unfold gF. apply Efa.
Qed.

Lemma gb_sp_facts :
  spZ (c_regs cx) mod 16 = 0 /\
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256.
Proof.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (Hac & _).
  assert (Hx : 0 <= spZ (c_regs cx) + -256) by (unfold GB_STK in *; lia).
  pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
  split; [exact Hal16|]. split; [unfold GB_STK in *; lia|]. split; [lia|].
  rewrite Hsp1. lia.
Qed.

(* The realigned stack pointer is 32-aligned (`andi sp,sp,-0x20` at 0x7ff8c). *)
Lemma gb_sp1_al : c_sp1 cx mod 32 = 0.
Proof.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  rewrite Hsp1, Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma gb_F_facts :
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\
  in_app (gF cx fp) 512 /\
  (gF cx fp + 512 <= IMG_LO \/ IMG_TOP <= gF cx fp) /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8.
Proof.
  pose proof HJ as (HAR3 & _).
  pose proof (frames_bounds _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 GB_CID fp HAR3 gb_fin) as HFo.
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  rewrite gb_frame_addr_eq in HF0, HFc, HFia, HFo. rewrite Hfb in HFc, HFia, HFo.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  reflexivity.
Qed.

(* The frame is 64-aligned (its slot of class 3 is 512 bytes). *)
Lemma gb_F_al : gF cx fp mod 64 = 0.
Proof.
  pose proof HJ as (HAR3 & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (Hal & _).
  rewrite gb_frame_addr_eq in Hal. exact Hal.
Qed.

Lemma gb_base_sp : forall E, gb_E cx fp E -> YP09.base_val E (Some GA_SP) = spZ (c_regs cx).
Proof.
  intros E (AG & _). destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Husp & _).
  cbn [YP09.base_val]. rewrite (AG GA_SP ltac:(unfold GA_SP; lia)). exact Husp.
Qed.

Lemma gb_region_saved : forall E, gb_E cx fp E -> gsaved cx W3 ms3 ->
  YP09.region_ok SEGS E M3 gb_saved_region.
Proof.
  intros E HE Hsv. pose proof (gb_base_sp E HE) as Ub.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & _).
  destruct HE as (AG & _).
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & _).
  pose proof asan_consts as (Hac & _).
  assert (HSV : forall (n : nat) (r : bv 5) off,
    Z.of_nat n = bv_unsigned r -> (n < 33)%nat ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) + off) =
      Some (bv_unsigned (getr (c_regs cx) r)) ->
    YP09.chunk_ok SEGS E M3 (spZ (c_regs cx)) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
  { intros n r off Hn Hlt Hrd.
    apply (chunk_ok_val SEGS E M3 (spZ (c_regs cx)) off 8%N (SOff n 0)
             (bv_unsigned (getr (c_regs cx) r))).
    - rewrite gb_sv_SOff0, (AG n Hlt), (HE0 n r Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hrd. }
  destruct Hsv as (Hra & Hsj).
  unfold YP09.region_ok, gb_saved_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold gb_saved_chunks.
  apply Forall_cons;
    [apply (HSV 1%nat (Z_to_bv 5 1) (-8)); [vm_compute; reflexivity | lia |
      replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact Hra] | ].
  apply Forall_cons;
    [apply (HSV 8%nat (Z_to_bv 5 (if 0 <? 2 then 8 + 0 else 16 + 0)) (-16));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia;
       exact (Hsj 0 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 9%nat (Z_to_bv 5 (if 1 <? 2 then 8 + 1 else 16 + 1)) (-24));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -24) with (spZ (c_regs cx) - 16 - 8 * 1) by lia;
       exact (Hsj 1 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 18%nat (Z_to_bv 5 (if 2 <? 2 then 8 + 2 else 16 + 2)) (-32));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -32) with (spZ (c_regs cx) - 16 - 8 * 2) by lia;
       exact (Hsj 2 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 19%nat (Z_to_bv 5 (if 3 <? 2 then 8 + 3 else 16 + 3)) (-40));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -40) with (spZ (c_regs cx) - 16 - 8 * 3) by lia;
       exact (Hsj 3 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 20%nat (Z_to_bv 5 (if 4 <? 2 then 8 + 4 else 16 + 4)) (-48));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -48) with (spZ (c_regs cx) - 16 - 8 * 4) by lia;
       exact (Hsj 4 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 21%nat (Z_to_bv 5 (if 5 <? 2 then 8 + 5 else 16 + 5)) (-56));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -56) with (spZ (c_regs cx) - 16 - 8 * 5) by lia;
       exact (Hsj 5 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 22%nat (Z_to_bv 5 (if 6 <? 2 then 8 + 6 else 16 + 6)) (-64));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -64) with (spZ (c_regs cx) - 16 - 8 * 6) by lia;
       exact (Hsj 6 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 23%nat (Z_to_bv 5 (if 7 <? 2 then 8 + 7 else 16 + 7)) (-72));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -72) with (spZ (c_regs cx) - 16 - 8 * 7) by lia;
       exact (Hsj 7 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 24%nat (Z_to_bv 5 (if 8 <? 2 then 8 + 8 else 16 + 8)) (-80));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -80) with (spZ (c_regs cx) - 16 - 8 * 8) by lia;
       exact (Hsj 8 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 25%nat (Z_to_bv 5 (if 9 <? 2 then 8 + 9 else 16 + 9)) (-88));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -88) with (spZ (c_regs cx) - 16 - 8 * 9) by lia;
       exact (Hsj 9 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 26%nat (Z_to_bv 5 (if 10 <? 2 then 8 + 10 else 16 + 10)) (-96));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -96) with (spZ (c_regs cx) - 16 - 8 * 10) by lia;
       exact (Hsj 10 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 27%nat (Z_to_bv 5 (if 11 <? 2 then 8 + 11 else 16 + 11)) (-104));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -104) with (spZ (c_regs cx) - 16 - 8 * 11) by lia;
       exact (Hsj 11 ltac:(lia))] | ].
  apply Forall_nil.
Qed.

Lemma gb_region_spill : forall E scs, gb_E cx fp E ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) scs ->
  YP09.region_ok SEGS E M3 (gb_spill_region scs).
Proof.
  intros E scs HE Hcs.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  destruct HE as (AG & Hsb & Hsp1E & _).
  assert (Ub : YP09.base_val E (Some GA_SP1) = c_sp1 cx).
  { cbn [YP09.base_val]. rewrite Hsp1E. apply unsigned_lit_small. lia. }
  unfold YP09.region_ok, gb_spill_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GB_STK. lia.
Qed.

Lemma gb_flag_addr_eq : flag_addr ly3 GB_CID fp = gFL cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  pose proof (Efa 0 0) as E00. unfold frame_addr in E00.
  unfold gFL, flag_addr. lia.
Qed.

Lemma gb_region_frame_w : forall E fwlo fwhi fcs, gb_E cx fp E -> 0 <= fwlo -> fwhi <= 512 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  YP09.region_ok SEGS E M3 (gb_frame_region_w fwlo fwhi fcs).
Proof.
  intros E fwlo fwhi fcs HE Hfw0 Hfw1 Hfl Hcs.
  pose proof gb_F_facts as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (_ & _ & HFpres & _).
  rewrite gb_frame_addr_eq, Hfb in HFpres.
  destruct (al_flag _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (_ & _ & Hfia & Hflt).
  rewrite gb_flag_addr_eq in Hfia, Hflt.
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE & _).
  assert (Ub : YP09.base_val E (Some GA_F) = gF cx fp).
  { cbn [YP09.base_val]. rewrite HFE. apply unsigned_lit_small. lia. }
  assert (HflZ : 0 <= gFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  rewrite Hfb in Hfl.
  unfold YP09.region_ok, gb_frame_region_w, set_window, fframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub, Hfb. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (gF cx fp + o) ltac:(lia))).
  - apply Forall_app. split; [exact Hcs|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (gF cx fp) (512 - 8) 8%N (SOff GA_FL 0) (gFL cx fp)).
    + rewrite gb_sv_SOff0, HFLE. reflexivity.
    + cbn [Z.of_N]. change (8 * 8) with 64. exact HflZ.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. replace (gF cx fp + (512 - 8)) with (gF cx fp + 512 - 8) by lia.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hfl.
Qed.

Lemma gb_region_frame : forall E fcs, gb_E cx fp E ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  YP09.region_ok SEGS E M3 (gb_frame_region fcs).
Proof. intros E fcs HE. exact (gb_region_frame_w E 0 512 fcs HE ltac:(lia) ltac:(lia)). Qed.

Lemma gb_sh_range : 0 <= gSH cx fp /\ gSH cx fp + 64 <= 2 ^ 64.
Proof.
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000)
    by (apply Z.div_le_upper_bound; lia).
  rewrite HSHeq. unfold SHADOW_OFF. lia.
Qed.

Lemma gb_region_shadow : forall E sh wlo whi, gb_E cx fp E ->
  0 <= wlo -> whi <= 64 -> gshadow cx fp W3 ms3 sh ->
  YP09.region_ok SEGS E M3 (gb_shadow_region wlo whi (gb_sh_chunks sh)).
Proof.
  intros E sh wlo whi HE Hwlo Hwhi Hsh.
  pose proof gb_sh_range as (Hs0 & Hs1).
  pose proof gb_F_facts as (_ & _ & _ & _ & HSHeq).
  pose proof HJ as (HAR3 & _).
  assert (Hfb8 : fs_frame_bytes GB_CID / 8 = 64) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (_ & _ & _ & HFSpres).
  rewrite gb_frame_addr_eq, Hfb8 in HFSpres.
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp)
    by (unfold shadow_addr; rewrite HSHeq; reflexivity).
  rewrite Hsa in HFSpres.
  pose proof (gb_sh_chunks_ok E sh Hsh) as Hcs.
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE & _).
  assert (Ub : YP09.base_val E (Some GA_FSH) = gSH cx fp).
  { cbn [YP09.base_val]. rewrite HFSE. apply unsigned_lit_small. lia. }
  unfold YP09.region_ok, gb_shadow_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub, Hfb8. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
Qed.

Lemma gb_region_objs : forall E, gb_E cx fp E -> img_env VAL A_LIM E ->
  Forall (YP09.region_ok SEGS E M3) gb_obj_regions.
Proof.
  intros E HE HEI.
  pose proof HJ as (HAR3 & _).
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & Kuar & Kgot & Kguar).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot.
  rewrite (pal_cell B TL) in Kcell.
  rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as Huc.
  destruct HE as (AG & Hsb & _ & _ & _ & _ & HUC).
  pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
  pose proof (pa_obj_img 12 ltac:(lia)) as Ho12.
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  assert (Ubuc : YP09.base_val E (Some GA_UC) = as_uar_cell B).
  { cbn [YP09.base_val]. rewrite HUC. apply unsigned_lit_small. lia. }
  unfold gb_obj_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 1)) 0 8%N (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12))).
    - rewrite gb_sv_SOff0. apply (img_env_atomP E (A_OBJ 12) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
    - cbn [Z.of_N]. change (8 * 8) with 64. pose proof (pa_val_range (A_OBJ 12)). lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kgot. }
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 12)) 0 8%N (SOff GA_SB 0) SHADOW_OFF).
    - rewrite gb_sv_SOff0. exact Hsb.
    - cbn [Z.of_N]. change (8 * 8) with 64. unfold SHADOW_OFF. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kcell. }
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 0)) 0 8%N (SOff GA_UC 0) (as_uar_cell B)).
    - rewrite gb_sv_SOff0. exact HUC.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kguar. }
  apply Forall_cons; [|apply Forall_nil].
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite Ubuc.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (as_uar_cell B) 0 4%N (SLit 1) 1).
    - reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rd32 SEGS (w_H W3) (ms_mem ms3)). exact Kuar. }
Qed.

Lemma gb_disjw : forall E sh scs fwlo fwhi fcs wlo whi, gb_E cx fp E -> img_env VAL A_LIM E ->
  YP09.pairwise_disjoint E (gb_regions0w cx fp sh scs fwlo fwhi fcs wlo whi).
Proof.
  intros E sh scs fwlo fwhi fcs wlo whi HE HEI.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof gb_F_facts as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof gb_sh_range as (Hs0 & Hs1).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
  pose proof (pa_obj_img 12 ltac:(lia)) as Ho12.
  pose proof (palf_uar_img B TLF) as Huc.
  pose proof (palf_sep B TLF) as Hsep.
  cbn [zseps zseps_from fst snd] in Hsep.
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  pose proof (gb_base_sp E HE) as Ub2.
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE & HUC).
  assert (Ub60 : YP09.base_val E (Some GA_SP1) = c_sp1 cx)
    by (cbn [YP09.base_val]; rewrite Hsp1E; apply unsigned_lit_small; lia).
  assert (Ub516 : YP09.base_val E (Some GA_F) = gF cx fp)
    by (cbn [YP09.base_val]; rewrite HFE; apply unsigned_lit_small; lia).
  assert (Ub529 : YP09.base_val E (Some GA_FSH) = gSH cx fp)
    by (cbn [YP09.base_val]; rewrite HFSE; apply unsigned_lit_small; lia).
  assert (Ub530 : YP09.base_val E (Some GA_UC) = as_uar_cell B)
    by (cbn [YP09.base_val]; rewrite HUC; apply unsigned_lit_small; lia).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes GB_CID / 8 = 64) by (vm_compute; reflexivity).
  apply pairwise_disjoint_of_extents.
  unfold gb_regions0w, gb_saved_region, gb_spill_region, gb_frame_region_w, set_window, fframe_region,
    gb_shadow_region, fshadow_region, gb_obj_regions, got_regionP, bcell_regionP,
    uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite Ub2, Ub60, Ub516, Ub529, Ub530, Hfb8, Hfb.
  rewrite (EA (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (EA (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (EA (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HSHeq.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  repeat split; lia.
Qed.

Lemma gb_disj : forall E sh scs fcs wlo whi, gb_E cx fp E -> img_env VAL A_LIM E ->
  YP09.pairwise_disjoint E (gb_regions0 cx fp sh scs fcs wlo whi).
Proof. intros E sh scs fcs wlo whi. exact (gb_disjw E sh scs 0 512 fcs wlo whi). Qed.

(* ---- the seat: a phase's machine state as the engine's symbolic state ---- *)
(* Over any spill chunks the slots satisfy and any frame write window inside the frame; gb_seat_cs (the whole
   frame writable), gb_seat (slots as numbers), gb_seat_sv and gb_seat_svw (slots as expressions) instantiate
   it. *)
Theorem gb_seat_csw : forall E pc sr sh scs fwlo fwhi fcs wlo whi extra G,
  gb_E cx fp E -> img_env VAL A_LIM E ->
  gb_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) scs ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= fwlo -> fwhi <= 512 ->
  0 <= wlo -> whi <= 64 ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwhi fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (gb_regions0w cx fp sh scs fwlo fwhi fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh scs fwlo fwhi fcs wlo whi extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh scs fwlo fwhi fcs wlo whi extra G HE HEI HBD HR HSC HFC Hfw0 Hfw1 Hwlo Hwhi Hwf Hex
    Hexp Hexd HG.
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & Hgregs & Hsaved & Hshadow
                     & Hlen & Hflag & Hslfr & Hgarr).
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold gb_ssw, gb_regionsw.
  apply pa_entry_st_ok_full; [exact HR | exact Hwf | | | exact HG].
  - apply Forall_app. split; [|exact Hex].
    unfold gb_regions0w. apply Forall_cons; [exact (gb_region_saved E HE Hsaved)|].
    apply Forall_cons; [exact (gb_region_spill E scs HE HSC)|].
    apply Forall_cons; [exact (gb_region_frame_w E fwlo fwhi fcs HE Hfw0 Hfw1 Hflag HFC)|].
    apply Forall_cons; [exact (gb_region_shadow E sh wlo whi HE Hwlo Hwhi Hshadow)|].
    exact (gb_region_objs E HE HEI).
  - apply gb_pwd_app; [exact (gb_disjw E sh scs fwlo fwhi fcs wlo whi HE HEI) | exact Hexp | exact Hexd].
Qed.

Theorem gb_seat_cs : forall E pc sr sh scs fcs wlo whi extra G,
  gb_E cx fp E -> img_env VAL A_LIM E ->
  gb_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) scs ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= wlo -> whi <= 64 ->
  YP09.regions_wf (gb_regions cx fp sh scs fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (gb_regions0 cx fp sh scs fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh scs fcs wlo whi extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh scs fcs wlo whi extra G HE HEI HBD HR HSC HFC.
  exact (gb_seat_csw E pc sr sh scs 0 512 fcs wlo whi extra G HE HEI HBD HR HSC HFC ltac:(lia) ltac:(lia)).
Qed.

Theorem gb_seat : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E -> img_env VAL A_LIM E ->
  gb_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  gb_slots cx W3 ms3 l ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= wlo -> whi <= 64 ->
  YP09.regions_wf (gb_regions cx fp sh (gb_slot_chunks l) fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (gb_regions0 cx fp sh (gb_slot_chunks l) fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HEI HBD HR HSL.
  exact (gb_seat_cs E pc sr sh (gb_slot_chunks l) fcs wlo whi extra G HE HEI HBD HR
           (gb_slot_chunks_ok E l HSL)).
Qed.

Theorem gb_seat_sv : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E -> img_env VAL A_LIM E ->
  gb_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  gb_slots_sv cx W3 ms3 E l ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= wlo -> whi <= 64 ->
  YP09.regions_wf (gb_regions cx fp sh (gb_slot_chunks_sv l) fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (gb_regions0 cx fp sh (gb_slot_chunks_sv l) fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks_sv l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HEI HBD HR HSL.
  exact (gb_seat_cs E pc sr sh (gb_slot_chunks_sv l) fcs wlo whi extra G HE HEI HBD HR
           (gb_slot_chunks_sv_ok E l HSL)).
Qed.

Theorem gb_seat_svw : forall E pc sr sh l fwlo fwhi fcs wlo whi extra G,
  gb_E cx fp E -> img_env VAL A_LIM E ->
  gb_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  gb_slots_sv cx W3 ms3 E l ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= fwlo -> fwhi <= 512 ->
  0 <= wlo -> whi <= 64 ->
  YP09.regions_wf (gb_regionsw cx fp sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra)
    (gb_regions0w cx fp sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra G)
    (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh l fwlo fwhi fcs wlo whi extra G HE HEI HBD HR HSL.
  exact (gb_seat_csw E pc sr sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra G HE HEI HBD HR
           (gb_slot_chunks_sv_ok E l HSL)).
Qed.

(* ---- reading a spill slot back from the engine's symbolic state ---- *)
Lemma gb_gslot_landw : forall E pc sr sh l fwlo fwhi fcs wlo whi extra G off v,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh (gb_slot_chunks l) fwlo fwhi fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  In (off, v) l -> 0 <= v < 2 ^ 64 ->
  gslot cx W3 ms3 off v.
Proof.
  intros E pc sr sh l fwlo fwhi fcs wlo whi extra G off v HE HS Hin Hv.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (Hac & _).
  destruct HE as (AG & Hsb & Hsp1E & _).
  assert (Rspill : YP09.region_ok SEGS E M3 (gb_spill_region (gb_slot_chunks l))).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 1%nat _ HS eq_refl). }
  unfold gslot.
  apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
  apply (field_of_region E M3 GA_SP1 (c_sp1 cx) (gb_slot_chunks l) 0 0x98 0 0x98 off 8%N
           (SLit v) v Rspill).
  - rewrite Hsp1E. apply unsigned_lit_small. lia.
  - exact (gb_slot_chunks_In l off v Hin).
  - reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hv.
  - cbn [Z.of_N]. lia.
Qed.

Lemma gb_gslot_land : forall E pc sr sh l fcs wlo whi extra G off v,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  In (off, v) l -> 0 <= v < 2 ^ 64 ->
  gslot cx W3 ms3 off v.
Proof. intros E pc sr sh l fcs wlo whi extra G. exact (gb_gslot_landw E pc sr sh l 0 512 fcs wlo whi extra G). Qed.

Lemma gb_slots_land : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  Forall (fun p => 0 <= snd p < 2 ^ 64) l ->
  gb_slots cx W3 ms3 l.
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HS Hr.
  unfold gb_slots. rewrite Forall_forall in Hr |- *. intros [off v] Hin.
  pose proof (Hr (off, v) Hin) as Hv. cbn [fst snd] in Hv |- *.
  split; [|exact Hv].
  exact (gb_gslot_land E pc sr sh l fcs wlo whi extra G off v HE HS Hin Hv).
Qed.

Lemma gb_slots_sv_landw : forall E pc sr sh l fwlo fwhi fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  gb_slots_sv cx W3 ms3 E l.
Proof.
  intros E pc sr sh l fwlo fwhi fcs wlo whi extra G HE HS.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (Hac & _).
  destruct HE as (AG & Hsb & Hsp1E & _).
  assert (Rspill : YP09.region_ok SEGS E M3 (gb_spill_region (gb_slot_chunks_sv l))).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 1%nat _ HS eq_refl). }
  unfold gb_slots_sv. rewrite Forall_forall. intros [off e] Hin. cbn [fst snd].
  apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|apply u64_range].
  apply (field_of_region E M3 GA_SP1 (c_sp1 cx) (gb_slot_chunks_sv l) 0 0x98 0 0x98 off 8%N
           e (bv_unsigned (sv_denot E e)) Rspill).
  - rewrite Hsp1E. apply unsigned_lit_small. lia.
  - exact (gb_slot_chunks_sv_In l off e Hin).
  - symmetry. apply Z_to_bv_bv_unsigned.
  - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
  - cbn [Z.of_N]. lia.
Qed.

Lemma gb_slots_sv_land : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks_sv l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  gb_slots_sv cx W3 ms3 E l.
Proof. intros E pc sr sh l fcs wlo whi extra G. exact (gb_slots_sv_landw E pc sr sh l 0 512 fcs wlo whi extra G). Qed.

(* The frame slots of `gb_body` as slots of the seat. *)
Lemma gb_slots_fr : gslots_fr cx fp W3 ms3 -> gb_slots cx W3 ms3 (gb_fr_slots cx fp).
Proof.
  intros (H18 & H28 & H70 & H78 & H80).
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _).
  pose proof asan_consts as (Hac & _).
  unfold gb_slots, gb_fr_slots, GO_MAC, GO_PREV in *.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [assumption | lia]).
Qed.

(* The frame's atom as the frame's address. *)
Lemma gb_sv_F : forall (E : env) c, gb_E cx fp E -> sv_denot E (SOff GA_F c) = w64 (gF cx fp + c).
Proof.
  intros E c (_ & _ & _ & HFE & _).
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _). pose proof asan_consts as (Hac & _).
  cbn [sv_denot]. rewrite HFE. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The frame slots of `gb_body` as slots of the seat over the frame's atom. *)
Lemma gb_slots_sv_fr : forall (E : env), gb_E cx fp E -> gslots_fr cx fp W3 ms3 ->
  gb_slots_sv cx W3 ms3 E gb_fr_slots_sv.
Proof.
  intros E HE (H18 & H28 & H70 & H78 & H80).
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _). pose proof asan_consts as (Hac & _).
  unfold gb_slots_sv, gb_fr_slots_sv, GO_MAC, GO_PREV in *.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (eapply gb_slot_sv_of_gslot; [eassumption | rewrite (gb_sv_F E _ HE); f_equal; lia | lia]).
Qed.

(* The frame slots of `gb_body` from the slots a landing state holds. *)
Lemma gb_gslots_fr_of :
  (forall off v, In (off, v) (gb_fr_slots cx fp) -> 0 <= v < 2 ^ 64 -> gslot cx W3 ms3 off v) ->
  gslots_fr cx fp W3 ms3.
Proof.
  intros GS.
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _). pose proof asan_consts as (Hac & _).
  unfold gslots_fr, GO_MAC, GO_PREV.
  split; [apply GS; [unfold gb_fr_slots; cbn [In]; tauto | lia]|].
  split; [apply GS; [unfold gb_fr_slots; cbn [In]; tauto | lia]|].
  split; [apply GS; [unfold gb_fr_slots, GO_MAC; cbn [In]; tauto | lia]|].
  split; [apply GS; [unfold gb_fr_slots, GO_PREV; cbn [In]; tauto | lia]|].
  apply GS; [unfold gb_fr_slots; cbn [In]; tauto | lia].
Qed.

(* The frame-slot premise of gb_land_sv, when l holds the frame slots over the frame's atom
   (gb_fr_slots_sv) or as numbers. *)
Lemma gb_fr_slots_sv_in : forall (E : env) l, gb_E cx fp E ->
  (forall p, In p gb_fr_slots_sv -> In p l) ->
  forall off v, In (off, v) (gb_fr_slots cx fp) -> exists e, In (off, e) l /\ sv_denot E e = w64 v.
Proof.
  intros E l HE Hl off v Hin. unfold gb_fr_slots in Hin. cbn [In] in Hin.
  destruct Hin as [Hp|[Hp|[Hp|[Hp|[Hp|[]]]]]]; injection Hp as <- <-;
    [exists (SOff GA_F 0) | exists (SOff GA_F 0) | exists (SOff GA_F GO_MAC) | exists (SOff GA_F GO_PREV)
    | exists (SOff GA_F 0)];
    (split; [apply Hl; unfold gb_fr_slots_sv; cbn [In]; tauto | rewrite (gb_sv_F E _ HE); f_equal; lia]).
Qed.

Lemma gb_fr_slots_lit_in : forall (E : env) l,
  (forall p, In p (gb_fr_slots cx fp) -> In (fst p, SLit (snd p)) l) ->
  forall off v, In (off, v) (gb_fr_slots cx fp) -> exists e, In (off, e) l /\ sv_denot E e = w64 v.
Proof. intros E l Hl off v Hin. exists (SLit v). split; [exact (Hl (off, v) Hin) | reflexivity]. Qed.

(* ---- the frame's objects in scope (GSH_it) ---- *)
(* `struct reac_boxreg prev` at F + 64 (288 bytes): its 36 shadow bytes are 0. *)
Lemma gb_prev_ra : forall o n, gshadow cx fp W3 ms3 GSH_it -> 0 <= o -> o + n <= REG_SIZE ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (gF cx fp + GO_PREV + o) n.
Proof.
  intros o n Hsh Ho Hn x Hx.
  pose proof gb_F_al as Hal.
  assert (Hal8 : gF cx fp mod 8 = 0).
  { pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as Hd. rewrite Hal, Z.add_0_r in Hd.
    rewrite Hd. replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia.
    apply Z.mod_mul. lia. }
  unfold GO_PREV, REG_SIZE in *.
  assert (Hi : 8 <= (x - gF cx fp) / 8 < 44).
  { split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia. }
  exists 0. split; [|left; reflexivity].
  replace x with (gF cx fp + (x - gF cx fp)) by lia.
  rewrite shadow_of_addr_aligned_off by exact Hal8.
  change (shadow_of_addr SHADOW_OFF (gF cx fp)) with (gSH cx fp).
  pose proof (Hsh (Z.to_nat ((x - gF cx fp) / 8))
    ltac:(rewrite gb_GSH_it_len; unfold GB_NSH; lia)) as H.
  rewrite Z2Nat.id in H by lia. rewrite H. f_equal. apply gb_GSH_it_prev. lia.
Qed.

(* `uint8_t mac[6]` at F + 32: its shadow byte (byte 4) is 6. *)
Lemma gb_mac_ra : forall o n, gshadow cx fp W3 ms3 GSH_it -> 0 <= o -> o + n <= 6 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (gF cx fp + GO_MAC + o) n.
Proof.
  intros o n Hsh Ho Hn x Hx.
  pose proof gb_F_al as Hal.
  pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as Hd. rewrite Hal, Z.add_0_r in Hd.
  assert (Hal8 : gF cx fp mod 8 = 0).
  { rewrite Hd. replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia.
    apply Z.mod_mul. lia. }
  unfold GO_MAC in *.
  assert (Hq : (x - gF cx fp) / 8 = 4).
  { symmetry. apply (Z.div_unique (x - gF cx fp) 8 4 (x - gF cx fp - 32)); [left; lia | lia]. }
  assert (Hxm : x mod 8 = x - gF cx fp - 32).
  { symmetry. apply (Z.mod_unique x 8 (8 * (gF cx fp / 64) + 4) (x - gF cx fp - 32)); [left; lia | lia]. }
  exists 6. split; [|right; lia].
  replace x with (gF cx fp + (x - gF cx fp)) by lia.
  rewrite shadow_of_addr_aligned_off by exact Hal8. rewrite Hq.
  change (shadow_of_addr SHADOW_OFF (gF cx fp)) with (gSH cx fp).
  exact (Hsh 4%nat ltac:(rewrite gb_GSH_it_len; unfold GB_NSH; lia)).
Qed.

(* ---- the landing: the engine's symbolic state back as a phase's machine state ---- *)
(* Over any spill chunks and any frame write window, given the frame slots; gb_land_cs (the whole frame
   writable), gb_land (slots as numbers), gb_land_sv and gb_land_svw (slots as expressions) read the frame
   slots from the spill region. *)
Theorem gb_land_csw : forall E pc sr sh scs fwlo fwhi fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh scs fwlo fwhi fcs wlo whi extra G) (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  sr_get sr 18 = SOff GA_SB 0 -> sr_get sr 24 = SOff GA_FSH 0 ->
  gslots_fr cx fp W3 ms3 ->
  length sh = GB_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  gb_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh scs fwlo fwhi fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24 SLFR Hlen Hsh256
    Hgarr.
  pose proof (gb_base_sp E HE) as Ub2.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof gb_sh_range as (Hs0 & Hs1).
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 gb_fin) as (_ & _ & Hfia & Hflt).
  rewrite gb_flag_addr_eq in Hfia, Hflt.
  assert (HflZ : 0 <= gFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & Husp & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE & _).
  cbn [YP09.base_val] in Ub2.
  assert (Rsaved : YP09.region_ok SEGS E M3 gb_saved_region).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 0%nat _ HS eq_refl). }
  assert (Rframe : YP09.region_ok SEGS E M3 (gb_frame_region_w fwlo fwhi fcs)).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 2%nat _ HS eq_refl). }
  assert (Rshadow : YP09.region_ok SEGS E M3 (gb_shadow_region wlo whi (gb_sh_chunks sh))).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 3%nat _ HS eq_refl). }
  assert (SAV : forall (n : nat) (r : bv 5) od,
    Z.of_nat n = bv_unsigned r -> (n < 33)%nat ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) gb_saved_chunks ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) + od) =
      Some (bv_unsigned (getr (c_regs cx) r))).
  { intros n r od Hn Hlt Hin.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|apply u64_range].
    apply (field_of_region E M3 GA_SP (spZ (c_regs cx)) gb_saved_chunks (-104) 0 0 0 od 8%N
             (SOff n 0) (bv_unsigned (getr (c_regs cx) r)) Rsaved Ub2 Hin).
    - rewrite gb_sv_SOff0, (AG n Hlt), (HE0 n r Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia. }
  assert (SHW : gshadow cx fp W3 ms3 sh).
  { intros i Hi.
    assert (Hb : 0 <= nth i sh 0 < 256).
    { rewrite Forall_forall in Hsh256. apply Hsh256. apply nth_In. exact Hi. }
    apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [|exact Hb].
    apply (field_of_region E M3 GA_FSH (gSH cx fp) (gb_sh_chunks sh) 0
             (fs_frame_bytes GB_CID / 8) wlo whi (Z.of_nat i) 1%N (SLit (nth i sh 0))
             (nth i sh 0) Rshadow).
    - rewrite HFSE. apply unsigned_lit_small. lia.
    - apply gb_sh_chunks_In. exact Hi.
    - reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia. }
  assert (FLG : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8)
                = Some (gFL cx fp)).
  { assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact HflZ].
    replace (gF cx fp + fs_frame_bytes GB_CID - 8) with (gF cx fp + (fs_frame_bytes GB_CID - 8)) by lia.
    apply (field_of_region E M3 GA_F (gF cx fp) (fcs ++ [YP09.mkChunk (fs_frame_bytes GB_CID - 8)
             (CVal 8 (SOff GA_FL 0))]) 0 (fs_frame_bytes GB_CID) fwlo fwhi
             (fs_frame_bytes GB_CID - 8) 8%N (SOff GA_FL 0) (gFL cx fp) Rframe).
    - rewrite HFE. apply unsigned_lit_small. lia.
    - apply in_or_app. right. left. reflexivity.
    - rewrite gb_sv_SOff0, HFLE. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. exact HflZ.
    - cbn [Z.of_N]. lia. }
  pose proof HS as (Hfr & Hpcv & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
  unfold gb_ssw, abs_ss, setpc in Hpcv, Hresv, Hregs.
  cbn [ss_pc ss_regs ss_resv resv_denot restrict
       ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs]
    in Hfr, Hpcv, Hpend, Hresv, Hfcsr, Hrom, Hregs.
  unfold gb_body.
  split; [rewrite Hpcv; reflexivity|].
  split; [exact Hresv|]. split; [exact Hpend|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfcsr|].
  split.
  { unfold gregs.
    split; [rewrite (Hregs (2%bv : bv 5)), Hr2, gb_sv_SOff0, Hsp1E; reflexivity|].
    split; [rewrite (Hregs (8%bv : bv 5)), Hr8, gb_sv_SOff0, (AG GA_SP ltac:(unfold GA_SP; lia));
            rewrite <- Husp; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [rewrite (Hregs (9%bv : bv 5)), Hr9, gb_sv_SOff0, Hsp1E; reflexivity|].
    split; [rewrite (Hregs (3%bv : bv 5)), Hr3, gb_sv_SOff0, (AG 3%nat ltac:(lia));
            exact (HE0 3%nat (3%bv : bv 5) eq_refl)|].
    split; [rewrite (Hregs (4%bv : bv 5)), Hr4, gb_sv_SOff0, (AG 4%nat ltac:(lia));
            exact (HE0 4%nat (4%bv : bv 5) eq_refl)|].
    split; [rewrite (Hregs (18%bv : bv 5)), Hr18, gb_sv_SOff0, Hsb; reflexivity|].
    rewrite (Hregs (24%bv : bv 5)), Hr24, gb_sv_SOff0, HFSE. reflexivity. }
  split.
  { unfold gsaved. split.
    - replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) + -8) by lia.
      exact (SAV 1%nat (1%bv : bv 5) (-8) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(unfold gb_saved_chunks; cbn [In]; tauto)).
    - assert (SJ : forall (j : Z) (n : nat) (od : Z),
        Z.of_nat n = bv_unsigned (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) -> (n < 33)%nat ->
        In (YP09.mkChunk od (CVal 8 (SOff n 0))) gb_saved_chunks ->
        od = -16 - 8 * j ->
        rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16 - 8 * j) =
          Some (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
      { intros j n od Hn Hlt Hin Hod.
        replace (spZ (c_regs cx) - 16 - 8 * j) with (spZ (c_regs cx) + od) by lia.
        exact (SAV n (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) od Hn Hlt Hin). }
      intros j Hj.
      assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                      j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 0 8%nat (-16));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 1 9%nat (-24));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 2 18%nat (-32));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 3 19%nat (-40));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 4 20%nat (-48));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 5 21%nat (-56));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 6 22%nat (-64));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 7 23%nat (-72));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 8 24%nat (-80));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 9 25%nat (-88));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 10 26%nat (-96));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]|].
      subst j. apply (SJ 11 27%nat (-104));
        [vm_compute; reflexivity | lia | unfold gb_saved_chunks; cbn [In]; tauto | lia]. }
  split; [exact SHW|]. split; [exact Hlen|]. split; [exact FLG|]. split; [exact SLFR | exact Hgarr].
Qed.

Theorem gb_land_cs : forall E pc sr sh scs fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh scs fcs wlo whi extra G) (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  sr_get sr 18 = SOff GA_SB 0 -> sr_get sr 24 = SOff GA_FSH 0 ->
  gslots_fr cx fp W3 ms3 ->
  length sh = GB_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  gb_body cx fp pc W3 ms3 sh.
Proof. intros E pc sr sh scs fcs wlo whi extra G. exact (gb_land_csw E pc sr sh scs 0 512 fcs wlo whi extra G). Qed.

Theorem gb_land : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  sr_get sr 18 = SOff GA_SB 0 -> sr_get sr 24 = SOff GA_FSH 0 ->
  (forall p, In p (gb_fr_slots cx fp) -> In p l) ->
  length sh = GB_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  gb_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24 Hfrl.
  apply (gb_land_cs E pc sr sh (gb_slot_chunks l) fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24).
  apply gb_gslots_fr_of. intros off v Hin Hv.
  exact (gb_gslot_land E pc sr sh l fcs wlo whi extra G off v HE HS (Hfrl _ Hin) Hv).
Qed.

(* The frame slots may be held as any expressions of their values (gb_fr_slots_sv_in: over the frame's atom,
   gb_fr_slots_lit_in: as numbers). *)
Theorem gb_land_sv : forall E pc sr sh l fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ss cx fp pc sr sh (gb_slot_chunks_sv l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  sr_get sr 18 = SOff GA_SB 0 -> sr_get sr 24 = SOff GA_FSH 0 ->
  (forall off v, In (off, v) (gb_fr_slots cx fp) -> exists e, In (off, e) l /\ sv_denot E e = w64 v) ->
  length sh = GB_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  gb_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24 Hfrl.
  pose proof (gb_slots_sv_land E pc sr sh l fcs wlo whi extra G HE HS) as HSL.
  apply (gb_land_cs E pc sr sh (gb_slot_chunks_sv l) fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24).
  apply gb_gslots_fr_of. intros off v Hin Hv.
  destruct (Hfrl off v Hin) as (e & Hine & He).
  exact (gb_gslot_of_sv E l off e v HSL Hine He Hv).
Qed.

Theorem gb_land_svw : forall E pc sr sh l fwlo fwhi fcs wlo whi extra G,
  gb_E cx fp E ->
  st_ok_pi SEGS VAL E (gb_ssw cx fp pc sr sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  sr_get sr 18 = SOff GA_SB 0 -> sr_get sr 24 = SOff GA_FSH 0 ->
  (forall off v, In (off, v) (gb_fr_slots cx fp) -> exists e, In (off, e) l /\ sv_denot E e = w64 v) ->
  length sh = GB_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  gb_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh l fwlo fwhi fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24 Hfrl.
  pose proof (gb_slots_sv_landw E pc sr sh l fwlo fwhi fcs wlo whi extra G HE HS) as HSL.
  apply (gb_land_csw E pc sr sh (gb_slot_chunks_sv l) fwlo fwhi fcs wlo whi extra G HE HS
           Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr24).
  apply gb_gslots_fr_of. intros off v Hin Hv.
  destruct (Hfrl off v Hin) as (e & Hine & He).
  exact (gb_gslot_of_sv E l off e v HSL Hine He Hv).
Qed.

(* ---- the frame across a run, with no frame write window ---- *)
(* With fwlo = fwhi the phase writes no frame byte, so no byte of [F, F + 512) is in the write range of the
   seat's regions, and `frame_of` (what a run gives) keeps every one of them: prev, mac and the frame's header
   carry from the seat state to the run's memory. *)
Lemma gb_frame_not_wrange : forall E sh scs fwlo fcs wlo whi extra a,
  gb_E cx fp E ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) = true ->
  YP09.pairwise_disjoint E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) ->
  gF cx fp <= a < gF cx fp + 512 ->
  ~ in_wrange E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) a.
Proof.
  intros E sh scs fwlo fcs wlo whi extra a HE Hwf Hpd Ha.
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _). pose proof asan_consts as (Hac & _).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  pose proof HE as (_ & _ & _ & HFE & _).
  assert (Ub516 : YP09.base_val E (Some GA_F) = gF cx fp)
    by (cbn [YP09.base_val]; rewrite HFE; apply unsigned_lit_small; lia).
  assert (Heq : gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra =
    [gb_saved_region; gb_spill_region scs] ++ gb_frame_region_w fwlo fwlo fcs
    :: (gb_shadow_region wlo whi (gb_sh_chunks sh) :: gb_obj_regions ++ extra)) by reflexivity.
  rewrite Heq in Hwf, Hpd |- *.
  apply (gb_not_wrange E _ _ _ a Hwf Hpd).
  - unfold gb_frame_region_w, set_window. cbn [YP09.r_wlo YP09.r_whi]. lia.
  - unfold gb_frame_region_w, set_window, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Ub516, Hfb. lia.
Qed.

Lemma gb_frame_kept : forall E sh scs fwlo fcs wlo whi extra (m m' : word -> option byte) a,
  gb_E cx fp E ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) = true ->
  YP09.pairwise_disjoint E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) ->
  frame_of E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) m m' ->
  gF cx fp <= a < gF cx fp + 512 ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros E sh scs fwlo fcs wlo whi extra m m' a HE Hwf Hpd HF Ha.
  pose proof gb_F_facts as (HF0 & HFc & _ & _ & _). pose proof asan_consts as (Hac & _).
  apply HF. rewrite unsigned_lit_small by lia.
  exact (gb_frame_not_wrange E sh scs fwlo fcs wlo whi extra a HE Hwf Hpd Ha).
Qed.

Lemma gb_frame_kept_aview : forall E sh scs fwlo fcs wlo whi extra (H : word -> bool)
  (m m' : word -> option byte) a,
  gb_E cx fp E ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) = true ->
  YP09.pairwise_disjoint E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) ->
  frame_of E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) (mrestrict H m) (mrestrict H m') ->
  gF cx fp <= a < gF cx fp + 512 ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E sh scs fwlo fcs wlo whi extra H m m' a HE Hwf Hpd HF Ha.
  apply (aview_eq_of SEGS).
  exact (gb_frame_kept E sh scs fwlo fcs wlo whi extra (mrestrict H m) (mrestrict H m') a HE Hwf Hpd HF Ha).
Qed.

(* The frame's copy `prev` of the table (F + 64 .. F + 351) carries across a run. *)
Lemma gb_gprev_kept : forall E sh scs fwlo fcs wlo whi extra (ms ms' : machine_state) bs,
  gb_E cx fp E ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) = true ->
  YP09.pairwise_disjoint E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) ->
  frame_of E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra)
    (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms')) ->
  gprev cx fp W3 ms bs -> gprev cx fp W3 ms' bs.
Proof.
  intros E sh scs fwlo fcs wlo whi extra ms ms' bs HE Hwf Hpd HF Hp i Hi.
  rewrite (gb_frame_kept_aview E sh scs fwlo fcs wlo whi extra (w_H W3) (ms_mem ms) (ms_mem ms')
    (gF cx fp + GO_PREV + i) HE Hwf Hpd HF ltac:(unfold GO_PREV, REG_SIZE in *; lia)).
  exact (Hp i Hi).
Qed.

(* Any array of the frame (mac at F + 32, the header at F .. F + 23) carries across a run. *)
Lemma gb_frame_garr8_kept : forall E sh scs fwlo fcs wlo whi extra (m m' : word -> option byte) off L,
  gb_E cx fp E ->
  YP09.regions_wf (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) = true ->
  YP09.pairwise_disjoint E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra) ->
  frame_of E (gb_regionsw cx fp sh scs fwlo fwlo fcs wlo whi extra)
    (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  0 <= off -> off + Z.of_nat (length L) <= 512 ->
  garr8 SEGS (mrestrict (w_H W3) m) (gF cx fp + off) L ->
  garr8 SEGS (mrestrict (w_H W3) m') (gF cx fp + off) L.
Proof.
  intros E sh scs fwlo fcs wlo whi extra m m' off L HE Hwf Hpd HF Hoff Hlen Hg j Hj.
  destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros kk Hk. assert (kk = 0)%nat by lia. subst kk.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (gF cx fp + off + Z.of_nat j)
    (gb_frame_kept_aview E sh scs fwlo fcs wlo whi extra (w_H W3) m m' (gF cx fp + off + Z.of_nat j)
       HE Hwf Hpd HF ltac:(lia))).
  exact Hv0.
Qed.

(* ---- the call chain this call hands to the functions it calls ---- *)
(* cgif lib/A/ACf5.v:172 `rt_chain`: the caller's own frame goes on the chain when it fits under the layout's
   top, and its two words are where the chain wants them. *)
Lemma gb_achain : forall (rd' : reader) sp',
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
     rd' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword rd' (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain (c_ly cx) rd' sp' (spZ (c_regs cx)) (gch cx).
Proof.
  intros rd' sp' Hk H8 H16 Hsp'.
  destruct HB as (HPRE & _).
  pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
    destruct Hal16 as [q Hq]. exists (2 * q). lia. }
  unfold gch.
  destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd'
             (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hk);
      [ replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact H8
      | replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16) by lia; exact H16
      | exact Hra4 | lia | exact Hal8 | lia | exact Hsp' ].
  - left. split; [right; left; lia | reflexivity].
Qed.

(* ---- a call that leaves this phase's own memory alone ---- *)
(* The journal of a call made from the realigned stack pointer that takes no frame of its own and leaves the
   blocks as it found them keeps every byte this phase's facts speak about. *)
Lemma gb_keep_call : forall rs STK1 memc mdc mem2 md2 k1,
  alloc_ceiling <= c_sp1 cx ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun r => exists n, In (fst r, n) (ablocks B ly3 S3) /\ 0 <= snd r <= req_size n) rs ->
  ajournal SEGS B STK1 (c_sp1 cx) [] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  gb_keep rs memc mem2.
Proof.
  intros rs STK1 memc mdc mem2 md2 k1 Hceil Hbl Hrs HJ1 a Ha.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct HB as (_ & _ & _ & Hpn & _).
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp).
  { pose proof gb_F_facts as (_ & _ & _ & _ & HSHeq). unfold shadow_addr. rewrite HSHeq. reflexivity. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) (Hbl _ _ Hin) (Hbl _ _ Hin)); [lia | apply inFP_nil].
  - apply (F4 GB_CID fp a gb_fin); [|apply inFP_nil].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite gb_frame_addr_eq. lia.
  - apply (F4 GB_CID fp a gb_fin); [|apply inFP_nil].
    right. unfold in_zr. cbn [fst snd]. rewrite gb_frame_addr_eq, Hsa. exact Ha.
  - apply Exists_exists in Ha as (r & Hr & Hb).
    rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as (n & Hin & Hn).
    replace a with (fst r + (a - fst r)) by lia.
    apply (F2 (fst r) n (a - fst r) Hin Hin); [lia | apply inFP_nil].
Qed.

(* ---- a phase's facts across such a call ---- *)
Lemma gb_map_length : forall (f : byte -> Z) (xs : list byte), length (map f xs) = length xs.
Proof. intros f xs. induction xs as [|x xs IHx]; cbn [map length]; [reflexivity | rewrite IHx; reflexivity]. Qed.

Lemma gb_gsaved_keep : forall rs (ms ms' : machine_state),
  gb_keep rs (ms_mem ms) (ms_mem ms') -> gsaved cx W3 ms -> gsaved cx W3 ms'.
Proof.
  intros rs ms ms' Hk (Hra & Hsj).
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  split.
  - apply (gb_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hra].
  - intros j Hj. apply (gb_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
      [intros i Hi; left; lia | exact (Hsj j Hj)].
Qed.

Lemma gb_gshadow_keep : forall rs (ms ms' : machine_state) sh,
  gb_keep rs (ms_mem ms) (ms_mem ms') ->
  Z.of_nat (length sh) <= fs_frame_bytes GB_CID / 8 ->
  gshadow cx fp W3 ms sh -> gshadow cx fp W3 ms' sh.
Proof.
  intros rs ms ms' sh Hk Hlen Hs i Hi.
  rewrite (Hk (gSH cx fp + Z.of_nat i)); [exact (Hs i Hi)|].
  right; right; right; left. lia.
Qed.

Lemma gb_gslot_keep : forall rs (ms ms' : machine_state) off v,
  gb_keep rs (ms_mem ms) (ms_mem ms') -> 0 <= off -> off <= 0x90 ->
  gslot cx W3 ms off v -> gslot cx W3 ms' off v.
Proof.
  intros rs ms ms' off v Hk H0 H1 Hv.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  apply (gb_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hv].
Qed.

Lemma gb_slots_keep : forall rs (ms ms' : machine_state) l,
  gb_keep rs (ms_mem ms) (ms_mem ms') ->
  Forall (fun p => 0 <= fst p <= 0x90) l ->
  gb_slots cx W3 ms l -> gb_slots cx W3 ms' l.
Proof.
  intros rs ms ms' l Hk Hoff Hl. unfold gb_slots in *.
  rewrite Forall_forall in Hoff, Hl |- *. intros p Hp.
  destruct (Hl p Hp) as [Hs Hr]. pose proof (Hoff p Hp) as Ho.
  split; [|exact Hr].
  exact (gb_gslot_keep rs ms ms' (fst p) (snd p) Hk ltac:(lia) ltac:(lia) Hs).
Qed.

Lemma gb_slots_sv_keep : forall rs (ms ms' : machine_state) (E : env) l,
  gb_keep rs (ms_mem ms) (ms_mem ms') ->
  Forall (fun p => 0 <= fst p <= 0x90) l ->
  gb_slots_sv cx W3 ms E l -> gb_slots_sv cx W3 ms' E l.
Proof.
  intros rs ms ms' E l Hk Hoff Hl.
  pose proof gb_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  unfold gb_slots_sv in *. rewrite Forall_forall in Hoff, Hl |- *. intros p Hp.
  pose proof (Hoff p Hp) as Ho.
  apply (gb_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact (Hl p Hp)].
Qed.

Lemma gb_gslots_fr_keep : forall rs (ms ms' : machine_state),
  gb_keep rs (ms_mem ms) (ms_mem ms') -> gslots_fr cx fp W3 ms -> gslots_fr cx fp W3 ms'.
Proof.
  intros rs ms ms' Hk (H18 & H28 & H70 & H78 & H80).
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H18]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H28]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H70]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H78]|].
  apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H80].
Qed.

Lemma gb_gslots_r_keep : forall rs (ms ms' : machine_state) r fab,
  gb_keep rs (ms_mem ms) (ms_mem ms') -> gslots_r cx fp W3 ms r fab -> gslots_r cx fp W3 ms' r fab.
Proof.
  intros rs ms ms' r fab Hk (H10 & H20 & H38 & H40 & H50 & H60).
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H10]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H20]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H38]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H40]|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H50]|].
  apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H60].
Qed.

Lemma gb_gcursor_keep : forall rs (ms ms' : machine_state) pos,
  gb_keep rs (ms_mem ms) (ms_mem ms') -> gcursor cx W3 ms pos -> gcursor cx W3 ms' pos.
Proof.
  intros rs ms ms' pos Hk (Hp & H88 & H90).
  split; [exact Hp|].
  split; [apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H88]|].
  apply (gb_gslot_keep rs ms ms' _ _ Hk); [lia | lia | exact H90].
Qed.

Lemma gb_flag_keep : forall rs (ms ms' : machine_state),
  gb_keep rs (ms_mem ms) (ms_mem ms') ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp).
Proof.
  intros rs ms ms' Hk Hv.
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  apply (gb_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
    [intros i Hi; right; right; left; lia | exact Hv].
Qed.

(* The frame's copy `prev` of the table, at F + 64 .. F + 352, inside the frame. *)
Lemma gb_gprev_keep : forall rs (ms ms' : machine_state) bs,
  gb_keep rs (ms_mem ms) (ms_mem ms') -> gprev cx fp W3 ms bs -> gprev cx fp W3 ms' bs.
Proof.
  intros rs ms ms' bs Hk Hp i Hi.
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  rewrite (Hk (gF cx fp + GO_PREV + i)); [exact (Hp i Hi)|].
  right; right; left. unfold GO_PREV, REG_SIZE in *. lia.
Qed.

Lemma gb_input_keep : forall rs (ms ms' : machine_state),
  gb_keep rs (ms_mem ms) (ms_mem ms') ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)).
Proof.
  intros rs ms ms' Hk Hg.
  apply (gb_garr8_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [|exact Hg].
  intros i Hi. rewrite gb_map_length in Hi. right; left. unfold c_n. lia.
Qed.

(* The registry r, a block the phase holds. *)
Lemma gb_greg_keep : forall rs (ms ms' : machine_state) r bs,
  gb_keep rs (ms_mem ms) (ms_mem ms') -> In (r, REG_SIZE) rs ->
  greg B ly3 S3 W3 ms r bs -> greg B ly3 S3 W3 ms' r bs.
Proof.
  intros rs ms ms' r bs Hk Hin (Hb & Hl & Hbytes).
  split; [exact Hb|]. split; [exact Hl|].
  intros i Hi.
  rewrite (Hk (r + i)); [exact (Hbytes i Hi)|].
  right; right; right; right. apply Exists_exists. exists (r, REG_SIZE).
  split; [exact Hin | cbn [fst snd]; lia].
Qed.

End e.

End d.

End c.
End b.
End a.

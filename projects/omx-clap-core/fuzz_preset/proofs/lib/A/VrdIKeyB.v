(* fuzz_preset, slice S5b, lane A2KeyB (a Theorem Labs lane): the THREE PIECES the donor VrdIKey.v never proved of parse_items'
   OBJECT KEY PATH in image A' (asan 1be0f53d, the #102 pins), rows 195..209 and 305..309 of parse_items
   (A' 0x8759c .. 0x875d4 and 0x87754 .. 0x87764, listing slots 6127 .. 6141 and 6237 .. 6241), and the assembly of
   VrdIElem.v's tvrd_ikey_aG from VrdIKey.v's segment lemmas.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Every callee (fuzz_free) is its record text, taken as a named
   Section hypothesis; every neighbouring segment is a lemma of VrdIKey.v or a boundary state of VrdIElem.v.

   THE THREE PIECES.
   1. C3, rows 195..209 (vk_c3_step_P): the colon test. Row 195 reloads q->p, row 198 compares it with the text end,
      rows 199..203 read the byte at p and test it against 0x3a (':'), rows 206..207 store q->p := p + 1 and the arm
      falls through to row 210 = A_ISLOT_SLOT. p = end, or a byte that is not the colon, branches to row 305.
   2. REFUSE-B, rows 305..309: `ld a0, 0(a0)` reloads the key out of the slot keys + 8 n (a0, with a2 its shadow
      address, both set by C2 at rows 161 / 163 and carried by vk_w2 / vk_c3 - the interface change this lane found),
      `jal fuzz_free` gives the key back, row 309 sets s2 = -1 and the arm joins the epilogue at row 310 = A_IEPI_SLOT.
      The exit is on a GRANTED prefix (EFree is no call, so ip_ok does not move), so its OUTCOME is
      VrdCallPos.vc_outc_granted; the key leaves D by VrdLedgerEv.vle_free_D.
   3. The assembly: tvrd_ikey_aG from vk_arr_P / vk_c0_P / vk_w1_loop_P / vk_c1_step_P / vk_call_step_P /
      vk_c2K_step_P / vk_w2_loop_P / vk_c2R_step_P / vk_refA_exit and the two pieces above.

   THE MODEL. At vk_key the continuation is vk_kont d n cap acc f z nm (rest_atR tb text p), i.e.
   jbind (vk_kname z nm (rest at p)) (fun '(name1, y1) => vrd_jval d true n cap acc f name1 y1), and vk_kname tests
   PjGrammar.skip of the rest: a colon continues with vrd_jval at the rest after it (no event), anything else gives
   the block back (jfree (sblock z), ONE EFree event, no ok eaten) and refuses. So the colon arm is
   VrdIElem.vrd_islot_a at p + 1 and the other arm is vrd_iexit_a (-1) with tr' = tr ++ [EFree k].
   THE FREE LIST (the kit's cut, the batch kit's layer): vk_key carries the call's free list at VrdIKey.vk_jfk (vk_kname's twin over
   jfl's body after the key); the colon arm continues at VrdIElem.vrd_jfvk (vkb_jfk_colon), the refusal arm frees the
   key, so the exit's order list is the completed slots' list then the arrays (vkb_jfk_refuse, VrdIStep.vi_part_fo).
   THE FREE'S TRACE (the kit's cut, PRH_FnAlloc.v tfuzz_free_specX): `admits (as_universe B) (call_trace ..) S`, from
   prh_cw_ok at q - 8: A''s code word (clause 4a, a fixed trace) or a trace of CW (clause 4b, admitted from the room
   the position has for CW); the post is budgeted at that one trace and goes back to the journal's budget CW.

   SET: the kit's cut 7cdbb61b5fa0 (PRH_Base.v ef7c8ca98529, PRH_FnParse.v f0d92dcec7e9, PRH_FnReader.v f1ae32e3b2cd,
   PRH_FnAlloc.v 4d8aeba047e5, PRH_Reader.v 4266e709561a), over the relocated A' listing (lane P102Reloc2,
   a working branch 43e0d7669c5b). Build (route of record, pins102): zfb-targets with PAU pau-preset-102 and
   facts 8f3e7e1a07f1 - never cb, whose facts predate the A' image.
   Numerals: listing slots (DERIVED, VrdIElem.v), 58 = ':' (the grammar's byte, PjGrammar), 8 / 24 / 144 (LENGTH:
   a word, the cursor, parse_items' frame). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun
  PresetReqAt PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc VrdFrame VrdIElem
VrdCurStore VrdIFd VrdArm VrdCallKeep VrdIStep VrdLedgerStep VrdCallPos VrdLedgerEv VrdSlotStore VrdIKey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdPro.
(* the re-hiding move's SRr' / wle' (YA0nH, YSRrG) and preset's zone (YGcfRehidePost.RZ_cf); the threaded hull
   budget *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- THE MODEL SIDE, pure: what vk_kont does at the colon test. No Section variable is used here. ---- *)

(* the colon is not white space, so PjGrammar.skip stops at it *)
Lemma vkb_skip_colon : forall r, PjGrammar.skip (58 :: r) = 58 :: r.
Proof. intros r. reflexivity. Qed.

(* a byte that is not white space stops skip as well *)
Lemma vkb_skip_nonws : forall b r, PjGrammar.ws b = false -> PjGrammar.skip (b :: r) = b :: r.
Proof. intros b r H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

(* THE COLON ARM: the name is done and the continuation is the VALUE at the rest after the colon, with no event *)
Lemma vkb_kont_colon : forall d n cap1 acc f z nm r r', r = 58 :: r' ->
  vk_kont d n cap1 acc f z nm r = vrd_jval d true n cap1 acc f nm r'.
Proof.
  intros d n cap1 acc f z nm r r' ->.
  apply functional_extensionality. intros ok.
  unfold vk_kont, vk_kname, PjGrammar.jbind. rewrite vkb_skip_colon.
  change (58 =? 58) with true. cbn beta iota. unfold PjGrammar.jret.
  destruct (vrd_jval d true n cap1 acc f nm r' ok) as [[a t] o]. reflexivity.
Qed.

(* THE REFUSAL ARM: the stored key's block is given back (one EFree, no ok eaten) and the item refuses *)
Lemma vkb_kont_refuse : forall d n cap1 acc f z nm r,
  (PjGrammar.skip r = [] \/ exists c r1, PjGrammar.skip r = c :: r1 /\ c <> 58) ->
  forall ok, vk_kont d n cap1 acc f z nm r ok = (None, [PjGrammar.EFree (PjGrammar.sblock z)], ok).
Proof.
  intros d n cap1 acc f z nm r Hc ok.
  unfold vk_kont, vk_kname, PjGrammar.jbind.
  destruct Hc as [Hs | (c & r1 & Hs & Hne)]; rewrite Hs.
  - unfold PjGrammar.jfree, PjGrammar.jrefuse. cbn beta iota. reflexivity.
  - rewrite (proj2 (Z.eqb_neq c 58) Hne). cbn beta iota.
    unfold PjGrammar.jfree, PjGrammar.jrefuse. cbn beta iota. reflexivity.
Qed.

(* THE FREE LIST AT THE COLON TEST (the kit's cut, VrdIKey.vk_jfk, vk_kname's twin over jfl's body after the key): the
   colon continues with jfl's body after the key (VrdIElem.vrd_jfvk) at the rest after it; anything else frees the
   key, so the call's free list is the completed slots' list then the arrays (PresetReqAt.arrz) *)
Lemma vkb_jfk_colon : forall f d n cap1 af lk r r' ok, r = 58 :: r' ->
  vk_jfk f d n cap1 af lk r ok = vrd_jfvk f d true n cap1 af lk r' ok.
Proof.
  intros f d n cap1 af lk r r' ok ->. unfold vk_jfk. rewrite vkb_skip_colon. reflexivity.
Qed.

Lemma vkb_jfk_refuse : forall f d n cap1 af lk r ok,
  (PjGrammar.skip r = [] \/ exists c r1, PjGrammar.skip r = c :: r1 /\ c <> 58) ->
  vk_jfk f d n cap1 af lk r ok = af ++ PresetReqAt.arrz true cap1.
Proof.
  intros f d n cap1 af lk r ok Hc. unfold vk_jfk.
  destruct Hc as [Hs | (c & r1 & Hs & Hne)]; rewrite Hs; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq c 58) Hne). reflexivity.
Qed.

(* the trace of the refusal arm: one EFree, no call, nothing held at its end *)
Lemma vkb_free_calls : forall k, PjGrammar.calls [PjGrammar.EFree k] = 0%nat.
Proof. intros k. reflexivity. Qed.

Lemma vkb_free_held : forall k, PjGrammar.held [PjGrammar.EFree k] = - Z.of_nat k.
Proof. intros k. cbn [PjGrammar.held PjGrammar.held_ev]. lia. Qed.

(* the heap event of one EFree, at the instance's head (HI_head: cf_head = PresetReqAt.HEAD) *)
Lemma vkb_rd_hevs_free : forall k,
  PresetReqAt.rd_hevs [PjGrammar.EFree k] = [PresetReqAt.HFr (Z.of_nat k + PresetReqAt.HEAD)].
Proof. intros k. reflexivity. Qed.

(* the live requests across one EFree: the freed request leaves the multiset *)
Lemma vkb_hlive_free : forall s k,
  PresetReqAt.hlive_from s (PresetReqAt.rd_hevs [PjGrammar.EFree k]) =
  PresetReqAt.rm1 (Z.of_nat k + PresetReqAt.HEAD) s.
Proof. intros s k. reflexivity. Qed.

(* the live class-24 count of an allocator state IS the room view's count over its live requests: ccnt24 reads
   map snd (blocks S), which is PresetRoom.rs_live (YGcfRoom.room_of_cf S) by definition, and PresetRoom.ccnt c is
   PresetReqAt.cnt (PresetRoom.in_cls c). One conversion, so fuzz_free's class-24 entry premise is the shape the
   entry conjunct of vrd_ient_ok and PresetRun.pkR speak (CfRoomLivePreset.preset_ccnt24 says the same; it is not
   Required here, to keep this file's closure at VrdIKey's). *)
Lemma vkb_ccnt24_cnt : forall S,
  YGcfRoomLive.ccnt24 S =
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))).
Proof. intros S. reflexivity. Qed.

(* a count is stable under a permutation of the live multiset (PresetReqAt.cnt_perm, in the room view's words) *)
Lemma vkb_cnt_perm : forall (f : Z -> bool) a b, Permutation a b -> PresetReqAt.cnt f a = PresetReqAt.cnt f b.
Proof. intros f a b H. exact (PresetReqAt.cnt_perm f a b H). Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {HL : Z}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation PLA := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
#[local] Notation VAL := (@pa_val _ A_prog_listing PAI).
#[local] Notation BASE := (@pa_val _ A_prog_listing PAI A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable HW : 8 <= cf_head.
Variable PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis Hfr144 : pi_frame F_parse_items = 144.
Hypothesis Hs0c : pi_s0cur F_parse_items = Some 0.
Hypothesis Hs0ps : pi_s0cur F_parse_string = Some 0.
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
Hypothesis H_fuzz_free : forall fxP : YK11.FPState, tfuzz_free_specX (fx := fxP) B ARx SK.
Hypothesis H_ffret : In (A_IPC 6241) (prh_free_sites F_parse_items).

Definition VKB_REFB_SLOT : nat := 6237%nat.
Definition VKB_FFCALL_SLOT : nat := 6240%nat.

Lemma vkb_ff_slot_ceil : bv_unsigned (Z_to_bv 64 (BASE + 24964)) < YM05.alloc_ceiling.
Proof.
  pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAI) 24964 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
  rewrite unsigned_lit_small; [exact H|]. rewrite vi_base. unfold A_prog_base. lia.
Qed.


(* VrdIKey.v's two run side-goal tactics (vk_ra_byte / vk_awr) are Section-local there, so this file carries its
   own copies under its own names: the byte's shadow range from src_rd's garr8, and the store into the cursor's p
   word, which lies in the caller window the journal grants. *)
Ltac vkb_ra_byte Hrat UB U32 := cbn [ms_mem mkst restrict]; rewrite UB, U32; intros y Hy; apply Hrat; lia.
Ltac vkb_ra_byte_ro Hrat UB U32 :=
  cbn [ms_mem mkst restrict];
  repeat match goal with HF : frame_of _ ?rs ?m ?m' |- context [?m'] =>
    rewrite (vk_frame_ro_gen _ rs m m'
      ltac:(let rs' := eval vm_compute in rs in change rs with rs'; repeat constructor; cbn; lia) HF) end;
  rewrite UB, U32; intros y Hy; apply Hrat; lia.
Ltac vkb_awr_ro :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs';
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end.
Ltac vkb_side_ro Hrat UB U32 := first [ vkb_ra_byte_ro Hrat UB U32 | vkb_awr_ro ].
Ltac vkb_awr1 E8u :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  eapply awr_ok_cons_gen;
  [ reflexivity | cbn [ew ewset Nat.eqb]; exact E8u
  | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia
  | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ].
Ltac vkb_awr E8u HSTK :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  eapply awr_ok_cons_gen;
  [ reflexivity | cbn [ew ewset Nat.eqb]; exact E8u
  | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia
  | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ].

(* VrdIKey.vk_key's model and the batch kit's conjuncts BY NAME (its last ones: the continuation at vk_kont, and the kit's cut's batch kit
   layer after the key - cap = ncap (S n), the members' caps, the order list with the key's block as its extra block,
   the call's free list at vk_jfk), so no proof below reads vk_key positionally past its fixed conjuncts *)
Lemma vkb_key_parts : forall E P x k nm, vk_key B ARx SK E P x k nm ->
  (exists z, ip_cont P = vk_kont (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) z nm
                           (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
              PjGrammar.sblock z = Z.to_nat k) /\
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [(x, k)] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vk_jfk (ip_f P) (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af [k + cf_head]
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).
Proof.
  intros E P x k nm HKY.
  destruct HKY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                   (z & Hcont & Hsz & Hcap1 & Hinc & af & Hfo & Hfl)).
  split; [exists z; split; [exact Hcont | exact Hsz]|].
  split; [exact Hcap1|]. split; [exact Hinc|]. exists af. split; [exact Hfo | exact Hfl].
Qed.

(* ---- the C3 seat: the cursor (writable: row 209 stores q->p) and the byte at p, over vk_sr0's registers. It is
   vk_seatWg's state without its three register rebindings: at row 195 no register holds p yet (row 197 loads it out
   of the cursor), and a3 / a0 / a2 are the plain atoms vk_c3 pins. ---- *)
Definition vkb_ssC (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) vk_sr0 [vk_cur_region true; vk_byte_region] None vk_factsW.

Lemma vkb_seatC : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en b (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b -> 0 <= b < 256 -> (p + 1 <= q \/ q + 24 <= p) ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EW regs p en b) (vkb_ssC k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SH0 (vk_EW regs p en b) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en b k R8 R26 R23 R27 Hq1 Hq2 Hq8 Vp Ve Hp He Vb Hb Hdj Hrw Hra.
  set (EW := vk_EW regs p en b).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EW j = getr regs r).
  { intros j Hj r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EW 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EW 32 = w64 p).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EW 33 = w64 en).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Uq : U EW (SOff 8 0) = q).
  { unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia. }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF).
  { unfold U. cbn [sv_denot]. rewrite E26, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (S32 : sv_denot EW (SOff 32 0) = w64 p).
  { cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (S33 : sv_denot EW (SOff 33 0) = w64 en).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vkb_ssC. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vk_sr0.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
      * rewrite R23. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 8)).
        rewrite (vk_U_sh EW q 8 E8 E26) by lia. unfold shadow_addr.
        assert (0 <= (q + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 0)).
        rewrite (vk_U_sh EW q 0 E8 E26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, vk_cur_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E8. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split.
        -- intros a Ha. apply Hrw. lia.
        -- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           ++ apply (chunk_ok_val SEGS EW _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
              rewrite Z.add_0_r. exact Vp.
           ++ apply (chunk_ok_val SEGS EW _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia |].
              exact Ve.
      * unfold region_ok, vk_byte_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS EW _ p 0 1 (SOff 34 0) b);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vb.
    + apply pairwise_disjoint_of_extents. unfold vk_cur_region, vk_byte_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E8, E32. unfold w64. rewrite !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vk_factsW f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vk_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EW (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.


(* ---- the position the colon step reaches: P with the new machine state, the cursor one byte on, and the model at
   the VALUE (vrd_jval) with the name already read ---- *)
Definition vkb_moveC (E : vrd_ient) (P : vrd_ipos) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (kk : Z) (nm : list Z) : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs mem md kk
    (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P + 1) (ip_acc P) (ip_f P)
    (vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) nm
       (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)))
    (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

Ltac vk_pjb := unfold vk_move; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids
  ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
Ltac vkb_proj := unfold vkb_moveC; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids
  ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* THE COLON STEP, off the machine: vk_key at p, the colon at p and the cursor word rewritten to p + 1 give
   VrdIElem.vrd_islot_a at p + 1. The model moves by vkb_kont_colon: NO event, NO ok eaten, so ip_tr / ip_ok / ip_D /
   the ledger all stay, and only the continuation and the cursor move. *)
Lemma vkb_islot_after : forall CTX CTX0 CW E P x k nm (regs' : bvmap 5 word) (mem' : word -> option byte) md' k',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_key B ARx SK E P x k nm ->
  (forall r, In r vk_live -> getr regs' r = getr (ip_regs P) r) ->
  (forall y : word, ~ (ie_q E <= bv_unsigned y < ie_q E + 8) -> mem' y = ip_mem P y) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 (ip_p P + 1) ->
  (forall a, ie_q E <= a < ie_q E + 8 -> writable_at SEGS (mrestrict (w_H (ip_W P)) mem') a) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  ip_p P < ie_text E + ie_len E ->
  nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 58 ->
  vrd_islot_a B ARx SK E (vkb_moveC E P regs' mem' md' k' nm) nm.
Proof.
  intros CTX CTX0 CW E P x k nm regs' mem' md' k' HEN HKY HR HKr Vp' Wq HJ' Hlt Hnth.
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  destruct (vkb_key_parts E P x k nm HKY) as ((z & Hc & Hsb) & Hcap1 & Hinc & af & Hfo & Hfl).
  pose proof HCU as (Hin & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HND as (_ & Hnc0 & Hcap & _ & _ & _ & (Di & HPerm & _) & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  destruct (vk_sp_frame B ARx Hfr144 CTX CTX0 CW E HEN) as [Hsp1 _].
  destruct (vk_q_bounds B ARx CTX CTX0 CW E HEN) as [Hq1 Hq2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hpr : ie_text E <= ip_p P + 1 <= ie_text E + ie_len E) by lia.
  assert (HK : forall y : word, ~ (ie_q E <= bv_unsigned y < ie_q E + 8) ->
                 mrestrict (w_H (ip_W P)) mem' y = mrestrict (w_H (ip_W P)) (ip_mem P) y)
    by (intros y Hy; unfold mrestrict; rewrite (HKr y Hy); reflexivity).
  assert (HKo : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                  (fun y => ie_q E + 8 <= y < ie_q E + 24 \/ ie_text E <= y < ie_text E + ie_len E)).
  { apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK). intros a Ha. lia. }
  assert (Hpin' : pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) (ip_p P + 1)
                    (Z.of_nat (ie_d E) + 1) (ie_tb E)).
  { split; [exact Vp'|].
    split; [eapply VrdFrame.val_mem_keep; [exact Ve | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split; [eapply VrdFrame.val_mem_keep; [exact Vd | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split.
    { intros y Hy. destruct (Z_lt_le_dec y (ie_q E + 8)) as [Hl | Hl]; [apply Wq; lia|].
      apply (proj2 HKo y); [cbn beta; lia | apply Hrw; lia]. }
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hpr|]. split; [exact Hlen|].
    split; [|exact (conj Hdisj Hd)].
    eapply VrdFrame.garr8_keep; [exact Hga | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]. }
  assert (Hsp' : spZ regs' = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  destruct (vk_cur_store_keep B ARx SK LAWS HW PST_IMG
              CTX CTX0 CW E P [(x, k)] regs' mem' md' k' (ip_p P + 1) (ie_q E) 8 Hfr144 Hs0c HEN HFR HND HCU HJN
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; exists (ie_q E, ie_q E + 8); split; [left; reflexivity | cbn; lia])
              ltac:(intros a Ha; lia) HK Hsp' HJ' Hpin'
              ltac:(apply vk_rest_len; lia))
    as (W1 & W2 & W3 & W4).
  assert (HKlow : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                    (fun y => 0 <= y < YM05.alloc_ceiling))
    by (apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK); intros a Ha; split; lia).
  assert (HxD : In (x, k) (ip_D P)) by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
  pose proof Hcs as (_ & Hsk & _).
  assert (Hx1 : 4096 <= x)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hx2 : x + k - 1 < YM05.alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & _ & HkD).
  assert (Hk1 : 4096 <= ip_keys P)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hk2 : ip_keys P + 8 * ip_cap P - 1 < YM05.alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  (* the model: the colon ends the name with no event *)
  assert (Hcolon : ip_cont P =
            vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) nm
              (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))).
  { rewrite Hc, Ho.
    exact (vkb_kont_colon (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) z nm
             (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))
             (vk_rest_cons (ie_tb E) (ie_text E) (ip_p P) 58 ltac:(lia) Hnth)). }
  unfold vrd_islot_a. split; [exact W1|]. split.
  { unfold vrd_iregs in *. vkb_proj. rewrite !HR by (cbn; tauto). exact HRG. }
  split; [exact W3|]. split; [exact W4|].
  split.
  { pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
    unfold vrd_imodel. vkb_proj. rewrite <- Hcolon.
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    split; [|exact (conj M6 (conj M7 (conj M8 (conj M9 M10))))].
    pose proof (vk_rest_len (ie_tb E) (ie_text E) (ip_p P) (ip_p P + 1) ltac:(lia)). lia. }
  vkb_proj. split; [exact Hnc|]. split.
  { rewrite Ho. exists x, k. split.
    { destruct Vx as (Hxr & Vxm). split; [exact Hxr|].
      eapply VrdFrame.val_mem_keep; [exact Vxm|]. eapply VrdFrame.rd_keep_mono; [exact HKlow|]. cbn; intros; nia. }
    split; [|exact W2].
    eapply pj_cstrR_keep; [exact Hcs | intros Hl; exact Hl |].
    eapply VrdFrame.rd_keep_mono; [exact HKlow|]. cbn; intros; lia. }
  split; [reflexivity|].
  (* THE BATCH KIT'S LAYER (the kit's cut): nothing moved but the cursor word, which no block of D holds (vrd_k1_keep); the key's
     block is the extra block of the order list and the slot's pj_keyR; the free list continues at the value *)
  assert (HKD : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem') (rd_blk (ip_D P))).
  { eapply VrdFrame.rd_keep_mono; [exact HKlow|]. intros y Hy. unfold rd_blk in Hy.
    apply Exists_exists in Hy as (b & Hb & Hy).
    pose proof (vk_D_low B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ y HAR HBM Hb Hy). lia. }
  destruct (vrd_k1_keep E P (vkb_moveC E P regs' mem' md' k' nm) [(x, k)] af
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              ltac:(intros a0 k0 H0; pose proof HMD as (_ & _ & (_ & _ & _ & HPL & _) & _);
                    unfold prh_lin; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact H0)
              HKD HND Hinc Hfo) as (Hinc' & Hfo').
  split; [exact Hcap1|]. split; [exact Hinc'|].
  exists [(x, k)], af, [k + cf_head].
  split.
  { rewrite Ho. exists x. split.
    { destruct Vx as (Hxr & Vxm). split; [exact Hxr|].
      eapply VrdFrame.val_mem_keep; [exact Vxm|]. eapply VrdFrame.rd_keep_mono; [exact HKlow|]. cbn; intros; nia. }
    right. exists k. split; [exact (proj1 Hcs) | reflexivity]. }
  split; [exact Hfo'|].
  split; [intros _; reflexivity|].
  intros okr. rewrite (Hfl okr), Ho.
  exact (vkb_jfk_colon (ip_f P) (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af [k + cf_head]
           (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) okr
           (vk_rest_cons (ie_tb E) (ie_text E) (ip_p P) 58 ltac:(lia) Hnth)).
Qed.



(* ---- 1. C3's COLON ARM. Rows 195..205 touch no memory, so they run over the READ-ONLY cursor seat (VrdIKey's
   vk_ssC) and stop at row 206 (slot 6138) with a1 = p; rows 206..209 store q->p := p + 1 over the WRITABLE seat and
   fall through to row 210 = A_ISLOT_SLOT. The split is at row 206 because the byte's shadow read (rows 199..201)
   falls after the branch of row 198, and a side goal of a later stretch can only name the memory of the stretch
   before it - which is the position's own only while nothing has been stored. ---- *)
Definition VKB_C3B_SLOT : nat := 6138%nat.

Definition vkb_c3b (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vk_key B ARx SK E P x k nm /\ getr (ip_regs P) 11 = w64 (ip_p P) /\
  ip_p P < ie_text E + ie_len E /\ nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 58.

Lemma vkb_c3_colon_a : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c3 B ARx SK E P x k nm ->
  ip_p P < ie_text E + ie_len E ->
  nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 58 ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_C3_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VKB_C3B_SLOT P' /\ ip_n P' = ip_n P /\
                     vkb_c3b E P' x k nm) /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HC3 Hlt Hnth HPM.
  pose proof HC3 as (HKY & R13 & R10 & R12 & _).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  (* The kit's cut: the position's journal is at the budget CW; the run is stated at the empty budget, so it runs from the
     journal rebased to the position's depot and steps back after it (VrdIElem.vrd_ijrn_base / vrd_ijrn_unbase) *)
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _). rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds B ARx CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  set (j := Z.to_nat (ip_p P - ie_text E)).
  assert (Hj : (j < length (ie_tb E))%nat) by (unfold j; lia).
  set (b := nth j (ie_tb E) 0).
  destruct (Hga j Hj) as [Vb Hb]. fold b in Vb, Hb.
  replace (ie_text E + Z.of_nat j) with (ip_p P) in Vb by (unfold j; lia).
  assert (Hb58 : b = 58) by (unfold b, j; exact (nth_error_nth _ _ 0 Hnth)).
  destruct (vk_seatC (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b VK_C3_SLOT
              G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq) as [HS SHOK].
  set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
  assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
  assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew EW kk = getr (ip_regs P) r).
  { intros kk Hkk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
  assert (E8 : ew EW 8 = w64 (ie_q E)) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact G8).
  assert (E8u : bv_unsigned (ew EW 8) = ie_q E) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (E13 : ew EW 13 = w64 (ie_text E + ie_len E)) by (rewrite (EL 13%nat ltac:(lia) 13%bv eq_refl); exact R13).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
  assert (E32 : ew EW 32 = w64 (ip_p P)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
  assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
    by (split; [intros kk Hkk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vk_ssC VK_C3_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ssC VK_C3_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_side_ro Hrat UB U32 .. | ].
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - exfalso. match goal with Hbr : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
      rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 13 0) in Hbr; cbn [ew ewset Nat.eqb] in Hbr;
      rewrite E32, E13 in Hbr; unfold w64 in Hbr; rewrite !unsigned_lit_small in Hbr by lia;
      rewrite !Z.add_0_r, !zcanon_id in Hbr by (unfold M64; lia);
      apply Bool.negb_true_iff, Z.ltb_ge in Hbr; lia end.
  - paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_side_ro Hrat UB U32 .. | ].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 205 bne taken: the byte at p is not the colon, refuted by Hnth *)
      exfalso.
      lazymatch goal with Hbr : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
        rename Hbr into HBR; set (EE := E') in HBR end.
      rewrite branch_ne_U in HBR.
      rewrite (U_SOff EE 34 0) in HBR.
      rewrite (U_lit EE 58) in HBR by lia.
      unfold EE in HBR. cbn [ew ewset Nat.eqb] in HBR. rewrite E34 in HBR. unfold w64 in HBR.
      rewrite unsigned_lit_small in HBR by lia. rewrite ?Z.add_0_r in HBR.
      apply Bool.negb_true_iff, Z.eqb_neq in HBR. apply HBR.
      first [ (rewrite ?Hb58; reflexivity) | lia | match goal with |- ?g => idtac "GOAL205" g end; fail ].
    + (* row 205 not taken: the colon; the fall-through lands on row 206 = slot 6138 *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VKB_C3B_SLOT);
        [ vkb_side_ro Hrat UB U32 .. | ].
      lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
        assert (HM : ms_mem ms2 = ip_mem P)
          by (repeat match goal with HF : frame_of _ ?rs ?m ?m' |- ?m' = _ =>
                rewrite (vk_frame_ro_gen _ rs m m'
                  ltac:(let rs' := eval vm_compute in rs in change rs with rs'; repeat constructor; cbn; lia) HF)
              end; reflexivity);
        assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E2)
          by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros kk Hkk; cbn [ew ewset];
              repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
        assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
          by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
              [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | rewrite R23; reflexivity | rewrite R27; reflexivity]);
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HSe) as R11e;
        cbn [ms_regs restrict] in R11e;
        (lazymatch type of R11e with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11e end);
        cbn [sv_denot] in R11e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R11e;
        cbn [ew ewset Nat.eqb] in R11e; rewrite E32 in R11e;
        lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
          pose proof (vk_unseatK B ARx SK LAWS HW PST_IMG Hfr144 Hs0c CTX CTX0 CW E P x k nm
                        (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P) HEN HKY HRk
                        ltac:(intros y Hy; rewrite HM; reflexivity)
                        ltac:(rewrite HM; exact Vp) ltac:(rewrite HM; intros a Ha; apply Hrw; lia)
                        (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) ltac:(left; reflexivity)) as HKY2;
          pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P))
        end
      end.
      split; [reflexivity|].
      split; [unfold vrd_cfg; vk_pjb;
              change (w64 (A_IPC VKB_C3B_SLOT)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat VKB_C3B_SLOT));
              reflexivity|].
      split; [vk_pjb; reflexivity|].
      split; [exact HKY2|]. vk_pjb. split; [exact R11e|]. split; [exact Hlt | exact Hnth].
Qed.


Lemma vkb_c3_colon_b : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vkb_c3b E P x k nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VKB_C3B_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ ip_n P' = ip_n P /\
                     vrd_islot_a B ARx SK E P' nm) /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HCB HPM.
  pose proof HCB as (HKY & R11 & Hlt & Hnth).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _). rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds B ARx CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (HSTK : 0 <= STK_parse_items (ie_d E)).
  { destruct HEN as ((HAF & _) & _). destruct HAF as (_ & _ & _ & _ & _ & Hstk & _). exact (proj1 (proj2 Hstk)). }
  set (j := Z.to_nat (ip_p P - ie_text E)).
  assert (Hj : (j < length (ie_tb E))%nat) by (unfold j; lia).
  set (b := nth j (ie_tb E) 0).
  destruct (Hga j Hj) as [Vb Hb]. fold b in Vb, Hb.
  replace (ie_text E + Z.of_nat j) with (ip_p P) in Vb by (unfold j; lia).
  destruct (vkb_seatC (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b
              VKB_C3B_SLOT G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq)
    as [HS SHOK].
  set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
  assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
  assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew EW kk = getr (ip_regs P) r).
  { intros kk Hkk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
  assert (E8 : ew EW 8 = w64 (ie_q E)) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact G8).
  assert (E8u : bv_unsigned (ew EW 8) = ie_q E) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (E11 : ew EW 11 = w64 (ip_p P)) by (rewrite (EL 11%nat ltac:(lia) 11%bv eq_refl); exact R11).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
  assert (E32 : ew EW 32 = w64 (ip_p P)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
  assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
    by (split; [intros kk Hkk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vkb_ssC VKB_C3B_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vkb_ssC VKB_C3B_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat A_ISLOT_SLOT);
    [ first [vkb_ra_byte Hrat UB U32 | vkb_awr E8u HSTK | vkb_awr_ro] .. | ].
  lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    assert (HKr : forall y : word, ~ (ie_q E <= bv_unsigned y < ie_q E + 8) -> ms_mem ms2 y = ip_mem P y)
      by (intros y Hy;
          repeat match goal with HF : frame_of _ _ ?m ?m' |- ?m' y = _ =>
            rewrite (vk_frame_cur _ _ _ (ie_q E) _ _ HF ltac:(cbn [ew ewset Nat.eqb]; exact E8u) y Hy) end;
          reflexivity);
    let rs := eval vm_compute in (ss_mem ss2) in
    lazymatch rs with (YP09.mkRegion (Some 8%nat) 0 24 0 8 ?cs) :: _ =>
    lazymatch cs with (YP09.mkChunk 0 (CVal 8 ?e0)) :: _ =>
      destruct (vk_end_cur _ _ E2 ss2 ms2 cs e0 (ie_q E) (ip_p P + 1) HSe
                  ltac:(change (ss_mem ss2) with rs; left; reflexivity) ltac:(left; reflexivity)
                  ltac:(cbn [ew ewset Nat.eqb]; exact E8u)
                  ltac:(rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E11; unfold w64;
                        rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia))
        as [Vq Wq]
    end end;
    assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E2)
      by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros kk Hkk; cbn [ew ewset];
          repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
      by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
          [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | rewrite R23; reflexivity | rewrite R27; reflexivity]);
    cbn [restrict ms_mem] in Vq, Wq;
    lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
      pose proof (vkb_islot_after CTX CTX0 CW E P x k nm (ms_regs ms2) (ms_mem ms2) MD K2 HEN HKY HRk HKr
                    Vq Wq (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) Hlt Hnth) as HSL;
      pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
      exists (vkb_moveC E P (ms_regs ms2) (ms_mem ms2) MD K2 nm)
    end
  end.
  split; [reflexivity|]. split; [unfold vrd_cfg; vkb_proj; reflexivity|].
  split; [vkb_proj; reflexivity | exact HSL].
Qed.

(* ---- 2. C3's REFUSAL ARM, rows 195..198 (p = end) or 195..205 (a byte that is not the colon), to row 305
   (slot VKB_REFB_SLOT). The whole stretch runs over VrdIKey's READ-ONLY cursor seat vk_ssC, so the memory at its end
   is the position's own (vk_frame_ro_gen) and the position moves by vk_unseatK at the SAME p. a0 / a2 are untouched
   by rows 195..205 (they write a1, a3, a4 only), so vk_c3's two new conjuncts survive the stretch - that is what
   REFUSE-B reads at rows 305 and 307. ---- *)
Definition vkb_refb (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vk_key B ARx SK E P x k nm /\
  getr (ip_regs P) 10 = w64 (ip_keys P + 8 * ip_n P) /\
  getr (ip_regs P) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)) /\
  (PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) = [] \/
   exists c r1, PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) = c :: r1 /\ c <> 58).

(* the position REFUSE-B starts from, off the machine: the run kept every live register, a0 / a2 and the memory, so
   vk_unseatK moves vk_key to the new machine state at the SAME p, and the model refuses there *)
Lemma vkb_ref_pos : forall CTX CTX0 CW E P x k nm (regs' : bvmap 5 word) (mem' : word -> option byte) md' k',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c3 B ARx SK E P x k nm ->
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false /\ b <> 58)) ->
  (forall r, In r vk_live -> getr regs' r = getr (ip_regs P) r) ->
  getr regs' 10 = getr (ip_regs P) 10 -> getr regs' 12 = getr (ip_regs P) 12 ->
  (forall y : word, mem' y = ip_mem P y) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vkb_refb E (vk_move P regs' mem' md' k' (ip_p P)) x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm regs' mem' md' k' HEN HC3 Hcase HRk R10' R12' Hkeep HJ'.
  pose proof HC3 as (HKY & R13 & R10 & R12 & _).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  assert (Hme : mem' = ip_mem P) by (apply functional_extensionality; exact Hkeep).
  unfold vkb_refb. split.
  { apply (vk_unseatK B ARx SK LAWS HW PST_IMG Hfr144 Hs0c CTX CTX0 CW E P x k nm regs' mem' md' k' (ip_p P) HEN HKY HRk).
    - intros y Hy. exact (Hkeep y).
    - rewrite Hme. exact Vp.
    - rewrite Hme. intros a Ha. apply Hrw. lia.
    - exact HJ'.
    - left. reflexivity. }
  vk_pjb. split; [rewrite R10'; exact R10|]. split; [rewrite R12'; exact R12|].
  destruct Hcase as [Hend | (Hlt & b & Hnth & Hnws & Hb58)].
  - left. replace (rest_atR (ie_tb E) (ie_text E) (ip_p P)) with (@nil Z); [reflexivity|].
    unfold rest_atR. symmetry. apply skipn_all2. lia.
  - right. exists b, (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)).
    split; [|exact Hb58].
    rewrite (vk_rest_cons (ie_tb E) (ie_text E) (ip_p P) b ltac:(lia) Hnth).
    exact (vkb_skip_nonws b _ Hnws).
Qed.

(* the end of a REFUSE-B run stretch: the memory is the position's (every region read-only), the live registers and
   a0 / a2 are kept, and vkb_ref_pos gives the position at row 305 *)
Ltac vkb_ref_finish CTX CTX0 CW E P x k nm HEN HC3 Hcase HJ HJN HPM HA EL R23 R27 :=
  lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    let HM := fresh "HM" in let HA2 := fresh "HA2" in let HRk := fresh "HRk" in
    let R10e := fresh "R10e" in let R12e := fresh "R12e" in let HREF := fresh "HREF" in
    assert (HM : ms_mem ms2 = ip_mem P)
      by (repeat match goal with HF : frame_of _ ?rs ?m ?m' |- ?m' = _ =>
            rewrite (vk_frame_ro_gen _ rs m m'
              ltac:(let rs' := eval vm_compute in rs in change rs with rs'; repeat constructor; cbn; lia) HF)
          end; reflexivity);
    lazymatch type of HA with env_agree 32 ?ER _ =>
      assert (HA2 : env_agree 32 ER E2)
        by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros kk Hkk; cbn [ew ewset];
            repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity)
    end;
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
      by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
          [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | rewrite R23; reflexivity | rewrite R27; reflexivity]);
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10e;
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HSe) as R12e;
    cbn [ms_regs restrict] in R10e, R12e;
    (lazymatch type of R10e with _ = sv_denot _ (sr_get ?l _) =>
       let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10e;
       let v2 := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v2 in R12e end);
    cbn [sv_denot] in R10e, R12e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10e, R12e;
    cbn [ew ewset Nat.eqb] in R10e, R12e;
    rewrite (EL 10%nat ltac:(lia) 10%bv eq_refl) in R10e;
    rewrite (EL 12%nat ltac:(lia) 12%bv eq_refl) in R12e;
    lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
      pose proof (vkb_ref_pos CTX CTX0 CW E P x k nm (ms_regs ms2) (ms_mem ms2) MD K2 HEN HC3 Hcase HRk R10e R12e
                    ltac:(intros y; rewrite HM; reflexivity) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ))
        as HREF;
      pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
      exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P))
    end;
    split; [reflexivity|];
    split; [unfold vrd_cfg; vk_pjb;
            change (w64 (A_IPC VKB_REFB_SLOT)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat VKB_REFB_SLOT));
            reflexivity|];
    split; [vk_pjb; reflexivity | exact HREF]
  end.

Lemma vkb_c3_ref : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c3 B ARx SK E P x k nm ->
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false /\ b <> 58)) ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_C3_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VKB_REFB_SLOT P' /\ ip_n P' = ip_n P /\
                     vkb_refb E P' x k nm) /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HC3 Hcase HPM.
  pose proof HC3 as (HKY & R13 & R10 & R12 & _).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _). rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds B ARx CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  destruct Hcase as [Hend | (Hlt & b & Hnth & Hnws & Hb58)].
  - (* p = end: row 198's bgeu is taken straight to row 305 *)
    assert (Hcase : ip_p P = ie_text E + ie_len E \/
              (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
                 PjGrammar.ws b = false /\ b <> 58)) by (left; exact Hend).
    destruct (vk_seat0 (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) false
                VK_C3_SLOT G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Hrw Hraq) as [HS SHOK].
    set (EO := vk_EO (ip_regs P) (ip_p P) (ie_text E + ie_len E)) in *.
    assert (HEI : img_env VAL A_LIM EO) by (unfold EO, vk_EO; apply Eimg_env).
    assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew EO kk = getr (ip_regs P) r).
    { intros kk Hkk r Hr. unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
      exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
    assert (E13 : ew EO 13 = w64 (ie_text E + ie_len E)) by (rewrite (EL 13%nat ltac:(lia) 13%bv eq_refl); exact R13).
    assert (E26 : ew EO 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
    assert (E32 : ew EO 32 = w64 (ip_p P)).
    { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
    assert (UB : U EO (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EO 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
    assert (U32 : U EO (SOff 32 0) = ip_p P) by (apply (U_atom EO 32 (ip_p P) E32); lia).
    assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E)]) EO)
      by (split; [intros kk Hkk; unfold EO, vk_EO; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
    change (sr_get (ss_regs (vk_ss0 false VK_C3_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
    change (sr_get (ss_regs (vk_ss0 false VK_C3_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
    unfold vrd_cfg.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_awr_ro .. | ].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 198 taken: p >= end, which is this case *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VKB_REFB_SLOT); [ vkb_awr_ro .. | ].
      vkb_ref_finish CTX CTX0 CW E P x k nm HEN HC3 Hcase HJ HJN HPM HA EL R23 R27.
    + (* row 198 not taken: p < end, refuted by p = end *)
      exfalso. match goal with Hbr : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
        rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 13 0) in Hbr; cbn [ew ewset Nat.eqb] in Hbr;
        rewrite E32, E13 in Hbr; unfold w64 in Hbr; rewrite !unsigned_lit_small in Hbr by lia;
        rewrite !Z.add_0_r, !zcanon_id in Hbr by (unfold M64; lia);
        apply Bool.negb_false_iff, Z.ltb_lt in Hbr; lia end.
  - (* p < end and the byte is not the colon: row 205's bne is taken *)
    assert (Hcase : ip_p P = ie_text E + ie_len E \/
              (ip_p P < ie_text E + ie_len E /\ exists bb, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some bb /\
                 PjGrammar.ws bb = false /\ bb <> 58))
      by (right; split; [exact Hlt | exists b; split; [exact Hnth | split; [exact Hnws | exact Hb58]]]).
    set (j := Z.to_nat (ip_p P - ie_text E)).
    assert (Hj : (j < length (ie_tb E))%nat) by (unfold j; lia).
    assert (Hb58' : nth j (ie_tb E) 0 = b) by (unfold j; exact (nth_error_nth _ _ 0 Hnth)).
    destruct (Hga j Hj) as [Vb Hb]. rewrite Hb58' in Vb, Hb.
    replace (ie_text E + Z.of_nat j) with (ip_p P) in Vb by (unfold j; lia).
    destruct (vk_seatC (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b VK_C3_SLOT
                G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq) as [HS SHOK].
    set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
    assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
    assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew EW kk = getr (ip_regs P) r).
    { intros kk Hkk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
      exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
    assert (E13 : ew EW 13 = w64 (ie_text E + ie_len E)) by (rewrite (EL 13%nat ltac:(lia) 13%bv eq_refl); exact R13).
    assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
    assert (E32 : ew EW 32 = w64 (ip_p P)).
    { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
    assert (E34 : ew EW 34 = w64 b).
    { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
    assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
    assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
    assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
      by (split; [intros kk Hkk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
    change (sr_get (ss_regs (vk_ssC VK_C3_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
    change (sr_get (ss_regs (vk_ssC VK_C3_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
    unfold vrd_cfg.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_side_ro Hrat UB U32 .. | ].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 198 taken: p >= end, refuted *)
      exfalso. match goal with Hbr : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
        rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 13 0) in Hbr; cbn [ew ewset Nat.eqb] in Hbr;
        rewrite E32, E13 in Hbr; unfold w64 in Hbr; rewrite !unsigned_lit_small in Hbr by lia;
        rewrite !Z.add_0_r, !zcanon_id in Hbr by (unfold M64; lia);
        apply Bool.negb_true_iff, Z.ltb_ge in Hbr; lia end.
    + paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_side_ro Hrat UB U32 .. | ].
      psrr_branch_tok RUN BR HS SHOK vk_Bspan.
      * (* row 205 taken: the byte is not the colon - this case *)
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VKB_REFB_SLOT);
          [ vkb_side_ro Hrat UB U32 .. | ].
        vkb_ref_finish CTX CTX0 CW E P x k nm HEN HC3 Hcase HJ HJN HPM HA EL R23 R27.
      * (* row 205 not taken: the byte IS the colon, refuted *)
        exfalso.
        lazymatch goal with Hbr : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
          rename Hbr into HBR; set (EE := E') in HBR end.
        rewrite branch_ne_U in HBR.
        rewrite (U_SOff EE 34 0) in HBR.
        rewrite (U_lit EE 58) in HBR by lia.
        unfold EE in HBR. cbn [ew ewset Nat.eqb] in HBR. rewrite E34 in HBR. unfold w64 in HBR.
        rewrite unsigned_lit_small in HBR by lia. rewrite ?Z.add_0_r in HBR.
        apply Bool.negb_false_iff, Z.eqb_eq in HBR. rewrite zcanon_id in HBR by (unfold M64; lia).
        exact (Hb58 HBR).
Qed.

(* ---- 3. REFUSE-B's seat, rows 305..308 (slots 6237..6240): ONE read-only region, the key slot keys + 8 n as atom
   32 holding the key x (atom 33); a0 is the slot and a2 its shadow address, as vk_c3 pins them. The shadow entry
   makes row 305's `lbu a1, 0(a2)` the slot's shadow byte, which row 306's `bnez a1` then reads as 0, so the ASan
   report is not reachable and the engine resolves both rows itself. ---- *)
Definition vkb_sh_sl (kk : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 kk) (SLit 3)) (SOff 26 0).
Definition vkb_srR : list sv := sr_set (sr_set sr_atoms 10%bv (SOff 32 0)) 12%bv (vkb_sh_sl 0).
Definition vkb_slot_region : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition vkb_factsR : facts :=
  mkFacts [ (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 (2 ^ 47 - 8) 3); (33%nat, mkAF 0 (2 ^ 62) 0) ] [] [].
Definition vkb_ssR (kk : nat) : sstate := mkSS (4 * Z.of_nat kk) vkb_srR [vkb_slot_region] None vkb_factsR.
Definition vkb_ER (regs : bvmap 5 word) (sl xx : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 sl; w64 xx]).
Definition vkb_SHR : list shent := [mkSHE 32 0 8].

(* the shadow address of the slot atom, as the engine's shadow-token match reads a2 (VrdIKey's vk_U_slot_sh at
   atom 36, here at atom 32) *)
Lemma vkb_U_sl : forall E' z, ew E' 32 = w64 z -> ew E' 26 = w64 SHADOW_OFF -> 0 <= z < 2 ^ 47 ->
  U E' (vkb_sh_sl 0) = SHADOW_OFF + z / 8.
Proof.
  intros E' z H32 H26 Hz. unfold vkb_sh_sl.
  rewrite !U_SAlu, (U_lit E' 3) by lia.
  rewrite U_SOff, H32. unfold w64. rewrite unsigned_lit_small by lia. rewrite ?Z.add_0_r.
  rewrite (U_atom E' 26 SHADOW_OFF H26) by (unfold SHADOW_OFF; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite (zcanon_id z) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= z / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id (z / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Lemma vkb_seatR : forall (fxP : YK11.FPState) (W : world SEGS) regs mem sl xx (kk : nat),
  getr regs 26 = w64 SHADOW_OFF -> getr regs 10 = w64 sl -> getr regs 12 = w64 (shadow_addr sl) ->
  4096 <= sl -> sl + 8 <= 2 ^ 47 - 8 -> sl mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) sl 8 xx -> 0 <= xx <= 2 ^ 62 ->
  (forall y, sl <= y < sl + 8 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 2 ^ 44)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF sl 8 ->
  st_ok_pi (fx := fxP) SEGS VAL (vkb_ER regs sl xx) (vkb_ssR kk)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC kk)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vkb_SHR (vkb_ER regs sl xx) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem sl xx kk R26 R10 R12 Hs1 Hs2 Hs8 Vx Hx Hsh Hra.
  set (ER := vkb_ER regs sl xx).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew ER j = getr regs r).
  { intros j Hj r Hr. unfold ER, vkb_ER. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E26 : ew ER 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew ER 32 = w64 sl).
  { unfold ER, vkb_ER. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew ER 33 = w64 xx).
  { unfold ER, vkb_ER. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (UB : U ER (SOff 26 0) = SHADOW_OFF) by (apply (U_atom ER 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
  assert (Usl : U ER (SOff 32 0) = sl) by (apply (U_atom ER 32 sl E32); lia).
  assert (S33 : sv_denot ER (SOff 33 0) = w64 xx).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC kk)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat kk)).
    unfold vkb_ssR. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vkb_srR.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
      * rewrite R10. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
        cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
        rewrite unsigned_lit_small by lia. reflexivity.
      * rewrite R12. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
        fold (U ER (vkb_sh_sl 0)). rewrite (vkb_U_sl ER sl E32 E26) by lia. unfold shadow_addr.
        assert (0 <= sl / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia).
        reflexivity.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, vkb_slot_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS ER _ sl 0 8 (SOff 33 0) xx); [exact S33 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vx.
    + apply pairwise_disjoint_of_extents. unfold vkb_slot_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
    + split; [|split; [exact I | exact I]].
      cbn [vkb_factsR f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vkb_SHR. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem ER (SOff 26 0) 32 sl 8 sl 0 8 Hra UB Usl); [lia | lia |].
    intros y Hy. apply Hsh. change (Z.min 0 8) with 0 in Hy. change (Z.max 0 8) with 8 in Hy. lia.
Qed.

(* fuzz_free's frame fits under parse_items' budget (VrdIKey's vk_stk_budget for parse_string, here for the free) *)
Lemma vkb_stk_ff : forall d, STK_fuzz_free + 144 <= STK_parse_items d.
Proof.
  intros d. unfold STK_parse_items, LEAF_pv_pi, zmaxl. cbn [fold_right].
  pose proof (pi_frame_nonneg F_parse_items). pose proof (pi_frame_nonneg F_parse_value).
  assert (0 <= Z.of_nat (PjGrammar.MAXD - d) * (pi_frame F_parse_value + pi_frame F_parse_items))
    by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Hfr144 in *. lia.
Qed.

Lemma vkb_stk_ff_nonneg : 0 <= STK_fuzz_free.
Proof.
  assert (Hz : forall l, 0 <= zmaxl l) by (intros l; unfold zmaxl; induction l; cbn [fold_right]; lia).
  unfold STK_fuzz_free. pose proof (pi_frame_nonneg F_fuzz_free). pose proof (Hz [STK_RT_ALLOC; STK_RT_ECALL]). lia.
Qed.

(* ==== REFUSE-B after fuzz_free returns (slot 6241): the exit position. fuzz_free's text ends in fpostbm, an
   apost_base_xbR journal at wle' SEGS RZ_cf at the CALL's sp (spZ (ie_regs E) - 144), while VrdCallKeep.vrd_call_keep
   reads a callee journal at the caller's window top (spZ (ie_regs E) + ie_e E): vkb_jrn_widen moves it there. The free
   REMOVES a block, so vrd_call_keep's fifth conclusion and VrdCallPos.vrd_pos_after_call (both assume the blocks only
   grow) do not apply: the node's bytes are kept here block by block (vkb_keep_hdr for the header,
   VrdIStep.vi_keep_blocks for the arrays and the subtree), and the node is rebuilt as VrdIStep's grow arms rebuild it
   (vi_swap_move, vi_sub_move, vi_part_fd). ==== *)

(* a ledger move is stable under a permutation of its block list *)
Lemma vkb_lm_perm : forall L0 pk0 c0 f0 r0 m0 ok gt tr D D2 Lam peak cnt fail ran,
  rd_ledger_move L0 pk0 c0 f0 r0 m0 ok gt tr D Lam peak cnt fail ran -> Permutation D D2 ->
  rd_ledger_move L0 pk0 c0 f0 r0 m0 ok gt tr D2 Lam peak cnt fail ran.
Proof.
  intros L0 pk0 c0 f0 r0 m0 ok gt tr D D2 Lam peak cnt fail ran (O & C & F & HPL & HPs & Hln & Hpk) HP.
  refine (conj O (conj C (conj F (conj _ (conj _ (conj _ Hpk)))))).
  - eapply Permutation_trans; [exact HPL|]. apply Permutation_app_tail. exact HP.
  - eapply Permutation_trans; [|exact HPs]. apply Permutation_map. apply Permutation_sym. exact HP.
  - rewrite <- (Permutation_length HP). exact Hln.
Qed.

(* one EFree never raises the held peak *)
Lemma vkb_hpeak_free : forall k, hpeakR [PjGrammar.EFree k] = 0.
Proof. intros k. cbn. lia. Qed.

(* the live requests across the free of the block (p, k + cf_head): the room view's live list is the blocks'
   request sizes (YGcfRoom.room_of_cf, YCbq.ablocks), and the free removes that one *)
Lemma vkb_live_free : forall ly ly2 S S2 b1 b2 p k,
  ablocks B ly S = b1 ++ (p, k + cf_head) :: b2 -> ablocks B ly2 S2 = b1 ++ b2 -> 0 <= k ->
  vc_live S S2 [PjGrammar.EFree (Z.to_nat k)].
Proof.
  intros ly ly2 S S2 b1 b2 p k E1 E2 Hk. unfold vc_live.
  rewrite vkb_hlive_free, Z2Nat.id, <- HI_head by exact Hk.
  replace (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (ablocks B ly S))
    by (unfold ablocks; rewrite map_map; reflexivity).
  replace (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (ablocks B ly2 S2))
    by (unfold ablocks; rewrite map_map; reflexivity).
  rewrite E1, E2, !map_app. cbn [map snd].
  apply Permutation_sym. apply PresetReqAtNoMiss.rm1_mid.
Qed.

(* a journal at a call's sp, read at a window top d bytes above it (the window present at the end); at any budget WS
   (the kit's cut: fuzz_free's post is budgeted, PRH_FnAlloc.v tfuzz_free_specX's fpostbm), read BY NAME (YCbqG.v ajxR_ar ..) *)
Lemma vkb_jrn_widen : forall STK sp0 d FP ly S Hp (W : world SEGS) mem md ly' S' Hp' (W' : world SEGS) mem' md' k WS,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS ->
  0 <= d -> d mod 16 = 0 -> sp0 + d <= ly_top ly ->
  (forall a, sp0 <= a < sp0 + d -> apresent (w_H W') mem' a) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK + d) (sp0 + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS.
Proof.
  intros STK sp0 d FP ly S Hp W mem md ly' S' Hp' W' mem' md' k WS HJ Hd Hd16 Htop Hpres.
  pose proof (ajxR_stk HJ) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold ajournal_xwR. apply ajxR_intro.
  - exact (ajxR_ar HJ).
  - exact (ajxR_ly HJ).
  - exact (ajxR_secs HJ).
  - exact (ajxR_rel HJ).
  - exact (ajxR_io HJ).
  - exact (ajxR_frs HJ).
  - exact (ajxR_nev HJ).
  - exact (ajxR_k HJ).
  - intros a Ha Hn. apply (ajxR_hi HJ); [exact Ha | lia].
  - exact (ajxR_blk HJ).
  - exact (ajxR_img HJ).
  - exact (ajxR_frm HJ).
  - exact (ajxR_gone HJ).
  - intros a Ha. destruct (Z_lt_le_dec a sp0) as [Hlt | Hge]; [apply (ajxR_pres HJ); lia | apply Hpres; lia].
  - unfold astk_ok. split; [rewrite Z.add_mod, A1, Hd16 by lia; reflexivity|]. lia.
  - exact (ajxR_extra HJ).
  - exact (ajxR_qt HJ).
  - exact (ajxR_wild HJ).
Qed.

(* the node's header is apart from the whole allocator block of every block the position owns (VrdIFd's
   vrd_inode_apart, over the block's allocator range in place of its user bytes) *)
Lemma vkb_fb_apart : forall CTX CTX0 CW E P a' k',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P -> In (a', k') (ip_D P) ->
  forall y, ie_v E <= y < ie_v E + 56 -> ~ inFP (ablocks_fp [(a' - cf_head, k' + cf_head)]) y.
Proof.
  intros CTX CTX0 CW E P a' k' HEN HJN Hb x Hvx Hfp.
  unfold ablocks_fp in Hfp. destruct Hfp as (r & Hr & Hx). cbn [map In] in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Hx.
  pose proof HJN as ((HAR & Hlay & _) & _ & _ & _ & _ & HBM & _).
  pose proof HBM as (HnotE & HPab & HPfr & _).
  pose proof Hlay as (_ & _ & _ & _ & _ & HFl & _).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPV & _ & _ & Hwin & HLE & _).
  pose proof HPV as (_ & _ & _ & _ & Hat & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  assert (HB' : In (a' - cf_head, k' + cf_head) (ablocks B (ip_ly P) (ip_S P))).
  { apply (Permutation_in _ (Permutation_sym HPab)). apply in_or_app. left. unfold prhReader_ab.
    exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) _ (a', k') Hb). }
  pose proof (HnotE a' k' Hb) as HnE.
  destruct Hat as [(a & k & HinL & Ha1 & Ha2) | [(b & m & Hab & _ & Hb1 & Hb2) | [(cid & pos & Hfr & Hf1 & Hf2) | Hw]]].
  - pose proof HLE as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
    destruct (HHB _ HinL) as (Hk0 & HabE & _). cbn [fst snd] in Hk0, HabE.
    assert (HabP : In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)))
      by (apply (Permutation_in _ (Permutation_sym HPab)); apply in_or_app; right; exact HabE).
    assert (Hne : (a' - cf_head, k' + cf_head) <> (a - cf_head, k + cf_head))
      by (intros Heq; apply HnE; rewrite Heq; exact HabE).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR HB' HabP Hne) as Hz.
    destruct (req_size_pos (k + cf_head)) as [_ Hr]; [lia|].
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - assert (HbP : In (b, m) (ablocks B (ip_ly P) (ip_S P)))
      by (apply (Permutation_in _ (Permutation_sym HPab)); apply in_or_app; right; exact Hab).
    assert (Hne : (a' - cf_head, k' + cf_head) <> (b, m)) by (intros Heq; apply HnE; rewrite Heq; exact Hab).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR HB' HbP Hne) as Hz.
    destruct (req_size_pos m) as [_ Hr]; [lia|].
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - assert (HfP : In (cid, pos) (frames (ip_S P))) by (apply (Permutation_in _ (Permutation_sym HPfr)); exact Hfr).
    destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HAR) as [Hq _].
    pose proof (pairwise_In _ _ _ _ _ _ eq_refl Hq
                  (in_map (fun b => (fst b, req_size (snd b))) _ _ HB')
                  (in_map (fun f => (frame_addr (ip_ly P) (fst f) (snd f), fs_frame_bytes (fst f))) _ _ HfP)) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. unfold frame_addr in Hz, Hf1, Hf2. rewrite HFl in Hz. lia.
  - lia.
Qed.

(* the node's header bytes across a callee whose journal keeps every entry block and whose footprint misses them
   (VrdCallKeep.vrd_call_keep's fifth conclusion, its node part, with the entry's blocks in place of P's); the
   callee's journal at any budget WS (the kit's cut: fuzz_free's post is budgeted) *)
Lemma vkb_keep_hdr : forall CTX CTX0 CW E P STK sp0 FP md ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 WS,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) md []
    ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  (forall b, In b (ablocks B (ie_ly E) (ie_S E)) -> In b (ablocks B ly2 S2)) ->
  (forall a, ie_v E <= a < ie_v E + 56 -> ~ inFP FP a) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W2) mem2) (fun a => ie_v E <= a < ie_v E + 56).
Proof.
  intros CTX CTX0 CW E P STK sp0 FP md ly2 S2 Hp2 W2 mem2 md2 k1 WS HEN HJN HJc Hkeep HnFP.
  destruct (vc_bounds B ARx LAWS CTX CTX0 CW E Hfr144 HEN) as (Bc & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & _).
  pose proof HJN as ((HAR & HlyE & _) & _ & _ & _ & _ & HBM & _).
  pose proof (ajxR_blk HJc) as Hblk. pose proof (ajxR_frm HJc) as Hfrc.
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _ & _ & _ & HLED & _).
  destruct HNODE as (_ & _ & _ & _ & HATv & _).
  pose proof HBM as (_ & HABP & HFRP & _).
  pose proof HlyE as (_ & _ & _ & _ & _ & EF & _).
  pose proof (@cf_head_nonneg cp) as Hh0.
  assert (Hold : forall b, In b (ablocks B (ie_ly E) (ie_S E)) -> In b (ablocks B (ip_ly P) (ip_S P)))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HABP)); apply in_or_app; right; exact Hb).
  assert (Hblock : forall p n a, In (p, n) (ablocks B (ie_ly E) (ie_S E)) -> p <= a < p + req_size n ->
            ~ inFP FP a -> 0 <= a < 2 ^ 64 /\ ~ in_img SEGS a /\
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros p n a Hin Hr Hnf.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR (Hold _ Hin)) as (_ & H4 & Hc & _).
    split; [lia|]. split.
    - exact (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ a HAR
                      (or_introl (ex_intro _ p (ex_intro _ n (conj (Hold _ Hin) Hr)))))).
    - pose proof (Hblk p n (a - p) (Hold _ Hin) (Hkeep _ Hin) ltac:(lia)) as Hk.
      replace (p + (a - p)) with a in Hk by lia. exact (Hk Hnf). }
  apply vc_rd_keep. intros a Hv. pose proof (HnFP a Hv) as Hnf.
  destruct HATv as [(a1 & k1' & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                   [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a1 k1' _ _ HLED Hin1) as (Hk1 & Hab1 & _).
    apply (Hblock (a1 - cf_head) (k1' + cf_head) a Hab1); [|exact Hnf].
    unfold req_size. destruct (Z.eqb_spec (k1' + cf_head) 0); lia.
  - apply (Hblock b m a Hinb); [|exact Hnf]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - assert (Hf' : In (cid, pos) (frames (ip_S P))) by (apply (Permutation_in _ (Permutation_sym HFRP)); exact Hf).
    assert (Hfa : frame_addr (ip_ly P) cid pos = frame_addr (ie_ly E) cid pos)
      by (unfold frame_addr; rewrite EF; reflexivity).
    split; [lia|]. split.
    + assert (Hrng : frame_addr (ip_ly P) cid pos <= a < frame_addr (ip_ly P) cid pos + fs_frame_bytes cid)
        by (rewrite Hfa; lia).
      exact (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ a HAR
               (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hf' Hrng))))))).
    + apply (Hfrc cid pos a Hf'); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfa; lia | exact Hnf].
  - lia.
Qed.

(* the exit position after the free: the key's block left D and Lam, one EFree in the trace, the rest kept *)
Definition vkb_P3 (P : vrd_ipos) ly2 S2 Hp2 (W2 : world SEGS) (regs' : bvmap 5 word) (mem2 : word -> option byte)
  (md' : Model) (k1 : Z) (D' Lam' : list (Z * Z)) (k : Z) : vrd_ipos :=
  MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P)
    (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P) (ip_tr P ++ [PjGrammar.EFree (Z.to_nat k)]) D' Lam'
    (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

(* REFUSE-B's exit, off the machine: from the state at row 305 (vkb_refb), the entry journal at the call state, the
   callee's journal at the call's sp, the entry journal after the join (row 309 run), the registers it kept, and
   fuzz_free's p <> 0 arm *)
Lemma vkb_free_exit : forall CTX CTX0 CW E P x k nm MD ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 md' k1 WS1
    (regs' : bvmap 5 word) b1 b2 l1 l2,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vkb_refb E P x k nm ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) MD (ip_k P) (ie_CW E) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK_fuzz_free (spZ (ip_regs P)) (ablocks_fp [(x - cf_head, k + cf_head)])
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) MD [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (ie_CW E) ->
  spZ regs' = spZ (ip_regs P) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  getr regs' 18 = w64 (-1) ->
  room_live_cf S2 -> vc_xfer (ip_S P) S2 [PjGrammar.EFree (Z.to_nat k)] ->
  (* the free's hull use: it keeps both meters (its all-granted list is empty) *)
  PresetHullBudget.hull_used (ip_S P) S2 [] ->
  ablocks B (ip_ly P) (ip_S P) = b1 ++ (x - cf_head, k + cf_head) :: b2 -> ablocks B ly2 S2 = b1 ++ b2 ->
  ip_Lam P = l1 ++ (x, k) :: l2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (l1 ++ l2) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) ->
  exists D', vrd_iexit_a B ARx SK E (vkb_P3 P ly2 S2 Hp2 W2 regs' mem2 md' k1 D' (l1 ++ l2) k) (-1).
Proof.
  intros CTX CTX0 CW E P x k nm MD ly2 S2 Hp2 W2 mem2 md2 md' k1 WS1 regs' b1 b2 l1 l2
    HEN HRB HJ HJg HJc Hsp' R3 R4 R18 Hrl2 HXF2 HHU2 Eab1 Eab2 ELam HLED2.
  pose proof HRB as (HKY & _ & _ & Hmodel).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  destruct (vkb_key_parts E P x k nm HKY) as ((z & Hcont & Hsz) & Hcap1 & Hinc & af & Hfo & Hfl).
  pose proof HJN as (HJN1 & HWIN & HFZ & HFK & HARO & HBM & HCH).
  pose proof (ajxR_ar HJN1) as HAR.
  pose proof (ajxR_ar HJg) as HAR2. pose proof (ajxR_frs HJg) as Hfr2. pose proof (ajxR_hi HJg) as J9.
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd32).
  pose proof HND as (Hhdr & Hnc0 & Hcap & Hc0 & Hlin & Hlen' & (Di & HDperm & Hrep) & Hrwk & Hrav & Hrak & Hrakeys
    & Hkeys0).
  pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
  pose proof HRG as (G3 & G4 & G8 & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  destruct (vc_bounds B ARx LAWS CTX CTX0 CW E Hfr144 HEN) as (Bc & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & HSTK).
  pose proof HFR as (Hf0 & _).
  rewrite Ho in HDperm, Hrep, Hhdr. cbv beta iota in Hrep.
  assert (Hcp : 0 < ip_cap P) by lia.
  destruct (Hlin Hcp) as (HkL & HyL'). pose proof (HyL' Ho) as HyL. clear HyL'.
  set (D' := kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR 6 (ip_keys P) (ip_cap P) ++ Di).
  assert (HDp : Permutation (ip_D P) ((x, k) :: D')) by exact HDperm.
  assert (ED' : D' = (ip_kids P, 56 * ip_cap P) :: (ip_keys P, 8 * ip_cap P) :: Di).
  { unfold D', kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity. }
  pose proof M3 as (_ & _ & _ & HPL & _).
  pose proof Hled as (_ & HNL & _).
  assert (HNL' : NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
  destruct (vi_nodup_of (ip_Lam P) (ip_D P) (ie_Lam E) HNL' HPL) as (HNDD & HNDf & _).
  assert (HxD : In (x, k) (ip_D P)) by (apply (Permutation_in _ (Permutation_sym HDp)); left; reflexivity).
  assert (HxL : In (x, k) (ip_Lam P)) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ x k _ _ Hled HxL) as (Hk0 & Habx & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Habx) as (_ & Hfb4 & Hfbc & _).
  assert (HLx : Permutation (ip_Lam P) ((x, k) :: (l1 ++ l2)))
    by (rewrite ELam; apply Permutation_sym, Permutation_middle).
  assert (HLp3 : Permutation (l1 ++ l2) (D' ++ ie_Lam E)).
  { apply (Permutation_cons_inv (a := (x, k))). eapply perm_trans; [apply Permutation_sym; exact HLx|].
    eapply perm_trans; [exact HPL|]. change ((x, k) :: D' ++ ie_Lam E) with (((x, k) :: D') ++ ie_Lam E).
    apply Permutation_app_tail. exact HDp. }
  assert (HinL' : forall b, In b D' -> In b (l1 ++ l2))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HLp3)); apply in_or_app; left; exact Hb).
  assert (HDL : forall b, In b D' -> In b (ip_Lam P))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left;
        apply (Permutation_in _ (Permutation_sym HDp)); right; exact Hb).
  destruct (vi_nodup_of (ip_Lam P) [(x, k)] (l1 ++ l2) HNL' HLx) as (_ & _ & Hxne).
  (* a block the exit still owns holds no byte of the freed allocator block *)
  assert (HoffFP : forall a0 k0 y, In (a0, k0) (l1 ++ l2) -> a0 <= y < a0 + k0 ->
                     ~ inFP (ablocks_fp [(x - cf_head, k + cf_head)]) y).
  { intros a0 k0 y Hin0 Hy Hfp. unfold ablocks_fp in Hfp. destruct Hfp as (r & Hr & Hlo). cbn [map In] in Hr.
    destruct Hr as [<- | []]. cbn [fst snd] in Hlo.
    assert (HinP : In (a0, k0) (ip_Lam P)) by (apply (Permutation_in _ (Permutation_sym HLx)); right; exact Hin0).
    exact (vi_lam_disj B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 x k y HAR Hled HinP HxL
             (fun Heq => Hxne x k a0 k0 (or_introl eq_refl) Hin0 (eq_sym Heq)) Hy Hlo). }
  (* the frame, the window, the read-only view and the chain at the exit (VrdCallKeep.vrd_call_keep) *)
  destruct (vrd_reader_call_pre B ARx SK LAWS CTX CTX0 CW E P (ip_regs P) Hfr144 Hs0c Hs0ps HEN HFR HJN Hf0 G8)
    as (_ & _ & _ & _ & _ & HFW & _ & _).
  pose proof HFW as (_ & He16 & Hetop & _).
  assert (HJw : ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_fuzz_free + (ie_e E + 144)) (spZ (ie_regs E) + ie_e E)
                  (ablocks_fp [(x - cf_head, k + cf_head)]) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) MD []
                  ly2 S2 Hp2 W2 mem2 md2 k1 WS1).
  { replace (spZ (ie_regs E) + ie_e E) with (spZ (ip_regs P) + (ie_e E + 144)) by lia.
    apply vkb_jrn_widen; [exact HJg | lia | exact He16 | exact Hetop |].
    intros a Ha. apply (ajxR_pres HJc). lia. }
  destruct (vrd_call_keep B ARx SK LAWS H_pst_ro (R := wle' SEGS YGcfRehidePost.RZ_cf) CTX CTX0 CW E
              (MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_regs P) (ip_mem P) MD (ip_k P) (ip_n P)
                 (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P) (ip_tr P)
                 (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P))
              (vkb_P3 P ly2 S2 Hp2 W2 regs' mem2 md2 k1 D' (l1 ++ l2) k)
              (STK_fuzz_free + (ie_e E + 144)) (ablocks_fp [(x - cf_head, k + cf_head)]) k1 WS1
              Hfr144 Hs0c HEN HFR (conj HJ (proj2 HJN)))
    as (CK1 & CK2 & CK3 & CK4 & _).
  { intros a Ha. right. right. unfold ablocks_fp in Ha. destruct Ha as (r & Hr & Hlo). cbn [map In] in Hr.
    destruct Hr as [<- | []]. cbn [fst snd] in Hlo. lia. }
  { exact HJw. }
  { intros a Ha _. cbn [vkb_P3 ip_W ip_mem]. apply J9; lia. }
  { exact Hsp'. }
  (* the blocks the exit owns: the free swapped the key's block for none (VrdIStep.vi_swap_move) *)
  assert (HBM3 : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 D' (ip_tr P ++ [PjGrammar.EFree (Z.to_nat k)])
                   (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
  { pose proof HBM as (_ & _ & _ & Hhp).
    apply (vi_swap_move B ARx LAWS _ _ _ _ _ _ Hp2 W2 mem2 md2 (ip_D P) (ip_tr P) _ _ _ [(x, k)] [] D' (b1 ++ b2)
             HBM HDp).
    - rewrite Eab1. unfold prhReader_ab. cbn [map fst snd app]. apply Permutation_sym. apply Permutation_middle.
    - rewrite Eab2. unfold prhReader_ab. cbn [map app]. apply Permutation_refl.
    - exact HAR2.
    - intros b [].
    - intros b b' [].
    - exact Hfr2.
    - rewrite vle_hpeak_app, vkb_hpeak_free. pose proof (vle_held_le_hpeak (ip_tr P)). lia. }
  (* the ledger: the key leaves D and Lam (VrdLedgerEv.vle_free_D) *)
  assert (HDpk : Permutation (ip_D P) (D' ++ [(x, Z.of_nat (Z.to_nat k))])).
  { rewrite Z2Nat.id by lia. eapply perm_trans; [exact HDp|]. apply Permutation_cons_append. }
  assert (HLxk : Permutation (ip_Lam P) ((x, Z.of_nat (Z.to_nat k)) :: (l1 ++ l2)))
    by (rewrite Z2Nat.id by lia; exact HLx).
  destruct (vle_free_D (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
              (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P) D' (ip_Lam P)
              (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (l1 ++ l2) x (Z.to_nat k)
              (vkb_lm_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M3 HDpk) HLxk
              ltac:(rewrite <- (vi_lsum_perm _ _ HDpk); exact M8)) as (HLM3 & HLS3).
  (* the answer: the continuation refuses with one EFree of the key's block *)
  assert (Hans : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                   (ip_ok P) = (None, ip_tr P ++ [PjGrammar.EFree (Z.to_nat k)], [])).
  { pose proof (M2 []) as H. rewrite app_nil_r in H. rewrite H, Hcont.
    rewrite (vkb_kont_refuse _ _ _ _ _ _ _ _ Hmodel). cbn [fst snd]. rewrite Hsz. reflexivity. }
  assert (Hcl : PjGrammar.calls (ip_tr P ++ [PjGrammar.EFree (Z.to_nat k)]) = PjGrammar.calls (ip_tr P))
    by (rewrite vle_calls_app, vkb_free_calls; lia).
  assert (Hbb : blocks_bytes S2 <= blocks_bytes (ip_S P) + prh_held [PjGrammar.EFree (Z.to_nat k)]).
  { rewrite (vi_blocks_bytes_lsum B ly2 S2), (vi_blocks_bytes_lsum B (ip_ly P) (ip_S P)), Eab1, Eab2, !vi_lsum_app.
    cbn [Ledger.lsum]. unfold prh_held. rewrite vkb_free_held, vkb_free_calls, Z2Nat.id by lia. lia. }
  (* the cursor's words, at and above the call's sp, read the same after the free *)
  assert (Hnimg : forall a, alloc_ceiling <= a -> ~ in_img SEGS a).
  { intros a Ha Hi. pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
  assert (HKq : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W2) mem2)
                  (fun a => ie_q E <= a < ie_q E + 24)).
  { apply vc_rd_keep. intros a Ha. split; [lia|]. split; [apply Hnimg; lia | apply J9; lia]. }
  assert (HAFT : pj_in_afterR SEGS (mrestrict (w_H W2) mem2) (ie_q E) (ie_text E) (ie_len E)
                   (Z.of_nat (ie_d E) + 1) 33).
  { exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [lia|]. split; [lia|].
    split; [eapply val_mem_keep; [exact Vp | eapply rd_keep_mono; [exact HKq | cbn; intros; lia]]|].
    split; [eapply val_mem_keep; [exact Ve | eapply rd_keep_mono; [exact HKq | cbn; intros; lia]]|].
    split; [eapply val_mem_keep; [exact Vd | eapply rd_keep_mono; [exact HKq | cbn; intros; lia]]|].
    eapply rd_rw_keep; [exact Hrw | eapply rd_keep_mono; [exact HKq | intros; lia]]. }
  (* the node's bytes: the header (vkb_keep_hdr), the arrays and the subtree (vi_keep_blocks) *)
  assert (HKhdr : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W2) mem2)
                    (fun a => ie_v E <= a < ie_v E + 56)).
  { apply (vkb_keep_hdr CTX CTX0 CW E P _ _ _ MD ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HEN HJN HJg).
    - intros b Hb. pose proof HBM as (HDnew & HABP & _).
      assert (HbP : In b (ablocks B (ip_ly P) (ip_S P)))
        by (apply (Permutation_in _ (Permutation_sym HABP)); apply in_or_app; right; exact Hb).
      rewrite Eab1 in HbP. rewrite Eab2. apply in_app_or in HbP. apply in_or_app.
      destruct HbP as [H1 | [<- | H2]]; [left; exact H1 | | right; exact H2].
      exfalso. exact (HDnew x k HxD Hb).
    - intros a Ha. exact (vkb_fb_apart CTX CTX0 CW E P x k HEN HJN HxD a Ha). }
  assert (HKD : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W2) mem2) (rd_blk D')).
  { eapply (vi_keep_blocks B ARx SK LAWS); [exact HJg | exact Hled | exact HLED2 | |].
    - intros b Hb. split; [exact (HDL b Hb) | exact (HinL' b Hb)].
    - intros [a0 k0] y Hb Hy. unfold pj_holdsR in Hy; cbn [fst snd] in Hy. exact (HoffFP a0 k0 y (HinL' _ Hb) Hy). }
  (* the refused node is freeable (VrdIStep.vi_part_fd) *)
  assert (HMX : (PjGrammar.MAXD - ie_d E)%nat = S (PjGrammar.MAXD - S (ie_d E))) by (unfold PjGrammar.MAXD; lia).
  assert (HNDDl : List.NoDup (ip_D P)) by (first [exact HNDD | apply NoDup_ListNoDup; exact HNDD]).
  assert (HNDfl : List.NoDup (map fst (ip_D P))) by (first [exact HNDf | apply NoDup_ListNoDup; exact HNDf]).
  assert (HNDD' : List.NoDup D') by (pose proof (Permutation_NoDup HDp HNDDl) as H; inversion H; assumption).
  assert (HDiK : forall b, In b Di -> fst b <> ip_kids P).
  { intros b Hb Heq. pose proof (Permutation_NoDup (Permutation_map fst HDp) HNDfl) as H.
    rewrite ED' in H. cbn [map] in H. apply NoDup_cons_iff in H as [_ H]. apply NoDup_cons_iff in H as [Hn _].
    apply Hn. cbn [fst]. right. rewrite <- Heq. apply in_map. exact Hb. }
  assert (HDiApK : forall b y, In b Di -> pj_holdsR b y ->
                     ~ (ip_kids P <= y < ip_kids P + 56 * Z.of_nat (length (ip_acc P)))).
  { intros [a0 k0] y Hin0 Hy Hy'. unfold pj_holdsR in Hy; cbn [fst snd] in Hy.
    assert (HD0 : In (a0, k0) D') by (rewrite ED'; right; right; exact Hin0).
    assert (HK0 : In (ip_kids P, 56 * ip_cap P) D') by (rewrite ED'; left; reflexivity).
    apply (vi_lam_disj B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 (ip_kids P) (56 * ip_cap P) y HAR Hled
             (HDL _ HD0) (HDL _ HK0) (HDiK _ Hin0) Hy).
    unfold req_size. destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia. }
  assert (HFD : pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin (l1 ++ l2)) (PjGrammar.MAXD - ie_d E) (ie_v E) D').
  { rewrite HMX.
    apply (vi_part_fd _ _ _ 6 (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) true
             [(ip_kids P, 56 * ip_cap P)] [(ip_keys P, 8 * ip_cap P)] Di D' (rev (ip_acc P))).
    - first [exact HNDD' | apply NoDup_ListNoDup; exact HNDD'].
    - intros b y Hb Hy. apply (vrd_inode_apart B ARx SK LAWS CTX CTX0 CW E P HEN HJN b y); [|exact Hy].
      apply (Permutation_in _ (Permutation_sym HDp)). right. exact Hb.
    - eapply pj_hdrR_keep; [exact Hhdr | exact HKhdr].
    - right. exists (56 * ip_cap P). split; [apply HinL'; rewrite ED'; left; reflexivity | split; [lia | reflexivity]].
    - right. split; [reflexivity|]. exists (8 * ip_cap P).
      split; [apply HinL'; rewrite ED'; right; left; reflexivity | split; [lia | reflexivity]].
    - rewrite ED'. apply Permutation_refl.
    - apply (vi_sub_move true _ _ _ _ (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di Hrep).
      + intros a0 k0 Hin0 _. apply HinL'. rewrite ED'. right. right. exact Hin0.
      + eapply rd_keep_mono; [exact HKD|]. intros y Hy. unfold rd_blk in *. rewrite ED'.
        apply Exists_cons_tl. apply Exists_cons_tl. exact Hy.
      + intros y Hy. apply (proj1 HKD). apply (vk_rd_blk_in _ (ip_kids P, 56 * ip_cap P));
          [rewrite ED'; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
      + intros y Hy. apply apresent_writable.
        apply (vi_lam_present B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ (ip_kids P) (56 * ip_cap P) _ HAR2 HLED2);
          [apply HinL'; rewrite ED'; left; reflexivity | lia].
      + destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hled HkL) as (_ & _ & _ & Hk16 & _). lia.
      + intros _ y Hy. apply (proj1 HKD). apply (vk_rd_blk_in _ (ip_keys P, 8 * ip_cap P));
          [rewrite ED'; right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
      + exact HDiApK.
    - rewrite length_rev. exact Hlen'.
    - apply Forall_rev. exact M7. }
  (* THE KIT'S CUT: THE PARTIAL FREE ORDER of the refused node (the post's None arm, vrd_iexit_a's res = -1 conjunct): the
     completed slots' order list (vk_key's vrd_iforder at the members' depth bound nn, carried to the exit memory by
     VrdIStep.vi_fo_sub over vi_sub_move's keep premises), then the arrays (VrdIStep.vi_part_fo), against the model's
     free list after the missing colon: the completed slots' list, then the arrays (vkb_jfk_refuse, VrdIFd.vrd_arrz_blk) *)
  assert (HDp1 : Permutation (ip_D P) ((x, k) :: (ip_kids P, 56 * ip_cap P) :: (ip_keys P, 8 * ip_cap P) :: Di))
    by (rewrite <- ED'; exact HDp).
  assert (HSK : vi_subkeep true (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W2) mem2) (prh_lin (l1 ++ l2))
                  (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di).
  { split; [intros a0 k0 Hin0; apply HinL'; rewrite ED'; right; right; exact Hin0|].
    split.
    { eapply rd_keep_mono; [exact HKD|]. intros y Hy. unfold rd_blk in *. rewrite ED'.
      apply Exists_cons_tl. apply Exists_cons_tl. exact Hy. }
    split.
    { intros y Hy. apply (proj1 HKD). apply (vk_rd_blk_in _ (ip_kids P, 56 * ip_cap P));
        [rewrite ED'; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia]. }
    split.
    { intros y Hy. apply apresent_writable.
      apply (vi_lam_present B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ (ip_kids P) (56 * ip_cap P) _ HAR2 HLED2);
        [apply HinL'; rewrite ED'; left; reflexivity | lia]. }
    split; [destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hled HkL) as (_ & _ & _ & Hk16 & _); lia|].
    split.
    { intros _ y Hy. apply (proj1 HKD). apply (vk_rd_blk_in _ (ip_keys P, 8 * ip_cap P));
        [rewrite ED'; right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia]. }
    exact HDiApK. }
  assert (HFO : cf_head = PresetReqAt.HEAD -> forall n0, (PjGrammar.MAXD - ie_d E <= n0)%nat ->
            exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin (l1 ++ l2)) n0 (ie_v E) D' F /\
              map (fun b => snd b + cf_head) F =
                prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)).
  { assert (EKK : forall l, kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR 6 (ip_keys P) (ip_cap P) ++ l =
                    (ip_kids P, 56 * ip_cap P) :: (ip_keys P, 8 * ip_cap P) :: l).
    { intros l. unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity. }
    intros Hhd n0 Hn0. rewrite HMX in Hn0.
    destruct n0 as [|nn]; [lia|].
    assert (Hdep : Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P))
      by (apply (vi_dep_le (ip_acc P) (PjGrammar.MAXD - S (ie_d E)) nn); [lia | exact M7]).
    destruct (Hfo Hhd nn Hdep) as (Di0 & Facc & HP0 & HOI & HFm).
    rewrite Ho in HP0. cbv beta iota in HP0. rewrite EKK in HP0. cbn [app] in HP0.
    assert (HDi0 : Permutation Di0 Di).
    { apply (Permutation_cons_inv (a := (ip_keys P, 8 * ip_cap P))).
      apply (Permutation_cons_inv (a := (ip_kids P, 56 * ip_cap P))).
      apply (Permutation_cons_inv (a := (x, k))).
      eapply perm_trans; [apply Permutation_sym; exact HP0 | exact HDp1]. }
    assert (Hn : Z.to_nat (ip_n P) = length (ip_acc P)) by lia.
    rewrite Ho, Hn in HOI.
    pose proof (vi_fo_sub true _ _ _ _ (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di Di0 Facc nn
                  HSK HDi0 HOI) as HOI2.
    rewrite <- Hn in HOI2.
    exists (Facc ++ [(ip_kids P, 56 * ip_cap P)] ++ [(ip_keys P, 8 * ip_cap P)]). split.
    - apply (vi_part_fo _ _ _ 6 (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) true
               [(ip_kids P, 56 * ip_cap P)] [(ip_keys P, 8 * ip_cap P)] Di0 D' Facc nn).
      + first [exact HNDD' | apply NoDup_ListNoDup; exact HNDD'].
      + intros b y Hb Hy. apply (vrd_inode_apart B ARx SK LAWS CTX CTX0 CW E P HEN HJN b y); [|exact Hy].
        apply (Permutation_in _ (Permutation_sym HDp)). right. exact Hb.
      + eapply pj_hdrR_keep; [exact Hhdr | exact HKhdr].
      + right. exists (56 * ip_cap P). split; [apply HinL'; rewrite ED'; left; reflexivity | split; [lia | reflexivity]].
      + right. split; [reflexivity|]. exists (8 * ip_cap P).
        split; [apply HinL'; rewrite ED'; right; left; reflexivity | split; [lia | reflexivity]].
      + rewrite ED'. cbn [app]. apply perm_skip, perm_skip. apply Permutation_sym. exact HDi0.
      + exact HOI2.
    - pose proof (Hfl []) as HF0. rewrite app_nil_r in HF0. rewrite HF0.
      rewrite (vkb_jfk_refuse _ _ _ _ _ _ _ _ Hmodel).
      rewrite map_app, HFm. f_equal.
      pose proof (vrd_arrz_blk true (ip_kids P) (ip_keys P) (ip_cap P) ltac:(lia) Hhd) as HA.
      cbv beta iota in HA. rewrite <- (app_nil_r (keys_blkR 6 (ip_keys P) (ip_cap P))), EKK in HA.
      exact HA. }
  set (P3 := vkb_P3 P ly2 S2 Hp2 W2 regs' mem2 md' k1 D' (l1 ++ l2) k).
  assert (HXF3 : vc_xfer (ie_S E) S2 (ip_tr P ++ [PjGrammar.EFree (Z.to_nat k)]))
    by exact (vc_xfer_app (ie_S E) (ip_S P) S2 (ip_tr P) [PjGrammar.EFree (Z.to_nat k)] M9 HXF2).
  assert (HOC : vc_outc E P3).
  { apply (vc_outc_granted E P3 None []); unfold P3, vkb_P3; cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran ip_S].
    - rewrite Hcl. exact M1.
    - exact Hans.
    - exact HLM3.
    - exact HXF3. }
  exists D'. fold P3. unfold vrd_iexit_a.
  split; [exact CK1|].
  split; [split; [exact HJc|]; split; [exact CK2|]; split; [exact HFZ|]; split; [exact HFK|]; split; [exact CK3|];
          split; [exact HBM3 | exact CK4]|].
  split; [exact R3|]. split; [exact R4|]. split; [exact R18|]. split; [right; reflexivity|].
  split; [exact HLED2|]. split; [exact Hrl2|]. split; [exact HXF3|]. split; [exact HOC|].
  split; [exact HLM3|].
  split; [exact (vle_blocks_step (ie_S E) (ip_S P) S2 (ip_tr P) _ M6 Hbb)|].
  split; [exact HLS3|].
  split.
  { exists [], []. split; [unfold P3, vkb_P3; cbn [ip_ok ip_tr]; rewrite Hans; reflexivity|].
    split; [intros H; discriminate H|]. intros _. split; [exact HAFT|]. split; [exact HFD | exact HFO]. }
  split; [exact (vc_live_app (ie_S E) (ip_S P) S2 (ip_tr P) _ M10
                   (vkb_live_free (ip_ly P) ly2 (ip_S P) S2 b1 b2 (x - cf_head) k Eab1 Eab2 ltac:(lia)))|].
  (* the hull use over the call's all-granted events: the use so far, then the free's over the empty list, then the
     rest of the granted continuation (VrdIStep.vi_hull_exit over VrdCallPos.vc_gt_split) *)
  split; [exact (vi_hull_exit (ie_S E) (ip_S P) S2 (ip_tr P) [] (snd (fst (ip_cont P []))) _ [] (vc_gt_split E P HMD)
                  eq_refl M11 HHU2)|].
  (* the outcome of an injected reading: the free is no call, so the exit is on the granted prefix
     (VrdIElem.vrd_inj_granted) *)
  apply vrd_inj_granted. unfold P3, vkb_P3. cbn [ip_ok ip_tr]. rewrite Hcl. exact M1.
Qed.

Lemma vkb_refb_exit : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop),
  srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vkb_refb E P x k nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VKB_REFB_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' (-1)) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW PCALL HEN HRB HPM.
  pose proof HRB as (HKY & R10 & R12 & Hmodel).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & _).
  (* The kit's cut: the run of rows 305..307 from the journal rebased to the position's depot (VrdIElem.vrd_ijrn_base) *)
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HUC & _).
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HCW & _ & _ & HHB)).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof HND as (Hhdr & Hnc0 & Hcap & Hc0 & Hlin & Hlen' & (Di & HDperm & Hrep) & Hrwk & Hrav & Hrak & Hrakeys & Hkeys0).
  pose proof HFR as (Hf0 & _).
  pose proof Hcs as (_ & Hsk & _).
  pose proof asan_consts as (C1 & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  destruct (vk_q_bounds B ARx CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  destruct (vk_sp_frame B ARx Hfr144 CTX CTX0 CW E HEN) as [Hsp1 Hsp16].
  (* the key slot and the key *)
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  destruct (vk_slot_place B ARx SK LAWS HW CTX CTX0 CW E P _ (ip_keys P) 8 Hfr144 HEN HND Hled HJN Hin8 Hnc)
    as (Hpl1 & Hpl2 & Hplz & Hplsh & Hplv & Hplra).
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & HlinK & HkD).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hled HlinK) as (HkK & HabK & _ & Hk16 & _).
  assert (HxD : In (x, k) (ip_D P))
    by (apply (Permutation_in _ (Permutation_sym HDperm)); left; reflexivity).
  assert (Hx1 : 4096 <= x)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hx2 : x + k - 1 < YM05.alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hsl8 : (ip_keys P + 8 * ip_n P) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hk16; [|lia]. destruct Hk16 as [m Hm].
    exists (2 * m + ip_n P). lia. }
  destruct (vkb_seatR (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ip_keys P + 8 * ip_n P) x VKB_REFB_SLOT
              G26 R10 R12 ltac:(lia) ltac:(lia) Hsl8 (proj2 Vx) ltac:(lia)
              ltac:(intros y Hy; exact (Hplsh y ltac:(lia))) Hplra) as [HS SHOK].
  set (ER := vkb_ER (ip_regs P) (ip_keys P + 8 * ip_n P) x) in *.
  assert (HEI : img_env VAL A_LIM ER) by (unfold ER, vkb_ER; apply Eimg_env).
  assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew ER kk = getr (ip_regs P) r).
  { intros kk Hkk r Hr. unfold ER, vkb_ER. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
  assert (E33 : ew ER 33 = w64 x).
  { unfold ER, vkb_ER. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  (* the call's own premises at the position's view *)
  destruct (vrd_reader_call_pre B ARx SK LAWS CTX CTX0 CW E P (ip_regs P) Hfr144 Hs0c Hs0ps HEN HFR HJN Hf0 G8)
    as (HCUR & HCE & HCH & Hq16 & Hq24' & HFW & HROD & HTOP).
  pose proof HFW as (He0' & He16 & Hetop & Hepres).
  destruct (HCH (spZ (ip_regs P)) ltac:(lia)) as (chc & Hchc & Hspn).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vkb_awr_ro | ].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  assert (HM : ms_mem ms = ip_mem P)
    by (eapply (vk_frame_ro_gen _ [vkb_slot_region]); [repeat constructor; cbn; lia | exact HF1]).
  (* the key block as a block of this position the entry did not have (aj_call_xb_sp's footprint premise) *)
  assert (HxL : In (x, k) (ip_Lam P))
    by (pose proof HMD as (_ & _ & (_ & _ & _ & HPL & _) & _);
        apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact HxD).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ x k _ _ Hled HxL) as (Hkx & Habx & _).
  pose proof HBM as (HDnew & HABperm & HFRperm & Hhpk).
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
  rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl) in P2.
  rewrite (EL 3%nat ltac:(lia) 3%bv eq_refl) in P3.
  rewrite (EL 4%nat ltac:(lia) 4%bv eq_refl) in P4.
  rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl) in P8.
  assert (Hspms : spZ (ms_regs ms) = spZ (ip_regs P)) by (unfold spZ; rewrite P2; reflexivity).
  pose proof (@pa_B_ok _ _ PI_prog_A) as HBok.
  (* THE KIT'S CUT, THE FREE'S TRACE (tfuzz_free_specX's `admits (as_universe B) (call_trace ..) S`, PRH_FnAlloc.v:340): the
     cursor chain stops after one record (prh_cur_low), so the trace is [pc0; r; w] at the word w at q - 8, and
     prh_cw_ok (vrd_reader_call_pre) places it: A''s CODE word (clause 4a, PRH_Base.prh_univ_closure_cur: a FIXED
     trace) or one of CW's traces (clause 4b, prh_univ_closure_wild: inU through the wild arm); the empty-chain and
     no-frame traces are fixed (clauses 1-2) *)
  assert (Hra : raZ (ms_regs ms) = A_IPC 6241) by (unfold raZ; rewrite P1; vm_compute; reflexivity).
  assert (HTR : In (call_trace (ip_ly P) (pc_free_ra0 (as_code B)) (ms_regs ms) chc) (u_fix (as_universe B)) \/
                (In (call_trace (ip_ly P) (pc_free_ra0 (as_code B)) (ms_regs ms) chc) CW /\
                 inU (as_universe B) (call_trace (ip_ly P) (pc_free_ra0 (as_code B)) (ms_regs ms) chc))).
  { assert (Hlit : forall ra, ra = A_IPC 6241 ->
              In (prh_trace (pc_free_ra0 (as_code B)) ra []) (u_fix (as_universe B))).
    { intros ra ->. pose proof H_ffret as Hff. unfold prh_free_sites in Hff. apply in_app_or in Hff.
      destruct Hff as [Hr | Hr];
        [ exact (prh_univ_closure_lit B CTX0 F_parse_items RT_free _ HUC Hr)
        | exact (prh_univ_closure_lit B CTX0 F_parse_items RT_fuzz_free _ HUC Hr) ]. }
    unfold call_trace. destruct (frame0_ok (ip_ly P) (ms_regs ms)); [| left; exact (proj1 HUC RT_fuzz_free)].
    destruct Hchc as [(_ & ->) | (Hv1 & Hv2 & Hv3 & Hfpc & _)].
    { left. replace (unwind_of_chain (pc_free_ra0 (as_code B)) [(spZ (ms_regs ms), raZ (ms_regs ms), s0Z (ms_regs ms))])
        with (prh_trace (pc_free_ra0 (as_code B)) (raZ (ms_regs ms)) [])
        by (cbn [unwind_of_chain prh_trace flat_map]; reflexivity).
      exact (Hlit _ Hra). }
    destruct chc as [|[[fp w] nfp] rest].
    { left. replace (unwind_of_chain (pc_free_ra0 (as_code B)) [(spZ (ms_regs ms), raZ (ms_regs ms), s0Z (ms_regs ms))])
        with (prh_trace (pc_free_ra0 (as_code B)) (raZ (ms_regs ms)) [])
        by (cbn [unwind_of_chain prh_trace flat_map]; reflexivity).
      exact (Hlit _ Hra). }
    cbn [fpchain] in Hfpc. destruct Hfpc as (-> & _ & Hw & Hnfp & _ & Hrest).
    destruct (HCUR F_parse_items (or_intror eq_refl)) as [HCO HCL].
    unfold prh_cur_low, prh_s0 in HCL. rewrite Hs0c, Z.add_0_r in HCL.
    pose proof (HCL nfp Hnfp) as Hnfp1.
    unfold bad_next in Hrest.
    replace (nfp <=? ie_q E) with true in Hrest by (symmetry; apply Z.leb_le; lia).
    cbn [orb] in Hrest. subst rest.
    replace (unwind_of_chain (pc_free_ra0 (as_code B))
               [(spZ (ms_regs ms), raZ (ms_regs ms), s0Z (ms_regs ms)); (ie_q E, w, nfp)])
      with (prh_trace (pc_free_ra0 (as_code B)) (raZ (ms_regs ms)) [w])
      by (cbn [unwind_of_chain prh_trace flat_map]; reflexivity).
    rewrite Hra.
    assert (Hw' : rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (prh_s0 F_parse_items (ie_q E) - 8) = Some w)
      by (unfold prh_s0; rewrite Hs0c, Z.add_0_r; exact Hw).
    destruct (HCO (A_IPC 6241) w H_ffret Hw') as [Hcw | Hcode].
    - right. split; [exact Hcw|].
      exact (prh_univ_closure_wild B CTX0 F_parse_items (A_IPC 6241) w HUC (or_intror eq_refl) H_ffret).
    - left. exact (prh_univ_closure_cur B CTX0 F_parse_items (A_IPC 6241) w HUC (or_intror eq_refl) H_ffret Hcode). }
  (* the admission: a fixed trace at every state (YCbqG.admits_ct_fix, no room spent); a CW trace from the room the
     position has for CW (VrdIElem.vrd_wild_room_at, YCbqGwild.wild_room_admits_laws) *)
  assert (HADM : admits (as_universe B) (call_trace (ip_ly P) (pc_free_ra0 (as_code B)) (ms_regs ms) chc) (ip_S P)).
  { destruct HTR as [Hfix | (Hcw & HinU)].
    - exact (admits_ct_fix _ _ _ _ _ _ Hfix).
    - pose proof (vrd_wild_room_at B ARx SK CTX CTX0 CW E P HEN HJN) as HWR.
      exact (YCbqGwild.wild_room_admits_laws SEGS B ARx LAWS (as_universe B) CW 0 (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P)
               (ip_mem P) (ip_md P) _ HAR HWR HinU (or_introl Hcw)). }
  (* the caller's journal at the call state, back at its budget CW (VrdIElem.vrd_ijrn_unbase) *)
  pose proof (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) as HJu.
  eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  { lazymatch goal with |- SRrG _ _ _ (mkCfg ?msq ?mdq) _ =>
    eapply (YCbqGwild.aj_call_xb_spR (fx := ip_fx P) (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PAI)
      (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
      (ip_W P) _ _ msq (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
      (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] (ip_ly P) (ip_S P) (ip_Hp P) mdq (ip_k P)
      (ie_CW E) STK_fuzz_free (if x =? 0 then [] else ablocks_fp [(x - cf_head, k + cf_head)]) (- (ie_e E + 144))
      _ chc _ _ HS eq_refl HJu) end.
    - rewrite Hspms, Hf0. lia.
    - replace (- (ie_e E + 144)) with ((- ((ie_e E + 144) / 16)) * 16)
        by (pose proof (Z.div_mod (ie_e E + 144) 16 ltac:(lia)); lia).
      apply Z_mod_mult.
    - lia.
    - exact vkb_stk_ff_nonneg.
    - pose proof (vkb_stk_ff (ie_d E)). lia.
    - rewrite P3. exact G3.
    - rewrite P4. exact G4.
    - exact P1.
    - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - unfold s0Z. rewrite P8, G8, HM. unfold w64. rewrite unsigned_lit_small by lia.
      replace (spZ (ie_regs E) + ie_e E + - (ie_e E + 144)) with (spZ (ip_regs P)) by lia.
      exact Hchc.
    - intros HPRE1. cbn [ss_pc setpc].
      refine (H_fuzz_free (ip_fx P) (ie_most E) (ie_own E) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P)
                (ms_regs ms) (ms_mem ms) _ chc x k (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
                _ _ _ _ _ _ _ _).
      + (* fpre *)
        split; [exact HPRE1|]. rewrite HM. split; [exact HROD|]. split; [rewrite Hspms; exact HTOP|].
        unfold raZ. rewrite P1. split; [exact vkb_ff_slot_ceil|].
        pose proof HJN as (_ & _ & Hfz & _). exact Hfz.
      + (* p <> 0 -> room_live_cf S *)
        intros _. pose proof HMD as (_ & _ & _ & M4 & _). exact (proj1 M4).
      + (* p <> 0 -> the live class-24 count at the call *)
        intros _. pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
        pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H240) & _).
        rewrite vkb_ccnt24_cnt. eapply Z.le_trans; [| exact H240]. apply Nat2Z.inj_le.
        rewrite (vc_gt_split E P HMD).
        change (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass)
                  (PresetRoom.rs_live (YGcfRoom.room_of_cf (ip_S P))))
          with (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass)
                  (PresetRoom.rs_live (YGcfRoom.room_of_cf (ip_S P))) (PresetReqAt.rd_hevs [])).
        exact (vi_pk_mid _ (ie_S E) (ip_S P) (ip_tr P) [] (snd (fst (ip_cont P []))) M10).
      + (* p <> 0 -> the hull budget for the free's empty list: the entry's, past the events so far
           (PresetHullBudget.hull_budget_infix with an empty callee list, over VrdCallPos.vc_gt_split) *)
        intros _. pose proof HMD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M11).
        pose proof HHB as HHB'. rewrite (vc_gt_split E P HMD), PresetHullBudget.hull_rd_app in HHB'.
        exact (PresetHullBudget.hull_budget_infix (ie_S E) (ip_S P) _ [] _ HHB' M11).
      + (* the free call's trace is admitted (the kit's cut) *)
        exact HADM.
      + (* a0 = the key *)
        rewrite P10. cbn [sv_denot]. rewrite E33. unfold w64.
        rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
      + (* the key is a block of the ledger *)
        right. exact HxL.
      + (* the ledger at the call state *)
        rewrite HM. exact Hled.
    - intros a Ha. rewrite (proj2 (Z.eqb_neq x 0) ltac:(lia)) in Ha. right. left.
      unfold ablocks_fp in Ha. destruct Ha as (r & Hr & Hlo). cbn [map In] in Hr.
      destruct Hr as [<- | []]. cbn [fst snd] in Hlo.
      exists (x - cf_head), (k + cf_head). split; [exact Habx|].
      split; [exact (HDnew x k HxD) | lia]. }
  (* fuzz_free returned to slot 6241 (row 309, `addi s2, zero, -1`), which falls through to A_IEPI_SLOT *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJc0 & HJg & HKR & HQ).
  (* the caller's composed journal at CW ++ WS1, WS1 within the free's one trace: back to the budget CW, by dropping
     a fixed trace (YCbqG.ajournal_xw_fix1R) or as one of CW's (YCbqG.ajx_budgetR over wild_incl_mono) *)
  assert (HJc' : ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
                   (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E)
                   (ie_mem E) (ie_md E) [] ly2 S2 Hp2 W2 mem2 md2 (ip_k P + k1) (ie_CW E)).
  { pose proof (vrd_wbudget_incl _ WS1 HPW) as Hws.
    destruct HTR as [Hfix | (Hcw & _)].
    - apply (ajournal_xw_fix1R Hfix). apply (ajx_budgetR _ HJc0).
      eapply wild_incl_mono; [|exact (ajxR_wild HJc0)].
      apply incl_app; [apply incl_appl, incl_refl | apply incl_appr; exact Hws].
    - apply (ajx_budgetR _ HJc0). eapply wild_incl_mono; [|exact (ajxR_wild HJc0)].
      apply incl_app; [apply incl_refl|]. intros t Ht. apply Hws in Ht. destruct Ht as [<- | []].
      rewrite HCW. exact Hcw. }
  (* the run of row 309 from it, rebased to the depot after the call (YCbqGwild.ajournal_xw_rebaseR) *)
  pose proof (ajxR_wild HJc') as HwC.
  pose proof (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc') as HJc.
  cbv beta delta [fQmn] in HQ. destruct HQ as (HQ & HMN2).
  rewrite HM in HJg, HMN2, HJu, HPM.
  pose proof (PCALL _ _ HMN2 HPM) as HPM2.
  rewrite (proj2 (Z.eqb_neq x 0) ltac:(lia)) in HJg.
  destruct HQ as (Hrl2 & HHU2 & _ & Hpos2 & _ & _ &
                  [(Hx0 & _) | (_ & _ & _ & (b1 & b2 & Eab1 & Eab2) & (l1 & l2 & ELam & HLED2))]);
    [lia|].
  specialize (Hrl2 ltac:(lia)). specialize (Hpos2 ltac:(lia)).
  assert (HXF2 : vc_xfer (ip_S P) S2 [PjGrammar.EFree (Z.to_nat k)]).
  { unfold vc_xfer. rewrite vkb_rd_hevs_free, Z2Nat.id, <- HI_head by lia. exact Hpos2. }
  replace (Z_to_bv 64 (BASE + 24964)) with (w64 (A_IPC 6241)) by (vm_compute; reflexivity).
  destruct (vk_st_ok (ip_fx P) W2 regs2 mem2 6241) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (vk_EI regs2)) by (unfold vk_EI; apply Eimg_env).
  pose (RUNTO2 := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_to_tok_x_inv RUNTO2 HS2 HJc SHOK2 HPM2 vk_Bspan (4 * Z.of_nat A_IEPI_SLOT);
    [ cbn; apply awr_ok_nil .. | ].
  replace (spZ (ie_regs E) + ie_e E + - (ie_e E + 144)) with (spZ (ip_regs P)) in HJg by lia.
  lazymatch goal with
  | HSe : st_ok_pi _ _ (vk_EI regs2) _ (restrict _ ?ms3), HF3 : frame_of (vk_EI regs2) _ mem2 (ms_mem ?ms3)
    |- SRrG _ _ _ {| cfg_ms := ?ms3; cfg_model := ?MD3 |} _ =>
    assert (HM3 : ms_mem ms3 = mem2) by (apply (vk_frame_ro_gen (vk_EI regs2) []); [constructor | exact HF3]);
    assert (EK : forall (r : bv 5) (n : nat), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
                   sv_denot (vk_EI regs2) (SOff n 0) = getr regs2 r)
      by (intros r n Hn Hr; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold vk_EI;
          rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 [] n r Hr));
    assert (R2x : getr (ms_regs ms3) (Z_to_bv 5 2) = getr regs2 (Z_to_bv 5 2))
      by (rewrite (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 2) HSe); exact (EK (Z_to_bv 5 2) 2%nat ltac:(lia) eq_refl));
    assert (R3x : getr (ms_regs ms3) (Z_to_bv 5 3) = getr regs2 (Z_to_bv 5 3))
      by (rewrite (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 3) HSe); exact (EK (Z_to_bv 5 3) 3%nat ltac:(lia) eq_refl));
    assert (R4x : getr (ms_regs ms3) (Z_to_bv 5 4) = getr regs2 (Z_to_bv 5 4))
      by (rewrite (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 4) HSe); exact (EK (Z_to_bv 5 4) 4%nat ltac:(lia) eq_refl));
    assert (R18x : getr (ms_regs ms3) 18 = w64 (-1));
    [ change (getr (ms_regs ms3) 18) with (getr (ms_regs ms3) (Z_to_bv 5 18));
      rewrite (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 18) HSe);
      lazymatch goal with |- sv_denot _ (sr_get ?l _) = _ =>
        let v := eval vm_compute in (sr_get l (Z_to_bv 5 18)) in change (sr_get l (Z_to_bv 5 18)) with v end;
      cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity
    | ];
    assert (Hsp3 : spZ (ms_regs ms3) = spZ (ip_regs P));
    [ unfold spZ; change (getr (ms_regs ms3) 2) with (getr (ms_regs ms3) (Z_to_bv 5 2));
      rewrite R2x, (HKR 2 ltac:(unfold acallee_saved; lia)); unfold spZ in Hspms; exact Hspms
    | ];
    assert (G3x : getr (ms_regs ms3) 3 = w64 (as_gp B));
    [ change (getr (ms_regs ms3) 3) with (getr (ms_regs ms3) (Z_to_bv 5 3));
      rewrite R3x, (HKR 3 ltac:(unfold acallee_saved; lia));
      change (getr (ms_regs ms) (Z_to_bv 5 3)) with (getr (ms_regs ms) 3); rewrite P3; exact G3
    | ];
    assert (G4x : getr (ms_regs ms3) 4 = w64 (as_tp B));
    [ change (getr (ms_regs ms3) 4) with (getr (ms_regs ms3) (Z_to_bv 5 4));
      rewrite R4x, (HKR 4 ltac:(unfold acallee_saved; lia));
      change (getr (ms_regs ms) (Z_to_bv 5 4)) with (getr (ms_regs ms) 4); rewrite P4; exact G4
    | ];
    pose proof (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HwC) as HJcu;
    destruct (vkb_free_exit CTX CTX0 CW E P x k nm _ ly2 S2 Hp2 W2 mem2 md2 MD3 k1 WS1 (ms_regs ms3) b1 b2 l1 l2
                HEN HRB HJu HJg ltac:(first [exact HJcu | rewrite <- HM3; exact HJcu]) Hsp3 G3x G4x R18x Hrl2 HXF2
                HHU2 Eab1 Eab2 ELam HLED2)
      as (D' & HEX);
    pmkst HSe; apply SRr'_ret;
    split; [| cbn [cfg_ms ms_mem mkst]; first [exact HPM2 | rewrite <- HM3; exact HPM2]];
    exists (vkb_P3 P ly2 S2 Hp2 W2 (ms_regs ms3) mem2 MD3 k1 D' (l1 ++ l2) k);
    split; [reflexivity|];
    split; [unfold vrd_cfg, vkb_P3; cbn [ip_regs ip_mem ip_md]; rewrite HM3; reflexivity | exact HEX]
  end.
Qed.
Lemma vk_c3_step_P : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop),
  srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c3 B ARx SK E P x k nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_C3_SLOT P)
    (fun W2 c2 =>
       ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ vrd_islot_a B ARx SK E P' nm /\
                    ip_n P' = ip_n P) \/
        (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
       Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW PCALL HEN HC3 HPM.
  pose proof HC3 as (_ & _ & _ & _ & Hcase).
  assert (Hdec : (ip_p P < ie_text E + ie_len E /\
                  nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 58) \/
                 (ip_p P = ie_text E + ie_len E \/
                  (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
                     PjGrammar.ws b = false /\ b <> 58))).
  { destruct Hcase as [Hend | (Hlt & b & Hnth & Hws)]; [right; left; exact Hend|].
    destruct (Z.eq_dec b 58) as [-> | Hne]; [left; split; assumption|].
    right; right; split; [exact Hlt|]. exists b. split; [exact Hnth|]. split; [exact Hws | exact Hne]. }
  destruct Hdec as [(Hlt & Hnth) | Href].
  - eapply SRr'_bind; [exact (vkb_c3_colon_a CTX CTX0 CW E P x k nm Pm PLAW HEN HC3 Hlt Hnth HPM)|].
    cbv beta. intros W2 c2 _ ((P2 & -> & -> & Hn2 & HCB) & HPM2).
    eapply SRr'_mono; [exact (vkb_c3_colon_b CTX CTX0 CW E P2 x k nm Pm PLAW HEN HCB HPM2)|].
    cbv beta. intros W3 c3 _ ((P3 & -> & -> & Hn3 & HSL) & HPM3).
    split; [|exact HPM3]. left. exists P3. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HSL | rewrite Hn3; exact Hn2].
  - eapply SRr'_bind; [exact (vkb_c3_ref CTX CTX0 CW E P x k nm Pm PLAW HEN HC3 Href HPM)|].
    cbv beta. intros W2 c2 _ ((P2 & -> & -> & _ & HRB) & HPM2).
    eapply SRr'_mono; [exact (vkb_refb_exit CTX CTX0 CW E P2 x k nm Pm PLAW PCALL HEN HRB HPM2)|].
    cbv beta. intros W3 c3 _ ((P3 & -> & -> & HEX) & HPM3).
    split; [|exact HPM3]. right. exists P3, (-1). split; [reflexivity|]. split; [reflexivity | exact HEX].
Qed.

Theorem vrd_ikey_okG : forall CTX CTX0 CW,
  (forall fxP : YK11.FPState, tparse_string_specX (fx := fxP) B ARx SK CTX0 CW) ->
  tvrd_ikey_aG B ARx SK CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW HPS Pm PLAW PCALL E P HEN HEL HPM.
  (* the exit and the islot arm of the target post, from each segment's own post *)
  assert (XIT : forall W2 c2 P2 res, W2 = ip_W P2 -> c2 = vrd_cfg A_IEPI_SLOT P2 -> vrd_iexit_a B ARx SK E P2 res ->
                  Pm (ms_mem (cfg_ms c2)) ->
                  ((exists P' nm, W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ vrd_islot_a B ARx SK E P' nm /\
                                  ip_n P' = ip_n P) \/
                   (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
                  Pm (ms_mem (cfg_ms c2))).
  { intros W2 c2 P2 res -> -> HX HP2. split; [|exact HP2]. right. exists P2, res. auto. }
  destruct (ie_o E) eqn:Ho.
  - (* an object: the key path *)
    eapply SRr'_bind; [(eapply vk_c0_P; eassumption)|].
    cbv beta. intros W1 c1 _ ((P1 & -> & Hn1 & [(-> & HW1) | (-> & HC1)]) & HPM1).
    + (* the first white-space loop, then C1 *)
      eapply SRr'_bind; [(eapply vk_w1_loop_P; eassumption)|].
      cbv beta. intros W1' c1' _ ((P1' & -> & -> & Hn1' & HC1') & HPM1').
      eapply SRr'_bind; [(eapply vk_c1_step_P; eassumption)|].
      cbv beta. intros Wc cc _ ((Pc & -> & Hnc & [(-> & HCALL) | (-> & HRA)]) & HPMc).
      * eapply SRr'_bind;
          [(eapply vk_call_step_P; eassumption)|].
        cbv beta. intros Wr cr _ ((Pr & -> & -> & Hnr & [HRR | (xk & kk & nmk & HRK)]) & HPMr).
        -- eapply SRr'_mono; [(eapply vk_c2R_step_P; eassumption)|].
           cbv beta. intros We ce _ ((Pe & HWe & Hce & HXe) & HPMe). exact (XIT We ce Pe (-1) HWe Hce HXe HPMe).
        -- eapply SRr'_bind;
             [(eapply vk_c2K_step_P; eassumption)|].
           cbv beta. intros Wk ck _ ((Pk & xk2 & kk2 & nmk2 & -> & Hnk & [(-> & HW2) | (-> & HC3)]) & HPMk).
           ++ eapply SRr'_bind;
                [(eapply vk_w2_loop_P; eassumption)|].
              cbv beta. intros W3 c3 _ ((P3 & -> & -> & Hn3 & HC3') & HPM3).
              eapply SRr'_mono; [exact (vk_c3_step_P CTX CTX0 CW E P3 xk2 kk2 nmk2 Pm PLAW PCALL HEN HC3' HPM3)|].
              cbv beta. intros W4 c4 _ ([(P4 & -> & -> & HSL & Hn4) | (P4 & res & HW4 & Hc4 & HX4)] & HPM4).
              ** split; [|exact HPM4]. left. exists P4, nmk2. split; [reflexivity|]. split; [reflexivity|].
                 split; [exact HSL|]. lia.
              ** exact (XIT _ _ P4 res HW4 Hc4 HX4 HPM4).
           ++ eapply SRr'_mono; [exact (vk_c3_step_P CTX CTX0 CW E Pk xk2 kk2 nmk2 Pm PLAW PCALL HEN HC3 HPMk)|].
              cbv beta. intros W4 c4 _ ([(P4 & -> & -> & HSL & Hn4) | (P4 & res & HW4 & Hc4 & HX4)] & HPM4).
              ** split; [|exact HPM4]. left. exists P4, nmk2. split; [reflexivity|]. split; [reflexivity|].
                 split; [exact HSL|]. lia.
              ** exact (XIT _ _ P4 res HW4 Hc4 HX4 HPM4).
      * apply SRr'_ret. apply (XIT _ _ Pc (-1) eq_refl eq_refl); [eapply vk_refA_exit; eassumption | exact HPMc].
    + (* C1 straight away *)
      eapply SRr'_bind; [(eapply vk_c1_step_P; eassumption)|].
      cbv beta. intros Wc cc _ ((Pc & -> & Hnc & [(-> & HCALL) | (-> & HRA)]) & HPMc).
      * eapply SRr'_bind;
          [(eapply vk_call_step_P; eassumption)|].
        cbv beta. intros Wr cr _ ((Pr & -> & -> & Hnr & [HRR | (xk & kk & nmk & HRK)]) & HPMr).
        -- eapply SRr'_mono; [(eapply vk_c2R_step_P; eassumption)|].
           cbv beta. intros We ce _ ((Pe & HWe & Hce & HXe) & HPMe). exact (XIT We ce Pe (-1) HWe Hce HXe HPMe).
        -- eapply SRr'_bind;
             [(eapply vk_c2K_step_P; eassumption)|].
           cbv beta. intros Wk ck _ ((Pk & xk2 & kk2 & nmk2 & -> & Hnk & [(-> & HW2) | (-> & HC3)]) & HPMk).
           ++ eapply SRr'_bind;
                [(eapply vk_w2_loop_P; eassumption)|].
              cbv beta. intros W3 c3 _ ((P3 & -> & -> & Hn3 & HC3') & HPM3).
              eapply SRr'_mono; [exact (vk_c3_step_P CTX CTX0 CW E P3 xk2 kk2 nmk2 Pm PLAW PCALL HEN HC3' HPM3)|].
              cbv beta. intros W4 c4 _ ([(P4 & -> & -> & HSL & Hn4) | (P4 & res & HW4 & Hc4 & HX4)] & HPM4).
              ** split; [|exact HPM4]. left. exists P4, nmk2. split; [reflexivity|]. split; [reflexivity|].
                 split; [exact HSL|]. lia.
              ** exact (XIT _ _ P4 res HW4 Hc4 HX4 HPM4).
           ++ eapply SRr'_mono; [exact (vk_c3_step_P CTX CTX0 CW E Pk xk2 kk2 nmk2 Pm PLAW PCALL HEN HC3 HPMk)|].
              cbv beta. intros W4 c4 _ ([(P4 & -> & -> & HSL & Hn4) | (P4 & res & HW4 & Hc4 & HX4)] & HPM4).
              ** split; [|exact HPM4]. left. exists P4, nmk2. split; [reflexivity|]. split; [reflexivity|].
                 split; [exact HSL|]. lia.
              ** exact (XIT _ _ P4 res HW4 Hc4 HX4 HPM4).
      * apply SRr'_ret. apply (XIT _ _ Pc (-1) eq_refl eq_refl); [eapply vk_refA_exit; eassumption | exact HPMc].
  - (* an array: no key *)
    eapply SRr'_mono; [(eapply vk_arr_P; eassumption)|].
    cbv beta. intros W2 c2 _ ((P2 & nm & -> & -> & Hn2 & HSL) & HPM2).
    split; [|exact HPM2]. left. exists P2, nm. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSL | exact Hn2].
Qed.

End KB.

Print Assumptions vrd_ikey_okG.

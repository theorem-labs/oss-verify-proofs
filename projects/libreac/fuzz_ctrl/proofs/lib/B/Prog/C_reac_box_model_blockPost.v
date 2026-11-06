(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): POST, the last piece of pb_reac_box_model_block (plan of
   record analyses/libreac/fuzz_ctrl/glue-B/model_block/pb_reac_box_model_block.plan.md, step 7 (a working note, not in this delivery)), a Theorem Labs lane.  From the journal after stretch B's frame
   release (GlueLift.rrB_journal_free at cid 0, lib/B/Prog/GlueLift.v; moved there from C_reac_box_model_blockPf.v), stretch B's final state (the re-based copy's Q0,
   C_reac_box_model_blockRB.v, related to the real final state by MemNorm.ms_rel) and the write facts of the three
   stretches (A: the window only; E0: the class-0 request's acall_kept; B: its own write list), it concludes the spec's
   post treac_box_model_block_post (lib/B/Prog/C_reac_box_model_block.v) at the real final configuration.

   rule 24: no function proved (glue of the proved run reac_box_model_block_holds_F; lookup of record
   lookup-reac_box_model_block.txt (a working note, not in this delivery), CONFIRM in lookup-check.md (a working note, not in this delivery)).

   mbB_kept: CtrlCallerJ.tcj_kept over the call's window [sp - 4272, sp) and the bytes E it writes, composed from
     A   munch over the window at the normalized memory (mb_pre_facts), back to the real memory by mem_rel / ro_same;
     E0  YCbq.aj_stack_malloc_at's acall_kept over [A - ESTACK, A), inside the window (A >= sp - 176);
     B   stretch B's writes Wr in rrB_journal_free's form, each byte in the window, the class-0 frame (0, pos), its
         shadow, its flag byte, or E.  The frame, shadow and flag are apart from every kept class by the AR laws at the
         state S2 after the request (sep_block_frame, sep_frames_pos, al_frames, al_flag, al_client_img); E is the
         caller's grant (never an image byte; readable at the end, so present).
   mbB_post: the spec's post: the configuration in mkst form, the journal, aregs_preserved from the restored
   registers, frames / ablocks after the free, a0 and the output block from the run's post, and mbB_kept.

   Section hypotheses (as rrB_journal_free takes them): LAWS (core), segs_low (core, PENDING THE RECORD CORE: its
   statement is Reusable.YCeg.tfib_segs_low, YCeg.v:64). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcSynth RcSynthLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c reac_box_model_block_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK0s YK14 YA0n YM05 YI16 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO0f YP09 YG00 YG01 YG0f YG0d YG0n YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlImg CtrlCallerJ C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require GlueLift.
#[local] Existing Instance CtrlImg.PI_ctrl_B.
Import ListNotations.
Open Scope Z_scope.

Section Post.
Context {fx : lib.Reusable.YK11.FPState} {rcl : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.

(* ---- small facts ------------------------------------------------------------------------------------------------ *)

(* Off a stretch's write set Wr the REAL final byte is the base byte: the stretch keeps the normalized byte off Wr,
   mem_rel relates the real and normalized end bytes off the read-only addresses, ro_same keeps the read-only ones
   (rrB_journal_gen's OFF step, at an address given as a Z). *)
Lemma mbB_off : forall (Wr : Z -> Prop) (m mn m' : word -> option byte),
  (forall x : word, ~ Wr (bv_unsigned x) -> mn x = B.MemNorm.normalize rsegs m x) ->
  B.MemNorm.mem_rel rsegs m' mn -> B.MemNorm.ro_same rsegs m m' ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros Wr m mn m' MU [REL1 _] ROS a Ha HWa.
  change (Z_to_bv 64 a) with (wa a).
  assert (Hx : ~ Wr (bv_unsigned (wa a))) by (rewrite wa_unsigned by exact Ha; exact HWa).
  destruct (ro_addr rsegs (wa a)) eqn:R; [exact (ROS _ R)|].
  pose proof (REL1 (wa a)) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
  pose proof (MU (wa a) Hx) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2.
  rewrite <- E1, E2. reflexivity.
Qed.

Lemma mbB_vw : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.aview rsegs H m' a = lib.Reusable.YG0n.aview rsegs H m a.
Proof.
  intros H m m' a E. apply lib.Reusable.YCbq.aview_eq_of. unfold lib.Reusable.YK04.mrestrict. cbv beta.
  rewrite E. reflexivity.
Qed.

Lemma mbB_pr : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.apresent H m a -> lib.Reusable.YG0n.apresent H m' a.
Proof. intros H m m' a E [Hh Hb]. split; [exact Hh | rewrite E; exact Hb]. Qed.

Lemma mbB_mbyte_vis : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict H m) a = mrd rsegs m (wa a).
Proof.
  intros H m a Hh. unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, mrd, wa. cbv beta.
  rewrite Hh. reflexivity.
Qed.

(* A shadow byte of a range below alloc_ceiling lies in the shadow band [SHADOW_OFF, kHighMemBeg), which holds no
   application byte. *)
Lemma mbB_shadow_band : forall x n a, 4096 <= x -> 0 <= n -> x + n <= lib.Reusable.YM05.alloc_ceiling ->
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr x, n / 8) ->
  lib.Reusable.YG0f.SHADOW_OFF <= a < lib.Reusable.YG0f.kHighMemBeg.
Proof.
  intros x n a Hx Hn Hc Ha. pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.shadow_addr in Ha. cbn [fst snd] in Ha.
  unfold lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kHighMemBeg in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mbB_app_not_band : forall lo len a, lib.Reusable.YG0f.in_app lo len -> lo <= a < lo + len ->
  lib.Reusable.YG0f.SHADOW_OFF <= a < lib.Reusable.YG0f.kHighMemBeg -> False.
Proof.
  intros lo len a Ha Hr Hb. unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg in Ha.
  unfold lib.Reusable.YG0f.SHADOW_OFF in Hb. lia.
Qed.

(* The shadow of two disjoint ranges is disjoint (floor x/8 + floor n/8 <= floor (x+n)/8). *)
Lemma mbB_shadow_disj : forall x nx y ny a, 0 <= nx -> 0 <= ny -> (x + nx <= y \/ y + ny <= x) ->
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr x, nx / 8) ->
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr y, ny / 8) -> False.
Proof.
  intros x nx y ny a Hnx Hny Hd Ha Hb.
  unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.shadow_addr in Ha, Hb. cbn [fst snd] in Ha, Hb.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mbB_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma mbB_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

(* the return address the spec's ret_ok premise names is even, so the run's `ret_pc ra` is ra *)
Lemma mbB_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, mbB_mod2_land; apply mbB_land_m2).
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact Hr | exact Hm].
Qed.

Local Ltac mb_reg H := etransitivity; [|exact (eq_sym H)]; reflexivity.

(* the restored callee-saved registers *)
Lemma mbB_saved : forall (regs : bvmap 5 word)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  lib.Reusable.YK11.getr regs 2 = sp -> lib.Reusable.YK11.getr regs 3 = gp -> lib.Reusable.YK11.getr regs 4 = tp ->
  lib.Reusable.YK11.getr regs 8 = s0 -> lib.Reusable.YK11.getr regs 9 = s1 ->
  lib.Reusable.YK11.getr regs 18 = s2 -> lib.Reusable.YK11.getr regs 19 = s3 ->
  lib.Reusable.YK11.getr regs 20 = s4 -> lib.Reusable.YK11.getr regs 21 = s5 ->
  lib.Reusable.YK11.getr regs 22 = s6 -> lib.Reusable.YK11.getr regs 23 = s7 ->
  lib.Reusable.YK11.getr regs 24 = s8 -> lib.Reusable.YK11.getr regs 25 = s9 ->
  lib.Reusable.YK11.getr regs 26 = s10 -> lib.Reusable.YK11.getr regs 27 = s11 ->
  lib.Reusable.YG0d.aregs_preserved regs
    (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros regs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
  unfold lib.Reusable.YG0d.acallee_saved in Hr.
  assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr0 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    [mb_reg H2 | mb_reg H3 | mb_reg H4 | mb_reg H8 | mb_reg H9 | mb_reg H18 | mb_reg H19 | mb_reg H20 |
     mb_reg H21 | mb_reg H22 | mb_reg H23 | mb_reg H24 | mb_reg H25 | mb_reg H26 | mb_reg H27].
Qed.

(* the class-0 frame released: the caller's frames are back *)
Lemma mbB_frames_free : forall (S2 Sc : lib.Reusable.YG00.astate) (pos : Z),
  lib.Reusable.YG01.frames S2 = (0, pos) :: lib.Reusable.YG01.frames Sc ->
  lib.Reusable.YG01.frames (lib.Reusable.YG01.stack_free_state 0 pos S2) = lib.Reusable.YG01.frames Sc.
Proof.
  intros S2 Sc pos H. unfold lib.Reusable.YG01.stack_free_state, lib.Reusable.YG01.frames in *.
  cbn [lib.Reusable.YG00.set_fs lib.Reusable.YG00.st_fs lib.Reusable.YG00.fs_live]. rewrite H.
  cbn [lib.Reusable.YG00.del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

(* the bytes the call writes outside its window and its class-0 frame: the output block when p and o are not 0
   (the E of the spec's post, both arms) *)
Definition mbB_E (p o : Z) (a : Z) : Prop :=
  if (p =? 0) || (o =? 0) then False else C_reac_box_model_block.treac_box_model_block_out o a.

Section Kept.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
(* core, PENDING THE RECORD CORE (YCeg.v:25 refused name); its statement is Reusable.YCeg.tfib_segs_low (YCeg.v:64) *)
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

(* ---- tcj_kept of the whole call ------------------------------------------------------------------------------- *)
Lemma mbB_kept :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
         (W : lib.Reusable.YA0n.world rsegs) (memc : word -> option byte) (sp : Z)
         (m1 mcA : word -> option byte) (A : Z) S2 (mem2 : word -> option byte) md2 k (pos : Z)
         (m3 mcB : word -> option byte) md3 (Wr E : Z -> Prop),
    sp0 - STK <= sp - 4272 -> sp <= sp0 -> sp mod 16 = 0 ->
    (* A: the window only *)
    munch [(sp - 4272, sp)] (B.MemNorm.normalize rsegs memc) mcA ->
    B.MemNorm.mem_rel rsegs m1 mcA -> B.MemNorm.ro_same rsegs memc m1 ->
    (* E0: the class-0 request at A *)
    A = (sp - 160) / 32 * 32 ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
    lib.Reusable.YG01.frames S2 = (0, pos) :: lib.Reusable.YG01.frames Sc ->
    lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
    lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
      (sp0 + (A - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (A - sp0)) (fun _ => False) ->
    (* B: its own writes Wr *)
    (forall x : word, ~ Wr (bv_unsigned x) -> mcB x = B.MemNorm.normalize rsegs mem2 x) ->
    B.MemNorm.mem_rel rsegs m3 mcB -> B.MemNorm.ro_same rsegs mem2 m3 ->
    (forall a, Wr a ->
       (sp - 4272 <= a < sp) \/
       lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (0, pos)) \/
       lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc 0 pos),
                                  lib.Reusable.YG00.fs_frame_bytes 0 / 8) \/
       a = lib.Reusable.YG0f.flag_addr lyc 0 pos \/ E a) ->
    (* E: the caller's grant: never an image byte, readable at the end *)
    (forall a, E a \/ ~ E a) ->
    (forall a, E a -> ~ lib.Reusable.YG0d.in_img rsegs a) ->
    (forall a, E a -> exists v, mrd rsegs mcB (wa a) = Some v) ->
    (* the journal after the free (its window presence) *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
      (lib.Reusable.YG01.stack_free_state 0 pos S2) W m3 md3 k ->
    CtrlCallerJ.tcj_kept B C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK lyc Sc W memc W m3 sp E.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc sp m1 mcA A S2 mem2 md2 k pos m3 mcB md3 Wr E
    Hlo Hhi H16 MUA RELA ROSA HA HJ2 HFR HAB K0 MUB RELB ROSB HWr HEdec HEimg HErd HJ3.
  unfold CtrlCallerJ.tcj_kept, C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK.
  pose proof HJ2 as (HAR2 & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk3 & _).
  destruct Hstk3 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  assert (HAb : sp - 176 <= A <= sp - 160) by (rewrite HA; Z.div_mod_to_equations; lia).
  assert (Es : lib.Reusable.YG0d.ESTACK = 4096) by reflexivity.
  assert (Hin0 : In (0, pos) (lib.Reusable.YG01.frames S2)) by (rewrite HFR; left; reflexivity).
  assert (HinS : forall c q, In (c, q) (lib.Reusable.YG01.frames Sc) -> In (c, q) (lib.Reusable.YG01.frames S2))
    by (intros c q H; rewrite HFR; right; exact H).
  pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg 0) as Hn0.
  destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hin0) as (F0lo & F0hi & _).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc S2 W mem2 md2 0 pos HAR2 Hin0) as (_ & F0app & _ & _).
  destruct (lib.Reusable.YG0d.al_flag _ _ LAWS lyc S2 W mem2 md2 0 pos HAR2 Hin0) as (_ & FLo & _ & FLhi).
  (* the real end memories off the stretches' writes *)
  assert (OFFA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 4272 <= a < sp) -> m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { apply (mbB_off (fun a => sp - 4272 <= a < sp) memc mcA m1); [|exact RELA | exact ROSA].
    intros x Hx. apply MUA. cbn [outside]. split; [exact Hx | exact I]. }
  pose proof (mbB_off Wr mem2 mcB m3 MUB RELB ROSB) as OFFB.
  destruct K0 as (K1 & K2 & K3 & K4 & K5 & _).
  (* a high byte outside the window and off E is not written by B *)
  assert (NW1 : forall a, lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - 4272 <= a < sp) -> ~ E a ->
                  ~ Wr a).
  { intros a Ha Hw Hne HW. destruct (HWr a HW) as [H|[H|[H|[H|H]]]].
    - exact (Hw H).
    - unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in H. cbn [fst snd] in H. lia.
    - pose proof (mbB_shadow_band _ _ _ F0lo Hn0 F0hi H) as Hb.
      unfold lib.Reusable.YG0f.kHighMemBeg in Hb. lia.
    - lia.
    - exact (Hne H). }
  split; [|split; [|split; [|split; [|split]]]].
  - (* high memory outside the window, off E *)
    intros a Ha Hw Hne.
    assert (G : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m3 a =
                lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
    { rewrite (mbB_vw _ _ _ _ (OFFB a ltac:(lia) (NW1 a Ha Hw Hne))).
      rewrite (K1 a Ha ltac:(rewrite Es; lia)).
      apply mbB_vw. apply OFFA; lia. }
    exact G.
  - (* the caller's blocks, off E *)
    intros b0 m0 i Hb Hi HnE.
    assert (Hb2 : In (b0, m0) (lib.Reusable.YG0d.ablocks B lyc S2)) by (rewrite HAB; exact Hb).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc S2 W mem2 md2 b0 m0 HAR2 Hb2) as (_ & Bl & Bh & Bapp & Bo & _).
    pose proof (lib.Reusable.YCbq.sep_block_frame rsegs B LAWS lyc S2 W mem2 md2 b0 m0 0 pos HAR2 Hb2 Hin0) as Hd.
    unfold lib.Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    assert (NW : ~ Wr (b0 + i)).
    { intros HW. destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
      - lia.
      - unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in H. cbn [fst snd] in H. lia.
      - exact (mbB_app_not_band _ _ (b0 + i) Bapp ltac:(lia) (mbB_shadow_band _ _ _ F0lo Hn0 F0hi H)).
      - apply (proj2 (Bo (b0 + i) ltac:(lia))). rewrite H. exact FLo.
      - exact (HnE H). }
    assert (G : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m3 (b0 + i) =
                lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc (b0 + i)).
    { rewrite (mbB_vw _ _ _ _ (OFFB (b0 + i) ltac:(lia) NW)).
      rewrite (K2 b0 m0 i Hb Hi (fun H => H)).
      apply mbB_vw. apply OFFA; lia. }
    exact G.
  - (* the image, but owned-static and errno bytes *)
    intros a Himg Hns Herr.
    pose proof (segs_low a Himg) as Hlow.
    pose proof (lib.Reusable.YG0d.al_client_img _ _ LAWS lyc S2 W mem2 md2 a HAR2) as CI.
    assert (NW : ~ Wr a).
    { intros HW. destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
      - unfold lib.Reusable.YG0f.kLowMemEnd in Hlow. lia.
      - unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in H. cbn [fst snd] in H.
        exact (proj2 (CI (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin0 H)))))) Himg).
      - pose proof (mbB_shadow_band _ _ _ F0lo Hn0 F0hi H) as Hb.
        unfold lib.Reusable.YG0f.SHADOW_OFF in Hb. unfold lib.Reusable.YG0f.kLowMemEnd in Hlow. lia.
      - exact (proj2 (CI (or_intror (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin0 H)))))) Himg).
      - exact (HEimg a H Himg). }
    assert (G : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m3 a =
                lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
    { unfold lib.Reusable.YG0f.kLowMemEnd in Hlow.
      rewrite (mbB_vw _ _ _ _ (OFFB a ltac:(lia) NW)).
      rewrite (K3 a Himg Hns Herr).
      apply mbB_vw. apply OFFA; lia. }
    exact G.
  - (* the caller's frames and their shadow, off E *)
    intros cid q a Hin Hr HnE.
    pose proof (HinS cid q Hin) as Hin2.
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc S2 W mem2 md2 cid q HAR2 Hin2) as (Qlo & Qhi & Qapp).
    destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc S2 W mem2 md2 cid q HAR2 Hin2) as (_ & _ & Qb & Qs).
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg cid) as Qn.
    destruct (in_split _ _ Hin) as (l1 & l2 & El).
    pose proof (lib.Reusable.YCbq.sep_frames_pos rsegs B LAWS lyc S2 W mem2 md2 (0, pos) (cid, q) [] l1 l2 HAR2
                  ltac:(rewrite HFR, El; reflexivity)) as Hd.
    unfold lib.Reusable.YG0f.zdisjoint, lib.Reusable.YCbq.frame_rng in Hd. cbn [fst snd] in Hd.
    assert (Ha64 : 0 <= a < lib.Reusable.YM05.alloc_ceiling).
    { destruct Hr as [Hr' | Hr'].
      - unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr'. cbn [fst snd] in Hr'. lia.
      - pose proof (mbB_shadow_band _ _ _ Qlo Qn Qhi Hr') as Hb.
        unfold lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kHighMemBeg in Hb. lia. }
    assert (NW : ~ Wr a).
    { intros HW. destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
      - lia.
      - unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in H. cbn [fst snd] in H.
        destruct Hr as [Hr' | Hr'].
        + unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr'. cbn [fst snd] in Hr'. lia.
        + exact (mbB_app_not_band _ _ _ F0app H (mbB_shadow_band _ _ _ Qlo Qn Qhi Hr')).
      - destruct Hr as [Hr' | Hr'].
        + unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr'. cbn [fst snd] in Hr'.
          exact (mbB_app_not_band _ _ _ Qapp Hr' (mbB_shadow_band _ _ _ F0lo Hn0 F0hi H)).
        + exact (mbB_shadow_disj _ _ _ _ _ Hn0 Qn Hd H Hr').
      - destruct Hr as [Hr' | Hr'].
        + unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr'. cbn [fst snd] in Hr'.
          apply (proj2 (Qb a Hr')). rewrite H. exact FLo.
        + unfold lib.Reusable.YG0n.in_zr in Hr'. cbn [fst snd] in Hr'.
          pose proof (Qs (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid q)) ltac:(lia))
            as (_ & Hno).
          replace (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid q) +
                   (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid q))) with a in Hno
            by lia.
          apply Hno. rewrite H. exact FLo.
      - exact (HnE H). }
    assert (G : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m3 a =
                lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
    { rewrite (mbB_vw _ _ _ _ (OFFB a ltac:(lia) NW)).
      rewrite (K4 cid q a Hin Hr (fun H => H)).
      apply mbB_vw. apply OFFA; lia. }
    exact G.
  - (* presence of a high byte outside the window *)
    intros a Ha Hw Hp.
    destruct (HEdec a) as [He | Hne].
    + (* a byte of E: the run leaves it readable, and above the image a readable byte is present *)
      split; [exact (proj1 Hp)|].
      destruct (HErd a He) as (v & Hv).
      assert (R : ro_addr rsegs (wa a) = false)
        by (apply B.MemNormTr.ro_addr_above_img; unfold ImgBounds.IMG_HI; lia).
      pose proof RELB as [RB1 _]. pose proof (RB1 (wa a)) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
      unfold mrd in Hv. destruct (mcB (wa a)) as [c|] eqn:Ec.
      * exists c. change (Z_to_bv 64 a) with (wa a). rewrite <- E1. first [reflexivity | exact Ec].
      * try rewrite Ec in Hv.
        rewrite (GlueLift.rrB_seg_rom_above a ltac:(unfold ImgBounds.IMG_HI; lia)) in Hv.
        discriminate Hv.
    + apply (mbB_pr _ _ _ _ (OFFB a ltac:(lia) (NW1 a Ha Hw Hne))).
      apply (K5 a Ha ltac:(rewrite Es; lia)).
      apply (mbB_pr _ _ _ _ (OFFA a ltac:(lia) Hw)). exact Hp.
  - (* the window is present at the end (the caller's journal window contains it) *)
    intros a Ha. apply Hpres3. lia.
Qed.

(* ---- the spec's post ------------------------------------------------------------------------------------------- *)
Lemma mbB_post :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
         (W : lib.Reusable.YA0n.world rsegs) (memc : word -> option byte) k (regs : bvmap 5 word)
         (p b o : Z) (row nb : list byte)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (m1 mcA : word -> option byte) (A : Z) S2 (mem2 : word -> option byte) md2 (pos FS : Z)
         (sN ms' : machine_state) md3 (Wr : Z -> Prop),
    (* the entry registers, as the stretches name them *)
    lib.Reusable.YK11.getr regs 1 = ra -> lib.Reusable.YK11.getr regs 2 = sp ->
    lib.Reusable.YK11.getr regs 3 = gp -> lib.Reusable.YK11.getr regs 4 = tp ->
    lib.Reusable.YK11.getr regs 8 = s0 -> lib.Reusable.YK11.getr regs 9 = s1 ->
    lib.Reusable.YK11.getr regs 18 = s2 -> lib.Reusable.YK11.getr regs 19 = s3 ->
    lib.Reusable.YK11.getr regs 20 = s4 -> lib.Reusable.YK11.getr regs 21 = s5 ->
    lib.Reusable.YK11.getr regs 22 = s6 -> lib.Reusable.YK11.getr regs 23 = s7 ->
    lib.Reusable.YK11.getr regs 24 = s8 -> lib.Reusable.YK11.getr regs 25 = s9 ->
    lib.Reusable.YK11.getr regs 26 = s10 -> lib.Reusable.YK11.getr regs 27 = s11 ->
    (* the spec's premises at memc that the post reads *)
    lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) ->
    lib.Reusable.YG0d.spZ regs mod 16 = 0 ->
    sp0 - STK <= lib.Reusable.YG0d.spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK ->
    lib.Reusable.YG0d.spZ regs <= sp0 ->
    (p <> 0 -> length row = 296%nat) ->
    (o <> 0 -> forall x, o <= x < o + 32 ->
       ~ lib.Reusable.YG0d.in_img rsegs x /\ lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memc x) ->
    (* A (mbB_to_E0's continuation): its window-only write, its real end memory m1 *)
    munch [(bv_unsigned sp - 4272, bv_unsigned sp)] (B.MemNorm.normalize rsegs memc) mcA ->
    B.MemNorm.mem_rel rsegs m1 mcA -> B.MemNorm.ro_same rsegs memc m1 ->
    (* E0 (mbB_E0's continuation) *)
    A = (bv_unsigned sp - 160) / 32 * 32 ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
    lib.Reusable.YG01.frames S2 = (0, pos) :: lib.Reusable.YG01.frames Sc ->
    lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
    lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
      (sp0 + (A - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (A - sp0)) (fun _ => False) ->
    (* B (rrB_lift o mb_post_rebaseRB): the run's post at the normalized end state sN, the real end state ms', and
       its own writes Wr in rrB_journal_free's form, classified *)
    reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (B.MemNorm.normalize rsegs mem2) p b o FS row nb sN ->
    B.MemNorm.ms_rel rsegs ms' sN -> B.MemNorm.ro_same rsegs mem2 (ms_mem ms') ->
    (forall x : word, ~ Wr (bv_unsigned x) -> ms_mem sN x = B.MemNorm.normalize rsegs mem2 x) ->
    (forall a, Wr a ->
       (bv_unsigned sp - 4272 <= a < bv_unsigned sp) \/
       lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (0, pos)) \/
       lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc 0 pos),
                                  lib.Reusable.YG00.fs_frame_bytes 0 / 8) \/
       a = lib.Reusable.YG0f.flag_addr lyc 0 pos \/
       (if (p =? 0) || (o =? 0) then False else C_reac_box_model_block.treac_box_model_block_out o a)) ->
    (* the journal after B's free (rrB_journal_free at cid 0) *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
      (lib.Reusable.YG01.stack_free_state 0 pos S2) W (ms_mem ms') md3 k ->
    C_reac_box_model_block.treac_box_model_block_post B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc k regs
      p b o row nb W (mkCfg ms' md3).
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc k regs p b o row nb
    ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mcA A S2 mem2 md2 pos FS sN ms' md3 Wr
    Hr1 Hr2 Hr3 Hr4 Hr8 Hr9 Hr18 Hr19 Hr20 Hr21 Hr22 Hr23 Hr24 Hr25 Hr26 Hr27
    Hret H16 Hlo Hhi Hrow Ho MUA RELA ROSA HA HJ2 HFR HAB K0 HQ HREL HROS MUB HWr HJ3.
  assert (Hsp : lib.Reusable.YG0d.spZ regs = bv_unsigned sp)
    by (unfold lib.Reusable.YG0d.spZ; rewrite Hr2; reflexivity).
  rewrite Hsp in H16, Hlo, Hhi. unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK in Hlo.
  rewrite Hr1 in Hret.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Es &
                  Hbr & _).
  rewrite Es in HREL.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
  assert (MUB' : forall x : word, ~ Wr (bv_unsigned x) -> m' x = B.MemNorm.normalize rsegs mem2 x)
    by (intros x Hx; rewrite <- (MUB x Hx), Es; reflexivity).
  (* the bytes the call writes: the output block, when p and o are not 0 *)
  assert (HEdec : forall a, mbB_E p o a \/ ~ mbB_E p o a).
  { intros a. unfold mbB_E. destruct ((p =? 0) || (o =? 0)); [right; intros []|].
    unfold C_reac_box_model_block.treac_box_model_block_out. lia. }
  assert (HEimg : forall a, mbB_E p o a -> ~ lib.Reusable.YG0d.in_img rsegs a).
  { intros a Ha. unfold mbB_E in Ha. revert Ha. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros Ha; [destruct Ha|].
    apply Bool.orb_false_iff in Epo as [_ Eo]. apply Z.eqb_neq in Eo. exact (proj1 (Ho Eo a Ha)). }
  assert (HErd : forall a, mbB_E p o a -> exists v, mrd rsegs m' (wa a) = Some v).
  { intros a Ha. unfold mbB_E in Ha. revert Ha Hbr. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros Ha Hbr;
      [destruct Ha|].
    destruct Hbr as ((_ & _ & HB3) & _).
    apply Bool.orb_false_iff in Epo as [Ep _]. apply Z.eqb_neq in Ep.
    pose proof (rs_synth_len row b nb (Hrow Ep)) as HL.
    unfold C_reac_box_model_block.treac_box_model_block_out in Ha.
    assert (Hj : (Z.to_nat (a - o) < length (synth row b nb))%nat) by (rewrite HL; lia).
    pose proof (HB3 _ Hj) as Ev. rewrite (nth_error_nth' _ (Z_to_bv 8 0) Hj) in Ev.
    replace (o + Z.of_nat (Z.to_nat (a - o))) with a in Ev by lia.
    eexists. exact Ev. }
  pose proof (mbB_kept STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc (bv_unsigned sp) m1 mcA A S2 mem2 md2 k pos
                (ms_mem ms') m' md3 Wr (mbB_E p o) Hlo Hhi H16 MUA RELA ROSA HA HJ2 HFR HAB K0 MUB' HMR HROS HWr
                HEdec HEimg HErd HJ3) as KEPT.
  assert (ER : ms_regs ms' =
               mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if (p =? 0) || (o =? 0) then -1 else RcSynth.rc row b))
                 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
    by exact (f_equal ms_regs Ems).
  assert (Ems2 : ms' = lib.Reusable.YK11.mkst (ms_regs ms') (lib.Reusable.YK11.getr regs 1) (ms_mem ms')
                         (lib.Reusable.YK11.seg_rom rsegs)).
  { rewrite Hr1. etransitivity; [exact Ems|]. rewrite (mbB_ret_pc ra Hret), ER. reflexivity. }
  unfold C_reac_box_model_block.treac_box_model_block_post.
  exists lyc, (lib.Reusable.YG01.stack_free_state 0 pos S2), (ms_regs ms'), (ms_mem ms'), md3.
  split; [exact (f_equal (fun s => mkCfg s md3) Ems2)|].
  split; [unfold C_reac_box_model_block.EV_BMB; rewrite Z.add_0_r; exact HJ3|].
  split; [rewrite ER; exact (mbB_saved regs ra sp gp tp t0' t1' t2' s0 s1 _ a1' a2' a3' a4' a5' a6' a7'
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' Hr2 Hr3 Hr4 Hr8 Hr9 Hr18 Hr19 Hr20
                               Hr21 Hr22 Hr23 Hr24 Hr25 Hr26 Hr27)|].
  split; [exact (mbB_frames_free S2 Sc pos HFR)|].
  split.
  { unfold lib.Reusable.YG0d.ablocks in HAB |- *. rewrite lib.Reusable.YG01.blocks_stack_free_state. exact HAB. }
  rewrite Hsp, ER.
  unfold mbB_E in KEPT. revert KEPT Hbr.
  destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros KEPT Hbr.
  - split; [reflexivity | exact KEPT].
  - apply Bool.orb_false_iff in Epo as [Ep Eo]. apply Z.eqb_neq in Ep, Eo.
    destruct Hbr as (HBY & _).
    pose proof (proj2 (B.MemNorm.bytes_at_rel rsegs (ms_mem ms') m' o _ HMR) HBY) as (_ & _ & HB3).
    pose proof (rs_synth_len row b nb (Hrow Ep)) as HL.
    split; [reflexivity|]. split; [|exact KEPT].
    unfold C_reac_box_model_block.bmb_z.
    intros j Hj. rewrite length_map in Hj.
    assert (Hj32 : (j < 32)%nat) by (rewrite <- HL; exact Hj).
    assert (Hn : nth j (map (fun x : byte => bv_unsigned x) (synth row b nb)) 0 =
                 bv_unsigned (nth j (synth row b nb) (Z_to_bv 8 0))).
    { rewrite <- (map_nth (fun x : byte => bv_unsigned x)). reflexivity. }
    rewrite Hn. pose proof (bv_unsigned_in_range 8 (nth j (synth row b nb) (Z_to_bv 8 0))) as R8.
    change (bv_modulus 8) with 256 in R8.
    split; [|lia].
    intros kk Hk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
    assert (Hh : lib.Reusable.YA0n.w_H W (Z_to_bv 64 (o + Z.of_nat j)) = false)
      by exact (proj1 (proj2 (Ho Eo (o + Z.of_nat j) ltac:(lia)))).
    transitivity (mrd rsegs (ms_mem ms') (wa (o + Z.of_nat j))); [exact (mbB_mbyte_vis _ _ _ Hh)|].
    rewrite (HB3 j Hj), (nth_error_nth' (synth row b nb) (Z_to_bv 8 0) Hj). f_equal.
    unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256 R8).
    apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
End Kept.
End Post.

Print Assumptions mbB_kept.
Print Assumptions mbB_post.

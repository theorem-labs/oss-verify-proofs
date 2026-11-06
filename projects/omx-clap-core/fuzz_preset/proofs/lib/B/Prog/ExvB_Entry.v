(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value (B 0x8352c): the ENTRY segment C0 of its walk, i.e. ExvB_Top.v's Section hypothesis `seg_entry`
     forall n, (forall fx, CUT_C1 B ARx SK n) -> forall fx, CUT_C0 B ARx SK n
   with `EXV_HYP B ARx SK ->` added, over ExvB_Stmt.v's statements. The segment runs B 0x8352c .. 0x83644
   (`jal ex_ws`), and its work is to establish `EXB` and CUT_C1's two extra premises at the return site 0x83648.
   SHAPE (the three stretches are this file's helper lemmas, each in its own file):
   - `ExvB_Entry_r1.exve_run1`: the prologue 0x8352c-0x8359c, ending at the entry of __asan_stack_malloc_1
     (frame_alloc_1, outside the listing range), with the 13 callee-saved slots and sp = s1 = `exv_s1 E`.
     The use-after-return flag is 1 (`alx_const`), so `beqz a2` at 0x83594 is not taken and the frame call is made.
   - the frame call itself: `YGcallSx.aj_stack_malloc_at_x` at `eh_sm1` / `eh_sm1_pc`, class 1, which returns the
     frame f = `frame_addr lyc 1 pos`, its zero shadow, the flag pointer at f + 120 and `acall_kept_x`.
     f <> 0, so the alloca probe loop 0x835b4-0x835cc is unreachable.
   - `ExvB_Entry_r2.exve_run2`: 0x835a0-0x83644, the frame slot 176(s1), the frame header and the twelve shadow
     bytes of the frame, ending at ex_ws's entry.
   - the ex_ws call: `YCbqGcallW.aj_call_xW` over the PROVED walk (`exv_ws HYP fx`), at o = s1 - (sp + d),
     e1 = sp + d - s1, FP1 = [(q, q + 8)]; then CUT_C1 at 0x83648.
   - `ExvB_Entry_kit.v` carries the transports (ledger, read-only view, the call's frame chain, bytes, cursor,
     tree) and `ExvB_Open_sh.v` (ExvOpen) the shadow facts of the text, the scratch and the Lam tree nodes.
   PINS: checked against B_prog_listing (lib/B/Listing_prog.v, image B sha256 f8f98a95bc52..., slot k = byte offset
   4k from B_prog_base = 0x816cc): ex_value's entry is slot 1944, `jal frame_alloc_1` slot 1972
   (= `PCall AS___asan_stack_malloc_1`), `jal ex_ws` slot 2014 (= `PCall AS_ex_ws`), the C1 cut slot 2015; 72 slots
   of the stretch compared with the neutral listing of record, 0 mismatches.
   NUMERALS: 288 / 304 / 320 / 176 / 184 / 96 / 128 / 120 / 24 / 16 / 12 / 8 / 4 / 0 and the thirteen save-area
   offsets 184..280 (LENGTH: the body's own frame and slot offsets); 116 / 284 (DERIVED: 0x74 and 0x11c, the two
   return sites, as offsets from B_prog_sigma AS_ex_value); 7892 / 1944 / 1972 / 2014 / 2015 / 2794 (DERIVED: listing
   slots); 16688 / 16384 (LENGTH: STK_ex_value's own bound); 2 ^ 64 / 2 ^ 47 / 2 ^ 46 / 4096 (LENGTH / DERIVED:
   address-space and stack bounds); 1 (WORD: the use-after-return flag, and the frame class). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03 YP0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC80x YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Open_sh ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Entry_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Entry_r1 ExvB_Entry_r2 ExvB_Entry_fr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kit ExvB_Loop_kitQ ExvB_Loop_kitP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* S1ImgB / S1ImgA bring image A's listing instance PI_prog_A into scope, so image B's are declared again HERE:
   a later Existing Instance wins resolution, and every world of this file is a `world rsegs` *)
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PL_prog_B.
#[local] Existing Instance PI_prog_B.

(* ---- the two return sites of the segment, as listing slots (DERIVED) ---- *)
Lemma exve_ret1_slot : B_prog_sigma AS_ex_value + 116 = B_prog_base + 7892.
Proof. vm_compute. reflexivity. Qed.
Lemma exve_c1_slot : B_prog_sigma AS_ex_value + 284 = B_prog_base + 8060.
Proof. vm_compute. reflexivity. Qed.
Lemma exve_c1_pc : exv_pc 0x11c = B_prog_sigma AS_ex_value + 284.
Proof. reflexivity. Qed.

(* ex_value's stack need at every nesting: its own 304-byte frame per level over the largest runtime need
   (STK_RT_STRTOD = 4 * ESTACK), so every level is far above the 320 bytes the prologue itself uses and the
   ESTACK the frame-area call asks below the realigned sp *)
Lemma exve_stk_lo : forall n : nat, 16688 <= STK_ex_value n.
Proof.
intros n. unfold STK_ex_value.
assert (Hf : @pi_frame prh_img_B F_ex_value = 304) by reflexivity.
assert (Hz : zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; @STK_ex_string prh_img_B; @STK_ex_word prh_img_B;
  @STK_ex_ws prh_img_B] = 16384) by (vm_compute; reflexivity).
rewrite Hf, Hz. pose proof (Nat2Z.is_nonneg n) as Hn. rewrite Nat2Z.inj_succ. nia.
Qed.

Section e. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
(* every live fake frame has one of the fake stack's classes: EXV_HYP's eh_frames_cid (h-rw-pre-7 agreed the field
   on this lane's ask). The entry needs it where the expected tree's ROOT lies in a live fake frame (prhex_home's
   second arm): the root's shadow bytes are inside that frame's own 16, which is what the kept package keeps, and
   placing them there needs 8 | fs_frame_bytes cid, i.e. 0 <= cid. *)
Definition EXVE_FRAMES_CID : forall ly S Hp (W : world rsegs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 0 <= cid <= 10 :=
  eh_frames_cid B ARx SK HYP.

(* the five alloc.c statics the ledger reads are image bytes, are not runtime-owned (eh_pst_own) and are not
   errno's four bytes (eh_errno_B at image B's YF0m.TFIB_ERRNO; both sides are generated numbers) *)
Lemma exve_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img rsegs a.
Proof. exact S1ImgB.pst_in_img_B. Qed.

Lemma exve_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (eh_errno_B B ARx SK HYP).
assert (Hb : S1ImgCheck.pst_allb (fun x => negb ((YF0m.TFIB_ERRNO <=? x) && (x <? YF0m.TFIB_ERRNO + 4)))
  (@prh_pst prh_img_B) = true) by (vm_compute; reflexivity).
pose proof (S1ImgCheck.pst_allb_sound _ _ a Hb Ha) as H. cbv beta in H.
apply negb_true_iff in H. apply andb_false_iff in H as [H | H];
  [apply Z.leb_gt in H | apply Z.ltb_ge in H]; lia.
Qed.
(* the layout the journal ends at names the same frames and the same flag bytes (alx_layout gives the frame
   addresses; the flag offset is the same function of ly_F) *)
Lemma exve_flag_layout : forall ly ly' (S : astate) Hp (W : world rsegs) mem md cid pos,
  ARx ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros ly ly' S Hp W mem md cid pos HAR Hle.
destruct (alx_layout rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md ly' HAR Hle) as (_ & Hfr & _).
pose proof (Hfr cid pos) as Hf. split; [exact Hf|].
unfold frame_addr in Hf. unfold flag_addr. assert (HF : ly_F ly' = ly_F ly) by lia. rewrite HF. reflexivity.
Qed.

(* the cursor's shadow: it lies on the REAL STACK, whose every granule the runtime keeps at shadow 0
   (alx_zshadow_byte), so the fact holds at every allocator state, before and after a call *)
Lemma exve_stack_ra : forall ly S Hp (W : world rsegs) mem md (x n : Z),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S Hp W mem md x n HAR Hlo Hhi z Hz. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
apply (alx_zshadow_byte rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md z HAR). lia.
Qed.

(* the geometry the two calls and the two runs ask: the entry sp, the realigned base s1, the caller window and the
   stack bounds (astk_ok and fwin of EXV_PRE's fpre, with ExvB_Open_kt's exv_s1_le for the realignment) *)
Lemma exve_geom : forall E, EXV_PRE B ARx E ->
  exv_sp E mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo (e_ly E) /\
  ly_stk_lo (e_ly E) + exv_STK E <= exv_sp E /\ exv_sp E + 64 <= ly_stk_hi (e_ly E) /\
  ly_stk_hi (e_ly E) <= 2 ^ 47 /\ exv_sp E + e_d E <= ly_top (e_ly E) /\
  ly_top (e_ly E) <= ly_stk_hi (e_ly E) /\ 16688 <= exv_STK E /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\
  exv_sp E - 319 <= exv_s1 E /\ exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0.
Proof.
intros E HPRE. unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & _).
destruct HFP as (HFN & _ & H64 & _).
destruct HFN as (_ & _ & _ & _ & _ & Hastk & _).
destruct Hastk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HWIN as (Hd0 & Hd16 & Hdtop & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & S1m).
pose proof (exve_stk_lo (e_n E)) as HK.
unfold exv_sp, exv_STK in *.
split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hslo|]. split; [exact H64|].
split; [exact H47|]. split; [exact Hdtop|]. split; [exact Htop2|]. split; [exact HK|].
split; [exact Hd0|]. split; [exact Hd16|].
split; [exact S1a|]. split; [exact S1b | exact S1m].
Qed.

(* the journal the segment runs under: the entry state at the caller-window width (STK + d) (sp + d) *)
Lemma exve_HJ0 : forall E, EXV_PRE B ARx E ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) []
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) 0.
Proof.
intros E HPRE. pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & _).
destruct HFP as (HFN & _ & _).
exact (ajournal_x_init_W (SK := SK) rsegs B prh_pst ARx (exv_STK E) (e_d E) (exv_FP E)
  (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_regs E) (e_mem E) (e_md E) (e_ch E) HFN HWIN).
Qed.

(* ---- THE KEPT PACKAGE. Each stretch and each call of the segment keeps the entry's bytes in the same four
   shapes the frame call's own `acall_kept_x` has (YCbq.v:824) - the high bytes outside the writer's stack window,
   the bytes of a live block, the image bytes it does not own, the bytes and shadow bytes of a live fake frame -
   `Wr` is the writer's write set. The legs of the segment compose by exve_kept_trans. PRESENCE IS NOT CARRIED: the
   frame call keeps presence only at or above the allocation ceiling, and nothing here needs it - writability comes
   from ARx at the state it is read (alx_blocks / alx_frames) or from exve_writ_keep off the image. ---- *)
Definition exve_kept (E : exv_e) (W W' : world rsegs) (m m' : word -> option byte) (Wr : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ Wr a ->
     aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) /\
  (forall b n i, In (b, n) (ablocks B (e_ly E) (e_S E)) -> 0 <= i < req_size n ->
     aview rsegs (w_H W') m' (b + i) = aview rsegs (w_H W) m (b + i)) /\
  (forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) /\
  (forall cid p a, In (cid, p) (frames (e_S E)) ->
     (in_zr a (frame_rng (e_ly E) (cid, p)) \/
      in_zr a (shadow_addr (frame_addr (e_ly E) cid p), fs_frame_bytes cid / 8)) ->
     aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a).

Lemma exve_kept_trans : forall E W1 W2 W3 m1 m2 m3 Wr1 Wr2,
  exve_kept E W1 W2 m1 m2 Wr1 -> exve_kept E W2 W3 m2 m3 Wr2 ->
  exve_kept E W1 W3 m1 m3 (fun a => Wr1 a \/ Wr2 a).
Proof.
intros E W1 W2 W3 m1 m2 m3 Wr1 Wr2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [intros a Ha Hn; rewrite (B1 a Ha ltac:(tauto)); exact (A1 a Ha ltac:(tauto))|].
split; [intros b n i Hb Hi; rewrite (B2 b n i Hb Hi); exact (A2 b n i Hb Hi)|].
split; [intros a Hi Ho He; rewrite (B3 a Hi Ho He); exact (A3 a Hi Ho He)|].
intros cid p a Hf Hz. rewrite (B4 cid p a Hf Hz). exact (A4 cid p a Hf Hz).
Qed.

(* the entry's blocks and the bytes and shadow bytes of its live frames lie below the allocation ceiling, so a
   stretch whose writes are all at or above it keeps every one of them *)
Lemma exve_blk_low : forall E, EXV_PRE B ARx E ->
  forall b n i, In (b, n) (ablocks B (e_ly E) (e_S E)) -> 0 <= i < req_size n -> 0 <= b + i < alloc_ceiling.
Proof.
intros E HPRE b n i Hb Hi. pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _). destruct HFP as (HFN & _). destruct HFN as (HAR & _).
destruct (alx_blocks rsegs B ARx (eh_laws B ARx SK HYP) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
  b n HAR Hb) as (_ & H4096 & Hc & _).
lia.
Qed.

Lemma exve_frm_low : forall E, EXV_PRE B ARx E ->
  forall cid p a, In (cid, p) (frames (e_S E)) ->
  (in_zr a (frame_rng (e_ly E) (cid, p)) \/
   in_zr a (shadow_addr (frame_addr (e_ly E) cid p), fs_frame_bytes cid / 8)) -> 0 <= a < alloc_ceiling.
Proof.
intros E HPRE cid p a Hf Hz. pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _). destruct HFP as (HFN & _). destruct HFN as (HAR & _).
pose proof alloc_ceiling_val as (ACa & ACb).
destruct (frames_bounds_x rsegs B ARx (eh_laws B ARx SK HYP) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
  cid p HAR Hf) as (F1 & F2 & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
unfold in_zr, frame_rng, shadow_addr in Hz. cbn [fst snd] in Hz.
destruct Hz as [Hz | Hz]; [lia|].
assert (D1 : frame_addr (e_ly E) cid p / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (D2 : 0 <= frame_addr (e_ly E) cid p / 8) by (apply Z.div_pos; lia).
assert (D3 : fs_frame_bytes cid / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (D4 : 0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
assert (D5 : alloc_ceiling / 8 <= CEIL_MAX / 8) by (apply Z.div_le_mono; lia).
assert (D6 : CEIL_MAX / 8 = 17592184995840) by (vm_compute; reflexivity).
unfold SHADOW_OFF in *. lia.
Qed.

(* a stretch that writes only at or above the allocation ceiling (the prologue's save area, the body's own slots) *)
Lemma exve_kept_of_uniform : forall E (W : world rsegs) m m' (Wr : Z -> Prop),
  EXV_PRE B ARx E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  (forall a, Wr a -> alloc_ceiling <= a < 2 ^ 64) ->
  exve_kept E W W m m' Wr.
Proof.
intros E W m m' Wr HPRE HK HW.
pose proof (exve_blk_low E HPRE) as HBL. pose proof (exve_frm_low E HPRE) as HFL.
pose proof alloc_ceiling_val as (AC1 & AC2).
split; [intros a Ha Hn; exact (HK a ltac:(lia) Hn)|].
split; [intros b n i Hb Hi; destruct (HBL b n i Hb Hi); apply HK; [lia | intros Hw; destruct (HW _ Hw); lia]|].
split.
{ intros a Hi Ho He. pose proof (B_prog_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply HK; [lia | intros Hw; destruct (HW _ Hw); lia]. }
intros cid p a Hf Hz. destruct (HFL cid p a Hf Hz). apply HK; [lia | intros Hw; destruct (HW _ Hw); lia].
Qed.

(* ---- EXB AT THE C1 CUT: the invariant assembled from the journal, the kept package, ex_ws's post and the
   registers the body holds. Every shadow fact is re-derived at the C1 state (ajournal_x keeps no shadow byte of a
   heap block): the text and the scratch by ExvB_Open_sh.exv_sh_blk, a Lam tree root by exv_sh_lam, a root in the
   fake frame by eh_frame_hull, a root on the real stack by exve_stack_ra and eh_stk_hull. ---- *)
Lemma exve_EXB : forall (fx : YK11.FPState) (E : exv_e) (pos : Z) (S2 : astate)
    (ly2 : alayout) (S2' : astate) (Hp2 : list Z) (W2 : world rsegs) (regs' : bvmap 5 word) mem4 md4 (k : Z)
    (Wr : Z -> Prop),
  e_fx E = fx -> EXV_PRE B ARx E ->
  frames S2 = (1, pos) :: frames (e_S E) ->
  ablocks B (e_ly E) S2 = ablocks B (e_ly E) (e_S E) -> (exists g, S2 = set_fs g (e_S E)) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] ly2 S2' Hp2 W2 mem4 md4 k ->
  exve_kept E (e_W E) W2 (e_mem E) mem4 Wr ->
  (forall a, Wr a -> (exv_sp E - 288 <= a < exv_sp E) \/ (exv_s1 E - ESTACK <= a < exv_s1 E + 184) \/
     (e_q E <= a < e_q E + 8)) ->
  rdword (aview rsegs (w_H W2) mem4) (frame_addr (e_ly E) 1 pos + 120) = Some (flag_addr (e_ly E) 1 pos) ->
  getr regs' 2 = w64 (exv_s1 E) -> getr regs' 8 = w64 (exv_sp E) -> getr regs' 9 = w64 (exv_s1 E) ->
  getr regs' 18 = w64 (frame_addr (e_ly E) 1 pos) -> getr regs' 24 = w64 (frame_addr (e_ly E) 1 pos) ->
  getr regs' 25 = w64 SHADOW_OFF -> getr regs' 26 = w64 (shadow_addr (frame_addr (e_ly E) 1 pos)) ->
  getr regs' 19 = w64 (e_q E) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  (forall o r, In (o, r) exv_saved ->
     val_mem rsegs (mrestrict (w_H W2) mem4) (exv_sp E - 288 + o) 8
       (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))) ->
  val_mem rsegs (mrestrict (w_H W2) mem4) (exv_s1 E + 176) 8 (frame_addr (e_ly E) 1 pos) ->
  exv_room S2 S2' -> (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs mem4) -> Hp2 = e_Hp E ->
  ablocks B ly2 S2' = ablocks B (e_ly E) S2 ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly2 S2' Hp2 W2 mem4
    (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) ->
  EXB (fx := fx) B ARx SK E ly2 S2' Hp2 W2 regs' mem4 md4 k pos.
Proof.
intros fx E pos S2 ly2 S2' Hp2 W2 regs' mem4 md4 k Wr Hfx HPRE Hfrs2 Eab2 ES2 HJ HKP HWr HFLAG
  R2 R8 R9 R18 R24 R25 R26 R19 R3 R4 HSV H176 HRM HMN HHp2 Eab' HLED'.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof alloc_ceiling_val as (ACa & ACb).
pose proof (exve_geom E HPRE) as (Gal & Gceil & Gslo & G64 & Ghi & Gdtop & Gtop & Gstk & Gd0 & Gd16 & Gs1a & Gs1b & Gs1m).
pose proof HKP as (KHI & KBLK & KIMG & KFRM).
pose proof HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs' & Hnev & Hk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (exve_flag_layout (e_ly E) ly2 (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) 1 pos
  ltac:(pose proof HPRE as HP; unfold EXV_PRE in HP; cbv zeta in HP;
        destruct HP as (HFP & _); destruct HFP as (HFN & _); destruct HFN as (HAR0 & _); exact HAR0)
  Hly) as (EFR & EFL).
(* the entry's own facts, unpacked *)
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & Hfrm0 & Hcnt0 & _ & _ & Hcur0 & Hq8 & _ & Hqlo & Hqhi & HWIN0 & HSRC0 & HINB0 & Hlen3 &
  Hi00 & _ & _ & _ & HWD0 & HSB0 & Hsx & Hsq & HV0 & HLED0 & HMN0).
destruct HFP as (HFN0 & HROD0 & H64' & HRAC0).
pose proof HFN0 as (HAR0 & _).
(* the record's abbreviations, so the entry's own bounds and the geometry speak of the same terms *)
unfold exv_sp, exv_STK, exv_s1 in *.
(* the shadow facts at the C1 state, from the allocator laws and the ledger *)
assert (HINBx : 0 < exv_len E -> prhex_inblk B ly2 S2' Hp2 (e_x0 E) (exv_len E)).
{ intros Hl. unfold prhex_inblk in *. rewrite Eab', Eab2, HHp2. exact (HINB0 Hl). }
assert (HINBs : prhex_inblk B ly2 S2' Hp2 (e_scr E) (exv_len E + 1)).
{ unfold prhex_inblk in *. rewrite Eab', Eab2, HHp2. exact HSB0. }
assert (HSHs : range_addressable (aview rsegs (w_H W2) mem4) SHADOW_OFF (e_scr E) (exv_len E + 1) /\
               shadow_hull_vis (aview rsegs (w_H W2) mem4) (e_scr E) (exv_len E + 1)).
{ apply (exv_sh_blk B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E));
  [exact HAR' | exact HLED' | exact HINBs | pose proof (Zle_0_nat (length (e_x E))); unfold exv_len; lia]. }
(* the text's bytes are kept: they lie in a live block and no byte of the write set touches them *)
assert (HXK : forall x, e_x0 E <= x < e_x0 E + Z.of_nat (length (e_x E)) ->
  aview rsegs (w_H W2) mem4 x = aview rsegs (w_H (e_W E)) (e_mem E) x).
{ intros x Hx. destruct (Z_le_dec (exv_len E) 0) as [Hz | Hz]; [unfold exv_len in Hz, Hx; lia|].
  destruct (HINB0 ltac:(unfold exv_len; lia)) as (b & nn & Hb & Hb1 & Hb2 & _).
  replace x with (b + (x - b)) by lia. apply (KBLK b nn (x - b)); [exact Hb|].
  assert (nn <= req_size nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia).
  unfold exv_len in Hb2. lia. }
assert (HSRC' : src_rd W2 mem4 (e_x0 E) (e_x E)).
{ apply (exve_src_rd_kept (e_W E) W2 (e_mem E) mem4 (e_x0 E) (e_x E) HXK); [| | exact HSRC0].
  - destruct (Z_le_dec (Z.of_nat (length (e_x E))) 0) as [Hz | Hz];
    [apply range_addressable_nil; lia|].
    refine (proj1 (exv_sh_blk B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E)
      (e_ran E) (e_most E) (e_own E) (e_x0 E) (Z.of_nat (length (e_x E))) HAR' HLED' _ ltac:(lia))).
    unfold prhex_inblk in *. rewrite Eab', Eab2, HHp2. exact (HINB0 ltac:(unfold exv_len; lia)).
  - intros Hl.
    refine (proj2 (exv_sh_blk B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E)
      (e_ran E) (e_most E) (e_own E) (e_x0 E) (Z.of_nat (length (e_x E))) HAR' HLED' _ Hl)).
    unfold prhex_inblk in *. rewrite Eab', Eab2, HHp2. exact (HINB0 ltac:(unfold exv_len; lia)). }
(* the cursor's own 40 bytes are on the real stack, so their shadow is the runtime's zero shadow *)
assert (HQR : range_addressable (aview rsegs (w_H W2) mem4) SHADOW_OFF (e_q E) 40).
{ apply (exve_stack_ra ly2 S2' Hp2 W2 mem4 md4 (e_q E) 40 HAR'); rewrite ?Eslo, ?Eshi; lia. }
(* EXB, clause by clause *)
unfold EXB. cbv zeta. unfold exv_sp, exv_STK, exv_s1. rewrite EFR, EFL.
split; [exact HJ|].
split.
{ intros a Ha Hn. apply KHI; [lia|]. intros Hw.
  destruct (HWr a Hw) as [Hw1 | [Hw2 | Hw3]]; [lia | lia |].
  apply Hn. exists (e_q E, e_q E + 8). split; [unfold exv_FP; cbn [In]; tauto | cbn [fst snd]; lia]. }
split; [rewrite <- Hfx; intros r _; reflexivity|].
split; [rewrite <- Hfx; exact Hfrm0|].
split; [exact HHp2|].
split; [rewrite Eab', Eab2; reflexivity|].
split.
{ split; [|exact HMN]. destruct ES2 as (g & ->).
  exact (exv_room_trans (e_S E) (set_fs g (e_S E)) S2'
    (exv_room_set_fs (e_S E) (e_S E) g (exv_room_refl (e_S E))) HRM). }
split; [exact HLED'|].
split.
{ rewrite Hfrs'. cbn [app count_cid]. rewrite Z.eqb_refl.
  rewrite Nat2Z.inj_succ in Hcnt0. lia. }
split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R24|].
split; [exact R25|]. split; [exact R26|]. split; [exact R19|]. split; [exact R3|]. split; [exact R4|].
split; [exact HSV|]. split; [exact H176|]. split; [exact HFLAG|].
split; [exact HSRC'|]. split; [exact HINBx|].
split.
{ apply (exve_wdest_of_blk B ARx LAWS ly2 S2' Hp2 W2 regs' mem4 md4 (e_scr E) (exv_len E + 1) HAR' HINBs);
  [pose proof (Zle_0_nat (length (e_x E))); unfold exv_len; lia
  | destruct HWD0 as (_ & _ & Ham & _); exact Ham
  | exact (proj1 HSHs) | intros _; exact (proj2 HSHs)]. }
split; [exact HINBs|].
split; [exact HQR|].
(* the tree *)
destruct HV0 as [Hv0 | (HTREE0 & HDpos & HFAP)]; [left; exact Hv0 | right].
destruct HTREE0 as (HND0 & HHOME0 & HRA0 & HHULL0).
assert (HFC : forall x, PRH_Reader.pj_footR (e_v E) (e_D E) x ->
  (exists a kk, In (a, kk) (e_Lam E) /\ a <= x < a + kk) \/
  (exists cid p', In (cid, p') (frames (e_S E)) /\ in_zr x (frame_rng (e_ly E) (cid, p'))) \/
  (spZ (e_regs E) <= x /\ x < ly_stk_hi (e_ly E))).
{ intros x [Hx | (bk & Hbk & Hx)].
  - destruct HHOME0 as [(b & kk & Hin & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]].
    + left. exists b, kk. split; [exact Hin | lia].
    + right; left. exists cid, p'. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    + right; right. unfold exv_sp. lia.
  - left. pose proof (exv_node_D (e_t E) (mrestrict (w_H (e_W E)) (e_mem E)) (prh_lin (e_Lam E)) (e_v E)
      (e_D E) HND0 bk Hbk) as Hl. destruct bk as (b, kk). unfold prh_lin in Hl. cbn [fst snd] in Hl, Hx.
    exists b, kk. split; [exact Hl|]. unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx. lia. }
assert (HFK : forall x, PRH_Reader.pj_footR (e_v E) (e_D E) x ->
  aview rsegs (w_H W2) mem4 x = aview rsegs (w_H (e_W E)) (e_mem E) x /\
  (writable_at rsegs (mrestrict (w_H (e_W E)) (e_mem E)) x ->
   writable_at rsegs (mrestrict (w_H W2) mem4) x)).
{ intros x Hx.
  pose proof (exv_foot_rng B ARx SK HYP (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) (e_Lam E)
    (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) (e_regs E) (e_v E) (e_t E) (e_D E) HAR0 HLED0 HND0 HHOME0
    ltac:(lia) x Hx) as Hxr.
  destruct (HFAP x Hx) as (Hap1 & Hap2 & Hap3 & Hap4).
  assert (HE : aview rsegs (w_H W2) mem4 x = aview rsegs (w_H (e_W E)) (e_mem E) x /\ ~ in_img rsegs x).
  { destruct (HFC x Hx) as [(a & kk & Hin & Hr) | [(cid & p' & Hin & Hr) | Hr]].
    - destruct (exve_lam_blk B (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_Lam E) (e_peak E) (e_cnt E)
        (e_fail E) (e_ran E) (e_most E) (e_own E) a kk (eh_head B ARx SK HYP) HLED0 Hin) as (Hblk & Hk0 & Hrng).
      split.
      + replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
        apply (KBLK (a - cf_head) (kk + cf_head) (x - (a - cf_head)));
        [exact Hblk | pose proof (Hrng x ltac:(pose proof (@cf_head_nonneg cp); lia)); lia].
      + intros Hi. exact (blk_img_x rsegs B ARx LAWS (e_ly E) (e_S E) (e_Hp E) (e_W E)
          (e_mem E) (e_md E) (a - cf_head) (kk + cf_head) x HAR0 Hblk
          ltac:(pose proof (Hrng x ltac:(pose proof (@cf_head_nonneg cp); lia)); lia) Hi).
    - split.
      + apply (KFRM cid p' x Hin). left. exact Hr.
      + intros Hi. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
        exact (frm_img_x rsegs B ARx LAWS (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
          cid p' x HAR0 Hin ltac:(lia) Hi).
    - split.
      + apply KHI; [lia|]. intros Hw. destruct (HWr x Hw) as [H1 | [H2 | H3]]; lia.
      + intros Hi. pose proof (B_prog_segs_low x Hi) as Hlow. unfold kLowMemEnd in Hlow. lia. }
  destruct HE as (HE1 & HE2). split; [exact HE1|].
  intros Hwr. exact (exve_writ_keep (e_W E) W2 (e_mem E) mem4 x ltac:(lia) HE2 HE1 Hwr). }
(* the root's home and its shadow at the C1 state *)
assert (HHOME' : prhex_home ly2 S2' (e_Lam E) regs' (e_v E) 56).
{ destruct HHOME0 as [(b & kk & Hin & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]].
  - left. exists b, kk. split; [exact Hin | lia].
  - right; left. exists cid, p'. split; [rewrite Hfrs'; cbn [app]; right; exact Hin|].
    destruct (exve_flag_layout (e_ly E) ly2 (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) cid p' HAR0 Hly)
      as (EFR' & _). rewrite EFR'. split; [exact H1 | exact H2].
  - right; right. unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia.
    rewrite Eshi. unfold exv_sp in H1. split; [lia | lia]. }
assert (HSHt : range_addressable (aview rsegs (w_H W2) mem4) SHADOW_OFF (e_v E) 56 /\
               shadow_hull_vis (aview rsegs (w_H W2) mem4) (e_v E) 56).
{ destruct HHOME0 as [(b & kk & Hin & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]].
  - exact (exv_sh_lam B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      b kk (e_v E) 56 HAR' HLED' Hin H1 H2 ltac:(lia)).
  - split.
    + (* the root's shadow bytes lie inside the frame's own 16, which the kept package keeps (YCbq.v's
         range_addressable_entry_frame, over exve_kept's frame clause) *)
      destruct (alx_frames rsegs B ARx LAWS (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) cid p' HAR0 Hin)
        as (Hal32 & Hiapp & _ & _).
      pose proof (EXVE_FRAMES_CID (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) cid p' HAR0 Hin) as Hcid.
      assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
      { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
        replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z_mod_mult. }
      assert (Hf8 : frame_addr (e_ly E) cid p' mod 8 = 0)
        by (rewrite (Znumtheory.Zmod_div_mod 8 32) by (first [lia | exists 4; reflexivity]);
            rewrite Hal32; reflexivity).
      intros z Hz. destruct (HRA0 z Hz) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
      rewrite <- Hs. apply (KFRM cid p' (shadow_of_addr SHADOW_OFF z) Hin). right.
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      pose proof (fs_frame_bytes_nonneg cid) as Hnn.
      pose proof (Z.div_mod (frame_addr (e_ly E) cid p') 8 ltac:(lia)) as Df.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Db.
      assert (Hq1 : frame_addr (e_ly E) cid p' / 8 <= z / 8) by (apply Z.div_le_mono; lia).
      assert (Hq2 : z / 8 < frame_addr (e_ly E) cid p' / 8 + fs_frame_bytes cid / 8)
        by (apply Z.div_lt_upper_bound; lia).
      lia.
    + exact (eh_frame_hull B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 cid p' (e_v E) 56 HAR'
        ltac:(rewrite Hfrs'; cbn [app]; right; exact Hin)
        ltac:(destruct (exve_flag_layout (e_ly E) ly2 (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) cid p' HAR0 Hly)
              as (EFR' & _); rewrite EFR'; exact H1)
        ltac:(destruct (exve_flag_layout (e_ly E) ly2 (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) cid p' HAR0 Hly)
              as (EFR' & _); rewrite EFR'; exact H2) ltac:(lia)).
  - split.
    + apply (exve_stack_ra ly2 S2' Hp2 W2 mem4 md4 (e_v E) 56 HAR'); rewrite ?Eslo, ?Eshi;
      unfold exv_sp in H1; lia.
    + exact (eh_stk_hull B ARx SK HYP ly2 S2' Hp2 W2 mem4 md4 (e_v E) 56 HAR'
        ltac:(rewrite Eslo; unfold exv_sp in H1; lia) ltac:(rewrite Eshi; lia)). }
exact (exve_tree_kept ly2 S2' (e_Lam E) (e_W E) W2 regs' (e_mem E) mem4 (e_v E) (e_t E) (e_D E)
  HND0 HFK HHOME' (proj1 HSHt) (proj2 HSHt)).
Qed.

(* a callee-saved register at its bv name (S8aEntry.v's eve_kept) *)
Lemma exve_reg_kept : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' z r H Hc Hz. pose proof (H z Hc) as HH.
rewrite <- Hz, Z_to_bv_bv_unsigned in HH. exact HH.
Qed.

(* ---- THE SEGMENT LEMMA: ExvB_Top.v's seg_entry. The prologue (ExvB_Entry_r1), the class-1 frame call
   (YGcallSx.aj_stack_malloc_at_x at eh_sm1), the frame header and its shadow (ExvB_Entry_r2), then EXB at the
   pre-call state (exve_EXB) and the ex_ws call (YCbqGcallW.aj_call_xW over the PROVED exv_ws), whose post the
   shared call kit (ExvB_Loop_kitP.exv_kit_call) turns into EXB at the C1 cut. ---- *)
Theorem exvB_entry : forall n, (forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_C0 (fx := fx) B ARx SK n.
Proof.
intros n HC1 fx E Hn Hfx HPRE.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof alloc_ceiling_val as (ACa & ACb).
pose proof (exve_geom E HPRE) as (Gal & Gceil & Gslo & G64 & Ghi & Gdtop & Gtop & Gstk & Gd0 & Gd16 & Gs1a & Gs1b & Gs1m).
pose proof (exve_HJ0 E HPRE) as HJ0.
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & Hfrm0 & Hcnt0 & Ha0 & Ha1 & Hcur0 & Hq8 & Hca0 & Hqlo & Hqhi & HWIN0 & HSRC0 & HINB0 & Hlen3
  & Hi00 & Hdep & Hdepn & Hdl & HWD0 & HSB0 & Hsx & Hsq & HV0 & HLED0 & HMN0).
(* memnorm, carried as the keep from the entry memory (YSRrMemnorm.v): MNP m := memnorm (e_mem E) -> memnorm m *)
pose (MNP := fun m : word -> option byte => YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs m).
assert (MNL : YC80x.srr_inv_laws rsegs MNP)
  by exact (YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) (e_mem E)
              (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)).
destruct HFP as (HFN0 & HROD0 & H64' & HRAC0).
pose proof HFN0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hastk0 & Hpres0 & Hch0 & HQT0).
(* the alignments the two calls ask of the realigned base *)
assert (Hs116 : exv_s1 E mod 16 = 0).
{ rewrite (Znumtheory.Zmod_div_mod 16 32) by (first [lia | exists 2; reflexivity]).
  rewrite Gs1m. reflexivity. }
assert (Hspd16 : (exv_sp E + e_d E) mod 16 = 0) by (rewrite Z.add_mod, Gal, Gd16 by lia; reflexivity).
assert (Ho16 : (exv_s1 E - (exv_sp E + e_d E)) mod 16 = 0)
  by (rewrite Zminus_mod, Hs116, Hspd16; reflexivity).
assert (Hcnt1 : count_cid 1 (frames (e_S E)) < fs_frames 1)
  by (rewrite Nat2Z.inj_succ in Hcnt0; pose proof (Zle_0_nat (e_n E)); lia).
unfold CUT_C0.
(* ---- the prologue, B 0x8352c-0x8359c ---- *)
eapply (ExvB_Entry_r1.exve_run1 B prh_pst ARx LAWS (eh_palib B ARx SK HYP) (eh_got_uar B ARx SK HYP)
  (eh_uar_cell B ARx SK HYP) (eh_sm1_pc B ARx SK HYP)
  (e_W E) (e_regs E) (e_mem E) (e_md E) (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
  (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [] (e_ly E) (e_S E) (e_Hp E) 0
  (exv_sp E) (e_q E) (e_v E) (EXV_POST B ARx SK E) MNP HJ0 MNL (fun h => h)
  eq_refl ltac:(lia) ltac:(lia) Hgp Htp Ha0 Ha1).
intros regs1 memc1 mdc1 HJ1 HMN1 P1ra P1sp P1s1 P1gp P1tp P1s0 P1a0 P1s3 P1s9 P1s11 P1sv P1keep P1pres.
assert (HspT : spZ regs1 = exv_s1 E).
{ unfold spZ. rewrite P1sp. unfold ExvB_Entry_r1.exve_s1, w64. apply unsigned_lit_small.
  unfold exv_s1, exv_sp in *. lia. }
(* ---- the class-1 frame call ---- *)
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm rsegs B prh_pst ARx LAWS B_prog_segs_low (eh_errno B ARx SK HYP)
    (eh_ownlow B ARx SK HYP) (eh_smx B ARx SK HYP) 1 (eh_sm1 B ARx SK HYP fx) ltac:(lia)
    (e_W E) regs1 memc1 (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [] (e_ly E) (e_S E) (e_Hp E) mdc1 0
    (exv_s1 E - (exv_sp E + e_d E)) (w64 (B_prog_sigma AS_ex_value + 116)) HJ1).
  - rewrite HspT. lia.
  - exact Ho16.
  - lia.
  - assert (ESTACK = 4096) by reflexivity. lia.
  - rewrite P1gp. exact Hgp.
  - rewrite P1tp. exact Htp.
  - exact P1ra.
  - unfold w64. rewrite exve_ret1_slot.
    apply (YC1fP.ret_ok_codeptr_v (L := B_prog_listing) (PI := PI_prog_B) 7892); [lia | reflexivity].
  - exact Hcnt1. }
cbv beta. intros W1 c1 Hwle1
  (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0f & Eab2 & Hfrs2 & Hnin2 & Hnev2 & Hbb2 & Hz2 & Hflag2
   & Hfpres2 & HKept2 & HJin2 & ES2 & HMN2k).
assert (HMN2 : MNP mem2) by (intros h; exact (HMN2k (HMN1 h))).
(* the frame and its shadow, from the allocator laws at the state after the call *)
pose proof (proj1 HJ2) as HAR2. cbv beta in HAR2.
assert (HinF : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (alx_frames rsegs B ARx LAWS (e_ly E) S2 (e_Hp E) (e_W E) mem2 md2 1 pos HAR2 HinF)
  as (HF32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds_x rsegs B ARx LAWS (e_ly E) S2 (e_Hp E) (e_W E) mem2 md2 1 pos HAR2 HinF)
  as (HF4096 & HFceil & _).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFB in HFceil, HFpres, HFSpres, Hz2, Hflag2, Hfpres2.
(* the registers the frame call kept *)
assert (R2' : getr regs2 2 = w64 (exv_s1 E))
  by (rewrite (exve_reg_kept regs1 regs2 2 2%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1sp).
assert (R9' : getr regs2 9 = w64 (exv_s1 E))
  by (rewrite (exve_reg_kept regs1 regs2 9 9%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1s1).
assert (R8' : getr regs2 8 = w64 (exv_sp E))
  by (rewrite (exve_reg_kept regs1 regs2 8 8%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1s0).
assert (R3' : getr regs2 3 = w64 (as_gp B))
  by (rewrite (exve_reg_kept regs1 regs2 3 3%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)), P1gp; exact Hgp).
assert (R4' : getr regs2 4 = w64 (as_tp B))
  by (rewrite (exve_reg_kept regs1 regs2 4 4%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)), P1tp; exact Htp).
assert (R19' : getr regs2 19 = w64 (e_q E))
  by (rewrite (exve_reg_kept regs1 regs2 19 19%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1s3).
assert (R25' : getr regs2 25 = w64 SHADOW_OFF)
  by (rewrite (exve_reg_kept regs1 regs2 25 25%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1s9).
assert (R27' : getr regs2 27 = w64 (e_v E))
  by (rewrite (exve_reg_kept regs1 regs2 27 27%bv HP2 ltac:(unfold acallee_saved; lia)
        ltac:(vm_compute; reflexivity)); exact P1s11).
assert (HspT2 : spZ regs2 = exv_s1 E).
{ unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. unfold exv_s1, exv_sp in *. lia. }
(* ---- the frame header and the frame's own shadow, B 0x835a0-0x83644 ---- *)
eapply (ExvB_Entry_r2.exve_run2 B prh_pst ARx LAWS (e_W E) regs2 mem2 md2
  (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
  [(1, pos)] (e_ly E) S2 (e_Hp E) 0 (exv_sp E) (e_q E) (e_v E) pos (EXV_POST B ARx SK E) MNP HJ2 MNL HMN2
  ltac:(left; reflexivity) HspT2 ltac:(unfold exv_s1, exv_sp in *; lia) ltac:(lia) ltac:(lia)
  HF4096 HFceil HF32 Hfpres2
  ltac:(intros i Hi; exact (proj1 (HFSpres i ltac:(change (fs_frame_bytes 1 / 8) with 16; lia))))
  R2' R9' R8' R3' R4' Ha0f R19' R25' R27').
intros regs3 mem3 md3 HJ3 HMN3 P2ra P2sp P2s1 P2s0 P2gp P2tp P2a0 P2s2 P2s8 P2s3 P2s9 P2s10 P2s11 P2slot P2keep
  P2pres.
(* ---- the kept package of the three stretches, from the entry memory to the pre-call memory ---- *)
pose proof (exve_kept_of_uniform E (e_W E) (e_mem E) memc1 (fun a => exv_sp E - 288 <= a < exv_sp E)
  HPRE P1keep ltac:(intros a Ha; unfold exv_sp in *; lia)) as KEEP1.
pose proof HKept2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
assert (KEEP2 : exve_kept E (e_W E) (e_W E) memc1 mem2
  (fun a => exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) - ESTACK <= a
            < exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)))).
{ split; [intros a Ha Hna; exact (Q1 a Ha Hna)|].
  split; [intros b nn i Hb Hi; exact (Q2 b nn i Hb Hi ltac:(intros []))|].
  split; [intros a Hia Hoa Hea; exact (Q3 a Hia Hoa Hea)|].
  intros cid p a Hfa Hza. exact (Q4 cid p a Hfa Hza ltac:(intros [])). }
(* the two legs composed *)
pose proof (exve_kept_trans E (e_W E) (e_W E) (e_W E) (e_mem E) memc1 mem2 _ _ KEEP1 KEEP2) as KEEP12.
(* the ledger after the frame call: its statics are image bytes the call keeps (eh_pst_own, exve_pst_errno) and its
   harness heads lie in live blocks (eh_head) *)
pose proof KEEP12 as (K12H & K12B & K12I & K12F).
assert (HLED2 : prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B (e_ly E) S2 (e_Hp E)
  (e_W E) mem2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)).
{ apply (exve_ledger_keep B ARx (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    (e_ly E) S2 (e_Hp E) (e_W E) mem2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    (eh_head B ARx SK HYP) HAR0 HLED0 ltac:(rewrite Eab2; apply incl_refl) eq_refl); [|exact K12B].
  intros a Hst. apply K12I; [exact (exve_pst_img a Hst) | exact (eh_pst_own B ARx SK HYP a Hst)
    | exact (exve_pst_errno a Hst)]. }
(* ---- the frame-header leg (ExvB_Entry_fr) and the whole kept package ---- *)
pose proof (ExvB_Entry_fr.exve_kept_of_frame B ARx SK HYP E S2 (e_Hp E) (e_W E) mem2 md2 mem3 pos
  (exv_s1 E + 176) (exv_s1 E + 184) HPRE HAR2 Eab2
  ltac:(intros z Hz; rewrite Hfrs2; right; exact Hz) HinF Hnin2
  ltac:(unfold exv_s1, exv_sp in *; lia) ltac:(unfold exv_s1, exv_sp in *; lia) P2keep) as (F1 & F2 & F3 & F4).
assert (KEEP3 : exve_kept E (e_W E) (e_W E) mem2 mem3 (fun a => exv_s1 E + 176 <= a < exv_s1 E + 184))
  by (split; [exact F1|]; split; [exact F2|]; split; [exact F3 | exact F4]).
pose proof (exve_kept_trans E (e_W E) (e_W E) (e_W E) memc1 mem2 mem3 _ _ KEEP2 KEEP3) as KEEP23.
pose proof (exve_kept_trans E (e_W E) (e_W E) (e_W E) (e_mem E) mem2 mem3 _ _ KEEP12 KEEP3) as KEEP.
pose proof KEEP as (KH & KB & KI & KF).
pose proof KEEP23 as (K23H & K23B & K23I & K23F).
(* the frame and its own shadow are apart (the frame is in the application range, its shadow in the shadow band) *)
assert (HFSH : shadow_addr (frame_addr (e_ly E) 1 pos) + 12 <= frame_addr (e_ly E) 1 pos \/
               frame_addr (e_ly E) 1 pos + 128 <= shadow_addr (frame_addr (e_ly E) 1 pos)).
{ pose proof (Z.div_mod (frame_addr (e_ly E) 1 pos) 8 ltac:(lia)) as Dm.
  pose proof (Z.mod_pos_bound (frame_addr (e_ly E) 1 pos) 8 ltac:(lia)) as Dr.
  unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct HFapp as (HA1 & [HA2 | (HA2 & HA3)]); [right | left]; lia. }
(* the ledger and the flag pointer at the pre-call state *)
assert (HLED3 : prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B (e_ly E) S2 (e_Hp E)
  (e_W E) mem3 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)).
{ apply (exve_ledger_keep B ARx (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    (e_ly E) S2 (e_Hp E) (e_W E) mem3 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    (eh_head B ARx SK HYP) HAR0 HLED0 ltac:(rewrite Eab2; apply incl_refl) eq_refl); [|exact KB].
  intros a Hst. apply KI; [exact (exve_pst_img a Hst) | exact (eh_pst_own B ARx SK HYP a Hst)
    | exact (exve_pst_errno a Hst)]. }
replace (frame_addr (e_ly E) 1 pos + 128 - 8) with (frame_addr (e_ly E) 1 pos + 120) in Hflag2 by lia.
assert (HFL3 : rdword (aview rsegs (w_H (e_W E)) mem3) (frame_addr (e_ly E) 1 pos + 120)
  = Some (flag_addr (e_ly E) 1 pos)).
{ rewrite <- Hflag2. apply rdword_ext. intros kk Hkk.
  apply P2keep; unfold exv_s1, exv_sp in *; lia. }
(* the thirteen saved slots at the pre-call state *)
assert (HSV3 : forall o r, In (o, r) exv_saved ->
  val_mem rsegs (mrestrict (w_H (e_W E)) mem3) (exv_sp E - 288 + o) 8
    (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))).
{ intros o r Hor. pose proof (exv_saved_rng o r Hor) as Hrng.
  apply (exve_val_kept (e_W E) (e_W E) memc1 mem3 (exv_sp E - 288 + o) 8%nat
    (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))); [|exact (P1sv o r Hor)].
  intros x Hx. apply K23H; unfold exv_s1, exv_sp in *; cbn [Z.of_nat] in Hx; lia. }
assert (P2gp' : getr regs3 3 = w64 (as_gp B)) by (rewrite P2gp; exact R3').
assert (P2tp' : getr regs3 4 = w64 (as_tp B)) by (rewrite P2tp; exact R4').
assert (HES : ESTACK = 4096) by reflexivity.
assert (HWrB : forall a, ((exv_sp E - 288 <= a < exv_sp E) \/
    (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) - ESTACK <= a
     < exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)))) \/ (exv_s1 E + 176 <= a < exv_s1 E + 184) ->
  (exv_sp E - 288 <= a < exv_sp E) \/ (exv_s1 E - ESTACK <= a < exv_s1 E + 184) \/ (e_q E <= a < e_q E + 8)).
{ intros a [[Hw | Hw] | Hw]; [left; lia | right; left; lia | right; left; lia]. }
assert (HEXB : EXB (fx := fx) B ARx SK E (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 0 pos).
{ apply (exve_EXB fx E pos S2 (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 0 _ Hfx HPRE Hfrs2 Eab2 ES2
    HJ3 KEEP HWrB
    HFL3 P2sp P2s0 P2s1 P2s2 P2s8 P2s9 P2s10 P2s3 P2gp' P2tp' HSV3 P2slot (exv_room_refl S2) HMN3
    eq_refl eq_refl HLED3). }
pose proof HEXB as HB. unfold EXB in HB. cbv zeta in HB.
destruct HB as (HBJ & HBW & HBF & HBZ & HBHp & HBab & HBrm & HBled & HBcnt & HB2 & HB8 & HB9 & HB18 & HB24
  & HB25 & HB26 & HB19 & HB3 & HB4 & HBsv & HB176 & HBfl & HBsrc & HBinb & HBwd & HBsb & HBqr & HBtree).
(* ---- the frame chain and the read-only view at the call, from the shared kit ---- *)
destruct (exv_kit_chain B ARx SK fx E (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 0 pos regs3
  HPRE HEXB P2sp P2s0) as (ch1 & Hch1 & Hca1).
pose proof (exv_kit_rodata B ARx SK HYP fx E (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 0 pos HPRE HEXB)
  as (HROD3 & HROM3).
assert (HspT3 : spZ regs3 = exv_s1 E).
{ unfold spZ. rewrite P2sp. unfold w64. apply unsigned_lit_small. unfold exv_s1, exv_sp in *. lia. }
assert (Hs0T3 : s0Z regs3 = exv_sp E).
{ unfold s0Z. rewrite P2s0. unfold w64. apply unsigned_lit_small. unfold exv_sp in *. lia. }
assert (HWS16 : @STK_ex_ws prh_img_B = 16) by reflexivity.
assert (He116 : (exv_sp E + e_d E - exv_s1 E) mod 16 = 0) by (rewrite Zminus_mod, Hspd16, Hs116; reflexivity).
(* ---- the call of ex_ws (the PROVED walk, cited as exv_ws) ---- *)
eapply SRr_bind.
{ eapply (aj_call_xW rsegs B prh_pst ARx LAWS B_prog_segs_low (e_W E) regs3 mem3 (B_prog_sigma AS_ex_ws)
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] (e_ly E) S2 (e_Hp E) md3 0
    (@STK_ex_ws prh_img_B) (exv_sp E + e_d E - exv_s1 E) [(e_q E, e_q E + 8)]
    (exv_s1 E - (exv_sp E + e_d E)) (w64 (B_prog_sigma AS_ex_value + 284)) ch1 _ HJ3).
  - rewrite HspT3. lia.
  - exact Ho16.
  - unfold exv_s1, exv_sp in *. lia.
  - rewrite HWS16. lia.
  - rewrite HWS16. unfold exv_s1, exv_sp in *. lia.
  - unfold exv_s1, exv_sp in *. lia.
  - exact He116.
  - lia.
  - exact P2gp'.
  - exact P2tp'.
  - exact P2ra.
  - unfold w64. rewrite exve_c1_slot.
    apply (YC1fP.ret_ok_codeptr_v (L := B_prog_listing) (PI := PI_prog_B) 8060); [lia | reflexivity].
  - assert (Hc1v : B_prog_sigma AS_ex_value + 284 = 538184) by (vm_compute; reflexivity).
    unfold w64. rewrite Hc1v, unsigned_lit_small by lia. lia.
  - rewrite Hs0T3. replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by lia.
    exact Hch1.
  - intros HFNc HWINc.
    eapply (exv_ws B ARx SK HYP fx (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 ch1 (e_q E) (e_x0 E) (e_i0 E)
      (exv_sp E + e_d E - exv_s1 E) (e_x E) (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)).
    + split; [exact HFNc | split; [exact HROD3 | split]].
      * rewrite HspT3. unfold exv_s1, exv_sp in *. lia.
      * (* fpre's return-address bound: ra = the C1 cut, a listing literal; and (kit f97c8b2f046b, FRM0-ENTRY)
           the rounding mode 0 at the call: ex_value's entry one, no float instruction ran (EXV_PRE) *)
        split.
        -- unfold raZ. rewrite P2ra.
           assert (Hc1v' : B_prog_sigma AS_ex_value + 284 = 538184) by (vm_compute; reflexivity).
           pose proof (@alloc_ceiling_value rc) as [[HCm _] _].
           unfold w64. rewrite Hc1v', unsigned_lit_small by lia. lia.
        -- pose proof HPRE as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0. rewrite <- Hfx. exact (proj1 (proj2 HP0)).
    + exact P2a0.
    + apply (exve_val_kept (e_W E) (e_W E) (e_mem E) mem3 (e_q E) 8%nat (e_x0 E + e_i0 E));
      [|exact (proj1 Hcur0)].
      intros x Hx. cbn [Z.of_nat] in Hx. apply KH;
        [unfold exv_sp in *; lia | unfold exv_s1, exv_sp in *; intros [[Hw | Hw] | Hw]; lia].
    + apply (exve_val_kept (e_W E) (e_W E) (e_mem E) mem3 (e_q E + 8) 8%nat
        (e_x0 E + Z.of_nat (length (e_x E)))); [|exact (proj1 (proj2 Hcur0))].
      intros x Hx. cbn [Z.of_nat] in Hx. apply KH;
        [unfold exv_sp in *; lia | unfold exv_s1, exv_sp in *; intros [[Hw | Hw] | Hw]; lia].
    + exact Hq8.
    + rewrite HspT3. unfold exv_s1, exv_sp in *. lia.
    + rewrite HspT3. unfold exv_s1, exv_sp in *. lia.
    + exact HWINc.
    + exact HBsrc.
    + exact HBinb.
    + exact Hlen3.
    + exact Hi00.
    + exact HLED3.
  - intros a (r & Hr & Ha). cbn [In] in Hr. destruct Hr as [<- | []]. left.
    exists (e_q E, e_q E + 8). split; [unfold exv_FP; cbn [In]; tauto | exact Ha]. }
(* ---- the C1 cut: the shared call kit turns ex_ws's post into EXB at 0x83648 ---- *)
cbv beta. intros W2 c2 Hwle2 (ly2 & S2' & Hp2 & regs4 & mem4 & md4 & k1 & -> & HJo & HJi & HWk & HPr & HQ).
destruct HQ as ((HQroom & HQp & HQhp & HQS & HQab & HQled) & HQmn).
assert (HMN4 : MNP mem4) by (intros h; exact (HQmn (HMN3 h))).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) in HJi, HWk by lia.
replace (exv_s1 E + (exv_sp E + e_d E - exv_s1 E)) with (exv_sp E + e_d E) in HJi, HWk by lia.
assert (HBR : forall r, In r exv_bregs -> getr regs4 r = getr regs3 r).
{ intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]];
  [ exact (HPr 2 ltac:(unfold acallee_saved; lia)) | exact (HPr 3 ltac:(unfold acallee_saved; lia))
  | exact (HPr 4 ltac:(unfold acallee_saved; lia)) | exact (HPr 8 ltac:(unfold acallee_saved; lia))
  | exact (HPr 9 ltac:(unfold acallee_saved; lia)) | exact (HPr 18 ltac:(unfold acallee_saved; lia))
  | exact (HPr 19 ltac:(unfold acallee_saved; lia)) | exact (HPr 24 ltac:(unfold acallee_saved; lia))
  | exact (HPr 25 ltac:(unfold acallee_saved; lia)) | exact (HPr 26 ltac:(unfold acallee_saved; lia)) ]. }
destruct (exv_kit_call B ARx SK HYP fx E (e_ly E) S2 (e_Hp E) (e_W E) regs3 mem3 md3 0 pos fx
  [(e_q E, e_q E + 8)] (@STK_ex_ws prh_img_B + (exv_sp E + e_d E - exv_s1 E))
  ly2 S2' Hp2 W2 regs4 mem4 md4 k1 HPRE HEXB
  ltac:(intros a (r & Hr & Ha); cbn [In] in Hr; destruct Hr as [<- | []];
        exists (e_q E, e_q E + 8); split; [unfold exv_FP; cbn [In]; tauto | exact Ha])
  HJo HJi HWk HBR ltac:(intros r _; reflexivity) ltac:(rewrite <- Hfx; exact Hfrm0)
  (exv_room_eq S2 S2 S2' (exv_room_refl S2) HQS) HMN4 HQhp HQab HQled) as (HEXB1 & HKC).
(* the cursor at the cut: ex_ws moved its first cell, the other four the call kept *)
assert (HKQ : forall a nn v, e_q E + 8 <= a -> a + Z.of_nat nn <= e_q E + 40 ->
  val_mem rsegs (mrestrict (w_H (e_W E)) (e_mem E)) a nn v ->
  val_mem rsegs (mrestrict (w_H W2) mem4) a nn v).
{ intros a nn v Hq1 Hq2 Hv. apply (exve_val_kept (e_W E) W2 (e_mem E) mem4 a nn v); [|exact Hv].
  intros x Hx.
  rewrite (HWk x ltac:(unfold exv_s1, exv_sp in *; lia)
    ltac:(intros (r & Hr & Hrr); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hrr; lia)).
  apply KH; [unfold exv_sp in *; lia | unfold exv_s1, exv_sp in *; intros [[Hw | Hw] | Hw]; lia]. }
destruct Hcur0 as (C1a & C2a & C3a & C4a & C5a).
apply (HC1 fx E ly2 S2' Hp2 W2 regs4 mem4 md4 (0 + k1) pos Hn HPRE HEXB1).
- assert (Hpv : e_x0 E + exv_i1 E
    = e_x0 E + exv_len E - Z.of_nat (length (PjGrammar.skip (exv_X E)))) by (unfold exv_i1; lia).
  rewrite Hpv. split; [exact HQp|].
  split; [exact (HKQ (e_q E + 8) 8%nat (e_x0 E + exv_len E) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) C2a)|].
  split; [exact (HKQ (e_q E + 16) 4%nat (e_dep E) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) C3a)|].
  split; [exact (HKQ (e_q E + 24) 8%nat (e_scr E) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) C4a)
         | exact (HKQ (e_q E + 32) 4%nat (e_dl E) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) C5a)].
- rewrite (exve_reg_kept regs3 regs4 27 27%bv HPr ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)). rewrite P2s11. reflexivity.
Qed.

End e.

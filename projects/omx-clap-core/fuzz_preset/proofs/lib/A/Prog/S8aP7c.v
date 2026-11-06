(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumE.v, with its module paths and module names changed; 2503 of its 2694 lines of code are new or changed and 1724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aP7a.v; 543 of its 663 lines of code are new or changed and 2574 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): piece 7 SEG 1 of the walk of
   ex_value (A' 0x832a4), sub-lane S8aP7c of EvItems: ev7_seg1_A, S8aItems.v's ev7_seg1_stmt at L := A_prog_listing,
   PA := PI_prog_A. From P_STEP (0x837ec, EV_STEP) to C_KID (0x83878, EV_KID), listing lines 340-374 and the
   partial-granule arm 0x83b34-0x83b40 (C fuzz_preset.c :241-244): `kid = v && n < v->n ? &v->kids[n] : NULL;
   if (v && !kid) in->differs = 1;`. Three paths, no exit arm:
     v' = 0          : 0x837ec sd, 0x837f0 beqz taken, 0x83870-0x83874 (kid 0, s7 1, no store);
     v' <> 0, n >= v->n : 0x837ec-0x83814 (bgeu taken), 0x8384c-0x8386c with the arm 0x83b34-0x83b40 not taken
                       (kid 0, s7 1, in->differs = 1);
     v' <> 0, n < v->n  : 0x837ec-0x83814, 0x83818-0x83848 (kid = v->kids + 56 n, s7 0).
   The symbolic states (p7c_ssZ for v' = 0, p7c_ssV for v' <> 0) are written for this segment; they are VARIANTS of
   S8aItemsWalk.v's ev7_ss / ev7_entry at e3200869f2e (not copies, and S8aItemsWalk.v is not Required): ev7_entry
   takes `a1 = length x` where P_STEP has a1 = n (ev_at_step), and its node premise `v' + 48 <= alloc_ceiling` fails
   on prhex_home's caller-stack arm; here the node's separation from the body's frame and `struct ex` comes from
   ev_pre's footprint clause (all three home arms), and the shadow checks are engine TOKENS (YCbn: each leaves an
   obligation range_addressable, discharged after its run). in->differs is a chunk of the state (atom 37), so the
   path that does not store it keeps its value.
   Section hypotheses: S8aItemsWalk.v's header (LAWS, WS, PSTI, verbatim; HSH derived from LAWS) and MIDF / BNDS (lane FRAME's
   ev_mid_frame / ev_bounds, the internal file FRAME.md's statements verbatim; S8aP7 discharges them at composition).
   Atoms: 0..31 the registers; 32 = v' + 24, 33 = v' + 40, 34 = q + 32, 35 = v->n, 36 = v->kids, 37 = in->differs
   (DERIVED: Ereg's extras start at 32); the engine's token atoms are 512 + j (DERIVED: A_LIM).
   Numerals: 7364 (LENGTH: ex_value's listing offset, bff8519b); 24, 40, 56 (LENGTH: struct pj's kids / n fields
   and its size), 32, 36, 40 (LENGTH: in->differs, its end, sizeof(struct ex)), 72, 80, 88, 104, 120, 128, 152
   (LENGTH: s1 offsets of the spills and of the body's locals), 8, 4, 1 (LENGTH: access sizes, the granule), 256, 64
   (LENGTH: a byte's range, a word's bits), 44, 47, 32, 64 as exponents and 2 ^ 47 - 8 / - 16 / - 32 (DERIVED: the
   shadow span, user-space top less a field offset, the word ranges), 4096 (DERIVED: the page floor of application
   memory), 5 and 6 (WORD: PjTree tags of an array and an object), 9..37 and the register numbers (WORD: RISC-V ABI /
   atom indices), 0..8 (WORD: list positions, byte indices). No ADDRESS literal: addresses are pa_sigma / pa_val of
   PAImg_prog.v, SHADOW_OFF, kHighMemBeg, alloc_ceiling. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG.
(* the caller-window call kit is Reusable/YCbqGcallW.v (walkkit b77223726823's engine set) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf YGcallMx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aItems.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aWs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the walk is at image A's PrhImg (frames, statics), as at its listing *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PI)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
(* the kit's allocator laws at ARx, at the harness head length cf_head (YCbqG.v journal 83da015952be; at ARx := ARcf
   this is YGcallcf.v's AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the shared whitespace loop, PROVED (no longer a stand-in): WalkS8a's S8aWs.ev_ws_loop (ws-rawframe 91e4dffbfb7),
   whose only Section hypothesis is LAWS *)
Lemma WS : ev_ws_loop_spec_FIX (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (S8aWs.ev_ws_loop B ARx SK LAWS). Qed.
(* HSH is DERIVED (c-omx-hpreset 10:43Z): ev_hshadow_law is AR_laws_x's field alx_hshadow at hl := cf_head (journal
   83da015952be, YCbqG.v:163); S8aItems.v ev_hshadow_of_laws *)
Lemma HSH : ev_hshadow_law (L := A_prog_listing) (PA := PA) B ARx.
Proof. exact (ev_hshadow_of_laws B ARx LAWS). Qed.
(* STAND-IN: a Theorem Labs lane, the image binding of PrhImg: alloc.c's statics (prh_pst) are image bytes (true at prh_img_A: PRH_Img.v,
   below kLowMemEnd by pa_segs_low, so apart from the stack); without it a generic PrhImg could put them in `struct ex` *)
Hypothesis PSTI : forall z, Exists (in_zr z) PST -> in_img SEGS z.

(* ======== LOCAL KIT (EvItems) ======== *)

(* The CALL of a caller-window callee: PRW_CallerJ.v (by path from walk-S4 036034006eb0) aj_call_xW / aj_call_xWF over
   fp_sub_xW, instantiated at the piece's float state. *)
Let ev_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd := @pa_segs_low _ A_prog_listing PA.




(* ======== END LOCAL KIT ======== *)

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN0d.

(* STAND-IN (lane FRAME: S8aItemsWalk.v FRAME KIT ev_mid_frame, Qed at e3200869f2e; the internal file FRAME.md's statement verbatim;
   S8aP7 discharges it at composition). Its last premise, memnorm at the new memory, is ev_mid's last conjunct
   (S8aIface.v, the memnorm interface), as in S8aItemsWalk.ev_mid_frame. *)
Hypothesis MIDF : forall (a : ev_act) ly S Hp W mem md k p dep dl mem' md' p' dep' dl' (Wr : Z -> Prop),
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall z, Wr z -> ea_S1 a <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36) ->
  prhex_cur W mem' (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_mid B ARx SK a ly S Hp W mem' md' k p' dep' dl'.
(* STAND-IN (lane FRAME: S8aItemsWalk.v FRAME KIT ev_bounds, Qed at e3200869f2e; the internal file FRAME.md's statement verbatim) *)
Hypothesis BNDS : forall (a : ev_act), ev_pre (fx := fx) B ARx a ->
  alloc_ceiling <= ea_sp0 a - ea_STK a /\ ea_sp0 a - ea_STK a <= ea_S1 a /\ ea_S1 a + 152 <= ea_sp0 a /\
  ea_S1 a mod 32 = 0 /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\ ea_sp0 a + ea_d a <= 2 ^ 47 /\
  ea_q a mod 8 = 0 /\ 0 <= ea_d a.

(* ======== the symbolic states at P_STEP ======== *)
Lemma p7c_sigma : SIGMA AS_ex_value = BASE + 7364.
Proof. vm_compute. reflexivity. Qed.

Definition p7c_Bx : sv := SOff 24 0.
Definition p7c_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition p7c_fa0 : list (nat * afact) :=
  [(9%nat, mkAF kHighMemBeg (2 ^ 47) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
(* v' = 0: the body's frame at s1, its write window s1 + 120 (the item index) *)
Definition p7c_ssZ : sstate :=
  mkSS (7364 + EV_STEP) sr_atoms [YP09.mkRegion (Some 9%nat) 120 128 120 128 []] None (mkFacts p7c_fa0 [] []).
(* v' <> 0: the body's frame (the spills of v' + 24, v' + 40, q + 32; the window s1 + 120), in->differs at q + 32
   (writable, holding dln), v->n at v' + 40 and v->kids at v' + 24 (read-only) *)
Definition p7c_memV : smem :=
  [ YP09.mkRegion (Some 9%nat) 72 128 120 128
      [YP09.mkChunk 72 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
    YP09.mkRegion (Some 34%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))];
    YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))];
    YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))] ].
Definition p7c_faV : list (nat * afact) :=
  [(9%nat, mkAF kHighMemBeg (2 ^ 47) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF kHighMemBeg (2 ^ 47 - 8) 0); (33%nat, mkAF 0 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 (2 ^ 47 - 32) 0)].
Definition p7c_ssV : sstate := mkSS (7364 + EV_STEP) sr_atoms p7c_memV None (mkFacts p7c_faV [] []).
Definition p7c_E (regs : bvmap 5 word) (ex : list word) : env := @Eimg _ A_prog_listing PA (Ereg regs ex).
(* the bytes the segment writes: s1 + 120 (n) and in->differs *)
Definition p7c_Wr (a : ev_act) (z : Z) : Prop := ea_S1 a + 120 <= z < ea_S1 a + 128 \/ ea_q a + 32 <= z < ea_q a + 36.
Definition p7c_WrS (a : ev_act) (z : Z) : Prop := ea_S1 a + 120 <= z < ea_S1 a + 128.
(* the registers no path writes (the segment writes a0, a1, a2, a3, s7) *)
Definition p7c_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(* ======== small facts ======== *)
Lemma p7c_ewr : forall regs ex (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (p7c_E regs ex) n = getr regs r.
Proof. intros regs ex n r Hn Hr. unfold p7c_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs ex n r Hr). Qed.
Lemma p7c_ewx : forall regs ex j, (32 + j < A_TEXT)%nat -> ew (p7c_E regs ex) (32 + j) = nth j ex (Z_to_bv 64 0).
Proof. intros regs ex j Hj. unfold p7c_E. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.
Lemma p7c_agree : forall regs ex, env_agree 32 (Ereg regs ex) (p7c_E regs ex).
Proof. intros regs ex. unfold p7c_E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma p7c_denot0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma p7c_cfg_eq : forall (fxc : YK11.FPState) regs off mem md,
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (7364 + off))) mem (YK11.seg_rom SEGS)) md =
  ev_cfg (L := A_prog_listing) (PA := PA) fxc regs off mem md.
Proof.
intros fxc regs off mem md. unfold ev_cfg, ev_pc. rewrite p7c_sigma.
replace (BASE + 7364 + off) with (BASE + (7364 + off)) by lia. reflexivity.
Qed.

(* the byte of a little-endian value; a chunk as val_mem (copies of lane NEXT's ev8_byte_eq / ev8_val_of_chunk,
   S8aItemsWalk.v at cb3bf00de8c, Qed text) *)
Lemma p7c_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros j Hj. change 256 with (2 ^ 8).
destruct (Z.lt_ge_cases j 8) as [E|E].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma p7c_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) ->
  val_mem SEGS m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (p7c_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.
(* a chunk of a run's final state *)
Lemma p7c_chunk_val : forall (fxc : YK11.FPState) E ss ms (H : word -> bool) i r off (w : N) e,
  st_ok_pi (fx := fxc) SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some r -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> (w <= 8)%N ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros fxc E ss ms H i r off w e HS Hn Hin Hw. unfold st_ok_pi in HS.
pose proof (st_ok_chunk SEGS E _ _ i r _ HS Hn Hin) as HC. cbn [ms_mem restrict] in HC.
exact (p7c_val_of_chunk E _ _ off w e Hw HC).
Qed.

(* two little-endian words at the same 8 bytes are equal *)
Lemma p7c_vm_det : forall (m : word -> option byte) a x y,
  val_mem SEGS m a 8 x -> val_mem SEGS m a 8 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
intros m a x y Hx Hy Rx Ry.
assert (Hb : forall k, (k < 8)%nat -> Z.shiftr x (8 * Z.of_nat k) mod 256 = Z.shiftr y (8 * Z.of_nat k) mod 256).
{ intros k Hk. pose proof (Hx k Hk) as A. rewrite (Hy k Hk) in A. injection A as A.
  assert (A2 : bv_unsigned (Z_to_bv 8 (YG0f.le_byte x 8 k)) = bv_unsigned (Z_to_bv 8 (YG0f.le_byte y 8 k)))
    by first [exact (eq_sym A) | exact (f_equal (@bv_unsigned 8) (eq_sym A))].
  rewrite !Z_to_bv_unsigned in A2. unfold bv_wrap, YG0f.le_byte in A2. change (bv_modulus 8) with 256 in A2.
  change (8 * Z.of_nat 8) with 64 in A2. rewrite !Z.mod_mod in A2 by lia.
  rewrite (Z.mod_small x (2 ^ 64)), (Z.mod_small y (2 ^ 64)) in A2 by lia. exact A2. }
apply Z.bits_inj'. intros j Hj.
destruct (Z.lt_ge_cases j 64) as [Hj64|Hj64].
- pose proof (Z.div_mod j 8 ltac:(lia)) as Dj. pose proof (Z.mod_pos_bound j 8 ltac:(lia)) as Mj.
  assert (Q : 0 <= j / 8 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  specialize (Hb (Z.to_nat (j / 8)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  assert (T : forall v, Z.testbit v j = Z.testbit (Z.shiftr v (8 * (j / 8)) mod 256) (j mod 8)).
  { intros v. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
    f_equal. lia. }
  rewrite (T x), (T y), Hb. reflexivity.
- rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite <- (Z.mod_small y (2 ^ 64)) by lia.
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- frames: bytes kept off a write set ---- *)
Lemma p7c_mb_kept : forall (W : world SEGS) mem mem' (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ P z -> mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z.
Proof. intros W mem mem' P H z Hz Hn. unfold mbyte. rewrite H; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma p7c_vm_kept : forall (W : world SEGS) mem mem' (P : Z -> Prop) b (nb : nat) v,
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  0 <= b -> b + Z.of_nat nb <= 2 ^ 64 -> (forall z, b <= z < b + Z.of_nat nb -> ~ P z) ->
  val_mem SEGS (mrestrict (w_H W) mem) b nb v -> val_mem SEGS (mrestrict (w_H W) mem') b nb v.
Proof.
intros W mem mem' P b nb v K H0 H1 H2 Hv kk Hk. rewrite (p7c_mb_kept W mem mem' P K); [exact (Hv kk Hk) | lia |].
apply H2. lia.
Qed.
Lemma p7c_frame_step : forall E rs (H : word -> bool) (m0 mA mB : word -> option byte) (P : Z -> Prop),
  (forall z, in_wrange E rs z -> P z) ->
  frame_of E rs (mrestrict H mA) (mrestrict H mB) ->
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict H mA x = mrestrict H m0 x) ->
  forall x : word, ~ P (bv_unsigned x) -> mrestrict H mB x = mrestrict H m0 x.
Proof. intros E rs H m0 mA mB P Hw HF HK x Hx. rewrite (HF x); [exact (HK x Hx)|]. intros Hi. exact (Hx (Hw _ Hi)). Qed.
Lemma p7c_ra_kept : forall (W : world SEGS) mem mem' (P : Z -> Prop) x n,
  (forall y : word, ~ P (bv_unsigned y) -> mrestrict (w_H W) mem' y = mrestrict (w_H W) mem y) ->
  (forall s, SHADOW_OFF <= s < alloc_ceiling -> ~ P s) -> 0 <= x -> x + n <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF x n.
Proof.
intros W mem mem' P x n K HP Hx Hxn H.
apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem') SHADOW_OFF x n); [|exact H].
intros y Hy. pose proof asan_consts as ((C1 & _) & _).
assert (D : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold aview. f_equal. apply (p7c_mb_kept W mem mem' P K); unfold shadow_of_addr; [unfold SHADOW_OFF; lia|].
apply HP. unfold SHADOW_OFF in *. lia.
Qed.
Lemma p7c_ra_of : forall (H : word -> bool) m x n,
  range_addressable (aview SEGS H m) SHADOW_OFF x n -> range_addressable (rd_of SEGS (mrestrict H m)) SHADOW_OFF x n.
Proof. intros H m x n R. exact R. Qed.

(* ---- the tree ---- *)
(* a block of the ledger lies in application memory below alloc_ceiling *)
Lemma p7c_lam_box : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (b, m) Lam ->
  4096 <= b /\ b + m <= alloc_ceiling /\ in_app b m /\ 0 <= m.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin. destruct HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk) as (_ & H4096 & Hceil & Happ & _).
assert (Hrq : m + cf_head <= req_size (m + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
split; [lia|]. split; [lia|]. split; [|exact Hm0].
apply (in_app_sub (b - cf_head) (req_size (m + cf_head))); [exact Happ | lia | lia | lia].
Qed.
Lemma p7c_amem_of_app : forall lo len, in_app lo len -> amem_range lo len.
Proof.
intros lo len (H0 & [H|[H1 H2]]); pose proof asan_consts as ((_ & C2) & _); unfold amem_range;
  unfold kLowShadowBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; [left; lia | right; split; [exact H1 | lia]].
Qed.
(* a tree node's home lies below 2 ^ 47 *)
Lemma p7c_home_bound : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> ly_stk_hi ly <= 2 ^ 47 -> 0 <= n ->
  prhex_home ly S Lam regs p n -> 0 <= p /\ p + n <= 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs p n HAR HLED Hhi Hn
  [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hf1 & Hf2) | (Hsp & Hph)]];
  pose proof asan_consts as ((C1 & C2) & _).
- destruct (p7c_lam_box ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin) as (H1 & H2 & _). lia.
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (H1 & H2 & _). lia.
- assert (0 <= spZ regs) by (unfold spZ; exact (proj1 (bv_unsigned_in_range _ _))). lia.
Qed.
(* a node whose 56 bytes miss [lo, hi) lies on one side of it *)
Lemma p7c_apart : forall p lo hi, lo < hi -> (forall z, p <= z < p + 56 -> ~ (lo <= z < hi)) -> p + 56 <= lo \/ hi <= p.
Proof.
intros p lo hi Hlh H. destruct (Z.le_gt_cases (p + 56) lo) as [h|h]; [left; exact h|].
destruct (Z.le_gt_cases hi p) as [h2|h2]; [right; exact h2|]. exfalso. apply (H (Z.max p lo)); lia.
Qed.
(* the n-th kid of an array / object node: ev_kid_tree (S8aItems.v) with the kids block of the ledger exported *)
Lemma p7c_kid_tree : forall ly S Hp W mem md Lam peak cnt fail ran most own regs' v t D (n : nat),
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_Reader.pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D -> (n < length (ev_kids t))%nat ->
  (PjTree.tag t = 5 \/ PjTree.tag t = 6) ->
  exists kids cap Dk,
    PRH_Reader.rd_u64 SEGS (mrestrict (w_H W) mem) (v + 24) kids /\ In (kids, 56 * cap) Lam /\ Z.of_nat n < cap /\
    prhex_tree ly S Lam W regs' mem (kids + 56 * Z.of_nat n) (snd (nth n (ev_kids t) ([], PjTree.JNull))) Dk /\
    incl Dk D /\
    (forall z, PRH_Reader.pj_footR (kids + 56 * Z.of_nat n) Dk z -> PRH_Reader.pj_footR v D z) /\ 4096 <= kids.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs' v t D n HAR HLED Hnode Hn Htag.
destruct t as [| | | txt bits | s | ts | ms]; cbn [PjTree.tag] in Htag; try lia.
- rewrite ev_kids_arr_len in Hn. rewrite ev_kids_arr_nth.
  destruct (ev_arr_kid _ _ _ _ _ n Hnode Hn) as (kids & cap & Dk & Hk & Hc & Hle & HL1 & HinD & Hnode' & Hinc).
  destruct (ev_kid_tree_of B ARx LAWS HSH ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap n
    (nth n ts PjTree.JNull) Dk HAR HLED HL1 HinD ltac:(lia) Hnode' Hinc) as (Ht & Hf & H4).
  exists kids, cap, Dk. split; [exact Hk|]. split; [exact HL1|]. split; [lia|].
  split; [exact Ht|]. split; [exact Hinc|]. split; [exact Hf | exact H4].
- change (ev_kids (PjTree.JObj ms)) with ms in Hn |- *.
  destruct (ev_obj_kid _ _ _ _ _ n Hnode Hn)
    as (kids & keys & cap & x & k & Dk & Hk & _ & Hc & Hle & HL1 & _ & HinD & _ & _ & _ & _ & Hnode' & Hinc).
  destruct (ev_kid_tree_of B ARx LAWS HSH ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap n
    (snd (nth n ms ([], PjTree.JNull))) Dk HAR HLED HL1 HinD ltac:(lia) Hnode' Hinc) as (Ht & Hf & H4).
  exists kids, cap, Dk. split; [exact Hk|]. split; [exact HL1|]. split; [lia|].
  split; [exact Ht|]. split; [exact Hinc|]. split; [exact Hf | exact H4].
Qed.

(* ======== the entry states: st_ok_pi at P_STEP ======== *)
Lemma p7c_stZ : forall (fxc : YK11.FPState) (W : world SEGS) regs mem (s1 : Z),
  getr regs 9 = w64 s1 -> getr regs 24 = w64 SHADOW_OFF -> kHighMemBeg <= s1 -> s1 + 128 <= 2 ^ 47 ->
  (forall z, s1 + 120 <= z < s1 + 128 -> writable_at SEGS (mrestrict (w_H W) mem) z) ->
  st_ok_pi (fx := fxc) SEGS VAL (p7c_E regs []) p7c_ssZ
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (7364 + EV_STEP))) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc W regs mem s1 R9 R24 Hs1 Hs2 Wst.
assert (E9 : ew (p7c_E regs []) 9 = Z_to_bv 64 s1) by (rewrite (p7c_ewr regs [] 9 9%bv) by (lia || reflexivity); exact R9).
assert (E24 : ew (p7c_E regs []) 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (p7c_ewr regs [] 24 24%bv) by (lia || reflexivity); exact R24).
unfold kHighMemBeg in Hs1.
rewrite restrict_mkst_fx. unfold p7c_ssZ. apply (pa_entry_st_ok_full (fx := fxc)).
- unfold p7c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia|].
  constructor.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [p7c_fa0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E24, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold kHighMemBeg. repeat split; try lia; exact I.
Qed.

Lemma p7c_stV : forall (fxc : YK11.FPState) (W : world SEGS) regs mem (s1 q v nv kids dl : Z),
  getr regs 9 = w64 s1 -> getr regs 24 = w64 SHADOW_OFF ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 ->
  0 <= v -> v + 56 <= 2 ^ 47 -> (v + 56 <= s1 \/ s1 + 152 <= v) -> (v + 56 <= q \/ q + 40 <= v) ->
  0 <= nv < 2 ^ 64 -> 0 <= kids < 2 ^ 64 -> 0 <= dl < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 72) 8 (v + 24) ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 80) 8 (v + 40) ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 88) 8 (q + 32) ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 40) 8 nv ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 24) 8 kids ->
  val_mem SEGS (mrestrict (w_H W) mem) (q + 32) 4 dl ->
  (forall z, s1 + 120 <= z < s1 + 128 -> writable_at SEGS (mrestrict (w_H W) mem) z) ->
  (forall z, q + 32 <= z < q + 36 -> writable_at SEGS (mrestrict (w_H W) mem) z) ->
  st_ok_pi (fx := fxc) SEGS VAL (p7c_E regs [w64 (v + 24); w64 (v + 40); w64 (q + 32); w64 nv; w64 kids; w64 dl])
    p7c_ssV (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (7364 + EV_STEP))) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc W regs mem s1 q v nv kids dl R9 R24 Hs1 Hsq Hq Hv0 Hv1 Hvs Hvq Hnv Hkd Hdl M72 M80 M88 M40 M24 M32 Wst Wq.
set (ex := [w64 (v + 24); w64 (v + 40); w64 (q + 32); w64 nv; w64 kids; w64 dl]).
assert (E9 : ew (p7c_E regs ex) 9 = Z_to_bv 64 s1) by (rewrite (p7c_ewr regs ex 9 9%bv) by (lia || reflexivity); exact R9).
assert (E24 : ew (p7c_E regs ex) 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (p7c_ewr regs ex 24 24%bv) by (lia || reflexivity); exact R24).
assert (E32 : ew (p7c_E regs ex) 32 = Z_to_bv 64 (v + 24)) by exact (p7c_ewx regs ex 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew (p7c_E regs ex) 33 = Z_to_bv 64 (v + 40)) by exact (p7c_ewx regs ex 1 ltac:(unfold A_TEXT; lia)).
assert (E34 : ew (p7c_E regs ex) 34 = Z_to_bv 64 (q + 32)) by exact (p7c_ewx regs ex 2 ltac:(unfold A_TEXT; lia)).
assert (E35 : ew (p7c_E regs ex) 35 = Z_to_bv 64 nv) by exact (p7c_ewx regs ex 3 ltac:(unfold A_TEXT; lia)).
assert (E36 : ew (p7c_E regs ex) 36 = Z_to_bv 64 kids) by exact (p7c_ewx regs ex 4 ltac:(unfold A_TEXT; lia)).
assert (E37 : ew (p7c_E regs ex) 37 = Z_to_bv 64 dl) by exact (p7c_ewx regs ex 5 ltac:(unfold A_TEXT; lia)).
unfold kHighMemBeg in Hs1.
rewrite restrict_mkst_fx. unfold p7c_ssV. apply (pa_entry_st_ok_full (fx := fxc)).
- unfold p7c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold p7c_memV. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS _ _ s1 72 8 (SOff 32 0) (v + 24)); [exact (p7c_denot0 _ 32 _ E32) | cbn; lia | lia | exact M72].
    * apply (chunk_ok_val SEGS _ _ s1 80 8 (SOff 33 0) (v + 40)); [exact (p7c_denot0 _ 33 _ E33) | cbn; lia | lia | exact M80].
    * apply (chunk_ok_val SEGS _ _ s1 88 8 (SOff 34 0) (q + 32)); [exact (p7c_denot0 _ 34 _ E34) | cbn; lia | lia | exact M88].
  + rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wq; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (q + 32) 0 4 (SOff 37 0) dl); [exact (p7c_denot0 _ 37 _ E37) | cbn; lia | lia |].
    rewrite Z.add_0_r. exact M32.
  + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (v + 40) 0 8 (SOff 35 0) nv); [exact (p7c_denot0 _ 35 _ E35) | cbn; lia | lia |].
    rewrite Z.add_0_r. exact M40.
  + rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (v + 24) 0 8 (SOff 36 0) kids); [exact (p7c_denot0 _ 36 _ E36) | cbn; lia | lia |].
    rewrite Z.add_0_r. exact M24.
- apply pairwise_disjoint_of_extents. unfold extent_of_region, p7c_memV.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32, E33, E34, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [p7c_faV f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E24, E32, E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold kHighMemBeg. repeat split; try lia; exact I.
Qed.

(* ======== the post: C_KID from a run's end ======== *)
Lemma p7c_post : forall (a : ev_act) W regs mem md ly S Hp k o n cap acc i dln regs' mem' md' kid dl1,
  ev_pre (fx := fx) B ARx a ->
  ev_at_step B ARx SK a W regs mem md ly S Hp k o n cap acc i dln ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ p7c_Wr a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall r, In r p7c_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 11 = w64 kid -> getr regs' 23 = w64 (if kid =? 0 then 1 else 0) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 120) 8 (Z.of_nat n) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 dl1 ->
  ev_dl_kid a o n dln dl1 ->
  (ev_mid B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dl1 -> ev_kid_ok a ly S W mem' o n kid) ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_at_kid B ARx SK a W regs' mem' md' ly S Hp k o n cap acc i dln kid dl1.
Proof.
intros a W regs mem md ly S Hp k o n cap acc i dln regs' mem' md' kid dl1 HPRE HSTN HJ' RAW GROW HK N11 N23 V120 V32
  HDL HKID HMN'.
destruct HSTN as (HMID & HR & R20 & R21 & R22 & R23 & R27 & R11 & HSP & V104 & Hdep & Hilen & Hnacc & HV & Hdl & Hni).
destruct (BNDS a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof asan_consts as ((C1 & C2) & _).
assert (VK : forall b (nb : nat) v, b + Z.of_nat nb <= ea_S1 a + 120 \/ ea_S1 a + 128 <= b ->
  b + Z.of_nat nb <= ea_q a + 32 \/ ea_q a + 36 <= b -> 0 <= b -> b + Z.of_nat nb <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) b nb v -> val_mem SEGS (mrestrict (w_H W) mem') b nb v).
{ intros b nb v H1 H2 H3 H4. apply (p7c_vm_kept W mem mem' (p7c_Wr a) b nb v RAW H3 H4).
  intros z Hz. unfold p7c_Wr. lia. }
pose proof HMID as (_ & _ & _ & _ & _ & (Q0 & Q8 & Q16 & Q24 & _) & _).
assert (HCUR' : prhex_cur W mem' (ea_q a) (ea_x0 a + Z.of_nat i) (ea_x0 a + ea_len a) (ea_dep a + 1) (ea_scr a) dl1).
{ split; [apply VK; [lia | lia | lia | lia | exact Q0]|].
  split; [apply VK; [lia | lia | lia | lia | exact Q8]|].
  split; [apply VK; [lia | lia | lia | lia | exact Q16]|].
  split; [apply VK; [lia | lia | lia | lia | exact Q24]|]. exact V32. }
assert (HMID' : ev_mid B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dl1).
{ apply (MIDF a ly S Hp W mem md k _ _ _ mem' md' _ _ _ (p7c_Wr a) HPRE HMID HJ' RAW GROW); [|exact HCUR' | exact HMN'].
  intros z [Hz|Hz]; [left; lia | right; right; right; exact Hz]. }
unfold ev_spills in HSP. cbv zeta in HSP.
destruct HSP as (P24 & P32 & P40 & P48 & P56 & P64 & P72 & P80 & P88).
unfold ev_at_kid. cbv zeta.
split; [exact HMID'|].
split; [unfold ev_regs in HR |- *; rewrite !HK by (cbv; tauto); exact HR|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact R20|].
split; [rewrite (HK 21%bv) by (cbv; tauto); exact R21|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact R22|].
split; [rewrite (HK 27%bv) by (cbv; tauto); exact R27|].
split; [exact N11|]. split; [exact N23|].
split.
{ unfold ev_spills. cbv zeta.
  split; [apply VK; [lia | lia | lia | lia | exact P24]|].
  split; [apply VK; [lia | lia | lia | lia | exact P32]|].
  split; [apply VK; [lia | lia | lia | lia | exact P40]|].
  split; [apply VK; [lia | lia | lia | lia | exact P48]|].
  split; [apply VK; [lia | lia | lia | lia | exact P56]|].
  split; [apply VK; [lia | lia | lia | lia | exact P64]|].
  split; [apply VK; [lia | lia | lia | lia | exact P72]|].
  split; [apply VK; [lia | lia | lia | lia | exact P80]|].
  apply VK; [lia | lia | lia | lia | exact P88]. }
split; [apply VK; [lia | lia | lia | lia | exact V104]|].
split; [exact V120|].
split; [exact Hdep|]. split; [exact Hni|]. split; [exact Hilen|]. split; [exact Hnacc|]. split; [exact HV|].
split; [exact (HKID HMID')|]. split; [exact HDL | exact Hdl].
Qed.

(* ======== the run tactics ======== *)
(* an atom's value through the run's environment *)
Ltac p7c_ewq n :=
  first [ match goal with Ex : ew _ n = Z_to_bv 64 _ |- _ => exact Ex end
        | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia);
          match goal with Ex : ew _ n = Z_to_bv 64 _ |- _ => exact Ex end ].
Ltac p7c_U n v Hc := rewrite (U_atom _ n v) in Hc; [ | p7c_ewq n | first [lia | unfold SHADOW_OFF; lia] ].
Ltac p7c_Ug n v := rewrite (U_atom _ n v); [ | p7c_ewq n | first [lia | unfold SHADOW_OFF; lia] ].
(* a region's base, read through the run's environment *)
Ltac p7c_base Hr :=
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb extK] in Hr;
  rewrite ?ew_havoc_old in Hr by (cbv; lia);
  repeat match goal with Ex : ew ?E0 ?nn = Z_to_bv 64 _ |- _ => rewrite Ex in Hr end;
  rewrite ?unsigned_lit_small in Hr by lia.
(* the write windows of a state are inside the write set *)
Ltac p7c_inwr :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); vm_compute in Hin; unfold p7c_Wr, p7c_WrS;
  repeat (destruct Hin as [<- | Hin]; [p7c_base Hr; lia |]); destruct Hin.
(* fold a run's frame into the accumulated frame KM (write set P) and growth GM *)
Ltac p7c_keep P :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?mA) (mrestrict _ ?mB), HG : mem_grows (mrestrict _ ?mA) (mrestrict _ ?mB),
    KM : forall x : word, ~ P (bv_unsigned x) -> mrestrict _ ?mA x = mrestrict _ ?m0 x,
    GM : mem_grows (mrestrict _ ?m0) (mrestrict _ ?mA) |- _ =>
    let K2 := fresh "K2" in let G2 := fresh "G2" in
    pose proof (p7c_frame_step Ex rsx Hh m0 mA mB P ltac:(p7c_inwr) HFr KM) as K2;
    pose proof (mem_grows_trans _ _ _ GM HG) as G2;
    clear HFr HG KM GM; rename K2 into KM; rename G2 into GM;
    try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end
  end.
(* the write premise: the windows s1 + 120 and q + 32 are in the caller window [sp0 - STK, sp0 + d) *)
Ltac p7c_ewv :=
  cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia);
  repeat match goal with Ex : ew ?E0 ?nn = Z_to_bv 64 _ |- context [ew ?E0 ?nn] => rewrite Ex end;
  apply unsigned_lit_small; lia.
Ltac p7c_awr a :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (ea_S1 a));
        [reflexivity | p7c_ewv | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; lia |]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (ea_q a + 32));
        [reflexivity | p7c_ewv | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; lia |] ].
(* a register of a run's final state *)
Ltac p7c_get HS r H :=
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (st_ok_pi_restrict_reg Hh E' ss ms r HS) as H;
    change (sr_get (ss_regs ss) r) with e in H end.
(* a chunk of a run's final state: region i, its first chunk *)
Ltac p7c_chunk HS i off w e H :=
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss (restrict ?Hh ?ms) =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (p7c_chunk_val _ E' ss ms Hh i r off w e HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [YP09.r_chunks]; left; reflexivity) ltac:(lia)) as H;
    cbn [YP09.r_base base_val] in H end.
(* the chunk value of an atom *)
Ltac p7c_val H n v :=
  rewrite (p7c_denot0 _ n v) in H; [rewrite unsigned_lit_small in H by lia | p7c_ewq n].
(* the C_KID configuration of a run's end *)
Ltac p7c_end HSx lyx Sx Hpx kx kidx dlx :=
  pmkst HSx; apply SRr_ret; cbv beta;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
    exists rg, m, d, lyx, Sx, Hpx, kx, kidx, dlx end;
  split; [exact (p7c_cfg_eq _ _ EV_KID _ _)|].

(* v->kids + 56 n, as the code computes it (0x83834-0x83844) *)
Lemma p7c_kid_denot : forall E kids n, ew E 11 = Z_to_bv 64 n -> ew E 36 = Z_to_bv 64 kids ->
  0 <= n < 2 ^ 32 -> 0 <= kids < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit 56)) (SOff 36 0)) = Z_to_bv 64 (kids + 56 * n).
Proof.
intros E kids n H11 H36 Hn Hk. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit 56)) (SOff 36 0))))
  with (U E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit 56)) (SOff 36 0))).
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 11 n H11), (U_atom E 36 kids H36) by lia.
cbn [zalu_raw zmd_raw]. change (zcanon 56) with 56. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (n * 56)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ======== SEG 1: P_STEP (0x837ec) -> C_KID (0x83878) ========
   Report checks of the range, each NOT TAKEN:
     0x837f8-0x83804 (shadow of v' + 40, `ld a3,0(a0)` = v->n): token obligation range_addressable (v' + 40) 8, from
       prhex_tree's range_addressable v' 56 (ev_mid), carried across the store at s1 + 120 below alloc_ceiling;
     0x83818-0x83824 (shadow of v' + 24, `ld a0,0(a0)` = v->kids): range_addressable (v' + 24) 8, the same fact;
     0x8384c-0x8385c with the partial-granule arm 0x83b34-0x83b40 (signed shadow of q + 32 before `sw s7,0(a0)`):
       slow_block obligation range_addressable (q + 32) 4, from ev_q_addressable (struct ex's 40 bytes, Qed).
   The branch 0x8382c `beqz a0` (v->kids = NULL) is NOT TAKEN when n < v->n: the node has item n, so its kids array is
   a block (kids, 56 cap) of the ledger with 4096 <= kids (ev_kid_tree / p7c_kid_tree). *)
Lemma ev7_seg1_A : ev7_seg1_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros a fxc W regs mem md ly S Hp k o n cap acc i dln HPRE HFX HSTN.
pose proof HSTN as (HMID & HR & R20 & R21 & R22 & R23 & R27 & R11 & HSP & V104 & Hdep & Hilen & Hnacc & HV & Hdl & Hni).
destruct (BNDS a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HMID as (HJ & _ & _ & _ & HLED & HCUR & _ & _ & HTREE & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof HCUR as (_ & _ & _ & _ & Q32).
pose proof HPRE as ((HA & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
assert (HN : Z.of_nat n <= ea_len a) by (unfold ea_len; lia).
assert (Wst : forall z, ea_S1 a + 120 <= z < ea_S1 a + 128 -> writable_at SEGS (mrestrict (w_H W) mem) z)
  by (intros z Hz; apply (apresent_writable SEGS); apply HPRES; lia).
assert (Wq : forall z, ea_q a + 32 <= z < ea_q a + 36 -> writable_at SEGS (mrestrict (w_H W) mem) z)
  by (intros z Hz; apply (apresent_writable SEGS); apply HPRES; lia).
assert (Hdl01 : dln = 0 \/ dln = 1) by exact (proj1 Hdl).
assert (WrHi : forall s, SHADOW_OFF <= s < alloc_ceiling -> ~ p7c_Wr a s) by (intros s Hs; unfold p7c_Wr; lia).
pose proof (mem_grows_refl (mrestrict (w_H W) mem)) as GM.
rewrite <- (p7c_cfg_eq fxc regs EV_STEP mem md).
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
destruct (Z.eq_dec (ev_v' (ea_v a) o (ea_t a)) 0) as [Hv0 | Hv0].
{ (* ---- v' = 0: `beqz s7` taken, kid = 0, s7 = 1, in->differs untouched ---- *)
  assert (KM : forall x : word, ~ p7c_WrS a (bv_unsigned x) -> mrestrict (w_H W) mem x = mrestrict (w_H W) mem x)
    by (intros; reflexivity).
  pose proof (p7c_stZ fxc W regs mem (ea_S1 a) R9 R24 ltac:(unfold kHighMemBeg; lia) ltac:(lia) Wst) as HS.
  assert (HAE : env_agree 32 (Ereg regs []) (p7c_E regs [])) by apply p7c_agree.
  assert (E11 : ew (p7c_E regs []) 11 = Z_to_bv 64 (Z.of_nat n))
    by (rewrite (p7c_ewr regs [] 11 11%bv) by (lia || reflexivity); exact R11).
  assert (E23 : ew (p7c_E regs []) 23 = Z_to_bv 64 (ev_v' (ea_v a) o (ea_t a)))
    by (rewrite (p7c_ewr regs [] 23 23%bv) by (lia || reflexivity); exact R23).
  assert (E9 : ew (p7c_E regs []) 9 = Z_to_bv 64 (ea_S1 a))
    by (rewrite (p7c_ewr regs [] 9 9%bv) by (lia || reflexivity); exact R9).
  assert (HEI : img_env VAL A_LIM (p7c_E regs [])) by (unfold p7c_E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS p7c_Bx [] (p7c_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7c_Bspan.
  { p7c_awr a. }
  p7c_keep (p7c_WrS a).
  psrr_branch_tok RUN BR HS SHOK p7c_Bspan.
  - (* taken: 0x83870 li a1,0; 0x83874 li s7,1 *)
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7c_Bspan (7364 + EV_KID).
    { p7c_awr a. }
    p7c_keep (p7c_WrS a).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] p7c_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
      as HK.
    cbn [ms_regs restrict] in HK.
    p7c_get HS (11%bv : bv 5) N11. p7c_get HS (23%bv : bv 5) N23.
    p7c_chunk HS 0%nat 120 8%N (SOff 11 0) V120.
    p7c_base V120. p7c_val V120 11%nat (Z.of_nat n).
    p7c_end HS ly S Hp k 0 dln.
    apply (p7c_post a W regs mem md ly S Hp k o n cap acc i dln); [exact HPRE | exact HSTN | exact HJ | | exact GM
      | exact HK | rewrite N11; reflexivity | rewrite N23; reflexivity | exact V120 | | | | exact HMN ].
    + intros x Hx. apply KM. intros h. apply Hx. left. exact h.
    + apply (p7c_vm_kept W mem _ (p7c_WrS a) (ea_q a + 32) 4 dln KM); [lia | lia | | exact Q32].
      intros z Hz. unfold p7c_WrS. lia.
    + split; [exact Hdl01|]. split; [intros H; left; exact H | intros [H|(H & _)]; [exact H | contradiction]].
    + intros _. left. split; [reflexivity | left; exact Hv0].
  - (* not taken: v' <> 0, impossible *)
    exfalso. rewrite branch_eq_U, U_SLit in Hc. p7c_U 23%nat (ev_v' (ea_v a) o (ea_t a)) Hc.
    rewrite Hv0 in Hc. change (zcanon 0) with 0 in Hc. rewrite Z.eqb_refl in Hc. discriminate Hc. }
(* ---- v' <> 0: v' = v, a node of the container's type ---- *)
assert (KM : forall x : word, ~ p7c_Wr a (bv_unsigned x) -> mrestrict (w_H W) mem x = mrestrict (w_H W) mem x)
  by (intros; reflexivity).
assert (Etv : ev_tv (ea_v a) o (ea_t a) = true).
{ destruct (ev_tv (ea_v a) o (ea_t a)) eqn:X; [reflexivity|]. exfalso. apply Hv0. unfold ev_v'. rewrite X. reflexivity. }
assert (EVV : ev_v' (ea_v a) o (ea_t a) = ea_v a) by (unfold ev_v'; rewrite Etv; reflexivity).
assert (Hva : ea_v a <> 0) by (rewrite <- EVV; exact Hv0).
assert (Htag : PjTree.tag (ea_t a) = 5 \/ PjTree.tag (ea_t a) = 6).
{ unfold ev_tv in Etv. apply orb_true_iff in Etv as [E1|E1]; [apply Z.eqb_eq in E1; contradiction|].
  apply Z.eqb_eq in E1. destruct o; [right|left]; exact E1. }
destruct HTREE as [HT0|HT]; [contradiction|].
pose proof HT as (HNODE & HHOME & HRA & HHV).
destruct HTR0 as [HT0|(_ & _ & HFOOT)]; [contradiction|].
change (spZ (ea_regs a)) with (ea_sp0 a) in HFOOT.
pose proof HA as (_ & _ & _ & _ & _ & HSTK & _). pose proof HSTK as (_ & _ & _ & _ & _ & H47 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _).
assert (Hhi : ly_stk_hi ly <= 2 ^ 47) by (rewrite Eshi; exact H47).
destruct (p7c_home_bound ly S Hp W mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) (ea_regs a)
  (ea_v a) 56 HAR HLED Hhi ltac:(lia) HHOME) as (Hv1 & Hv2).
assert (FT : forall z, ea_v a <= z < ea_v a + 56 -> ~ (ea_q a <= z < ea_q a + 40) /\
  ~ (ea_sp0 a - ea_STK a <= z < ea_sp0 a)).
{ intros z Hz. destruct (HFOOT z ltac:(unfold PjStruct.pj_foot; left; exact Hz)) as (_ & F2 & F3 & _).
  split; assumption. }
assert (NA1 : ea_v a + 56 <= ea_sp0 a - ea_STK a \/ ea_sp0 a <= ea_v a)
  by (apply p7c_apart; [lia | intros z Hz; exact (proj2 (FT z Hz))]).
assert (NA2 : ea_v a + 56 <= ea_q a \/ ea_q a + 40 <= ea_v a)
  by (apply p7c_apart; [lia | intros z Hz; exact (proj1 (FT z Hz))]).
destruct (ev_node_hdr _ _ _ _ _ HNODE) as (num & str & kids & keys & nv & capH & HH & Env & _).
destruct HH as (_ & _ & _ & _ & (Hk0 & HKV) & _ & (Hn0 & HNV) & _).
destruct HSP as (P24 & P32 & P40 & P48 & P56 & P64 & P72 & P80 & P88).
rewrite EVV in P72, P80.
rewrite (Z.mod_small (ea_v a + 24)) in P72 by lia. rewrite (Z.mod_small (ea_v a + 40)) in P80 by lia.
pose proof (p7c_stV fxc W regs mem (ea_S1 a) (ea_q a) (ea_v a) nv kids dln R9 R24 ltac:(unfold kHighMemBeg; lia)
  ltac:(lia) ltac:(lia) Hv1 Hv2 ltac:(lia) NA2 Hn0 Hk0 ltac:(lia) P72 P80 P88 HNV HKV Q32 Wst Wq) as HS.
set (ex := [w64 (ea_v a + 24); w64 (ea_v a + 40); w64 (ea_q a + 32); w64 nv; w64 kids; w64 dln]) in HS.
assert (HAE : env_agree 32 (Ereg regs ex) (p7c_E regs ex)) by apply p7c_agree.
assert (E9 : ew (p7c_E regs ex) 9 = Z_to_bv 64 (ea_S1 a)) by (rewrite (p7c_ewr regs ex 9 9%bv) by (lia || reflexivity); exact R9).
assert (E24 : ew (p7c_E regs ex) 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (p7c_ewr regs ex 24 24%bv) by (lia || reflexivity); exact R24).
assert (E11 : ew (p7c_E regs ex) 11 = Z_to_bv 64 (Z.of_nat n))
  by (rewrite (p7c_ewr regs ex 11 11%bv) by (lia || reflexivity); exact R11).
assert (E23 : ew (p7c_E regs ex) 23 = Z_to_bv 64 (ea_v a))
  by (rewrite (p7c_ewr regs ex 23 23%bv) by (lia || reflexivity); rewrite R23, EVV; reflexivity).
assert (E32 : ew (p7c_E regs ex) 32 = Z_to_bv 64 (ea_v a + 24)) by exact (p7c_ewx regs ex 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew (p7c_E regs ex) 33 = Z_to_bv 64 (ea_v a + 40)) by exact (p7c_ewx regs ex 1 ltac:(unfold A_TEXT; lia)).
assert (E34 : ew (p7c_E regs ex) 34 = Z_to_bv 64 (ea_q a + 32)) by exact (p7c_ewx regs ex 2 ltac:(unfold A_TEXT; lia)).
assert (E35 : ew (p7c_E regs ex) 35 = Z_to_bv 64 nv) by exact (p7c_ewx regs ex 3 ltac:(unfold A_TEXT; lia)).
assert (E36 : ew (p7c_E regs ex) 36 = Z_to_bv 64 kids) by exact (p7c_ewx regs ex 4 ltac:(unfold A_TEXT; lia)).
assert (E37 : ew (p7c_E regs ex) 37 = Z_to_bv 64 dln) by exact (p7c_ewx regs ex 5 ltac:(unfold A_TEXT; lia)).
assert (HEI : img_env VAL A_LIM (p7c_E regs ex)) by (unfold p7c_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS p7c_Bx [] (p7c_E regs ex) (mrestrict (w_H W) mem)) by apply Forall_nil.
paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7c_Bspan.
{ p7c_awr a. }
p7c_keep (p7c_Wr a).
psrr_branch_tok RUN BR HS SHOK p7c_Bspan.
{ (* taken: v' = 0, impossible *)
  exfalso. rewrite branch_eq_U, U_SLit in Hc. p7c_U 23%nat (ea_v a) Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc. contradiction. }
clear Hc.
(* 0x837f4-0x83814: v->n read through the token of 0x837f8-0x83804 *)
paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7c_Bspan.
{ unfold p7c_Bx. p7c_Ug 24%nat SHADOW_OFF. p7c_Ug 33%nat (ea_v a + 40). apply p7c_ra_of.
  apply (p7c_ra_kept W mem _ (p7c_Wr a) _ _ KM WrHi); [lia | lia |].
  apply (range_addressable_sub _ _ (ea_v a) 56); [exact HRA | lia | lia]. }
{ p7c_awr a. }
p7c_keep (p7c_Wr a).
psrr_branch_tok RUN BR HS SHOK p7c_Bspan.
- (* bgeu taken: n >= v->n, no kid; 0x8384c-0x8386c, the arm 0x83b34-0x83b40, in->differs = 1 *)
  rewrite branch_geu_U in Hc. p7c_U 11%nat (Z.of_nat n) Hc. p7c_U 35%nat nv Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7c_Bspan (7364 + EV_KID).
  { unfold p7c_Bx. p7c_Ug 24%nat SHADOW_OFF. p7c_Ug 34%nat (ea_q a + 32). apply p7c_ra_of.
    apply (p7c_ra_kept W mem _ (p7c_Wr a) _ _ KM WrHi); [lia | lia |].
    apply (range_addressable_sub _ _ (ea_q a) 40); [|lia|lia].
    exact (ev_q_addressable (fx := fx) B ARx SK LAWS a ly S Hp W mem md k _ _ _ HPRE HMID). }
  { p7c_awr a. }
  p7c_keep (p7c_Wr a).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs ex p7c_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  p7c_get HS (11%bv : bv 5) N11. p7c_get HS (23%bv : bv 5) N23.
  p7c_chunk HS 0%nat 120 8%N (SOff 11 0) V120. p7c_base V120. p7c_val V120 11%nat (Z.of_nat n).
  p7c_chunk HS 1%nat 0 4%N (SLit 1) V32. p7c_base V32. rewrite Z.add_0_r in V32.
  change (bv_unsigned (sv_denot _ (SLit 1))) with 1 in V32.
  p7c_end HS ly S Hp k 0 1.
  apply (p7c_post a W regs mem md ly S Hp k o n cap acc i dln); [exact HPRE | exact HSTN | exact HJ | exact KM | exact GM
    | exact HK | rewrite N11; reflexivity | rewrite N23; reflexivity | exact V120 | exact V32 | | | exact HMN ].
  + split; [right; reflexivity|]. split; [intros _; right; split; [exact Hv0 | lia] | intros _; reflexivity].
  + intros _. left. split; [reflexivity | right; lia].
- (* bgeu not taken: n < v->n, the kid &v->kids[n] *)
  rewrite branch_geu_U in Hc. p7c_U 11%nat (Z.of_nat n) Hc. p7c_U 35%nat nv Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hnl : (n < length (ev_kids (ea_t a)))%nat) by lia.
  clear Hc.
  destruct (p7c_kid_tree ly S Hp W mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) (ea_regs a) (ea_v a)
    (ea_t a) (ea_D a) n HAR HLED HNODE Hnl Htag) as (kids0 & cap0 & Dk0 & (Hk00 & HK0) & HL0 & Hnc0 & _ & _ & _ & H4096).
  assert (Ekids : kids = kids0) by exact (p7c_vm_det _ _ _ _ HKV HK0 Hk0 Hk00). subst kids0.
  destruct (p7c_lam_box ly S Hp W mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) kids (56 * cap0)
    HAR HLED HL0) as (Hb1 & Hb2 & Happ & _).
  (* 0x83818-0x8382c: v->kids read through the token of 0x83818-0x83824 *)
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7c_Bspan.
  { unfold p7c_Bx. p7c_Ug 24%nat SHADOW_OFF. p7c_Ug 32%nat (ea_v a + 24). apply p7c_ra_of.
    apply (p7c_ra_kept W mem _ (p7c_Wr a) _ _ KM WrHi); [lia | lia |].
    apply (range_addressable_sub _ _ (ea_v a) 56); [exact HRA | lia | lia]. }
  { p7c_awr a. }
  p7c_keep (p7c_Wr a).
  psrr_branch_tok RUN BR HS SHOK p7c_Bspan.
  + (* beqz a0 taken: kids = 0, impossible (4096 <= kids) *)
    exfalso. rewrite branch_eq_U, U_SLit in Hc. p7c_U 36%nat kids Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_eq in Hc. lia.
  + (* 0x83830-0x83848: s7 = 0, a1 = kids + 56 n *)
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7c_Bspan (7364 + EV_KID).
    { p7c_awr a. }
    p7c_keep (p7c_Wr a).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs ex p7c_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
      as HK.
    cbn [ms_regs restrict] in HK.
    p7c_get HS (11%bv : bv 5) N11. p7c_get HS (23%bv : bv 5) N23.
    rewrite (p7c_kid_denot _ kids (Z.of_nat n)) in N11; [| p7c_ewq 11%nat | p7c_ewq 36%nat | lia | lia].
    p7c_chunk HS 0%nat 120 8%N (SOff 11 0) V120. p7c_base V120. p7c_val V120 11%nat (Z.of_nat n).
    p7c_chunk HS 1%nat 0 4%N (SOff 37 0) V32. p7c_base V32. rewrite Z.add_0_r in V32. p7c_val V32 37%nat dln.
    p7c_end HS ly S Hp k (kids + 56 * Z.of_nat n) dln.
    apply (p7c_post a W regs mem md ly S Hp k o n cap acc i dln); [exact HPRE | exact HSTN | exact HJ | exact KM | exact GM
      | exact HK | exact N11 | | exact V120 | exact V32 | | | exact HMN ].
    * rewrite N23. replace (kids + 56 * Z.of_nat n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    * split; [exact Hdl01|]. split; [intros H; left; exact H | intros [H|(_ & H)]; [exact H | lia]].
    * intros HMID'. right. split; [exact Hv0|]. split; [exact Hnl|]. split; [lia|]. split; [lia|].
      split; [apply p7c_amem_of_app; apply (in_app_sub kids (56 * cap0)); [exact Happ | lia | lia | lia]|].
      pose proof HMID' as (HJ2 & _ & _ & _ & HLED2 & _ & _ & _ & HTREE2 & _). pose proof HJ2 as (HAR2 & _).
      destruct HTREE2 as [HT2|(HNODE2 & _)]; [contradiction|].
      destruct (p7c_kid_tree ly S Hp W _ _ (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) (ea_regs a) (ea_v a)
        (ea_t a) (ea_D a) n HAR2 HLED2 HNODE2 Hnl Htag) as (kids2 & cap2 & Dk & (Hk20 & HK2) & _ & _ & Ht2 & Hinc & Hft & _).
      assert (HKV' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_v a + 24) 8 kids).
      { apply (p7c_vm_kept W mem _ (p7c_Wr a) (ea_v a + 24) 8 kids KM); [lia | lia | | exact HKV].
        intros z Hz. unfold p7c_Wr. lia. }
      assert (Ek2 : kids = kids2) by exact (p7c_vm_det _ _ _ _ HKV' HK2 Hk0 Hk20). subst kids2.
      exists Dk. split; [exact Ht2|]. split; [exact Hinc | exact Hft].
Qed.

End w.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v; 1219 of its 1297 lines of code are new or changed and 850 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aEntry.v, with its module paths and module names changed; 1189 of its 1363 lines of code are new or changed and 1123 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): SEGMENT 3 of piece 7
   (ev_item_step) of the walk of ex_value (A' 0x832a4), at L := A_prog_listing, PA := PI_prog_A, in the SRr /
   srealizes form, against S8aItems.v's cut interface. Hand: h-walk-ctrl's EvItems, sub-lane S8aP7b.
   The stretch: C_KEY (A' 0x839a0, EV_KEY) -> C_CALL (A' 0x83a4c, EV_CALL), with the refusal join 0x83b54 ->
   P_EXIT (A' 0x83d48). C source fuzz_preset.c @0b89c6c1bd :270-273 (`ex_ws(in); if (in->p >= in->end ||
   *in->p != ':') return -1; in->p++;`) and the kid reload 0x83a48 that the recursive call takes as its second
   argument. The inlined ex_ws at 0x839c0-0x83a08 is NOT walked: the Section hypothesis WS
   (ev_ws_loop_spec_FIX) covers it at b = 0x71c, e = 0x768, and its report arms 0x839e8 and 0x83a04 are its own.
   `ev_at_key`'s name clause was corrected at the request of this lane (S8aItems.v 26bb6a56313 :248-257): the cut
   is proved against the published text, with no twin.

   Report checks in range, each NOT TAKEN with the fact that makes it so:
     0x839a4  bnez (shadow of q + 8) : the symbolic chunk at s4 is the byte 0 of `alx_zshadow_byte` on the real
              stack (ev_q_stack puts [q, q + 40) inside [ly_stk_lo, ly_stk_hi)).
     0x839ac, 0x83a10, 0x83a3c  bnez (shadow of q) : the same, at q itself.
     0x83a28  bnez (shadow of the text byte), with its partial-granule arm 0x83b28-0x83b30 -> 0x83fdc : the token
             is covered by sh_ok (p7b_stB), whose range_addressable is the text's own, src_rd's, which ev_mid
             carries at every cut (upstream it is ev_inblk_shadow_FIX on the text's block).
     0x839e8, 0x83a04  belong to the ws loop and are discharged by WS, not here.

   Numerals. LENGTH: 0x6fc / 0x7a8 / 0xaa4 (EV_KEY / EV_CALL / EV_EXIT, pc - 0x832a4 on the bff8519b listing),
   0x71c and 0x768 (the second entry of EV_WSLOOPS: the ws loop's first slot A' 0x839c0 and its exit A' 0x83a0c),
   7364 (ex_value's listing offset, A_prog_sigma AS_ex_value - A_prog_base); 1, 4, 8, 16, 24, 32, 40, 56, 96, 104,
   120, 128, 152 (access sizes and s1 / struct ex / tree-node offsets, as in S8aIface's ev_spills / ev_mid and
   S8aItems' cuts). DERIVED: atom indices 9-35 (the engine's Ereg numbering, extras from 32), 2 ^ 44 / 2 ^ 47 /
   2 ^ 64 (shadow span, user-space top, word range), 4096 (the page floor of application memory), P7B_QLO =
   0x7fff7f800000 (asan_consts' closed floor of alloc_ceiling, as S8aDisp.v's D_QLO; a RunCeil field cannot be
   vm_computed, its floor can; not an image address). WORD: 0 (a
   clear shadow byte), 32 (the blank bound), 58 (':'), 91 / 123 (the openers), 255 (the byte bound), -1 (the
   refusal result), register numbers 2-27 (RISC-V ABI). No ADDRESS literal: addresses come from pa_sigma / pa_val.

   p7b_vm .. p7b_nodeR_frame, p7b_sh_lt, p7b_ra_kept, p7b_lamb and p7b_fr_bounds are COPIES (renamed) of Qed texts of
   S8aItemsWalk.v's FRAME KIT at sha ebf0edf14b4 (evf_vm / evf_garr8 / evf_hdr / evf_cstr / evf_nodeP /
   evf_items_frame / evf_mems_frame / evf_nodeR_frame / evf_sh_lt / evf_ra, and the LAMB / flag-word steps of
   ev_mid_frame); p7b_denot_atom .. p7b_regs_kept, p7b_inp and the state / run idiom are S8aDisp.v's at
   85194de74e52, renamed. Neither file is Required (S8aP7 owns S8aItemsWalk.v; S8aDisp.v is another slice's).
   Hypotheses beyond the shared five: MIDF / BNDS, lane FRAME's ev_mid_frame / ev_bounds verbatim (the internal file FRAME.md). *)
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
(* (HSH is not a hypothesis: S8aItems.v ev_hshadow_of_laws derives it from LAWS's field alx_hshadow) *)
(* STAND-IN: a Theorem Labs lane, the image binding of PrhImg: alloc.c's statics (prh_pst) are image bytes (true at prh_img_A: PRH_Img.v,
   below kLowMemEnd by pa_segs_low, so apart from the stack); without it a generic PrhImg could put them in `struct ex` *)
Hypothesis PSTI : forall z, Exists (in_zr z) PST -> in_img SEGS z.
(* STAND-IN: lane FRAME, S8aItemsWalk.v's FRAME KIT (Qed at 26bb6a56313): the ev_mid transport of a straight
   stretch and the frame arithmetic of an activation, verbatim from the internal file FRAME.md. S8aP7 discharges both. MIDF's last
   premise, memnorm at the new memory, is ev_mid's last conjunct (S8aIface.v, the memnorm interface), as in
   S8aItemsWalk.ev_mid_frame. *)
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
Hypothesis BNDS : forall (a : ev_act), ev_pre (fx := fx) B ARx a ->
  alloc_ceiling <= ea_sp0 a - ea_STK a /\ ea_sp0 a - ea_STK a <= ea_S1 a /\ ea_S1 a + 152 <= ea_sp0 a /\
  ea_S1 a mod 32 = 0 /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\ ea_sp0 a + ea_d a <= 2 ^ 47 /\
  ea_q a mod 8 = 0 /\ 0 <= ea_d a.

(* plain lia: the imported `lia` prunes hypotheses and fails on goals over record projections. Zify's euclidean
   division equations are OFF in this file, so no `mod` goal is ever handed to it. *)
Ltac zl := Zify.zify; xlia zchecker.

(* ======== the offsets of this segment ======== *)
Definition P7B_EV0 : Z := 7364.      (* ex_value's listing offset (LENGTH) *)
Definition P7B_WSB : Z := 0x71c.     (* A' 0x839c0, the ws loop's first slot (EV_WSLOOPS' second entry) *)
Definition P7B_WSE : Z := 0x768.     (* A' 0x83a0c, its exit *)

Lemma p7b_wsloop_in : In (P7B_WSB, P7B_WSE) EV_WSLOOPS.
Proof. unfold EV_WSLOOPS, P7B_WSB, P7B_WSE. right. left. reflexivity. Qed.

Lemma p7b_sigma : SIGMA AS_ex_value = BASE + P7B_EV0.
Proof. vm_compute. reflexivity. Qed.

Lemma p7b_pc_eq : forall off, SIGMA AS_ex_value + off = BASE + (P7B_EV0 + off).
Proof. intros off. rewrite p7b_sigma. zl. Qed.

Lemma p7b_cfg_eq : forall fxc regs off mem md n, BASE + n = SIGMA AS_ex_value + off ->
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + n)) mem (YK11.seg_rom SEGS)) md =
  ev_cfg (L := A_prog_listing) (PA := PA) fxc regs off mem md.
Proof. intros fxc regs off mem md n H. unfold ev_cfg, ev_pc. rewrite H. reflexivity. Qed.

Ltac p7b_cfg_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 (pa_val A_TEXT + ?n)) ?m _; cfg_model := ?d |} _ =>
    rewrite (p7b_cfg_eq _ r off m d n ltac:(rewrite p7b_pc_eq; vm_compute; reflexivity)) end.

(* ======== small byte / env helpers (S8aDisp.v at 85194de74e52, renamed) ======== *)
Lemma p7b_denot_atom : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia.
rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

Lemma p7b_denot_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hvc. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma p7b_chunk8_val : forall E (m : word -> option byte) base off e v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (base + off) 8 v.
Proof.
intros E m base off e v HC He Hv k Hk. destruct (HC (Z.of_nat k) ltac:(cbn; zl)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite He in Hb. injection Hb as <-. rewrite Hm. f_equal.
apply bv_eq. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). change (8 * Z.of_nat 8) with 64.
rewrite (Z.mod_small v (2 ^ 64)) by zl. rewrite Z.mod_mod by zl. reflexivity.
Qed.

Lemma p7b_vm1_of_aview : forall (H : word -> bool) mem z,
  aview SEGS H mem z = Some 0 -> val_mem SEGS (mrestrict H mem) z 1 0.
Proof.
intros H mem z E k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte SEGS (mrestrict H mem) z) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma p7b_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr). rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma p7b_vm_eq : forall (m m' : word -> option byte) a n v,
  (forall x, m' x = m x) -> val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v H Hv k Hk. unfold mbyte. rewrite H. exact (Hv k Hk). Qed.

Lemma p7b_frame_slot : forall E rs (m m' : word -> option byte) lo hi, frame_of E rs m m' ->
  (forall z, in_wrange E rs z -> lo <= z < hi) -> forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros H. exact (Hx (Hw _ H)). Qed.

Lemma p7b_mb_kept : forall (W : world SEGS) mem mem' (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ P z -> mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z.
Proof.
intros W mem mem' P H z Hz Hn. unfold mbyte. rewrite H; [reflexivity|].
rewrite unsigned_lit_small by zl. exact Hn.
Qed.

Lemma p7b_av_of_mb : forall (H : word -> bool) (m m' : word -> option byte) z,
  mbyte SEGS (mrestrict H m') z = mbyte SEGS (mrestrict H m) z -> aview SEGS H m' z = aview SEGS H m z.
Proof. intros H m m' z E. unfold aview. rewrite E. reflexivity. Qed.

Lemma p7b_vm_kept : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.

Lemma p7b_skipn_cons : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
intros x. induction x as [|b x IH]; intros i Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|].
cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.

Lemma p7b_regs_kept : forall a regs regs', ev_regs a regs ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) -> ev_regs a regs'.
Proof.
intros a regs regs' (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) HK.
unfold ev_regs. rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.

Lemma p7b_bne_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof.
intros E n v z H Hv Hz. rewrite branch_ne_U, U_SLit, (U_atom E n v H) by zl.
rewrite zcanon_id by (unfold M64; zl). reflexivity.
Qed.

(* ======== bounds and shadow transports (S8aItemsWalk.v FRAME KIT at ebf0edf14b4, renamed) ======== *)
Lemma p7b_sh_lt : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x /\ shadow_addr x + 8 <= alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as ((C1 & _) & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma p7b_ra_kept : forall (rd rd' : Z -> option Z) x n, 0 <= x -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Hx Hxn E H. apply (range_addressable_agree rd rd' SHADOW_OFF x n); [|exact H].
intros y Hy. destruct (p7b_sh_lt y ltac:(lia)) as [A0 A1]. apply E.
unfold shadow_of_addr. unfold shadow_addr in A0, A1. lia.
Qed.

(* prhex_tree's shadow-hull conjunct (walkkit b77223726823), kept the same way (S8aItemsWalk.v evf_hull, renamed) *)
Lemma p7b_hull_kept : forall (rd rd' : Z -> option Z) x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Hx Hn Hxn E H s Hs.
destruct (p7b_sh_lt x ltac:(lia)) as [A0 _]. destruct (p7b_sh_lt (x + n - 1) ltac:(lia)) as [_ A1].
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as D0.
pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M0.
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)) as M1.
rewrite E by lia. exact (H s Hs).
Qed.

(* ======== the reader's tree: pj_nodeR is kept when its node bytes and its lblk blocks are
   (S8aItemsWalk.v evf_vm .. evf_nodeR_frame at ebf0edf14b4, renamed) ======== *)
Lemma p7b_vm : forall (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> mbyte SEGS m' z = mbyte SEGS m z) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H k Hk. rewrite E by lia. exact (H k Hk). Qed.

Lemma p7b_garr8 : forall (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' a l E H j Hj. destruct (H j Hj) as [Hv Hb]. split; [|exact Hb].
apply (p7b_vm m m'); [|exact Hv]. intros z Hz. apply E. lia.
Qed.

Lemma p7b_hdr : forall (m m' : word -> option byte) p ty num str kids keys n cap, mem_grows m m' ->
  (forall z, p <= z < p + 56 -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_hdrR SEGS m p ty num str kids keys n cap -> PRH_Reader.pj_hdrR SEGS m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap G E
  ((Hal & Hrw) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)).
split; [split; [exact Hal|intros x Hx; exact (writable_at_grows SEGS m m' x G (Hrw x Hx))]|].
split; [split; [exact T0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact T1]]|].
split; [split; [exact N0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact N1]]|].
split; [split; [exact S0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact S1]]|].
split; [split; [exact K0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact K1]]|].
split; [split; [exact Y0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact Y1]]|].
split; [split; [exact C0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact C1]]|].
split; [exact P0|apply (p7b_vm m m'); [intros z Hz; apply E; lia|exact P1]].
Qed.

Lemma p7b_cstr : forall (m m' : word -> option byte) lblk a k s,
  (forall z, a <= z < a + k -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_cstrR SEGS m lblk a k s -> PRH_Reader.pj_cstrR SEGS m' lblk a k s.
Proof.
intros m m' lblk a k s E (Hl & Hk & Hf & Hc & Hg). split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
split; [exact Hc|].
apply (p7b_garr8 m m'); [|exact Hg]. intros z Hz. apply E. rewrite length_app in Hz. cbn [length] in Hz. lia.
Qed.

Definition p7b_nodeP (m m' : word -> option byte) (lblk : Z -> Z -> Prop) (t : PjTree.jv) : Prop :=
  forall p D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
  (forall z, (p <= z < p + 56 \/ exists b k, In (b, k) D /\ lblk b k /\ b <= z < b + k) ->
     mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_nodeR SEGS m' lblk p t D.

Lemma p7b_items_frame : forall (m m' : word -> option byte) lblk (items : list PjTree.jv),
  Forall (p7b_nodeP m m' lblk) items ->
  forall a Di, PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m lblk) a items Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length items) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m' lblk) a items Di.
Proof.
intros m m' lblk items IH. induction IH as [|u r Hu Hr IHr]; intros a Di H E1 E2;
  cbn [PRH_Reader.pj_itemsR] in H |- *.
- exact H.
- destruct H as (D1 & D2 & ED & H1 & H2). exists D1, D2. split; [exact ED|]. split.
  + apply (Hu a D1 H1). intros z [Hz|(b & k & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E2. exists b, k. split; [rewrite ED; apply in_or_app; left; exact Hin|]. split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z (b & k & Hin & Hl & Hz). apply E2. exists b, k.
      split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma p7b_mems_frame : forall (m m' : word -> option byte) lblk (members : list (list Z * PjTree.jv)),
  Forall (fun mm => p7b_nodeP m m' lblk (snd mm)) members ->
  forall a ka Di, PRH_Reader.pj_memsR SEGS m lblk (PRH_Reader.pj_nodeR SEGS m lblk) a ka members Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length members) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, ka <= z < ka + 8 * Z.of_nat (length members) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_memsR SEGS m' lblk (PRH_Reader.pj_nodeR SEGS m' lblk) a ka members Di.
Proof.
intros m m' lblk members IH. induction IH as [|mm r Hu Hr IHr]; intros a ka Di H E1 E2 E3.
- cbn [PRH_Reader.pj_memsR] in H |- *. exact H.
- destruct mm as [nm u]. cbn [PRH_Reader.pj_memsR snd] in H, Hu |- *.
  destruct H as (x & k & D1 & D2 & ED & (Hx0 & Hx) & Hc & H1 & H2).
  exists x, k, D1, D2. split; [exact ED|].
  split; [split; [exact Hx0|apply (p7b_vm m m'); [intros z Hz; apply E2; cbn [length]; lia|exact Hx]]|].
  split.
  { apply (p7b_cstr m m'); [|exact Hc]. intros z Hz. apply E3. exists x, k.
    split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz]. }
  split.
  + apply (Hu a D1 H1). intros z [Hz|(b & kk & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E3. exists b, kk. split; [rewrite ED; right; apply in_or_app; left; exact Hin|].
      split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) (ka + 8) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z Hz. apply E2. cbn [length]. lia.
    * intros z (b & kk & Hin & Hl & Hz). apply E3. exists b, kk.
      split; [rewrite ED; right; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma p7b_nodeR_frame : forall (m m' : word -> option byte) lblk, mem_grows m m' -> forall t, p7b_nodeP m m' lblk t.
Proof.
intros m m' lblk G t.
induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; unfold p7b_nodeP; intros p D H E;
  cbn [PRH_Reader.pj_nodeR] in H |- *;
  destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & R);
  (split; [exact ND|]); (split; [exact AP|]);
  exists num, str, kids, keys, n, cap;
  (split; [apply (p7b_hdr m m'); [exact G|intros z Hz; apply E; left; exact Hz|exact HH]|]).
- exact R.
- exact R.
- exact R.
- destruct R as (R1 & R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 5 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (p7b_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 4 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (p7b_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & R5 & Di & ED & HI).
  do 5 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (p7b_items_frame m m' lblk items IH kids Di HI).
  + intros z Hz. apply E. right. destruct R5 as [(Hc0 & _)|(Hc0 & Hl)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & Di & ED & HM).
  do 4 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (p7b_mems_frame m m' lblk members IH kids keys Di HM).
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists keys, (8 * cap). split; [|split; [exact Hl2|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

(* ======== the pure model of this segment ======== *)

(* the key's name is read exactly when the first non-blank byte after the string is ':' *)
Lemma p7b_name_none : forall (x : list Z) (i i1 i' : nat) nm o,
  skipn i' x = PjGrammar.skip (skipn i1 x) ->
  ev_run0 (PjGrammar.jr_name o (skipn i x)) =
    (match PjGrammar.skip (skipn i1 x) with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end) ->
  ((length x <= i')%nat \/ nth i' x 0 <> 58) ->
  ev_run0 (PjGrammar.jr_name o (skipn i x)) = None.
Proof.
intros x i i1 i' nm o Hsk Hnm Hbad. rewrite Hnm, <- Hsk.
destruct (Nat.le_gt_cases (length x) i') as [Hge|Hlt].
- rewrite skipn_all2 by exact Hge. reflexivity.
- rewrite (p7b_skipn_cons x i' Hlt).
  destruct Hbad as [Hbad|Hbad]; [lia|].
  replace (nth i' x 0 =? 58) with false by (symmetry; apply Z.eqb_neq; exact Hbad). reflexivity.
Qed.

Lemma p7b_name_some : forall (x : list Z) (i i1 i' : nat) nm o,
  skipn i' x = PjGrammar.skip (skipn i1 x) ->
  ev_run0 (PjGrammar.jr_name o (skipn i x)) =
    (match PjGrammar.skip (skipn i1 x) with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end) ->
  (i' < length x)%nat -> nth i' x 0 = 58 ->
  ev_run0 (PjGrammar.jr_name o (skipn i x)) = Some (nm, skipn (S i') x).
Proof.
intros x i i1 i' nm o Hsk Hnm Hlt Hc. rewrite Hnm, <- Hsk, (p7b_skipn_cons x i' Hlt), Hc.
reflexivity.
Qed.

Lemma p7b_L_none : forall d o n cap acc y,
  ev_run0 (PjGrammar.jr_name o y) = None -> ev_L d o n cap acc y = None.
Proof. intros d o n cap acc y H. rewrite evp_L_step, H. reflexivity. Qed.

Lemma p7b_L_some : forall d o n cap acc y nm y1, ev_run0 (PjGrammar.jr_name o y) = Some (nm, y1) ->
  ev_L d o n cap acc y =
  ev_K d o n (ev_cap n cap) acc nm (ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod d y1)).
Proof. intros d o n cap acc y nm y1 H. rewrite evp_L_step, H. reflexivity. Qed.

Lemma p7b_V_value : forall d y, 0 <= d ->
  prhex_V (d + 1) y = ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod (Nat.succ (Z.to_nat d)) y).
Proof.
intros d y Hd. unfold prhex_V, ev_run0.
replace (Z.to_nat (d + 1)) with (Nat.succ (Z.to_nat d)); [reflexivity|].
rewrite Z2Nat.inj_add by zl. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r. reflexivity.
Qed.

(* ======== arithmetic of the activation at a cut of this segment ========
   The text's ceiling is ev_pre's src_rd's own, x0 + len <= alloc_ceiling (PRH_Base.v src_rd, SRC-CEIL: the cut
   dropped the old `+ 8`, which bounded no access). No reader below needs more: a text byte is read at x0 + i, i < len. *)
Lemma p7b_arith : forall a ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  alloc_ceiling <= ea_S1 a /\ ea_S1 a + 152 <= ea_q a /\ ea_q a + 40 <= 2 ^ 47 /\
  ea_S1 a mod 32 = 0 /\ ea_q a mod 8 = 0 /\
  4096 <= ea_x0 a /\ ea_x0 a + ea_len a <= alloc_ceiling /\
  ly_stk_lo ly <= ea_q a /\ ea_q a + 40 <= ly_stk_hi ly /\
  ea_len a <= 3 * 2 ^ 20 /\ 0 <= ea_dep a <= 32 /\ 0 <= ea_len a.
Proof.
intros a ly S Hp W mem md k p dep dl HP HM.
pose proof (BNDS a HP) as (BC & BS1 & BS2 & BA1 & BQ & BQD & B47 & BA2 & BD0).
pose proof (ev_q_stack B ARx SK a ly S Hp W mem md k p dep dl HP HM) as [HQL HQH].
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _ & HLEN & _ & HDEP & _).
destruct HSRC as (_ & HX0 & HXC & _).
unfold ea_len in *.
pose proof (Zle_0_nat (length (ea_x a))) as HL0.
split; [zl|]. split; [zl|]. split; [zl|]. split; [exact BA1|]. split; [exact BA2|].
split; [zl|]. split; [zl|]. split; [exact HQL|]. split; [exact HQH|].
split; [zl|]. split; [zl|]. zl.
Qed.

(* the shadow byte of a real-stack address reads 0 *)
Lemma p7b_zsh : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (shadow_addr a) = Some 0.
Proof.
intros ly S Hp W mem md a HAR Ha.
exact (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md a HAR Ha).
Qed.

(* shadow (q + 8) is shadow q + 1 when q is 8-aligned *)
Lemma p7b_sh8 : forall q, q mod 8 = 0 -> shadow_addr (q + 8) = shadow_addr q + 1.
Proof.
intros q Hq. unfold shadow_addr. replace (q + 8) with (q + 1 * 8) by lia.
rewrite Z.div_add by lia. lia.
Qed.

(* the ledger's blocks lie in [4096, alloc_ceiling) *)
Lemma p7b_lamb : forall ly S Hp W mem md Lam peak cnt fail ran most own b mm,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, mm) Lam -> 4096 <= b /\ b + mm <= alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b mm HAR HLED Hin.
destruct HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (b, mm) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (mm + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
assert (Hrq : mm + cf_head <= req_size (mm + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (mm + cf_head) 0); lia).
lia.
Qed.

(* the activation's own fake frame lies below alloc_ceiling *)
Lemma p7b_fr_bounds : forall (a : ev_act) ly S Hp W mem md k p dep dl,
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl -> 4096 <= ea_fr a /\ ea_fr a + 128 <= alloc_ceiling.
Proof.
intros a ly S Hp W mem md k p dep dl HMID.
destruct HMID as (HJ & _).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFR & _).
assert (HIN : In (1, ea_pos a) (frames S)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN) as (F0 & F1 & _).
assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a).
{ destruct HLY as (_ & _ & _ & _ & _ & ELF & _). unfold ea_fr, frame_addr. rewrite ELF. reflexivity. }
rewrite EF in F0, F1. change (fs_frame_bytes 1) with 128 in F1. split; [exact F0|exact F1].
Qed.

(* ======== the memory facts a stretch of this segment keeps ========
   Every stretch writes only in->p, i.e. [q, q + 8); the spills, the tree and the kid live below alloc_ceiling. *)
Lemma p7b_spills_keep : forall (a : ev_act) W (mem mem' : word -> option byte) o v',
  alloc_ceiling <= ea_S1 a -> ea_S1 a + 152 <= ea_q a -> ea_q a + 40 <= 2 ^ 47 ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
     mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) ->
  ev_spills a W mem o v' -> ev_spills a W mem' o v'.
Proof.
intros a W mem mem' o v' HS1 HSQ HQ47 HK HSP.
pose proof asan_consts as ((C1 & _) & _).
destruct HSP as (V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88).
unfold ev_spills. cbv zeta.
repeat (split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|eassumption]|]).
eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|eassumption].
Qed.

Lemma p7b_kid_keep : forall (a : ev_act) ly S Hp W mem md mem' md' k p dep dl o n kid,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ARx ly S Hp W mem' md' ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
     mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) ->
  ev_kid_ok a ly S W mem o n kid -> ev_kid_ok a ly S W mem' o n kid.
Proof.
intros a ly S Hp W mem md mem' md' k p dep dl o n kid HP HM HAR' GROW HK HKID.
pose proof (p7b_arith a ly S Hp W mem md k p dep dl HP HM) as (AS1 & ASQ & AQ47 & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as ((C1 & _) & _).
pose proof HM as (HJ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & _).
assert (HKA : forall s, 0 <= s < alloc_ceiling -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply p7b_av_of_mb. apply HK; zl. }
destruct HKID as [HZ | (Hv & Hn & H4096 & Hceil & Hamr & Dk & HT & Hinc & HFOOT)]; [left; exact HZ|].
right. split; [exact Hv|]. split; [exact Hn|]. split; [exact H4096|]. split; [exact Hceil|].
split; [exact Hamr|]. exists Dk.
destruct HT as (HN & HH & HRA & HHV).
split; [|split; [exact Hinc|exact HFOOT]].
split; [|split; [exact HH|split; [apply (p7b_ra_kept (aview SEGS (w_H W) mem)); [zl|zl|exact HKA|exact HRA] |
  apply (p7b_hull_kept (aview SEGS (w_H W) mem)); [zl|zl|zl|exact HKA|exact HHV]]]].
apply (p7b_nodeR_frame (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin (ea_Lam a)) GROW _ _ _ HN).
intros z [Hz | (b & kk & Hin & Hl & Hz)].
- apply HK; zl.
- destruct (p7b_lamb ly S Hp W mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) b kk HAR HLED Hl).
  apply HK; zl.
Qed.

(* presence inside the only write window plus equality outside it is mem_grows *)
Lemma p7b_grows_mid : forall (W : world SEGS) (m m' : word -> option byte) lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  (forall z, lo <= z < hi -> apresent (w_H W) m' z) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m').
Proof.
intros W m m' lo hi HE HP x Hx.
destruct (Z.le_gt_cases lo (bv_unsigned x)) as [H1|H1];
  [destruct (Z.lt_ge_cases (bv_unsigned x) hi) as [H2|H2]|].
- destruct (HP (bv_unsigned x) ltac:(zl)) as (Hh & b & Hb).
  rewrite Z_to_bv_bv_unsigned in Hh, Hb. unfold mrestrict. rewrite Hh, Hb. discriminate.
- rewrite HE by zl. exact Hx.
- rewrite HE by zl. exact Hx.
Qed.

(* ======== the cut at the ws loop's exit, A' 0x83a0c (internal to this segment) ======== *)
Definition p7b_at_wse (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (n : nat) (kid dl2 : Z) (i' : nat) : Prop :=
  let v' := ev_v' (ea_v a) true (ea_t a) in
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl2 /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 123 /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  getr regs 23 = w64 (if kid =? 0 then 1 else 0) /\
  getr regs 11 = w64 (ea_x0 a + ea_len a) /\
  ev_spills a W mem true v' /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 v' /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  ev_kid_ok a ly S W mem true n kid /\ (i' <= length (ea_x a))%nat.

(* the five memory facts a stretch of this segment carries, transported in one step *)
Lemma p7b_keep5 : forall (a : ev_act) ly S Hp W mem md mem' md' k p dep dl n kid,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ARx ly S Hp W mem' md' ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
     mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) ->
  ev_spills a W mem true (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n) ->
  ev_kid_ok a ly S W mem true n kid ->
  ev_spills a W mem' true (ev_v' (ea_v a) true (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 96) 8 kid /\
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 104) 8 (ev_v' (ea_v a) true (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 120) 8 (Z.of_nat n) /\
  ev_kid_ok a ly S W mem' true n kid.
Proof.
intros a ly S Hp W mem md mem' md' k p dep dl n kid HP HM HAR' GROW HK HSP M96 M104 M120 HKID.
pose proof (p7b_arith a ly S Hp W mem md k p dep dl HP HM) as (AS1 & ASQ & AQ47 & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as ((C1 & _) & _).
split; [exact (p7b_spills_keep a W mem mem' true _ AS1 ASQ AQ47 HK HSP)|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact M96]|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact M104]|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact M120]|].
exact (p7b_kid_keep a ly S Hp W mem md mem' md' k p dep dl true n kid HP HM HAR' GROW HK HKID).
Qed.

(* ======== the symbolic states (closed terms: the engine vm_computes from them) ========
   P7B_QLO is alloc_ceiling's closed floor (asan_consts): a Context field cannot be vm_computed. *)
Definition P7B_QLO : Z := 0x7fff7f800000.
Definition p7b_Bx : sv := SOff 24 0.
Definition p7b_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition p7b_E (regs : bvmap 5 word) (p c fr kid : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs [w64 p; w64 c; w64 fr; w64 kid]).
Definition p7b_ms (fxc : YK11.FPState) (regs : bvmap 5 word) (mem : word -> option byte) (off : Z) : machine_state :=
  @YK11.mkst fxc regs (Z_to_bv 64 (BASE + (P7B_EV0 + off))) mem (YK11.seg_rom SEGS).

Lemma p7b_ew : forall regs p c fr kid (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < A_TEXT)%nat ->
  ew (p7b_E regs p c fr kid) nn = getr regs r.
Proof.
intros regs p c fr kid nn r Hn H32. unfold p7b_E. rewrite Eimg_low by exact H32.
exact (ew_Ereg_nat regs _ nn r Hn).
Qed.

Lemma p7b_ex : forall regs p c fr kid (j : nat), (32 + j < A_TEXT)%nat ->
  ew (p7b_E regs p c fr kid) (32 + j) = nth j [w64 p; w64 c; w64 fr; w64 kid] (Z_to_bv 64 0).
Proof.
intros regs p c fr kid j Hj. unfold p7b_E. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra.
Qed.

Lemma p7b_env_agree : forall regs p c fr kid,
  env_agree 32 (Ereg regs [w64 p; w64 c; w64 fr; w64 kid]) (p7b_E regs p c fr kid).
Proof.
intros regs p c fr kid. unfold p7b_E.
split; [intros nn Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Ltac p7b_uat n v Hn H :=
  match type of H with context [U ?E' (SOff n 0)] =>
    let Hx := fresh "Hx" in assert (Hx : ew E' n = w64 v) by (cbn [ew ewset Nat.eqb]; exact Hn);
    rewrite (U_atom E' n v Hx) in H by zl; clear Hx end.

(* C_KEY A' 0x839a0: the two shadow bytes of `struct ex`, in->p (atom 32) and in->end (atom 33); nothing writable *)
Definition p7b_ssA : sstate :=
  mkSS (P7B_EV0 + EV_KEY) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 16 0 0
        [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))];
      YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ]
    None (mkFacts [ (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF P7B_QLO (2 ^ 47) 3);
                    (20%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
                    (26%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
                    (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 4096 (2 ^ 47) 0) ] [] []).

Lemma p7b_stA : forall (a : ev_act) (fxc : YK11.FPState) (W : world SEGS) regs mem (E : env)
    (ly : alayout) (S : astate) (Hp : list Z) md k (i1 : nat) dep dl,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) dep dl ->
  ev_regs a regs -> getr regs 20 = w64 (shadow_addr (ea_q a + 8)) ->
  (i1 <= length (ea_x a))%nat ->
  regs_ok E sr_atoms regs ->
  ew E 19 = w64 (ea_q a) -> ew E 20 = w64 (shadow_addr (ea_q a + 8)) ->
  ew E 24 = w64 SHADOW_OFF -> ew E 26 = w64 (shadow_addr (ea_q a)) ->
  ew E 32 = w64 (ea_x0 a + Z.of_nat i1) -> ew E 33 = w64 (ea_x0 a + ea_len a) ->
  st_ok_pi SEGS VAL E p7b_ssA (restrict (w_H W) (p7b_ms fxc regs mem EV_KEY)).
Proof.
intros a fxc W regs mem E ly S Hp md k i1 dep dl HP HM HR R20 Hi1 HRO E19 E20 E24 E26 E32 E33.
pose proof (p7b_arith a ly S Hp W mem md k _ dep dl HP HM) as
  (AS1 & ASQ & AQ47 & AAL1 & AAL2 & AX0 & AXC & AQL & AQH & ALEN & ADEP & AL0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof HM as (HJ & _ & _ & _ & _ & HCUR & _).
pose proof HJ as (HAR & _).
destruct HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
assert (Hi1z : 0 <= Z.of_nat i1 <= ea_len a) by (unfold ea_len; pose proof (Zle_0_nat i1); zl).
assert (Hsh0 : shadow_addr (ea_q a) = SHADOW_OFF + ea_q a / 8) by reflexivity.
assert (HD0 : 0 <= ea_q a / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
assert (Hsh8 : shadow_addr (ea_q a + 8) = shadow_addr (ea_q a) + 1) by (apply p7b_sh8; exact AAL2).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; apply unsigned_lit_small; zl).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr (ea_q a + 8))
  by (rewrite E20; apply unsigned_lit_small; rewrite Hsh8, Hsh0; unfold SHADOW_OFF; zl).
assert (U26 : bv_unsigned (ew E 26) = shadow_addr (ea_q a))
  by (rewrite E26; apply unsigned_lit_small; rewrite Hsh0; unfold SHADOW_OFF; zl).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; zl).
assert (U32 : bv_unsigned (ew E 32) = ea_x0 a + Z.of_nat i1) by (rewrite E32; apply unsigned_lit_small; zl).
assert (U33 : bv_unsigned (ew E 33) = ea_x0 a + ea_len a) by (rewrite E33; apply unsigned_lit_small; zl).
assert (Z8 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a + 8)) 1 0).
{ apply p7b_vm1_of_aview. apply (p7b_zsh ly S Hp W mem md _ HAR). zl. }
assert (Z0 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a)) 1 0).
{ apply p7b_vm1_of_aview. apply (p7b_zsh ly S Hp W mem md _ HAR). zl. }
unfold p7b_ssA, p7b_ms. rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (fx := fxc)).
- exact HRO.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U19. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_q a) 0 8 (SOff 32 0) (ea_x0 a + Z.of_nat i1));
        [apply p7b_denot_atom; [exact E32 | zl] | cbn; zl | cbn; zl | rewrite Z.add_0_r; exact Q1].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_q a) 8 8 (SOff 33 0) (ea_x0 a + ea_len a));
        [apply p7b_denot_atom; [exact E33 | zl] | cbn; zl | cbn; zl | exact Q2].
  + rewrite U20, Hsh8, Hsh0. split; [unfold SHADOW_OFF; zl|]. split; [unfold SHADOW_OFF; zl|].
    split; [intros o Ho; zl|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (SHADOW_OFF + ea_q a / 8 + 1) 0 1 (SLit 0) 0);
      [reflexivity | cbn; zl | cbn; zl | rewrite Z.add_0_r, <- Hsh0, <- Hsh8; exact Z8].
  + rewrite U26, Hsh0. split; [unfold SHADOW_OFF; zl|]. split; [unfold SHADOW_OFF; zl|].
    split; [intros o Ho; zl|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (SHADOW_OFF + ea_q a / 8) 0 1 (SLit 0) 0);
      [reflexivity | cbn; zl | cbn; zl | rewrite Z.add_0_r, <- Hsh0; exact Z0].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U19, U20, U26, Hsh8, Hsh0. unfold SHADOW_OFF.
  repeat apply conj; try exact I; right; zl.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U24, U19, U20, U26, U32, U33, Hsh8, Hsh0. unfold SHADOW_OFF, P7B_QLO.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
  repeat apply conj; try exact I; try reflexivity; try assumption; zl.
Qed.

(* A' 0x83a0c, the ws loop's exit, with the text used up: in->p, the shadow of q, the frame and the kid spills;
   nothing writable, no text byte *)
Definition p7b_ssE : sstate :=
  mkSS (P7B_EV0 + P7B_WSE) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 9%nat) 24 104 0 0
        [YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 96 (CVal 8 (SOff 35 0))] ]
    None (mkFacts [ (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF P7B_QLO (2 ^ 47) 3);
                    (9%nat, mkAF P7B_QLO (2 ^ 47) 5);
                    (26%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
                    (32%nat, mkAF 4096 (2 ^ 47) 0) ] [] []).

(* the same with the text byte at in->p (atom 33) and in->p writable: the ':' test and `in->p++` *)
Definition p7b_ssB : sstate :=
  mkSS (P7B_EV0 + P7B_WSE) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 9%nat) 24 104 0 0
        [YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 96 (CVal 8 (SOff 35 0))];
      YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ]
    None (mkFacts [ (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF P7B_QLO (2 ^ 47) 3);
                    (9%nat, mkAF P7B_QLO (2 ^ 47) 5);
                    (26%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
                    (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0) ] [] []).
Definition p7b_SHB : list shent := [mkSHE 32 0 1].

Lemma p7b_stE : forall (a : ev_act) (fxc : YK11.FPState) (W : world SEGS) regs mem (E : env)
    (ly : alayout) (S : astate) (Hp : list Z) md k (i' : nat) dep dl kid,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i') dep dl ->
  (i' <= length (ea_x a))%nat ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 24) 8 (ea_fr a) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid ->
  0 <= kid -> kid + 56 <= alloc_ceiling ->
  regs_ok E sr_atoms regs ->
  ew E 9 = w64 (ea_S1 a) -> ew E 19 = w64 (ea_q a) ->
  ew E 24 = w64 SHADOW_OFF -> ew E 26 = w64 (shadow_addr (ea_q a)) ->
  ew E 32 = w64 (ea_x0 a + Z.of_nat i') -> ew E 34 = w64 (ea_fr a) -> ew E 35 = w64 kid ->
  st_ok_pi SEGS VAL E p7b_ssE (restrict (w_H W) (p7b_ms fxc regs mem P7B_WSE)).
Proof.
intros a fxc W regs mem E ly S Hp md k i' dep dl kid HP HM Hi' M24 M96 HK0 HKC HRO E9 E19 E24 E26 E32 E34 E35.
pose proof (p7b_arith a ly S Hp W mem md k _ dep dl HP HM) as
  (AS1 & ASQ & AQ47 & AAL1 & AAL2 & AX0 & AXC & AQL & AQH & ALEN & ADEP & AL0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof HM as (HJ & _ & _ & _ & _ & HCUR & _).
pose proof HJ as (HAR & _).
destruct HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof (p7b_fr_bounds a ly S Hp W mem md k _ dep dl HM) as [F0 F1].
assert (Hi'z : 0 <= Z.of_nat i' <= ea_len a) by (unfold ea_len; pose proof (Zle_0_nat i'); zl).
assert (Hsh0 : shadow_addr (ea_q a) = SHADOW_OFF + ea_q a / 8) by reflexivity.
assert (HD0 : 0 <= ea_q a / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite E9; apply unsigned_lit_small; zl).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; apply unsigned_lit_small; zl).
assert (U26 : bv_unsigned (ew E 26) = shadow_addr (ea_q a))
  by (rewrite E26; apply unsigned_lit_small; rewrite Hsh0; unfold SHADOW_OFF; zl).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; zl).
assert (U32 : bv_unsigned (ew E 32) = ea_x0 a + Z.of_nat i') by (rewrite E32; apply unsigned_lit_small; zl).
assert (Z0 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a)) 1 0).
{ apply p7b_vm1_of_aview. apply (p7b_zsh ly S Hp W mem md _ HAR). zl. }
unfold p7b_ssE, p7b_ms. rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (fx := fxc)).
- exact HRO.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U19. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_q a) 0 8 (SOff 32 0) (ea_x0 a + Z.of_nat i'));
      [apply p7b_denot_atom; [exact E32 | zl] | cbn; zl | cbn; zl | rewrite Z.add_0_r; exact Q1].
  + rewrite U26, Hsh0. split; [unfold SHADOW_OFF; zl|]. split; [unfold SHADOW_OFF; zl|].
    split; [intros o Ho; zl|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (SHADOW_OFF + ea_q a / 8) 0 1 (SLit 0) 0);
      [reflexivity | cbn; zl | cbn; zl | rewrite Z.add_0_r, <- Hsh0; exact Z0].
  + rewrite U9. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_S1 a) 24 8 (SOff 34 0) (ea_fr a));
        [apply p7b_denot_atom; [exact E34 | zl] | cbn; zl | cbn; zl | exact M24].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_S1 a) 96 8 (SOff 35 0) kid);
        [apply p7b_denot_atom; [exact E35 | zl] | cbn; zl | cbn; zl | exact M96].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U19, U26, U9, Hsh0. unfold SHADOW_OFF.
  repeat apply conj; try exact I; first [right; zl | left; zl].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U24, U19, U9, U26, U32, Hsh0. unfold SHADOW_OFF, P7B_QLO.
  change (2 ^ 3) with 8. change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
  repeat apply conj; try exact I; try reflexivity; try assumption; zl.
Qed.

Lemma p7b_stB : forall (a : ev_act) (fxc : YK11.FPState) (W : world SEGS) regs mem (E : env)
    (ly : alayout) (S : astate) (Hp : list Z) md k (i' : nat) dep dl kid c,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i') dep dl ->
  (i' < length (ea_x a))%nat ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 24) 8 (ea_fr a) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid ->
  0 <= kid -> kid + 56 <= alloc_ceiling ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_x0 a + Z.of_nat i') 1 c -> 0 <= c < 256 ->
  (ea_x0 a + Z.of_nat i' + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= ea_x0 a + Z.of_nat i') ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_x0 a) (ea_len a) ->
  regs_ok E sr_atoms regs ->
  ew E 9 = w64 (ea_S1 a) -> ew E 19 = w64 (ea_q a) ->
  ew E 24 = w64 SHADOW_OFF -> ew E 26 = w64 (shadow_addr (ea_q a)) ->
  ew E 32 = w64 (ea_x0 a + Z.of_nat i') -> ew E 33 = w64 c ->
  ew E 34 = w64 (ea_fr a) -> ew E 35 = w64 kid ->
  st_ok_pi SEGS VAL E p7b_ssB (restrict (w_H W) (p7b_ms fxc regs mem P7B_WSE)) /\
  sh_ok SEGS p7b_Bx p7b_SHB E (mrestrict (w_H W) mem).
Proof.
intros a fxc W regs mem E ly S Hp md k i' dep dl kid c HP HM Hi' M24 M96 HK0 HKC MC HC HAPP HRA
  HRO E9 E19 E24 E26 E32 E33 E34 E35.
pose proof (p7b_arith a ly S Hp W mem md k _ dep dl HP HM) as
  (AS1 & ASQ & AQ47 & AAL1 & AAL2 & AX0 & AXC & AQL & AQH & ALEN & ADEP & AL0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (BNDS a HP) as (BC & BS1 & BS2 & BA1 & BQ & BQD & B47 & BA2 & BD0).
pose proof HM as (HJ & _ & _ & _ & _ & HCUR & _).
pose proof HJ as (HAR & _).
destruct HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof (p7b_fr_bounds a ly S Hp W mem md k _ dep dl HM) as [F0 F1].
assert (Hi'z : 0 <= Z.of_nat i' < ea_len a) by (unfold ea_len; pose proof (Zle_0_nat i'); zl).
assert (Hsh0 : shadow_addr (ea_q a) = SHADOW_OFF + ea_q a / 8) by reflexivity.
assert (HD0 : 0 <= ea_q a / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite E9; apply unsigned_lit_small; zl).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; apply unsigned_lit_small; zl).
assert (U26 : bv_unsigned (ew E 26) = shadow_addr (ea_q a))
  by (rewrite E26; apply unsigned_lit_small; rewrite Hsh0; unfold SHADOW_OFF; zl).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; zl).
assert (U32 : bv_unsigned (ew E 32) = ea_x0 a + Z.of_nat i') by (rewrite E32; apply unsigned_lit_small; zl).
assert (Z0 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a)) 1 0).
{ apply p7b_vm1_of_aview. apply (p7b_zsh ly S Hp W mem md _ HAR). zl. }
split.
{ unfold p7b_ssB, p7b_ms. rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (fx := fxc)).
  - exact HRO.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [zl|]. split; [zl|].
      split; [intros o Ho; apply (apresent_writable SEGS); destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _); apply Hpres; zl|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_q a) 0 8 (SOff 32 0) (ea_x0 a + Z.of_nat i'));
        [apply p7b_denot_atom; [exact E32 | zl] | cbn; zl | cbn; zl | rewrite Z.add_0_r; exact Q1].
    + rewrite U26, Hsh0. split; [unfold SHADOW_OFF; zl|]. split; [unfold SHADOW_OFF; zl|].
      split; [intros o Ho; zl|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (SHADOW_OFF + ea_q a / 8) 0 1 (SLit 0) 0);
        [reflexivity | cbn; zl | cbn; zl | rewrite Z.add_0_r, <- Hsh0; exact Z0].
    + rewrite U9. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_S1 a) 24 8 (SOff 34 0) (ea_fr a));
          [apply p7b_denot_atom; [exact E34 | zl] | cbn; zl | cbn; zl | exact M24].
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_S1 a) 96 8 (SOff 35 0) kid);
          [apply p7b_denot_atom; [exact E35 | zl] | cbn; zl | cbn; zl | exact M96].
    + rewrite U32. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) (ea_x0 a + Z.of_nat i') 0 1 (SOff 33 0) c);
        [apply p7b_denot_atom; [exact E33 | zl] | cbn; zl | cbn; zl | rewrite Z.add_0_r; exact MC].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U26, U9, U32, Hsh0. unfold SHADOW_OFF in *.
    repeat apply conj; try exact I; destruct HAPP as [HA|HA]; first [right; zl | left; zl].
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U24, U19, U9, U26, U32, Hsh0. unfold SHADOW_OFF, P7B_QLO.
    assert (E33u : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; zl).
    rewrite E33u.
    change (2 ^ 3) with 8. change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
    repeat apply conj; try exact I; try reflexivity; try assumption; zl. }
unfold sh_ok, p7b_SHB, p7b_Bx. apply Forall_cons; [|apply Forall_nil]. split.
- cbn [she_m she_lo she_hi]. rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl).
  rewrite (U_atom E 32 _ E32) by zl.
  apply (range_addressable_sub _ _ (ea_x0 a) (ea_len a)); [exact HRA | zl | zl].
- intros z Hz. cbn [she_m she_lo she_hi] in Hz.
  rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl).
  rewrite (U_atom E 32 _ E32) in Hz by zl.
  change (Z.min 0 1) with 0 in Hz. change (Z.max 0 1) with 1 in Hz.
  unfold SHADOW_OFF in *. destruct HAPP as [HA|HA]; zl.
Qed.

(* ======== builders for the three posts (so a walk never has to name the engine's memory) ======== *)
Lemma p7b_mb_of_eq : forall (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall z, mbyte SEGS m' z = mbyte SEGS m z.
Proof. intros m m' H z. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma p7b_grows_of_eq : forall (m m' : word -> option byte), (forall x, m' x = m x) -> mem_grows m m'.
Proof. intros m m' H x Hx. rewrite H. exact Hx. Qed.

(* the cursor's other four cells are outside [q, q + 8) *)
Lemma p7b_cur_of : forall (a : ev_act) ly S Hp W mem md mem' k p dep dl p',
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
     mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 p' ->
  prhex_cur W mem' (ea_q a) p' (ea_x0 a + ea_len a) dep (ea_scr a) dl.
Proof.
intros a ly S Hp W mem md mem' k p dep dl p' HP HM HK HQ0.
pose proof (p7b_arith a ly S Hp W mem md k p dep dl HP HM) as
  (AS1 & ASQ & AQ47 & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as ((C1 & _) & _).
pose proof HM as (_ & _ & _ & _ & _ & (Q1 & Q2 & Q3 & Q4 & Q5) & _).
unfold prhex_cur. split; [exact HQ0|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact Q2]|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact Q3]|].
split; [eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact Q4]|].
eapply p7b_vm_kept; [intros kk Hk; apply HK; zl|exact Q5].
Qed.

Lemma p7b_wse_of : forall (a : ev_act) ly S Hp W regs mem md k mem' md' regs' n kid dl2 (i' : nat) p0,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat i') ->
  ev_regs a regs ->
  (forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv -> getr regs' r = getr regs r) ->
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) -> getr regs 21 = w64 123 ->
  getr regs 22 = w64 EV_WSMASK -> getr regs 27 = w64 32 ->
  getr regs 23 = w64 (if kid =? 0 then 1 else 0) ->
  getr regs' 11 = w64 (ea_x0 a + ea_len a) ->
  ev_spills a W mem true (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n) ->
  ev_kid_ok a ly S W mem true n kid -> (i' <= length (ea_x a))%nat ->
  YAkMemnorm.memnorm SEGS mem' ->
  p7b_at_wse a W regs' mem' md' ly S Hp k n kid dl2 i'.
Proof.
intros a ly S Hp W regs mem md k mem' md' regs' n kid dl2 i' p0 HP HM HJ' HRAW HGR HQ0 HR HK
  R20 R21 R22 R27 R23 N11 HSP M96 M104 M120 HKID Hi' HMN'.
assert (HKB : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z)
  by (apply (p7b_mb_kept W mem mem' (fun z => ea_q a <= z < ea_q a + 8)); exact HRAW).
pose proof HJ' as (HAR' & _).
destruct (p7b_keep5 a ly S Hp W mem md mem' md' k p0 (ea_dep a + 1) dl2 n kid
  HP HM HAR' HGR HKB HSP M96 M104 M120 HKID) as (K1 & K2 & K3 & K4 & K5).
unfold p7b_at_wse. cbv zeta.
split.
{ apply (MIDF a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 mem' md'
    (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl2 (fun z => ea_q a <= z < ea_q a + 8) HP HM HJ');
  [ exact HRAW | exact HGR | intros z Hz; right; left; exact Hz
  | exact (p7b_cur_of a ly S Hp W mem md mem' k p0 (ea_dep a + 1) dl2 _ HP HM HKB HQ0) | exact HMN' ]. }
split; [apply (p7b_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact R20|].
split; [rewrite (HK 21%bv) by (cbv; tauto); exact R21|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact R22|].
split; [rewrite (HK 27%bv) by (cbv; tauto); exact R27|].
split; [rewrite (HK 23%bv) by (cbv; tauto); exact R23|].
split; [exact N11|].
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [exact K5|exact Hi'].
Qed.

Lemma p7b_exit_of : forall (a : ev_act) ly S Hp W regs mem md k mem' md' regs' (i' : nat) dl2 p0,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat i') ->
  ev_regs a regs ->
  (forall r, In r [2;3;4;8;9;18;19;24;25;26]%bv -> getr regs' r = getr regs r) ->
  getr regs' 22 = w64 (ea_fr a) -> getr regs' 27 = w64 (-1) ->
  (dl2 = 0 \/ dl2 = 1) -> 0 <= ea_dep a <= 31 -> (i' <= length (ea_x a))%nat ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_at_exit B ARx SK a W regs' mem' md' ly S Hp k (-1) (Z.of_nat i') (ea_dep a + 1) dl2.
Proof.
intros a ly S Hp W regs mem md k mem' md' regs' i' dl2 p0 HP HM HJ' HRAW HGR HQ0 HR HK N22 N27 HDL2 HDEP Hi' HNONE HMN'.
assert (HKB : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z)
  by (apply (p7b_mb_kept W mem mem' (fun z => ea_q a <= z < ea_q a + 8)); exact HRAW).
unfold ev_at_exit.
split.
{ apply (MIDF a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 mem' md'
    (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl2 (fun z => ea_q a <= z < ea_q a + 8) HP HM HJ');
  [ exact HRAW | exact HGR | intros z Hz; right; left; exact Hz
  | exact (p7b_cur_of a ly S Hp W mem md mem' k p0 (ea_dep a + 1) dl2 _ HP HM HKB HQ0) | exact HMN' ]. }
split; [apply (p7b_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [exact N22|]. split; [exact N27|].
unfold ev_out. rewrite HNONE. split; [exact HDL2|].
split; [reflexivity|]. unfold ea_len. pose proof (Zle_0_nat i'). split; zl.
Qed.

Lemma p7b_call_of : forall (a : ev_act) ly S Hp W regs mem md k mem' md' regs' n cap1 acc i (iv : nat)
    nm dln kid dl2 p0,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat iv) ->
  ev_regs a regs ->
  (forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv -> getr regs' r = getr regs r) ->
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) -> getr regs 21 = w64 123 ->
  getr regs 22 = w64 EV_WSMASK -> getr regs 27 = w64 32 ->
  getr regs' 11 = w64 kid ->
  ev_spills a W mem true (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 (ev_v' (ea_v a) true (ea_t a)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n) ->
  ev_kid_ok a ly S W mem true n kid ->
  0 <= ea_dep a <= 31 -> (n <= i)%nat -> (i <= iv)%nat -> (iv <= length (ea_x a))%nat -> n = length acc ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_K (Nat.succ (Z.to_nat (ea_dep a))) true n cap1 acc nm (prhex_V (ea_dep a + 1) (skipn iv (ea_x a))) ->
  ev_dl_key a true n nm dln dl2 -> ev_dl (ea_dl a) (ea_v a) true (ea_t a) acc dln ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_at_call B ARx SK a W regs' mem' md' ly S Hp k true n cap1 acc i iv nm dln kid dl2.
Proof.
intros a ly S Hp W regs mem md k mem' md' regs' n cap1 acc i iv nm dln kid dl2 p0
  HP HM HJ' HRAW HGR HQ0 HR HK R20 R21 R22 R27 N11 HSP M96 M104 M120 HKID
  HDEP Hni Hiiv Hiv Hnacc HMOD HDLK HDL HMN'.
assert (HKB : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z)
  by (apply (p7b_mb_kept W mem mem' (fun z => ea_q a <= z < ea_q a + 8)); exact HRAW).
pose proof HJ' as (HAR' & _).
destruct (p7b_keep5 a ly S Hp W mem md mem' md' k p0 (ea_dep a + 1) dl2 n kid
  HP HM HAR' HGR HKB HSP M96 M104 M120 HKID) as (K1 & K2 & K3 & K4 & K5).
unfold ev_at_call. cbv zeta.
split.
{ apply (MIDF a ly S Hp W mem md k p0 (ea_dep a + 1) dl2 mem' md'
    (ea_x0 a + Z.of_nat iv) (ea_dep a + 1) dl2 (fun z => ea_q a <= z < ea_q a + 8) HP HM HJ');
  [ exact HRAW | exact HGR | intros z Hz; right; left; exact Hz
  | exact (p7b_cur_of a ly S Hp W mem md mem' k p0 (ea_dep a + 1) dl2 _ HP HM HKB HQ0) | exact HMN' ]. }
split; [apply (p7b_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact R20|].
split; [rewrite (HK 21%bv) by (cbv; tauto); exact R21|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact R22|].
split; [rewrite (HK 27%bv) by (cbv; tauto); exact R27|].
split; [exact N11|].
split; [exact K1|]. split; [exact K3|]. split; [exact K4|].
split; [exact HDEP|]. split; [exact Hni|]. split; [exact Hiiv|]. split; [exact Hiv|].
split; [exact Hnacc|]. split; [exact HMOD|].
split; [exact K5|]. split; [exact HDLK|exact HDL].
Qed.

(* ======== THE WALK ======== *)
Lemma p7b_ws_kept : forall (regs1 regs2 : bvmap 5 word),
  (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs2 r = getr regs1 r) ->
  forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv -> getr regs2 r = getr regs1 r.
Proof.
intros regs1 regs2 HK r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [apply HK; intros Hx; apply (f_equal bv_unsigned) in Hx; vm_compute in Hx; discriminate Hx|]).
destruct Hr.
Qed.

Ltac p7b_rv N E := rewrite N; first
  [ exact E
  | (cbn [ew ewset Nat.eqb]; exact E)
  | (apply p7b_denot_atom; [first [exact E | cbn [ew ewset Nat.eqb]; exact E] | zl])
  | (rewrite E; apply bv_eq; cbn; zl)
  | (unfold w64; rewrite E; apply bv_eq; cbn; zl) ].

Ltac p7b_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  repeat (apply awr_ok_cons_ro; [cbn; zl|]); apply awr_ok_nil.

(* the write premise of state B: in->p (region 19, s3) is in the caller's window [sp0, sp0 + d) *)
Ltac p7b_awrB E19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat);
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; rewrite unsigned_lit_small by zl; reflexivity
    | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; zl
    | repeat (apply awr_ok_cons_ro; [cbn; zl|]); apply awr_ok_nil ].

(* the write window of state B is [q, q + 8) *)
Ltac p7b_slot E19 :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (cbn [ew ewset Nat.eqb] in Hr; rewrite E19 in Hr; unfold w64 in Hr; rewrite unsigned_lit_small in Hr by zl);
    zl|]);
  destruct Hin.

(* in->p after the stretch, read back from the final state's first region (s3) and its first chunk *)
Ltac p7b_inp HS E19 Ev Hp' :=
  let HMO := fresh "HMO" in let HRO := fresh "HRO" in let HCK := fresh "HCK" in
  pose proof (st_ok_mem_ok _ _ _ _ HS) as HMO; destruct HMO as (_ & HRO & _);
  cbn [ss_mem abs_ss add_cond setpc ms_mem restrict] in HRO;
  apply Forall_inv in HRO; destruct HRO as (_ & _ & _ & HCK); cbn [YP09.r_chunks YP09.r_base base_val] in HCK;
  apply Forall_inv in HCK;
  let Hx := fresh "Hx" in
  match type of HCK with YP09.chunk_ok _ ?Ex _ _ _ =>
    assert (Hx : ew Ex 19 = ew _ 19) by (cbn [ew ewset Nat.eqb]; reflexivity) end;
  rewrite Hx, E19 in HCK; clear Hx; unfold w64 in HCK; rewrite unsigned_lit_small in HCK by zl;
  pose proof (p7b_chunk8_val _ _ _ _ _ _ HCK
    ltac:(apply p7b_denot_off; [cbn [ew ewset Nat.eqb]; exact Ev | zl | zl]) ltac:(zl)) as Hp';
  rewrite Z.add_0_r in Hp'; clear HCK.

(* C_KEY (A' 0x839a0) -> the ws loop's exit (A' 0x83a0c). Report checks 0x839a4 and 0x839ac (the shadow bytes of
   `struct ex`) are NOT TAKEN: the symbolic chunks at s4 and s10 are the byte 0 of alx_zshadow_byte on the real
   stack (ev_q_stack puts [q, q + 40) inside [ly_stk_lo, ly_stk_hi)). The end test 0x839b8 either skips the loop
   (the text is used up) or enters it at 0x839c0, where the Section hypothesis WS takes over. *)
Lemma p7b_head : forall a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_at_key B ARx SK a W regs mem md ly S Hp k true n cap acc i i1 nm dln kid dl2 ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_KEY mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md' (i' : nat),
       c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' P7B_WSE mem' md' /\
       p7b_at_wse a W regs' mem' md' ly S Hp k n kid dl2 i' /\
       (i1 <= i')%nat /\ skipn i' (ea_x a) = PjGrammar.skip (skipn i1 (ea_x a))).
Proof.
intros a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 HP HFX HKEY.
pose proof HKEY as (Ho & HM & HR & R20 & R21 & R22 & R27 & R23 & HSP & M96 & M104 & M120 &
  HDEP & Hni & Hii1 & Hi1 & Hnacc & HMODEL & HNAME & HKID & HDLK & HDL).
pose proof (p7b_arith a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a + 1) dl2 HP HM) as
  (AS1 & ASQ & AQ47 & AAL1 & AAL2 & AX0 & AXC & AQL & AQH & ALEN & ADEP & AL0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (BNDS a HP) as (BC & BS1 & BS2 & BA1 & BQ & BQD & B47 & BA2 & BD0).
pose proof HM as (HJ & _ & _ & _ & _ & HCUR & HSRC & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
assert (Hi1z : 0 <= Z.of_nat i1 <= ea_len a) by (unfold ea_len; pose proof (Zle_0_nat i1); zl).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
set (EA := p7b_E regs (ea_x0 a + Z.of_nat i1) (ea_x0 a + ea_len a) 0 0).
assert (HEI : img_env VAL A_LIM EA) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (ea_x0 a + Z.of_nat i1); w64 (ea_x0 a + ea_len a); w64 0; w64 0]) EA)
  by apply p7b_env_agree.
assert (E19 : ew EA 19 = w64 (ea_q a))
  by (exact (eq_trans (p7b_ew regs _ _ _ _ 19%nat 19%bv eq_refl ltac:(unfold A_TEXT; lia)) R19)).
assert (E20 : ew EA 20 = w64 (shadow_addr (ea_q a + 8)))
  by (exact (eq_trans (p7b_ew regs _ _ _ _ 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)) R20)).
assert (E24 : ew EA 24 = w64 SHADOW_OFF)
  by (exact (eq_trans (p7b_ew regs _ _ _ _ 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)) R24)).
assert (E26 : ew EA 26 = w64 (shadow_addr (ea_q a)))
  by (exact (eq_trans (p7b_ew regs _ _ _ _ 26%nat 26%bv eq_refl ltac:(unfold A_TEXT; lia)) R26)).
assert (E32 : ew EA 32 = w64 (ea_x0 a + Z.of_nat i1))
  by (exact (p7b_ex regs _ _ _ _ 0%nat ltac:(unfold A_TEXT; lia))).
assert (E33 : ew EA 33 = w64 (ea_x0 a + ea_len a))
  by (exact (p7b_ex regs _ _ _ _ 1%nat ltac:(unfold A_TEXT; lia))).
assert (HS : st_ok_pi SEGS VAL EA p7b_ssA (restrict (w_H W) (p7b_ms fxc regs mem EV_KEY))).
{ apply (p7b_stA a fxc W regs mem EA ly S Hp md k i1 (ea_dep a + 1) dl2 HP HM HR R20 Hi1);
  [ apply regs_ok_Eimg_Ereg | exact E19 | exact E20 | exact E24 | exact E26 | exact E32 | exact E33 ]. }
assert (SHOK : sh_ok SEGS p7b_Bx (@nil shent) EA (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold p7b_ms in HS.
unfold ev_cfg, ev_pc. rewrite p7b_pc_eq.
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7b_Bspan.
{ p7b_awr. }
pose proof (p7b_frame_ro EA _ _ _ HFr ltac:(vm_compute; reflexivity)) as HQ1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK p7b_Bspan;
  rewrite branch_geu_U in Hc;
  p7b_uat 32%nat (ea_x0 a + Z.of_nat i1) E32 Hc;
  p7b_uat 33%nat (ea_x0 a + ea_len a) E33 Hc.
- (* 0x839b8 taken: in->p >= in->end, the text is used up and the loop is skipped *)
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hi1e : i1 = length (ea_x a)) by (unfold ea_len in *; pose proof (Zle_0_nat i1); zl).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7b_Bspan (P7B_EV0 + P7B_WSE).
  { p7b_awr. }
  pose proof (p7b_frame_ro EA _ _ _ HFr ltac:(vm_compute; reflexivity)) as HQ2. clear HF HFr HG.
  pose proof (fun x => eq_trans (HQ2 x) (HQ1 x)) as HQ.
  pose proof (regs_kept_of_st_ok_pi EA _ _ regs _
    [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (11%bv : bv 5) N11.
  pmkst HS. p7b_cfg_to P7B_WSE.
  apply SRr_ret. split; [reflexivity|]. do 3 eexists. exists i1. split; [reflexivity|].
  split.
  { apply (p7b_wse_of a ly S Hp W regs mem md k _ _ _ n kid dl2 i1 _ HP HM HJ).
    - intros x _. exact (HQ x).
    - apply p7b_grows_of_eq. exact HQ.
    - eapply p7b_vm_eq; [exact HQ | exact (proj1 HCUR)].
    - exact HR.
    - exact HK.
    - exact R20.
    - exact R21.
    - exact R22.
    - exact R27.
    - exact R23.
    - p7b_rv N11 E33.
    - exact HSP.
    - exact M96.
    - exact M104.
    - exact M120.
    - exact HKID.
    - exact Hi1.
    - exact HMN. }
  split; [lia|]. rewrite Hi1e, skipn_all. reflexivity.
- (* 0x839b8 not taken: a byte is left, the loop runs from 0x839c0 *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hi1l : (i1 < length (ea_x a))%nat) by (unfold ea_len in *; zl).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7b_Bspan (P7B_EV0 + P7B_WSB).
  { p7b_awr. }
  pose proof (p7b_frame_ro EA _ _ _ HFr ltac:(vm_compute; reflexivity)) as HQ2. clear HF HFr HG.
  pose proof (fun x => eq_trans (HQ2 x) (HQ1 x)) as HQ.
  pose proof (regs_kept_of_st_ok_pi EA _ _ regs _
    [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  pmkst HS. p7b_cfg_to P7B_WSB.
  eapply SRr_bind.
  { apply (WS P7B_WSB P7B_WSE p7b_wsloop_in a fxc W _ _ _ ly S Hp k i1 (ea_dep a + 1) dl2 HP HFX).
    - apply (MIDF a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a + 1) dl2 _ _
        (ea_x0 a + Z.of_nat i1) (ea_dep a + 1) dl2 (fun z => ea_q a <= z < ea_q a + 8) HP HM HJ).
      + intros x _. exact (HQ x).
      + apply p7b_grows_of_eq. exact HQ.
      + intros z Hz. right. left. exact Hz.
      + eapply (p7b_cur_of a ly S Hp W mem md _ k _ (ea_dep a + 1) dl2 _ HP HM).
        * apply (p7b_mb_kept W mem _ (fun z => ea_q a <= z < ea_q a + 8)). intros x _. exact (HQ x).
        * eapply p7b_vm_eq; [exact HQ | exact (proj1 HCUR)].
      + exact HMN.
    - apply (p7b_regs_kept a regs _ HR). intros r Hr. apply HK. cbv in Hr |- *. tauto.
    - p7b_rv N10 E32.
    - p7b_rv N12 E32.
    - p7b_rv N11 E33.
    - rewrite (HK 27%bv) by (cbv; tauto). exact R27.
    - rewrite (HK 22%bv) by (cbv; tauto). exact R22.
    - exact Hi1l. }
  intros W2 c2 _ (HWeq & regs2 & mem2 & md2 & i' & Hc2 & HMID2 & Hii & Hsk & N10' & N12' & HKreg & HMEM2).
  subst W2. subst c2.
  apply SRr_ret. split; [reflexivity|]. exists regs2, mem2, md2, i'. split; [reflexivity|].
  pose proof HMID2 as (HJ2 & _ & _ & _ & _ & HCUR2 & _).
  pose proof HMID2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN2).
  assert (HRAW2 : forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) ->
    mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x)
    by (intros x Hx; exact (eq_trans (HMEM2 x Hx) (HQ x))).
  assert (HGR2 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2)).
  { eapply mem_grows_trans; [apply p7b_grows_of_eq; exact HQ|].
    apply (p7b_grows_mid W _ mem2 (ea_q a) (ea_q a + 8)); [exact HMEM2|].
    intros z Hz. destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply Hpres. zl. }
  split.
  { apply (p7b_wse_of a ly S Hp W regs mem md k mem2 md2 regs2 n kid dl2 i' _ HP HM HJ2).
    - exact HRAW2.
    - exact HGR2.
    - exact (proj1 HCUR2).
    - exact HR.
    - intros r Hr. rewrite (p7b_ws_kept _ _ HKreg r Hr). apply HK. cbv in Hr |- *. tauto.
    - exact R20.
    - exact R21.
    - exact R22.
    - exact R27.
    - exact R23.
    - rewrite (HKreg 11%bv) by (intros Hx; apply (f_equal bv_unsigned) in Hx; vm_compute in Hx; discriminate Hx).
      p7b_rv N11 E33.
    - exact HSP.
    - exact M96.
    - exact M104.
    - exact M120.
    - exact HKID.
    - lia.
    - exact HMN2. }
  split; [lia | exact Hsk].
Qed.

(* the ws loop's exit (A' 0x83a0c) -> P_EXIT through the refusal join 0x83b54 (`ld s6,24(s1); li s11,-1; j`), or
   -> C_CALL (A' 0x83a4c). Report checks 0x83a10 and 0x83a3c (the shadow byte of q) are NOT TAKEN: the symbolic chunk
   at s10 is the byte 0 of alx_zshadow_byte on the real stack. 0x83a28 (the text byte's shadow) with its
   partial-granule arm 0x83b28-0x83b30 -> 0x83fdc is NOT TAKEN: the token is covered by sh_ok, whose
   range_addressable is the text's (src_rd, carried by ev_mid; it is the ev_inblk_shadow_FIX fact on the text's
   block). The two refusals: in->p = in->end (0x83a18) and a byte other than ':' (0x83a34); in both the model
   refuses because the reader's name does (p7b_name_none, evp_L_step). *)
Lemma p7b_tail : forall a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 (i' : nat),
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  p7b_at_wse a W regs mem md ly S Hp k n kid dl2 i' ->
  0 <= ea_dep a <= 31 -> (n <= i)%nat -> (i <= i1)%nat -> (i1 <= i')%nat -> n = length acc ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_L (Nat.succ (Z.to_nat (ea_dep a))) true n cap acc (skipn i (ea_x a)) ->
  ev_run0 (PjGrammar.jr_name true (skipn i (ea_x a))) =
    (match PjGrammar.skip (skipn i1 (ea_x a)) with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end) ->
  skipn i' (ea_x a) = PjGrammar.skip (skipn i1 (ea_x a)) ->
  ev_dl_key a true n nm dln dl2 -> ev_dl (ea_dl a) (ea_v a) true (ea_t a) acc dln ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs P7B_WSE mem md)
    (fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
       exists regs' mem' md' ly' S' Hp' k' iv cap1,
         c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_CALL mem' md' /\
         ev_at_call B ARx SK a W' regs' mem' md' ly' S' Hp' k' true n cap1 acc i iv nm dln kid dl2).
Proof.
intros a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 i' HP HFX HWSE HDEP Hni Hii1 Hi1i' Hnacc
  HMODEL HNAME Hsk HDLK HDL.
pose proof HWSE as (HM & HR & R20 & R21 & R22 & R27 & R23 & N11 & HSP & M96 & M104 & M120 & HKID & Hi'len).
pose proof (p7b_arith a ly S Hp W mem md k (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl2 HP HM) as
  (AS1 & ASQ & AQ47 & AAL1 & AAL2 & AX0 & AXC & AQL & AQH & ALEN & ADEP & AL0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (BNDS a HP) as (BC & BS1 & BS2 & BA1 & BQ & BQD & B47 & BA2 & BD0).
pose proof HM as (HJ & _ & _ & _ & _ & HCUR & HSRC & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSP as (M24 & _).
pose proof (p7b_fr_bounds a ly S Hp W mem md k _ _ _ HM) as [F0 F1].
assert (HKB : 0 <= kid /\ kid + 56 <= alloc_ceiling).
{ destruct HKID as [(HZ & _) | (_ & _ & H1 & H2 & _)]; [subst kid|]; split; zl. }
destruct HKB as [HK0 HKC].
assert (Hi'z : 0 <= Z.of_nat i' <= ea_len a) by (unfold ea_len; pose proof (Zle_0_nat i'); zl).
assert (HDL2 : dl2 = 0 \/ dl2 = 1) by exact (proj1 HDLK).
unfold ev_cfg, ev_pc. rewrite p7b_pc_eq.
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx cf_head LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
destruct (Nat.lt_ge_cases i' (length (ea_x a))) as [Hlt | Hge].
- (* ---- a byte is left at in->p ---- *)
  destruct HSRC as (HBY & HX4 & HXC & HAMR & HRA & HHU).
  destruct (HBY i' Hlt) as [MC HC8].
  remember (nth i' (ea_x a) 0) as c eqn:Hceq.
  assert (HAPP : ea_x0 a + Z.of_nat i' + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= ea_x0 a + Z.of_nat i').
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR. unfold SHADOW_OFF.
    pose proof (Zle_0_nat (length (ea_x a))).
    assert (Hil : Z.of_nat i' < Z.of_nat (length (ea_x a))) by zl.
    destruct HAMR as [H1 | [H1 H2]]; [left | right]; zl. }
  set (EB := p7b_E regs (ea_x0 a + Z.of_nat i') c (ea_fr a) kid).
  assert (HEI : img_env VAL A_LIM EB) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs [w64 (ea_x0 a + Z.of_nat i'); w64 c; w64 (ea_fr a); w64 kid]) EB)
    by apply p7b_env_agree.
  assert (E9 : ew EB 9 = w64 (ea_S1 a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)) R9)).
  assert (E11 : ew EB 11 = w64 (ea_x0 a + ea_len a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 11%nat 11%bv eq_refl ltac:(unfold A_TEXT; lia)) N11)).
  assert (E19 : ew EB 19 = w64 (ea_q a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 19%nat 19%bv eq_refl ltac:(unfold A_TEXT; lia)) R19)).
  assert (E24 : ew EB 24 = w64 SHADOW_OFF)
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)) R24)).
  assert (E26 : ew EB 26 = w64 (shadow_addr (ea_q a)))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 26%nat 26%bv eq_refl ltac:(unfold A_TEXT; lia)) R26)).
  assert (E32 : ew EB 32 = w64 (ea_x0 a + Z.of_nat i'))
    by (exact (p7b_ex regs _ _ _ _ 0%nat ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew EB 33 = w64 c) by (exact (p7b_ex regs _ _ _ _ 1%nat ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew EB 34 = w64 (ea_fr a)) by (exact (p7b_ex regs _ _ _ _ 2%nat ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew EB 35 = w64 kid) by (exact (p7b_ex regs _ _ _ _ 3%nat ltac:(unfold A_TEXT; lia))).
  destruct (p7b_stB a fxc W regs mem EB ly S Hp md k i' (ea_dep a + 1) dl2 kid c HP HM Hlt M24 M96 HK0 HKC
    MC HC8 HAPP HRA ltac:(apply regs_ok_Eimg_Ereg) E9 E19 E24 E26 E32 E33 E34 E35) as [HS SHOK].
  unfold p7b_ms in HS.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7b_Bspan.
  { p7b_awrB E19. }
  pose proof (p7b_frame_slot _ _ _ _ (ea_q a) (ea_q a + 8) HFr ltac:(p7b_slot E19)) as HQ1.
  rename HG into HG1. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK p7b_Bspan;
    rewrite branch_geu_U in Hc;
    p7b_uat 32%nat (ea_x0 a + Z.of_nat i') E32 Hc;
    p7b_uat 11%nat (ea_x0 a + ea_len a) E11 Hc.
  + (* 0x83a18 taken: impossible, a byte is left *)
    exfalso. apply negb_true_iff, Z.ltb_ge in Hc. unfold ea_len in *. zl.
  + (* 0x83a18 not taken: the shadow token at 0x83a1c-0x83a28 (NOT TAKEN by sh_ok), the byte, the ':' test *)
    paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7b_Bspan.
    { p7b_awrB E19. }
    pose proof (p7b_frame_slot _ _ _ _ (ea_q a) (ea_q a + 8) HFr ltac:(p7b_slot E19)) as HQ2.
    rename HG into HG2. clear HF HFr Hc.
    psrr_branch_tok RUN BR HS SHOK p7b_Bspan;
      rewrite (p7b_bne_lit _ 33%nat c 58) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E33 | zl]).
    * (* 0x83a34 taken: the byte is not ':', the refusal join 0x83b54 *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      assert (HNONE : prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None).
      { rewrite HMODEL. apply p7b_L_none.
        apply (p7b_name_none (ea_x a) i i1 i' nm true Hsk HNAME). right. rewrite <- Hceq. exact Hc. }
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7b_Bspan (P7B_EV0 + EV_EXIT).
      { p7b_awrB E19. }
      pose proof (p7b_frame_slot _ _ _ _ (ea_q a) (ea_q a + 8) HFr ltac:(p7b_slot E19)) as HQ3.
      rename HG into HG3. clear HF HFr.
      p7b_inp HS E19 E32 HQV.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;24;25;26]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      prreg HS (22%bv : bv 5) N22. prreg HS (27%bv : bv 5) N27.
      pmkst HS. p7b_cfg_to EV_EXIT.
      apply SRr_ret. left.
      eexists; eexists; eexists; eexists. exists ly, S, Hp, k, (-1), (Z.of_nat i'), (ea_dep a + 1), dl2.
      split; [reflexivity|]. split; [exact HFX|].
      apply (p7b_exit_of a ly S Hp W regs mem md k _ _ _ i' dl2 _ HP HM HJ).
      -- intros x Hx. exact (eq_trans (HQ3 x Hx) (eq_trans (HQ2 x Hx) (HQ1 x Hx))).
      -- exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3).
      -- rewrite Z.add_0_r in HQV. exact HQV.
      -- exact HR.
      -- exact HK.
      -- p7b_rv N22 E34.
      -- rewrite N27. apply bv_eq. reflexivity.
      -- exact HDL2.
      -- exact HDEP.
      -- exact Hi'len.
      -- exact HNONE.
      -- exact HMN.
    * (* 0x83a34 not taken: the byte is ':', in->p++ and the kid reloaded, to C_CALL *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7b_Bspan (P7B_EV0 + EV_CALL).
      { p7b_awrB E19. }
      pose proof (p7b_frame_slot _ _ _ _ (ea_q a) (ea_q a + 8) HFr ltac:(p7b_slot E19)) as HQ3.
      rename HG into HG3. clear HF HFr.
      p7b_inp HS E19 E32 HQV.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) N11'.
      pmkst HS. p7b_cfg_to EV_CALL.
      apply SRr_ret. right.
      do 3 eexists. exists ly, S, Hp, k, (Nat.succ i'), (ev_cap n cap).
      split; [reflexivity|].
      apply (p7b_call_of a ly S Hp W regs mem md k _ _ _ n (ev_cap n cap) acc i (Nat.succ i') nm dln kid dl2 _ HP HM HJ).
      -- intros x Hx. exact (eq_trans (HQ3 x Hx) (eq_trans (HQ2 x Hx) (HQ1 x Hx))).
      -- exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3).
      -- rewrite Nat2Z.inj_succ. replace (ea_x0 a + Z.succ (Z.of_nat i')) with (ea_x0 a + Z.of_nat i' + 1) by zl.
         exact HQV.
      -- exact HR.
      -- exact HK.
      -- exact R20.
      -- exact R21.
      -- exact R22.
      -- exact R27.
      -- p7b_rv N11' E35.
      -- exact HSP.
      -- exact M96.
      -- exact M104.
      -- exact M120.
      -- exact HKID.
      -- exact HDEP.
      -- exact Hni.
      -- apply (Nat.le_trans _ _ _ Hii1). apply (Nat.le_trans _ _ _ Hi1i'). apply Nat.le_succ_diag_r.
      -- exact Hlt.
      -- exact Hnacc.
      -- rewrite HMODEL.
         rewrite (p7b_L_some _ _ _ _ _ _ nm (skipn (Nat.succ i') (ea_x a))
           (p7b_name_some (ea_x a) i i1 i' nm true Hsk HNAME Hlt ltac:(rewrite <- Hceq; exact Hc))).
         rewrite (p7b_V_value (ea_dep a) _ ltac:(zl)). reflexivity.
      -- exact HDLK.
      -- exact HDL.
      -- exact HMN.
- (* ---- the text is used up: in->p = in->end ---- *)
  assert (HNONE : prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None).
  { rewrite HMODEL. apply p7b_L_none. apply (p7b_name_none (ea_x a) i i1 i' nm true Hsk HNAME). left. exact Hge. }
  set (EE := p7b_E regs (ea_x0 a + Z.of_nat i') 0 (ea_fr a) kid).
  assert (HEI : img_env VAL A_LIM EE) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs [w64 (ea_x0 a + Z.of_nat i'); w64 0; w64 (ea_fr a); w64 kid]) EE)
    by apply p7b_env_agree.
  assert (E9 : ew EE 9 = w64 (ea_S1 a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)) R9)).
  assert (E11 : ew EE 11 = w64 (ea_x0 a + ea_len a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 11%nat 11%bv eq_refl ltac:(unfold A_TEXT; lia)) N11)).
  assert (E19 : ew EE 19 = w64 (ea_q a))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 19%nat 19%bv eq_refl ltac:(unfold A_TEXT; lia)) R19)).
  assert (E24 : ew EE 24 = w64 SHADOW_OFF)
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)) R24)).
  assert (E26 : ew EE 26 = w64 (shadow_addr (ea_q a)))
    by (exact (eq_trans (p7b_ew regs _ _ _ _ 26%nat 26%bv eq_refl ltac:(unfold A_TEXT; lia)) R26)).
  assert (E32 : ew EE 32 = w64 (ea_x0 a + Z.of_nat i'))
    by (exact (p7b_ex regs _ _ _ _ 0%nat ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew EE 34 = w64 (ea_fr a)) by (exact (p7b_ex regs _ _ _ _ 2%nat ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew EE 35 = w64 kid) by (exact (p7b_ex regs _ _ _ _ 3%nat ltac:(unfold A_TEXT; lia))).
  assert (HS : st_ok_pi SEGS VAL EE p7b_ssE (restrict (w_H W) (p7b_ms fxc regs mem P7B_WSE))).
  { apply (p7b_stE a fxc W regs mem EE ly S Hp md k i' (ea_dep a + 1) dl2 kid HP HM Hi'len M24 M96 HK0 HKC);
    [ apply regs_ok_Eimg_Ereg | exact E9 | exact E19 | exact E24 | exact E26 | exact E32 | exact E34
    | exact E35 ]. }
  assert (SHOK : sh_ok SEGS p7b_Bx (@nil shent) EE (mrestrict (w_H W) mem)) by apply Forall_nil.
  unfold p7b_ms in HS.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7b_Bspan.
  { p7b_awr. }
  pose proof (p7b_frame_ro EE _ _ _ HFr ltac:(vm_compute; reflexivity)) as HQ1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK p7b_Bspan;
    rewrite branch_geu_U in Hc;
    p7b_uat 32%nat (ea_x0 a + Z.of_nat i') E32 Hc;
    p7b_uat 11%nat (ea_x0 a + ea_len a) E11 Hc.
  + (* 0x83a18 taken: the refusal join 0x83b54 *)
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7b_Bspan (P7B_EV0 + EV_EXIT).
    { p7b_awr. }
    pose proof (p7b_frame_ro EE _ _ _ HFr ltac:(vm_compute; reflexivity)) as HQ2. clear HF HFr HG.
    pose proof (fun x => eq_trans (HQ2 x) (HQ1 x)) as HQ.
    pose proof (regs_kept_of_st_ok_pi EE _ _ regs _ [2;3;4;8;9;18;19;24;25;26]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
    prreg HS (22%bv : bv 5) N22. prreg HS (27%bv : bv 5) N27.
    pmkst HS. p7b_cfg_to EV_EXIT.
    apply SRr_ret. left.
    eexists; eexists; eexists; eexists. exists ly, S, Hp, k, (-1), (Z.of_nat i'), (ea_dep a + 1), dl2.
    split; [reflexivity|]. split; [exact HFX|].
    apply (p7b_exit_of a ly S Hp W regs mem md k _ _ _ i' dl2 _ HP HM HJ).
    * intros x _. exact (HQ x).
    * apply p7b_grows_of_eq. exact HQ.
    * eapply p7b_vm_eq; [exact HQ | exact (proj1 HCUR)].
    * exact HR.
    * exact HK.
    * p7b_rv N22 E34.
    * rewrite N27. apply bv_eq. reflexivity.
    * exact HDL2.
    * exact HDEP.
    * exact Hi'len.
    * exact HNONE.
    * exact HMN.
  + (* 0x83a18 not taken: impossible, in->p = in->end *)
    exfalso. apply negb_false_iff, Z.ltb_lt in Hc. unfold ea_len in *. zl.
Qed.

(* ======== SEG 3 of piece 7: C_KEY (A' 0x839a0) -> C_CALL (A' 0x83a4c), or the refusal join -> P_EXIT ========
   `Proof using` pins the generalized signature to the Section's order (LAWS, PSTI, MIDF, BNDS; WS is now a lemma
   derived from LAWS, not a Section hypothesis) so S8aP7 can instantiate it; PSTI is not used by this segment. *)
Lemma ev7_seg3_A : ev7_seg3_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof using LAWS PSTI MIDF BNDS.
intros a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 HP HFX HKEY.
pose proof HKEY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HDEP & Hni & Hii1 & Hi1 & Hnacc & HMODEL & HNAME & _ & HDLK & HDL).
eapply SRr_bind; [exact (p7b_head a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 HP HFX HKEY)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & i' & -> & HWSE & Hi1i' & Hsk).
exact (p7b_tail a fxc W regs1 mem1 md1 ly S Hp k n cap acc i i1 nm dln kid dl2 i' HP HFX HWSE
  HDEP Hni Hii1 Hi1i' Hnacc HMODEL HNAME Hsk HDLK HDL).
Qed.

End w.

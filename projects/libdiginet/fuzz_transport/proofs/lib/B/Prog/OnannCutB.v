(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module paths and module names changed; 411 of its 477 lines of code are new or changed and 379 lines of the source are left out. *)
(* OnannCutB: the cuts of the walk of on_announce on fuzz_transport.asan-ubsan (0x87cc8 = transportb_sigma
   TB_on_announce, AF_on_announce = 0x6a28 of lib/B/Prog/DgnTransportBList.v, 2244 bytes), as STATEMENTS only, and the
   composition onann_holds_of: the statement transport_on_announce_cg_holds_stmt of lib/B/Prog/on_announce_cg.v from
   the piece Props. Image B's twin of image A's lib/A/Prog/OnannCut.v: the same cuts at image B's code. The walk holds
   the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the return, with
   (ONANN_CID, pos) :: own while the class-3 frame is live. Offsets are from the entry (+0x000 = 0x87cc8).
     head  +0x000 .. +0x198  the frame (`addi sp, sp, -192`, the zero word at sp, the 13 saves), s0, the realign into
                             s1, s7 = now, s6 = fp, the runtime cells (the flag word 1, so `beq a2, zero` at +0x06c is
                             not taken), s8 = the shadow base, s4 = s, the class-3 stack malloc (+0x074), s9 = s3 = the
                             frame, `bne s9, zero` taken, the frame word at s1 + 80, s10 = a = frame + 32, the header and
                             the 44 shadow bytes (s2 = their base), to the parse cut (onann_lp_at, +0x19c).
                             Prop: onann_head_stmt.
     lp    +0x19c .. +0x1a8  diginet_announce_parse (+0x1a4, a0 = fp, a1 = a) and `beq a0, zero` (+0x1a8): a code <> 0
                             goes to the ignore cut (onann_ign_at, +0x1ac), 0 to the personality cut (onann_pf_at,
                             +0x1e0). Prop: onann_lp_stmt.
     ign   +0x1ac .. +0x1dc  s & 7 (UBSan's alignment check; the trap word +0x774 not reached), g_s.stats.rx_ignored + 1,
                             `j` to the release cut (onann_arel_at, +0x644). Prop: onann_ign_stmt.
     pf    +0x1e0 .. +0x274  diginet_personality_from_name (+0x1e4), the store of g_s.personality, fp & 7 (UBSan), the
                             checked load of f + 30, the spills at s1 + 48, 56, 24, 16 and `bne a1, a2` (+0x24c):
                             cmd = 0xe1 goes to the find_mac cut (onann_fm_at, +0x250); any other cmd runs +0x270 ..
                             +0x274 (a1 = 1, `j`) to the desk notice cut (onann_dn_at, +0x300). Prop: onann_pf_stmt.
     fm    +0x250 .. +0x2fc  s & 7 (UBSan), find_mac's bcmp loop (i = 0 .. 9; the UBSan pointer checks of unknown + i),
                             to the desk notice cut. Prop: onann_fm_stmt.
     dn    +0x300 .. +0x3e8  n's shadow, the desk notice's fields, __asan_memset (+0x390), notice (+0x3cc), the
                             reload of f + 30 and `bne a0, a1` (+0x3e8): 0xe0 goes to onann_e0_at (+0x3ec), 0xe1 to
                             onann_e1_at (+0x4a0). Prop: onann_dn_stmt.
     e0    +0x3ec .. +0x420  g_s.foreign = 0, the reloads of s10, s5, s6, the load of g_s.state, `bne a0, a1` (+0x420):
                             S_ONLINE goes to the first inlined session_lost (onann_sl1_at, +0x424), any other state
                             to onann_wk_at (+0x470). Prop: onann_e0_stmt.
     sl1   +0x424 .. +0x46c  the first inlined session_lost (the stores at s + 212 and s + 168, set_state at +0x460 with
                             why = 3), the reload of g_s.state, to onann_wk_at. Prop: onann_sl1_stmt.
     wk    +0x470 .. +0x49c  the tests of :204 and diginet_session_wake (+0x498), to onann_nrel_at (+0x61c).
                             Prop: onann_wk_stmt.
     e1    +0x4a0 .. +0x4e0  `blt s7, zero` (+0x4ac): off < 0 goes to the foreign cut (onann_fn_at, +0x4e4); else
                             g_s.foreign = 0, g_s.e1_named_us = 1, maybe_online (+0x4dc), to onann_nrel_at.
                             Prop: onann_e1_stmt.
     fn    +0x4e4 .. +0x5b0  g_s.foreign = 1, fn's shadow and fields, __asan_memset (+0x568), notice (+0x590), the load
                             of g_s.state and `bltu a1, a0` (+0x5b0): S_WAKING / S_ONLINE goes to the second inlined
                             session_lost (onann_sl2_at, +0x5b4), any other state to onann_fnrel_at (+0x5f4).
                             Prop: onann_fn_stmt.
     sl2   +0x5b4 .. +0x5f0  the second inlined session_lost (set_state at +0x5f0 with why = 5), to onann_fnrel_at.
                             Prop: onann_sl2_stmt.
     tail  +0x5f4 .. +0x770  fn's shadow 0xf8 (onann_fnrel_at), n's shadow 0xf8 (onann_nrel_at, +0x61c), a's shadow
                             0xf8 (onann_arel_at, +0x644), the header word, `beq s9, zero` not taken,
                             __asan_set_shadow_f5 (+0x674, 64 shadow bytes), the flag store (+0x67c), `j`, the epilogue
                             and `ret`. Prop: onann_tail_stmt (the three cuts).
   Each cut holds the caller's facts (onann_fix), the facts the walk carries while its frame is live (onann_cur), the
   cut's world and model continuation, the spill slots of s1 the code after the cut reads, and the registers it reads
   (the onann_regs_ predicates), and concludes the statement's post (on_announce_cg.v transport_onann_post) at the
   cut's pc. The continuations onann_k_ are the rest of on_announce_m after each cut (onann_model_split). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The cut points, the saved words, the frame                       *)
(* ------------------------------------------------------------------ *)

(* The cut points, as offsets from the listing's base (each the first instruction of its piece). *)
Definition ONANN_LP : Z := AF_on_announce + 0x19c.     (* 0x87e64 `mv a0, s6` *)
Definition ONANN_IGN : Z := AF_on_announce + 0x1ac.    (* 0x87e74 `andi a0, s4, 7` *)
Definition ONANN_PF : Z := AF_on_announce + 0x1e0.     (* 0x87ea8 `addi a0, s10, 10` *)
Definition ONANN_FM : Z := AF_on_announce + 0x250.     (* 0x87f18 `bne a0, zero` (UBSan, s & 7) *)
Definition ONANN_DN : Z := AF_on_announce + 0x300.     (* 0x87fc8 `addi s5, s3, 112` *)
Definition ONANN_E0 : Z := AF_on_announce + 0x3ec.     (* 0x880b4 `addi a0, s4, 136` *)
Definition ONANN_SL1 : Z := AF_on_announce + 0x424.    (* 0x880ec `addi a0, s4, 212` *)
Definition ONANN_WK : Z := AF_on_announce + 0x470.     (* 0x88138 `bne a0, zero` *)
Definition ONANN_E1 : Z := AF_on_announce + 0x4a0.     (* 0x88168 `addi a0, s4, 136` *)
Definition ONANN_FN : Z := AF_on_announce + 0x4e4.     (* 0x881ac `lb a1, 0(a1)` *)
Definition ONANN_SL2 : Z := AF_on_announce + 0x5b4.    (* 0x8827c `addi a0, s4, 212` *)
Definition ONANN_FNREL : Z := AF_on_announce + 0x5f4.  (* 0x882bc `li a0, -8` (fn's shadow) *)
Definition ONANN_NREL : Z := AF_on_announce + 0x61c.   (* 0x882e4 `li a0, -8` (n's shadow) *)
Definition ONANN_AREL : Z := AF_on_announce + 0x644.   (* 0x8830c `li a0, -8` (a's shadow) *)
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 184 ..
   sp + 88 after `addi sp, sp, -192`). *)
Definition ONANN_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-3 frame's size. *)
Definition ONANN_FBYTES : Z := 512.
Lemma onann_fbytes : fs_frame_bytes ONANN_CID = ONANN_FBYTES.
Proof. reflexivity. Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma onann_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model after each cut                                         *)
(* ------------------------------------------------------------------ *)

(* :204-205, after the e0 arm's world B4. *)
Definition onann_k_wk (I : TI.timg) (Fr : option TI.tframe) (B4 : list byte) (now : Z) : option (list byte * unit) :=
  if (TW.S_state B4 =? TS0.DIGINET_S_IDLE) && negb (TW.S_cfg_auto_wake B4 =? 0) then
    match TSS.diginet_session_wake_m I Fr B4 now with
    | None => None
    | Some (B5, _) => Some (B5, tt)
    end
  else Some (B4, tt).
(* :203, the first inlined session_lost at Bx = set_S_foreign B2 0, then :204-205. *)
Definition onann_k_sl1 (I : TI.timg) (Fr : option TI.tframe) (Bx : list byte) (now : Z) : option (list byte * unit) :=
  match TSS.session_lost_m I Fr Bx TS0.DIGINET_R_DESK_OFFLINE with
  | None => None
  | Some (B4, _) => onann_k_wk I Fr B4 now
  end.
(* :201-205 from the desk notice's world B2 (cmd 0xe0). *)
Definition onann_k_e0 (I : TI.timg) (Fr : option TI.tframe) (B2 : list byte) (now : Z) : option (list byte * unit) :=
  if TW.S_state (TW.set_S_foreign B2 0) =? TS0.DIGINET_S_ONLINE
  then onann_k_sl1 I Fr (TW.set_S_foreign B2 0) now
  else onann_k_wk I Fr (TW.set_S_foreign B2 0) now.
(* :219-220 from the foreign notice's world B3. *)
Definition onann_k_fs (I : TI.timg) (Fr : option TI.tframe) (B3 : list byte) : option (list byte * unit) :=
  if (TW.S_state B3 =? TS0.DIGINET_S_ONLINE) || (TW.S_state B3 =? TS0.DIGINET_S_WAKING)
  then TSS.session_lost_m I Fr B3 TS0.DIGINET_R_FOREIGN else Some (B3, tt).
(* :217-220 from the world Bf = set_S_foreign B2 1 of :216. *)
Definition onann_k_fn (I : TI.timg) (Fr : option TI.tframe) (Bf b : list byte) : option (list byte * unit) :=
  match TSS.call_notify I Fr Bf (onann_fntc Bf b) with
  | None => None
  | Some (B3, _) => onann_k_fs I Fr B3
  end.
(* :209-220 from the desk notice's world B2 (cmd 0xe1), off = find_mac's result. *)
Definition onann_k_e1 (I : TI.timg) (Fr : option TI.tframe) (B2 : list byte) (off : Z) (b : list byte)
    : option (list byte * unit) :=
  if 0 <=? off then TSS.maybe_online_m I Fr (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)
  else onann_k_fn I Fr (TW.set_S_foreign B2 1) b.

(* on_announce_m on a frame the parse accepts: the desk notice, then the two arms. *)
Lemma onann_model_split : forall (I : TI.timg) (Fr : option TI.tframe) (Bw b : list byte) (now : Z),
  onann_ign b = false ->
  TSS.on_announce_m I Fr Bw b now =
  match TSS.call_notify I Fr (onann_w1 I Bw b) (onann_dntc I (onann_w1 I Bw b) b) with
  | None => None
  | Some (B2, _) =>
      if DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE then onann_k_e0 I Fr B2 now
      else onann_k_e1 I Fr B2 (onann_off (onann_w1 I Bw b) b) b
  end.
Proof.
intros I Fr Bw b now Hig. rewrite onann_model, Hig. cbv iota.
destruct (TSS.call_notify I Fr (onann_w1 I Bw b) (onann_dntc I (onann_w1 I Bw b) b)) as [[B2 u]|]; [|reflexivity].
destruct (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE); [|reflexivity].
unfold onann_k_e0, onann_k_sl1.
destruct (TW.S_state (TW.set_S_foreign B2 0) =? TS0.DIGINET_S_ONLINE); reflexivity.
Qed.

(* The run invariants (1) and (4) of diginet_session_wake at a world (on_announce_cg.v's premises), with (4)'s index
   bound g_ncmd Bx <= CMDS_MAX: past g_cmd's 1024 entries an index aliases other world bytes (GOT.t among them), which
   the notices and set_state write, so (4) carries across those stores only with the bound. The bound at the entry is
   the statement's premise beside (4) (image A's statement has it; image B's is to gain it). *)
Definition onann_ri (Bx : list byte) : Prop :=
  (TW.M_fly_on Bx <> 0 -> TW.M_fly_len Bx <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bx -> TW.Cmd_st Bx s = TC.PENDING -> TW.Cmd_len Bx s <= DSpec.SPEC_CMD_MAX) /\
  TW.g_ncmd Bx <= TC.CMDS_MAX.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma onann_cut_pcs :
  BASE + AF_on_announce = transportb_sigma TB_on_announce /\
  BASE + ONANN_LP = 0x87e64 /\
  BASE + ONANN_IGN = 0x87e74 /\ BASE + ONANN_PF = 0x87ea8 /\ BASE + ONANN_FM = 0x87f18 /\
  BASE + ONANN_DN = 0x87fc8 /\ BASE + ONANN_E0 = 0x880b4 /\ BASE + ONANN_SL1 = 0x880ec /\
  BASE + ONANN_WK = 0x88138 /\ BASE + ONANN_E1 = 0x88168 /\ BASE + ONANN_FN = 0x881ac /\
  BASE + ONANN_SL2 = 0x8827c /\ BASE + ONANN_FNREL = 0x882bc /\ BASE + ONANN_NREL = 0x882e4 /\
  BASE + ONANN_AREL = 0x8830c.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The record, the callees, the caller's facts                      *)
(* ------------------------------------------------------------------ *)

(* The facts of the record every piece may use: the premises of transport_on_announce_cg_holds_stmt that are not
   callee contracts, and gx_ok / gx_noerrno (DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno). *)
Definition onann_laws : Prop :=
  pc_stack_malloc (as_code B) ONANN_CID = transportb_sigma TB___asan_stack_malloc_3 /\
  transport_cells B /\ trans_onann_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The callee contracts of the statement, in its order. *)
Definition onann_callees : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONANN_CID) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_announce_parse_cg fx' rc B MT (transportb_sigma TB_diginet_announce_parse)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_personality_from_name_cg fx' rc B MT (transportb_sigma TB_diginet_personality_from_name)) /\
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) /\
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) /\
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_wake_cg fx' rc B MT (transportb_sigma TB_diginet_session_wake)) /\
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transportb_sigma TB_maybe_online)) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_f5) 0xf5).

(* The caller's facts (the premises of transport_on_announce_cg at the entry registers regs), and what the head fixes
   before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -192`, `andi sp, sp, -32`); pos, the slot of
   the class-3 frame the stack malloc gave; F, the frame's address. *)
Definition onann_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
    (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 ONANN_S /\ YK11.getr regs 11 = w64 fp /\ YK11.getr regs 12 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - ONANN_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  trans_dframe_at B lyc Sc W memc regs ONANN_STK fp buf b fj /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.on_announce_m timg_B TF Bw b now = Some (Bw', tt) /\
  trans_tframe_at B lyc Sc W memc regs ONANN_STK TF /\
  trans_tf_off_g TF /\
  trans_rom_view_rd W memc /\
  onann_apart TF Bw b /\
  onann_ri Bw /\
  count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID /\
  count_cid WAKE_CID (frames Sc) < fs_frames WAKE_CID /\
  count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID /\
  st_nev S + k + ONANN_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - ONANN_FRAME) / 32) /\
  F = frame_addr lyc ONANN_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + ONANN_FBYTES <= alloc_ceiling /\ in_app F ONANN_FBYTES.

(* ------------------------------------------------------------------ *)
(* 4. What every cut carries                                           *)
(* ------------------------------------------------------------------ *)

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range onann_wr Bw b); the 13 saved words below the entry sp; the frame's last word, the address of its
   flag byte (astack_malloc_realizes' rdword). *)
Definition onann_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw b : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= ONANN_EV /\
  frames S2 = (ONANN_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos).

(* The local a (F + 32, 40 bytes) as diginet_announce_parse left it, read through the view: the version field's
   bytes up to its 0 at a (TSS.ann_field of the body from 15), the name's at a + 10 (from 24), unknown = buf + 30 at
   a + 24 and unknown_len = 15 at a + 32; and a's 5 shadow bytes 4 .. 8 are 0 (a usable). *)
Definition onann_a_ok (W2 : world segs) (mem2 : word -> option byte) (F buf : Z) (b : list byte) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) (F + ONANN_A) (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b)))) /\
  garr8 segs (mrestrict (w_H W2) mem2) (F + ONANN_A + 10)
    (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b)))) /\
  rdword (aview segs (w_H W2) mem2) (F + ONANN_A + 24) = Some (buf + 30) /\
  rdword (aview segs (w_H W2) mem2) (F + ONANN_A + 32) = Some 15 /\
  (forall i, 4 <= i < 9 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0).

(* A spill slot of the machine frame: the 8-byte word at sp1 + o holds v. *)
Definition onann_slot (W2 : world segs) (mem2 : word -> option byte) (sp1 o v : Z) : Prop :=
  rdword (aview segs (w_H W2) mem2) (sp1 + o) = Some v.

(* The world after the desk notice (an N_DESK notice changes GOT.desk only: TCb.v notice_m, check_state_desk_m). *)
Definition onann_b2 (Fr : option TI.tframe) (Bw b B2 : list byte) : Prop :=
  TSS.call_notify timg_B Fr (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) = Some (B2, tt) /\
  exists d, B2 = TW.set_GOT_desk (onann_w1 timg_B Bw b) d.

(* ------------------------------------------------------------------ *)
(* 5. The registers each cut's code reads                              *)
(* ------------------------------------------------------------------ *)

(* Every cut: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = the frame's first shadow byte, s3 = s9 = the frame
   (s9: the stack malloc's result, which the release tests at +0x668 and reads at +0x678). These are what the release
   cuts (+0x5f4, +0x61c, +0x644) read. *)
Definition onann_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\
  YK11.getr regs2 18 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 19 = w64 F /\ YK11.getr regs2 25 = w64 F.
(* The ignore cut (+0x1ac), e0 (+0x3ec) and sl2 (+0x5b4): and s4 = s, s8 = the shadow base. *)
Definition onann_regs_ign (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  onann_regs_rel regs regs2 sp1 F /\ YK11.getr regs2 20 = w64 ONANN_S /\ YK11.getr regs2 24 = w64 SHADOW_OFF.
(* The parse cut (+0x19c) and the personality cut (+0x1e0): and s6 = fp, s7 = now, s10 = a. *)
Definition onann_regs_pf (regs regs2 : bvmap 5 word) (fp now sp1 F : Z) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 22 = w64 fp /\ YK11.getr regs2 23 = w64 now /\ YK11.getr regs2 26 = w64 (F + ONANN_A).
(* The find_mac cut (+0x250): and s6 = fp, s10 = a, a6 = p (the personality pointer), a0 = s & 7 = 0. *)
Definition onann_regs_fm (regs regs2 : bvmap 5 word) (fp sp1 F : Z) (b : list byte) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 22 = w64 fp /\ YK11.getr regs2 26 = w64 (F + ONANN_A) /\
  YK11.getr regs2 16 = w64 (onann_pv timg_B b) /\ YK11.getr regs2 10 = w64 0.
(* The desk notice cut (+0x300): s6 = fp, s10 = a, a6 = p, a5 = off, a1 = 1 (s & 7 = 0, the test at +0x330). *)
Definition onann_regs_dn (regs regs2 : bvmap 5 word) (fp sp1 F off : Z) (b : list byte) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 22 = w64 fp /\ YK11.getr regs2 26 = w64 (F + ONANN_A) /\
  YK11.getr regs2 16 = w64 (onann_pv timg_B b) /\ YK11.getr regs2 15 = w64 off /\ YK11.getr regs2 11 = w64 1.
(* The e1 cut (+0x4a0): and s7 = off, s6 = fp, s10 = s + 96, s11 = s + 104. *)
Definition onann_regs_e1 (regs regs2 : bvmap 5 word) (fp sp1 F off : Z) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 23 = w64 off /\ YK11.getr regs2 22 = w64 fp /\
  YK11.getr regs2 26 = w64 (ONANN_S + 96) /\ YK11.getr regs2 27 = w64 (ONANN_S + 104).
(* The foreign cut (+0x4e4): a0 = s + 136, a1 = its shadow byte, s6 = fp, s10 = s + 96, s11 = s + 104. *)
Definition onann_regs_fn (regs regs2 : bvmap 5 word) (fp sp1 F : Z) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 10 = w64 (ONANN_S + 136) /\ YK11.getr regs2 11 = w64 (SHADOW_OFF + (ONANN_S + 136) / 8) /\
  YK11.getr regs2 22 = w64 fp /\
  YK11.getr regs2 26 = w64 (ONANN_S + 96) /\ YK11.getr regs2 27 = w64 (ONANN_S + 104).
(* The first inlined session_lost (+0x424): s5 = now, s6 = s + 112, s10 = its shadow byte. *)
Definition onann_regs_sl1 (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 21 = w64 now /\ YK11.getr regs2 22 = w64 (ONANN_S + 112) /\
  YK11.getr regs2 26 = w64 (SHADOW_OFF + (ONANN_S + 112) / 8).
(* The wake test (+0x470): a0 = the state the code loaded (`lw`: sign-extended), s5 = now. *)
Definition onann_regs_wk (regs regs2 : bvmap 5 word) (now sp1 F st : Z) : Prop :=
  onann_regs_ign regs regs2 sp1 F /\ YK11.getr regs2 10 = w64 st /\ YK11.getr regs2 21 = w64 now.

(* ------------------------------------------------------------------ *)
(* 6. The state at each cut                                            *)
(* ------------------------------------------------------------------ *)

(* The parse cut (+0x19c): the frame taken, its header and shadow bytes written; a's 5 shadow bytes 4 .. 8 are 0
   (a usable); the world is the call's. The registers are the personality cut's (onann_regs_pf). *)
Definition onann_lp_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Bw b : list byte) pos F
    ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw /\
  (forall i, 4 <= i < 9 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0).

(* The ignore cut (+0x1ac): the parse's code was not 0; the world is the call's. *)
Definition onann_ign_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Bw b : list byte) pos F
    ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw /\ onann_ign b = true.

(* The personality cut (+0x1e0): the parse answered 0; the world is the call's; a holds the parse's fields. *)
Definition onann_pf_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (buf : Z) (Bw b : list byte) pos F
    ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw /\ onann_ign b = false /\
  onann_a_ok W2 mem2 F buf b.

(* The spill slots the find_mac loop and the desk notice read: the shadow byte of f + 30 at sp1 + 48, f + 30 at
   sp1 + 56, now at sp1 + 24, a at sp1 + 16. *)
Definition onann_slots_dn (W2 : world segs) (mem2 : word -> option byte) (fp now sp1 F : Z) : Prop :=
  onann_slot W2 mem2 sp1 48 (SHADOW_OFF + (fp + 30) / 8) /\ onann_slot W2 mem2 sp1 56 (fp + 30) /\
  onann_slot W2 mem2 sp1 24 now /\ onann_slot W2 mem2 sp1 16 (F + ONANN_A).

(* The find_mac cut (+0x250): cmd = 0xe1; the world after the personality's store. *)
Definition onann_fm_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (fp buf now sp1 : Z) (Bw b : list byte)
    pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) (onann_w1 timg_B Bw b) /\ onann_ign b = false /\
  DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE_SESSION /\
  onann_a_ok W2 mem2 F buf b /\ onann_slots_dn W2 mem2 fp now sp1 F.

(* The desk notice cut (+0x300): the world after the personality's store; a5 = off (onann_regs_dn). *)
Definition onann_dn_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (fp buf now sp1 : Z) (Bw b : list byte)
    pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) (onann_w1 timg_B Bw b) /\ onann_ign b = false /\
  onann_a_ok W2 mem2 F buf b /\ onann_slots_dn W2 mem2 fp now sp1 F.

(* The spill slots the arms after the desk notice read: the shadow byte of s + 112 at sp1 + 32 and s + 112 at
   sp1 + 40 (stored at +0x36c and +0x370). *)
Definition onann_slots_arm (W2 : world segs) (mem2 : word -> option byte) (sp1 : Z) : Prop :=
  onann_slot W2 mem2 sp1 32 (SHADOW_OFF + (ONANN_S + 112) / 8) /\ onann_slot W2 mem2 sp1 40 (ONANN_S + 112).
(* The spill slots the foreign notice reads: the shadow bytes of s + 96 and s + 104 at sp1 + 8 and sp1 + 0 (stored
   at +0x3a4 and +0x3b4). *)
Definition onann_slots_ntf (W2 : world segs) (mem2 : word -> option byte) (sp1 : Z) : Prop :=
  onann_slot W2 mem2 sp1 8 (SHADOW_OFF + (ONANN_S + 96) / 8) /\
  onann_slot W2 mem2 sp1 0 (SHADOW_OFF + (ONANN_S + 104) / 8).

(* The e0 cut (+0x3ec): cmd = 0xe0, the world B2 after the desk notice, the rest of the model; now at sp1 + 24. *)
Definition onann_e0_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (now sp1 : Z) (TF : option TI.tframe)
    (Bw Bw' b B2 : list byte) pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B2 /\ onann_b2 TF Bw b B2 /\
  DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE /\
  onann_k_e0 timg_B TF B2 now = Some (Bw', tt) /\
  TW.g_fail_next B2 <= 1 /\ onann_ri B2 /\
  onann_slots_arm W2 mem2 sp1 /\ onann_slot W2 mem2 sp1 24 now.

(* The e1 cut (+0x4a0): cmd = 0xe1, the world B2 after the desk notice, the rest of the model at off; a is still
   the parse's (the foreign notice reads it). *)
Definition onann_e1_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (buf sp1 : Z) (TF : option TI.tframe)
    (Bw Bw' b B2 : list byte) pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B2 /\ onann_b2 TF Bw b B2 /\
  DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE_SESSION /\
  onann_k_e1 timg_B TF B2 (onann_off (onann_w1 timg_B Bw b) b) b = Some (Bw', tt) /\
  TW.g_fail_next B2 <= 1 /\
  onann_a_ok W2 mem2 F buf b /\
  onann_slots_arm W2 mem2 sp1 /\ onann_slots_ntf W2 mem2 sp1 /\ onann_slot W2 mem2 sp1 16 (F + ONANN_A).

(* The first inlined session_lost (+0x424): the world Bx = set_S_foreign B2 0, whose state is S_ONLINE. *)
Definition onann_sl1_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (now : Z) (TF : option TI.tframe)
    (Bw Bw' b B2 : list byte) pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) (TW.set_S_foreign B2 0) /\ onann_b2 TF Bw b B2 /\
  TW.S_state (TW.set_S_foreign B2 0) = TS0.DIGINET_S_ONLINE /\
  onann_k_sl1 timg_B TF (TW.set_S_foreign B2 0) now = Some (Bw', tt) /\
  TW.g_fail_next (TW.set_S_foreign B2 0) <= 1 /\ onann_ri (TW.set_S_foreign B2 0).

(* The wake test (+0x470): the e0 arm's world B4 (a0 = its state, onann_regs_wk). *)
Definition onann_wk_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (now : Z) (TF : option TI.tframe)
    (Bw Bw' b B4 : list byte) pos F ly2 S2 W2 mem2 md2 e : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e /\
  e + WAKE_EV <= ONANN_EV /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B4 /\
  onann_k_wk timg_B TF B4 now = Some (Bw', tt) /\
  TW.g_fail_next B4 <= 1 /\ onann_ri B4.

(* The foreign cut (+0x4e4): off < 0; the world B2 after the desk notice (the store of :216 is the piece's); the
   rest of the model at set_S_foreign B2 1; a is still the parse's. *)
Definition onann_fn_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (buf sp1 : Z) (TF : option TI.tframe)
    (Bw Bw' b B2 : list byte) pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B2 /\ onann_b2 TF Bw b B2 /\
  onann_k_fn timg_B TF (TW.set_S_foreign B2 1) b = Some (Bw', tt) /\
  TW.g_fail_next B2 <= 1 /\
  onann_a_ok W2 mem2 F buf b /\
  onann_slots_arm W2 mem2 sp1 /\ onann_slots_ntf W2 mem2 sp1 /\ onann_slot W2 mem2 sp1 16 (F + ONANN_A).

(* The second inlined session_lost (+0x5b4): the foreign notice's world B3 (an N_FOREIGN notice changes GOT.foreign
   only), whose state is S_WAKING or S_ONLINE. *)
Definition onann_sl2_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (TF : option TI.tframe)
    (Bw Bw' b B2 B3 : list byte) pos F ly2 S2 W2 mem2 md2 : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B3 /\ onann_b2 TF Bw b B2 /\
  TSS.call_notify timg_B TF (TW.set_S_foreign B2 1) (onann_fntc (TW.set_S_foreign B2 1) b) = Some (B3, tt) /\
  (exists d, B3 = TW.set_GOT_foreign (TW.set_S_foreign B2 1) d) /\
  (TW.S_state B3 = TS0.DIGINET_S_ONLINE \/ TW.S_state B3 = TS0.DIGINET_S_WAKING) /\
  TSS.session_lost_m timg_B TF B3 TS0.DIGINET_R_FOREIGN = Some (Bw', tt) /\
  TW.g_fail_next B3 <= 1.

(* The release cuts (+0x5f4, +0x61c, +0x644): every path's model is done; the post's X already holds. *)
Definition onann_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Bw Bw' b : list byte) pos F
    ly2 S2 W2 mem2 md2 e : Prop :=
  onann_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* ------------------------------------------------------------------ *)
(* 7. The cut statements                                               *)
(* ------------------------------------------------------------------ *)

(* The post at the current machine state: transport_onann_post at the entry's facts. *)
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b :=
  (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Local Notation AT pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

Definition onann_arel_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
    onann_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_AREL regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_nrel_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
    onann_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_NREL regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_fnrel_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
    onann_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_FNREL regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_lp_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_lp_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 ->
    onann_regs_pf regs regs2 fp now sp1 F ->
    SRr segs W2 (AT ONANN_LP regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_ign_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_ign_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 ->
    onann_regs_ign regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_IGN regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_pf_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_pf_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf Bw b pos F ly2 S2 W2 mem2 md2 ->
    onann_regs_pf regs regs2 fp now sp1 F ->
    SRr segs W2 (AT ONANN_PF regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_fm_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_fm_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now sp1 Bw b pos F ly2 S2 W2 mem2 md2 ->
    onann_regs_fm regs regs2 fp sp1 F b ->
    SRr segs W2 (AT ONANN_FM regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_dn_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_dn_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now sp1 Bw b pos F ly2 S2 W2 mem2 md2 ->
    onann_regs_dn regs regs2 fp sp1 F (onann_off (onann_w1 timg_B Bw b) b) b ->
    SRr segs W2 (AT ONANN_DN regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_e0_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B2 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_e0_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now sp1 TF Bw Bw' b B2 pos F
      ly2 S2 W2 mem2 md2 ->
    onann_regs_ign regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_E0 regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_e1_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B2 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_e1_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf sp1 TF Bw Bw' b B2 pos F
      ly2 S2 W2 mem2 md2 ->
    onann_regs_e1 regs regs2 fp sp1 F (onann_off (onann_w1 timg_B Bw b) b) ->
    SRr segs W2 (AT ONANN_E1 regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_sl1_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B2 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_sl1_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now TF Bw Bw' b B2 pos F
      ly2 S2 W2 mem2 md2 ->
    onann_regs_sl1 regs regs2 now sp1 F ->
    SRr segs W2 (AT ONANN_SL1 regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_wk_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B4 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_wk_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now TF Bw Bw' b B4 pos F
      ly2 S2 W2 mem2 md2 e ->
    onann_regs_wk regs regs2 now sp1 F (TW.S_state B4) ->
    SRr segs W2 (AT ONANN_WK regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_fn_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B2 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_fn_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf sp1 TF Bw Bw' b B2 pos F
      ly2 S2 W2 mem2 md2 ->
    onann_regs_fn regs regs2 fp sp1 F ->
    SRr segs W2 (AT ONANN_FN regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition onann_sl2_at : Prop :=
  onann_laws -> onann_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B2 B3 : list byte) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onann_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_sl2_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' b B2 B3 pos F
      ly2 S2 W2 mem2 md2 ->
    onann_regs_ign regs regs2 sp1 F ->
    SRr segs W2 (AT ONANN_SL2 regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* ------------------------------------------------------------------ *)
(* 8. The pieces and the composition                                   *)
(* ------------------------------------------------------------------ *)

Definition onann_tail_stmt : Prop := onann_arel_at /\ onann_nrel_at /\ onann_fnrel_at.
Definition onann_ign_stmt : Prop := onann_arel_at -> onann_ign_at.
Definition onann_sl2_stmt : Prop := onann_fnrel_at -> onann_sl2_at.
Definition onann_fn_stmt : Prop := onann_sl2_at -> onann_fnrel_at -> onann_fn_at.
Definition onann_e1_stmt : Prop := onann_fn_at -> onann_nrel_at -> onann_e1_at.
Definition onann_wk_stmt : Prop := onann_nrel_at -> onann_wk_at.
Definition onann_sl1_stmt : Prop := onann_wk_at -> onann_sl1_at.
Definition onann_e0_stmt : Prop := onann_sl1_at -> onann_wk_at -> onann_e0_at.
Definition onann_dn_stmt : Prop := onann_e0_at -> onann_e1_at -> onann_dn_at.
Definition onann_fm_stmt : Prop := onann_dn_at -> onann_fm_at.
Definition onann_pf_stmt : Prop := onann_fm_at -> onann_dn_at -> onann_pf_at.
Definition onann_lp_stmt : Prop := onann_ign_at -> onann_pf_at -> onann_lp_at.
Definition onann_head_stmt : Prop := onann_lp_at -> @transport_on_announce_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma onann_holds_of :
  onann_head_stmt -> onann_lp_stmt -> onann_ign_stmt -> onann_pf_stmt -> onann_fm_stmt -> onann_dn_stmt ->
  onann_e0_stmt ->
  onann_sl1_stmt -> onann_wk_stmt -> onann_e1_stmt -> onann_fn_stmt -> onann_sl2_stmt -> onann_tail_stmt ->
  @transport_on_announce_cg_holds_stmt fx rc B MT.
Proof.
intros HEAD LP IGN PF FM DN E0 SL1 WK E1 FN SL2 (AREL & NREL & FNREL).
pose proof (WK NREL) as WK'. pose proof (SL1 WK') as SL1'. pose proof (E0 SL1' WK') as E0'.
pose proof (SL2 FNREL) as SL2'. pose proof (FN SL2' FNREL) as FN'. pose proof (E1 FN' NREL) as E1'.
pose proof (DN E0' E1') as DN'. pose proof (FM DN') as FM'. pose proof (PF FM' DN') as PF'.
exact (HEAD (LP (IGN AREL) PF')).
Qed.
End cut.

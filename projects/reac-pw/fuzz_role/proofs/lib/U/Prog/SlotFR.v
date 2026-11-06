(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths, module names, addresses and numbers changed; 257 of its 295 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/U/Prog/SlotInvCF.v, with its module paths and numbers changed; 35 of its 157 lines of code are new or changed and 173 lines of the source are left out. *)
(* The slot frame of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan, [0x12ec0, 0x14224)): ghost values, the frame
   FR over a list hb of live harness blocks, CUTST, Inv_ENTRY, Post, Hcut and the slot obligation. Statement text:
   no function is proved here; the cut invariants are stated over CUTST in their own file.
   The plain file (lib/Prog/SlotFR.v) with the UBSan numbers below. Taken from reac-pw/fuzz_pin's U/Prog/SlotInv.v, itself libreac/fuzz_ctrl's released Prog/SlotInv.v (origin/ossv/recipes
   25e3d17bdb50, lines 98-194 and 318-393), with role's UBSan numbers:
   - Frame (0x12ec0 `addi sp,sp,-0x220`): SLOT_FRAME 544; the prologue saves ra, s0-s11 at S-8 .. S-104
     (0x12ec4 `sd ra,0x218(sp)` .. 0x12ef4 `sd s11,0x1b8(sp)`), SLOT_SAVE 104: ctrl's thirteen saved registers.
   - The FP state: a cut and Post hold for the FP state of their configuration (any FP registers, any fflags) with
     rounding mode 0 (frm_zero), as the frame's lib_contract_body takes any fx' with frm_zero (fp_csr fx') at its
     return. The body between the second malloc and the first free runs FP code (fadd.d, fcvt.l.d, fle.d and the
     soft-float routines accrue fflags and write the FP registers), so a cut after it is not at the entry's FP
     state. Inv_ENTRY carries frm_zero of the entry FP state, which the frame gives.
   - resb_room: the request bound is 2^26 (AllocRoom.CAPOK_big), for any hb of at most 16 blocks and 2^24 bytes:
     role's two requests are 19744 bytes and the pod length (at most 16384) with one block live. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0 Contract FrameAPI.
Import ListNotations.
Open Scope Z_scope.

Definition SLOT_FRAME : Z := 544.
Definition SLOT_SAVE : Z := 104.
Definition SLOT_K : Z := SLOT_STACK.

(* Ghost values fixed at ENTRY: the input bytes (n = length), p, S, the entry registers (s0-s11, gp, tp by
   getr), the entry layout, allocator state, memory and model (B0 = blocks g_L g_A) and the entry bound. *)
Record ghost := Ghost {
  g_in : list byte;
  g_p : Z;
  g_S : Z;
  g_regs : bvmap 5 word;
  g_L : layout;
  g_A : astate;
  g_mem : word -> option byte;
  g_md : Model;
  g_b : sbound
}.

Definition g_n (g : ghost) : Z := Z.of_nat (length (g_in g)).
Definition fsp (g : ghost) : Z := g_S g - SLOT_FRAME.
Definition spk (g : ghost) (k : Z) : Z := fsp g + k.

(* Resources (sbound): the live harness blocks hb on top of the entry bound. *)
Definition hb_bytes (hb : list (Z * Z)) : Z := fold_right Z.add 0 (map snd hb).
Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).
(* The slot's entry bound: the halts frame gives sb_cap = CAPMAX, the agreement frame sb_cap = CAP_AG; the slot
   needs only a cap between 128 and CAPMAX. *)
Definition slot_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.
Definition RESB (b0 : sbound) (hb : list (Z * Z)) (A : astate) : Prop := res_ok_slots A (sb_hb b0 hb).
Definition RES_END (b0 : sbound) (A : astate) : Prop := res_ok_slots A b0.

Lemma hb_bytes_cons : forall x l, hb_bytes (x :: l) = snd x + hb_bytes l.
Proof. intros x l. reflexivity. Qed.

Lemma sb_hb_perm : forall b0 h h', Permutation h h' -> sb_hb b0 h = sb_hb b0 h'.
Proof.
  intros b0 h h' HP. unfold sb_hb. rewrite (Permutation_length HP).
  assert (E : hb_bytes h = hb_bytes h').
  { induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
    - reflexivity.
    - rewrite IH. reflexivity.
    - ring.
    - rewrite IH1, IH2. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* The request bound is 2^26 for any hb of at most 16 blocks and 2^24 bytes (CAPOK_big). *)
Lemma resb_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 26 -> room_slots (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [exact (proj1 Hn)|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 28 - 2 ^ 13) n); [lia | lia | lia | exact CAPOK_big].
Qed.

Lemma resb_malloc : forall b0 hb hb' A res n, Permutation hb' ((res, n) :: hb) ->
  res_ok_slots A (sb_malloc (sb_hb b0 hb) n) -> RESB b0 hb' A.
Proof.
  intros b0 hb hb' A res n HP H. unfold RESB. rewrite (sb_hb_perm b0 _ _ HP).
  replace (sb_hb b0 ((res, n) :: hb)) with (sb_malloc (sb_hb b0 hb) n); [exact H|].
  unfold sb_malloc, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_free : forall b0 hb hb' A q n, Permutation hb ((q, n) :: hb') ->
  res_ok_slots A (sb_free (sb_hb b0 hb) n) -> RESB b0 hb' A.
Proof.
  intros b0 hb hb' A q n HP H. unfold RESB.
  rewrite (sb_hb_perm b0 _ _ HP) in H.
  replace (sb_hb b0 hb') with (sb_free (sb_hb b0 ((q, n) :: hb')) n); [exact H|].
  unfold sb_free, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_end : forall b0 A, RESB b0 [] A -> RES_END b0 A.
Proof.
  intros b0 A H. unfold RESB, RES_END in *.
  replace b0 with (sb_hb b0 []); [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

Lemma resb_start : forall b0 A, res_ok_slots A b0 -> RESB b0 [] A.
Proof.
  intros b0 A H. unfold RESB. replace (sb_hb b0 []) with b0; [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

(* Registers. Register numbers: ra 1, sp 2, gp 3, tp 4, s0 8, s1 9, a0-a7 10-17, s2-s11 18-27. *)
Definition rg (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Let API := APIf rc.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MI (m : word -> option byte) : Prop := ro_agree segs m.
Definition relro (m : word -> option byte) : Prop := G_img_c B frame_RELRO m.

(* [S - 104, S): s11, s10, .., s2, s1, s0, ra (0x12ef4 `sd s11,0x1b8(sp)` .. 0x12ec4 `sd ra,0x218(sp)`). *)
Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 27) ++ le8 (getr (g_regs g) 26) ++ le8 (getr (g_regs g) 25) ++
  le8 (getr (g_regs g) 24) ++ le8 (getr (g_regs g) 23) ++ le8 (getr (g_regs g) 22) ++
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++
  le8 (getr (g_regs g) 18) ++ le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* GV: the ghost facts. *)
Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B).

(* FR: sp, gp, tp, the saved registers, the window, ro_agree and RELRO, the allocator, no byte changed outside
   [S - K, S), A and the live harness blocks hb, the resources (ctrl's FR, conjunct for conjunct). *)
Definition FR (g : ghost) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  GV g /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
  bytes_at rsegs mem (g_S g - SLOT_SAVE) (saved_bytes g) /\
  stk rsegs mem (g_S g - SLOT_K) (g_S g) /\
  MI mem /\ relro mem /\
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (g_md g)) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte segs mem (a + i) = mbyte segs (g_mem g) (a + i)) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  sink_none B mem md /\ RESB (g_b g) hb A /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at segs mem a).

(* A cut state at pc: some FP state with rounding mode 0, FR with the live harness blocks hb, the allocator's
   blocks = hb and the entry blocks, and the cut's own facts P. *)
Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    frm_zero (@YK11.fp_csr fx') /\
    FR g hb L A regs mem md /\
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) /\
    P regs mem.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g) /\
  frm_zero fp_csr.

(* RET: lib_post with G = [], stk = SLOT_STACK, from the ENTRY state, at some FP state with rounding mode 0. *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    frm_zero (@YK11.fp_csr fx') /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

(* H(X): every configuration of cut X runs, in the SR sense, to Post. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).

(* The slot obligation for this function: G = frame_G = [], GI trivial (FrameAPI.frame_ubsan's last conjunct). *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

End Slot.

(* Cut invariants of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (UBSan, [0x12cbc, 0x12eb8)): ghost values, the frame
   FR, CUTST, Post, Hcut, and one Inv_<cut> per cut. Statement text: no function is proved here. The plain file
   (lib/Prog/SlotInv.v) with the UBSan numbers below; ctrl's U/Prog/SlotInv.v is the same text as its plain one but
   for the numerals, and so is this one.
   Taken from libreac/fuzz_ctrl's released Prog/SlotInv.v (origin/ossv/recipes 25e3d17bdb50, lines 98-194 and
   318-393; ctrl's frame interface files are byte-identical to knock's, which pin's frame copies), with pin's numbers:
   - Frame (0x12cbc `addi sp,sp,-0x50`): SLOT_FRAME 80; the prologue saves ra, s0-s5 at S-8 .. S-56 (SLOT_SAVE 56;
     ctrl saved 13 registers at S - 104). s6-s11 are never written by the harness and every callee keeps them, so
     the cuts carry them as registers (KS) instead of saved bytes.
   - frame_facts: pin's U/FrameAPI.frame_facts_ubsan (ctrl defined its own frame_facts; the same conjuncts, in the
     order of the knock frame's frame_ubsan). ctrl's frame_ubsan_split / slot_obligation are U/FrameAPI's
     frame_ubsan_split here.
   - resb_room: the request bound is 2^26 (pin mallocs n + 1 <= 2^26 - 1 bytes), from AllocRoom.CAPOK_big, where
     ctrl's was 2^20 from CAPOK_small.
   - Cuts: ENTRY (0x12cbc); K12d50, malloc's return address (0x12d4c `jal malloc`); K12e24, the join of the
     rc <> 0 branch (0x12e08 `bnez s3,0x12e24`) and the fall-through after check_label, just before free's argument
     move (0x12e24 `mv a0,s0`; 0x12e28 `jal free`); RET = Post. The n >= 2^26 return (0x12ce0 `bnez a2,0x12e2c`) does
     not pass a cut: as ctrl's slot_early, the slot runs it as one evt from ENTRY to ra.
   - Segments (U/Prog/LLVMFuzzerTestOneInput_c.v): ENTRY -> K12d50 (prologue, flags, the UBSan checks on data + 1 and
     data + n, memchr, malloc(k + 1) by ctrl's b1_malloc_call), K12d50 -> K12e24 (pin_mid_contract's evt),
     K12e24 -> RET (free by ctrl's b8_free_call, `mv a0,zero`, epilogue). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
Import ListNotations.
Open Scope Z_scope.

Definition SLOT_FRAME : Z := 80.
Definition SLOT_SAVE : Z := 56.
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

(* The pin quantities of the input (pin_spec): k = fuzz_str's length (the malloc request is k + 1), the flags
   byte, and the address of the rest (data + 1; data itself when the input is empty, where k = 0). *)
Definition g_k (g : ghost) : Z := Z.of_nat (pin_k (g_in g)).
Definition g_fl (g : ghost) : Z := pin_flags (g_in g).
Definition g_src (g : ghost) : Z := g_p g + Z.min 1 (g_n g).

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

(* pin's one request is k + 1 <= 2^26 - 1 bytes: the bound is 2^26 (ctrl: 2^20 from CAPOK_small). *)
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
Definition hb1 (phi n : Z) : list (Z * Z) := [(phi, n)].

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

(* [S - 56, S): s5, s4, s3, s2, s1, s0, ra (0x12cdc `sd s5,24(sp)` .. 0x12cc0 `sd ra,72(sp)`). *)
Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++ le8 (getr (g_regs g) 18) ++
  le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* KS: the s registers the harness never writes, s6-s11, still hold their entry values. *)
Definition KS (g : ghost) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = getr (g_regs g) 22 /\ getr regs 23 = getr (g_regs g) 23 /\ getr regs 24 = getr (g_regs g) 24 /\
  getr regs 25 = getr (g_regs g) 25 /\ getr regs 26 = getr (g_regs g) 26 /\ getr regs 27 = getr (g_regs g) 27.

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

Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FR g hb L A regs mem md /\
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) /\
    P regs mem.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g).

(* RET: lib_post with G = [], stk = SLOT_STACK, from the ENTRY state. *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

(* H(X): every configuration of cut X runs, in the SR sense, to Post. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).

(* The slot obligation for this function: G = frame_G = [], GI trivial (U/FrameAPI.frame_ubsan's last conjunct). *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

(* K12d50, malloc's return (0x12d4c `jal malloc` with a0 = k + 1): phi = the result, nonzero (malloc_ret), the one
   live harness block (phi, k + 1); s2 = k (0x12d44 `sub s2,a0,s0` or n - 1 / 0), s1 = the rest's address (0x12d00
   `mv s1,s0` after 0x12cec `addi s0,s1,1`; data when the input is empty), s3 = the flags byte (0x12cf8
   `lbu s3,0(s1)`, 0 when empty). The UBSan registers differ from the plain build's: k in s2, the rest in s1. *)
Definition Inv_K12d50 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x12d50 (hb1 phi (g_k g + 1)) (fun regs m =>
    rg regs 10 phi /\ phi <> 0 /\ rg regs 18 (g_k g) /\ rg regs 9 (g_src g) /\ rg regs 19 (g_fl g) /\ KS g regs) c.

(* K12e24, the join before free: s0 = phi (0x12d54 `mv s0,a0`), still the one live harness block. *)
Definition Inv_K12e24 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x12e24 (hb1 phi (g_k g + 1)) (fun regs m => rg regs 8 phi /\ KS g regs) c.

End Slot.

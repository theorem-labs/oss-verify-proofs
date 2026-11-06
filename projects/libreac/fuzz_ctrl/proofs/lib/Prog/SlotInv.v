(* Cut invariants of fuzz_ctrl LLVMFuzzerTestOneInput (plain, [0x131f8, 0x13e1c)): ghost values, the frame FR,
   CUTST, Post, Hcut and one Inv_<cut> per cut of slot-plan.md section 3 (ENTRY, the 84 K cuts, RET = Post). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...). Every pc, frame offset, register
   and image address below is the v1.9.0 one, from the plain segment table of record
   v190-segment-table-plain.md (a working note, not in this delivery) (v190map-plain/out/plain.json) and the v1.9.0 .symtab; the
   v1.9.0 listing is the authority for each cut body. rule 24: no function proved.
   - Frame: 1936 bytes (0x131f8 `addi sp,sp,-0x790`), SLOT_FRAME 1936; the saved registers stay at S - 104. Frame
     objects move by live range (table 7a / A1): our 60->76, frag 66->82 (+19: 85->101), id 138->154 (141->157),
     out/blk/before 176->192, p 1736->1752, n/q/ports 1672/1676/1680->1688/1692/1696, ev 1668->1684, fuzz_frame
     pl/pll/addr 1720/1712/1734->1736/1728/1750, type_filler 48->24; main `count` 1808->1792 (K132ac) but `code` and
     row_of_block `count` 1808->1824 (PZ, K13660, K13d38); round_trip pll/ports 1776/1780/1784->40/44/48 and addr
     1720->1824 (K133cc, K13408, K13478); `a` / check_ports `first` 1776->1792 (QB, K13d58, K13d6c).
   - Registers (table 6a): n - c s7->s11 (CUR); the round-trip constants s8/s9/s10/s11->s7/s8/s9/s10 (RT);
     left - h s1->s11 and the body pointer s3->s0, spilled to [sp+32] at 0x136e0 (FCr at K136d4, FC after);
     sum_ok s0->s1 (V0); is_8819 s11->s0 (VC), which 0x13b1c `li s0,-1` overwrites, so EQ / CC7 carry VCm (VC
     without it); K136d4 carries LIp (CUR without the length register, which 0x136b0 overwrote).
   - FSb is restated on v1.9.0's `first` and SlotModel.v's v1.9 fstate (have, nb, body; comment at FSb): have
     [sp+16], nb in s3, body at sp+40; FSb / FSj / IFS take `regs` (before `m`), FC takes `m`. Positions kept in
     every Definition that existed in v1.8; CURp, LIp, FCr and VCm are new.
   - K13598 stays at 0x13598 (comment at Inv_K13598), so its name is kept; the alignment pc 0x135a8 is after the new
     memset.
   - Cut renames, v1.8 -> v1.9 (each with its _at form): K135a0->K135b0, K135b0->K135c0, K135e0->K135f0,
     K13604->K13614, K13614->K13624, K13628->K13638, K13638->K13648, K13650->K13660, K1368c->K13694,
     K136cc->K136d4, K136ec->K136f8, K13700->K1370c, K13728->K13734, K1373c->K13748, K13740->K1374c,
     K137bc->K137c8, K137cc->K137d8, K137e0->K137ec, K137ec->K137f8, K13824->K13830, K13868->K13874,
     K138b8->K138c4, K138bc->K138c8, K138cc->K138d8, K138e8->K138f4, K13904->K13910, K13908->K13914,
     K13944->K13950, K139b4->K139e4, K139b8->K139e8, K13a50->K13a80, K13a64->K13a94, K13a78->K13aa8,
     K13ac0->K13af0, K13b34->K13b64, K13b50->K13b80, K13b68->K13b98, K13b78->K13ba8, K13ba8->K13bd8,
     K13c10->K13c40, K13c70->K13ca0, K13c90->K13cc0, K13cc4->K13cf4, K13cdc->K13d0c, K13d08->K13d38,
     K13d1c->K13d4c, K13d28->K13d58, K13d3c->K13d6c, K13d40->K13d70, K13d4c->K13d7c, K13d50->K13d80,
     K13d5c->K13d8c, K13d68->K13d98, K13d80->K13db4, K13d98->K13dcc, K13d9c->K13dd0 (56). The 27 cuts before
     0x13598 and K13598 keep their pcs and names. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcReply RcIdentModel RcFrag RcLeaf RcPorts
  RcDecl RcClassify
  reac_ctrl_kind_name_c reac_ctrl_classify_box_frame_c.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* frame_plain (FrameAPI.v) without its last conjunct, and that conjunct (the slot's obligation). *)
Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x1649c /\ ms_free B = 0x1635c /\ ms_realloc B = None /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x51170 /\ ms_got_guard B = 0x1fb80 /\
  ms_ctx B = 0x51208 /\ ms_lock B = 0x51200 /\ ms_libc B = 0x51190 /\ ms_size_classes B = 0x10788 /\
  ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10728 /\ ms_debruijn B = 0x10704 /\ ms_tp B = 0x30f00 /\
  ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\
  @sk_ofl_head SH = 0x515c0 /\ @sk_ofl_lock SK = 0x515b8 /\ @sk_threaded SK = 0x51190 + 1 /\
  empty = 0x30e10 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX) /\
  ms_debruijn_len B = 132 /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition slot_obligation (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
    (forall a, in_globals G a -> in_globals frame_G a) ->
    G_local_c B G GI ->
    (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
    (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
       @lib_contract_g fx rc LS B (API rc) SH SK G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
    Statements.plain_halts.

Lemma frame_plain_split : frame_plain -> exists B API LS SH SK ra empty,
  frame_facts B API LS SH SK ra empty /\ slot_obligation B API LS SH SK ra empty.
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts, slot_obligation.
  assert (R0 : forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX)
    by tauto.
  assert (HR : forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\
                 128 <= sb_cap b <= CAPMAX).
  { intros b n Hb. destruct (R0 b n Hb) as (Ha & Hb' & Hc). rewrite Hc. unfold CAPMAX. lia. }
  clear R0. tauto.
Qed.

Definition SLOT_FRAME : Z := 1936.
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

Definition g_n (g : ghost) : Z := nlen (g_in g).
Definition fsp (g : ghost) : Z := g_S g - SLOT_FRAME.
Definition spk (g : ghost) (k : Z) : Z := fsp g + k.
Definition z8 : byte := Z_to_bv 8 0.

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

Lemma resb_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 -> room_slots (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [exact (proj1 Hn)|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
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

(* Registers and memory cells. Register numbers: ra 1, sp 2, gp 3, tp 4, s0 8, s1 9, a0-a7 10-17,
   s2-s11 18-27. *)
Definition rg (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.
Definition q64 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Definition u32 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le4 (Z_to_bv 64 v)).
Definition u16 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le2 (Z_to_bv 64 v)).
Definition b8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a [Z_to_bv 8 v].
Definition hb1 (phi n : Z) : list (Z * Z) := [(phi, n)].

(* Bundles of slot-plan.md 3.1. v1.9.0: the length n - c is in s11 (0x13258 `mv s11, a1`; v1.8 s7), and the
   frame objects our / id / frag are 16 bytes higher (sp+76 / sp+154 / sp+82). *)
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ rg regs 21 (g_p g + c) /\ rg regs 27 (g_n g - c).
Definition OURb (g : ghost) (m : word -> option byte) : Prop := bytes_at rsegs m (spk g 76) (OUR (g_in g)).
Definition IDB (g : ghost) (m : word -> option byte) (idb : list byte) : Prop := bytes_at rsegs m (spk g 154) idb.
Definition FGB (g : ghost) (m : word -> option byte) (st : list byte) : Prop := bytes_at rsegs m (spk g 82) st.
Definition M7 (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 8) 0xfffffff9fffffff9.

(* Round trip. v1.9.0 allocates the constants one register lower: 0x132f0 `li s7,7`, 0x132fc `li s8,1`,
   0x132f8 `li s9,0x24`, 0x132f4 / 0x13308 `lui s10,0xe38f; slli s10,s10,4` (v1.8 s8 / s9 / s10 / s11). *)
Definition RT (g : ghost) (regs : bvmap 5 word) : Prop :=
  rg regs 8 (mrow (g_in g)) /\ rg regs 18 BOXA /\ rg regs 19 CNT16 /\ rg regs 23 7 /\ rg regs 24 1 /\
  rg regs 25 36 /\ rg regs 26 0xe38f0000.
Definition rnb (g : ghost) (b : nat) : Z := rt_n (g_in g) (Z.of_nat b).
Definition rFb (g : ghost) (b : nat) : list byte := rt_F (g_in g) (Z.of_nat b).
Definition rgb (g : ghost) (b : nat) : list byte := rt_g (g_in g) (Z.of_nat b).
Definition RB (g : ghost) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR g 7 regs /\ OURb g m /\ RT g regs /\ rg regs 9 (Z.of_nat b) /\ IDB g m idb /\ FGB g m fgb.
Definition RS (g : ghost) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g b (RID (g_in g) b) (RFG (g_in g) b) regs m.
Definition RFb (g : ghost) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  RB g b idb fgb regs m /\ rnb g b <> 0 /\ rg regs 20 phi /\ bytes_at rsegs m phi (rFb g b).
Definition RFx (g : ghost) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  RFb g b idb fgb phi regs m /\ rg regs 22 (rnb g b).
Definition RF (g : ghost) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx g b (RID (g_in g) b) (RFG (g_in g) b) phi regs m.

(* Frame loop, turn j. *)
Definition IDb (g : ghost) (idb : list byte) (m : word -> option byte) : Prop :=
  IDB g m idb /\ RcIdentModel.id_ok idb.
Definition FGb (g : ghost) (st : list byte) (m : word -> option byte) : Prop := FGB g m st /\ frag_ok st.
(* FS_j in v1.9.0's `first` (40 bytes; DWARF: have at sp+16, the length byte nb in s3, the 35-byte body buffer at
   sp+40). have is [sp+16], 8-byte accesses (0x13680 `sd zero,16(sp)`, 0x13a70 `sd a0,16(sp)` with a0 = 1, read
   0x1397c `ld a0,16(sp)`); nb is s3, never spilled in the loop (0x1367c `mv s3,zero`, 0x13a74 `mv s3,s8` with
   s8 = Phi[26], read 0x13960 `mv a6,s3`); the body is the nb bytes at sp+40 that 0x13a68 memcpy(sp+40, Phi+27,
   Phi[26]) writes (the bytes past nb are not modelled; 0x13598's memset zeroes 35 bytes before the loop). The
   ubsan bundle's shape, with nb in a register where ubsan keeps it in memory. *)
Definition FSb (g : ghost) (s : fstate) (st : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  q64 m (spk g 16) (fs_have s) /\ rg regs 19 (fs_nb s) /\ bytes_at rsegs m (spk g 40) (fs_body s) /\
  Z.of_nat (length (fs_body s)) = fs_nb s /\ FI st s.
Definition IDj (g : ghost) (j : nat) (m : word -> option byte) : Prop := IDb g (t_ID (g_in g) j) m.
Definition FGj (g : ghost) (j : nat) (m : word -> option byte) : Prop := FGb g (t_FG (g_in g) j) m.
Definition FSj (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FSb g (fst_at (g_in g) j) (t_FG (g_in g) j) regs m.
Definition IFS (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj g j m /\ FGj g j m /\ FSj g j regs m.

Definition LI (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 26 (Z.of_nat j) /\ CUR g (t_c (g_in g) j) regs /\ 1 <= t_left (g_in g) j /\
  OURb g m /\ IFS g j regs m /\ M7 g m.
(* K136d4 only: v1.9.0 overwrites the length register s11 with left - h (0x1369c / 0x136b0), so the cursor keeps
   only its pointer s5. *)
Definition CURp (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop := 0 <= c <= g_n g /\ rg regs 21 (g_p g + c).
Definition LIp (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 26 (Z.of_nat j) /\ CURp g (t_c (g_in g) j) regs /\ 1 <= t_left (g_in g) j /\
  OURb g m /\ IFS g j regs m /\ M7 g m.
(* The record cursor: left - h in s11 (v1.8 s1), the body pointer in s0 (v1.8 s3) until 0x136e0 `sd s0,32(sp)`
   spills it, then [sp+32] (reloaded 0x13da0 `ld s5,32(sp)`); FCr is the form at K136d4, before the spill. *)
Definition FCr (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop :=
  rg regs 27 (t_left (g_in g) j - t_h (g_in g) j) /\ rg regs 8 (g_p g + t_body (g_in g) j) /\
  rg regs 20 (t_len (g_in g) j).
Definition FC (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 27 (t_left (g_in g) j - t_h (g_in g) j) /\ q64 m (spk g 32) (g_p g + t_body (g_in g) j) /\
  rg regs 20 (t_len (g_in g) j).
Definition FT (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 26 (Z.of_nat j) /\ FC g j regs m /\ rg regs 21 phi /\
  bytes_at rsegs m phi (t_phi (g_in g) j) /\ OURb g m /\ M7 g m.
Definition V7 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 23 (t_k (g_in g) j).
Definition V9 (phi : Z) (regs : bvmap 5 word) : Prop := rg regs 25 (phi + 18).
(* v1.9.0: sum_ok in s1 (0x1379c `seqz s1,a0`; v1.8 s0), is_8819 in s0 (0x1372c `seqz s0,a0`; v1.8 s11), type_filler
   at sp+24 (0x137c0 `sd a2,24(sp)`; v1.8 sp+48), the parsed block p at sp+1752. *)
Definition V0 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 9 (b2z (t_sum_ok (g_in g) j)).
Definition V2 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 18 (b2z (t_big (g_in g) j)).
Definition V2m (regs : bvmap 5 word) : Prop := rg regs 18 (-7).
Definition VC (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 8 (b2z (t_8819 (g_in g) j)) /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
  q64 m (spk g 24) (b2z (t_TF (g_in g) j)) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j).
(* VC without is_8819: 0x13b1c `li s0,-1` (headamp check) overwrites s0, and K13ca0 is also reached from 0x13a80
   with s0 = 0, so EQ / CC7 (K13b64 .. K13d8c) keep only these three. *)
Definition VCm (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
  q64 m (spk g 24) (b2z (t_TF (g_in g) j)) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j).
Definition FV (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  V7 g j regs /\ V9 phi regs /\ V0 g j regs /\ V2 g j regs /\ VC g j phi regs m.
Definition FB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ FV g j phi regs m.
(* K13a80 without is_8819 (EA), and the parts kept to K13ca0 (CC). *)
Definition EA (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ V7 g j regs /\ V9 phi regs /\ V0 g j regs /\ V2m regs /\ VC g j phi regs m /\
  IFS g (S j) regs m.
Definition EQ (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ V7 g j regs /\ V2m regs /\ VCm g j phi regs m /\ IFS g (S j) regs m /\
  t_8819 (g_in g) j = true.
Definition CC7 (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ V2m regs /\ VCm g j phi regs m /\ IFS g (S j) regs m.
Definition CC (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CC7 g j phi regs m /\ V7 g j regs.
Definition PORTS (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  (t_rp (g_in g) j = 0 ->
     u32 m (spk g 1688) (4 * RcLeaf.n_in (t_pbs (g_in g) j)) /\
     u32 m (spk g 1692) (4 * RcLeaf.n_out (t_pbs (g_in g) j)) /\
     u32 m (spk g 1696) (16 * RcLeaf.bt (t_pbs (g_in g) j) 7)) /\
  (t_rp (g_in g) j <> 0 -> u32 m (spk g 1688) (-7) /\ u32 m (spk g 1692) (-7) /\ u32 m (spk g 1696) (-7)).
Definition QB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  EQ g j phi regs m /\ rg regs 25 (t_rp (g_in g) j) /\ PORTS g j m /\ b8 m (spk g 1792) (t_first (g_in g) j).
Definition RSEL (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CC7 g j phi regs m /\ t_rowsel (g_in g) j = true.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MI (m : word -> option byte) : Prop := ro_agree segs m.
Definition relro (m : word -> option byte) : Prop := G_img_c B frame_RELRO m.

Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 27) ++ le8 (getr (g_regs g) 26) ++ le8 (getr (g_regs g) 25) ++
  le8 (getr (g_regs g) 24) ++ le8 (getr (g_regs g) 23) ++ le8 (getr (g_regs g) 22) ++
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++
  le8 (getr (g_regs g) 18) ++ le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* GV: the ghost facts (S1 of C1). *)
Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B).

(* FR (FR1-FR5 of the plan): sp, gp, tp, the saved registers, the window, ro_agree and RELRO, the allocator,
   no byte changed outside [S - K, S), A and the live harness blocks hb, the resources. *)
Definition FR (g : ghost) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  GV g /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
  bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
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

(* RET: C1's post at pc = R (lib_post with G = [], stk = SLOT_STACK, from the ENTRY state). *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

(* H(X) of plan section 5, for plain cuts and for cuts with one or two indices. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).
Definition Hat {I : Type} (X : ghost -> I -> config -> Prop) (i : I) : Prop :=
  forall g c, X g i c -> SR segs c (Post g).
Definition Hat2 {I J : Type} (X : ghost -> I -> J -> config -> Prop) (i : I) (k : J) : Prop :=
  forall g c, X g i k c -> SR segs c (Post g).

(* The slot obligation for this function: G = frame_G = [], GI trivial. *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

(* ---- 3.2 Start (A) ---- *)
Definition Inv_K1324c_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST g 0x1324c [] (fun regs m =>
    0 <= t <= 5 /\ t <= g_n g /\ rg regs 10 t /\ rg regs 11 (g_n g - t) /\ rg regs 21 (g_p g + t) /\
    rg regs 13 (spk g 76) /\ rg regs 14 7 /\ rg regs 15 6 /\
    bytes_at rsegs m (spk g 76) (firstn (Z.to_nat t) (g_in g))) c.
Definition Inv_K1324c (g : ghost) (c : config) : Prop := exists t, Inv_K1324c_at g t c.
Definition Inv_K13288 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13288 [] (fun regs m =>
    6 <= g_n g /\ OURb g m /\ rg regs 11 (g_n g - 6) /\ rg regs 12 (g_p g + 5) /\ rg regs 21 (g_p g + 6) /\
    rg regs 27 (g_n g - 5)) c.

(* ---- 3.2 Round trip (R); b : nat is the turn ---- *)
Definition RA (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  7 <= g_n g /\ CUR g 7 regs /\ OURb g m.
Definition Inv_K132a0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x132a0 [] (fun regs m => RA g regs m /\ rg regs 8 (mode (g_in g)) /\ rt_on (g_in g) = true) c.
Definition Inv_K132ac (g : ghost) (c : config) : Prop :=
  CUTST g 0x132ac [] (fun regs m => RA g regs m /\ rg regs 8 (mode (g_in g)) /\ rt_on (g_in g) = true /\
    rg regs 10 CAT /\ q64 m (spk g 1792) CAT_N) c.
Definition Inv_K132d4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x132d4 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ IDB g m RcIdentModel.ID0) c.
Definition Inv_K132e4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x132e4 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ IDB g m RcIdentModel.ID0 /\
    FGB g m z72) c.
Definition Inv_K1330c_at (g : ghost) (b : nat) (c : config) : Prop := CUTST g 0x1330c [] (RS g b) c.
Definition Inv_K1330c (g : ghost) (c : config) : Prop := exists b, Inv_K1330c_at g b c.
Definition Inv_K13330_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x13330 [] (fun regs m => RS g b regs m /\ rg regs 10 (rnb g b) /\
    (rnb g b <> 0 -> bytes_at rsegs m (spk g 192) (rFb g b))) c.
Definition Inv_K13330 (g : ghost) (c : config) : Prop := exists b, Inv_K13330_at g b c.
Definition Inv_K13374_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13374 (hb1 phi (rnb g b)) (fun regs m => RS g b regs m /\ rnb g b <> 0 /\
    rg regs 22 (rnb g b) /\ rg regs 10 phi /\ phi <> 0 /\ bytes_at rsegs m (spk g 192) (rFb g b)) c.
Definition Inv_K13374 (g : ghost) (c : config) : Prop := exists b, Inv_K13374_at g b c.
Definition Inv_K13388_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13388 (hb1 phi (rnb g b)) (RF g b phi) c.
Definition Inv_K13388 (g : ghost) (c : config) : Prop := exists b, Inv_K13388_at g b c.
Definition Inv_K13398_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13398 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b)) /\ bytes_at rsegs m (spk g 1752) (rt_B (g_in g) (Z.of_nat b))) c.
Definition Inv_K13398 (g : ghost) (c : config) : Prop := exists b, Inv_K13398_at g b c.
Definition Inv_K133cc_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x133cc (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 3 \/ b = 4)%nat /\
    rt_k (g_in g) (Z.of_nat b) = 5 /\ RcReply.ir (rnb g b) (rgb g b) = true /\ rg regs 10 1 /\
    bytes_at rsegs m (spk g 1824) (RcReply.reply_addr (rgb g b)) /\ q64 m (spk g 1688) (phi + 38) /\
    q64 m (spk g 40) (r_pll (rgb g b))) c.
Definition Inv_K133cc (g : ghost) (c : config) : Prop := exists b, Inv_K133cc_at g b c.
Definition Inv_K13408 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x13408 (hb1 phi (rnb g 6)) (fun regs m =>
    RFx g 6 (RID (g_in g) 6) (RFG (g_in g) 7) phi regs m /\ rt_k (g_in g) 6 = 11 /\
    fg_rf (rnb g 6) (RFG (g_in g) 6) (rgb g 6) = 1 /\ rg regs 10 1 /\
    u16 m (spk g 1824) (RcFrag.fg_addr (RFG (g_in g) 6) (rgb g 6)) /\ q64 m (spk g 1688) (spk g 101) /\
    q64 m (spk g 40) (f_pll (RFG (g_in g) 6) (rgb g 6))) c.
Definition Inv_K133d4_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x133d4 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 5 \/ b = 6)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_K133d4 (g : ghost) (c : config) : Prop := exists b, Inv_K133d4_at g b c.
Definition Inv_K13420_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13420 (hb1 phi (rnb g b)) (fun regs m =>
    RFx g b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) phi regs m /\ (b = 3 \/ b = 4 \/ b = 6)%nat /\
    rg regs 10 1) c.
Definition Inv_K13420 (g : ghost) (c : config) : Prop := exists b, Inv_K13420_at g b c.
Definition Inv_K13428_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13428 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b <= 2)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_K13428 (g : ghost) (c : config) : Prop := exists b, Inv_K13428_at g b c.
Definition Inv_K13464 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x13464 (hb1 phi (rnb g 0)) (fun regs m => RF g 0 phi regs m /\
    rt_k (g_in g) 0 = 9 /\ RcModel.blocksum (skipn 18 (rgb g 0)) = 0 /\ rg regs 10 (mrow (g_in g))) c.
Definition Inv_K13478 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x13478 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 22 (phi + 18) /\ rg regs 10 0 /\
    u32 m (spk g 40) (4 * RcLeaf.n_in (rt_pbs (g_in g))) /\
    u32 m (spk g 44) (4 * RcLeaf.n_out (rt_pbs (g_in g))) /\
    u32 m (spk g 48) (16 * RcLeaf.bt (rt_pbs (g_in g)) 7)) c.
Definition Inv_K134a0 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x134a0 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 22 (phi + 18) /\ rg regs 10 1 /\
    bytes_at rsegs m (spk g 1688) (RcDecl.decl (rt_mb (g_in g)))) c.
Definition Inv_K134b4 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x134b4 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 22 (phi + 18) /\ rg regs 10 0 /\
    bytes_at rsegs m (spk g 1688) (RcDecl.decl (rt_mb (g_in g)))) c.
Definition Inv_K134bc (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x134bc (hb1 phi (rnb g 5)) (fun regs m => RF g 5 phi regs m /\
    rg regs 10 (rt_k (g_in g) 5)) c.
Definition Inv_K134e0 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x134e0 (hb1 phi (rnb g 5)) (fun regs m =>
    RFx g 5 (RID (g_in g) 6) (RFG (g_in g) 6) phi regs m /\ rg regs 10 0) c.
Definition Inv_K134e8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x134e8 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 1 \/ b = 2)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_K134e8 (g : ghost) (c : config) : Prop := exists b, Inv_K134e8_at g b c.
Definition Inv_K13514_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13514 (hb1 phi (rnb g b)) (fun regs m =>
    RB g b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\ rnb g b <> 0 /\ rg regs 20 phi) c.
Definition Inv_K13514 (g : ghost) (c : config) : Prop := exists b, Inv_K13514_at g b c.
Definition Inv_K1351c_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x1351c [] (RB g b (RID (g_in g) (S b)) (RFG (g_in g) (S b))) c.
Definition Inv_K1351c (g : ghost) (c : config) : Prop := exists b, Inv_K1351c_at g b c.
Definition Inv_K13524 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13524 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ IDB g m (RID (g_in g) 7)) c.
Definition Inv_K1358c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1358c [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ IDB g m (RID (g_in g) 7) /\
    rg regs 10 0) c.

(* ---- 3.3 Init and P8 (P) ---- *)
Definition PB (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CUR g (c0 (g_in g)) regs /\ OURb g m.
Definition P0 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  PB g regs m /\ IDB g m RcIdentModel.ID0 /\ FGB g m z72.
Definition PZ (g : ghost) (code : Z) (m : word -> option byte) : Prop :=
  b8 m (spk g 1824) code /\ bytes_at rsegs m (spk g 192) (repeat z8 32).
(* K13598 stays at 0x13598, the target of the four branches into it (0x1329c, 0x13568, 0x1358c, 0x13e14) and of
   the fall-through from 0x13594, before v1.9.0's memset of `first` (0x13598 .. 0x135a4: memset(sp+40, 0, 35));
   PB holds there unchanged, and the memset becomes the head of S_P01 (K13598 -> K135b0) instead of the tail of
   S_A02 / S_A03 / S_R23 / S_R24. *)
Definition Inv_K13598 (g : ghost) (c : config) : Prop := CUTST g 0x13598 [] (PB g) c.
Definition Inv_K135b0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x135b0 [] (fun regs m => PB g regs m /\ IDB g m RcIdentModel.ID0) c.
Definition Inv_K135c0 (g : ghost) (c : config) : Prop := CUTST g 0x135c0 [] (P0 g) c.
Definition Inv_K135f0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x135f0 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 10 (-1)) c.
Definition Inv_K13614 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13614 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 8 (-1) /\ rg regs 10 (-1)) c.
Definition Inv_K13624 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13624 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 10 (-1)) c.
Definition Inv_K13638 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13638 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 8 (-1) /\ rg regs 10 (-1)) c.
Definition Inv_K13648 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13648 [] (fun regs m => P0 g regs m /\ PZ g 0 m /\ rg regs 10 (-1)) c.
Definition Inv_K13660 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13660 [] (fun regs m => P0 g regs m /\ b8 m (spk g 1824) 0 /\
    rg regs 10 reac_ctrl_kind_name_c.QMARK) c.

(* ---- 3.4 Frame loop, turn j (F, I, G); Φ is an existential of the cut ---- *)
Definition FCUT (g : ghost) (pc : Z) (j : nat) (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop :=
  exists phi, CUTST g pc (hb1 phi (t_len (g_in g) j)) (P phi) c.

Definition Inv_K13694_at (g : ghost) (j : nat) (c : config) : Prop := CUTST g 0x13694 [] (LI g j) c.
Definition Inv_K13694 (g : ghost) (c : config) : Prop := exists j, Inv_K13694_at g j c.
Definition Inv_K136d4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x136d4 j (fun phi regs m => LIp g j regs m /\ FCr g j regs /\ rg regs 10 phi /\ phi <> 0) c.
Definition Inv_K136d4 (g : ghost) (c : config) : Prop := exists j, Inv_K136d4_at g j c.
Definition Inv_K136f8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x136f8 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j <> 0 /\ IFS g j regs m) c.
Definition Inv_K136f8 (g : ghost) (c : config) : Prop := exists j, Inv_K136f8_at g j c.
Definition Inv_K13734_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13734 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j = 0 /\ IFS g j regs m) c.
Definition Inv_K13734 (g : ghost) (c : config) : Prop := exists j, Inv_K13734_at g j c.
Definition Inv_K1370c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x1370c j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j <> 0 /\ IFS g j regs m /\
    V9 phi regs /\ rg regs 10 (t_k (g_in g) j) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j)) c.
Definition Inv_K1370c (g : ghost) (c : config) : Prop := exists j, Inv_K1370c_at g j c.
Definition Inv_K13748_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13748 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j = 0 /\ IFS g j regs m /\
    V9 phi regs /\ rg regs 10 (t_k (g_in g) j) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j)) c.
Definition Inv_K13748 (g : ghost) (c : config) : Prop := exists j, Inv_K13748_at g j c.
Definition Inv_K1374c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x1374c j (fun phi regs m => FT g j phi regs m /\ 1 <= t_len (g_in g) j <= 49 /\ IFS g j regs m /\
    V9 phi regs /\ V7 g j regs /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j)) c.
Definition Inv_K1374c (g : ghost) (c : config) : Prop := exists j, Inv_K1374c_at g j c.
Definition Inv_K137c8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x137c8 j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m) c.
Definition Inv_K137c8 (g : ghost) (c : config) : Prop := exists j, Inv_K137c8_at g j c.
Definition Inv_K137d8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x137d8 j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m /\ rg regs 10 (t_k (g_in g) j)) c.
Definition Inv_K137d8 (g : ghost) (c : config) : Prop := exists j, Inv_K137d8_at g j c.
Definition Inv_K137ec_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x137ec j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m /\
    rg regs 10 (reac_ctrl_kind_name_c.kind_name_addr (t_k (g_in g) j))) c.
Definition Inv_K137ec (g : ghost) (c : config) : Prop := exists j, Inv_K137ec_at g j c.
Definition Inv_K137f8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x137f8 j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m /\
    rg regs 10 (reac_ctrl_kind_name_c.kind_name_addr (t_k (g_in g) j))) c.
Definition Inv_K137f8 (g : ghost) (c : config) : Prop := exists j, Inv_K137f8_at g j c.
(* The reply's three outputs: written when IR(Φ, len), else the 0 stored at 0x1380c-0x13814. *)
Definition RPS (g : ghost) (j : nat) (phi : Z) (m : word -> option byte) : Prop :=
  (t_ir (g_in g) j = true ->
     bytes_at rsegs m (spk g 1750) (RcReply.reply_addr (t_g (g_in g) j)) /\ q64 m (spk g 1736) (phi + 38) /\
     q64 m (spk g 1728) (r_pll (t_g (g_in g) j))) /\
  (t_ir (g_in g) j = false -> u16 m (spk g 1750) 0 /\ q64 m (spk g 1736) 0 /\ q64 m (spk g 1728) 0).
Definition Inv_K13830_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13830 j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m /\ rg regs 10 (t_r (g_in g) j) /\
    RPS g j phi m) c.
Definition Inv_K13830 (g : ghost) (c : config) : Prop := exists j, Inv_K13830_at g j c.
Definition Inv_K13874_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13874 j (fun phi regs m => FB g j phi regs m /\ IFS g j regs m /\ t_ir (g_in g) j = true /\
    RPS g j phi m /\ rg regs 12 (phi + 38) /\ rg regs 13 (r_pll (t_g (g_in g) j))) c.
Definition Inv_K13874 (g : ghost) (c : config) : Prop := exists j, Inv_K13874_at g j c.
(* After the reply arm: id = IDr. *)
Definition GA (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDb g (t_IDr (g_in g) j) m /\ FGj g j m /\ FSj g j regs m.
Definition Inv_K138c4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x138c4 j (fun phi regs m => GA g j phi regs m /\ t_ir (g_in g) j = true /\
    rg regs 10 (fst (RcIdentModel.ING (t_ID (g_in g) j) (r_addr (t_g (g_in g) j)) (r_pl (t_g (g_in g) j))))) c.
Definition Inv_K138c4 (g : ghost) (c : config) : Prop := exists j, Inv_K138c4_at g j c.
Definition Inv_K138c8_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x138c8 j (GA g j) c.
Definition Inv_K138c8 (g : ghost) (c : config) : Prop := exists j, Inv_K138c8_at g j c.
Definition Inv_K138d8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x138d8 j (fun phi regs m => GA g j phi regs m /\ bytes_at rsegs m (spk g 192) (t_FG (g_in g) j)) c.
Definition Inv_K138d8 (g : ghost) (c : config) : Prop := exists j, Inv_K138d8_at g j c.
(* After the fragment call: frag = FGf, FS and FI still of turn j's start. *)
Definition GF (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDb g (t_IDr (g_in g) j) m /\ FGb g (t_FGf (g_in g) j) m /\ FSj g j regs m /\
  bytes_at rsegs m (spk g 192) (t_FG (g_in g) j) /\
  (t_rf (g_in g) j = 1 ->
     u16 m (spk g 1750) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) /\
     q64 m (spk g 1736) (spk g 101) /\ q64 m (spk g 1728) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
Definition Inv_K138f4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x138f4 j (fun phi regs m => GF g j phi regs m /\ rg regs 10 (t_rf (g_in g) j)) c.
Definition Inv_K138f4 (g : ghost) (c : config) : Prop := exists j, Inv_K138f4_at g j c.
Definition Inv_K13910_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13910 j (fun phi regs m => GF g j phi regs m /\ rg regs 24 (t_rf (g_in g) j) /\
    t_sum_ok (g_in g) j = false /\ rg regs 10 0) c.
Definition Inv_K13910 (g : ghost) (c : config) : Prop := exists j, Inv_K13910_at g j c.
Definition Inv_K13914_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13914 j (fun phi regs m => GF g j phi regs m /\ rg regs 24 (t_rf (g_in g) j)) c.
Definition Inv_K13914 (g : ghost) (c : config) : Prop := exists j, Inv_K13914_at g j c.
Definition Inv_K13950_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13950 j (fun phi regs m => GF g j phi regs m /\ rg regs 24 (t_rf (g_in g) j) /\
    t_rf (g_in g) j = 1 /\ rg regs 12 (spk g 101) /\ rg regs 13 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))) c.
Definition Inv_K13950 (g : ghost) (c : config) : Prop := exists j, Inv_K13950_at g j c.
(* After the fragment arm: id = ID_(j+1), frag = FG_(j+1) = FGf, FS still of turn j. *)
Definition GE (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDj g (S j) m /\ FGb g (t_FGf (g_in g) j) m /\ FSj g j regs m.
Definition Inv_K139e4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x139e4 j (fun phi regs m => GE g j phi regs m /\ t_rf (g_in g) j = 1 /\
    rg regs 10 (fst (RcIdentModel.ING (t_IDr (g_in g) j) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))
                       (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j))))) c.
Definition Inv_K139e4 (g : ghost) (c : config) : Prop := exists j, Inv_K139e4_at g j c.
Definition Inv_K139e8_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x139e8 j (GE g j) c.
Definition Inv_K139e8 (g : ghost) (c : config) : Prop := exists j, Inv_K139e8_at g j c.
Definition Inv_K13a80_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13a80 j (EA g j) c.
Definition Inv_K13a80 (g : ghost) (c : config) : Prop := exists j, Inv_K13a80_at g j c.

(* ---- 3.5 is_8819, check_ports, classify, match, latch (E, Q, C, W, X) ---- *)
Definition EB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  EA g j phi regs m /\ t_8819 (g_in g) j = true.
Definition Inv_K13a94_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a94 j (fun phi regs m => EB g j phi regs m /\ rg regs 10 0) c.
Definition Inv_K13a94 (g : ghost) (c : config) : Prop := exists j, Inv_K13a94_at g j c.
Definition Inv_K13aa8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13aa8 j (fun phi regs m => EB g j phi regs m /\ rg regs 10 0) c.
Definition Inv_K13aa8 (g : ghost) (c : config) : Prop := exists j, Inv_K13aa8_at g j c.
Definition Inv_K13af0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13af0 j (fun phi regs m => EB g j phi regs m /\
    rg regs 10 (if t_sum_ok (g_in g) j then 0 else -1)) c.
Definition Inv_K13af0 (g : ghost) (c : config) : Prop := exists j, Inv_K13af0_at g j c.
Definition Inv_K13b64_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13b64 j (fun phi regs m => EQ g j phi regs m /\ V9 phi regs /\
    rg regs 8 (t_want_v (g_in g) j) /\ rg regs 10 (t_want_v (g_in g) j)) c.
Definition Inv_K13b64 (g : ghost) (c : config) : Prop := exists j, Inv_K13b64_at g j c.
Definition Inv_K13b80_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13b80 j (fun phi regs m => EQ g j phi regs m /\ rg regs 10 (t_rp (g_in g) j) /\ PORTS g j m) c.
Definition Inv_K13b80 (g : ghost) (c : config) : Prop := exists j, Inv_K13b80_at g j c.
Definition Inv_K13b98_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13b98 j (fun phi regs m => QB g j phi regs m /\ rg regs 10 (t_unk (g_in g) j)) c.
Definition Inv_K13b98 (g : ghost) (c : config) : Prop := exists j, Inv_K13b98_at g j c.
Definition Inv_K13ba8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13ba8 j (fun phi regs m => QB g j phi regs m /\ rg regs 24 (t_unk (g_in g) j) /\
    rg regs 10 (t_unk (g_in g) j)) c.
Definition Inv_K13ba8 (g : ghost) (c : config) : Prop := exists j, Inv_K13ba8_at g j c.
Definition Inv_K13bd8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13bd8 j (fun phi regs m => QB g j phi regs m /\ rg regs 24 (t_unk (g_in g) j) /\
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j) c.
Definition Inv_K13bd8 (g : ghost) (c : config) : Prop := exists j, Inv_K13bd8_at g j c.
Definition Inv_K13c40_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13c40 j (fun phi regs m => QB g j phi regs m /\ rg regs 24 (t_unk (g_in g) j) /\
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j /\
    rg regs 11 (RcLeaf.n_in (t_pbs (g_in g) j)) /\ rg regs 10 (RcLeaf.n_out (t_pbs (g_in g) j)) /\
    rg regs 12 (RcLeaf.cnt is_empty (t_pbs (g_in g) j) 12) /\
    rg regs 15 (RcPorts.pu_first (t_pbs (g_in g) j) 12)) c.
Definition Inv_K13c40 (g : ghost) (c : config) : Prop := exists j, Inv_K13c40_at g j c.
Definition Inv_K13ca0_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13ca0 j (CC g j) c.
Definition Inv_K13ca0 (g : ghost) (c : config) : Prop := exists j, Inv_K13ca0_at g j c.
Definition CLS (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 1688) (t_B (g_in g) j) /\
  bytes_at rsegs m (spk g 1684)
    (reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_ev (t_cls (g_in g) j) (le4 (Z_to_bv 64 (-1)))).
Definition Inv_K13cc0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13cc0 j (fun phi regs m => CC g j phi regs m /\ CLS g j regs m /\
    rg regs 10 (RcClassify.cl_r (t_cls (g_in g) j))) c.
Definition Inv_K13cc0 (g : ghost) (c : config) : Prop := exists j, Inv_K13cc0_at g j c.
Definition Inv_K13cf4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13cf4 j (fun phi regs m => CC g j phi regs m /\ CLS g j regs m /\ t_cls (g_in g) j <> None /\
    (getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g))) c.
Definition Inv_K13cf4 (g : ghost) (c : config) : Prop := exists j, Inv_K13cf4_at g j c.
Definition Inv_K13d0c_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13d0c j (CC g j) c.
Definition Inv_K13d0c (g : ghost) (c : config) : Prop := exists j, Inv_K13d0c_at g j c.
Definition Inv_K13d38_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13d38 j (fun phi regs m => CC g j phi regs m /\ t_rowsel (g_in g) j = true /\ rg regs 10 CAT /\
    q64 m (spk g 1824) CAT_N) c.
Definition Inv_K13d38 (g : ghost) (c : config) : Prop := exists j, Inv_K13d38_at g j c.
(* row_of_block, row i (i : nat, 0 .. 10). *)
Definition WB (g : ghost) (j i : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RSEL g j phi regs m /\ (i <= 10)%nat /\ rg regs 23 (CAT + CAT_ROW * Z.of_nat i) /\ rg regs 8 (11 - Z.of_nat i) /\
  (forall i', (i' < i)%nat -> t_blk (g_in g) j <> decl_i (Z.of_nat i')).
Definition Inv_K13d4c_at (g : ghost) (j i : nat) (c : config) : Prop := FCUT g 0x13d4c j (WB g j i) c.
Definition Inv_K13d4c (g : ghost) (c : config) : Prop := exists j i, Inv_K13d4c_at g j i c.
Definition Inv_K13d58_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x13d58 j (fun phi regs m => WB g j i phi regs m /\ rg regs 10 1 /\
    bytes_at rsegs m (spk g 1792) (decl_i (Z.of_nat i))) c.
Definition Inv_K13d58 (g : ghost) (c : config) : Prop := exists j i, Inv_K13d58_at g j i c.
Definition Inv_K13d6c_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x13d6c j (fun phi regs m => WB g j i phi regs m /\
    bytes_at rsegs m (spk g 1792) (decl_i (Z.of_nat i)) /\
    (getr regs 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i))) c.
Definition Inv_K13d6c (g : ghost) (c : config) : Prop := exists j i, Inv_K13d6c_at g j i c.
Definition Inv_K13d70_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x13d70 j (fun phi regs m => WB g j i phi regs m /\ t_blk (g_in g) j <> decl_i (Z.of_nat i)) c.
Definition Inv_K13d70 (g : ghost) (c : config) : Prop := exists j i, Inv_K13d70_at g j i c.
Definition Inv_K13d7c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13d7c j (fun phi regs m => CC7 g j phi regs m /\ t_want_m (g_in g) j = 0) c.
Definition Inv_K13d7c (g : ghost) (c : config) : Prop := exists j, Inv_K13d7c_at g j c.
Definition Inv_K13d80_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13d80 j (fun phi regs m => CC7 g j phi regs m /\ rg regs 23 (t_want_m (g_in g) j)) c.
Definition Inv_K13d80 (g : ghost) (c : config) : Prop := exists j, Inv_K13d80_at g j c.
Definition Inv_K13d8c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13d8c j (fun phi regs m => CC7 g j phi regs m /\ rg regs 23 (t_want_m (g_in g) j) /\
    rg regs 10 (t_want (g_in g) j)) c.
Definition Inv_K13d8c (g : ghost) (c : config) : Prop := exists j, Inv_K13d8c_at g j c.
Definition Inv_K13d98_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x13d98 [] (fun regs m => (j <= 255)%nat /\ rg regs 26 (Z.of_nat j) /\ FC g j regs m /\ OURb g m /\
    M7 g m /\ IFS g (S j) regs m) c.
Definition Inv_K13d98 (g : ghost) (c : config) : Prop := exists j, Inv_K13d98_at g j c.
Definition Inv_K13db4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13db4 [] (fun regs m => IDj g (fJ (g_in g)) m) c.
Definition Inv_K13dcc (g : ghost) (c : config) : Prop :=
  CUTST g 0x13dcc [] (fun regs m => IDj g (fJ (g_in g)) m /\
    RcIdentModel.has_model_name (t_ID (g_in g) (fJ (g_in g))) = 1 /\
    rg regs 10 (spk g 157 + Z.of_nat (RcIdentModel.first_zero
                                        (RcIdentModel.model_name (t_ID (g_in g) (fJ (g_in g))))))) c.
Definition Inv_K13dd0 (g : ghost) (c : config) : Prop := CUTST g 0x13dd0 [] (fun _ _ => True) c.

End Slot.

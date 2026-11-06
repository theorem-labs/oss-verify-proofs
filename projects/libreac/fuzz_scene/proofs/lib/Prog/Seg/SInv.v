From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI.
Import ListNotations.
Open Scope Z_scope.

Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x16698 /\ ms_free B = 0x16558 /\ ms_realloc B = None /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x50580 /\ ms_got_guard B = 0x1ef90 /\
  ms_ctx B = 0x50618 /\ ms_lock B = 0x50610 /\ ms_libc B = 0x505a0 /\ ms_size_classes B = 0x126f2 /\
  ms_small_cnt B = 0x12752 /\ ms_med_cnt B = 0x1276d /\ ms_debruijn B = 0x126d2 /\ ms_tp B = 0x30310 /\
  ms_errno_off B = -164 /\ ms_replaced B = None /\
  @sk_ofl_head SH = 0x509d0 /\ @sk_ofl_lock SK = 0x509c8 /\ @sk_threaded SK = 0x505a0 + 1 /\
  empty = 0x30220 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
  ms_vmlock B = None /\ ms_debruijn_len B = 32.

Definition SLOT_FRAME : Z := 9072.
Definition SLOT_K : Z := SLOT_STACK.
Definition SLOT_MALLOCS : Z := 3.
Definition SLOT_REQ : Z := 65535.

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
Definition z8 : byte := Z_to_bv 8 0.
Definition zlen (l : list byte) : Z := Z.of_nat (length l).

Definition hb_bytes (hb : list (Z * Z)) : Z := fold_right Z.add 0 (map snd hb).
Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).

Definition slot_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.
Definition RESB (b0 : sbound) (km : Z) (hb : list (Z * Z)) (A : astate) : Prop :=
  res_ok_slots A (sb_hb b0 hb).
Definition RES_END (b0 : sbound) (A : astate) : Prop := res_ok_slots A b0.

Lemma hb_bytes_app : forall h1 h2, hb_bytes (h1 ++ h2) = hb_bytes h1 + hb_bytes h2.
Proof.
  intros h1 h2. unfold hb_bytes. rewrite map_app.
  induction (map snd h1) as [|x l IH]; cbn [app fold_right]; lia.
Qed.

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
  intros b0 hb n (HL & HB & HC1 & HC2) Hlen HS Hn.
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [exact (proj1 Hn)|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
Qed.

Lemma resb_malloc : forall b0 km' hb hb' A res n, Permutation hb' ((res, n) :: hb) ->
  res_ok_slots A (sb_malloc (sb_hb b0 hb) n) -> RESB b0 km' hb' A.
Proof.
  intros b0 km' hb hb' A res n HP H. unfold RESB. rewrite (sb_hb_perm b0 _ _ HP).
  replace (sb_hb b0 ((res, n) :: hb)) with (sb_malloc (sb_hb b0 hb) n); [exact H|].
  unfold sb_malloc, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_free : forall b0 km' hb hb' A q n, Permutation hb ((q, n) :: hb') ->
  res_ok_slots A (sb_free (sb_hb b0 hb) n) -> RESB b0 km' hb' A.
Proof.
  intros b0 km' hb hb' A q n HP H. unfold RESB.
  rewrite (sb_hb_perm b0 _ _ HP) in H.
  replace (sb_hb b0 hb') with (sb_free (sb_hb b0 ((q, n) :: hb')) n); [exact H|].
  unfold sb_free, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_end : forall b0 km A, RESB b0 km [] A -> RES_END b0 A.
Proof.
  intros b0 km A H. unfold RESB, RES_END in *.
  replace b0 with (sb_hb b0 []); [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

Lemma resb_start : forall b0 A, res_ok_slots A b0 -> RESB b0 0 [] A.
Proof.
  intros b0 A H. unfold RESB. replace (sb_hb b0 []) with b0; [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

Definition q64 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Definition u32 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le4 (Z_to_bv 64 v)).
Definition b8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a [Z_to_bv 8 v].
Definition cstr (m : word -> option byte) (a : Z) (s : list byte) : Prop := bytes_at rsegs m a (s ++ [z8]).

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

Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B).

Definition FR (g : ghost) (km : Z) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
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
  sink_none B mem md /\ RESB (g_b g) km hb A /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at segs mem a).

Definition CUTST (g : ghost) (pc km : Z) (hb : list (Z * Z))
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FR g km hb L A regs mem md /\
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) /\
    P regs mem.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g).

Definition Post (g : ghost) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).
Definition Hrec (X : ghost -> nat -> config -> Prop) (i : nat) : Prop :=
  forall g c, X g i c -> SR segs c (Post g).

End Slot.

From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel reac_identity_fw_str_c
  reac_box_catalogue_defect_c SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_stem_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Export URz.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Definition frame_facts_u (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x15ab4 /\ ms_free B = 0x15974 /\ ms_realloc B = None /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x50720 /\ ms_got_guard B = 0x1f138 /\
  ms_ctx B = 0x507b8 /\ ms_lock B = 0x507b0 /\ ms_libc B = 0x50740 /\ ms_size_classes B = 0x10678 /\
  ms_small_cnt B = 0x106d8 /\ ms_med_cnt B = 0x106f3 /\ ms_debruijn B = 0x10658 /\ ms_tp B = 0x304b0 /\
  ms_errno_off B = -164 /\ (ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32) /\
  @sk_ofl_head SH = 0x50b70 /\ @sk_ofl_lock SK = 0x50b68 /\ @sk_threaded SK = 0x50740 + 1 /\
  empty = 0x303c0 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma ff_vmlock_u : forall B API LS SH SK ra empty, frame_facts_u B API LS SH SK ra empty -> ms_vmlock B = None.
Proof.
  intros B API LS SH SK ra empty H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & V & _) & _). exact V.
Qed.

Lemma ff_dbl_u : forall B API LS SH SK ra empty, frame_facts_u B API LS SH SK ra empty -> ms_debruijn_len B = 32.
Proof.
  intros B API LS SH SK ra empty H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & V) & _). exact V.
Qed.

Definition SLOT_FRAME : Z := 384.
Definition SLOT_K : Z := SLOT_STACK.
Definition CAT : Z := 0x1e3f0.

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
Definition NR (g : ghost) : Z := nrec (g_in g).
Definition NRn (g : ghost) : nat := nrecn (g_in g).
Definition notw (x : Z) : word := Z_to_bv 64 (2 ^ 64 - 1 - x).
Definition EVN (g : ghost) : Z := 2 ^ 64 - 1 - spk g 192.

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

Definition idS (g : ghost) (i : nat) : list byte := rec_id (g_in g) (S i).
Definition fwT (g : ghost) : Z := RcIdentModel.fw_milli (idT (g_in g)).
Definition said_v (g : ghost) : Z := if n_said (g_in g) then spk g 149 else 0.
Definition stem_addr (g : ghost) : Z :=
  if n_use_said (g_in g) then spk g 149 else U.Prog.reac_box_family_stem_c.STEM_Addr (n_fam (g_in g)).
Definition fw_out (m : word -> option byte) (v cap s : Z) : Prop :=
  8 <= cap -> cstr m s (lib.Prog.reac_identity_fw_str_c.FW v).
Definition ver_out (m : word -> option byte) (idb : list byte) (cap s : Z) : Prop :=
  20 <= cap -> cstr m s (id_VER idb).
Definition cat_e (inp : list byte) : Z := CAT + CAT_ROW * (t_row inp mod CAT_N).
Definition cat_mask (inp : list byte) (dp I O P : Z) (sP : list byte) : Z :=
  lib.Prog.reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK (cat_e inp) (t_in inp) (t_out inp) dp I O P sP
    (n_EXP_DP inp).
Definition cat_entry (m : word -> option byte) (e I O P : Z) (sP : list byte) : Prop :=
  -2 ^ 31 <= I < 2 ^ 31 /\ -2 ^ 31 <= O < 2 ^ 31 /\ 0 <= P < 2 ^ 64 /\
  bytes_at rsegs m (e + 8) (le8 (Z_to_bv 64 P)) /\ bytes_at rsegs m (e + 16) (le4 (Z_to_bv 64 I)) /\
  bytes_at rsegs m (e + 20) (le4 (Z_to_bv 64 O)) /\ (P <> 0 -> cstr m P sP /\ ~ In z8 sP).

Definition IDb (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 146) (rec_id (g_in g) j).
Definition HWb (g : ghost) (j : nat) (v : Z) (m : word -> option byte) : Prop :=
  q64 m (spk g 32) (rec_have (g_in g) j) /\ u32 m (spk g 128) v /\
  bytes_at rsegs m (spk g 132) (rec_hwb (g_in g) j).
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ getr regs 26 = Z_to_bv 64 (g_p g + c) /\ getr regs 25 = Z_to_bv 64 (g_n g - c).
Definition G24 (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 24) (spk g 149).
Definition NRb (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 48) (NR g).
Definition EVb (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 40) (EVN g).
Definition REC (g : ghost) (i : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  Z.of_nat i < NR g /\ getr regs 9 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G24 g m /\ HWb g i 0 m /\ EVb g m.
Definition PLB (g : ghost) (i : nat) (pl : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m pl (rec_pl (g_in g) i).
Definition hb_pl (g : ghost) (i : nat) (pl : Z) : list (Z * Z) := [(pl, rec_k (g_in g) i)].
Definition RKB (g : ghost) (i : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  REC g i regs m /\
  getr regs 22 = Z_to_bv 64 (rec_addr (g_in g) i) /\
  getr regs 20 = Z_to_bv 64 (rec_k (g_in g) i) /\
  getr regs 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)).
Definition LPm (g : ghost) (i : nat) (m : word -> option byte) : Prop := q64 m (spk g 56) (rec_Lp (g_in g) i).
Definition B03 (g : ghost) (i : nat) (pl : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RKB g i regs m /\ getr regs 21 = Z_to_bv 64 pl /\ PLB g i pl m.
Definition S7B (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = Z_to_bv 64 (g_p g + rec_body (g_in g) i).
Definition S9L (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = Z_to_bv 64 (rec_Lp (g_in g) i).
Definition BEF (g : ghost) (i : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 64) (rec_id (g_in g) i).
Definition AGN (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 242) (rec_id (g_in g) j).
Definition RRr (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 24 = Z_to_bv 64 (rec_r (g_in g) i).
Definition RB12 (g : ghost) (i : nat) (pl : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  REC g i regs m /\
  getr regs 20 = Z_to_bv 64 (rec_k (g_in g) i) /\
  getr regs 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)) /\
  getr regs 21 = Z_to_bv 64 pl /\ PLB g i pl m /\
  IDb g (S i) m /\ AGN g (S i) m /\ BEF g i m /\ LPm g i m.
Definition S6A (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = Z_to_bv 64 (rec_addr (g_in g) i).
Definition F7 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = Z_to_bv 64 (RcIdentModel.fw_milli (idS g i)).
Definition F2 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 18 = Z_to_bv 64 (RcIdentModel.has_fw (idS g i)).
Definition F0 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 8 = Z_to_bv 64 (RcIdentModel.has_model_name (idS g i)).
Definition F9 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = Z_to_bv 64 (RcIdentModel.major (idS g i)).
Definition F3 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = Z_to_bv 64 (RcIdentModel.minor (idS g i)).
Definition F11 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 27 = Z_to_bv 64 (RcIdentModel.patch (idS g i)).
Definition FNM (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  F7 g i regs /\ F2 g i regs /\ F9 g i regs /\ F3 g i regs /\ F11 g i regs.
Definition FALL (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop := FNM g i regs /\ F0 g i regs.
Definition VB (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_REAC_VERSION.
Definition NMA (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_MODEL_NAME.
Definition FWA (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_FIRMWARE.

Definition CB (g : ghost) (v : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  1 <= NR g /\ NRb g m /\ G24 g m /\ HWb g (NRn g) v m /\ CUR g (cT (g_in g)) regs /\ IDb g (NRn g) m.
Definition TID (g : ghost) (m : word -> option byte) : Prop := G24 g m /\ IDb g (NRn g) m.
Definition HW_miss (g : ghost) (j : nat) : Prop :=
  forall j', (j' < j)%nat -> map bv_unsigned (hwbT (g_in g)) <> HWT j'.
Definition TL (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 24 = Z_to_bv 64 (t_fam_raw (g_in g)) /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\
  q64 m (spk g 56) (t_out (g_in g)) /\ q64 m (spk g 48) (t_row (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (t_cap_name (g_in g)) /\ getr regs 27 = Z_to_bv 64 (t_cap_tok (g_in g)) /\
  getr regs 19 = Z_to_bv 64 (t_cap_disp (g_in g)).
Definition NMB (g : ghost) (nm tk dp : Z) : list (Z * Z) :=
  [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g))); (dp, bsz (t_cap_disp (g_in g)))].
Definition OUTS (g : ghost) (nm tk dp : Z) (m : word -> option byte) : Prop :=
  n_r (g_in g) = 0 ->
  cstr m nm (n_EXP_NM (g_in g)) /\ cstr m tk (n_TK (g_in g)) /\ cstr m dp (n_EXP_DP (g_in g)).
Definition G930 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\ q64 m (spk g 56) (t_out (g_in g)) /\
  q64 m (spk g 48) (t_row (g_in g)) /\ getr regs 19 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
  getr regs 18 = Z_to_bv 64 (RcIdentModel.has_model_name (idT (g_in g))) /\
  getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\ getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (said_v g) /\ getr regs 26 = Z_to_bv 64 (n_fam (g_in g)).
Definition G978 (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  G930 g regs m /\ getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\
  getr regs 22 = Z_to_bv 64 dp /\ q64 m (spk g 0) dp /\ q64 m (spk g 8) (t_cap_disp (g_in g)).
Definition NB (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\ n_wok (g_in g) = true /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\ getr regs 19 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
  q64 m (spk g 56) (t_out (g_in g)) /\ q64 m (spk g 48) (t_row (g_in g)) /\ OUTS g nm tk dp m.
Definition STP (g : ghost) (m : word -> option byte) : Prop :=
  q64 m (spk g 24) (stem_addr g) /\ cstr m (stem_addr g) (n_stem (g_in g)).
Definition N1 (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NB g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (t_out (g_in g)) /\ STP g m /\
  q64 m (spk g 216) 4 /\ cstr m (spk g 192) (n_W4 (g_in g)).
Definition H9a (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (n_ln (g_in g)) /\ cstr m (spk g 242) (n_EXP_NM (g_in g)).
Definition HB0 (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NB g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (n_ln (g_in g)) /\
  getr regs 26 = notw (spk g 64) /\ getr regs 18 = Z_to_bv 64 (spk g 64) /\
  cstr m (spk g 242) (n_EXP_NM (g_in g)).
Definition HA (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  HB0 g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (t_out (g_in g)).
Definition H17b (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  HB0 g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (n_ld (g_in g)) /\ cstr m (spk g 64) (n_EXP_DP (g_in g)).
Definition IRb (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\
  q64 m (spk g 56) (t_out (g_in g)) /\ q64 m (spk g 48) (t_row (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\ getr regs 19 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
  OUTS g nm tk dp m /\
  (n_r (g_in g) = 0 -> cstr m (spk g 242) (n_EXP_NM (g_in g)) /\ cstr m (spk g 64) (n_EXP_DP (g_in g))).
Definition IR (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IRb g nm tk dp regs m /\ n_r (g_in g) = 0.
Definition IRc (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\ q64 m (spk g 56) (t_out (g_in g)) /\ q64 m (spk g 48) (t_row (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\ getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\
  OUTS g nm tk dp m /\ n_r (g_in g) = 0 /\ cstr m (spk g 242) (n_EXP_NM (g_in g)) /\
  cstr m (spk g 64) (n_EXP_DP (g_in g)).

Section Slot.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Let API := APIf rc.
Context {RzCi : RzC} {RzAi : RzA B API}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MI (m : word -> option byte) : Prop := ro_agree segs m.
Definition relro (m : word -> option byte) : Prop := G_img_c B frame_RELRO m.
Definition HBR (hb : list (Z * Z)) : Prop :=
  forall a k, In (a, k) hb -> 0 < k -> 4096 <= a /\ a + k <= alloc_ceiling.

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
  rz_sroom (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B) /\
  (g_n g = 0 \/ (4096 <= g_p g /\ g_p g + g_n g <= alloc_ceiling)).

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

Lemma cut_hb_range : forall g pc km hb P c, CUTST g pc km hb P c -> HBR hb.
Proof.
  intros g pc km hb P c (L & A & regs & mem & md & _ & HF & HP & _) a k Hin Hk.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & HW & HB & _).
  assert (Hb : In (a, k) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin. }
  assert (R : 4096 <= a /\ a + k <= alloc_ceiling /\ a mod 16 = 0).
  { eapply heap_blocks_range; try exact (aa_laws API); try exact Hb; try exact Hk;
      try (hnf; split; [exact HM | split; assumption]). }
  destruct R as (R1 & R2 & _). split; assumption.
Qed.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g).

Definition Post (g : ghost) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> Rz segs c (Post g).
Definition Hrec (X : ghost -> nat -> config -> Prop) (i : nat) : Prop :=
  forall g c, X g i c -> Rz segs c (Post g).

Definition A0 (g : ghost) (regs : bvmap 5 word) : Prop :=
  getr regs 9 = Z_to_bv 64 (g_n g) /\ getr regs 18 = Z_to_bv 64 (g_p g).

Definition Inv_U12f50 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f50 0 [] (fun regs m => A0 g regs) c.
Definition Inv_U12f58 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f58 0 [] (fun regs m => A0 g regs /\ IDb g 0 m) c.
Definition Inv_U12f6c (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f6c 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_U12f8c (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f8c 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 8 = Z_to_bv 64 (-1) /\
    getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_U12fa4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12fa4 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_U12fc4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12fc4 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_U12fe4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12fe4 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U12ff0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12ff0 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 0) c.

Definition Inv_U13058_at (g : ghost) (i : nat) (c : config) : Prop :=
  CUTST g 0x13058 (2 * Z.of_nat i) []
    (fun regs m => REC g i regs m /\ CUR g (rec_c (g_in g) i) regs /\ IDb g i m /\
       getr regs 12 = Z_to_bv 64 1) c.
Definition Inv_U130fc_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x130fc (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => RKB g i regs m /\ S7B g i regs /\ S9L g i regs /\ IDb g i m /\
       getr regs 10 = Z_to_bv 64 pl) c.
Definition Inv_U13124_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13124 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ S7B g i regs /\ S9L g i regs /\ LPm g i m /\ IDb g i m) c.
Definition Inv_U13134_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13134 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ S7B g i regs /\ S9L g i regs /\ LPm g i m /\ IDb g i m /\
       BEF g i m) c.
Definition Inv_U13148_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13148 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ S7B g i regs /\ S9L g i regs /\ LPm g i m /\ IDb g (S i) m /\
       BEF g i m /\ getr regs 10 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_U1315c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x1315c (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ S7B g i regs /\ S9L g i regs /\ LPm g i m /\ IDb g (S i) m /\
       BEF g i m /\ RRr g i regs /\ getr regs 10 = Z_to_bv 64 gb) c.
Definition Inv_U13174_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x13174 (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ S9L g i regs /\ LPm g i m /\ IDb g (S i) m /\ BEF g i m /\
       RRr g i regs /\ getr regs 23 = Z_to_bv 64 gb /\ PLB g i gb m) c.
Definition Inv_U13198_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x13198 (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ S9L g i regs /\ LPm g i m /\ IDb g (S i) m /\ BEF g i m /\
       RRr g i regs /\ getr regs 23 = Z_to_bv 64 gb /\ PLB g i gb m /\
       b8 m (gb + rec_k (g_in g) i) 0x5a /\ AGN g i m) c.
Definition Inv_U131ac_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x131ac (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ S9L g i regs /\ LPm g i m /\ IDb g (S i) m /\ BEF g i m /\
       RRr g i regs /\ getr regs 23 = Z_to_bv 64 gb /\ PLB g i gb m /\
       b8 m (gb + rec_k (g_in g) i) 0x5a /\ AGN g (S i) m /\
       getr regs 10 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_U131b8_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x131b8 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ LPm g i m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       AGN g (S i) m /\ getr regs 25 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_U131ec_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x131ec (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ LPm g i m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       AGN g (S i) m /\ getr regs 25 = Z_to_bv 64 (rec_r (g_in g) i) /\ F7 g i regs /\ F2 g i regs /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13230_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13230 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U133ac_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x133ac (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\
       rec_r (g_in g) i = 0 /\ getr regs 10 = Z_to_bv 64 (RcIdentModel.has_reac_version (idS g i)) /\
       getr regs 11 = Z_to_bv 64 (RcIdentModel.has_reac_version (idS g i))) c.
Definition Inv_U1341c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x1341c (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       getr regs 10 = Z_to_bv 64 (RcIdentModel.has_reac_version (idS g i)) /\
       getr regs 11 = Z_to_bv 64 1536) c.
Definition Inv_U135c0_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x135c0 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ NMA g i) c.
Definition FWL (g : ghost) (i : nat) (pl t : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ FWA g i /\
  getr regs 10 = Z_to_bv 64 (4 - t) /\ getr regs 11 = Z_to_bv 64 (pl + t) /\
  getr regs 12 = Z_to_bv 64 (pl + t) /\
  (forall j, 0 <= j < t -> RcIdentModel.bz (RcIdentModel.nthb (rec_pl (g_in g) i) (Z.to_nat j)) <= 9).
Definition Inv_U13270_at (g : ghost) (i : nat) (t : Z) (c : config) : Prop :=
  exists pl, CUTST g 0x13270 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => 0 <= t <= 3 /\ FWL g i pl t regs m) c.
Definition Inv_U132a4_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x132a4 (2 * Z.of_nat i + 2) (hb_pl g i pl) (fun regs m => FWL g i pl 4 regs m) c.
Definition Inv_U13304_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13304 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ FWA g i /\
       RcIdentModel.fw_milli (idS g i) <= 9999 /\ getr regs 10 = Z_to_bv 64 5 /\
       cstr m (spk g 192) (lib.Prog.reac_identity_fw_str_c.FW (RcIdentModel.fw_milli (idS g i)))) c.
Definition Inv_U13314_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13314 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ FALL g i regs /\ RRr g i regs /\ getr regs 22 = Z_to_bv 64 5 /\
       FWA g i /\ RcIdentModel.fw_milli (idS g i) <= 9999 /\
       cstr m (spk g 192) (lib.Prog.reac_identity_fw_str_c.FW (RcIdentModel.fw_milli (idS g i)))) c.
Definition Inv_U133bc_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x133bc (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\
       rec_r (g_in g) i = 0 /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13438_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13438 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U134b4_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x134b4 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 184) (zlen (EV1 (idS g i))) /\ bytes_at rsegs m (spk g 192) (EV1 (idS g i))) c.
Definition Inv_U134f4_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x134f4 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 184) (zlen (EV2 (idS g i))) /\ bytes_at rsegs m (spk g 192) (EV2 (idS g i))) c.
Definition Inv_U13508_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13508 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 184) (zlen (EV (idS g i))) /\ bytes_at rsegs m (spk g 192) (EV (idS g i))) c.
Definition VER_LV (g : ghost) (i : nat) : Z :=
  lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV (RcIdentModel.major (idS g i))
    (RcIdentModel.minor (idS g i)) (RcIdentModel.patch (idS g i)).
Definition V540 (g : ghost) (i : nat) (pl : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB12 g i pl regs m /\ S6A g i regs /\ FNM g i regs /\ RRr g i regs /\ VB g i /\
  q64 m (spk g 184) (zlen (EV (idS g i))) /\ cstr m (spk g 192) (EV (idS g i)) /\
  getr regs 8 = Z_to_bv 64 (zlen (EV (idS g i))) /\ cstr m (spk g 216) (id_VER (idS g i)).
Definition Inv_U13540_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13540 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => V540 g i pl regs m /\ getr regs 10 = Z_to_bv 64 (VER_LV g i)) c.
Definition Inv_U13558_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13558 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => V540 g i pl regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U135d0_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x135d0 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ NMA g i /\
       getr regs 10 = Z_to_bv 64 (spk g 149 + wn (idS g i))) c.
Definition Inv_U13604_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13604 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ FNM g i regs /\ RRr g i regs /\ NMA g i /\
       getr regs 22 = Z_to_bv 64 (wn (idS g i)) /\ getr regs 8 = Z_to_bv 64 (wn (idS g i) + 1) /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13660_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13660 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => Z.of_nat i < NR g /\ getr regs 9 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G24 g m /\
       HWb g (S i) 0 m /\ EVb g m /\ IDb g (S i) m /\
       getr regs 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)) /\
       getr regs 20 = Z_to_bv 64 (rec_k (g_in g) i) /\ LPm g i m /\ getr regs 21 = Z_to_bv 64 pl) c.

Definition Inv_U13058 (g : ghost) (c : config) : Prop := exists i, Inv_U13058_at g i c.
Definition Inv_U130fc (g : ghost) (c : config) : Prop := exists i, Inv_U130fc_at g i c.
Definition Inv_U13124 (g : ghost) (c : config) : Prop := exists i, Inv_U13124_at g i c.
Definition Inv_U13134 (g : ghost) (c : config) : Prop := exists i, Inv_U13134_at g i c.
Definition Inv_U13148 (g : ghost) (c : config) : Prop := exists i, Inv_U13148_at g i c.
Definition Inv_U1315c (g : ghost) (c : config) : Prop := exists i, Inv_U1315c_at g i c.
Definition Inv_U13174 (g : ghost) (c : config) : Prop := exists i, Inv_U13174_at g i c.
Definition Inv_U13198 (g : ghost) (c : config) : Prop := exists i, Inv_U13198_at g i c.
Definition Inv_U131ac (g : ghost) (c : config) : Prop := exists i, Inv_U131ac_at g i c.
Definition Inv_U131b8 (g : ghost) (c : config) : Prop := exists i, Inv_U131b8_at g i c.
Definition Inv_U131ec (g : ghost) (c : config) : Prop := exists i, Inv_U131ec_at g i c.
Definition Inv_U13230 (g : ghost) (c : config) : Prop := exists i, Inv_U13230_at g i c.
Definition Inv_U133ac (g : ghost) (c : config) : Prop := exists i, Inv_U133ac_at g i c.
Definition Inv_U1341c (g : ghost) (c : config) : Prop := exists i, Inv_U1341c_at g i c.
Definition Inv_U135c0 (g : ghost) (c : config) : Prop := exists i, Inv_U135c0_at g i c.
Definition Inv_U13270 (g : ghost) (c : config) : Prop := exists i t, Inv_U13270_at g i t c.
Definition Inv_U132a4 (g : ghost) (c : config) : Prop := exists i, Inv_U132a4_at g i c.
Definition Inv_U13304 (g : ghost) (c : config) : Prop := exists i, Inv_U13304_at g i c.
Definition Inv_U13314 (g : ghost) (c : config) : Prop := exists i, Inv_U13314_at g i c.
Definition Inv_U133bc (g : ghost) (c : config) : Prop := exists i, Inv_U133bc_at g i c.
Definition Inv_U13438 (g : ghost) (c : config) : Prop := exists i, Inv_U13438_at g i c.
Definition Inv_U134b4 (g : ghost) (c : config) : Prop := exists i, Inv_U134b4_at g i c.
Definition Inv_U134f4 (g : ghost) (c : config) : Prop := exists i, Inv_U134f4_at g i c.
Definition Inv_U13508 (g : ghost) (c : config) : Prop := exists i, Inv_U13508_at g i c.
Definition Inv_U13540 (g : ghost) (c : config) : Prop := exists i, Inv_U13540_at g i c.
Definition Inv_U13558 (g : ghost) (c : config) : Prop := exists i, Inv_U13558_at g i c.
Definition Inv_U135d0 (g : ghost) (c : config) : Prop := exists i, Inv_U135d0_at g i c.
Definition Inv_U13604 (g : ghost) (c : config) : Prop := exists i, Inv_U13604_at g i c.
Definition Inv_U13660 (g : ghost) (c : config) : Prop := exists i, Inv_U13660_at g i c.

Definition Inv_U136a0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136a0 (2 * NR g) []
    (fun regs m => CB g 0 regs m /\ getr regs 9 = Z_to_bv 64 (NR g)) c.
Definition Inv_U136b0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136b0 (2 * NR g) []
    (fun regs m => CB g (haveT (g_in g)) regs m /\ getr regs 8 = Z_to_bv 64 (haveT (g_in g)) /\
       getr regs 10 = Z_to_bv 64 (FAM (idT (g_in g)))) c.
Definition Inv_U136c8_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x136c8 (2 * NR g) []
    (fun regs m => CB g 1 regs m /\ haveT (g_in g) = 1 /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       getr regs 19 = Z_to_bv 64 (spk g 132) /\ getr regs 8 = Z_to_bv 64 (3 - Z.of_nat j) /\
       getr regs 18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) /\ (j < 3)%nat /\ HW_miss g j) c.
Definition Inv_U136c8 (g : ghost) (c : config) : Prop := exists j, Inv_U136c8_at g j c.
Definition Inv_U13f04_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x13f04 (2 * NR g) []
    (fun regs m => CB g 1 regs m /\ haveT (g_in g) = 1 /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       getr regs 18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) /\ (j < 3)%nat /\
       map bv_unsigned (hwbT (g_in g)) = HWT j /\ HW_miss g j) c.
Definition Inv_U13f04 (g : ghost) (c : config) : Prop := exists j, Inv_U13f04_at g j c.
Definition Inv_U136ec (g : ghost) (c : config) : Prop :=
  CUTST g 0x136ec 0 []
    (fun regs m => g_n g = 0 /\ getr regs 9 = Z_to_bv 64 0 /\ getr regs 18 = Z_to_bv 64 (g_p g) /\
       G24 g m /\ IDb g 0 m) c.
Definition Inv_U136f4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136f4 0 []
    (fun regs m => NR g = 0 /\ CUR g (cT (g_in g)) regs /\ G24 g m /\ IDb g 0 m) c.
Definition Inv_U136fc (g : ghost) (c : config) : Prop :=
  CUTST g 0x136fc 0 []
    (fun regs m => NR g = 0 /\ CUR g (cT (g_in g)) regs /\ G24 g m /\ IDb g 0 m /\
       getr regs 10 = Z_to_bv 64 (FAM (idT (g_in g)))) c.
Definition Inv_U13700 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13700 (2 * NR g) []
    (fun regs m => CUR g (cT (g_in g)) regs /\ TID g m /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       fam_hw (haveT (g_in g)) (hwbT (g_in g)) = 0) c.
Definition Inv_U13704 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13704 (2 * NR g) []
    (fun regs m => CUR g (cT (g_in g)) regs /\ TID g m /\
       FAM (idT (g_in g)) = fam_hw (haveT (g_in g)) (hwbT (g_in g))) c.

Definition D784 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 20 = Z_to_bv 64 (t_cap_fw (g_in g)) /\
  getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\ getr regs 11 = Z_to_bv 64 (tb (g_in g) 9) /\
  getr regs 10 = Z_to_bv 64 (tb (g_in g) 10).
Definition Inv_U13784 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13784 (2 * NR g) [] (D784 g) c.
Definition E794 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 20 = Z_to_bv 64 (t_cap_fw (g_in g)) /\
  getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\ getr regs 22 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_U13794 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x13794 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 10 = Z_to_bv 64 s) c.
Definition Inv_U137ac (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x137ac (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\
       getr regs 10 = Z_to_bv 64 (fw_res (fwT g) (t_cap_fw (g_in g))) /\
       fw_out m (fwT g) (t_cap_fw (g_in g)) s) c.
Definition Inv_U137b8 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x137b8 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\ fw_out m (fwT g) (t_cap_fw (g_in g)) s) c.
Definition Inv_U137c8 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x137c8 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\
       getr regs 10 = Z_to_bv 64 (fw_res (t_any_fw (g_in g)) (t_cap_fw (g_in g))) /\
       fw_out m (t_any_fw (g_in g)) (t_cap_fw (g_in g)) s) c.
Definition Inv_U137d4 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x137d4 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\
       fw_out m (t_any_fw (g_in g)) (t_cap_fw (g_in g)) s) c.
Definition E7dc (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\
  getr regs 22 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_U137dc (g : ghost) (c : config) : Prop :=
  CUTST g 0x137dc (2 * NR g + 1) [] (E7dc g) c.
Definition Inv_U137e4 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x137e4 (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E7dc g regs m /\ getr regs 10 = Z_to_bv 64 s) c.
Definition Inv_U13804 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x13804 (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E7dc g regs m /\ getr regs 20 = Z_to_bv 64 s /\
       getr regs 10 = Z_to_bv 64 (ver_res (idT (g_in g)) (t_cap_ver (g_in g))) /\
       ver_out m (idT (g_in g)) (t_cap_ver (g_in g)) s) c.
Definition Inv_U13810 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x13810 (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E7dc g regs m /\ getr regs 20 = Z_to_bv 64 s /\
       ver_out m (idT (g_in g)) (t_cap_ver (g_in g)) s) c.
Definition F818 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 22 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_U13818 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13818 (2 * NR g + 2) [] (F818 g) c.
Definition Inv_U1384c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1384c (2 * NR g + 2) []
    (fun regs m => F818 g regs m /\ getr regs 20 = Z_to_bv 64 (t_any_fw (g_in g) / 1000) /\
       getr regs 8 = Z_to_bv 64 (spk g 64) /\
       q64 m (spk g 192) (zlen (DEC (t_any_fw (g_in g) / 1000) 1)) /\
       bytes_at rsegs m (spk g 64) (DEC (t_any_fw (g_in g) / 1000) 1)) c.
Definition Inv_U1389c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1389c (2 * NR g + 2) []
    (fun regs m => F818 g regs m /\ getr regs 20 = Z_to_bv 64 (t_any_fw (g_in g) / 1000) /\
       getr regs 8 = notw (spk g 64) /\ q64 m (spk g 192) (zlen (t_EF (g_in g))) /\
       bytes_at rsegs m (spk g 64) (t_EF (g_in g))) c.
Definition F8c8 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  F818 g regs m /\ getr regs 18 = Z_to_bv 64 (zlen (t_EF (g_in g))) /\ cstr m (spk g 64) (t_EF (g_in g)) /\
  cstr m (spk g 242) (lib.Prog.reac_identity_fw_str_c.FW (t_any_fw (g_in g))).
Definition Inv_U138c8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x138c8 (2 * NR g + 2) []
    (fun regs m => F8c8 g regs m /\
       getr regs 10 = Z_to_bv 64 (lib.Prog.reac_identity_fw_str_c.L (t_any_fw (g_in g)))) c.
Definition Inv_U138e0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x138e0 (2 * NR g + 2) [] (fun regs m => F8c8 g regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U138f4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x138f4 (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ t_fam_raw (g_in g) < 128 /\
       getr regs 10 = Z_to_bv 64 (FAM (idT (g_in g)))) c.
Definition Inv_U138fc (g : ghost) (c : config) : Prop :=
  CUTST g 0x138fc (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ 128 <= t_fam_raw (g_in g)) c.
Definition Inv_U13908 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13908 (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ getr regs 26 = Z_to_bv 64 (n_fam (g_in g)) /\
       getr regs 10 = Z_to_bv 64 (U.Prog.reac_box_family_stem_c.STEM_Addr (n_fam (g_in g)))) c.
Definition Inv_U13930 (g : ghost) (c : config) : Prop :=
  exists nm, CUTST g 0x13930 (2 * NR g + 3) [(nm, bsz (t_cap_name (g_in g)))]
    (fun regs m => G930 g regs m /\ getr regs 10 = Z_to_bv 64 nm) c.
Definition Inv_U1393c (g : ghost) (c : config) : Prop :=
  exists nm tk, CUTST g 0x1393c (2 * NR g + 4)
    [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))]
    (fun regs m => G930 g regs m /\ getr regs 20 = Z_to_bv 64 nm /\ getr regs 10 = Z_to_bv 64 tk) c.
Definition Inv_U13948 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13948 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G930 g regs m /\ getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\
       getr regs 10 = Z_to_bv 64 dp) c.
Definition Inv_U13978 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13978 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G978 g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_U139ac (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x139ac (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G978 g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_r (g_in g)) /\ OUTS g nm tk dp m) c.

Definition Inv_U13a98 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a98 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => NB g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (t_out (g_in g)) /\
       getr regs 8 = Z_to_bv 64 (spk g 192) /\ STP g m /\ q64 m (spk g 216) 2 /\
       bytes_at rsegs m (spk g 192) (DEC (t_in (g_in g)) 2)) c.
Definition Inv_U13aac (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13aac (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => NB g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (t_out (g_in g)) /\
       getr regs 8 = Z_to_bv 64 (spk g 192) /\ STP g m /\ q64 m (spk g 216) 4 /\
       bytes_at rsegs m (spk g 192) (n_W4 (g_in g))) c.
Definition Inv_U13ae8_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ae8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (spk g 192) /\
       0 <= t < zlen (n_stem (g_in g)) /\
       getr regs 15 = Z_to_bv 64 (stem_addr g + t) /\
       getr regs 11 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat t))) /\
       getr regs 12 = Z_to_bv 64 (- t) /\ getr regs 13 = Z_to_bv 64 (-1) /\
       getr regs 14 = Z_to_bv 64 (spk g 242 + t) /\ getr regs 10 = Z_to_bv 64 (spk g 242) /\
       bytes_at rsegs m (spk g 242) (firstn (Z.to_nat t) (n_stem (g_in g)))) c.
Definition Inv_U13ae8 (g : ghost) (c : config) : Prop := exists t, Inv_U13ae8_at g t c.
Definition Inv_U13b08 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b08 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (spk g 192) /\
       getr regs 12 = Z_to_bv 64 (- zlen (n_stem (g_in g))) /\ getr regs 10 = Z_to_bv 64 (spk g 242) /\
       bytes_at rsegs m (spk g 242) (n_stem (g_in g))) c.
Definition Inv_U13b10 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b10 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (spk g 192) /\
       getr regs 10 = Z_to_bv 64 (spk g 242) /\
       RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g)) 0) = 0) c.
Definition Inv_U13b98 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b98 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       getr regs 10 = notw (spk g 242) /\ bytes_at rsegs m (spk g 242) (n_stem (g_in g)) /\
       n_ends_w4 (g_in g) = false) c.
Definition Inv_U13bc8_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13bc8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       getr regs 10 = notw (spk g 242) /\ n_ends_w4 (g_in g) = false /\ 0 <= t <= 3 /\
       bytes_at rsegs m (spk g 242) (n_stem (g_in g) ++ [dash] ++ firstn (Z.to_nat t) (n_W4 (g_in g))) /\
       getr regs 11 = Z_to_bv 64 (spk g 242) /\
       getr regs 12 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_W4 (g_in g)) (Z.to_nat t))) /\
       getr regs 13 = Z_to_bv 64 (2 ^ 64 - 1 - zlen (n_stem (g_in g)) - t) /\
       getr regs 14 = Z_to_bv 64 (spk g 242 + zlen (n_stem (g_in g)) + 1 + t) /\
       getr regs 15 = Z_to_bv 64 (spk g 192 + t) /\ getr regs 16 = Z_to_bv 64 (-1)) c.
Definition Inv_U13bc8 (g : ghost) (c : config) : Prop := exists t, Inv_U13bc8_at g t c.
Definition Inv_U13bf0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13bf0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       getr regs 10 = notw (spk g 242) /\ n_ends_w4 (g_in g) = false /\
       bytes_at rsegs m (spk g 242) (n_stem (g_in g) ++ [dash]) /\
       getr regs 14 = Z_to_bv 64 (zlen (n_stem (g_in g)) + 1) /\
       RcIdentModel.bz (RcIdentModel.nthb (n_W4 (g_in g)) 0) = 0) c.
Definition Inv_U13be8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13be8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       getr regs 10 = notw (spk g 242) /\ n_ends_w4 (g_in g) = false /\
       getr regs 13 = Z_to_bv 64 (2 ^ 64 - 1 - zlen (n_stem (g_in g)) - 4) /\
       bytes_at rsegs m (spk g 242) (n_EXP_NM (g_in g))) c.
Definition Inv_U13bf4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13bf4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (n_ln (g_in g)) /\
       getr regs 10 = notw (spk g 242) /\ bytes_at rsegs m (spk g 242) (n_EXP_NM (g_in g))) c.
Definition Inv_U13c24_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c24 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H9a g nm tk dp regs m /\ 0 <= t < n_ln (g_in g) /\
       getr regs 10 = Z_to_bv 64 (spk g 64) /\ getr regs 26 = notw (spk g 64) /\
       getr regs 11 = Z_to_bv 64 t /\ getr regs 12 = Z_to_bv 64 (spk g 242 + t) /\
       getr regs 13 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (Z.to_nat t))) /\
       getr regs 14 = Z_to_bv 64 (-1) /\
       bytes_at rsegs m (spk g 64) (firstn (Z.to_nat t) (n_EXP_NM (g_in g)))) c.
Definition Inv_U13c24 (g : ghost) (c : config) : Prop := exists t, Inv_U13c24_at g t c.
Definition Inv_U13c44 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c44 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H9a g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (spk g 64) /\
       getr regs 26 = notw (spk g 64) /\
       ((getr regs 11 = Z_to_bv 64 (n_ln (g_in g)) /\ bytes_at rsegs m (spk g 64) (n_EXP_NM (g_in g))) \/
        (getr regs 11 = Z_to_bv 64 0 /\ b8 m (spk g 242) 0))) c.
Definition Inv_U13c98 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c98 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HA g nm tk dp regs m /\ q64 m (spk g 184) (ld1 (g_in g)) /\
       bytes_at rsegs m (spk g 64) (dp1 (g_in g))) c.
Definition Inv_U13cb0_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13cb0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HA g nm tk dp regs m /\ q64 m (spk g 184) (ld1 (g_in g)) /\ 0 <= t <= 5 /\
       bytes_at rsegs m (spk g 64) (dp1 (g_in g) ++ firstn (Z.to_nat t) s_in) /\
       getr regs 13 = Z_to_bv 64 (ld1 (g_in g) + t) /\ getr regs 11 = Z_to_bv 64 (6 - t) /\
       getr regs 10 = Z_to_bv 64 (IN_SLASH + 1 + t) /\
       getr regs 12 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb s_in (Z.to_nat t)))) c.
Definition Inv_U13cb0 (g : ghost) (c : config) : Prop := exists t, Inv_U13cb0_at g t c.
Definition Inv_U13cd4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13cd4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HA g nm tk dp regs m /\ bytes_at rsegs m (spk g 64) (dp1 (g_in g) ++ s_in) /\
       getr regs 14 = Z_to_bv 64 (ld1 (g_in g) + 6)) c.
Definition Inv_U13cf0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13cf0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HA g nm tk dp regs m /\ q64 m (spk g 184) (ld2 (g_in g)) /\
       bytes_at rsegs m (spk g 64) (dp2 (g_in g))) c.
Definition Inv_U13d08_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d08 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HB0 g nm tk dp regs m /\ q64 m (spk g 184) (ld2 (g_in g)) /\ 0 <= t <= 4 /\
       bytes_at rsegs m (spk g 64) (dp2 (g_in g) ++ firstn (Z.to_nat t) s_out) /\
       getr regs 13 = Z_to_bv 64 (ld2 (g_in g) + t) /\ getr regs 11 = Z_to_bv 64 (5 - t) /\
       getr regs 10 = Z_to_bv 64 (OUT_PAREN + 1 + t) /\
       getr regs 12 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb s_out (Z.to_nat t)))) c.
Definition Inv_U13d08 (g : ghost) (c : config) : Prop := exists t, Inv_U13d08_at g t c.
Definition Inv_U13d2c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d2c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HB0 g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 (n_ld (g_in g)) /\
       getr regs 13 = Z_to_bv 64 (n_ld (g_in g)) /\ bytes_at rsegs m (spk g 64) (n_EXP_DP (g_in g))) c.
Definition Inv_U13d58 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d58 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H17b g nm tk dp regs m /\ n_ln (g_in g) < t_cap_name (g_in g) /\
       (has_dash (n_EXP_NM (g_in g)) = true -> getr regs 10 <> Z_to_bv 64 0) /\
       (has_dash (n_EXP_NM (g_in g)) = false -> getr regs 10 = Z_to_bv 64 0)) c.
Definition Inv_U13d74 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d74 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H17b g nm tk dp regs m /\ t_cap_name (g_in g) <= n_ln (g_in g)) c.

Definition Inv_U13d84 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d84 (2 * NR g + 5) (NMB g nm tk dp) (IRb g nm tk dp) c.
Definition Inv_U13d90 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13d90 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_ln (g_in g))) c.
Definition Inv_U13da0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13da0 (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_U13da8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13da8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (zlen (n_TK (g_in g)))) c.
Definition Inv_U13db8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13db8 (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_U13dc0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13dc0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_ld (g_in g))) c.
Definition Inv_U13dd0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13dd0 (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_U13ddc (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ddc (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13dec (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13dec (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13e08_at (g : ghost) (q : nat) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13e08 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ (q <= length (n_EXP_NM (g_in g)))%nat /\
       getr regs 10 = Z_to_bv 64 (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q) /\
       getr regs 11 = Z_to_bv 64 (Z.of_nat q) /\
       getr regs 12 = Z_to_bv 64 (dropped (n_EXP_NM (g_in g)) q) /\
       getr regs 13 = notw tk /\ getr regs 14 = notw nm /\ getr regs 15 = Z_to_bv 64 45 /\
       getr regs 16 = Z_to_bv 64 (nm + Z.of_nat q)) c.
Definition Inv_U13e08 (g : ghost) (c : config) : Prop := exists q, Inv_U13e08_at g q c.
Definition Inv_U13e54 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13e54 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (zlen (n_TK (g_in g))) /\
       getr regs 13 = notw tk) c.
Definition Inv_U13e70 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13e70 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 192) CAT_N /\ getr regs 10 = Z_to_bv 64 CAT) c.
Definition Inv_U13ee4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ee4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 192) 0) c.
Definition Inv_U13ebc (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ebc (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\
       getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
       exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\
         getr regs 23 = Z_to_bv 64 CAT /\ getr regs 19 = Z_to_bv 64 (cat_e (g_in g)) /\
         getr regs 10 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP)) c.
Definition Inv_U13ef8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ef8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 192) 0 /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_U13efc (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13efc (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\ getr regs 23 = Z_to_bv 64 0 /\ getr regs 23 = Z_to_bv 64 CAT) c.
Definition Inv_U13f24 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13f24 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\
       exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\ P <> 0 /\
         getr regs 19 = Z_to_bv 64 (cat_e (g_in g)) /\
         getr regs 8 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP) /\
         getr regs 9 = Z_to_bv 64 (if (I =? t_in (g_in g)) && (O =? t_out (g_in g)) then 0 else 1) /\
         (getr regs 10 = Z_to_bv 64 0 <-> sP = n_EXP_DP (g_in g))) c.
Definition Inv_U13f30 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13f30 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\
       ((exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\
           getr regs 8 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP) /\
           getr regs 9 = Z_to_bv 64 (exp_mask (g_in g) I O P sP)) \/
        (q64 m (spk g 192) 0 /\ getr regs 8 = Z_to_bv 64 0 /\ getr regs 9 = Z_to_bv 64 0))) c.
Definition Inv_U13f34 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13f34 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\
       getr regs 22 = Z_to_bv 64 dp) c.
Definition Inv_U13f3c (g : ghost) (c : config) : Prop :=
  exists nm tk, CUTST g 0x13f3c (2 * NR g + 5)
    [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))]
    (fun regs m => getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk) c.
Definition Inv_U13f44 (g : ghost) (c : config) : Prop :=
  exists nm, CUTST g 0x13f44 (2 * NR g + 5) [(nm, bsz (t_cap_name (g_in g)))]
    (fun regs m => getr regs 20 = Z_to_bv 64 nm) c.
Definition Inv_U13f4c (g : ghost) (c : config) : Prop :=
  CUTST g 0x13f4c (2 * NR g + 5) [] (fun regs m => True) c.

End Slot.

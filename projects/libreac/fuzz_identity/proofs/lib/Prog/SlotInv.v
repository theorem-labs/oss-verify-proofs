From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel reac_identity_fw_str_c
  reac_identity_reac_ver_str_c reac_box_family_stem_c reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
Import ListNotations.
Open Scope Z_scope.

Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x15580 /\ ms_free B = 0x15440 /\ ms_realloc B = None /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x501f0 /\ ms_got_guard B = 0x1ec08 /\
  ms_ctx B = 0x50288 /\ ms_lock B = 0x50280 /\ ms_libc B = 0x50210 /\ ms_size_classes B = 0x10678 /\
  ms_small_cnt B = 0x106d8 /\ ms_med_cnt B = 0x106f3 /\ ms_debruijn B = 0x10658 /\ ms_tp B = 0x2ff80 /\
  ms_errno_off B = -164 /\ (ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32) /\
  @sk_ofl_head SH = 0x50640 /\ @sk_ofl_lock SK = 0x50638 /\ @sk_threaded SK = 0x50210 + 1 /\
  empty = 0x2fe90 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma ff_vmlock : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty -> ms_vmlock B = None.
Proof.
  intros B API LS SH SK ra empty H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & V & _) & _). exact V.
Qed.

Lemma ff_dbl : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty -> ms_debruijn_len B = 32.
Proof.
  intros B API LS SH SK ra empty H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & V) & _). exact V.
Qed.

Ltac vml_simp FF := unfold vml_lo, vml_len in *; rewrite (ff_vmlock _ _ _ _ _ _ _ FF) in *.

Definition SLOT_FRAME : Z := 368.
Definition SLOT_K : Z := SLOT_STACK.
Definition SLOT_MALLOCS : Z := 133.
Definition SLOT_REQ : Z := 256.
Definition HWT_ADDR : Z := 0x105ac.
Definition IN_SLASH : Z := 0x1034e.
Definition OUT_PAREN : Z := 0x10507.
Definition CAT : Z := 0x1dec0.
Definition CAT_N : Z := 11.
Definition CAT_ROW : Z := 296.

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
Definition bsz (cap : Z) : Z := Z.max cap 1.
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
Definition said_v (g : ghost) : Z := if n_said (g_in g) then spk g 133 else 0.
Definition stem_addr (g : ghost) : Z :=
  if n_use_said (g_in g) then spk g 133 else reac_box_family_stem_c.STEM_Addr (n_fam (g_in g)).
Definition fw_res (v cap : Z) : Z := if cap <? 8 then -1 else reac_identity_fw_str_c.L v.
Definition fw_out (m : word -> option byte) (v cap s : Z) : Prop :=
  8 <= cap -> cstr m s (reac_identity_fw_str_c.FW v).
Definition id_VER (idb : list byte) : list byte :=
  reac_identity_reac_ver_str_c.reac_ver_str_VER (RcIdentModel.major idb) (RcIdentModel.minor idb)
    (RcIdentModel.patch idb).
Definition ver_res (idb : list byte) (cap : Z) : Z :=
  if cap <? 20 then -1
  else reac_identity_reac_ver_str_c.reac_ver_str_LV (RcIdentModel.major idb) (RcIdentModel.minor idb)
         (RcIdentModel.patch idb).
Definition ver_out (m : word -> option byte) (idb : list byte) (cap s : Z) : Prop :=
  20 <= cap -> cstr m s (id_VER idb).
Definition EV1 (idb : list byte) : list byte := DEC (RcIdentModel.major idb) 1.
Definition EV2 (idb : list byte) : list byte := EV1 idb ++ [dot] ++ DEC (RcIdentModel.minor idb) 1.
Definition EV (idb : list byte) : list byte := EV2 idb ++ DEC (RcIdentModel.patch idb) 2.
Definition wn (idb : list byte) : Z := Z.of_nat (RcIdentModel.first_zero (RcIdentModel.model_name idb)).
Definition s_open : list byte := str_bytes " ("%string.
Definition s_in : list byte := str_bytes " in / "%string.
Definition s_out : list byte := str_bytes " out)"%string.
Definition dp1 (inp : list byte) : list byte := n_EXP_NM inp ++ s_open ++ DEC (t_in inp) 1.
Definition dp2 (inp : list byte) : list byte := dp1 inp ++ s_in ++ DEC (t_out inp) 1.
Definition ld1 (inp : list byte) : Z := zlen (dp1 inp).
Definition ld2 (inp : list byte) : Z := zlen (dp2 inp).
Definition dropped (l : list byte) (q : nat) : Z := if has_dash (firstn q l) then 1 else 0.
Definition cat_e (inp : list byte) : Z := CAT + CAT_ROW * (t_row inp mod CAT_N).
Definition exp_mask (inp : list byte) (I O P : Z) (sP : list byte) : Z :=
  (if (I =? t_in inp) && (O =? t_out inp) then 0 else 1) +
  (if P =? 0 then 0 else if bytes_eqb sP (n_EXP_DP inp) then 0 else 2).
Definition cat_mask (inp : list byte) (dp I O P : Z) (sP : list byte) : Z :=
  reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK (cat_e inp) (t_in inp) (t_out inp) dp I O P sP (n_EXP_DP inp).
Definition cat_entry (m : word -> option byte) (e I O P : Z) (sP : list byte) : Prop :=
  -2 ^ 31 <= I < 2 ^ 31 /\ -2 ^ 31 <= O < 2 ^ 31 /\ 0 <= P < 2 ^ 64 /\
  bytes_at rsegs m (e + 8) (le8 (Z_to_bv 64 P)) /\ bytes_at rsegs m (e + 16) (le4 (Z_to_bv 64 I)) /\
  bytes_at rsegs m (e + 20) (le4 (Z_to_bv 64 O)) /\ (P <> 0 -> cstr m P sP /\ ~ In z8 sP).

Definition IDb (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 130) (rec_id (g_in g) j).
Definition HWb (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  q64 m (spk g 24) (rec_have (g_in g) j) /\ u32 m (spk g 112) (rec_have (g_in g) j) /\
  bytes_at rsegs m (spk g 116) (rec_hwb (g_in g) j).
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ getr regs 20 = Z_to_bv 64 (g_p g + c) /\ getr regs 26 = Z_to_bv 64 (g_n g - c).
Definition G16 (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 16) (spk g 133).
Definition NRb (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 32) (NR g).
Definition REC (g : ghost) (i : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  Z.of_nat i < NR g /\ getr regs 19 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G16 g m /\ HWb g i m.
Definition PLB (g : ghost) (i : nat) (pl : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m pl (rec_pl (g_in g) i).
Definition hb_pl (g : ghost) (i : nat) (pl : Z) : list (Z * Z) := [(pl, rec_k (g_in g) i)].
Definition RKB (g : ghost) (i : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  REC g i regs m /\
  getr regs 23 = Z_to_bv 64 (rec_addr (g_in g) i) /\
  getr regs 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
  getr regs 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i).
Definition B03 (g : ghost) (i : nat) (pl : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RKB g i regs m /\ getr regs 26 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 22 = Z_to_bv 64 pl /\
  PLB g i pl m.
Definition BEF (g : ghost) (i : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 48) (rec_id (g_in g) i).
Definition AGN (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 226) (rec_id (g_in g) j).
Definition RRr (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 9 = Z_to_bv 64 (rec_r (g_in g) i).
Definition LPm (g : ghost) (i : nat) (m : word -> option byte) : Prop := q64 m (spk g 40) (rec_Lp (g_in g) i).
Definition RB12 (g : ghost) (i : nat) (pl : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  REC g i regs m /\
  getr regs 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
  getr regs 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\
  getr regs 22 = Z_to_bv 64 pl /\ PLB g i pl m /\
  IDb g (S i) m /\ AGN g (S i) m /\ BEF g i m /\ LPm g i m.
Definition S7A (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = Z_to_bv 64 (rec_addr (g_in g) i).
Definition F11 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 27 = Z_to_bv 64 (RcIdentModel.fw_milli (idS g i)).
Definition F0 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 8 = Z_to_bv 64 (RcIdentModel.has_fw (idS g i)).
Definition F2 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 18 = Z_to_bv 64 (RcIdentModel.has_model_name (idS g i)).
Definition F8 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 24 = Z_to_bv 64 (RcIdentModel.major (idS g i)).
Definition F9 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = Z_to_bv 64 (RcIdentModel.minor (idS g i)).
Definition F10 (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 26 = Z_to_bv 64 (RcIdentModel.patch (idS g i)).
Definition FALL (g : ghost) (i : nat) (regs : bvmap 5 word) : Prop :=
  F11 g i regs /\ F0 g i regs /\ F2 g i regs /\ F8 g i regs /\ F9 g i regs /\ F10 g i regs.
Definition VB (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_REAC_VERSION.
Definition NMA (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_MODEL_NAME.
Definition FWA (g : ghost) (i : nat) : Prop :=
  rec_r (g_in g) i = 1 /\ rec_addr (g_in g) i = RcIdentModel.ADDR_FIRMWARE.

Definition CB (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  1 <= NR g /\ NRb g m /\ G16 g m /\ HWb g (NRn g) m /\ CUR g (cT (g_in g)) regs /\ IDb g (NRn g) m.
Definition TID (g : ghost) (m : word -> option byte) : Prop := G16 g m /\ IDb g (NRn g) m.
Definition TLr (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\ getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ q64 m (spk g 40) (t_cap_disp (g_in g)).
Definition TL (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 8 = Z_to_bv 64 (t_fam_raw (g_in g)) /\ TLr g regs m.
Definition NMB (g : ghost) (nm tk dp : Z) : list (Z * Z) :=
  [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g))); (dp, bsz (t_cap_disp (g_in g)))].
Definition OUTS (g : ghost) (nm tk dp : Z) (m : word -> option byte) : Prop :=
  n_r (g_in g) = 0 ->
  cstr m nm (n_EXP_NM (g_in g)) /\ cstr m tk (n_TK (g_in g)) /\ cstr m dp (n_EXP_DP (g_in g)).
Definition NB (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\ n_wok (g_in g) = true /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\ q64 m (spk g 40) (t_cap_disp (g_in g)) /\ OUTS g nm tk dp m.
Definition N0 (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NB g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\ getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
  q64 m (spk g 16) (stem_addr g) /\ cstr m (stem_addr g) (n_stem (g_in g)).
Definition N1 (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  N0 g nm tk dp regs m /\ getr regs 8 = Z_to_bv 64 (spk g 176) /\
  cstr m (spk g 176) (n_W4 (g_in g)) /\ q64 m (spk g 200) 4 /\ q64 m (spk g 168) 0.
Definition NC (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NB g nm tk dp regs m /\ getr regs 26 = Z_to_bv 64 (n_ln (g_in g)) /\
  getr regs 19 = Z_to_bv 64 (t_in (g_in g)) /\ q64 m (spk g 32) (t_row (g_in g)) /\
  cstr m (spk g 226) (n_EXP_NM (g_in g)).
Definition IRb (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\
  getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\ getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
  OUTS g nm tk dp m /\
  (n_r (g_in g) = 0 -> cstr m (spk g 226) (n_EXP_NM (g_in g)) /\ cstr m (spk g 48) (n_EXP_DP (g_in g))).
Definition IRc (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb g (NRn g) m /\ getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (n_r (g_in g)) /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
  OUTS g nm tk dp m /\ n_r (g_in g) = 0 /\ cstr m (spk g 226) (n_EXP_NM (g_in g)) /\
  cstr m (spk g 48) (n_EXP_DP (g_in g)).
Definition IR (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IRb g nm tk dp regs m /\ n_r (g_in g) = 0.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Context {RzCi : RzC} {RzAi : RzA B API}.
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
  rz_sroom (g_b g) /\
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

Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> Rz segs c (Post g).
Definition Hrec (X : ghost -> nat -> config -> Prop) (i : nat) : Prop :=
  forall g c, X g i c -> Rz segs c (Post g).

Definition A0 (g : ghost) (regs : bvmap 5 word) : Prop :=
  getr regs 9 = Z_to_bv 64 (g_n g) /\ getr regs 20 = Z_to_bv 64 (g_p g).

Definition Inv_K12eec (g : ghost) (c : config) : Prop :=
  CUTST g 0x12eec 0 [] (fun regs m => A0 g regs) c.
Definition Inv_K12ef4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12ef4 0 [] (fun regs m => A0 g regs /\ IDb g 0 m) c.
Definition Inv_K12f08 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f08 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_K12f24 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f24 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 8 = Z_to_bv 64 (-1) /\
    getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_K12f38 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f38 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_K12f54 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f54 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_K12f70 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f70 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K12f78 (g : ghost) (c : config) : Prop :=
  CUTST g 0x12f78 0 [] (fun regs m => A0 g regs /\ IDb g 0 m /\ getr regs 10 = Z_to_bv 64 0) c.

Definition Inv_K12fc4_at (g : ghost) (i : nat) (c : config) : Prop :=
  CUTST g 0x12fc4 (2 * Z.of_nat i) []
    (fun regs m => REC g i regs m /\ CUR g (rec_c (g_in g) i) regs /\ IDb g i m) c.
Definition Inv_K13068_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13068 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => RKB g i regs m /\ IDb g i m /\ getr regs 26 = Z_to_bv 64 (rec_Lp (g_in g) i) /\
       getr regs 10 = Z_to_bv 64 pl) c.
Definition Inv_K13088_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13088 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ IDb g i m) c.
Definition Inv_K13098_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13098 (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ IDb g i m /\ BEF g i m) c.
Definition Inv_K130ac_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x130ac (2 * Z.of_nat i + 1) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\
       getr regs 10 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_K130bc_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x130bc (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       getr regs 10 = Z_to_bv 64 gb) c.
Definition Inv_K130dc_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x130dc (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       getr regs 24 = Z_to_bv 64 gb /\ LPm g i m /\ PLB g i gb m) c.
Definition Inv_K130f8_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x130f8 (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       getr regs 24 = Z_to_bv 64 gb /\ LPm g i m /\ PLB g i gb m /\
       b8 m (gb + rec_k (g_in g) i) 0x5a /\ AGN g i m) c.
Definition Inv_K1310c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl gb, CUTST g 0x1310c (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)])
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\
       getr regs 24 = Z_to_bv 64 gb /\ LPm g i m /\ PLB g i gb m /\
       b8 m (gb + rec_k (g_in g) i) 0x5a /\ AGN g (S i) m /\
       getr regs 10 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_K13118_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13118 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\ LPm g i m /\
       AGN g (S i) m /\ getr regs 25 = Z_to_bv 64 (rec_r (g_in g) i)) c.
Definition Inv_K13144_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13144 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => B03 g i pl regs m /\ IDb g (S i) m /\ BEF g i m /\ RRr g i regs /\ LPm g i m /\
       AGN g (S i) m /\ getr regs 25 = Z_to_bv 64 (rec_r (g_in g) i) /\ F11 g i regs /\ F0 g i regs /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13188_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13188 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K1328c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x1328c (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\
       rec_r (g_in g) i = 0 /\ getr regs 10 = Z_to_bv 64 (RcIdentModel.has_reac_version (idS g i))) c.
Definition Inv_K132d8_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x132d8 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       getr regs 10 = Z_to_bv 64 (RcIdentModel.has_reac_version (idS g i))) c.
Definition Inv_K13440_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13440 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ NMA g i) c.
Definition FWL (g : ghost) (i : nat) (pl t : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ FWA g i /\
  getr regs 14 = Z_to_bv 64 10 /\ getr regs 10 = Z_to_bv 64 (4 - t) /\ getr regs 11 = Z_to_bv 64 (pl + t) /\
  (forall j, 0 <= j < t -> RcIdentModel.bz (RcIdentModel.nthb (rec_pl (g_in g) i) (Z.to_nat j)) <= 9).
Definition Inv_K131c8_at (g : ghost) (i : nat) (t : Z) (c : config) : Prop :=
  exists pl, CUTST g 0x131c8 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => 0 <= t <= 3 /\ FWL g i pl t regs m) c.
Definition Inv_K131dc_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x131dc (2 * Z.of_nat i + 2) (hb_pl g i pl) (fun regs m => FWL g i pl 4 regs m) c.
Definition Inv_K13220_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13220 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ FWA g i /\
       RcIdentModel.fw_milli (idS g i) <= 9999 /\ getr regs 10 = Z_to_bv 64 5 /\
       cstr m (spk g 176) (reac_identity_fw_str_c.FW (RcIdentModel.fw_milli (idS g i)))) c.
Definition Inv_K13230_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13230 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ getr regs 9 = Z_to_bv 64 5 /\
       FWA g i /\ RcIdentModel.fw_milli (idS g i) <= 9999 /\
       cstr m (spk g 176) (reac_identity_fw_str_c.FW (RcIdentModel.fw_milli (idS g i)))) c.
Definition Inv_K1329c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x1329c (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\
       rec_r (g_in g) i = 0 /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K132f4_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x132f4 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K1334c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x1334c (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 168) (zlen (EV1 (idS g i))) /\ bytes_at rsegs m (spk g 176) (EV1 (idS g i))) c.
Definition Inv_K1337c_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x1337c (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\
       getr regs 9 = Z_to_bv 64 (spk g 176) /\ VB g i /\
       q64 m (spk g 168) (zlen (EV2 (idS g i))) /\ bytes_at rsegs m (spk g 176) (EV2 (idS g i))) c.
Definition Inv_K13390_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13390 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\
       getr regs 9 = Z_to_bv 64 (spk g 176) /\ VB g i /\
       q64 m (spk g 168) (zlen (EV (idS g i))) /\ bytes_at rsegs m (spk g 176) (EV (idS g i))) c.
Definition Inv_K133b4_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x133b4 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ F11 g i regs /\ F2 g i regs /\ F8 g i regs /\
       F9 g i regs /\ F10 g i regs /\ getr regs 9 = Z_to_bv 64 (spk g 176) /\ VB g i /\
       q64 m (spk g 168) (zlen (EV (idS g i))) /\ cstr m (spk g 176) (EV (idS g i)) /\
       getr regs 8 = Z_to_bv 64 (zlen (EV (idS g i))) /\
       getr regs 10 = Z_to_bv 64 (reac_identity_reac_ver_str_c.reac_ver_str_LV (RcIdentModel.major (idS g i))
         (RcIdentModel.minor (idS g i)) (RcIdentModel.patch (idS g i))) /\
       cstr m (spk g 200) (id_VER (idS g i))) c.
Definition Inv_K133d0_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x133d0 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ F11 g i regs /\ F8 g i regs /\
       F9 g i regs /\ F10 g i regs /\ getr regs 9 = Z_to_bv 64 (spk g 176) /\ VB g i /\
       q64 m (spk g 168) (zlen (EV (idS g i))) /\ cstr m (spk g 176) (EV (idS g i)) /\
       getr regs 8 = Z_to_bv 64 (zlen (EV (idS g i))) /\ cstr m (spk g 200) (id_VER (idS g i)) /\
       getr regs 18 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13454_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13454 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ FALL g i regs /\ RRr g i regs /\ NMA g i /\
       getr regs 23 = Z_to_bv 64 (spk g 133) /\ getr regs 10 = Z_to_bv 64 (spk g 133 + wn (idS g i))) c.
Definition Inv_K13480_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x13480 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => RB12 g i pl regs m /\ F11 g i regs /\ F8 g i regs /\ F9 g i regs /\ F10 g i regs /\
       NMA g i /\ getr regs 23 = Z_to_bv 64 (spk g 133) /\
       getr regs 18 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 9 = Z_to_bv 64 (wn (idS g i)) /\
       getr regs 8 = Z_to_bv 64 (wn (idS g i) + 1) /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K134c8_at (g : ghost) (i : nat) (c : config) : Prop :=
  exists pl, CUTST g 0x134c8 (2 * Z.of_nat i + 2) (hb_pl g i pl)
    (fun regs m => Z.of_nat i < NR g /\ getr regs 19 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G16 g m /\
       HWb g (S i) m /\ IDb g (S i) m /\
       getr regs 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\ getr regs 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
       getr regs 18 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 22 = Z_to_bv 64 pl) c.

Definition Inv_K12fc4 (g : ghost) (c : config) : Prop := exists i, Inv_K12fc4_at g i c.
Definition Inv_K13068 (g : ghost) (c : config) : Prop := exists i, Inv_K13068_at g i c.
Definition Inv_K13088 (g : ghost) (c : config) : Prop := exists i, Inv_K13088_at g i c.
Definition Inv_K13098 (g : ghost) (c : config) : Prop := exists i, Inv_K13098_at g i c.
Definition Inv_K130ac (g : ghost) (c : config) : Prop := exists i, Inv_K130ac_at g i c.
Definition Inv_K130bc (g : ghost) (c : config) : Prop := exists i, Inv_K130bc_at g i c.
Definition Inv_K130dc (g : ghost) (c : config) : Prop := exists i, Inv_K130dc_at g i c.
Definition Inv_K130f8 (g : ghost) (c : config) : Prop := exists i, Inv_K130f8_at g i c.
Definition Inv_K1310c (g : ghost) (c : config) : Prop := exists i, Inv_K1310c_at g i c.
Definition Inv_K13118 (g : ghost) (c : config) : Prop := exists i, Inv_K13118_at g i c.
Definition Inv_K13144 (g : ghost) (c : config) : Prop := exists i, Inv_K13144_at g i c.
Definition Inv_K13188 (g : ghost) (c : config) : Prop := exists i, Inv_K13188_at g i c.
Definition Inv_K1328c (g : ghost) (c : config) : Prop := exists i, Inv_K1328c_at g i c.
Definition Inv_K132d8 (g : ghost) (c : config) : Prop := exists i, Inv_K132d8_at g i c.
Definition Inv_K13440 (g : ghost) (c : config) : Prop := exists i, Inv_K13440_at g i c.
Definition Inv_K131c8 (g : ghost) (c : config) : Prop := exists i t, Inv_K131c8_at g i t c.
Definition Inv_K131dc (g : ghost) (c : config) : Prop := exists i, Inv_K131dc_at g i c.
Definition Inv_K13220 (g : ghost) (c : config) : Prop := exists i, Inv_K13220_at g i c.
Definition Inv_K13230 (g : ghost) (c : config) : Prop := exists i, Inv_K13230_at g i c.
Definition Inv_K1329c (g : ghost) (c : config) : Prop := exists i, Inv_K1329c_at g i c.
Definition Inv_K132f4 (g : ghost) (c : config) : Prop := exists i, Inv_K132f4_at g i c.
Definition Inv_K1334c (g : ghost) (c : config) : Prop := exists i, Inv_K1334c_at g i c.
Definition Inv_K1337c (g : ghost) (c : config) : Prop := exists i, Inv_K1337c_at g i c.
Definition Inv_K13390 (g : ghost) (c : config) : Prop := exists i, Inv_K13390_at g i c.
Definition Inv_K133b4 (g : ghost) (c : config) : Prop := exists i, Inv_K133b4_at g i c.
Definition Inv_K133d0 (g : ghost) (c : config) : Prop := exists i, Inv_K133d0_at g i c.
Definition Inv_K13454 (g : ghost) (c : config) : Prop := exists i, Inv_K13454_at g i c.
Definition Inv_K13480 (g : ghost) (c : config) : Prop := exists i, Inv_K13480_at g i c.
Definition Inv_K134c8 (g : ghost) (c : config) : Prop := exists i, Inv_K134c8_at g i c.

Definition Inv_K134e4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x134e4 (2 * NR g) []
    (fun regs m => CB g regs m /\ getr regs 19 = Z_to_bv 64 (NR g)) c.
Definition Inv_K134ec (g : ghost) (c : config) : Prop :=
  CUTST g 0x134ec (2 * NR g) []
    (fun regs m => CB g regs m /\ getr regs 19 = Z_to_bv 64 (NR g) /\
       getr regs 10 = Z_to_bv 64 (FAM (idT (g_in g)))) c.
Definition HW_miss (g : ghost) (j : nat) : Prop :=
  forall j', (j' < j)%nat -> map bv_unsigned (hwbT (g_in g)) <> HWT j'.
Definition Inv_K13508_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x13508 (2 * NR g) []
    (fun regs m => CB g regs m /\ haveT (g_in g) = 1 /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       getr regs 19 = Z_to_bv 64 (spk g 116) /\ getr regs 8 = Z_to_bv 64 (3 - Z.of_nat j) /\
       getr regs 18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) /\ (j < 3)%nat /\ HW_miss g j) c.
Definition Inv_K13508 (g : ghost) (c : config) : Prop := exists j, Inv_K13508_at g j c.
Definition Inv_K13c68_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x13c68 (2 * NR g) []
    (fun regs m => CB g regs m /\ haveT (g_in g) = 1 /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       getr regs 18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) /\ (j < 3)%nat /\
       map bv_unsigned (hwbT (g_in g)) = HWT j /\ HW_miss g j) c.
Definition Inv_K13c68 (g : ghost) (c : config) : Prop := exists j, Inv_K13c68_at g j c.
Definition Inv_K1352c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1352c 0 []
    (fun regs m => g_n g = 0 /\ getr regs 9 = Z_to_bv 64 0 /\ getr regs 20 = Z_to_bv 64 (g_p g) /\
       G16 g m /\ IDb g 0 m) c.
Definition Inv_K13530 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13530 0 []
    (fun regs m => NR g = 0 /\ CUR g (cT (g_in g)) regs /\ G16 g m /\ IDb g 0 m) c.
Definition Inv_K1353c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1353c (2 * NR g) []
    (fun regs m => CUR g (cT (g_in g)) regs /\ TID g m /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       fam_hw (haveT (g_in g)) (hwbT (g_in g)) = 0) c.
Definition Inv_K13540 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13540 (2 * NR g) []
    (fun regs m => CUR g (cT (g_in g)) regs /\ TID g m /\ getr regs 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       haveT (g_in g) = 0 /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13544 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13544 (2 * NR g) []
    (fun regs m => CUR g (cT (g_in g)) regs /\ TID g m /\
       FAM (idT (g_in g)) = fam_hw (haveT (g_in g)) (hwbT (g_in g))) c.

Definition D594 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 22 = Z_to_bv 64 (t_cap_fw (g_in g)) /\
  getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\ getr regs 27 = Z_to_bv 64 (tb (g_in g) 9) /\
  getr regs 20 = Z_to_bv 64 (tb (g_in g) 10).
Definition Inv_K13594 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13594 (2 * NR g) [] (D594 g) c.
Definition Inv_K135a0 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135a0 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => D594 g regs m /\ getr regs 10 = Z_to_bv 64 s) c.
Definition E5c0 (g : ghost) (s : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\
  getr regs 22 = Z_to_bv 64 (t_cap_fw (g_in g)) /\ getr regs 23 = Z_to_bv 64 s /\
  getr regs 20 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_K135c0 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135c0 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E5c0 g s regs m /\ getr regs 10 = Z_to_bv 64 (fw_res (fwT g) (t_cap_fw (g_in g))) /\
       fw_out m (fwT g) (t_cap_fw (g_in g)) s) c.
Definition Inv_K135cc (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135cc (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E5c0 g s regs m /\ fw_out m (fwT g) (t_cap_fw (g_in g)) s) c.
Definition Inv_K135dc (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135dc (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E5c0 g s regs m /\
       getr regs 10 = Z_to_bv 64 (fw_res (t_any_fw (g_in g)) (t_cap_fw (g_in g))) /\
       fw_out m (t_any_fw (g_in g)) (t_cap_fw (g_in g)) s) c.
Definition Inv_K135e8 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135e8 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E5c0 g s regs m /\ fw_out m (t_any_fw (g_in g)) (t_cap_fw (g_in g)) s) c.
Definition E5f0 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\
  getr regs 20 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_K135f0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x135f0 (2 * NR g + 1) [] (E5f0 g) c.
Definition Inv_K135fc (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x135fc (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E5f0 g regs m /\ getr regs 10 = Z_to_bv 64 s) c.
Definition Inv_K1361c (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x1361c (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E5f0 g regs m /\ getr regs 22 = Z_to_bv 64 s /\
       getr regs 10 = Z_to_bv 64 (ver_res (idT (g_in g)) (t_cap_ver (g_in g))) /\
       ver_out m (idT (g_in g)) (t_cap_ver (g_in g)) s) c.
Definition Inv_K13628 (g : ghost) (c : config) : Prop :=
  exists s, CUTST g 0x13628 (2 * NR g + 2) [(s, bsz (t_cap_ver (g_in g)))]
    (fun regs m => E5f0 g regs m /\ getr regs 22 = Z_to_bv 64 s /\
       ver_out m (idT (g_in g)) (t_cap_ver (g_in g)) s) c.
Definition F630 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TL g regs m /\ getr regs 20 = Z_to_bv 64 (t_any_fw (g_in g)).
Definition Inv_K13630 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13630 (2 * NR g + 2) [] (F630 g) c.
Definition Inv_K13664 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13664 (2 * NR g + 2) []
    (fun regs m => F630 g regs m /\ getr regs 21 = Z_to_bv 64 (t_any_fw (g_in g) / 1000) /\
       getr regs 22 = Z_to_bv 64 (spk g 48) /\
       q64 m (spk g 176) (zlen (DEC (t_any_fw (g_in g) / 1000) 1)) /\
       bytes_at rsegs m (spk g 48) (DEC (t_any_fw (g_in g) / 1000) 1)) c.
Definition Inv_K136a4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136a4 (2 * NR g + 2) []
    (fun regs m => F630 g regs m /\ getr regs 21 = Z_to_bv 64 (t_any_fw (g_in g) / 1000) /\
       getr regs 22 = Z_to_bv 64 (spk g 48) /\ q64 m (spk g 176) (zlen (t_EF (g_in g))) /\
       bytes_at rsegs m (spk g 48) (t_EF (g_in g))) c.
Definition F6c0 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  F630 g regs m /\ getr regs 21 = Z_to_bv 64 (zlen (t_EF (g_in g))) /\
  getr regs 22 = Z_to_bv 64 (spk g 48 + zlen (t_EF (g_in g))) /\ cstr m (spk g 48) (t_EF (g_in g)) /\
  cstr m (spk g 226) (reac_identity_fw_str_c.FW (t_any_fw (g_in g))).
Definition Inv_K136c0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136c0 (2 * NR g + 2) []
    (fun regs m => F6c0 g regs m /\ getr regs 10 = Z_to_bv 64 (reac_identity_fw_str_c.L (t_any_fw (g_in g)))) c.
Definition Inv_K136dc (g : ghost) (c : config) : Prop :=
  CUTST g 0x136dc (2 * NR g + 2) []
    (fun regs m => F6c0 g regs m /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
       getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K136f0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136f0 (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
       t_fam_raw (g_in g) < 128 /\ getr regs 10 = Z_to_bv 64 (FAM (idT (g_in g)))) c.
Definition Inv_K136f8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136f8 (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
       128 <= t_fam_raw (g_in g)) c.
Definition Inv_K13704 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13704 (2 * NR g + 2) []
    (fun regs m => TID g m /\ TL g regs m /\ getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\
       getr regs 26 = Z_to_bv 64 (n_fam (g_in g)) /\
       getr regs 10 = Z_to_bv 64 (reac_box_family_stem_c.STEM_Addr (n_fam (g_in g)))) c.
Definition G71c (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ TLr g regs m /\ getr regs 8 = Z_to_bv 64 (RcIdentModel.has_model_name (idT (g_in g))) /\
  getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\ getr regs 26 = Z_to_bv 64 (n_fam (g_in g)).
Definition Inv_K1371c (g : ghost) (c : config) : Prop :=
  exists nm, CUTST g 0x1371c (2 * NR g + 3) [(nm, bsz (t_cap_name (g_in g)))]
    (fun regs m => G71c g regs m /\ getr regs 10 = Z_to_bv 64 nm) c.
Definition Inv_K13734 (g : ghost) (c : config) : Prop :=
  exists nm tk, CUTST g 0x13734 (2 * NR g + 4)
    [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))]
    (fun regs m => G71c g regs m /\ getr regs 20 = Z_to_bv 64 nm /\
       getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 10 = Z_to_bv 64 tk) c.
Definition Inv_K13748 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13748 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G71c g regs m /\ getr regs 20 = Z_to_bv 64 nm /\
       getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 21 = Z_to_bv 64 tk /\
       getr regs 10 = Z_to_bv 64 dp) c.
Definition G78c (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  TID g m /\ getr regs 8 = Z_to_bv 64 (RcIdentModel.has_model_name (idT (g_in g))) /\
  getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\ getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
  getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\ getr regs 22 = Z_to_bv 64 dp /\
  getr regs 23 = Z_to_bv 64 (t_cap_tok (g_in g)) /\ getr regs 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\
  getr regs 25 = Z_to_bv 64 (said_v g) /\ getr regs 26 = Z_to_bv 64 (n_fam (g_in g)) /\
  getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) /\ q64 m (spk g 40) (t_cap_disp (g_in g)) /\
  q64 m (spk g 0) dp /\ q64 m (spk g 8) (t_cap_disp (g_in g)).
Definition Inv_K1378c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x1378c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G78c g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (-1)) c.
Definition Inv_K137c0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x137c0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => G78c g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_r (g_in g)) /\ OUTS g nm tk dp m) c.

Definition Inv_K138bc (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x138bc (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N0 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       getr regs 8 = Z_to_bv 64 (spk g 176) /\ q64 m (spk g 200) 2 /\ q64 m (spk g 168) 0 /\
       bytes_at rsegs m (spk g 176) (DEC (t_in (g_in g)) 2)) c.
Definition Inv_K138d0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x138d0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N0 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       getr regs 8 = Z_to_bv 64 (spk g 176) /\ q64 m (spk g 200) 4 /\ q64 m (spk g 168) 0 /\
       bytes_at rsegs m (spk g 176) (n_W4 (g_in g))) c.
Definition Inv_K138f4_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x138f4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       0 <= t < zlen (n_stem (g_in g)) /\ getr regs 26 = Z_to_bv 64 t /\
       getr regs 10 = Z_to_bv 64 (spk g 222 + t) /\ getr regs 12 = Z_to_bv 64 (stem_addr g + 1) /\
       getr regs 11 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat t))) /\
       bytes_at rsegs m (spk g 226) (firstn (Z.to_nat t) (n_stem (g_in g)))) c.
Definition Inv_K138f4 (g : ghost) (c : config) : Prop := exists t, Inv_K138f4_at g t c.
Definition Inv_K1390c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x1390c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       getr regs 26 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       getr regs 10 = Z_to_bv 64 (spk g 222 + zlen (n_stem (g_in g))) /\
       bytes_at rsegs m (spk g 226) (n_stem (g_in g))) c.
Definition Inv_K13968 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13968 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       getr regs 26 = Z_to_bv 64 (zlen (n_stem (g_in g))) /\
       bytes_at rsegs m (spk g 226) (n_stem (g_in g)) /\ n_ends_w4 (g_in g) = false) c.
Definition Inv_K1398c_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x1398c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       n_ends_w4 (g_in g) = false /\ 0 <= t <= 3 /\
       bytes_at rsegs m (spk g 226) (n_stem (g_in g) ++ [dash] ++ firstn (Z.to_nat t) (n_W4 (g_in g))) /\
       getr regs 26 = Z_to_bv 64 (zlen (n_stem (g_in g)) + 1 + t) /\
       getr regs 11 = Z_to_bv 64 (spk g 226 + zlen (n_stem (g_in g)) + 1 + t) /\
       getr regs 12 = Z_to_bv 64 (spk g 177 + t) /\
       getr regs 10 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_W4 (g_in g)) (Z.to_nat t)))) c.
Definition Inv_K1398c (g : ghost) (c : config) : Prop := exists t, Inv_K1398c_at g t c.
Definition Inv_K139a4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x139a4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => N1 g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\
       getr regs 26 = Z_to_bv 64 (n_ln (g_in g)) /\ bytes_at rsegs m (spk g 226) (n_EXP_NM (g_in g))) c.
Definition H9a (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  N1 g nm tk dp regs m /\ getr regs 26 = Z_to_bv 64 (n_ln (g_in g)) /\ q64 m (spk g 32) (t_row (g_in g)) /\
  cstr m (spk g 226) (n_EXP_NM (g_in g)).
Definition H9b (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  H9a g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_in (g_in g)).
Definition Inv_K139cc_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x139cc (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H9b g nm tk dp regs m /\ 0 <= t < n_ln (g_in g) /\
       getr regs 12 = Z_to_bv 64 (spk g 227) /\ getr regs 13 = Z_to_bv 64 (spk g 48) /\
       getr regs 11 = Z_to_bv 64 t /\
       getr regs 10 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (Z.to_nat t))) /\
       bytes_at rsegs m (spk g 48) (firstn (Z.to_nat t) (n_EXP_NM (g_in g)))) c.
Definition Inv_K139cc (g : ghost) (c : config) : Prop := exists t, Inv_K139cc_at g t c.
Definition Inv_K139ec (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x139ec (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H9a g nm tk dp regs m /\ getr regs 19 = Z_to_bv 64 (t_row (g_in g)) /\ b8 m (spk g 226) 0) c.
Definition Inv_K139f4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x139f4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H9b g nm tk dp regs m /\ getr regs 14 = Z_to_bv 64 (n_ln (g_in g)) /\
       bytes_at rsegs m (spk g 48) (n_EXP_NM (g_in g))) c.
Definition HAb (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NC g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\ getr regs 8 = Z_to_bv 64 (spk g 48) /\
  q64 m (spk g 168) (ld1 (g_in g)).
Definition Inv_K13a2c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a2c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HAb g nm tk dp regs m /\ getr regs 27 = Z_to_bv 64 32 /\
       bytes_at rsegs m (spk g 48) (dp1 (g_in g))) c.
Definition Inv_K13a40_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a40 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HAb g nm tk dp regs m /\ 0 <= t <= 5 /\
       bytes_at rsegs m (spk g 48) (dp1 (g_in g) ++ firstn (Z.to_nat t) s_in) /\
       getr regs 12 = Z_to_bv 64 (ld1 (g_in g) + t) /\ getr regs 11 = Z_to_bv 64 (ld1 (g_in g) + 6) /\
       getr regs 10 = Z_to_bv 64 (IN_SLASH + 1 + t) /\
       getr regs 27 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb s_in (Z.to_nat t)))) c.
Definition Inv_K13a40 (g : ghost) (c : config) : Prop := exists t, Inv_K13a40_at g t c.
Definition Inv_K13a58 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a58 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HAb g nm tk dp regs m /\ bytes_at rsegs m (spk g 48) (dp1 (g_in g) ++ s_in) /\
       getr regs 12 = Z_to_bv 64 (ld1 (g_in g) + 6) /\ getr regs 27 = Z_to_bv 64 0) c.
Definition HBb (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NC g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 18 = Z_to_bv 64 (spk g 48) /\ q64 m (spk g 168) (ld2 (g_in g)).
Definition Inv_K13a74 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a74 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HBb g nm tk dp regs m /\ bytes_at rsegs m (spk g 48) (dp2 (g_in g))) c.
Definition Inv_K13a94_at (g : ghost) (t : Z) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13a94 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HBb g nm tk dp regs m /\ 0 <= t <= 4 /\
       bytes_at rsegs m (spk g 48) (dp2 (g_in g) ++ firstn (Z.to_nat t) s_out) /\
       getr regs 8 = Z_to_bv 64 (- t) /\ getr regs 13 = Z_to_bv 64 (-5) /\
       getr regs 27 = Z_to_bv 64 (ld2 (g_in g)) /\ getr regs 10 = Z_to_bv 64 (spk g 48 + ld2 (g_in g) + t) /\
       getr regs 12 = Z_to_bv 64 (OUT_PAREN + 1 + t) /\
       getr regs 11 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb s_out (Z.to_nat t)))) c.
Definition Inv_K13a94 (g : ghost) (c : config) : Prop := exists t, Inv_K13a94_at g t c.
Definition Inv_K13aac (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13aac (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => HBb g nm tk dp regs m /\ bytes_at rsegs m (spk g 48) (n_EXP_DP (g_in g)) /\
       getr regs 8 = Z_to_bv 64 (-5) /\ getr regs 27 = Z_to_bv 64 (ld2 (g_in g)) /\
       getr regs 10 = Z_to_bv 64 (spk g 48 + ld2 (g_in g) + 5)) c.
Definition H17b (g : ghost) (nm tk dp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  NC g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_out (g_in g)) /\
  getr regs 18 = Z_to_bv 64 (t_out (g_in g)) /\ getr regs 8 = Z_to_bv 64 (-5) /\
  getr regs 27 = Z_to_bv 64 (ld2 (g_in g)) /\ cstr m (spk g 48) (n_EXP_DP (g_in g)).
Definition Inv_K13ac8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13ac8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H17b g nm tk dp regs m /\ n_ln (g_in g) < t_cap_name (g_in g) /\
       (has_dash (n_EXP_NM (g_in g)) = true -> getr regs 10 <> Z_to_bv 64 0) /\
       (has_dash (n_EXP_NM (g_in g)) = false -> getr regs 10 = Z_to_bv 64 0)) c.
Definition Inv_K13af4 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13af4 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => H17b g nm tk dp regs m /\ t_cap_name (g_in g) <= n_ln (g_in g)) c.

Definition Inv_K13b18 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b18 (2 * NR g + 5) (NMB g nm tk dp) (IRb g nm tk dp) c.
Definition Inv_K13b24 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b24 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_ln (g_in g))) c.
Definition Inv_K13b34 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b34 (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_K13b3c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b3c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (zlen (n_TK (g_in g)))) c.
Definition Inv_K13b4c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b4c (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_K13b54 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b54 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (n_ld (g_in g))) c.
Definition Inv_K13b64 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b64 (2 * NR g + 5) (NMB g nm tk dp) (IR g nm tk dp) c.
Definition Inv_K13b70 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b70 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13b80 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b80 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13b9c_at (g : ghost) (q : nat) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13b9c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ (q < length (n_EXP_NM (g_in g)))%nat /\
       getr regs 13 = Z_to_bv 64 45 /\
       getr regs 14 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q)) /\
       getr regs 11 = Z_to_bv 64 (nm + Z.of_nat q + 1) /\
       getr regs 12 = Z_to_bv 64 (dropped (n_EXP_NM (g_in g)) q) /\
       getr regs 10 = Z_to_bv 64 (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q)) c.
Definition Inv_K13b9c (g : ghost) (c : config) : Prop := exists q, Inv_K13b9c_at g q c.
Definition Inv_K13be0 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13be0 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ getr regs 10 = Z_to_bv 64 (zlen (n_TK (g_in g)))) c.
Definition Inv_K13bf8 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13bf8 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 176) CAT_N /\ getr regs 10 = Z_to_bv 64 CAT) c.
Definition Inv_K13c48 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c48 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 176) 0) c.
Definition Inv_K13c28 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c28 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\ getr regs 9 = Z_to_bv 64 (t_in (g_in g)) /\
       exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\
         getr regs 23 = Z_to_bv 64 CAT /\ getr regs 19 = Z_to_bv 64 (cat_e (g_in g)) /\
         getr regs 10 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP)) c.
Definition Inv_K13c5c (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c5c (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IR g nm tk dp regs m /\ q64 m (spk g 176) 0 /\ getr regs 10 = Z_to_bv 64 0) c.
Definition Inv_K13c60 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c60 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\ getr regs 23 = Z_to_bv 64 0 /\ getr regs 23 = Z_to_bv 64 CAT) c.
Definition Inv_K13c88 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c88 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\
       exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\ P <> 0 /\
         getr regs 19 = Z_to_bv 64 (cat_e (g_in g)) /\
         getr regs 8 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP) /\
         getr regs 9 = Z_to_bv 64 (if (I =? t_in (g_in g)) && (O =? t_out (g_in g)) then 0 else 1) /\
         (getr regs 10 = Z_to_bv 64 0 <-> sP = n_EXP_DP (g_in g))) c.
Definition Inv_K13c94 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c94 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => IRc g nm tk dp regs m /\
       ((exists I O P sP, cat_entry m (cat_e (g_in g)) I O P sP /\
           getr regs 8 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP) /\
           getr regs 9 = Z_to_bv 64 (exp_mask (g_in g) I O P sP)) \/
        (q64 m (spk g 176) 0 /\ getr regs 8 = Z_to_bv 64 0 /\ getr regs 9 = Z_to_bv 64 0))) c.
Definition Inv_K13c98 (g : ghost) (c : config) : Prop :=
  exists nm tk dp, CUTST g 0x13c98 (2 * NR g + 5) (NMB g nm tk dp)
    (fun regs m => getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk /\
       getr regs 22 = Z_to_bv 64 dp) c.
Definition Inv_K13ca0 (g : ghost) (c : config) : Prop :=
  exists nm tk, CUTST g 0x13ca0 (2 * NR g + 5)
    [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))]
    (fun regs m => getr regs 20 = Z_to_bv 64 nm /\ getr regs 21 = Z_to_bv 64 tk) c.
Definition Inv_K13ca8 (g : ghost) (c : config) : Prop :=
  exists nm, CUTST g 0x13ca8 (2 * NR g + 5) [(nm, bsz (t_cap_name (g_in g)))]
    (fun regs m => getr regs 20 = Z_to_bv 64 nm) c.
Definition Inv_K13cb0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13cb0 (2 * NR g + 5) [] (fun regs m => True) c.

End Slot.

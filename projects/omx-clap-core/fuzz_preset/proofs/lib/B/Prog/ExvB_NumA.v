(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only as the CUT_CN_MN premise / named step hypotheses (owner ruling 09:3xZ). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece A of lib/B/Prog/ExvB_NumCut.v: `exn_A : EXN_A B ARx SK E pos`, the cut CN
   (exv_pc 0x278, B 0x837a4) to CT (exv_pc 0xa70, B 0x83f9c) or CL (exv_pc 0x324, B 0x83850).
   Rule 24: proves no function (kind: segment lemma).
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, rows 160-202,
   B 0x837a4-0x8384c, and the two partial-granule arms rows 744-747 (B 0x840c4) and 792-794 (B 0x84184)):
     `sb zero, 4(s10)` / `sb zero, 8(s10)` open the frame's `end` and `num` slots (EXN_fsh);
     `bne s11, '-'`; on '-' the UBSan check `beq a1, -1 -> unimp` (NOT taken: a1 = x0 + i1 lies in [4096, 2 ^ 47),
     from src_rd) and s6 := a1 + 1; `li s5, -1`; `bgeu s6, a2 -> CT` (no byte after the sign);
     the ASan check of s6 (its partial-granule arm returns to B 0x837dc; the errpath_load1 arm is unreachable: the
     engine's obligation range_addressable [s6, s6 + 1), from src_rd) and `lbu`; the lead-digit test (B 0x837e0-
     0x837e8, exn_first_digit_digit) -> CT; `bne a0, '0' -> 0x83824`; on '0' the UBSan check `beq s6, -1 -> unimp`
     (NOT taken, as above), `bgeu s6 + 1, a2 -> 0x83824`, the ASan check of s6 + 1 (arm B 0x84184, as above) and
     `lbu`, the next-digit test (B 0x83818-0x83820, exn_next_digit_digit) -> B 0x83f98 (`li s5, -1`) -> CT;
     the fall-through B 0x83824-0x8384c: s7 = s2 + 32, `sd s2 + 64, 136(s1)`, a3 = -11, a4 = 58, a5 = exn_MASK,
     a0 = s6, then CL at j = EXN_i1 + exn_sg c.
   THE RUNS (h-verbs-1's listing engine YC80x / YC1fPx, paj_run_to_x over YCbqG's ajournal_x, at the listing of
   record B_prog_listing / PL_prog_B / PI_prog_B, every pc `exv_pc off` = B_prog_base + EXA_PC off): run 1, CN ..
   CN + 0xc (the two shadow stores, token band empty: the frame's shadow bytes lie in the shadow band); run 2 from
   CN + 0xc with the shadow band as token band, the s1 slot at +136 and the text bytes x[j0], x[j0 + 1] (atoms 32,
   33) as regions. The case split is up front on c = '-' and on the bytes after j0 = i1 + sg: five cases.
   Section hypotheses (task): HYP (EXV_HYP), HT (EXN_T), HL (EXN_Bl), MK (EXN_keepM), KS (EXN_keep_spill); no other.
   MK's memnorm keep (`YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs M`) comes from exa_mn_frame, the
   kit's YAkMemnorm.memnorm_frame_off_segs at [kLowMemEnd, TASK_SIZE): each run writes only there (the frame's two
   shadow bytes, the s1 slot +136), where no image segment lies (B_prog_segs_low), and keeps every other overlay byte
   (the run's frame_of on the whole overlay).
   Port of the proof shape of image A's walk of the same arm (reference only, never Required or cited).
   Numerals: no ADDRESS. DERIVED: 0x278, 0x284, 0x324, 0xa70 (cut offsets into ex_value, B address minus
   B_prog_sigma AS_ex_value, from the listing); 0x7fff7f800000 / 0x7fffff800000 (the bounds of alloc_ceiling, YCbq.v
   asan_consts); 0x7fff8000 (SHADOW_OFF); 0x10007fff8000 (kHighMemBeg); 2 ^ 44 (the shadow band); 16384 (STK_RT_STRTOD
   = 4 * ESTACK); 304 (pi_frame F_ex_value at prh_img_B). LENGTH: 136, 144, 160 (s1 slots of B's code and
   ExvB_NumCut's write zone), 4, 8, 9, 16 (the frame's shadow bytes, fs_frame_bytes 1 / 8), 32, 64, 128 (frame slots
   `end` / `num`, fs_frame_bytes 1), 40 (struct ex), 288, 319 (frame and its 32-alignment slack), 4096, 2 ^ 47,
   2 ^ 47 - 64, 2 ^ 64 (address bounds), 2 ^ 5 (s1's alignment), 0, 1, 2 (byte counts). WORD: 45 '-', 48 '0',
   -58, -10, -11, -1, 58, 18446744073709551605 / ..606 / ..615 (= -11, -10, -1 mod 2 ^ 64, as the engine prints
   the listing's immediates), 255 / 256 (a byte); register and atom numbers 2 .. 33. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure ExvB_NumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Open_kt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ======== pure: the arm's refusals before the scan (ExvB_NumPure's exn_N_unfold) ======== *)

Lemma exa_skipn_nth : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
induction x as [|y x IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.

(* the arm's reading at the five refusing shapes (exn_N_unfold, one step each) *)
Lemma exa_N_45nil : exn_N [45] = None.
Proof. vm_compute. reflexivity. Qed.
Lemma exa_N_45nd : forall b y, PjGrammar.digit b = false -> exn_N (45 :: b :: y) = None.
Proof.
intros b y Hd. rewrite exn_N_unfold. cbv beta iota zeta.
change (skipn (if 45 =? 45 then 1%nat else 0%nat) (45 :: b :: y)) with (b :: y).
cbv beta iota. rewrite Hd. reflexivity.
Qed.
Lemma exa_N_45z : forall b1 y, PjGrammar.digit b1 = true -> exn_N (45 :: 48 :: b1 :: y) = None.
Proof.
intros b1 y Hd. rewrite exn_N_unfold. cbv beta iota zeta.
change (skipn (if 45 =? 45 then 1%nat else 0%nat) (45 :: 48 :: b1 :: y)) with (48 :: b1 :: y).
cbv beta iota. rewrite Hd. reflexivity.
Qed.
Lemma exa_N_nd0 : forall b y, (b =? 45) = false -> PjGrammar.digit b = false -> exn_N (b :: y) = None.
Proof.
intros b y H45 Hd. rewrite exn_N_unfold. cbv beta iota zeta. rewrite H45.
change (skipn 0 (b :: y)) with (b :: y).
cbv beta iota. rewrite Hd. reflexivity.
Qed.
Lemma exa_N_z0 : forall b1 y, PjGrammar.digit b1 = true -> exn_N (48 :: b1 :: y) = None.
Proof.
intros b1 y Hd. rewrite exn_N_unfold. cbv beta iota zeta.
change (skipn (if 48 =? 45 then 1%nat else 0%nat) (48 :: b1 :: y)) with (48 :: b1 :: y).
cbv beta iota. rewrite Hd. reflexivity.
Qed.

(* no byte after the sign, a non-digit, a leading zero before a digit *)
Lemma exa_N_refuse : forall x i1 c, (i1 < length x)%nat -> nth i1 x 0 = c ->
  ((length x <= i1 + exn_sg c)%nat \/
   ((i1 + exn_sg c < length x)%nat /\ PjGrammar.digit (nth (i1 + exn_sg c) x 0) = false) \/
   ((S (i1 + exn_sg c) < length x)%nat /\ nth (i1 + exn_sg c) x 0 = 48 /\
    PjGrammar.digit (nth (S (i1 + exn_sg c)) x 0) = true)) ->
  exn_N (skipn i1 x) = None.
Proof.
intros x i1 c Hi Hc Hr. rewrite (exa_skipn_nth x i1 Hi), Hc.
destruct (Z.eqb_spec c 45) as [E45 | N45].
- assert (Hsg : exn_sg c = 1%nat) by (unfold exn_sg; rewrite (proj2 (Z.eqb_eq c 45) E45); reflexivity).
  rewrite Hsg in Hr. rewrite E45. replace (i1 + 1)%nat with (S i1) in Hr by lia.
  destruct Hr as [Hl | [[Hl Hd0] | (Hl & H0 & Hd1)]].
  + rewrite (skipn_all2 x) by lia. exact exa_N_45nil.
  + rewrite (exa_skipn_nth x (S i1) Hl). exact (exa_N_45nd _ _ Hd0).
  + rewrite (exa_skipn_nth x (S i1) ltac:(lia)), (exa_skipn_nth x (S (S i1)) Hl), H0.
    exact (exa_N_45z _ _ Hd1).
- assert (Hsg : exn_sg c = 0%nat) by (unfold exn_sg; rewrite (proj2 (Z.eqb_neq c 45) N45); reflexivity).
  rewrite Hsg, Nat.add_0_r in Hr. rewrite Hc in Hr.
  destruct Hr as [Hl | [[Hl Hd0] | (Hl & H0 & Hd1)]]; [lia | |].
  + exact (exa_N_nd0 c _ (proj2 (Z.eqb_neq c 45) N45) Hd0).
  + rewrite H0, (exa_skipn_nth x (S i1) Hl). exact (exa_N_z0 _ _ Hd1).
Qed.

(* ======== arithmetic: the listing's byte tests as the engine states them ======== *)

(* B 0x837e0-0x837e8 `addi a3, a0, -58; li a4, -10; bltu a3, a4`: taken iff the byte is not a digit *)
Lemma exa_digit_lt : forall b, 0 <= b < 256 ->
  (zcanon (b + -58) <? zcanon 18446744073709551606) = negb (PjGrammar.digit b).
Proof.
intros b Hb. rewrite <- (exn_first_digit_digit b Hb).
unfold exn_first_digit, exn_ult, exn_M64, zcanon, M64. rewrite negb_involutive.
replace (18446744073709551606 mod 2 ^ 64) with (-10 mod 2 ^ 64) by reflexivity. reflexivity.
Qed.

(* B 0x83818-0x83820 `addi a0, a0, -58; li a3, -11; bltu a3, a0`: taken iff the byte is a digit *)
Lemma exa_digit_gt : forall b, 0 <= b < 256 ->
  (zcanon 18446744073709551605 <? zcanon (b + -58)) = PjGrammar.digit b.
Proof.
intros b Hb. rewrite <- (exn_next_digit_digit b Hb).
unfold exn_next_digit, exn_ult, exn_M64, zcanon, M64.
replace (18446744073709551605 mod 2 ^ 64) with (-11 mod 2 ^ 64) by reflexivity. reflexivity.
Qed.

Lemma exa_eq48 : forall b, 0 <= b < 256 -> (zcanon (b + 0) =? zcanon 48) = (b =? 48).
Proof. intros b Hb. rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). reflexivity. Qed.

Lemma exa_w64_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma exa_w64_m11 : Z_to_bv 64 18446744073709551605 = w64 (-11).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma exa_w64_mask : Z_to_bv 64 288230376218820621 = w64 exn_MASK.
Proof. rewrite exn_MASK_value. reflexivity. Qed.

Lemma exa_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma exa_nth_byte : forall segs m p (x : list Z) j, YI00.garr8 segs m p x -> 0 <= nth j x 0 < 256.
Proof.
intros segs m p x j H. destruct (Nat.lt_ge_cases j (length x)) as [Hj|Hj].
- exact (proj2 (H j Hj)).
- rewrite nth_overflow by exact Hj. lia.
Qed.

(* the in_wrange of a concrete region list, one region at a time *)
Lemma exa_inw_cons : forall E r rs z, in_wrange E (r :: rs) z ->
  (base_val E (r_base r) + r_wlo r <= z < base_val E (r_base r) + r_whi r) \/ in_wrange E rs z.
Proof. intros E r rs z (r' & [<-|Hin] & Hr); [left; exact Hr | right; exists r'; auto]. Qed.
Lemma exa_inw_nil : forall E z, ~ in_wrange E [] z.
Proof. intros E z (r & Hin & _). destruct Hin. Qed.

Lemma exa_agree_ewset : forall k E E' n v, (k <= n)%nat -> YP06.env_agree k E E' -> YP06.env_agree k E (ewset E' n v).
Proof.
intros k E E' n v Hk [H1 H2]. split.
- intros i Hi. cbn [ew ewset]. destruct (Nat.eqb_spec i n); [lia|]. apply H1. exact Hi.
- cbn [ed ewset]. exact H2.
Qed.

(* the memory frame of a run: outside its write windows the view is unchanged *)
Lemma exa_frame_view : forall segs E rs H mem mem' (Z0 : Z -> Prop),
  frame_of E rs (mrestrict H mem) (mrestrict H mem') ->
  (forall z, 0 <= z < 2 ^ 64 -> in_wrange E rs z -> Z0 z) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ Z0 z -> aview segs H mem' z = aview segs H mem z.
Proof.
intros segs E rs H mem mem' Z0 HF Hw z Hz HZ. unfold aview, YP09.mbyte.
rewrite (HF (Z_to_bv 64 z)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. exact (HZ (Hw z Hz Hin)).
Qed.

Lemma exa_zmaxl_strtod : forall l1 l2, STK_RT_STRTOD <= zmaxl (l1 ++ STK_RT_STRTOD :: l2).
Proof.
intros l1 l2. unfold zmaxl. induction l1 as [|y l1 IH]; cbn [app fold_right]; lia.
Qed.

(* ex_value's stack need covers its frame and strtod's: 304 = pi_frame F_ex_value at prh_img_B *)
Lemma exa_STK : forall n, 304 + 16384 <= STK_ex_value (PI := prh_img_B) n.
Proof.
intros n. unfold STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304.
pose proof (exa_zmaxl_strtod [STK_RT_ECALL; STK_RT_STR] [STK_ex_string; STK_ex_word; STK_ex_ws]) as H.
cbn [app] in H. unfold STK_RT_STRTOD, ESTACK in H |- *. nia.
Qed.

Lemma exa_i1_nonneg : forall E, 0 <= exv_i1 E.
Proof.
intros E. unfold exv_i1, exv_len, exv_X.
destruct (exn_skip_suffix (skipn (Z.to_nat (e_i0 E)) (e_x E))) as (m & Hm & Hs).
rewrite Hs, !length_skipn. rewrite length_skipn in Hm. lia.
Qed.

(* ======== the symbolic states ======== *)

Definition EXA_PC (off : Z) : Z := B_prog_sigma AS_ex_value - B_prog_base + off.
Definition exa_Bx : sv := SOff 25 0.
Definition exa_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* run 1 loads no shadow byte; its band is empty so the frame's shadow bytes may be stored *)
Definition exa_Bspan0 : Z * Z := (0, 0).
Definition EXA_CEIL : Z := 0x7fff7f800000.
(* the s1 slot +136 (B 0x8382c `sd a0, 136(s1)`) *)
Definition exa_R136 : YP09.region := YP09.mkRegion (Some 9%nat) 136 144 136 144 [].
(* the frame's shadow bytes +4 and +8 (B 0x837a8, 0x837ac) *)
Definition exa_R4 : YP09.region := YP09.mkRegion (Some 26%nat) 4 5 4 5 [].
Definition exa_R8 : YP09.region := YP09.mkRegion (Some 26%nat) 8 9 8 9 [].
(* the text bytes x[j0] (atom 32) and x[j0 + 1] (atom 33), read-only, at a1 = x0 + i1 plus sg; n of them *)
Definition exa_RT (sg n : Z) : YP09.region :=
  YP09.mkRegion (Some 11%nat) sg (sg + n) 0 0
    (firstn (Z.to_nat n) [YP09.mkChunk sg (CVal 1 (SOff 32 0)); YP09.mkChunk (sg + 1) (CVal 1 (SOff 33 0))]).
Definition exa_atoms : list (nat * afact) :=
  [(9%nat, mkAF EXA_CEIL (2 ^ 47) 5); (11%nat, mkAF 4096 (2 ^ 47 - 64) 0); (12%nat, mkAF 4096 (2 ^ 47 - 64) 0);
   (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (26%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
   (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)].
(* the case conditions: c = '-' or not (B 0x837b4), x0 + i1 + o below the text's end or not *)
Definition exa_cEQ : acond := mkAC BC_EQ (SOff 27 0) (SLit 45).
Definition exa_cNE : acond := mkAC BC_NE (SOff 27 0) (SLit 45).
Definition exa_cLT (o : Z) : acond := mkAC BC_LTU (SOff 11 o) (SOff 12 0).
Definition exa_cGE (o : Z) : acond := mkAC BC_GEU (SOff 11 o) (SOff 12 0).
Definition exa_ss1 (sg n : Z) (cs : list acond) : sstate :=
  mkSS (EXA_PC 0x278) sr_atoms [exa_R136; exa_RT sg n; exa_R4; exa_R8] None (mkFacts exa_atoms cs []).
(* the registers the piece leaves as they were at the cut *)
Definition exa_kept : list Prelude.reg := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 18%bv; 19%bv; 24%bv; 25%bv; 26%bv; 27%bv].

(* the text byte x[j] as a one-byte chunk of atom n *)
Lemma exa_byte_chunk : forall segs E m base off n j (x : list Z) x0,
  YI00.garr8 segs m x0 x -> (j < length x)%nat -> base + off = x0 + Z.of_nat j ->
  bv_unsigned (ew E n) = nth j x 0 -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros segs E m base off n j x x0 Hg Hj Hb Hn i Hi. cbn [YP09.c_len YP09.c_val cv_len YP09.c_off] in *.
assert (i = 0) by lia. subst i. exists (Z_to_bv 8 (nth j x 0)). split.
- cbn [cbyte]. f_equal. unfold byte_of_word. cbn [sv_denot]. rewrite Hn, Z.add_0_r.
  pose proof (proj2 (Hg j Hj)) as Hr. rewrite unsigned_lit_small by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite Z.add_0_r, Hb. exact (YI00.garr8_mbyte _ _ _ _ _ Hg Hj).
Qed.

(* an 8-byte chunk of a run's state, read back *)
Lemma exa_chunk8 {fx : YK11.FPState} : forall segs val E ss ms r off e,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 8 e)) (r_chunks r) ->
  forall v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs (ms_mem ms) (base_val E (r_base r) + off) 8 v.
Proof.
intros segs val E ss ms r off e HS Hr Hc v He Hv.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok segs E _ _ off 8 e v (proj1 (Forall_forall _ _) Hcs _ Hc) He ltac:(exact Hv) ltac:(lia)).
Qed.

(* a one-byte zero chunk of a run's state (the frame's shadow stores) *)
Lemma exa_chunk1z {fx : YK11.FPState} : forall segs val E ss ms r off,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 1 (SLit 0))) (r_chunks r) ->
  YP09.mbyte segs (ms_mem ms) (base_val E (r_base r) + off) = Some (Z_to_bv 8 0).
Proof.
intros segs val E ss ms r off HS Hr Hc.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
destruct (proj1 (Forall_forall _ _) Hcs _ Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [cbyte YP09.c_val] in Hb1.
injection Hb1 as <-. reflexivity.
Qed.

(* dropping regions of a run's state *)
Lemma exa_submem {fx : YK11.FPState} : forall segs val E ss ms rs,
  st_ok_pi segs val E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs val E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs val E ss ms rs HS Hsub Hwf. unfold st_ok_pi, abs_ss in *.
exact (st_ok_submem segs E (setpc ss (val A_TEXT + ss_pc ss)) ms rs HS Hsub Hwf).
Qed.

Lemma exa_zadd : forall p o, 0 <= p -> p + o < 2 ^ 64 -> 0 <= o -> zcanon (p + o) = p + o.
Proof. intros p o H1 H2 H3. apply zcanon_id. unfold M64. lia. Qed.

(* the overlay normal form (YAkMemnorm.memnorm, the body of YStrtodRowX.aj_memnorm) across a run whose writes lie in
   [kLowMemEnd, TASK_SIZE): no image segment lies there (B_prog_segs_low); the kit's memnorm_frame_off_segs *)
Lemma exa_mn_frame : forall (m m' : word -> option byte) (Zw : Z -> Prop),
  YAkMemnorm.memnorm rsegs m -> (forall x : word, ~ Zw (bv_unsigned x) -> m' x = m x) ->
  (forall z, Zw z -> kLowMemEnd <= z < TASK_SIZE) -> YAkMemnorm.memnorm rsegs m'.
Proof.
intros m m' Zw Hm Hout Hw.
apply (YAkMemnorm.memnorm_frame_off_segs rsegs m m' kLowMemEnd TASK_SIZE Hm).
- intros x Hx. apply Hout. intros Hz. pose proof (Hw _ Hz). lia.
- lia.
- intros x Hx. apply YCbq.find_segment_none. intros Himg. pose proof (B_prog_segs_low _ Himg). lia.
Qed.

Section core.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.
Let LAWS := eh_laws B ARx SK HYP.
Let RUNTO := @paj_run_to_x fx rc SK B_prog_listing PL_prog_B PI_prog_B B PST ARx _ LAWS.
Let BR := paj_branch (fx := fx) (L := B_prog_listing) (PI := PI_prog_B).

Lemma exa_cfg : forall off regs mem md,
  mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + EXA_PC off)) mem (YK11.seg_rom rsegs)) md =
  cfg_at (fx := fx) rsegs (exv_pc off) regs mem md.
Proof.
intros off regs mem md. unfold cfg_at, exv_pc, EXA_PC, w64.
assert (HB : BASE = B_prog_base) by (vm_compute; reflexivity). rewrite HB.
replace (B_prog_base + (B_prog_sigma AS_ex_value - B_prog_base + off)) with (B_prog_sigma AS_ex_value + off) by lia.
reflexivity.
Qed.

Section ctx.
Variables (W : world rsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (k : Z) (c : Z).
Hypothesis HPRE : EXV_PRE B ARx E.
Hypothesis HBASE : EXN_base B ARx SK E pos fx lyc Sc Hpc W regs memc mdc k.
Hypothesis HDISP : EXN_disp E c.
Hypothesis HCUR : EXN_cur E W memc (exv_i1 E) (e_dl E).
Hypothesis H11 : YK11.getr regs 11 = w64 (e_x0 E + exv_i1 E).
Hypothesis H12 : YK11.getr regs 12 = w64 (e_x0 E + exv_len E).
Hypothesis H27 : YK11.getr regs 27 = w64 c.
Local Notation x := (e_x E).
Local Notation x0 := (e_x0 E).
Local Notation len := (exv_len E).
Local Notation i1 := (EXN_i1 E).
Local Notation S1 := (exv_s1 E).
Local Notation fr := (frame_addr lyc 1 pos).
Local Notation AJ M md' := (ajournal_x (SK := SK) rsegs B PST ARx (exv_STK E + e_d E) (exv_sp E + e_d E)
  (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc W M md' k).

(* the facts of EXV_PRE the piece reads *)
Lemma exa_pre : 0 <= e_d E /\ exv_sp E <= e_q E /\ 0 <= e_i0 E <= len /\ 0 <= e_dep E <= 32 /\
  (e_dl E = 0 \/ e_dl E = 1).
Proof.
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & Hq1 & _ & Hwin & _ & _ & _ & Hi0 & Hdep & _ & Hdl & _).
destruct Hwin as (Hd0 & _). unfold exv_sp. tauto.
Qed.

(* the arithmetic and presence facts of the cut *)
Lemma exa_facts :
  exv_sp E - exv_STK E <= S1 + 136 /\ S1 + 160 <= exv_sp E /\ EXA_CEIL <= S1 /\ S1 + 160 <= 2 ^ 47 /\
  S1 mod 32 = 0 /\ 4096 <= x0 /\ x0 + len <= alloc_ceiling /\ alloc_ceiling <= S1 /\
  alloc_ceiling <= 0x7fffff800000 /\ 4096 <= fr /\ fr + 128 <= alloc_ceiling /\
  (forall z, exv_sp E - exv_STK E <= z < exv_sp E + e_d E -> apresent (w_H W) memc z) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W) memc (shadow_addr fr + i)) /\
  In (1, pos) (frames Sc) /\ 0 <= exv_i1 E < len /\ amem_range x0 len /\ exv_sp E + e_d E <= 2 ^ 47.
Proof.
destruct HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Jastk & _ & _).
pose proof Jastk as (_ & _ & Jceil & Jslo & Jshi & J47 & _).
assert (HSTK : 304 + 16384 <= exv_STK E) by exact (exa_STK (e_n E)).
pose proof (ExvB_Open_kt.exv_s1_le E) as (Hs1 & Hs1m).
pose proof exa_pre as (Hd0 & _).
pose proof asan_consts as (C1 & _).
destruct HSRC as (_ & Hx0 & Hxe & Ham & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc W memc mdc 1 pos HAR Hin) as (HF4096 & HFceil & _).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc W memc mdc 1 pos HAR Hin) as (_ & _ & _ & Hshp).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity. rewrite Hfb in HFceil, Hshp.
change (128 / 8) with 16 in Hshp.
pose proof (exa_i1_nonneg E) as Hi1. destruct HDISP as (Hlt & _).
unfold exv_len in *. unfold EXA_CEIL.
repeat match goal with |- _ /\ _ => split end;
  first [ lia | exact Hin | exact Hs1m | exact Ham
        | (intros z Hz; apply Hpres; lia) | (intros i Hi; exact (proj1 (Hshp i Hi))) ].
Qed.

Lemma exa_shf : SHADOW_OFF <= shadow_addr fr /\ shadow_addr fr + 16 <= SHADOW_OFF + 2 ^ 44.
Proof.
pose proof exa_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _).
unfold shadow_addr. split; [pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia|].
pose proof (Z.div_le_upper_bound fr 8 (2 ^ 44 - 16) ltac:(lia) ltac:(lia)). lia.
Qed.

(* the bytes the piece writes: the frame's two shadow bytes and the s1 slot +136 *)
Definition exa_wz (z : Z) : Prop :=
  z = shadow_addr fr + 4 \/ z = shadow_addr fr + 8 \/ S1 + 136 <= z < S1 + 144.

Lemma exa_wz_sub : forall z, exa_wz z -> EXN_wz B E pos lyc z.
Proof.
intros z [H | [H | H]]; unfold EXN_wz.
- right; right; right; left. exact H.
- right; right; right; right; left. exact H.
- left. unfold STK_RT_STRTOD, ESTACK. lia.
Qed.

(* the state between the runs: the journal, the bytes outside exa_wz kept, presence grown, the overlay facts *)
Definition exa_mid (M : word -> option byte) (md' : Model) : Prop :=
  AJ M md' /\
  (forall z, 0 <= z < 2 ^ 64 -> ~ exa_wz z -> aview rsegs (w_H W) M z = aview rsegs (w_H W) memc z) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) M a) /\
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs M).
Definition exa_mid2 (M : word -> option byte) (md' : Model) : Prop :=
  exa_mid M md' /\ EXN_fsh pos lyc W M.

Lemma exa_mid0 : exa_mid memc mdc.
Proof.
destruct HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB. destruct HEXB as (HJ & _).
split; [exact HJ|]. split; [intros; reflexivity | split; [intros a Ha; exact Ha | intros Hm; exact Hm]].
Qed.

Lemma exa_mid_step : forall M md M' md' (Wr : Z -> Prop),
  exa_mid M md -> AJ M' md' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ Wr z -> aview rsegs (w_H W) M' z = aview rsegs (w_H W) M z) ->
  (forall z, Wr z -> exa_wz z) ->
  mem_grows (mrestrict (w_H W) M) (mrestrict (w_H W) M') ->
  (YAkMemnorm.memnorm rsegs M -> YAkMemnorm.memnorm rsegs M') ->
  exa_mid M' md'.
Proof.
intros M md M' md' Wr (_ & HV & HP & HN) HJ HV' HW HG HN'. split; [exact HJ|]. split; [|split].
- intros z Hz Hn. rewrite HV' by (try exact Hz; intros Hw; exact (Hn (HW z Hw))). exact (HV z Hz Hn).
- intros a Ha. apply (apresent_grows _ _ _ a HG). exact (HP a Ha).
- intros Hm. exact (HN' (HN Hm)).
Qed.

Lemma exa_fsh_keep : forall M M',
  (forall z, 0 <= z < 2 ^ 64 -> ~ (S1 + 136 <= z < S1 + 144) -> aview rsegs (w_H W) M' z = aview rsegs (w_H W) M z) ->
  EXN_fsh pos lyc W M -> EXN_fsh pos lyc W M'.
Proof.
intros M M' HV [H4 H8]. pose proof exa_shf as Hs. pose proof exa_facts as (_ & _ & F3 & _).
unfold EXA_CEIL in F3. unfold EXN_fsh. rewrite !HV by (unfold SHADOW_OFF in *; lia). split; assumption.
Qed.

Lemma exa_mid2_step : forall M md M' md',
  exa_mid2 M md -> AJ M' md' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (S1 + 136 <= z < S1 + 144) -> aview rsegs (w_H W) M' z = aview rsegs (w_H W) M z) ->
  mem_grows (mrestrict (w_H W) M) (mrestrict (w_H W) M') ->
  (YAkMemnorm.memnorm rsegs M -> YAkMemnorm.memnorm rsegs M') ->
  exa_mid2 M' md'.
Proof.
intros M md M' md' (HM & HF) HJ HV HG HN'. split.
- apply (exa_mid_step M md M' md' (fun z => S1 + 136 <= z < S1 + 144) HM HJ HV); [| exact HG | exact HN'].
  intros z Hz. right; right. exact Hz.
- exact (exa_fsh_keep M M' HV HF).
Qed.

Lemma exa_fsh_of : forall M,
  YP09.mbyte rsegs (mrestrict (w_H W) M) (shadow_addr fr + 4) = Some (Z_to_bv 8 0) ->
  YP09.mbyte rsegs (mrestrict (w_H W) M) (shadow_addr fr + 8) = Some (Z_to_bv 8 0) -> EXN_fsh pos lyc W M.
Proof. intros M H4 H8. unfold EXN_fsh, aview. rewrite H4, H8. split; reflexivity. Qed.

(* the text's shadow at a state between the runs: unchanged, or one of the two opened bytes, which read 0 *)
Lemma exa_ra : forall M md, exa_mid2 M md -> range_addressable (aview rsegs (w_H W) M) SHADOW_OFF x0 len.
Proof.
intros M md ((_ & HV & _) & H4 & H8) y Hy.
destruct HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
destruct HSRC as (_ & _ & _ & _ & HRA & _). unfold exv_len in Hy.
destruct (HRA y Hy) as (s & Hs & Hok).
pose proof exa_facts as (_ & _ & F3 & _ & _ & F6 & F7 & F8 & F9 & _). unfold EXA_CEIL in F3. unfold exv_len in F7.
pose proof asan_consts as (C1 & _).
assert (Hsy : 0 <= shadow_of_addr SHADOW_OFF y < alloc_ceiling).
{ unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
destruct (Z.eq_dec (shadow_of_addr SHADOW_OFF y) (shadow_addr fr + 4)) as [E4|N4];
  [exists 0; split; [rewrite E4; exact H4 | left; reflexivity]|].
destruct (Z.eq_dec (shadow_of_addr SHADOW_OFF y) (shadow_addr fr + 8)) as [E8|N8];
  [exists 0; split; [rewrite E8; exact H8 | left; reflexivity]|].
exists s. split; [|exact Hok]. rewrite HV; [exact Hs | lia |].
intros [Hw | [Hw | Hw]]; [exact (N4 Hw) | exact (N8 Hw) | lia].
Qed.

(* the ASan obligation of a text byte at a1 + o (B 0x837d4, 0x8380c) *)
Lemma exa_obl : forall E' M md o, exa_mid2 M md ->
  bv_unsigned (ew E' 25) = SHADOW_OFF -> bv_unsigned (ew E' 11) = x0 + exv_i1 E -> 0 <= o ->
  exv_i1 E + o + 1 <= len ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) M)) (U E' (SOff 25 0)) (U E' (SOff 11 o)) 1.
Proof.
intros E' M md o HM H25 H11' Ho Hl.
pose proof exa_facts as (_ & _ & _ & _ & _ & F6 & F7 & _ & F9 & _).
pose proof asan_consts as (C1 & _). pose proof (exa_i1_nonneg E) as Hi1.
apply (obl_of_range rsegs (w_H W) M E' (SOff 25 0) (U E' (SOff 11 o)) 1 x0 len (exa_ra M md HM)).
- rewrite U_SOff, H25, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
- rewrite U_SOff, H11', zcanon_id by (unfold M64; lia). lia.
- rewrite U_SOff, H11', zcanon_id by (unfold M64; lia). lia.
Qed.

(* the cursor cells [q, q + 40) lie above the entry sp, outside exa_wz *)
Lemma exa_cur_keep : forall M md p dl, exa_mid M md -> EXN_cur E W memc p dl -> EXN_cur E W M p dl.
Proof.
intros M md p dl (_ & HV & _) Hc. pose proof exa_pre as (_ & Hq & _).
pose proof exa_facts as (_ & F2 & F3 & F4 & _). pose proof exa_shf as Hs. unfold EXA_CEIL in F3.
pose proof asan_consts as (C1 & _).
assert (Hq47 : e_q E + 40 <= 2 ^ 64).
{ pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hq2 & Hwin & _).
  pose proof exa_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F17).
  unfold exv_sp in F17. lia. }
assert (VQ : forall a (w : nat) v, val_mem rsegs (mrestrict (w_H W) memc) a w v -> e_q E <= a ->
  a + Z.of_nat w <= e_q E + 40 -> val_mem rsegs (mrestrict (w_H W) M) a w v).
{ intros a w v Hv H1 H2 kk Hk.
  rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc M (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HV; [lia|]. unfold exa_wz, SHADOW_OFF in *. lia. }
unfold EXN_cur, prhex_cur in Hc |- *. destruct Hc as (V1 & V2 & V3 & V4 & V5).
refine (conj (VQ _ _ _ V1 _ _) (conj (VQ _ _ _ V2 _ _) (conj (VQ _ _ _ V3 _ _) (conj (VQ _ _ _ V4 _ _)
  (VQ _ _ _ V5 _ _))))); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

(* EXN_base at a state between the runs: EXB by MK, the two spills by KS *)
Lemma exa_base : forall regs' M md', exa_mid M md' ->
  (forall r, In r exa_kept -> YK11.getr regs' r = YK11.getr regs r) ->
  EXN_base B ARx SK E pos fx lyc Sc Hpc W regs' M md' k.
Proof.
intros regs' M md' HM Hkp. pose proof HM as (HJ & HV & HP & HMN).
destruct HBASE as (HEXB & HS144 & HS152).
pose proof exa_facts as (_ & F2 & F3 & F4 & _). pose proof exa_shf as Hs. unfold EXA_CEIL in F3.
assert (HK : forall o v, 144 <= o -> o + 8 <= 160 -> exv_spill E W memc o v -> exv_spill E W M o v).
{ intros o v Ho1 Ho2 Hv. apply (KS W memc M o v Hv). intros z Hz. apply HV; [lia|].
  unfold exa_wz, SHADOW_OFF in *. lia. }
split; [|split; [exact (HK 144 _ ltac:(lia) ltac:(lia) HS144) | exact (HK 152 _ ltac:(lia) ltac:(lia) HS152)]].
apply (MK fx lyc Sc Hpc W regs memc mdc k regs' M md' k HPRE HEXB HJ).
- intros z Hz Hn. apply HV; [exact Hz|]. intros Hw. exact (Hn (exa_wz_sub z Hw)).
- exact HP.
- exact HMN.
- unfold EXN_regs_kept.
  repeat split; apply Hkp; cbn [exa_kept In]; tauto.
Qed.

(* the leaf at CT: r = -1, the arm refuses *)
Lemma exa_CT : forall regs' M md', exa_mid M md' ->
  (forall r, In r exa_kept -> YK11.getr regs' r = YK11.getr regs r) -> YK11.getr regs' 21 = w64 (-1) ->
  exn_N (skipn i1 x) = None ->
  EXN_CT_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k (-1).
Proof.
intros regs' M md' HM Hkp H21 HN. unfold EXN_CT_pre.
split; [exact (exa_base regs' M md' HM Hkp)|]. split; [exact H21|].
pose proof exa_pre as (_ & _ & Hi0 & Hdep & Hdl). pose proof (exa_i1_nonneg E) as Hi1.
pose proof HDISP as (Hlt & _).
exists (exv_i1 E), (e_dep E), (e_dl E).
split; [exact (exa_cur_keep M md' (exv_i1 E) (e_dl E) HM HCUR)|]. split; [exact Hdl|].
rewrite (exn_V_eq E c Hi0 HDISP), HN. split; [reflexivity | lia].
Qed.

(* the leaf at CL: the scan's head at j0 = i1 + sg, the lead byte checked *)
Lemma exa_CL : forall regs' M md', exa_mid2 M md' ->
  (forall r, In r exa_kept -> YK11.getr regs' r = YK11.getr regs r) -> YK11.getr regs' 21 = w64 (-1) ->
  YK11.getr regs' 23 = w64 (fr + 32) -> exv_spill E W M 136 (fr + 64) ->
  YK11.getr regs' 22 = w64 (x0 + Z.of_nat (i1 + exn_sg c)) ->
  YK11.getr regs' 10 = w64 (x0 + Z.of_nat (i1 + exn_sg c)) ->
  YK11.getr regs' 13 = w64 (-11) -> YK11.getr regs' 14 = w64 58 -> YK11.getr regs' 15 = w64 exn_MASK ->
  (i1 + exn_sg c < length x)%nat -> PjGrammar.digit (nth (i1 + exn_sg c) x 0) = true ->
  ~ (nth (i1 + exn_sg c) x 0 = 48 /\ (S (i1 + exn_sg c) < length x)%nat /\
     PjGrammar.digit (nth (S (i1 + exn_sg c)) x 0) = true) ->
  EXN_CL_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k c (i1 + exn_sg c).
Proof.
intros regs' M md' (HM & HF) Hkp H21 H23 Hv R22 R10 R13 R14 R15 Hl Hd Hz.
pose proof (Hkp 11%bv ltac:(cbn; tauto)) as K11. pose proof (Hkp 12%bv ltac:(cbn; tauto)) as K12.
pose proof (Hkp 27%bv ltac:(cbn; tauto)) as K27.
unfold EXN_CL_pre.
split; [exact (exa_base regs' M md' HM Hkp)|]. split; [exact HDISP|].
split; [exact (exa_cur_keep M md' (exv_i1 E) (e_dl E) HM HCUR)|]. split; [exact HF|].
split; [unfold EXN_span; split; [exact Hl|]; split; [exact Hd|]; split; [exact Hz|];
        unfold exn_sub; rewrite Nat.sub_diag; constructor|].
split; [lia|].
rewrite K11, K12, K27.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Section env.
Variables (b0 b1 : Z) (E0 : env).
Hypothesis Hb0 : b0 = nth (i1 + exn_sg c)%nat x 0.
Hypothesis Hb1 : b1 = nth (S (i1 + exn_sg c)) x 0.
Hypothesis HB0 : 0 <= b0 < 256.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HEI : img_env VAL A_LIM E0.
Hypothesis HAG0 : YP06.env_agree 32 (Ereg regs []) E0.
Hypothesis HRE : regs_ok E0 sr_atoms regs.
Hypothesis U9 : bv_unsigned (ew E0 9) = S1.
Hypothesis U11 : bv_unsigned (ew E0 11) = x0 + exv_i1 E.
Hypothesis U12 : bv_unsigned (ew E0 12) = x0 + len.
Hypothesis U18 : bv_unsigned (ew E0 18) = fr.
Hypothesis U25 : bv_unsigned (ew E0 25) = SHADOW_OFF.
Hypothesis U26 : bv_unsigned (ew E0 26) = shadow_addr fr.
Hypothesis U27 : bv_unsigned (ew E0 27) = c.
Hypothesis U32 : bv_unsigned (ew E0 32) = b0.
Hypothesis U33 : bv_unsigned (ew E0 33) = b1.

Lemma exa_cLT_ok : forall o, 0 <= o <= 2 -> exv_i1 E + o < len -> acond_ok E0 (exa_cLT o).
Proof.
intros o Ho Hl. pose proof exa_facts as (_ & _ & _ & _ & _ & F6 & F7 & F8 & F9 & _).
pose proof asan_consts as (C1 & _). pose proof (exa_i1_nonneg E) as Hi1.
unfold acond_ok, exa_cLT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, !U_SOff, U11, U12.
rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia.
Qed.
Lemma exa_cGE_ok : forall o, 0 <= o <= 2 -> len <= exv_i1 E + o -> acond_ok E0 (exa_cGE o).
Proof.
intros o Ho Hl.
pose proof exa_facts as (_ & _ & _ & _ & _ & F6 & F7 & F8 & F9 & _ & _ & _ & _ & _ & F15 & _).
pose proof asan_consts as (C1 & _). pose proof (exa_i1_nonneg E) as Hi1.
unfold acond_ok, exa_cGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, U11, U12.
rewrite !zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma exa_c45 : 0 <= c < 256.
Proof.
destruct HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
destruct HSRC as (Hg & _). unfold bytes_at in Hg. destruct HDISP as (_ & Hc & _).
rewrite <- Hc. exact (exa_nth_byte _ _ _ _ _ Hg).
Qed.
Lemma exa_cEQ_ok : c = 45 -> acond_ok E0 exa_cEQ.
Proof.
intros Hc. unfold acond_ok, exa_cEQ. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_SOff, U_SLit, U27, Hc.
reflexivity.
Qed.
Lemma exa_cNE_ok : c <> 45 -> acond_ok E0 exa_cNE.
Proof.
intros Hc. pose proof exa_c45 as HC. unfold acond_ok, exa_cNE. cbn [ac_c ac_a ac_b].
rewrite branch_ne_U, U_SOff, U_SLit, U27, Z.add_0_r, !zcanon_id by (unfold M64; lia).
apply negb_true_iff, Z.eqb_neq. exact Hc.
Qed.

(* the text region x[j0 ..] at a1 + sg, at the cut's memory *)
Lemma exa_RT_ok : forall sg n, sg = Z.of_nat (exn_sg c) -> 0 <= n <= 2 -> exv_i1 E + sg + n <= len ->
  region_ok rsegs E0 (mrestrict (w_H W) memc) (exa_RT sg n).
Proof.
intros sg n Hsg Hn Hl.
destruct HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
destruct HSRC as (Hg & Hx0 & Hxe & _). unfold bytes_at in Hg.
pose proof asan_consts as (C1 & _). pose proof (exa_i1_nonneg E) as Hi1.
assert (Hsg01 : 0 <= sg <= 1) by (rewrite Hsg; unfold exn_sg; destruct (c =? 45); cbn; lia).
unfold exv_len in Hl, Hxe.
unfold region_ok, exa_RT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (Hj0 : x0 + exv_i1 E + sg = x0 + Z.of_nat (i1 + exn_sg c)).
{ unfold EXN_i1. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
destruct (Z.eq_dec n 0) as [->|Hn0]; [change (Z.to_nat 0) with 0%nat; cbn [firstn]; constructor|].
destruct (Z.eq_dec n 1) as [->|Hn1].
- change (Z.to_nat 1) with 1%nat. cbn [firstn]. constructor; [|constructor].
  apply (exa_byte_chunk rsegs E0 _ _ sg 32 (i1 + exn_sg c)%nat x x0 Hg); [| lia | rewrite U32; exact Hb0].
  apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add. unfold EXN_i1. rewrite Z2Nat.id by lia. lia.
- assert (n = 2) as -> by lia. change (Z.to_nat 2) with 2%nat. cbn [firstn]. constructor; [|constructor; [|constructor]].
  + apply (exa_byte_chunk rsegs E0 _ _ sg 32 (i1 + exn_sg c)%nat x x0 Hg); [| lia | rewrite U32; exact Hb0].
    apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add. unfold EXN_i1. rewrite Z2Nat.id by lia. lia.
  + apply (exa_byte_chunk rsegs E0 _ _ (sg + 1) 33 (S (i1 + exn_sg c)) x x0 Hg);
      [| rewrite Nat2Z.inj_succ; lia | rewrite U33; exact Hb1].
    apply Nat2Z.inj_lt. rewrite Nat2Z.inj_succ, Nat2Z.inj_add. unfold EXN_i1. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma exa_entry : forall sg n cs, (sg = 1 /\ c = 45 \/ sg = 0 /\ c <> 45) -> 0 <= n <= 2 ->
  exv_i1 E + sg + n <= len -> regions_wf [exa_R136; exa_RT sg n; exa_R4; exa_R8] = true -> conds_ok E0 cs ->
  st_ok_pi rsegs VAL E0 (exa_ss1 sg n cs)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + EXA_PC 0x278)) memc (YK11.seg_rom rsegs))).
Proof.
intros sg n cs Hsg Hn Hl Hwf Hcs.
pose proof exa_pre as (Hd0 & _).
pose proof exa_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
pose proof exa_shf as Hsf. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exa_i1_nonneg E) as Hi1. unfold EXA_CEIL in F3. unfold exv_len in *.
assert (Hsgv : sg = Z.of_nat (exn_sg c)).
{ unfold exn_sg. destruct Hsg as [[-> ->] | [-> Hc]]; [reflexivity|].
  destruct (Z.eqb_spec c 45); [contradiction | reflexivity]. }
assert (Hsg01 : 0 <= sg <= 1) by lia.
rewrite restrict_mkst_fx. unfold exa_ss1.
apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
- exact HRE.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  + unfold region_ok, exa_R136. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply apresent_writable. apply F12. lia.
  + exact (exa_RT_ok sg n Hsgv Hn ltac:(unfold exv_len; lia)).
  + unfold region_ok, exa_R4. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U26. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply apresent_writable. apply F13. lia.
  + unfold region_ok, exa_R8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U26. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply apresent_writable. apply F13. lia.
- unfold exa_R136, exa_RT, exa_R4, exa_R8.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.base_val YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite ?U9, ?U11, ?U26. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split].
  + unfold exa_atoms. cbn [YP0m.f_atoms YP0m.atoms_ok]. unfold YP0m.afact_ok. cbn [YP0m.af_lo YP0m.af_hi YP0m.af_al2].
    rewrite U9, U11, U12, U25, U26, U32, U33. unfold SHADOW_OFF, EXA_CEIL in *.
    repeat match goal with |- _ /\ _ => split end;
      first [ exact I | lia | (change (2 ^ 5) with 32; exact F5) | (change (2 ^ 0) with 1; apply Z.mod_1_r) ].
  + exact Hcs.
  + exact I.
Qed.

(* ---- the engine runs. The tactics find the walk's hypotheses by their types: the state (st_ok_pi), the journal
   (ajournal_x), the shadow facts (sh_ok), the state between the runs (exa_mid / exa_mid2), the run's frames
   (frame_of / mem_grows). ---- *)
Ltac exa_lia := unfold EXN_i1, exv_len in *; lia.
Ltac exa_regcbn H :=
  cbn [YP09.base_val YP09.r_base YP09.r_wlo YP09.r_whi] in H; cbn [ew ewset Nat.eqb] in H;
  rewrite ?U9, ?U26, ?U11 in H.
Ltac exa_awr1 :=
  unfold awr_byte;
  first [ exfalso; lia
        | left; lia
        | right; right; right; unfold in_frames; exists 1, pos; split; [left; reflexivity|];
          right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; lia ].
Ltac exa_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  unfold awr_ok; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz;
  repeat (apply exa_inw_cons in Hz; destruct Hz as [Hz|Hz]; [exa_regcbn Hz; exa_awr1|]);
  exfalso; exact (exa_inw_nil _ _ Hz).
Ltac exa_inw_split Hin tac :=
  lazymatch type of Hin with in_wrange ?E ?rs ?zz =>
    let rs' := eval vm_compute in rs in change (in_wrange E rs' zz) in Hin end;
  repeat (apply exa_inw_cons in Hin; destruct Hin as [Hin|Hin]; [exa_regcbn Hin; tac|]);
  exfalso; exact (exa_inw_nil _ _ Hin).
Ltac exa_wz1 :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Hin := fresh "Hin" in intros z Hz Hin;
  exa_inw_split Hin ltac:(cbv beta; unfold exa_wz; first [exfalso; lia | left; lia | right; left; lia | right; right; lia]).
Ltac exa_wz2 :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Hin := fresh "Hin" in intros z Hz Hin;
  exa_inw_split Hin ltac:(cbv beta; first [exfalso; lia | lia]).
(* a run's write windows lie in [kLowMemEnd, TASK_SIZE) (the s1 slot on the stack, the frame's shadow bytes) *)
Ltac exa_mnb :=
  first [ exfalso; lia
        | let HkL := fresh "HkL" in let HTS := fresh "HTS" in
          pose proof asan_consts as (_ & _ & _ & _ & HkL);
          assert (HTS : TASK_SIZE = 2 ^ 47) by reflexivity; unfold SHADOW_OFF in *; lia ].
(* the overlay facts across the run, from its frame on the whole overlay (the frame_of that is not restricted) *)
Ltac exa_mn_step HN :=
  match goal with HF : frame_of ?E ?rs ?m ?m' |- _ =>
    lazymatch m with
    | mrestrict _ _ => fail
    | _ => assert (HN : YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m')
             by (let H0 := fresh "H0" in intros H0; apply (exa_mn_frame m m' (in_wrange E rs) H0 HF);
                 let z := fresh "z" in let Hin := fresh "Hin" in intros z Hin;
                 exa_inw_split Hin ltac:(cbv beta; exa_mnb))
    end
  end.
(* after a run: the state between the runs at the new memory *)
Ltac exa_keep :=
  let HN := fresh "HN" in exa_mn_step HN;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
  lazymatch goal with
  | HM : exa_mid2 _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let HM' := fresh "HM" in
    pose proof (exa_mid2_step _ _ _ _ HM HJ
      (exa_frame_view rsegs _ _ _ _ _ (fun z => S1 + 136 <= z < S1 + 144) HFr ltac:(exa_wz2)) HG HN) as HM';
    clear HM HFr HG HN
  | HM : exa_mid _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let HM' := fresh "HM" in
    pose proof (exa_mid_step _ _ _ _ exa_wz HM HJ
      (exa_frame_view rsegs _ _ _ _ _ exa_wz HFr ltac:(exa_wz1)) (fun z H => H) HG HN) as HM';
    clear HM HFr HG HN
  end end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end.
Ltac exa_obl_tac :=
  unfold exa_Bx;
  lazymatch goal with HM : exa_mid2 _ _ |- _ =>
  eapply exa_obl; [ exact HM | cbn [ew ewset Nat.eqb]; exact U25 | cbn [ew ewset Nat.eqb]; exact U11 | exa_lia | exa_lia ] end.
Ltac exa_run Bsp stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok_x RUNTO HS HJ SHOK Bsp stop
  end;
  lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ => exa_awr
  | |- range_addressable _ _ _ _ => exa_obl_tac
  | |- SRr _ _ _ _ => exa_keep
  end.
(* the frame's shadow bytes after run 1, from its two one-byte zero chunks *)
Ltac exa_fsh_init :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict (w_H W) ?ms), HM : exa_mid _ _ |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with [?r1; ?rt; ?r4; ?r8] =>
      let H4 := fresh "Hz4" in let H8 := fresh "Hz8" in
      pose proof (exa_chunk1z rsegs VAL E ss (restrict (w_H W) ms) r4 4 HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as H4;
      pose proof (exa_chunk1z rsegs VAL E ss (restrict (w_H W) ms) r8 8 HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as H8;
      cbn [YP09.base_val YP09.r_base ms_mem restrict] in H4, H8; cbn [ew ewset Nat.eqb] in H4, H8;
      rewrite U26 in H4, H8;
      let HM2 := fresh "HM" in pose proof ((conj HM (exa_fsh_of _ H4 H8)) : exa_mid2 _ _) as HM2; clear H4 H8 HM
    end end.
(* run 2 drops the frame's shadow bytes (they lie in the token band) *)
Ltac exa_drop :=
  lazymatch goal with HS : st_ok_pi ?sgs ?v ?E ?ss ?ms |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with ?r1 :: ?rt :: _ =>
      let HS' := fresh "HS" in
      pose proof (exa_submem sgs v E ss ms [r1; rt] HS
        (submem_keep _ _ _ _ (subregion_refl _) (submem_keep _ _ _ _ (subregion_refl _) (submem_nil _)))
        ltac:(vm_compute; reflexivity)) as HS';
      clear HS end end.
(* a branch: the two cases, the engine's condition as a byte fact *)
Ltac exa_hc :=
  match goal with H : branch_taken _ _ _ = _ |- _ =>
    first [rewrite branch_ltu_U in H | rewrite branch_ne_U in H];
    rewrite ?U_SOff, ?U_SLit in H; cbn [ew ewset Nat.eqb] in H; rewrite ?U32, ?U33 in H;
    first [ rewrite (exa_digit_lt _ HB0) in H | rewrite (exa_digit_gt _ HB1) in H | rewrite (exa_eq48 _ HB0) in H ];
    repeat lazymatch type of H with
    | negb _ = true => apply negb_true_iff in H
    | negb _ = false => apply negb_false_iff in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end
  end.
Ltac exa_branch :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUNTO BR HS SHOK exa_Bspan end; exa_hc.
(* the leaves: the machine registers and memory at CT / CL *)
Ltac exa_reg r R :=
  lazymatch goal with HS : st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (st_ok_pi_restrict_reg (L := B_prog_listing) (PI := PI_prog_B) H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [sv_denot ew ewset Nat.eqb] in R
  end.
Ltac exa_kept_tac :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms) |- _ =>
    let Hk := fresh "Hkp" in
    pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) E ss (restrict (w_H W) ms) regs []
       exa_kept HS ltac:(repeat (apply exa_agree_ewset; [lia|]); exact HAG0) ltac:(vm_compute; reflexivity)) as Hk;
    cbn [ms_regs restrict] in Hk; exact Hk end.
Ltac exa_v136 :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss ?msr |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with context [YP09.mkRegion (Some 9%nat) ?lo ?hi ?wl ?wh ?cs] =>
      let Hv := fresh "Hv" in
      pose proof (exa_chunk8 rsegs VAL E ss msr (YP09.mkRegion (Some 9%nat) lo hi wl wh cs) 136 (SOff 18 64) HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as Hv;
      cbn [YP09.base_val YP09.r_base ms_mem restrict ew ewset Nat.eqb] in Hv; rewrite U9 in Hv;
      unfold exv_spill; apply Hv; [cbn [sv_denot ew ewset Nat.eqb]; rewrite U18; reflexivity | lia]
    end end.
Ltac exa_r21 := let R := fresh "R" in exa_reg (21%bv : bv 5) R; rewrite R; exact exa_w64_m1.
Ltac exa_mid1 := lazymatch goal with HM : exa_mid2 _ _ |- _ => exact (proj1 HM) end.
Ltac exa_mid2t := lazymatch goal with HM : exa_mid2 _ _ |- _ => exact HM end.
Ltac exa_pmkst := lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
  rewrite (st_ok_pi_restrict_mkst (L := B_prog_listing) (PI := PI_prog_B) _ _ _ _ HS eq_refl); cbn [ss_pc] end.
Ltac exa_atpc off :=
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rg (Z_to_bv 64 (_ + ?p)) ?m _) ?d) _ =>
    replace p with (EXA_PC off) by (vm_compute; reflexivity); rewrite exa_cfg end.
Ltac exa_leaf_CT K Hi1 Hnc :=
  exa_pmkst; exa_atpc 0xa70; apply K;
  eapply exa_CT; [ exa_mid1 | exa_kept_tac | exa_r21 | ];
  apply (exa_N_refuse _ _ c); [ exact Hi1 | exact Hnc | ].
Ltac exa_r23 := let R := fresh "R" in exa_reg (23%bv : bv 5) R; rewrite R, U18; reflexivity.
Ltac exa_rj r := let R := fresh "R" in exa_reg r R; rewrite R, U11; unfold w64; f_equal;
  lazymatch goal with Hsg : exn_sg c = _ |- _ => rewrite Hsg end;
  pose proof (exa_i1_nonneg E); unfold EXN_i1; lia.
Ltac exa_rlit r := let R := fresh "R" in exa_reg r R; rewrite R; first [exact exa_w64_m11 | exact exa_w64_mask | reflexivity].
Ltac exa_leaf_CL K :=
  exa_pmkst; exa_atpc 0x324; eapply K;
  eapply exa_CL; [ exa_mid2t | exa_kept_tac | exa_r21 | exa_r23 | exa_v136
                 | exa_rj (22%bv : bv 5) | exa_rj (10%bv : bv 5) | exa_rlit (13%bv : bv 5) | exa_rlit (14%bv : bv 5)
                 | exa_rlit (15%bv : bv 5) | | | ];
  rewrite <- ?Hb0, <- ?Hb1.

(* the walk of CN .. CT / CL *)
Lemma exa_walk : forall Q,
  (forall regs' M md', EXN_CT_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k (-1) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0xa70) regs' M md') Q) ->
  (forall regs' M md', EXN_CL_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k c (i1 + exn_sg c) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0x324) regs' M md') Q) ->
  SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0x278) regs memc mdc) Q.
Proof.
intros Q KTc KLc.
pose proof exa_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
pose proof exa_shf as Hsf. pose proof asan_consts as (C1 & _). pose proof (exa_i1_nonneg E) as Hi1z.
pose proof HDISP as (_ & Hnc & _). pose proof exa_pre as (Hd0 & _).
assert (Hi1 : (i1 < length x)%nat) by (unfold EXN_i1, exv_len in *; lia).
pose proof exa_mid0 as HM. pose proof (proj1 HM) as HJ.
assert (SHOK : sh_ok rsegs exa_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
unfold EXA_CEIL in F3. unfold exv_len in *.
rewrite <- (exa_cfg 0x278).
destruct (Z.eq_dec c 45) as [Hc45 | Hc45].
- assert (Hsg : exn_sg c = 1%nat) by (unfold exn_sg; rewrite (proj2 (Z.eqb_eq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases (i1 + exn_sg c) (length x)) as [Hj | Hj].
  + destruct (Nat.lt_ge_cases (i1 + exn_sg c + 1) (length x)) as [Hj2 | Hj2].
    * pose proof (exa_entry 1 2 [exa_cEQ; exa_cLT 1; exa_cLT 2] ltac:(left; split; [reflexivity | exact Hc45]) ltac:(lia)
        ltac:(exa_lia) ltac:(vm_compute; reflexivity)
        ltac:(split; [apply exa_cEQ_ok, Hc45 | split; [apply exa_cLT_ok; exa_lia
                                              | split; [apply exa_cLT_ok; exa_lia | exact I]]])) as HS.
      exa_run exa_Bspan0 (EXA_PC 0x284). exa_fsh_init. exa_drop.
      exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
      -- exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
      -- exa_run exa_Bspan (EXA_PC 0x324). exa_branch.
         ++ exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (H48 & _); congruence].
         ++ exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
            ** exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc.
               right; right. split; [lia|]. split; [rewrite <- Hb0; assumption | rewrite <- Hb1; assumption].
            ** exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (_ & _ & Hd1); congruence].
    * pose proof (exa_entry 1 1 [exa_cEQ; exa_cLT 1; exa_cGE 2] ltac:(left; split; [reflexivity | exact Hc45]) ltac:(lia)
        ltac:(exa_lia) ltac:(vm_compute; reflexivity)
        ltac:(split; [apply exa_cEQ_ok, Hc45 | split; [apply exa_cLT_ok; exa_lia
                                              | split; [apply exa_cGE_ok; exa_lia | exact I]]])) as HS.
      exa_run exa_Bspan0 (EXA_PC 0x284). exa_fsh_init. exa_drop.
      exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
      -- exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
      -- exa_run exa_Bspan (EXA_PC 0x324). exa_branch.
         ++ exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (H48 & _); congruence].
         ++ exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (_ & Hlt & _); lia].
  + pose proof (exa_entry 1 0 [exa_cEQ; exa_cGE 1] ltac:(left; split; [reflexivity | exact Hc45]) ltac:(lia)
      ltac:(exa_lia) ltac:(vm_compute; reflexivity)
      ltac:(split; [apply exa_cEQ_ok, Hc45 | split; [apply exa_cGE_ok; exa_lia | exact I]])) as HS.
    exa_run exa_Bspan0 (EXA_PC 0x284). exa_fsh_init. exa_drop.
    exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc. left. lia.
- assert (Hsg : exn_sg c = 0%nat) by (unfold exn_sg; rewrite (proj2 (Z.eqb_neq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases (i1 + exn_sg c + 1) (length x)) as [Hj2 | Hj2].
  + pose proof (exa_entry 0 2 [exa_cNE; exa_cLT 0; exa_cLT 1] ltac:(right; split; [reflexivity | exact Hc45]) ltac:(lia)
      ltac:(exa_lia) ltac:(vm_compute; reflexivity)
      ltac:(split; [apply exa_cNE_ok, Hc45 | split; [apply exa_cLT_ok; exa_lia
                                            | split; [apply exa_cLT_ok; exa_lia | exact I]]])) as HS.
    exa_run exa_Bspan0 (EXA_PC 0x284). exa_fsh_init. exa_drop.
    exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
    * exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
    * exa_run exa_Bspan (EXA_PC 0x324). exa_branch.
      -- exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (H48 & _); congruence].
      -- exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
         ++ exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc.
            right; right. split; [lia|]. split; [rewrite <- Hb0; assumption | rewrite <- Hb1; assumption].
         ++ exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (_ & _ & Hd1); congruence].
  + pose proof (exa_entry 0 1 [exa_cNE; exa_cLT 0; exa_cGE 1] ltac:(right; split; [reflexivity | exact Hc45]) ltac:(lia)
      ltac:(exa_lia) ltac:(vm_compute; reflexivity)
      ltac:(split; [apply exa_cNE_ok, Hc45 | split; [apply exa_cLT_ok; exa_lia
                                            | split; [apply exa_cGE_ok; exa_lia | exact I]]])) as HS.
    exa_run exa_Bspan0 (EXA_PC 0x284). exa_fsh_init. exa_drop.
    exa_run exa_Bspan (EXA_PC 0xa70). exa_branch.
    * exa_run exa_Bspan (EXA_PC 0xa70). exa_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
    * exa_run exa_Bspan (EXA_PC 0x324). exa_branch.
      -- exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (H48 & _); congruence].
      -- exa_run exa_Bspan (EXA_PC 0x324). exa_leaf_CL KLc; [lia | assumption | intros (_ & Hlt & _); lia].
Qed.

End env.

Lemma exa_E0_reg : forall extra n (r : Prelude.reg) v, Z.of_nat n = bv_unsigned r -> YK11.getr regs r = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (@Eimg _ B_prog_listing PI_prog_B (Ereg regs extra)) n) = v.
Proof.
intros extra n r v Hn Hr Hv. pose proof (u5_range r) as Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply exa_u64. exact Hv.
Qed.
Lemma exa_E0_extra : forall w0 w1, 0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 ->
  bv_unsigned (ew (@Eimg _ B_prog_listing PI_prog_B (Ereg regs [w64 w0; w64 w1])) 32) = w0 /\
  bv_unsigned (ew (@Eimg _ B_prog_listing PI_prog_B (Ereg regs [w64 w0; w64 w1])) 33) = w1.
Proof.
intros w0 w1 H0 H1. rewrite !Eimg_low by (unfold A_TEXT; lia).
pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 0) as E32. pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 1) as E33.
cbn [Nat.add nth] in E32, E33. rewrite E32, E33. split; apply exa_u64; assumption.
Qed.

(* the piece from the cut: the env of the walk is the cut's registers and the two text bytes after the sign *)
Lemma exa_core : forall Q,
  (forall regs' M md', EXN_CT_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k (-1) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0xa70) regs' M md') Q) ->
  (forall regs' M md', EXN_CL_pre B ARx SK E pos fx lyc Sc Hpc W regs' M md' k c (i1 + exn_sg c) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0x324) regs' M md') Q) ->
  SRr rsegs W (cfg_at (fx := fx) rsegs (exv_pc 0x278) regs memc mdc) Q.
Proof.
intros Q KTc KLc.
pose proof HBASE as (HEXB & _ & _). unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & _ & _ & _ & _ & _ & _ &
  HSRC & _).
destruct HSRC as (Hg & _). unfold bytes_at in Hg.
pose proof exa_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
pose proof exa_shf as Hsf. pose proof (exa_i1_nonneg E) as Hi1. pose proof exa_c45 as HC.
pose proof asan_consts as (C1 & _). unfold EXA_CEIL in F3. unfold exv_len in *.
pose proof (exa_nth_byte _ _ _ _ (i1 + exn_sg c)%nat Hg) as HB0.
pose proof (exa_nth_byte _ _ _ _ (S (i1 + exn_sg c)) Hg) as HB1.
destruct (exa_E0_extra (nth (i1 + exn_sg c)%nat x 0) (nth (S (i1 + exn_sg c)) x 0) ltac:(lia) ltac:(lia)) as (U32 & U33).
refine (exa_walk (nth (i1 + exn_sg c)%nat x 0) (nth (S (i1 + exn_sg c)) x 0)
  (@Eimg _ B_prog_listing PI_prog_B (Ereg regs [w64 (nth (i1 + exn_sg c)%nat x 0); w64 (nth (S (i1 + exn_sg c)) x 0)]))
  eq_refl eq_refl HB0 HB1 (Eimg_env _) _ (regs_ok_Eimg_Ereg _ _) _ _ _ _ _ _ _ U32 U33 Q KTc KLc).
- split; [|reflexivity]. intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite !ew_Ereg_lt by lia. reflexivity.
- apply (exa_E0_reg _ 9 9%bv); [reflexivity | exact R9 | lia].
- apply (exa_E0_reg _ 11 11%bv); [reflexivity | exact H11 | lia].
- apply (exa_E0_reg _ 12 12%bv); [reflexivity | exact H12 | unfold exv_len; lia].
- apply (exa_E0_reg _ 18 18%bv); [reflexivity | exact R18 | lia].
- apply (exa_E0_reg _ 25 25%bv); [reflexivity | exact R25 | unfold SHADOW_OFF; lia].
- apply (exa_E0_reg _ 26 26%bv); [reflexivity | exact R26 | unfold SHADOW_OFF in *; lia].
- apply (exa_E0_reg _ 27 27%bv); [reflexivity | exact H27 | lia].
Qed.

End ctx.
End core.

(* ======== the sub-piece: EXN_A of ExvB_NumCut.v ======== *)
Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis HT : EXN_T B ARx SK E pos.
Hypothesis HL : EXN_Bl B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.

Lemma exn_A : EXN_A B ARx SK E pos.
Proof.
intros fxc lyc Sc Hpc Wc regs memc mdc k c HPRE HBASE HDISP HCUR H11 H12 H27 H20.
unfold EXN_CN.
eapply (exa_core (fx := fxc) B ARx SK E pos HYP MK KS Wc regs memc mdc lyc Sc Hpc k c HPRE HBASE HDISP HCUR
  H11 H12 H27).
- intros regs' M md' HCT. exact (HT fxc lyc Sc Hpc Wc regs' M md' k (-1) HPRE HCT).
- intros regs' M md' HCL. exact (HL fxc lyc Sc Hpc Wc regs' M md' k c (EXN_i1 E + exn_sg c)%nat HPRE HCL).
Qed.
End p.

Print Assumptions exn_A.

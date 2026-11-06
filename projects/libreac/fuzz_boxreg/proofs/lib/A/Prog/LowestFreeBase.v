(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of rec_shape_of (plugin-hostd/fuzz_command, 0x891ec, 69 instructions),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the entry state with the GOT word and the shadow cell)
   and A/ACh5.v (the composition of the segments into the contract): the prologue up to the loop head (0x891ec ..
   0x89254), then the loop of lib/A/Prog/rec_shape_of_s.v for the 28 rows, from the image's read-only table g_shapes
   and the literals it points to (lib/A/Prog/CmdRo.v). The per-binary facts are the lemmas of CmdRecFacts' groups in
   lib/A/Prog/CmdRecBase.v, CmdRecRo.v and CmdRecImg.v, under the walk hypotheses
   (with cgif's names). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_shape_of.v, with its module paths, module names and numbers changed; 648 of its 709 lines of code are new or changed and 257 lines of the source are left out. *)
(* lowest_free_base (fuzz_boxreg.asan 0x81a54, 85 instructions): the contract of the ASan build's code.
   The function takes a 32-byte frame on the machine stack (addi sp,sp,-32; it saves ra, s0 and s1 there) and calls
   no function on a path that returns: range_taken is inlined. It reads the 288-byte registry struct at r (a0), a heap
   block of the caller: fabric (r + 284) once, n (r + 280) once, and, for each candidate base b = 0, 1, ... with
   b + k <= fabric, the base (r + 56 i + 8) and nch (r + 56 i + 12) of the rows i < n; each 4-byte load comes after
   the check of its shadow byte (the branches to __asan_report_load4 are refuted by the block's shadow: every byte of
   the struct is addressable). It returns in a0 the lowest b whose [b, b + k) fits in the fabric and meets no row's
   [base, base + nch), or -1 when there is none (fabric < k, or every b meets a row): Pau's lowest_free of
   lib/Prog/lowest_free_base_c.v, used as it is with the model of lib/Prog/Boxreg.v. It writes nothing outside its
   own frame.
   Hazards: the struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284); the code reads the rows
   i < n without a bound of its own, so n <= 5 (boxreg_B1) keeps every load inside the block; base + nch is an addw
   (32 bits), which the row bounds of boxreg_B3 and 1 <= fabric <= 40 (boxreg_B2) keep exact; k is the sign-extended
   int nch, 1 <= k < 2^31, compared with fabric in 64 bits.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBLowestFreeBase.v) calls range_taken instead of inlining
   it, takes a 64-byte frame and adds UBSan checks; the result is the same. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg lowest_free_base_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC81 YC4b YC1g YC1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 32-byte frame and ESTACK below it for the
   memory-checking runtime (it calls nothing but the error path). *)
Definition A_lowest_free_baseP : Z := BASE + AF_lowest_free_base.
Definition LOWEST_FREE_BASE_STK : Z := 32 + ESTACK.
Section h.
Variable B : asyms.
Definition tlowest_free_base_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (k : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B LOWEST_FREE_BASE_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
exists z, getr regs' 10 = w64 z /\ lowest_free_base_c.lowest_free bs k z).
Definition tlowest_free_base_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
afn_pre SEGS B LOWEST_FREE_BASE_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> 1 <= k < 2 ^ 31 ->
In (r, ReacBoxregInit.REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
SRr SEGS W (cfg_at SEGS A_lowest_free_baseP regs mem md) (tlowest_free_base_post regs ly S W mem md k bs).
(* The walk. The function runs in three pieces: the prologue and the two field checks (the entry state ss_lfb0, up to
   the row loop's head 0x81adc), the row loop (lfb_loop: from 0x81adc to 0x81b58, stated over machine states and
   proved by induction on 6 (fabric - b) + (n - i), one candidate base b and one row i per step), and the epilogue
   (from 0x81b58, after the loop's clobbered registers are havocked). Every __asan_report_load4 branch is refuted
   inside the symbolic runs: the struct's shadow is clean (lfb0_SH covers r .. r + 288, lfbI_SH the row's two
   words), so the shadow bytes the code loads are 0 or carry a slow-path check the struct's addressability
   discharges. *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
(* 0x81adc, the row loop's head, and 0x81b58, the epilogue, as offsets in the listing. *)
Definition A_lfb_I : Z := AF_lowest_free_base + 0x88.
Definition A_lfb_X : Z := AF_lowest_free_base + 0x104.
(* The entry state: atoms 32, 33, 34 are the shadow base, n and fabric; the struct's region holds n and fabric. *)
Definition lfb_struct_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 280 288 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 34 0))].
Definition lfb0_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, mkAF 1 (2 ^ 31 - 1) 0);
            (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 5 0); (34%nat, mkAF 1 40 0) ] [] [].
Definition ss_lfb0 : sstate :=
  mkSS AF_lowest_free_base sr_atoms [stack_region 32; got_regionP; bcell_regionP 32; lfb_struct_region] None lfb0_facts.
Definition lfb0_SH : list shent := [mkSHE 10 0 288].
Definition lfb_extra (bs : list byte) : list word :=
  map (Z_to_bv 64) [SB; Boxreg.bx_n bs; Boxreg.bx_fabric bs].
Definition EL (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (lfb_extra bs)).
(* The row loop's head: the machine's registers are atoms 0 .. 31, atoms 32 and 33 are row i's base and nch;
   t4 is named as the shadow address of t5 - 4 = r + 56 i + 8, a2 as t5. *)
Definition T4X : sv := SAlu ALU_ADD (SOff 14 0) (SAlu ALU_SRL (SOff 30 (-4)) (SLit 3)).
Definition lfb_row_region : YP09.region :=
  YP09.mkRegion (Some 30%nat) (-4) 4 0 0 [YP09.mkChunk (-4) (CVal 4 (SOff 32 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition lfbI_facts : facts :=
  mkFacts [ (5%nat, mkAF 2 41 0); (7%nat, mkAF 1 5 0); (11%nat, mkAF 1 40 0); (14%nat, mkAF SB SB 0);
            (15%nat, mkAF 1 40 0); (16%nat, mkAF 0 39 0); (17%nat, mkAF 1 5 0); (30%nat, mkAF 4108 140737479966720 2);
            (31%nat, mkAF 1 5 0); (32%nat, mkAF 0 38 0); (33%nat, mkAF 2 40 0) ] [] [].
Definition ss_lfbI : sstate :=
  mkSS A_lfb_I (sr_set (sr_set sr_atoms 29%bv T4X) 12%bv (SOff 30 0)) [lfb_row_region] None lfbI_facts.
Definition lfbI_SH : list shent := [mkSHE 30 (-4) 8].
Definition LFB_KEPT : list (bv 5) := [1; 2; 3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LFB_CLOB : list (bv 5) := [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Lemma lfb_clob_kept : forall r : bv 5, reg_in r LFB_CLOB = false -> r = 0%bv \/ In r LFB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
(* The registers at the row loop's head for candidate base b and row i. *)
Definition lfb_regs (regs : bvmap 5 word) (r k b i n f : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 (-1) /\ getr regs 11 = Z_to_bv 64 (b + k) /\ getr regs 14 = Z_to_bv 64 SB /\
  getr regs 15 = Z_to_bv 64 f /\ getr regs 16 = Z_to_bv 64 b /\ getr regs 17 = Z_to_bv 64 n /\
  getr regs 5 = Z_to_bv 64 (k + 1) /\ getr regs 6 = Z_to_bv 64 (r + 12) /\ getr regs 7 = Z_to_bv 64 n /\
  getr regs 28 = Z_to_bv 64 (SB + (r + 8) / 8) /\ getr regs 29 = Z_to_bv 64 (SB + (r + 8) / 8 + 7 * i) /\
  getr regs 30 = Z_to_bv 64 (r + 12 + 56 * i) /\ getr regs 12 = Z_to_bv 64 (r + 12 + 56 * i) /\
  getr regs 31 = Z_to_bv 64 (n - i).
(* What the row loop leaves at 0x81b58. *)
Definition lfb_loop_post (regsR : bvmap 5 word) (sp1 : Z) ly S (W : world SEGS) mem0 md0 (bs : list byte) (k : Z)
  : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' z,
  c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_lfb_X)) mem' (seg_rom SEGS)) md' /\
  ajournal SEGS B 0 sp1 [] ly S W mem0 md0 [] ly S W mem' md' 0 /\
  getr regs' 10 = Z_to_bv 64 z /\ lowest_free_base_c.lowest_free bs k z /\
  (forall rr, In rr LFB_KEPT -> getr regs' rr = getr regsR rr).
(* ---- byte and value facts ---- *)
Lemma lfb_swrap_mod32 : forall v, 0 <= v < 2 ^ 32 -> bv_swrap 32 v mod 2 ^ 32 = v.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31). Z.div_mod_to_equations. lia.
Qed.
Lemma lfb_le_val4 : forall u0 u1 u2 u3 (kk : nat), 0 <= u0 < 256 -> 0 <= u1 < 256 -> 0 <= u2 < 256 -> 0 <= u3 < 256 ->
  (kk < 4)%nat ->
  Z.shiftr (u0 + 256 * (u1 + 256 * (u2 + 256 * (u3 + 256 * 0)))) (8 * Z.of_nat kk) mod 256 = nth kk [u0; u1; u2; u3] 0.
Proof.
intros u0 u1 u2 u3 kk H0 H1 H2 H3 Hk. rewrite Z.shiftr_div_pow2 by lia.
destruct kk as [|[|[|[|kk]]]]; [| | | | lia]; cbn [nth].
- change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 2)) with 65536. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.
Lemma lfb_nth_skipn : forall (l : list byte) (o j : nat), nth (o + j) l (Z_to_bv 8 0) = nth j (skipn o l) (Z_to_bv 8 0).
Proof.
induction l as [|x l IH]; intros o j; [destruct o, j; reflexivity|].
destruct o as [|o]; [reflexivity|]. cbn [skipn]. rewrite <- IH. reflexivity.
Qed.
Lemma lfb_le_byte_rd4 : forall (bs : list byte) off (kk : nat), 0 <= off -> off + 4 <= Z.of_nat (length bs) -> (kk < 4)%nat ->
  YO0f.le_byte (Boxreg.rd4 bs off) 4 kk = bv_unsigned (nth (Z.to_nat (off + Z.of_nat kk)) bs (Z_to_bv 8 0)).
Proof.
intros bs off kk Ho Hl Hk.
replace (Z.to_nat (off + Z.of_nat kk)) with (Z.to_nat off + kk)%nat by lia.
rewrite lfb_nth_skipn. unfold Boxreg.rd4, Boxreg.bsub.
assert (HL : (4 <= length (skipn (Z.to_nat off) bs))%nat) by (rewrite length_skipn; lia).
destruct (skipn (Z.to_nat off) bs) as [|c0 [|c1 [|c2 [|c3 t]]]]; cbn [length] in HL; try lia.
change (Z.to_nat 4) with 4%nat. cbn [firstn]. rewrite ?firstn_O.
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val].
pose proof (bv_unsigned_in_range 8 c0) as B0. pose proof (bv_unsigned_in_range 8 c1) as B1.
pose proof (bv_unsigned_in_range 8 c2) as B2. pose proof (bv_unsigned_in_range 8 c3) as B3.
change (bv_modulus 8) with 256 in B0, B1, B2, B3.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
assert (HN : bv_unsigned (nth kk (c0 :: c1 :: c2 :: c3 :: t) (Z_to_bv 8 0)) =
  nth kk [bv_unsigned c0; bv_unsigned c1; bv_unsigned c2; bv_unsigned c3] 0)
  by (destruct kk as [|[|[|[|kk]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]).
rewrite HN. clear HN.
generalize (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) B0 B1 B2 B3 Hk.
clear. intros u0 u1 u2 u3 B0 B1 B2 B3 Hk.
rewrite lfb_swrap_mod32 by lia.
exact (lfb_le_val4 u0 u1 u2 u3 kk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hk).
Qed.
Lemma lfb_val_mem4 : forall H mem (r : Z) (bs : list byte) off,
  (forall j, 0 <= j < 288 -> aview SEGS H mem (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
  length bs = 288%nat -> 0 <= off -> off + 4 <= 288 ->
  val_mem SEGS (mrestrict H mem) (r + off) 4 (Boxreg.rd4 bs off).
Proof.
intros H mem r bs off HB HL Ho1 Ho2 kk Hk.
destruct (aview_byte SEGS H mem (r + off + Z.of_nat kk) _
  ltac:(replace (r + off + Z.of_nat kk) with (r + (off + Z.of_nat kk)) by lia; apply HB; lia)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. rewrite (lfb_le_byte_rd4 bs off kk Ho1 ltac:(rewrite HL; lia) Hk), Hv.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma lfb_shent : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z) (Bx : sv),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex Bx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS Bx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md Ex n q b sz lo hi Bx HAR Hin HB Hq Hlo Hlh Hhi.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
rewrite <- (aview_rd_of SEGS). split.
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
- intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
  revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.
Lemma lfb_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma lfb_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H. cbn [sv_denot]. rewrite H. apply Boxreg.addi_lit. Qed.
Lemma lfb_den_add : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof. intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply alu64_add_lit. Qed.
Lemma lfb_den_srl3 : forall E a x, sv_denot E a = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL a (SLit 3)) = Z_to_bv 64 (x / 8).
Proof.
intros E a x Ha Hx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
unfold U at 1. rewrite Ha, unsigned_lit_small by lia.
rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.
Lemma lfb_alu_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small x Hx), (unsigned_lit_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 < 2 ^ 64) by (Z.div_mod_to_equations; lia).
rewrite (unsigned_lit_small (x / 8) Hd). unfold bv_wrap, bv_modulus. apply Z.mod_small. exact Hd.
Qed.
Lemma lfb_div_row : forall r i, 0 <= i -> (r + 8 + 56 * i) / 8 = (r + 8) / 8 + 7 * i.
Proof. intros r i Hi. replace (r + 8 + 56 * i) with ((r + 8) + (7 * i) * 8) by lia. apply Z.div_add. lia. Qed.
Lemma lfb_T4X_val : forall E r i, ew E 14 = Z_to_bv 64 SB -> ew E 30 = Z_to_bv 64 (r + 12 + 56 * i) ->
  0 <= r -> 0 <= i -> r + 12 + 56 * i < 2 ^ 47 ->
  sv_denot E T4X = Z_to_bv 64 (SB + (r + 8) / 8 + 7 * i).
Proof.
intros E r i H14 H30 Hr Hi Hq. unfold T4X.
rewrite (lfb_den_add E _ _ SB ((r + 8 + 56 * i) / 8)); [ | exact (lfb_den_atom E 14 SB H14) | ].
- rewrite lfb_div_row by lia. f_equal. lia.
- apply lfb_den_srl3; [|lia]. rewrite (lfb_den_off E 30 _ (-4) H30). f_equal. lia.
Qed.
Lemma lfb_T4X7_val : forall E r i, ew E 14 = Z_to_bv 64 SB -> ew E 30 = Z_to_bv 64 (r + 12 + 56 * i) ->
  0 <= r -> 0 <= i -> r + 12 + 56 * i < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD T4X (SLit 7)) = Z_to_bv 64 (SB + (r + 8) / 8 + 7 * (i + 1)).
Proof.
intros E r i H14 H30 Hr Hi Hq.
rewrite (lfb_den_add E T4X (SLit 7) _ 7 (lfb_T4X_val E r i H14 H30 Hr Hi Hq) (eq_refl : sv_denot E (SLit 7) = Z_to_bv 64 7)).
f_equal. lia.
Qed.
Lemma lfb_T3_val : forall E r, ew E 32 = Z_to_bv 64 SB -> ew E 10 = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 8) (SLit 3))) = Z_to_bv 64 (SB + (r + 8) / 8).
Proof.
intros E r H32 H10 Hr.
apply (lfb_den_add E _ _ SB ((r + 8) / 8)); [exact (lfb_den_atom E 32 SB H32)|].
apply lfb_den_srl3; [exact (lfb_den_off E 10 r 8 H10) | lia].
Qed.
Lemma lfb_bt_ge : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !Boxreg.signed_lit by lia. reflexivity. Qed.
Lemma lfb_bt_lt : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !Boxreg.signed_lit by lia. reflexivity. Qed.
Lemma lfb_bt_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
(* ---- the model facts at the four exits ---- *)
Lemma lfb_lf_small : forall bs k, Boxreg.bx_fabric bs < k -> lowest_free_base_c.lowest_free bs k (-1).
Proof. intros bs k H. left. split; [reflexivity|]. intros b Hb Hbk. lia. Qed.
Lemma lfb_lf_zero : forall bs k, Boxreg.bx_n bs <= 0 -> k <= Boxreg.bx_fabric bs -> lowest_free_base_c.lowest_free bs k 0.
Proof.
intros bs k Hn Hk. right. split; [lia|]. split; [lia|]. split; [|intros b Hb; lia].
intros (j & Hj & _). lia.
Qed.
Lemma lfb_mod4 : forall r i, r mod 16 = 0 -> (r + 12 + 56 * i) mod 4 = 0.
Proof. intros r i H. Z.div_mod_to_equations. lia. Qed.
Lemma lfb_lf_found : forall bs k b, 0 <= b -> b + k <= Boxreg.bx_fabric bs ->
  (forall c, 0 <= c < b -> lowest_free_base_c.slice_meets bs c k) ->
  (forall j, 0 <= j < Boxreg.bx_n bs -> ~ Boxreg.meets b k (Boxreg.bx_base bs j) (Boxreg.bx_nch bs j)) ->
  lowest_free_base_c.lowest_free bs k b.
Proof.
intros bs k b Hb Hbk HM HN. right. split; [lia|]. split; [lia|]. split; [|exact HM].
intros (j & Hj & Hm). exact (HN j Hj Hm).
Qed.
Lemma lfb_lf_none : forall bs k b i, 0 <= i < Boxreg.bx_n bs -> Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i) ->
  Boxreg.bx_fabric bs < b + 1 + k -> (forall c, 0 <= c < b -> lowest_free_base_c.slice_meets bs c k) ->
  lowest_free_base_c.lowest_free bs k (-1).
Proof.
intros bs k b i Hi Hm Hf HM. left. split; [reflexivity|]. intros c Hc Hck.
destruct (Z.lt_ge_cases c b) as [L|L]; [apply HM; lia|].
assert (c = b) by lia. subst c. exists i. split; [exact Hi | exact Hm].
Qed.
(* A register's value at a symbolic state, as the state's expression (not unfolded). *)
Ltac lreg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
(* The machine state of a symbolic state stopped at listing offset A. *)
Ltac lfb_at HS A :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ss (restrict _ ?ms) =>
    let Hm := fresh "Hm" in
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hm;
    replace (BASE + ss_pc ss) with (BASE + A) in Hm by (vm_compute; reflexivity);
    rewrite Hm; clear Hm
  end.
(* A branch condition, as a fact about the numbers the atoms stand for. *)
Ltac lfb_hc Hc :=
  cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?ew_ewset_other in Hc by lia;
  repeat match type of Hc with context [ew ?E ?n] =>
    match goal with H : ew E n = Z_to_bv 64 _ |- _ => rewrite H in Hc end end;
  rewrite ?unsigned_lit_small in Hc by (unfold SB; lia);
  rewrite ?Z.add_0_r, ?alu64_add_lit in Hc;
  first [ rewrite lfb_bt_ge in Hc by lia | rewrite lfb_bt_lt in Hc by lia | rewrite lfb_bt_ne in Hc by lia ];
  first [ apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
        | apply (proj1 (negb_true_iff _)) in Hc; first [apply Z.ltb_ge in Hc | apply Z.eqb_neq in Hc]
        | apply (proj1 (negb_false_iff _)) in Hc; first [apply Z.ltb_lt in Hc | apply Z.eqb_eq in Hc] ];
  let H' := fresh "Hcond" in rename Hc into H'.
(* The value of a register's expression. *)
Ltac lfb_den :=
  first
  [ lazymatch goal with |- sv_denot ?E (SOff ?n 0) = _ =>
      match goal with H : ew E n = Z_to_bv 64 _ |- _ => rewrite (lfb_den_atom E n _ H) end end;
    first [reflexivity | f_equal; lia]
  | lazymatch goal with
    |- sv_denot ?E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 14 0) (SAlu ALU_SRL (SOff 30 (-4)) (SLit 3))) (SLit 7)) = _ =>
      change (SAlu ALU_ADD (SAlu ALU_ADD (SOff 14 0) (SAlu ALU_SRL (SOff 30 (-4)) (SLit 3))) (SLit 7))
        with (SAlu ALU_ADD T4X (SLit 7));
      match goal with H14 : ew E 14 = _, H30 : ew E 30 = _ |- _ =>
        rewrite (lfb_T4X7_val E _ _ H14 H30) by lia end;
      first [reflexivity | f_equal; lia]
    end
  | cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
    repeat match goal with |- context [ew ?E ?n] =>
      match goal with H : ew E n = Z_to_bv 64 _ |- _ => rewrite H end end;
    rewrite ?unsigned_lit_small by (unfold SB; lia);
    rewrite ?Z.add_0_r, ?lfb_alu_srl3 by lia; rewrite ?Z.add_0_r, ?alu64_add_lit;
    first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity] ].
(* The registers of lfb_regs at a stop, one by one. *)
Ltac lfb_regs_tac HS :=
  unfold lfb_regs;
  repeat match goal with
  | |- _ /\ _ => split
  | |- getr _ ?R = _ => let Q := fresh "Q" in lreg HS R Q; rewrite Q; clear Q; lfb_den
  end.
(* The registers the loop keeps. *)
Ltac lfb_kept :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr;
  lazymatch goal with HKR : forall rr, In rr LFB_KEPT -> getr _ rr = getr _ rr |- _ => rewrite <- (HKR rr Hrr) end;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HA : env_agree 32 _ _ |- _ =>
    exact (regs_kept_of_st_ok_pi _ _ _ _ _ LFB_KEPT HS HA ltac:(vm_compute; reflexivity) rr Hrr) end.
(* The loop's exit at 0x81b58 with a0 = z. *)
Ltac lfb_exit z HLF :=
  let Q10 := fresh "Q10" in
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => lreg HS (10%bv : bv 5) Q10; lfb_at HS A_lfb_X end;
  apply SRr_ret; split; [reflexivity|];
  do 3 eexists; exists z; split; [reflexivity|];
  split; [lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end|];
  split; [rewrite Q10; lfb_den|];
  split; [HLF|];
  lfb_kept.
(* ---- the row loop ---- *)
Lemma lfb_loop : forall (d : nat) (b i : Z) (regs regsR : bvmap 5 word) memc mdc sp1 ly S W mem0 md0 (r k : Z)
    (bs : list byte),
  6 * (Boxreg.bx_fabric bs - b) + (Boxreg.bx_n bs - i) <= Z.of_nat d ->
  ajournal SEGS B 0 sp1 [] ly S W mem0 md0 [] ly S W memc mdc 0 ->
  In (r, ReacBoxregInit.REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall j, 0 <= j < 288 -> aview SEGS (w_H W) mem0 (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
  lfb_regs regs r k b i (Boxreg.bx_n bs) (Boxreg.bx_fabric bs) ->
  0 <= i < Boxreg.bx_n bs -> 0 <= b -> 1 <= k -> b + k <= Boxreg.bx_fabric bs ->
  (forall c, 0 <= c < b -> lowest_free_base_c.slice_meets bs c k) ->
  (forall j, 0 <= j < i -> ~ Boxreg.meets b k (Boxreg.bx_base bs j) (Boxreg.bx_nch bs j)) ->
  (forall rr, In rr LFB_KEPT -> getr regs rr = getr regsR rr) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lfb_I)) memc (seg_rom SEGS)) mdc)
    (lfb_loop_post regsR sp1 ly S W mem0 md0 bs k).
Proof.
induction d as [|d IH]; intros b i regs regsR memc mdc sp1 ly S W mem0 md0 r k bs
  Hd HJ Hblk HL HBS HB1 HB2 HB3 HR Hi Hb Hk Hbk HM HN HKR.
{ exfalso. lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W memc mdc r ReacBoxregInit.REG_SIZE HAR Hblk) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size ReacBoxregInit.REG_SIZE) with 288 in *.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'. pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
assert (HBC : forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) memc (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))).
{ intros j Hj. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 r ReacBoxregInit.REG_SIZE j Hblk Hblk ltac:(change (req_size ReacBoxregInit.REG_SIZE) with 288; lia)
    ltac:(intros X; exact (inFP_nil _ X))).
  apply HBS. exact Hj. }
destruct (Boxreg.B3_bounds bs i HB2 HB3 Hi) as (Hb0 & Hn0 & Hbn).
pose proof (lfb_val_mem4 (w_H W) memc r bs (56 * i + 8) HBC HL ltac:(lia) ltac:(lia)) as VB.
pose proof (lfb_val_mem4 (w_H W) memc r bs (56 * i + 12) HBC HL ltac:(lia) ltac:(lia)) as VN.
change (Boxreg.rd4 bs (56 * i + 8)) with (Boxreg.bx_base bs i) in VB.
change (Boxreg.rd4 bs (56 * i + 12)) with (Boxreg.bx_nch bs i) in VN.
destruct HR as (R10 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & R7 & R28 & R29 & R30 & R12 & R31).
remember (Eimg (Ereg regs [Z_to_bv 64 (Boxreg.bx_base bs i); Z_to_bv 64 (Boxreg.bx_nch bs i)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (Boxreg.bx_base bs i); Z_to_bv 64 (Boxreg.bx_nch bs i)]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (Boxreg.bx_base bs i))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_nch bs i))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E5 : ew E 5 = Z_to_bv 64 (k + 1)) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E6 : ew E 6 = Z_to_bv 64 (r + 12)) by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
assert (E7 : ew E 7 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7).
assert (E10 : ew E 10 = Z_to_bv 64 (-1)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (b + k)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = Z_to_bv 64 SB) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (E15 : ew E 15 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E16 : ew E 16 = Z_to_bv 64 b) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E28 : ew E 28 = Z_to_bv 64 (SB + (r + 8) / 8)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
assert (E30 : ew E 30 = Z_to_bv 64 (r + 12 + 56 * i)) by (rewrite (EE 30%nat 30%bv eq_refl); exact R30).
assert (E31 : ew E 31 = Z_to_bv 64 (Boxreg.bx_n bs - i)) by (rewrite (EE 31%nat 31%bv eq_refl); exact R31).
clear HE.
assert (HS : st_ok_pi SEGS VAL E ss_lfbI
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_lfb_I)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lfbI. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_pin; [exact ER | intros X; discriminate X | ] | intros X; discriminate X | ].
    + rewrite R29, (lfb_T4X_val E r i E14 E30) by lia. reflexivity.
    + rewrite R12, (lfb_den_atom E 30 _ E30). reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, lfb_row_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E30, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ (r + 12 + 56 * i) (-4) 4 (SOff 32 0) (Boxreg.bx_base bs i));
        [exact (lfb_den_atom E 32 _ E32) | zside | zside |].
      replace (r + 12 + 56 * i + -4) with (r + (56 * i + 8)) by lia. exact VB.
    + apply (chunk_ok_val SEGS E _ (r + 12 + 56 * i) 0 4 (SOff 33 0) (Boxreg.bx_nch bs i));
        [exact (lfb_den_atom E 33 _ E33) | zside | zside |].
      replace (r + 12 + 56 * i + 0) with (r + (56 * i + 12)) by lia. exact VN.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]].
    cbn [lfbI_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E5, E7, E11, E14, E15, E16, E17, E30, E31, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 2) with 4.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | apply lfb_mod4; exact Hr16]. }
assert (SHOK : sh_ok SEGS (SOff 14 0) lfbI_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, lfbI_SH. apply Forall_cons; [|apply Forall_nil].
  apply (lfb_shent ly S W memc mdc E 30 (r + 12 + 56 * i) r ReacBoxregInit.REG_SIZE (-4) 8 (SOff 14 0) HAR Hblk).
  - rewrite (U_atom E 14 SB E14) by (unfold SB; lia). reflexivity.
  - apply (U_atom E 30 _ E30). lia.
  - lia.
  - lia.
  - change (req_size ReacBoxregInit.REG_SIZE) with 288. lia. }
clear ER EE.
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac |].
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* base_i >= b + k: row i does not meet b *)
  lfb_hc Hc.
  assert (Hnm : ~ Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia).
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac |].
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* another row: back to 0x81adc with row i + 1 *)
    lfb_hc Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_I; [awr_ok_tac |].
    lfb_at HS A_lfb_I.
    eapply (IH b (i + 1) _ regsR _ _ sp1 ly S W mem0 md0 r k bs);
    [ lia | exact HJ | exact Hblk | exact HL | exact HBS | exact HB1 | exact HB2 | exact HB3
    | lfb_regs_tac HS | lia | lia | lia | lia | exact HM
    | intros j Hj; destruct (Z.lt_ge_cases j i) as [Lj|Lj]; [apply HN; lia | replace j with i by lia; exact Hnm]
    | lfb_kept ].
  + (* no row left: b is free *)
    lfb_hc Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_X; [awr_ok_tac |].
    lfb_exit b ltac:(apply lfb_lf_found; [lia | lia | exact HM |];
      intros j Hj; destruct (Z.lt_ge_cases j i) as [Lj|Lj]; [apply HN; lia | replace j with i by lia; exact Hnm]).
- (* base_i < b + k *)
  lfb_hc Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac |].
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* b < base_i + nch_i: row i meets b *)
    lfb_hc Hc.
    assert (Hm : Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia).
    paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac |].
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* b + 1 + k <= fabric: the next candidate b + 1, from row 0 *)
      lfb_hc Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_I; [awr_ok_tac |].
      lfb_at HS A_lfb_I.
      eapply (IH (b + 1) 0 _ regsR _ _ sp1 ly S W mem0 md0 r k bs);
      [ lia | exact HJ | exact Hblk | exact HL | exact HBS | exact HB1 | exact HB2 | exact HB3
      | lfb_regs_tac HS | lia | lia | lia | lia
      | intros c Hc0; destruct (Z.lt_ge_cases c b) as [Lc|Lc];
        [apply HM; lia | replace c with b by lia; exists i; split; [exact Hi | exact Hm]]
      | intros j Hj; lia
      | lfb_kept ].
    * (* fabric < b + 1 + k: no candidate is left *)
      lfb_hc Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_X; [awr_ok_tac |].
      lfb_exit (-1) ltac:(apply (lfb_lf_none bs k b i Hi Hm); [lia | exact HM]).
  + (* base_i + nch_i <= b: row i does not meet b *)
    lfb_hc Hc.
    assert (Hnm : ~ Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia).
    paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac |].
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* another row: back to 0x81adc with row i + 1 *)
      lfb_hc Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_I; [awr_ok_tac |].
      lfb_at HS A_lfb_I.
      eapply (IH b (i + 1) _ regsR _ _ sp1 ly S W mem0 md0 r k bs);
      [ lia | exact HJ | exact Hblk | exact HL | exact HBS | exact HB1 | exact HB2 | exact HB3
      | lfb_regs_tac HS | lia | lia | lia | lia | exact HM
      | intros j Hj; destruct (Z.lt_ge_cases j i) as [Lj|Lj]; [apply HN; lia | replace j with i by lia; exact Hnm]
      | lfb_kept ].
    * (* no row left: b is free *)
      lfb_hc Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_X; [awr_ok_tac |].
      lfb_exit b ltac:(apply lfb_lf_found; [lia | lia | exact HM |];
        intros j Hj; destruct (Z.lt_ge_cases j i) as [Lj|Lj]; [apply HN; lia | replace j with i by lia; exact Hnm]).
Qed.
(* ---- the entry state ---- *)
Lemma lfb_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
  afn_pre SEGS B LOWEST_FREE_BASE_STK ly S W regs mem md ch ->
  getr regs 10 = w64 r -> getr regs 11 = w64 k -> 1 <= k < 2 ^ 31 ->
  In (r, ReacBoxregInit.REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs ->
  st_ok_pi SEGS VAL (EL regs bs) ss_lfb0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_lowest_free_base)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 32 0) lfb0_SH (EL regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hblk HL HBS HB1 HB2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STK = 4128) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r ReacBoxregInit.REG_SIZE HAR Hblk) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size ReacBoxregInit.REG_SIZE) with 288 in *.
pose proof (blk_off_imgP B ly S W mem md r ReacBoxregInit.REG_SIZE HAR Hblk) as Hrimg.
change (req_size ReacBoxregInit.REG_SIZE) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'. pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
assert (HBS' : forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) mem (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0))))
  by (intros j Hj; apply HBS; unfold ReacBoxregInit.REG_SIZE; lia).
pose proof (lfb_val_mem4 (w_H W) mem r bs 280 HBS' HL ltac:(lia) ltac:(lia)) as VN.
pose proof (lfb_val_mem4 (w_H W) mem r bs 284 HBS' HL ltac:(lia) ltac:(lia)) as VF.
change (Boxreg.rd4 bs 280) with (Boxreg.bx_n bs) in VN. change (Boxreg.rd4 bs 284) with (Boxreg.bx_fabric bs) in VF.
rewrite restrict_mkst_fx.
set (E := EL regs bs).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (lfb_extra bs)) n)
  by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k)
  by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_fabric bs))
  by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_lfb0. apply pa_entry_st_ok_full.
  + subst E. unfold EL. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, lfb_struct_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (Boxreg.bx_n bs));
         [exact (lfb_den_atom E 33 _ E33) | zside | zside | exact VN].
      -- apply (chunk_ok_val SEGS E _ r 284 4 (SOff 34 0) (Boxreg.bx_fabric bs));
         [exact (lfb_den_atom E 34 _ E34) | zside | zside | exact VF].
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, lfb_struct_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hrceil Hr4096 Hrimg. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [lfb0_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil Hk HB1' HB2'. clear. unfold SB. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lfb0_SH. apply Forall_cons; [|apply Forall_nil].
  apply (lfb_shent ly S W mem md E 10 r r ReacBoxregInit.REG_SIZE 0 288 (SOff 32 0) HAR Hblk).
  + rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
  + apply (U_atom E 10 _ E10). lia.
  + lia.
  + lia.
  + change (req_size ReacBoxregInit.REG_SIZE) with 288. lia.
Qed.
(* The return: a0 = z, the frame's saves restored, and the post of the contract. *)
Ltac lfb_leaf z Ha0 HLF :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R1 := fresh "R1" in let R10 := fresh "R10" in
  prreg HS (1%bv : bv 5) R1; lreg HS (10%bv : bv 5) R10;
  eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  unfold tlowest_free_base_post, apost_base;
  do 5 eexists;
  split; [cbn [ms_regs]; rewrite R1;
          lazymatch goal with E1 : ew _ 1 = getr _ 1, Hra : YK0s.ret_ok _ |- _ => rewrite E1, Hra end; reflexivity |];
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
          [lazymatch goal with HAE : env_agree 32 _ _ |- _ => env_agree_chain HAE end | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  exists z; split; [cbn [ms_regs]; rewrite R10; Ha0 | HLF]
  end.
Ltac lfb_usp :=
  lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
  cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); cbn [ew ewset Nat.eqb];
  rewrite ?ew_ewset_other by lia; exact Usp end.
Theorem pb_lowest_free_base : tlowest_free_base_spec.
Proof.
unfold tlowest_free_base_spec.
intros ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hblk HL HBS HB1 HB2 HB3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (lfb_entry ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hblk HL HBS HB1 HB2) as [HS SHOK].
pose proof (ajournal_init SEGS B LOWEST_FREE_BASE_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STK = 4128) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r ReacBoxregInit.REG_SIZE HAR Hblk) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size ReacBoxregInit.REG_SIZE) with 288 in *.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'. pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
remember (EL regs bs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EL; apply Eimg_env).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (lfb_extra bs)) n)
  by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k)
  by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_fabric bs))
  by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (lfb_extra bs)) E)
  by (split; [intros n Hn; apply EL0; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL0.
unfold cfg_at. change (w64 A_lowest_free_baseP) with (Z_to_bv 64 (BASE + AF_lowest_free_base)).
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; lfb_usp |].
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* fabric < k: -1 *)
  lfb_hc Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; lfb_usp |].
  lfb_leaf (-1) ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity) ltac:(apply lfb_lf_small; lia).
- (* k <= fabric *)
  lfb_hc Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; lfb_usp |].
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* n <= 0: 0 *)
    lfb_hc Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; lfb_usp |].
    lfb_leaf 0 ltac:(reflexivity) ltac:(apply lfb_lf_zero; lia).
  + (* n >= 1: the row loop from candidate 0, row 0 *)
    lfb_hc Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A_lfb_I; [awr_ok_tac; lfb_usp |].
    lfb_at HS A_lfb_I.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?dd) _ =>
      assert (HR : lfb_regs rg r k 0 0 (Boxreg.bx_n bs) (Boxreg.bx_fabric bs)) by (lfb_regs_tac HS);
      pose proof (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ W mm dd _ 0 (spZ regs - 32) [] (-32)
        HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(rewrite WS; lia)) as HJL;
      assert (HBL : forall j, 0 <= j < 288 ->
        aview SEGS (w_H W) mm (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0))));
      [ intros j Hj; pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
        rewrite (F2 r ReacBoxregInit.REG_SIZE j Hblk Hblk ltac:(change (req_size ReacBoxregInit.REG_SIZE) with 288; lia)
          ltac:(intros X; exact (inFP_nil _ X)));
        apply HBS; unfold ReacBoxregInit.REG_SIZE; lia
      | ];
      eapply SRr_bind;
      [ eapply (lfb_loop (Z.to_nat (6 * Boxreg.bx_fabric bs + Boxreg.bx_n bs)) 0 0 rg rg mm dd (spZ regs - 32)
          ly S W mm dd r k bs);
        [ lia | exact HJL | exact Hblk | exact HL | exact HBL | exact HB1 | exact HB2 | exact HB3 | exact HR
        | lia | lia | lia | lia | intros c Hc0; lia | intros j Hj; lia | intros rr Hrr; reflexivity ]
      | ];
      cbv beta; intros W3 c3 Hwle3 (-> & regsL & memL & mdL & z & -> & HJL3 & H10L & HLF & HKL);
      pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ mm _ 0 0 (spZ regs - 32) [] [] ly S W memL mdL 0
        HJ HJL3 ltac:(rewrite WS; lia) ltac:(lia)) as HJ3
    end.
    match type of HJ3 with ?P -> _ =>
      assert (HFP : P) by (intros a Ha; exfalso; exact (inFP_nil _ Ha)); specialize (HJ3 HFP); clear HFP end.
    cbn [app] in HJ3. change (0 + 0) with 0 in HJ3.
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex ?ss ?msr =>
      let rs := eval vm_compute in (pick (ss_mem ss) [0%nat]) in
      pose proof (st_ok_pi_after_stretch 35 Ex (abs_ss VAL ss) msr regsL (mrestrict (w_H W) memL) rs A_lfb_X LFB_CLOB HS eq_refl
        ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
      let ss2 := eval vm_compute in (ss_after_stretch ss rs 35 LFB_CLOB A_lfb_X) in
      change (ss_after_stretch (abs_ss VAL ss) rs 35 LFB_CLOB A_lfb_X) with ss2 in HS2;
      assert (HEIst : img_env VAL A_LIM (havoc Ex 35 (map (getr regsL) LFB_CLOB)))
        by (apply img_env_havoc; [first [exact HEI | assumption] | cbv; lia])
    end.
    match type of HS2 with ?P -> ?Q -> _ =>
      assert (HP : P); [| assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ]] end.
    { intros rr Hrr. cbn [ms_regs restrict].
      destruct (lfb_clob_kept rr Hrr) as [-> | Hin]; [rewrite !getr_zero; reflexivity | apply HKL; exact Hin]. }
    { cbn [ms_mem restrict]. constructor; [|constructor].
      eapply (region_kept_stack_sub SEGS B _); [exact HJL3 | exact HJ3 | lfb_usp | lia | rewrite WS; lia | lia | lia | lia]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
      assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by apply Forall_nil end.
    clear SHOK.
    paj_run_tok RUN HS HJ3 SHOK2 Bspan; [awr_ok_tac; lfb_usp |].
    lfb_leaf z ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      cbn [ew havoc Nat.ltb Nat.leb Nat.sub nth map LFB_CLOB]; exact H10L) ltac:(exact HLF).
Qed.
End h.
End f.
End d.

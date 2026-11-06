(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and numbers changed; 845 of its 937 lines of code are new or changed and 755 lines of the source are left out. *)
(* range_taken (fuzz_boxreg.asan-ubsan 0x81d6c, 74 instructions): the contract of the ASan+UBSan build's code. The
   asan build has no such function: it inlines range_taken into lowest_free_base and reac_boxreg_declare.
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; it saves ra there for the call of
   __asan_report_load4), checks r (a0) for 4-byte alignment for UBSan, and reads the 288-byte registry struct at r,
   a heap block of the caller: n (r + 280), then base (r + 56 i + 8) and nch (r + 56 i + 12) of the rows i < n, each
   4-byte load after the check of its shadow byte, up to the first row that meets [b, b + k) (b in a1, k in a2). It
   returns 1 in a0 when [b, b + k) meets some row's [base, base + nch), else 0: Pau's slice_meets of
   lib/Prog/lowest_free_base_c.v, used as it is with the model of lib/Prog/Boxreg.v. It writes nothing outside its
   own frame.
   Hazards: the struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284). Every UBSan check
   branches to the UBSan trap (the unimp at 0x81e74). The array-bounds check at row 5 is refuted by n <= 5
   (boxreg_B1). The overflow checks on b + k and on base + nch (addw against the 64-bit sum) are refuted by 0 <= b,
   0 <= k, b + k <= fabric and the row bounds 0 <= base, 0 <= nch, base + nch <= fabric <= 40. The alignment and
   pointer-overflow checks on r and the branches to __asan_report_load4 are refuted by the allocator's block and
   shadow laws (r a multiple of 16, r + 288 <= alloc_ceiling, every byte of the struct addressable).
   The model premises are those of the old walk (a working branch 67b70ae1ec3
   proofs/libreac/fuzz_boxreg/lib/B/Prog/range_taken_c.v), weaker than boxreg_B2 and boxreg_B3: lowest_free_base
   meets them from boxreg_B1..B3 and its loop guard b + k <= fabric, reac_boxreg_declare from boxreg_inv and its
   pinned-base test base <= fabric - nch. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg lowest_free_base_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK0w YP01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame and ESTACK below it for the
   memory-checking runtime (it calls nothing but the error path). *)
Definition AB_range_takenP : Z := BASE + AF_range_taken.
Definition RANGE_TAKEN_STKB : Z := 16 + ESTACK.
Section h.
Variable B : asyms.
Definition tbrange_taken_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (b k : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B RANGE_TAKEN_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
((lowest_free_base_c.slice_meets bs b k /\ getr regs' 10 = w64 1) \/
 (~ lowest_free_base_c.slice_meets bs b k /\ getr regs' 10 = w64 0))).
Definition tbrange_taken_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r b k : Z) (bs : list byte),
afn_pre SEGS B RANGE_TAKEN_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 b -> getr regs 12 = w64 k ->
In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.bx_fabric bs <= 40 ->
(forall i, 0 <= i < Boxreg.bx_n bs ->
  0 <= Boxreg.bx_base bs i /\ 0 <= Boxreg.bx_nch bs i /\
  Boxreg.bx_base bs i + Boxreg.bx_nch bs i <= Boxreg.bx_fabric bs) ->
0 <= b -> 0 <= k -> b + k <= Boxreg.bx_fabric bs ->
SRr SEGS W (cfg_at SEGS AB_range_takenP regs mem md) (tbrange_taken_post regs ly S W mem md b k bs).
(* The walk. Section hypotheses: the allocator's laws (LAWS), and PALib (TL) for the shadow base that the code
   reads through the GOT word (object 1) and its .bss cell (object 12).
   rt_entry builds the symbolic state at 0x81d6c; the engine decides the r & 3 trap (0x81d78) from r's 16-byte
   alignment, and the shadow check of n (r + 280) leaves an obligation that obl_of_block discharges from the
   block's shadow law. rt_loop walks the loop at 0x81dd8 by induction on n - i, from a fresh state at each turn
   (rt_lentry); there the engine decides the traps i = 5 (0x81dd8), ~r < 56 i (0x81ddc) and base + nch overflow
   (0x81e14) from the facts of that state, and the b + k overflow trap (0x81e20) from t2 = 0, which the walk
   up to the loop head computes; the two shadow checks leave obligations as above. rt_step is the shared tail
   from 0x81e28. The epilogue at 0x81e64 continues the entry state after a stretch over the registers the loop
   writes (RT_CLOB). *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* the loop head (0x81dd8) and the join before the epilogue (0x81e64) *)
Definition RT_A : Z := 0x1e2c.
Definition RT_X : Z := 0x1eb8.
(* ---- helpers: the 32-bit fields of the registry struct, read byte by byte ---- *)
Lemma rt_bits_high : forall x i, 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof.
intros x i Hx Hi. apply Z.testbit_false; [lia|].
rewrite Z.div_small; [reflexivity|]. split; [lia|].
eapply Z.lt_le_trans; [exact (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma rt_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx.
assert (HO : forall i, 0 <= i < 64 -> Z.testbit 18446744073709551615 i = true).
{ intros i Hi. change 18446744073709551615 with (Z.ones 64). apply Z.ones_spec_low. lia. }
assert (HD : Z.lxor x 18446744073709551615 = Z.ldiff 18446744073709551615 x).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.le_gt_cases 64 i) as [H|H].
- rewrite (rt_bits_high x i Hx H), (rt_bits_high 18446744073709551615 i ltac:(lia) H). reflexivity.
- rewrite (HO i ltac:(lia)). destruct (Z.testbit x i); reflexivity. }
rewrite HD. symmetry. apply Z.sub_nocarry_ldiff.
apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
destruct (Z.le_gt_cases 64 i) as [H|H].
- rewrite (rt_bits_high x i Hx H). reflexivity.
- rewrite (HO i ltac:(lia)). apply andb_false_r.
Qed.
Lemma rt_land_ones : forall n, 0 <= n < 2 ^ 64 -> Z.land 18446744073709551615 n = n.
Proof.
intros n Hn. change 18446744073709551615 with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma rt_nth_firstn : forall (A : Type) (d : A) (l : list A) (n j : nat),
(j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A d l. induction l as [|x l IH]; intros n j Hj.
- rewrite firstn_nil. destruct j; reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma rt_nth_skipn : forall (A : Type) (d : A) (l : list A) (n j : nat),
nth j (skipn n l) d = nth (n + j) l d.
Proof.
intros A d l. induction l as [|x l IH]; intros n j.
- rewrite skipn_nil. rewrite (nth_overflow (@nil A) d) by (cbn; lia).
rewrite (nth_overflow (@nil A) d) by (cbn; lia). reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Lemma rt_nth_bsub : forall (bs : list byte) (off j : Z) (d : byte),
0 <= off -> 0 <= j < 4 ->
nth (Z.to_nat j) (Boxreg.bsub bs off 4) d = nth (Z.to_nat (off + j)) bs d.
Proof.
intros bs off j d Hoff Hj. unfold Boxreg.bsub.
rewrite (rt_nth_firstn byte d (skipn (Z.to_nat off) bs) (Z.to_nat 4) (Z.to_nat j)) by lia.
rewrite rt_nth_skipn. f_equal. lia.
Qed.
Lemma rt_mbyte : forall (W : world SEGS) (mem : word -> option byte) (a : Z) (c : byte),
aview SEGS (w_H W) mem a = Some (bv_unsigned c) -> mbyte SEGS (mrestrict (w_H W) mem) a = Some c.
Proof.
intros W mem a c H. cbv [aview] in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [c0|] eqn:Em; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma rt_vm4 : forall (W : world SEGS) (mem : word -> option byte) (r off : Z) (bs : list byte),
length bs = 288%nat -> 0 <= off -> off + 4 <= 288 -> 0 <= Boxreg.rd4 bs off ->
(forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) mem (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
val_mem SEGS (mrestrict (w_H W) mem) (r + off) 4 (Boxreg.rd4 bs off).
Proof.
intros W mem r off bs HL Hoff Hoff4 Hnn HV.
assert (HB : length (Boxreg.bsub bs off 4) = 4%nat).
{ rewrite (Boxreg.bsub_length bs off 4) by (rewrite ?HL; lia). reflexivity. }
pose proof (Boxreg.le4_range _ HB) as HR.
assert (Hval : Boxreg.rd4 bs off = bytes_le_to_Z (Boxreg.bsub bs off 4)).
{ revert Hnn HR. unfold Boxreg.rd4, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296.
generalize (bytes_le_to_Z (Boxreg.bsub bs off 4)) as u. intros u Hnn HR.
Z.div_mod_to_equations. lia. }
intros kk Hkk.
specialize (HV (off + Z.of_nat kk) ltac:(lia)).
apply rt_mbyte in HV.
replace (r + off + Z.of_nat kk) with (r + (off + Z.of_nat kk)) by lia.
rewrite HV. f_equal. rewrite Hval.
rewrite (le_byte_small (bytes_le_to_Z (Boxreg.bsub bs off 4)) 4%nat kk
  ltac:(change (8 * Z.of_nat 4) with 32; lia) ltac:(lia)).
rewrite <- (rt_nth_bsub bs off (Z.of_nat kk) (Z_to_bv 8 0) ltac:(lia) ltac:(lia)).
rewrite Nat2Z.id.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- (zb_of_bytes (Boxreg.bsub bs off 4) kk ltac:(lia)).
unfold HZ.zb. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma rt_keep_bytes : forall ly S (W : world SEGS) mem0 md0 memc mdc (STK sp0 r : Z) (bs : list byte),
ajournal SEGS B STK sp0 [] ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (r, 288) (ablocks B ly S) ->
(forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) mem0 (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) memc (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0))).
Proof.
intros ly S W mem0 md0 memc mdc STK sp0 r bs HJ Hin HV j Hj.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 r 288 j Hin Hin ltac:(change (req_size 288) with 288; lia)
  ltac:(intros X; exact (inFP_nil _ X))).
exact (HV j Hj).
Qed.
(* ---- the symbolic state at the entry ---- *)
Definition rt_Bx : sv := SOff 32 0.
Definition rt_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 32;
  YP09.mkRegion (Some 10%nat) 0 288 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))] ].
Definition rt_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, mkAF 0 40 0);
          (12%nat, mkAF 0 40 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 5 0) ] [] [].
Definition ss_rt : sstate := mkSS AF_range_taken sr_atoms rt_regions None rt_facts.
Definition rt_extra (n : Z) : list word := map (Z_to_bv 64) [SB; n].
Definition ERT (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (rt_extra n)).
Lemma rt_ew : forall (regs : bvmap 5 word) (n r b k : Z),
getr regs 10 = w64 r -> getr regs 11 = w64 b -> getr regs 12 = w64 k ->
ew (ERT regs n) 1 = getr regs 1 /\ bv_unsigned (ew (ERT regs n) 2) = spZ regs /\
ew (ERT regs n) 10 = Z_to_bv 64 r /\ ew (ERT regs n) 11 = Z_to_bv 64 b /\
ew (ERT regs n) 12 = Z_to_bv 64 k /\ ew (ERT regs n) 32 = Z_to_bv 64 SB /\
ew (ERT regs n) 33 = Z_to_bv 64 n.
Proof.
intros regs n r b k H10 H11 H12. unfold ERT, w64 in *.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
Qed.
Lemma rt_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r b k : Z) (bs : list byte),
afn_pre SEGS B RANGE_TAKEN_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 b -> getr regs 12 = w64 k ->
In (r, 288) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < 288 ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
0 <= Boxreg.bx_n bs <= 5 -> 0 <= b <= 40 -> 0 <= k <= 40 ->
st_ok_pi SEGS VAL (ERT regs (Boxreg.bx_n bs)) ss_rt
  (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_range_takenP) mem (seg_rom SEGS)))
/\ sh_ok SEGS rt_Bx [] (ERT regs (Boxreg.bx_n bs)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r b k bs HPRE H10 H11 H12 Hin HL HV Hbn Hb Hk.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RANGE_TAKEN_STKB = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r 288 HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size 288) with 288 in Hrceil, Hria, Hrpres.
pose proof (blk_off_imgP B ly S W mem md r 288 HAR Hin) as Hrimg.
change (req_size 288) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
destruct (rt_ew regs (Boxreg.bx_n bs) r b k H10 H11 H12) as (E1 & Usp & E10 & E11 & E12 & E32 & E33).
set (E := ERT regs (Boxreg.bx_n bs)) in *.
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (unfold E, ERT; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (unfold E, ERT; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx.
split; [| apply Forall_nil].
unfold ss_rt, AB_range_takenP. apply pa_entry_st_ok_full.
- unfold E, ERT. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rt_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 rt_Bx SB);
[cbn [sv_denot rt_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB 10%nat r E10) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (Boxreg.bx_n bs));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (8 * Z.of_N 4) with 32; lia | zside |].
apply (rt_vm4 W mem r 280 bs HL ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n in Hbn; lia) HV).
- apply pairwise_disjoint_of_extents.
unfold rt_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat r E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hr4096 Hrceil Hrimg HcellR HgcD HgotR C1 C3 WS Hstk0. clear. intros.
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [rt_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hr4096 Hrceil Hr16 Hal16 Hb Hk Hbn C1 C3 WS Hstk0. clear.
unfold SB, Boxreg.bx_n. intros.
repeat match goal with |- _ /\ _ => split end; try lia.
Qed.
(* ---- the symbolic state at the loop head ---- *)
Definition rt_lBx : sv := SOff 14 0.
Definition rt_lregions : smem :=
[ YP09.mkRegion (Some 10%nat) (-4) 4 0 0
    [YP09.mkChunk (-4) (CVal 4 (SOff 32 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0))] ].
Definition rt_lfacts : facts :=
mkFacts [ (10%nat, PTR 2); (11%nat, mkAF 0 40 0); (5%nat, mkAF 0 40 0); (13%nat, mkAF 1 5 0);
          (14%nat, mkAF SB SB 0); (15%nat, mkAF 0 4 0); (16%nat, mkAF 0 224 0);
          (17%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (28%nat, mkAF 1 5 0); (29%nat, mkAF 5 5 0);
          (32%nat, mkAF 0 40 0); (33%nat, mkAF 0 40 0) ] [] [].
Definition rt_lregs : list sv := sr_set (sr_set sr_atoms 6%bv (SOff 10 0)) 7%bv (SLit 0).
Definition ss_lrt : sstate := mkSS RT_A rt_lregs rt_lregions None rt_lfacts.
Definition rt_lextra (base nch : Z) : list word := map (Z_to_bv 64) [base; nch].
Definition ELRT (regs : bvmap 5 word) (base nch : Z) : env := Eimg (Ereg regs (rt_lextra base nch)).
Definition RT_CLOB : list (bv 5) := [6; 7; 10; 12; 15; 16; 30; 31]%bv.
Definition RT_KEPT : list (bv 5) :=
[1; 2; 3; 4; 5; 8; 9; 11; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29]%bv.
Lemma rt_clob_kept : forall rr : bv 5, reg_in rr RT_CLOB = false -> rr = 0%bv \/ In rr RT_KEPT.
Proof.
intros rr Hr. pose proof (all_regs_in rr) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin];
  [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma rt_lew : forall (regs : bvmap 5 word) (base nch q bq n sb i s56 a7 : Z),
getr regs 10 = w64 q -> getr regs 11 = w64 bq -> getr regs 5 = w64 sb ->
getr regs 13 = w64 n -> getr regs 14 = w64 SB -> getr regs 15 = w64 i ->
getr regs 16 = w64 s56 -> getr regs 17 = w64 a7 -> getr regs 28 = w64 n -> getr regs 29 = w64 5 ->
ew (ELRT regs base nch) 10 = Z_to_bv 64 q /\ ew (ELRT regs base nch) 11 = Z_to_bv 64 bq /\
ew (ELRT regs base nch) 5 = Z_to_bv 64 sb /\ ew (ELRT regs base nch) 13 = Z_to_bv 64 n /\
ew (ELRT regs base nch) 14 = Z_to_bv 64 SB /\ ew (ELRT regs base nch) 15 = Z_to_bv 64 i /\
ew (ELRT regs base nch) 16 = Z_to_bv 64 s56 /\ ew (ELRT regs base nch) 17 = Z_to_bv 64 a7 /\
ew (ELRT regs base nch) 28 = Z_to_bv 64 n /\ ew (ELRT regs base nch) 29 = Z_to_bv 64 5 /\
ew (ELRT regs base nch) 32 = Z_to_bv 64 base /\ ew (ELRT regs base nch) 33 = Z_to_bv 64 nch.
Proof.
intros regs base nch q bq n sb i s56 a7 H10 H11 H5 H13 H14 H15 H16 H17 H28 H29.
unfold ELRT, w64 in *.
repeat split;
  first [ rewrite Eimg_low by (unfold A_TEXT; lia);
          first [ rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5
                | rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10
                | rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11
                | rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13
                | rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14
                | rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15
                | rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16
                | rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17
                | rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact H28
                | rewrite (ew_Ereg_nat regs _ 29 29%bv eq_refl); exact H29
                | exact (ew_Ereg_extra regs _ 0)
                | exact (ew_Ereg_extra regs _ 1) ] ].
Qed.
Lemma rt_lentry : forall ly S (W : world SEGS) memc mdc (regs : bvmap 5 word) (r b k i : Z) (bs : list byte),
AR SEGS B ly S W memc mdc ->
In (r, 288) (ablocks B ly S) -> length bs = 288%nat ->
(forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) memc (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
0 <= i < Boxreg.bx_n bs -> 0 <= Boxreg.bx_n bs <= 5 ->
0 <= b -> 0 <= k -> b + k <= 40 ->
0 <= Boxreg.bx_base bs i -> 0 <= Boxreg.bx_nch bs i ->
Boxreg.bx_base bs i + Boxreg.bx_nch bs i <= 40 ->
getr regs 10 = w64 (r + 12 + 56 * i) -> getr regs 6 = w64 (r + 12 + 56 * i) ->
getr regs 11 = w64 b -> getr regs 5 = w64 (b + k) -> getr regs 7 = w64 0 ->
getr regs 13 = w64 (Boxreg.bx_n bs) -> getr regs 28 = w64 (Boxreg.bx_n bs) ->
getr regs 14 = w64 SB -> getr regs 15 = w64 i -> getr regs 16 = w64 (56 * i) ->
getr regs 17 = w64 (18446744073709551615 - r) -> getr regs 29 = w64 5 ->
st_ok_pi SEGS VAL (ELRT regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) ss_lrt
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RT_A)) memc (seg_rom SEGS)))
/\ sh_ok SEGS rt_lBx [] (ELRT regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) (mrestrict (w_H W) memc).
Proof.
intros ly S W memc mdc regs r b k i bs HAR Hin HL HV Hi Hbn Hb Hk Hbk Hbase Hnch Hrow
H10 H6 H11 H5 H7 H13 H28 H14 H15 H16 H17 H29.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W memc mdc r 288 HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size 288) with 288 in Hrceil, Hria, Hrpres.
destruct (rt_lew regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i) (r + 12 + 56 * i) b
  (Boxreg.bx_n bs) (b + k) i (56 * i) (18446744073709551615 - r)
  H10 H11 H5 H13 H14 H15 H16 H17 H28 H29)
as (L10 & L11 & L5 & L13 & L14 & L15 & L16 & L17 & L28 & L29 & L32 & L33).
set (E := ELRT regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) in *.
assert (HR : 0 <= 18446744073709551615 - r < 2 ^ 64) by lia.
rewrite restrict_mkst_fx.
split; [| apply Forall_nil].
unfold ss_lrt. apply pa_entry_st_ok_full.
- unfold rt_lregs. apply regs_ok_pin; [apply regs_ok_pin|intros X; discriminate X|].
+ unfold E, ELRT. apply regs_ok_Eimg_Ereg.
+ intros X; discriminate X.
+ cbn [sv_denot]. rewrite L10, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64 in H6. exact H6.
+ cbn [sv_denot]. unfold w64 in H7. exact H7.
- vm_compute. reflexivity.
- unfold rt_lregions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite L10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
+ apply (chunk_ok_val SEGS E _ (r + 12 + 56 * i) (-4) 4 (SOff 32 0) (Boxreg.bx_base bs i));
[cbn [sv_denot]; rewrite L32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (8 * Z.of_N 4) with 32; lia | zside |].
replace (r + 12 + 56 * i + -4) with (r + (56 * i + 8)) by lia.
apply (rt_vm4 W memc r (56 * i + 8) bs HL ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_base in Hbase; lia) HV).
+ apply (chunk_ok_val SEGS E _ (r + 12 + 56 * i) 0 4 (SOff 33 0) (Boxreg.bx_nch bs i));
[cbn [sv_denot]; rewrite L33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (8 * Z.of_N 4) with 32; lia | zside |].
replace (r + 12 + 56 * i + 0) with (r + (56 * i + 12)) by lia.
apply (rt_vm4 W memc r (56 * i + 12) bs HL ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_nch in Hnch; lia) HV).
- unfold rt_lregions. cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
cbn [rt_lfacts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite L5, L10, L11, L13, L14, L15, L16, L17, L28, L29, L32, L33,
  !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hr4096 Hrceil Hr16 Hi Hbn Hb Hk Hbk Hbase Hnch Hrow C1 C3. clear.
unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; try lia; try (Z.div_mod_to_equations; lia).
Qed.
(* ---- the loop 0x81dd8 .. 0x81e38, by induction on n - i ---- *)
Definition rt_loop_post (W : world SEGS) ly S (sp0 : Z) mem0 md0 (regs : bvmap 5 word)
  (b k : Z) (bs : list byte) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' (j : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + RT_X)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp0 [] ly S W mem0 md0 [] ly S W mem' md' 0 /\
getr regs' 15 = w64 j /\ getr regs' 13 = w64 (Boxreg.bx_n bs) /\
0 <= j <= Boxreg.bx_n bs /\
(j < Boxreg.bx_n bs -> lowest_free_base_c.slice_meets bs b k) /\
(j = Boxreg.bx_n bs -> ~ lowest_free_base_c.slice_meets bs b k) /\
(forall rr : bv 5, reg_in rr RT_CLOB = false -> getr regs' rr = getr regs rr).
Local Ltac rt_obl E q r ly S W memc mdc HAR Hin HUB L10 :=
cbn [ms_mem mkst];
first [ rewrite (U_atom_off E 10 q (-4) L10 ltac:(lia) ltac:(lia))
      | rewrite (U_atom_off E 10 q 0 L10 ltac:(lia) ltac:(lia)) ];
eapply (obl_of_block SEGS B LAWS ly S W memc mdc E rt_lBx _ 4 r 288 HAR Hin);
[exact HUB | lia | change (req_size 288) with 288; lia].
Lemma rt_den_atom : forall (Ex : env) (m : nat) (v : Z),
ew Ex m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot Ex (SOff m 0) = Z_to_bv 64 v.
Proof.
intros Ex m v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
Qed.
Lemma rt_den_add : forall (Ex : env) (a c : sv) (x y : Z),
sv_denot Ex a = Z_to_bv 64 x -> sv_denot Ex c = Z_to_bv 64 y ->
sv_denot Ex (SAlu ALU_ADD a c) = Z_to_bv 64 (x + y).
Proof. intros Ex a c x y Ha Hc. cbn [sv_denot]. rewrite Ha, Hc. apply alu64_add_lit. Qed.
Lemma rt_br_ge : forall (Ex : env) (a c : sv) (x y : Z),
sv_denot Ex a = Z_to_bv 64 x -> sv_denot Ex c = Z_to_bv 64 y ->
- 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot Ex a) (sv_denot Ex c) = negb (x <? y).
Proof.
intros Ex a c x y Ha Hc Hx Hy. cbn [branch_taken]. rewrite Ha, Hc.
rewrite (Boxreg.lts_lit x y ltac:(lia) ltac:(lia)). reflexivity.
Qed.
Lemma rt_br_lt : forall (Ex : env) (a c : sv) (x y : Z),
sv_denot Ex a = Z_to_bv 64 x -> sv_denot Ex c = Z_to_bv 64 y ->
- 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot Ex a) (sv_denot Ex c) = (x <? y).
Proof.
intros Ex a c x y Ha Hc Hx Hy. cbn [branch_taken]. rewrite Ha, Hc.
rewrite (Boxreg.lts_lit x y ltac:(lia) ltac:(lia)). reflexivity.
Qed.
(* 0x81e28, the join of the two "row i does not meet" branches *)
Definition RT_B : Z := 0x1e7c.
Definition rt_loop_stmt (d : nat) : Prop :=
forall (i : Z) (W : world SEGS) ly S (sp0 : Z) mem0 md0 memc mdc
  (regs : bvmap 5 word) (r b k : Z) (bs : list byte),
d = Z.to_nat (Boxreg.bx_n bs - i) ->
ajournal SEGS B 0 sp0 [] ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (r, 288) (ablocks B ly S) -> length bs = 288%nat ->
(forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) mem0 (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
0 <= Boxreg.bx_n bs <= 5 -> Boxreg.bx_fabric bs <= 40 ->
(forall j, 0 <= j < Boxreg.bx_n bs ->
  0 <= Boxreg.bx_base bs j /\ 0 <= Boxreg.bx_nch bs j /\
  Boxreg.bx_base bs j + Boxreg.bx_nch bs j <= Boxreg.bx_fabric bs) ->
0 <= b -> 0 <= k -> b + k <= Boxreg.bx_fabric bs ->
0 <= i < Boxreg.bx_n bs ->
(forall j, 0 <= j < i -> ~ Boxreg.meets b k (Boxreg.bx_base bs j) (Boxreg.bx_nch bs j)) ->
getr regs 10 = w64 (r + 12 + 56 * i) -> getr regs 6 = w64 (r + 12 + 56 * i) ->
getr regs 11 = w64 b -> getr regs 5 = w64 (b + k) -> getr regs 7 = w64 0 ->
getr regs 13 = w64 (Boxreg.bx_n bs) -> getr regs 28 = w64 (Boxreg.bx_n bs) ->
getr regs 14 = w64 SB -> getr regs 15 = w64 i -> getr regs 16 = w64 (56 * i) ->
getr regs 17 = w64 (18446744073709551615 - r) -> getr regs 29 = w64 5 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + RT_A)) memc (seg_rom SEGS)) mdc)
  (rt_loop_post W ly S sp0 mem0 md0 regs b k bs).
Definition rt_bfacts : facts := mkFacts [ (15%nat, mkAF 0 4 0); (28%nat, mkAF 1 5 0) ] [] [].
Definition ss_brt : sstate := mkSS RT_B sr_atoms [] None rt_bfacts.
Definition EBRT (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition RT_KEPT2 : list (bv 5) :=
[1; 2; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma rt_bew : forall (regs : bvmap 5 word) (m : nat) (rr : bv 5) (v : Z),
Z.of_nat m = bv_unsigned rr -> (m < 32)%nat -> getr regs rr = w64 v -> ew (EBRT regs) m = Z_to_bv 64 v.
Proof.
intros regs m rr v Hm Hlt H. unfold EBRT, w64 in *.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ m rr Hm). exact H.
Qed.
Lemma rt_bentry : forall (W : world SEGS) memc (regs : bvmap 5 word) (n i : Z),
getr regs 15 = w64 i -> getr regs 28 = w64 n -> 0 <= i <= 4 -> 1 <= n <= 5 ->
st_ok_pi SEGS VAL (EBRT regs) ss_brt
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RT_B)) memc (seg_rom SEGS)))
/\ sh_ok SEGS rt_lBx [] (EBRT regs) (mrestrict (w_H W) memc).
Proof.
intros W memc regs n i H15 H28 Hi Hn.
pose proof (rt_bew regs 15 15%bv i eq_refl ltac:(lia) H15) as B15.
pose proof (rt_bew regs 28 28%bv n eq_refl ltac:(lia) H28) as B28.
rewrite restrict_mkst_fx. split; [|apply Forall_nil].
unfold ss_brt. apply pa_entry_st_ok_full.
- unfold EBRT. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; [exact I | exact I]].
cbn [rt_bfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite B15, B28, !unsigned_lit_small by lia.
rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
Qed.
Lemma rt_step : forall (d : nat) (i : Z) (W : world SEGS) ly S (sp0 : Z) mem0 md0 memc mdc
  (regs regs0 : bvmap 5 word) (r b k : Z) (bs : list byte),
rt_loop_stmt d ->
d = Z.to_nat (Boxreg.bx_n bs - (i + 1)) ->
ajournal SEGS B 0 sp0 [] ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (r, 288) (ablocks B ly S) -> length bs = 288%nat ->
(forall j, 0 <= j < 288 ->
  aview SEGS (w_H W) mem0 (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
0 <= Boxreg.bx_n bs <= 5 -> Boxreg.bx_fabric bs <= 40 ->
(forall j, 0 <= j < Boxreg.bx_n bs ->
  0 <= Boxreg.bx_base bs j /\ 0 <= Boxreg.bx_nch bs j /\
  Boxreg.bx_base bs j + Boxreg.bx_nch bs j <= Boxreg.bx_fabric bs) ->
0 <= b -> 0 <= k -> b + k <= Boxreg.bx_fabric bs ->
0 <= i < Boxreg.bx_n bs ->
(forall j, 0 <= j < i -> ~ Boxreg.meets b k (Boxreg.bx_base bs j) (Boxreg.bx_nch bs j)) ->
~ Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i) ->
(forall rr : bv 5, reg_in rr RT_CLOB = false -> getr regs rr = getr regs0 rr) ->
getr regs 10 = w64 (r + 12 + 56 * i) -> getr regs 6 = w64 (r + 12 + 56 * i) ->
getr regs 11 = w64 b -> getr regs 5 = w64 (b + k) -> getr regs 7 = w64 0 ->
getr regs 13 = w64 (Boxreg.bx_n bs) -> getr regs 28 = w64 (Boxreg.bx_n bs) ->
getr regs 14 = w64 SB -> getr regs 15 = w64 i -> getr regs 16 = w64 (56 * i) ->
getr regs 17 = w64 (18446744073709551615 - r) -> getr regs 29 = w64 5 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + RT_B)) memc (seg_rom SEGS)) mdc)
  (rt_loop_post W ly S sp0 mem0 md0 regs0 b k bs).
Proof.
intros d i W ly S sp0 mem0 md0 memc mdc regs regs0 r b k bs
IHyp Hd HJ Hin HL HV Hbn Hfab HROW Hb Hk Hbk Hi HINV HNM HKK
H10 H6 H11 H5 H7 H13 H28 H14 H15 H16 H17 H29.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
destruct (rt_bentry W memc regs (Boxreg.bx_n bs) i H15 H28 ltac:(lia) ltac:(lia)) as [HS SHOK].
destruct (al_blocks _ _ LAWS ly S W memc mdc r 288 HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size 288) with 288 in Hrceil, Hria, Hrpres.
pose proof (rt_bew regs 6 6%bv (r + 12 + 56 * i) eq_refl ltac:(lia) H6) as B6.
pose proof (rt_bew regs 10 10%bv (r + 12 + 56 * i) eq_refl ltac:(lia) H10) as B10.
pose proof (rt_bew regs 15 15%bv i eq_refl ltac:(lia) H15) as B15.
pose proof (rt_bew regs 16 16%bv (56 * i) eq_refl ltac:(lia) H16) as B16.
pose proof (rt_bew regs 28 28%bv (Boxreg.bx_n bs) eq_refl ltac:(lia) H28) as B28.
set (E := EBRT regs) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EBRT; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
  by (split; [intros m Hm; unfold E, EBRT; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (N15 : ew Ex 15 = Z_to_bv 64 i) by (rewrite ?ew_ewset_other by lia; exact B15);
assert (N28 : ew Ex 28 = Z_to_bv 64 (Boxreg.bx_n bs))
  by (rewrite ?ew_ewset_other by lia; exact B28)
end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <> i + 1 : one more turn of the loop *)
rewrite branch_ne_U, (U_atom _ 28 (Boxreg.bx_n bs) N28 ltac:(lia)),
        (U_atom_off _ 15 i 1 N15 ltac:(lia) ltac:(lia)) in Hc.
apply negb_true_iff, Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_A.
{ awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (@nil word) RT_KEPT2 HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) P10. prreg HS (6%bv : bv 5) P6.
prreg HS (15%bv : bv 5) P15. prreg HS (16%bv : bv 5) P16.
rewrite B10 in P10. rewrite B6 in P6. rewrite B15 in P15. rewrite B16 in P16.
rewrite !unsigned_lit_small in P10, P6, P15, P16 by lia.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
+ eapply (IHyp (i + 1) W ly S sp0 mem0 md0 _ _ _ r b k bs);
  [ lia | exact HJ | exact Hin | exact HL | exact HV | lia | exact Hfab | exact HROW
  | lia | lia | lia | lia
  | intros jj Hjj; destruct (Z.eq_dec jj i) as [->|Hne]; [ exact HNM | apply HINV; lia ]
  | cbn [ms_regs]; rewrite P10; unfold w64; f_equal; lia
  | cbn [ms_regs]; rewrite P6; unfold w64; f_equal; lia
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; rewrite P15; unfold w64; f_equal; lia
  | cbn [ms_regs]; rewrite P16; unfold w64; f_equal; lia
  | cbn [ms_regs]; kreg HK
  | cbn [ms_regs]; kreg HK ].
+ cbv beta. intros W' c' _ (-> & regs' & mem' & md' & jj & -> & HJ' & Q15 & Q13 & Qb & QT & QF & QK).
split; [reflexivity|].
exists regs', mem', md', jj.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact Q15|]. split; [exact Q13|].
split; [lia|]. split; [exact QT|]. split; [exact QF|].
intros rr Hrr. rewrite (QK rr Hrr). rewrite <- (HKK rr Hrr).
destruct (rt_clob_kept rr Hrr) as [-> | Hin'].
{ rewrite !getr_zero. reflexivity. }
cbn [ms_regs]. apply HK. revert Hin'. cbv [RT_KEPT RT_KEPT2 In]. tauto.
- (* n = i + 1 : the scan is over and no row meets *)
rewrite branch_ne_U, (U_atom _ 28 (Boxreg.bx_n bs) N28 ltac:(lia)),
        (U_atom_off _ 15 i 1 N15 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_X.
{ awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (@nil word) RT_KEPT2 HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (15%bv : bv 5) P15.
rewrite B15 in P15. rewrite !unsigned_lit_small in P15 by lia.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?dd = _ /\ _ =>
  exists rg, m, dd, (i + 1) end.
split; [unfold RT_X; reflexivity|].
split; [exact HJ|].
split; [cbn [ms_regs]; rewrite P15; unfold w64; f_equal; lia|].
split; [cbn [ms_regs]; rewrite (HK 13%bv ltac:(cbv; tauto)); exact H13|].
split; [lia|].
split; [intros Hlt; lia|].
split; [intros _ (jj & Hjj & Hmm); destruct (Z.eq_dec jj i) as [->|Hne];
        [ exact (HNM Hmm) | exact (HINV jj ltac:(lia) Hmm) ]|].
intros rr Hrr. rewrite <- (HKK rr Hrr).
destruct (rt_clob_kept rr Hrr) as [-> | Hin'].
{ rewrite !getr_zero. reflexivity. }
cbn [ms_regs]. apply HK. revert Hin'. cbv [RT_KEPT RT_KEPT2 In]. tauto.
Qed.
Lemma rt_loop : forall d : nat, rt_loop_stmt d.
Proof.
induction d as [|d IH]; unfold rt_loop_stmt in *;
intros i W ly S sp0 mem0 md0 memc mdc regs r b k bs
Hd HJ Hin HL HV Hbn Hfab HROW Hb Hk Hbk Hi HINV H10 H6 H11 H5 H7 H13 H28 H14 H15 H16 H17 H29;
[lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
destruct (HROW i ltac:(lia)) as (Hbase & Hnch & Hrow).
destruct (al_blocks _ _ LAWS ly S W memc mdc r 288 HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size 288) with 288 in Hrceil, Hria, Hrpres.
pose proof (rt_keep_bytes ly S W mem0 md0 memc mdc 0 sp0 r bs HJ Hin HV) as HVc.
destruct (rt_lentry ly S W memc mdc regs r b k i bs HAR Hin HL HVc Hi Hbn Hb Hk ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) H10 H6 H11 H5 H7 H13 H28 H14 H15 H16 H17 H29) as [HS SHOK].
destruct (rt_lew regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i) (r + 12 + 56 * i) b
  (Boxreg.bx_n bs) (b + k) i (56 * i) (18446744073709551615 - r)
  H10 H11 H5 H13 H14 H15 H16 H17 H28 H29)
as (L10 & L11 & L5 & L13 & L14 & L15 & L16 & L17 & L28 & L29 & L32 & L33).
set (E := ELRT regs (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ELRT; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rt_lextra (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))) E)
  by (split; [intros m Hm; unfold E, ELRT; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HUB : U E rt_lBx = SHADOW_OFF)
  by (unfold rt_lBx; rewrite (U_atom E 14 SB L14) by (unfold SB; lia); reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan.
{ rt_obl E (r + 12 + 56 * i) r ly S W memc mdc HAR Hin HUB L10. }
{ rt_obl E (r + 12 + 56 * i) r ly S W memc mdc HAR Hin HUB L10. }
{ awr_ok_tac. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (M5 : ew Ex 5 = Z_to_bv 64 (b + k)) by (rewrite ?ew_ewset_other by lia; exact L5);
assert (M11 : ew Ex 11 = Z_to_bv 64 b) by (rewrite ?ew_ewset_other by lia; exact L11);
assert (M13 : ew Ex 13 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite ?ew_ewset_other by lia; exact L13);
assert (M15 : ew Ex 15 = Z_to_bv 64 i) by (rewrite ?ew_ewset_other by lia; exact L15);
assert (M28 : ew Ex 28 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite ?ew_ewset_other by lia; exact L28);
assert (M32 : ew Ex 32 = Z_to_bv 64 (Boxreg.bx_base bs i)) by (rewrite ?ew_ewset_other by lia; exact L32);
assert (M33 : ew Ex 33 = Z_to_bv 64 (Boxreg.bx_nch bs i)) by (rewrite ?ew_ewset_other by lia; exact L33);
assert (D11 : sv_denot Ex (SOff 11 0) = Z_to_bv 64 b) by (apply rt_den_atom; [exact M11 | lia]);
assert (D5 : sv_denot Ex (SOff 5 0) = Z_to_bv 64 (b + k)) by (apply rt_den_atom; [exact M5 | lia]);
assert (D32 : sv_denot Ex (SOff 32 0) = Z_to_bv 64 (Boxreg.bx_base bs i))
  by (apply rt_den_atom; [exact M32 | lia]);
assert (D33 : sv_denot Ex (SOff 33 0) = Z_to_bv 64 (Boxreg.bx_nch bs i))
  by (apply rt_den_atom; [exact M33 | lia]);
assert (DSUM : sv_denot Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))
               = Z_to_bv 64 (Boxreg.bx_base bs i + Boxreg.bx_nch bs i))
  by (exact (rt_den_add Ex _ _ _ _ D32 D33))
end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* b >= base i + nch i : row i does not meet *)
rewrite (rt_br_ge _ _ _ b (Boxreg.bx_base bs i + Boxreg.bx_nch bs i) D11 DSUM ltac:(lia) ltac:(lia)) in Hc.
apply negb_true_iff, Z.ltb_ge in Hc.
assert (HNM : ~ Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))
  by (unfold Boxreg.meets; lia).
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_B.
{ awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rt_lextra (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))
  RT_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) P10. prreg HS (6%bv : bv 5) P6. prreg HS (7%bv : bv 5) P7.
prreg HS (15%bv : bv 5) P15. prreg HS (16%bv : bv 5) P16.
rewrite ?ew_ewset_other in P10, P6, P15, P16 by lia.
rewrite L10 in P10, P6. rewrite L15 in P15. rewrite L16 in P16.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (rt_step d i);
[ exact IH | lia | exact HJ | exact Hin | exact HL | exact HV | lia | exact Hfab | exact HROW
| lia | lia | lia | lia | exact HINV | exact HNM
| intros rr Hrr; destruct (rt_clob_kept rr Hrr) as [-> | Hin'];
  [ rewrite !getr_zero; reflexivity | cbn [ms_regs]; apply HK; exact Hin' ]
| cbn [ms_regs]; rewrite P10; unfold w64; reflexivity
| cbn [ms_regs]; rewrite P6; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK
| cbn [ms_regs]; rewrite P7; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK
| cbn [ms_regs]; rewrite P15; unfold w64; reflexivity
| cbn [ms_regs]; rewrite P16; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK ].
- (* b < base i + nch i *)
rewrite (rt_br_ge _ _ _ b (Boxreg.bx_base bs i + Boxreg.bx_nch bs i) D11 DSUM ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.ltb_lt in Hc.
rename Hc into HM1.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
psrr_branch_tok RUN BR HS SHOK Bspan.
+ (* base i < b + k : row i meets *)
rewrite (rt_br_lt _ _ _ (Boxreg.bx_base bs i) (b + k) D32 D5 ltac:(lia) ltac:(lia)) in Hc.
apply Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_X.
{ awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rt_lextra (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))
  RT_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
rewrite ?ew_ewset_other in Q15, Q13 by lia. rewrite L15 in Q15. rewrite L13 in Q13.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d, i end.
split; [unfold RT_X; reflexivity|].
split; [exact HJ|].
split; [cbn [ms_regs]; rewrite Q15; unfold w64; reflexivity|].
split; [cbn [ms_regs]; rewrite Q13; unfold w64; reflexivity|].
split; [lia|].
split; [intros _; exists i; split; [lia | unfold Boxreg.meets; lia]|].
split; [intros Heq; lia|].
intros rr Hrr. cbn [ms_regs]. destruct (rt_clob_kept rr Hrr) as [-> | Hin'].
{ rewrite !getr_zero. reflexivity. }
apply HK. exact Hin'.
+ (* base i >= b + k : row i does not meet *)
rewrite (rt_br_lt _ _ _ (Boxreg.bx_base bs i) (b + k) D32 D5 ltac:(lia) ltac:(lia)) in Hc.
apply Z.ltb_ge in Hc.
assert (HNM : ~ Boxreg.meets b k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))
  by (unfold Boxreg.meets; lia).
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_B.
{ awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rt_lextra (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i))
  RT_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) P10. prreg HS (6%bv : bv 5) P6. prreg HS (7%bv : bv 5) P7.
prreg HS (15%bv : bv 5) P15. prreg HS (16%bv : bv 5) P16.
rewrite ?ew_ewset_other in P10, P6, P15, P16 by lia.
rewrite L10 in P10, P6. rewrite L15 in P15. rewrite L16 in P16.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (rt_step d i);
[ exact IH | lia | exact HJ | exact Hin | exact HL | exact HV | lia | exact Hfab | exact HROW
| lia | lia | lia | lia | exact HINV | exact HNM
| intros rr Hrr; destruct (rt_clob_kept rr Hrr) as [-> | Hin'];
  [ rewrite !getr_zero; reflexivity | cbn [ms_regs]; apply HK; exact Hin' ]
| cbn [ms_regs]; rewrite P10; unfold w64; reflexivity
| cbn [ms_regs]; rewrite P6; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK
| cbn [ms_regs]; rewrite P7; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK
| cbn [ms_regs]; rewrite P15; unfold w64; reflexivity
| cbn [ms_regs]; rewrite P16; unfold w64; reflexivity
| cbn [ms_regs]; kreg HK | cbn [ms_regs]; kreg HK ].
Qed.
Lemma rt_swrap_small : forall x, 0 <= x < 2 ^ 63 -> bv_swrap 64 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.
Lemma rt_den_slt : forall (Ex : env) (a c : sv) (x y : Z),
sv_denot Ex a = Z_to_bv 64 x -> sv_denot Ex c = Z_to_bv 64 y ->
0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
sv_denot Ex (SAlu ALU_SLT a c) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof.
intros Ex a c x y Ha Hc Hx Hy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. unfold U. rewrite Ha, Hc, !unsigned_lit_small by lia.
rewrite !rt_swrap_small by lia. apply zcanon_id. unfold M64. destruct (x <? y); lia.
Qed.
Lemma rt_alu_slt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
alu64 ALU_SLT (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof.
intros x y Hx Hy.
exact (rt_den_slt (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])) (SLit x) (SLit y) x y eq_refl eq_refl Hx Hy).
Qed.
Lemma rt_alu_xor_self : forall v : word, alu64 ALU_XOR v v = Z_to_bv 64 0.
Proof.
intros v. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite Z.lxor_nilpotent.
rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma rt_alu_sltu00 : alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma rt_alu_not : forall x, 0 <= x < 2 ^ 64 ->
alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (18446744073709551615 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite rt_lxor_ones by lia. reflexivity.
Qed.
Lemma rt_alu_sub_lit : forall x y, alu64 ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
intros x y. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Zminus_mod x y). reflexivity.
Qed.
Lemma rt_alu_and_m1 : forall n, 0 <= n < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (0 - 1)) (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof.
intros n Hn. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change ((0 - 1) mod 2 ^ 64) with 18446744073709551615. rewrite (Z.mod_small n) by lia.
rewrite rt_land_ones by lia. apply Z.mod_small. lia.
Qed.
Theorem pbb_range_taken : tbrange_taken_spec.
Proof.
unfold tbrange_taken_spec.
intros ly S W regs mem md ch r b k bs HPRE H10 H11 H12 Hin HL HV HB1 HFab HROW Hb Hk Hbk.
unfold BoxBReacBoxregInit.REG_SIZEB in Hin, HV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RANGE_TAKEN_STKB = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r 288 HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size 288) with 288 in Hrceil, Hria, Hrpres.
assert (Hbn : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
destruct (rt_entry ly S W regs mem md ch r b k bs HPRE H10 H11 H12 Hin HL HV Hbn
  ltac:(lia) ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B RANGE_TAKEN_STKB [] ly S W regs mem md ch HPRE) as HJ.
destruct (rt_ew regs (Boxreg.bx_n bs) r b k H10 H11 H12) as (E1 & Usp & E10 & E11 & E12 & E32 & E33).
set (E := ERT regs (Boxreg.bx_n bs)) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ERT; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rt_extra (Boxreg.bx_n bs))) E)
  by (split; [intros m Hm; unfold E, ERT; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HUB : U E rt_Bx = SHADOW_OFF)
  by (unfold rt_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
unfold cfg_at. change (w64 AB_range_takenP) with (Z_to_bv 64 AB_range_takenP).
unfold AB_range_takenP.
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_A.
{ cbn [ms_mem mkst]. rewrite (U_atom_off E 10 r 280 E10 ltac:(lia) ltac:(lia)).
eapply (obl_of_block SEGS B LAWS ly S W mem md E rt_Bx _ 4 r 288 HAR Hin);
[exact HUB | lia | change (req_size 288) with 288; lia]. }
{ awr_ok_tac; exact Usp. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (M33 : ew Ex 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite ?ew_ewset_other by lia; exact E33);
assert (D33 : sv_denot Ex (SOff 33 0) = Z_to_bv 64 (Boxreg.bx_n bs))
  by (apply rt_den_atom; [exact M33 | lia]);
assert (D0 : sv_denot Ex (SLit 0) = Z_to_bv 64 0) by reflexivity
end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <= 0 : the registry has no row, the answer is 0 *)
rewrite (rt_br_ge _ _ _ 0 (Boxreg.bx_n bs) D0 D33 ltac:(lia) ltac:(lia)) in Hc.
apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; rewrite ?ew_ewset_other by lia; exact Usp. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra.
rewrite E33, rt_alu_slt in Ra0 by lia.
rewrite E1 in Rra.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tbrange_taken_post, apost_base.
exists ly, S. eexists. eexists. eexists.
split; [cbn [ms_regs]; rewrite Rra, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rt_extra (Boxreg.bx_n bs)) HS);
        [env_agree_chain HAE | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
right. split.
{ intros (jj & Hjj & _). lia. }
cbn [ms_regs]. rewrite Ra0.
replace (0 <? Boxreg.bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
- (* n >= 1 : walk the loop *)
rewrite (rt_br_ge _ _ _ 0 (Boxreg.bx_n bs) D0 D33 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan RT_A.
{ awr_ok_tac; rewrite ?ew_ewset_other by lia; exact Usp. }
(* at the loop head 0x81dd8: the register values the loop lemma needs *)
prreg HS (5%bv : bv 5) A5. prreg HS (6%bv : bv 5) A6. prreg HS (7%bv : bv 5) A7.
prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11. prreg HS (13%bv : bv 5) A13.
prreg HS (14%bv : bv 5) A14. prreg HS (15%bv : bv 5) A15. prreg HS (16%bv : bv 5) A16.
prreg HS (17%bv : bv 5) A17. prreg HS (28%bv : bv 5) A28. prreg HS (29%bv : bv 5) A29.
rewrite E11, E12, alu64_add_lit in A5.
rewrite E10, unsigned_lit_small in A6 by lia.
rewrite rt_alu_xor_self, rt_alu_sltu00 in A7.
rewrite E10, unsigned_lit_small in A10 by lia.
rewrite E11 in A11. rewrite E33 in A13. rewrite E32 in A14.
rewrite E10, rt_alu_not in A17 by lia.
rewrite E33, rt_alu_slt in A28 by lia.
replace (0 <? Boxreg.bx_n bs) with true in A28 by (symmetry; apply Z.ltb_lt; lia).
change (if true then 1 else 0) with 1 in A28.
rewrite rt_alu_sub_lit, rt_alu_and_m1 in A28 by lia.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by lia; exact Usp)
end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?memX _) ?mdX) _ =>
  pose proof (rt_keep_bytes ly S W mem md memX mdX RANGE_TAKEN_STKB (spZ regs) r bs HJ Hin HV) as HV2;
  pose proof (ajournal_sub_init SEGS B RANGE_TAKEN_STKB (spZ regs) [] ly S W mem md [] ly S W
     memX mdX 0 0 (spZ regs - 16) [] (-16) HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
     ltac:(rewrite WS; lia)) as HJL
end.
pose proof (rt_loop (Z.to_nat (Boxreg.bx_n bs - 0))) as RTL. unfold rt_loop_stmt in RTL.
eapply SRr_bind.
{ eapply (RTL 0 W ly S (spZ regs - 16) _ _ _ _ _ r b k bs);
  [ reflexivity | exact HJL | exact Hin | exact HL | exact HV2 | exact Hbn | exact HFab | exact HROW
  | lia | lia | lia | lia | intros jj Hjj; lia
  | cbn [ms_regs]; rewrite A10; unfold w64; f_equal; lia
  | cbn [ms_regs]; rewrite A6; unfold w64; f_equal; lia
  | cbn [ms_regs]; rewrite A11; reflexivity
  | cbn [ms_regs]; rewrite A5; reflexivity
  | cbn [ms_regs]; rewrite A7; reflexivity
  | cbn [ms_regs]; rewrite A13; reflexivity
  | cbn [ms_regs]; rewrite A28; reflexivity
  | cbn [ms_regs]; rewrite A14; reflexivity
  | cbn [ms_regs]; rewrite A15; reflexivity
  | cbn [ms_regs]; rewrite A16; reflexivity
  | cbn [ms_regs]; rewrite A17; reflexivity
  | cbn [ms_regs]; rewrite A29; reflexivity ]. }
cbv beta. intros W3 c3 _ (-> & regsL & memL & mdL & j & -> & HJL3 & Hj15 & Hj13 & Hjb & HjT & HjF & HjK).
(* back at 0x81e64: the main journal, then the symbolic state with the clobbered registers havocked *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msX) _ 0 0 (spZ regs - 16)
    [] [] ly S W memL mdL 0 HJ HJL3 ltac:(rewrite WS; lia) ltac:(lia)) as HJ3
end.
match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
{ intros a Ha. exfalso. exact (inFP_nil _ Ha). }
cbn [app] in HJ3.
jafter_stretch_keep_hi HS 40%nat regsL (mrestrict (w_H W) memL) RT_CLOB RT_X [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ =>
  assert (HP : P); [| assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros rr Hrr. cbn [ms_regs restrict]. exact (HjK rr Hrr). }
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply (region_kept_stack_sub SEGS B _);
  [exact HJL3 | exact HJ3 | exact U2 | lia | rewrite WS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Et _ _ =>
assert (HEIt : img_env VAL A_LIM Et) by (apply img_env_havoc; [assumption | cbv; lia]);
assert (U2t : bv_unsigned (ew Et 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact U2);
assert (SHOK2 : sh_ok SEGS rt_Bx [] Et (mrestrict (w_H W) memL)) by apply Forall_nil
end.
clear SHOK. rename SHOK2 into SHOK.
paj_run_tok RUN HS HJ3 SHOK Bspan.
{ awr_ok_tac; exact U2t. }
prreg HS (10%bv : bv 5) F10. prreg HS (1%bv : bv 5) F1.
unfold RT_CLOB in F10, F1. cbn [map nth] in F10, F1.
rewrite ?ew_ewset_other in F10, F1 by lia.
rewrite Hj15, E33 in F10. rewrite rt_alu_slt in F10 by lia.
rewrite E1 in F1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tbrange_taken_post, apost_base.
exists ly, S. eexists. eexists. eexists.
split; [cbn [ms_regs]; rewrite F1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rt_extra (Boxreg.bx_n bs)) HS);
        [env_agree_chain HAE | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
cbn [ms_regs]. rewrite F10.
destruct (Z.ltb_spec j (Boxreg.bx_n bs)) as [Hlt|Hge].
+ left. split; [exact (HjT Hlt) | reflexivity].
+ right. split; [apply HjF; lia | reflexivity].
Qed.
End h.
End f.
End d.

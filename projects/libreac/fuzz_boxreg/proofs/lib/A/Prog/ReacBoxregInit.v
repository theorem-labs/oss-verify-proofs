(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths, module names and numbers changed; 345 of its 443 lines of code are new or changed and 89 lines of the source are left out. *)
(* reac_boxreg_init (fuzz_boxreg.asan 0x8161c, 33 instructions): the contract of the ASan build's code.
   The function takes a 32-byte frame on the machine stack (addi sp,sp,-32), calls __asan_memset (r, 0, 284),
   then stores cap clamped to 1..40 (Pau's clamp40 of the sign-extended low 32 bits of a1) at r + 284 after
   checking that word's shadow byte, and returns: the 288-byte registry struct at r, a heap block of the caller,
   holds init_bytes (clamp40 cap) afterwards. It writes nothing else outside its own frame.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReacBoxregInit.v) clears all 288 bytes (memset length
   0x120, not 0x11c) and adds the UBSan null and alignment checks on r; the stored bytes are the same.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_init_c.v clamp40, init_bytes), used as it is. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require reac_boxreg_init_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* sizeof (struct reac_boxreg): 280 bytes of rows, then n (+280) and fabric (+284). *)
Definition REG_SIZE : Z := 288.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 32-byte frame and ESTACK below it for
   the memset wrapper. *)
Definition A_reac_boxreg_initP : Z := BASE + AF_reac_boxreg_init.
Definition REAC_BOXREG_INIT_STK : Z := 32 + ESTACK.
Section h.
Variable B : asyms.
Definition treac_boxreg_init_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r c : Z)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_INIT_STK [(r, r + REG_SIZE)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W') mem' (r + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 (bv_swrap 32 c)))
                         (Z_to_bv 8 0))))).
Definition treac_boxreg_init_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r c : Z),
afn_pre SEGS B REAC_BOXREG_INIT_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 c -> In (r, REG_SIZE) (ablocks B ly S) ->
SRr SEGS W (cfg_at SEGS A_reac_boxreg_initP regs mem md) (treac_boxreg_init_post regs ly S W mem md r c).
(* The walk. The code reads the shadow base through the GOT word of the shadow-base cell (object 1): the
   GOT word holds the cell's address (env slot 33) and the cell holds the shadow base (env slot 32). The
   walk takes the GOT word and the cell as regions one after the other, so it needs no fact on where the
   cell lies against the GOT word. *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Definition SB_RBI : Z := 0x7fff8000.
Definition Bx_RBI : sv := SOff 32 0.
Definition Bspan_RBI : Z * Z := (SB_RBI, SB_RBI + 2 ^ 44 - 1).
Definition got_region_RBI : YP09.region :=
YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition cell_region_RBI : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
(* The registry after the memset: 284 zero bytes and the word at r + 284 the code stores. *)
Definition reg_region_RBI : YP09.region := YP09.mkRegion (Some 10%nat) 0 288 284 288 [YP09.mkChunk 0 (CZero 284)].
Definition rbi_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF SB_RBI SB_RBI 0)] [] [].
Definition ss_rbi : sstate := mkSS AF_reac_boxreg_init sr_atoms [stack_region 32; got_region_RBI] None rbi_facts.
Definition rbi_SH : list shent := [mkSHE 10 0 288].
Definition rbi_extra (cell : Z) : list word := [Z_to_bv 64 SB_RBI; Z_to_bv 64 cell].
Lemma rbi_chunk_byte : forall E m n b cs lo hi wlo whi od cv i,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od cv) cs -> 0 <= i < YP09.cv_len cv ->
exists bb, YP09.cbyte SEGS E (b + od) cv i = Some bb /\ mbyte SEGS m (b + od + i) = Some bb.
Proof.
intros E m n b cs lo hi wlo whi od cv i HR Hb Hin Hi.
unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & HF). rewrite Hb in HF.
rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold YP09.chunk_ok in HF. cbn [YP09.c_off YP09.c_val YP09.c_len] in HF.
exact (HF i Hi).
Qed.
Lemma rbi_mbyte_zero : forall H (m : word -> option byte) a,
aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Ha. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as Hb0. f_equal. apply bv_eq. rewrite Hb0. reflexivity.
Qed.
Lemma rbi_le4_byte : forall (v : word) (k : nat), (k < 4)%nat ->
nth k (Mem.le4 v) (Z_to_bv 8 0) = YP09.byte_of_word v (Z.of_nat k).
Proof.
intros v k Hk. unfold Mem.le4, YP09.byte_of_word.
destruct k as [|[|[|[|k]]]]; try lia; cbn [Z_to_le_bytes nth Z.of_nat];
f_equal; rewrite ?Z.shiftr_div_pow2 by lia; try reflexivity.
Qed.
Lemma rbi_byte_eq : forall x y k, x mod 2 ^ 32 = y mod 2 ^ 32 -> 0 <= k < 4 ->
Z_to_bv 8 (Z.shiftr x (8 * k)) = Z_to_bv 8 (Z.shiftr y (8 * k)).
Proof.
intros x y k Hxy Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296 in Hxy.
assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
destruct Hk' as [-> | [-> | [-> | ->]]];
[change (2 ^ (8 * 0)) with 1 | change (2 ^ (8 * 1)) with 256 | change (2 ^ (8 * 2)) with 65536
| change (2 ^ (8 * 3)) with 16777216]; Z.div_mod_to_equations; lia.
Qed.
(* The bytes the walk leaves at r: 284 zeros, then the four bytes of a word whose low 32 bits are f's. *)
Lemma rbi_post_bytes : forall (H : word -> bool) (m : word -> option byte) (r : Z) (v : word) (f : Z),
(forall i, 0 <= i < 284 -> mbyte SEGS (mrestrict H m) (r + i) = Some (Z_to_bv 8 0)) ->
(forall k, 0 <= k < 4 -> mbyte SEGS (mrestrict H m) (r + 284 + k) = Some (YP09.byte_of_word v k)) ->
bv_unsigned v mod 2 ^ 32 = f mod 2 ^ 32 -> 1 <= f <= 40 ->
forall i, 0 <= i < 288 ->
aview SEGS H m (r + i) = Some (bv_unsigned (nth (Z.to_nat i) (reac_boxreg_init_c.init_bytes f) (Z_to_bv 8 0))).
Proof.
intros H m r v f Z0 ZV HV Hf i Hi. unfold aview, reac_boxreg_init_c.init_bytes.
destruct (Z_lt_ge_dec i 284) as [Hlo | Hhi].
- rewrite (Z0 i ltac:(lia)). cbn [option_map].
rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
- replace (r + i) with (r + 284 + (i - 284)) by lia. rewrite (ZV (i - 284) ltac:(lia)). cbn [option_map].
rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
replace (Z.to_nat i - 284)%nat with (Z.to_nat (i - 284)) by lia.
rewrite rbi_le4_byte by lia. rewrite Z2Nat.id by lia.
unfold YP09.byte_of_word. rewrite (unsigned_lit_small f) by lia.
f_equal. f_equal. apply rbi_byte_eq; [exact HV | lia].
Qed.
(* The clamp branch (bltu at 0x81658): addiw a0,s0,-1 is below 40 exactly when the low 32 bits of cap, signed,
   lie in 1..40. *)
Lemma rbi_cond : forall E c, ew E 11 = Z_to_bv 64 c ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-1)))) (sv_denot E (SLit 40)) =
((1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40)).
Proof.
intros E c H. rewrite branch_ltu_U, (U_lit E 40) by lia.
rewrite U_of_S, S_SAluw, U_SOff, U_SLit, H, Z_to_bv_unsigned. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
change (2 ^ 64) with 18446744073709551616.
apply eq_true_iff_eq. rewrite andb_true_iff, Z.ltb_lt, !Z.leb_le.
Z.div_mod_to_equations. lia.
Qed.
Lemma rbi_clamp40_range : forall x, 1 <= reac_boxreg_init_c.clamp40 x <= 40.
Proof.
intros x. unfold reac_boxreg_init_c.clamp40.
destruct (Z.leb_spec 1 x), (Z.leb_spec x 40); cbn [andb]; lia.
Qed.
Lemma rbi_clamp_in : forall c, (1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40) = true ->
bv_unsigned (Z_to_bv 64 c) mod 2 ^ 32 = reac_boxreg_init_c.clamp40 (bv_swrap 32 c) mod 2 ^ 32.
Proof.
intros c H. unfold reac_boxreg_init_c.clamp40. rewrite H. cbv iota.
rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.
Lemma rbi_clamp_out : forall c, (1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40) = false ->
reac_boxreg_init_c.clamp40 (bv_swrap 32 c) = 40.
Proof. intros c H. unfold reac_boxreg_init_c.clamp40. rewrite H. reflexivity. Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA BS___asan_memset).
Hypothesis HGOT : as_got_shadow B = VAL (A_OBJ 1).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
(* The shadow entry of the registry block: its 288 bytes are addressable. *)
Lemma rbi_shent : forall ly S (W : world SEGS) mem md Ex (q sz : Z),
AR SEGS B ly S W mem md -> In (q, sz) (ablocks B ly S) ->
U Ex Bx_RBI = SHADOW_OFF -> U Ex (SOff 10 0) = q -> req_size sz = 288 ->
shent_ok SEGS Bx_RBI Ex (mrestrict (w_H W) mem) (mkSHE 10 0 288).
Proof.
intros ly S W mem md Ex q sz HAR Hin HB Hq Hsz.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md q sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
rewrite Hsz in Hbceil, Hbia.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
rewrite <- (aview_rd_of SEGS). split.
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md q sz (q + 0) (288 - 0) HAR Hin); rewrite ?Hsz; lia.
- intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
revert Hbia Hb4096 Hbceil C1 C3 C5. clear. intros. lia.
Qed.
Lemma rbi_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r : Z),
afn_pre SEGS B REAC_BOXREG_INIT_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> In (r, REG_SIZE) (ablocks B ly S) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rbi_extra (as_shadow_cell B)))) ss_rbi
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_boxreg_init)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch r HPRE H10 Hin.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_INIT_STK = 4128) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (_ & _ & Kgot & _).
rewrite HGOT in Kgot.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 1)) as HgotV.
pose proof HAR as (M & _).
pose proof (asyms_area_bound B (as_shadow_cell B, 8) (am_syms _ _ _ _ M) ltac:(cbn; tauto)) as [Hc1 Hc2].
cbn [fst snd] in Hc1, Hc2. unfold kImgEnd in Hc2. clear M.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rbi_extra (as_shadow_cell B)))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rbi_extra (as_shadow_cell B))) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_RBI) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_shadow_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_rbi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_region_RBI.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite Egot, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_shadow_cell B));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
- apply pairwise_disjoint_of_extents.
unfold stack_region, got_region_RBI, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite Usp, Egot, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; exact I].
cbn [rbi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB_RBI; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB_RBI.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
(* The right to write the regions after the memset: the word r + 284 of the registry (in the footprint) and the
   stack frame. *)
Local Ltac rbi_awr r Hin F10 Usp' :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly0 ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly0 own) end;
eapply awr_ok_cons_block;
[ reflexivity | rewrite F10, unsigned_lit_small by lia; reflexivity | exact Hin | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size REG_SIZE) with 288; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
| awr_ok_tac; exact Usp' ].
Theorem pb_reac_boxreg_init : treac_boxreg_init_spec.
Proof.
unfold treac_boxreg_init_spec.
intros ly S W regs mem md ch r c HPRE H10 H11 Hin.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof (rbi_entry ly S W regs mem md ch r HPRE H10 Hin) as HS.
pose proof (ajournal_init SEGS B REAC_BOXREG_INIT_STK [(r, r + REG_SIZE)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_INIT_STK = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HRS : REG_SIZE = 288) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof HAR as (M & _).
pose proof (asyms_area_bound B (as_shadow_cell B, 8) (am_syms _ _ _ _ M) ltac:(cbn; tauto)) as [Hc1 Hc2].
cbn [fst snd] in Hc1, Hc2. unfold kImgEnd in Hc2. clear M.
remember (Eimg (Ereg regs (rbi_extra (as_shadow_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rbi_extra (as_shadow_cell B))) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB_RBI) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_shadow_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (rbi_extra (as_shadow_cell B))) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS Bx_RBI [] E (mrestrict (w_H W) mem)) by constructor.
clear HE EL.
unfold cfg_at, A_reac_boxreg_initP.
change (w64 (BASE + AF_reac_boxreg_init)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_init)).
(* 1. The frame, the saves of ra, s0, s1, s2 and the load of the GOT word, up to the load of the shadow base
   from the cell (0x8163c). *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan_RBI 0x16f0; [awr_ok_tac; exact Usp |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
try clear HEI0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell & _ & _ & _).
(* 2. The GOT word is read: drop it and take the cell; run to the call of __asan_memset. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
let rs := eval vm_compute in (pick (ss_mem ssx) [0%nat]) in
pose proof (st_ok_pi_submem Ex ssx (restrict Hh msx) rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HS1;
clear HS;
assert (HRc : region_ok SEGS Ex (ms_mem (restrict Hh msx)) cell_region_RBI);
[ cbn [restrict ms_mem]; unfold cell_region_RBI, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite E33, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  constructor; [|constructor];
  apply (chunk_ok_val SEGS Ex _ (as_shadow_cell B) 0 8 (SOff 32 0) SB_RBI);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_RBI; zside | zside |];
  rewrite Z.add_0_r; exact (val_mem_of_rdword SEGS (w_H W) _ _ _ Kcell)
| ];
pose proof (st_ok_pi_add_region Ex _ (restrict Hh msx) cell_region_RBI HS1 eq_refl HRc
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, cell_region_RBI;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E33, Usp, unsigned_lit_small by lia;
        split; [lia | exact I])) as HS;
clear HS1 HRc
end.
clear Kcell.
paj_run_tok RUN HS HJ SHOK Bspan_RBI; [awr_ok_tac; exact Usp |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
try clear HEI0.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -32) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity)
end.
(* 3. __asan_memset (r, 0, 284): it writes 0 to [r, r + 284) and keeps every other byte above its own stack. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA BS___asan_memset) AMEMSET W rg mm
REAC_BOXREG_INIT_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S _ 0 r 0 284 (-32) _ HJ);
[ rewrite Ra0, E10; reflexivity
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia
| lia
| lia
| exact Qsp
| reflexivity
| lia
| rewrite WS, Hes; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| intros a Ha; split;
[ right; left; split;
[ exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
| exists r, REG_SIZE; split; [exact Hin | change (req_size REG_SIZE) with 288; lia] ]
| rewrite Hes; lia ]
| eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZE) with 288; lia
| eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZE) with 288; lia
| intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
  change (req_size REG_SIZE) with 288; lia
| exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* Back at the return slot: the stack region (the saved registers) is kept by the wrapper. *)
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [1%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 512)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs (rbi_extra (as_shadow_cell B))) E')
by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (F10 : ew E' 10 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E10).
assert (F11 : ew E' 11 = Z_to_bv 64 c) by (rewrite OLD by lia; exact E11).
assert (F32 : ew E' 32 = Z_to_bv 64 SB_RBI) by (rewrite OLD by lia; exact E32).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* The registry as the memset left it: 284 zero bytes and the word at r + 284 to be stored. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
assert (HRr : region_ok SEGS Ex (ms_mem (restrict Hh msx)) reg_region_RBI);
[ cbn [restrict ms_mem mkst]; unfold reg_region_RBI, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite F10, unsigned_lit_small by lia;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE (proj1 HJ2) Hin) as (_ & _ & _ & _ & Hpr & _);
  split; [lia|]; split; [lia|];
  split; [intros o Ho; apply (apresent_writable SEGS);
          apply (proj1 (Hpr (r + o) ltac:(change (req_size REG_SIZE) with 288; lia)))|];
  constructor; [|constructor];
  intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in Hi |- *;
  exists (Z_to_bv 8 0); split; [reflexivity|];
  rewrite Z.add_0_r; apply rbi_mbyte_zero; exact (Heff i ltac:(lia))
| pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) reg_region_RBI HS eq_refl HRr
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, reg_region_RBI;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite F10, Usp', unsigned_lit_small by lia;
          split; [lia | exact I])) as HS2; clear HS HRr; rename HS2 into HS ]
end.
try clear SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
assert (SHOK : sh_ok SEGS Bx_RBI rbi_SH Ex (mrestrict (w_H W) (ms_mem msx)));
[ unfold sh_ok, rbi_SH; apply Forall_cons; [|apply Forall_nil];
  cbn [ms_mem mkst];
  apply (rbi_shent ly S W mem2 _ Ex r REG_SIZE (proj1 HJ2) Hin);
  [ unfold Bx_RBI; rewrite (U_atom Ex 32 SB_RBI F32) by (unfold SB_RBI; lia); reflexivity
  | rewrite (U_atom Ex 10 r F10) by lia; reflexivity
  | reflexivity ]
| ] end.
(* 4. The clamp of cap to 1..40, up to its branch. *)
paj_run_tok RUN HS HJ2 SHOK Bspan_RBI; [rbi_awr r Hin F10 Usp' |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
psrr_branch_tok RUN BR HS SHOK Bspan_RBI;
rewrite (rbi_cond E' c F11) in Hc;
(* 5. The store of the clamped cap at r + 284: its shadow byte is 0 (the block is addressable), so the
   report path at 0x81690 is not taken; then the reloads and the return. *)
(paj_run_tok RUN HS HJ2 SHOK Bspan_RBI; [rbi_awr r Hin F10 Usp' |]);
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
1: lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
assert (HVE : bv_unsigned (sv_denot Ef (SOff 11 0)) mod 2 ^ 32 = reac_boxreg_init_c.clamp40 (bv_swrap 32 c) mod 2 ^ 32)
by (cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite F11, Z.add_0_r, Z_to_bv_bv_unsigned;
    exact (rbi_clamp_in c Hc))
end.
2: lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
assert (HVE : bv_unsigned (sv_denot Ef (SLit 40)) mod 2 ^ 32 = reac_boxreg_init_c.clamp40 (bv_swrap 32 c) mod 2 ^ 32)
by (rewrite (rbi_clamp_out c Hc); reflexivity)
end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msc), HVE : bv_unsigned (sv_denot _ ?e) mod _ = _ |- _ =>
let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
assert (G10 : bv_unsigned (ew Ef 10) = r) by (rewrite !ew_ewset_other by lia; rewrite F10, unsigned_lit_small by lia; reflexivity);
let rf := eval vm_compute in (nth_error (ss_mem ssf) 0) in
lazymatch rf with Some ?rr =>
pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H W) msc) 0 rr HS eq_refl) as HRF
end;
assert (Z0 : forall i, 0 <= i < 284 -> mbyte SEGS (mrestrict (w_H W) (ms_mem msc)) (r + i) = Some (Z_to_bv 8 0));
[ intros i Hi0;
  destruct (rbi_chunk_byte Ef _ 10 r _ _ _ _ _ 0 (CZero 284) i HRF G10 ltac:(cbn [In]; auto 10) ltac:(cbn; lia))
    as (bb & Hbb & Hm);
  cbn [YP09.cbyte] in Hbb; injection Hbb as <-; rewrite Z.add_0_r in Hm; exact Hm
| ];
assert (ZV : forall k, 0 <= k < 4 ->
  mbyte SEGS (mrestrict (w_H W) (ms_mem msc)) (r + 284 + k) = Some (YP09.byte_of_word (sv_denot Ef e) k));
[ intros k Hk;
  destruct (rbi_chunk_byte Ef _ 10 r _ _ _ _ _ 284 (CVal 4 e) k HRF G10 ltac:(cbn [In]; auto 10) ltac:(cbn; lia))
    as (bb & Hbb & Hm);
  cbn [YP09.cbyte] in Hbb; injection Hbb as <-; exact Hm
| ];
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_boxreg_init_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (rbi_extra (as_shadow_cell B)) HS);
        [ split; [intros n Hn; rewrite !ew_ewset_other by lia; exact (proj1 HAE' n Hn) | rewrite !ed_ewset; exact (proj2 HAE')]
        | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
intros i Hi;
exact (rbi_post_bytes (w_H W) (ms_mem msc) r (sv_denot Ef e) _ Z0 ZV HVE (rbi_clamp40_range _) i Hi)
end.
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths, module names and numbers changed; 309 of its 395 lines of code are new or changed and 101 lines of the source are left out. *)
(* reac_boxreg_init (fuzz_boxreg.asan-ubsan 0x81894, 37 instructions): the contract of the ASan+UBSan build's code.
   The function takes a 32-byte frame on the machine stack (addi sp,sp,-32), calls __asan_memset (r, 0, 288),
   checks r against NULL and 4-byte alignment for UBSan (the branches to the UBSan handlers are refuted by the
   allocator's block law: a block's address is a multiple of 16 and at least 4096), then stores cap clamped to
   1..40 (Pau's clamp40 of the sign-extended low 32 bits of a1) at r + 284 after checking that word's shadow byte,
   and returns: the 288-byte registry struct at r, a heap block of the caller, holds init_bytes (clamp40 cap)
   afterwards. It writes nothing else outside its own frame.
   Image difference: the asan build (lib/A/Prog/ReacBoxregInit.v) clears 284 bytes (memset length 0x11c) and has no
   UBSan checks; the stored bytes are the same.
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require reac_boxreg_init_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* sizeof (struct reac_boxreg): 280 bytes of rows, then n (+280) and fabric (+284). *)
Definition REG_SIZEB : Z := 288.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 32-byte frame and ESTACK below it for
   the memset wrapper. *)
Definition AB_reac_boxreg_initP : Z := BASE + AF_reac_boxreg_init.
Definition REAC_BOXREG_INIT_STKB : Z := 32 + ESTACK.
Section h.
Variable B : asyms.
Definition tbreac_boxreg_init_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r c : Z)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_INIT_STKB [(r, r + REG_SIZEB)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W') mem' (r + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 (bv_swrap 32 c)))
                         (Z_to_bv 8 0))))).
Definition tbreac_boxreg_init_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r c : Z),
afn_pre SEGS B REAC_BOXREG_INIT_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 c -> In (r, REG_SIZEB) (ablocks B ly S) ->
SRr SEGS W (cfg_at SEGS AB_reac_boxreg_initP regs mem md) (tbreac_boxreg_init_post regs ly S W mem md r c).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA BB___asan_memset).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The walk's symbolic frame: atom 32 is the shadow offset that the code loads through the GOT word (object 1) from
   the shadow cell (object 12); the shadow checks are discharged from the shadow entry of the block at atom 10. *)
Definition SBR : Z := 0x7fff8000.
Definition CBR : sv := SOff 32 0.
Definition BspanR : Z * Z := (SBR, SBR + 2 ^ 44 - 1).
Definition rbi_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF SBR SBR 0)] [] [].
Definition rbi_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32].
Definition ss_rbi : sstate := mkSS AF_reac_boxreg_init sr_atoms rbi_regions None rbi_facts.
Definition ER (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SBR]).
Lemma rbi_entry : forall ly S W (regs : bvmap 5 word) mem md ch r,
afn_pre SEGS B REAC_BOXREG_INIT_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> In (r, REG_SIZEB) (ablocks B ly S) ->
st_ok_pi SEGS VAL (ER regs) ss_rbi (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_reac_boxreg_initP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBR [] (ER regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r HPRE H10 Hin.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_INIT_STKB = 4128) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := ER regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBR]) n)
  by (intros n Hn; subst E; unfold ER; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ER; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold ER; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rbi, AB_reac_boxreg_initP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rbi_regions, stack_region, got_regionP, bcell_regionP.
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
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBR SBR);
      [cbn [sv_denot CBR]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBR; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold rbi_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
    repeat split; lia.
  + split; [|split; exact I].
    cbn [rbi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SBR; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil.
    clear. unfold SBR. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. apply Forall_nil.
Qed.
(* The block's window: the word the code stores at r + 284; the shadow entry of the whole block. *)
Definition RB_rbi : YP09.region := YP09.mkRegion (Some 10%nat) 284 288 284 288 [].
Definition rbi_SH : list shent := [mkSHE 10 0 288].
Lemma rbi_shent : forall ly S (W : world SEGS) mem md Ex (q b sz lo hi : Z) (n : nat),
AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
U Ex CBR = SHADOW_OFF -> U Ex (SOff n 0) = q ->
b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
shent_ok SEGS CBR Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md Ex q b sz lo hi n HAR Hin HB Hq Hlo Hlh Hhi.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
rewrite <- (aview_rd_of SEGS). split.
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
- intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
  revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.
(* The clamp test bltu (addiw s0,-1), 40 is Pau's 1 <= cap <= 40 on the low 32 bits of cap. *)
Lemma rbi_cond : forall E c, ew E 11 = Z_to_bv 64 c ->
(U E (SAluw ALU_ADD (SOff 11 0) (SLit (-1))) <? 40) = ((1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40)).
Proof.
intros E c H11.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite U_SOff, H11, Z.add_0_r, U_SLit, Z_to_bv_unsigned.
unfold zcanon, M64, bv_swrap. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
change ((-1 mod 18446744073709551616) mod 4294967296) with 4294967295.
change (bv_half_modulus 32) with 2147483648.
apply eq_true_iff_eq. rewrite andb_true_iff, Z.ltb_lt, !Z.leb_le.
Z.div_mod_to_equations. lia.
Qed.
Lemma rbi_init_lo : forall f i, 0 <= i < 284 ->
nth (Z.to_nat i) (reac_boxreg_init_c.init_bytes f) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
intros f i Hi. unfold reac_boxreg_init_c.init_bytes.
rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.
Lemma rbi_init_hi : forall f k, 0 <= k < 4 ->
nth (Z.to_nat (284 + k)) (reac_boxreg_init_c.init_bytes f) (Z_to_bv 8 0) = byte_of_word (Z_to_bv 64 f) k.
Proof.
intros f k Hk. unfold reac_boxreg_init_c.init_bytes.
rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
replace (Z.to_nat (284 + k) - 284)%nat with (Z.to_nat k) by lia.
unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4, byte_of_word.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia;
cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z_to_le_bytes nth];
rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
Lemma rbi_swrap_mod : forall c, bv_swrap 32 c mod 2 ^ 32 = c mod 2 ^ 32.
Proof.
intros c. unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus. cbn [Z.of_N].
change (2 ^ 32) with 4294967296. change (4294967296 / 2) with 2147483648.
Z.div_mod_to_equations. lia.
Qed.
Lemma rbi_byte_low32 : forall x y k, 0 <= k < 4 -> x mod 2 ^ 32 = y mod 2 ^ 32 ->
byte_of_word (Z_to_bv 64 x) k = byte_of_word (Z_to_bv 64 y) k.
Proof.
intros x y k Hk Hxy. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
rewrite !Z.shiftr_div_pow2 by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
change (2 ^ 64) with 18446744073709551616. change (2 ^ 8) with 256. change (2 ^ 32) with 4294967296 in Hxy.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia; cbn [Z.mul Z.pow Z.pow_pos Pos.iter Z.mul];
Z.div_mod_to_equations; lia.
Qed.
Lemma rbi_val : forall E c e k,
ew E 11 = Z_to_bv 64 c -> 0 <= k < 4 ->
(e = SOff 11 0 /\ ((1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40)) = true \/
 e = SLit 40 /\ ((1 <=? bv_swrap 32 c) && (bv_swrap 32 c <=? 40)) = false) ->
byte_of_word (sv_denot E e) k =
nth (Z.to_nat (284 + k)) (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 (bv_swrap 32 c))) (Z_to_bv 8 0).
Proof.
intros E c e k H11 Hk He. rewrite rbi_init_hi by exact Hk.
unfold reac_boxreg_init_c.clamp40.
destruct He as [[-> Hc] | [-> Hc]]; rewrite Hc.
- cbn [sv_denot]. rewrite H11, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply rbi_byte_low32; [exact Hk|]. symmetry. apply rbi_swrap_mod.
- reflexivity.
Qed.
Lemma rbi_chunk_byte : forall segs E m n b cs lo hi wlo whi od (w : N) e i,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> 0 <= i < Z.of_N w ->
mbyte segs m (b + od + i) = Some (byte_of_word (sv_denot E e) i).
Proof.
intros segs E m n b cs lo hi wlo whi od w e i HR Hb Hin Hi.
unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & HF). rewrite Hb in HF.
rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold YP09.chunk_ok in HF. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in HF.
destruct (HF i Hi) as (bb & Hc & Hm). cbn [cbyte] in Hc. injection Hc as <-. exact Hm.
Qed.
(* The write windows of the walk after the call: the block's word at r + 284 (inside the footprint
   [(r, r + 288)]) and the frame. *)
Local Ltac rbi_awr r Hin F10 Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
  eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat r REG_SIZEB);
  [ reflexivity | rewrite F10; apply unsigned_lit_small; lia | exact Hin | cbn; lia
  | change (req_size REG_SIZEB) with 288; cbn; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; lia]
  | ];
  awr_ok_tac; exact Usp.
Theorem pbb_reac_boxreg_init : tbreac_boxreg_init_spec.
Proof.
unfold tbreac_boxreg_init_spec.
intros ly S W regs mem md ch r c HPRE H10 H11 Hin.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rbi_entry ly S W regs mem md ch r HPRE H10 Hin) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_INIT_STKB [(r, r + REG_SIZEB)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_INIT_STKB = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *. assert (Hsz : REG_SIZEB = 288) by reflexivity.
remember (ER regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBR]) n)
  by (intros n Hn; subst E; unfold ER; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SBR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SBR]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
unfold cfg_at, AB_reac_boxreg_initP.
change (w64 (BASE + AF_reac_boxreg_init)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_init)).
(* The frame, the saves, the shadow base, the arguments, up to the call of __asan_memset. *)
paj_run_tok RUN HS HJ SHOK BspanR; [awr_ok_tac; exact Usp |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -32) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity)
end.
(* The memset wrapper: it writes 0 to [r, r + 288) and keeps every other byte above its own stack. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA BB___asan_memset) AMEMSET W rg mm
REAC_BOXREG_INIT_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 r 0 REG_SIZEB (-32) _ HJ);
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
    [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; lia]
    | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ]
  | rewrite Hes; lia ]
| eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZEB) with 288; lia
| eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZEB) with 288; lia
| intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZEB) with 288; lia
| exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
clear Ra0 Ra1 Ra2 Rra Rgp Rtp.
(* Back at the return slot: the stack region (the saved registers) is kept by the wrapper. *)
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD : forall k, (k < 512)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs [Z_to_bv 64 SBR]) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (F10 : ew E' 10 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E10).
assert (F11 : ew E' 11 = Z_to_bv 64 c) by (rewrite OLD by lia; exact E11).
assert (F32 : ew E' 32 = Z_to_bv 64 SBR) by (rewrite OLD by lia; exact E32).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
clear SHOK.
(* The block's word at r + 284 as a writable window, and the shadow entry of the block. *)
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
  assert (HR : region_ok SEGS E' (ms_mem (restrict Hh msx)) RB_rbi);
  [ cbn [restrict ms_mem mkst]; unfold RB_rbi, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite F10, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS);
    destruct (al_blocks _ _ LAWS ly S W mem2 md2 r REG_SIZEB HAR2 Hin) as (_ & _ & _ & _ & Hbp & _);
    apply Hbp; change (req_size REG_SIZEB) with 288; lia
  | pose proof (st_ok_pi_add_region E' ssx (restrict Hh msx) RB_rbi HS ltac:(vm_compute; reflexivity) HR
                  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
                          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
                        cbn [all_disjoint]; unfold extent_disjoint, RB_rbi;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
                        rewrite F10, Usp', unsigned_lit_small by lia;
                        repeat match goal with |- _ /\ _ => split end; first [exact I | lia])) as HS2;
    clear HS HR; rename HS2 into HS ]
end.
assert (SHOK : sh_ok SEGS CBR rbi_SH E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, rbi_SH. apply Forall_cons; [|apply Forall_nil].
  apply (rbi_shent ly S W mem2 md2 E' r r REG_SIZEB 0 288 10 HAR2 Hin).
  - unfold CBR. rewrite (U_atom E' 32 SBR F32) by (unfold SBR; lia). reflexivity.
  - apply (U_atom E' 10 r F10). lia.
  - lia. - lia. - change (req_size REG_SIZEB) with 288. lia. }
(* The UBSan checks of r (beqz s1 at 0x818c8, andi s1,3 / bnez at 0x818cc..0x818d0, both to the trap at 0x81914):
   the engine decides them from atom 10's facts (r >= 4096, r mod 16 = 0). The run stops at the clamp test. *)
paj_run_tok RUN HS HJ2 SHOK BspanR; [rbi_awr r Hin F10 Usp' |].
psrr_branch_tok RUN BR HS SHOK BspanR.
all: rewrite branch_ltu_U, (U_lit E' 40) in Hc by lia; rewrite (rbi_cond E' c F11) in Hc.
(* Both arms (cap kept, or 40): the shadow check of r + 284 (the engine's shadow token: its granule r + 280 ..
   r + 287 is inside the block's shadow entry, so the __asan_report_store4 path at 0x81924 is not taken), the store
   of the clamped cap, the reloads, the release of the frame and the return. *)
all: paj_run_tok RUN HS HJ2 SHOK BspanR; [rbi_awr r Hin F10 Usp' |].
(* Outside the frame and the stored word the two runs after the call keep every byte. *)
all: assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (r + 284 <= a < r + 288) ->
       aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a);
[ intros a Ha Hw Hb; transitivity (aview SEGS (w_H W) (ms_mem ms0) a);
  [ apply (kept_of_frame E' _ (w_H W) (ms_mem ms0) (ms_mem ms1)
             (fun x => (spZ regs - 32 <= x < spZ regs) \/ (r + 284 <= x < r + 288)) HFr0); [| exact Ha | tauto]
  | apply (kept_of_frame E' _ (w_H W) mem2 (ms_mem ms0)
             (fun x => (spZ regs - 32 <= x < spZ regs) \/ (r + 284 <= x < r + 288)) HFr); [| exact Ha | tauto] ];
  intros bb wlo whi aa Hwin Hr; vm_compute in Hwin;
  destruct Hwin as [Hwin | [Hwin | []]]; injection Hwin as <- <- <-; cbn [base_val] in Hr;
  rewrite ?F10, ?Usp', ?unsigned_lit_small in Hr by lia; lia
| ].
(* The post: bytes 0 .. 283 are the wrapper's zeros, bytes 284 .. 287 the stored word of the block region. *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat';
  unfold tbreac_boxreg_init_post, apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SBR] HS);
          [ split; [intros n Hn; rewrite !ew_ewset_other by lia; exact (proj1 HAE' n Hn) | exact (proj2 HAE')]
          | vm_compute; reflexivity ]|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
  intros i Hi;
  destruct (Z_lt_le_dec i 284) as [Hlo | Hhi];
  [ rewrite (KEEP (r + i)) by lia; rewrite (Heff i) by lia; rewrite rbi_init_lo by lia; reflexivity
  | pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRB; cbn [restrict ms_mem] in HRB;
    unfold aview; replace (r + i) with (r + 284 + (i - 284)) by lia;
    lazymatch type of HRB with context [CVal 4 ?ev] => rewrite (rbi_chunk_byte SEGS _ _ 10 r _ _ _ _ _ 284 4 ev (i - 284) HRB) end;
    [ cbn [option_map]; do 2 f_equal;
      replace (Z.to_nat i) with (Z.to_nat (284 + (i - 284))) by (f_equal; lia);
      apply rbi_val;
      [ rewrite !ew_ewset_other by lia; exact F11 | lia
      | first [left; split; [reflexivity | exact Hc] | right; split; [reflexivity | exact Hc]] ]
    | rewrite !ew_ewset_other by lia; rewrite F10; apply unsigned_lit_small; lia
    | left; reflexivity
    | cbn; lia ] ]
end.
Qed.
End h.
End f.
End d.

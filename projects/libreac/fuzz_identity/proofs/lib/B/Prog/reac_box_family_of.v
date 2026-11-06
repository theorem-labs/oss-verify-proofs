(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* reac_box_family_of (fuzz_identity.asan-ubsan 0x82c20, 61 slots to 0x82d10): the contract of
   the ASan+UBSan build's code and its walk, the build-B twin of lib/A/Prog/reac_box_family_of.v.

   The code: a 64-byte machine frame keeps ra, s0..s5. A null box returns 0. Otherwise the UBSan
   alignment check of the box pointer (0x82c44 andi, 0x82c48 bnez to the trap word 0x82cf0) runs,
   then the code loads the shadow base, checks the shadow of box+36 and reads the byte at box+36;
   a zero byte returns 0. Otherwise it compares, for row i = 0, 1, 2 of the image's table
   HW_FAMILY (listing object 17, 3 rows of 12 bytes: a 4-byte family, then an 8-byte hw block),
   the 8 bytes at box+28 with the row's hw block through the bcmp wrapper
   (IB___interceptor_trampoline_bcmp, cgif's abcmp_realizes). At the first equal row it checks the
   shadow of the row's family field and returns that field, sign-extended from 32 bits; when no
   row is equal it returns 0.

   Callers: LLVMFuzzerTestOneInput calls this function with NULL and with &id, an object of its
   own side-stack frame. The function only reads the box: it writes its own machine frame and the
   bcmp wrapper's window below it, so the contract is in the afn_pre / apost_base form; the box
   premise accepts a heap block or an object of a caller's frame (afobj). Either one is 8-aligned
   (a heap block is 16-aligned by AR_blocks_law, a frame object is 8-aligned by afobj), so the
   UBSan alignment trap is not reached and the statement needs no premise beyond A's. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase IdentRo YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBPaLib YC1g YC1h IdentBFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The value a 32-bit load gives a register: v sign-extended from 32 bits. *)
Definition famof_sx32 (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32.
(* Row i of the table at t matches the box at p: the box's 8 hw bytes (p+28..p+35) equal the
   row's hw block (t+12i+4..t+12i+11). *)
Definition famof_row (rd : reader) (p t i : Z) : Prop :=
forall j, 0 <= j < 8 -> rd (p + 28 + j) = rd (t + 12 * i + 4 + j).
(* The value the call returns, r, for the box at p, the table at t and the table's family fields
   f0 f1 f2 (the plain model's FAMOF_FAM, lib/Prog/reac_box_family_of_c.v, with the table read from memory). *)
Definition famof_res (rd : reader) (p t f0 f1 f2 r : Z) : Prop :=
(p = 0 /\ r = 0) \/
(p <> 0 /\ rd (p + 36) = Some 0 /\ r = 0) \/
(p <> 0 /\ rd (p + 36) <> Some 0 /\ famof_row rd p t 0 /\ r = f0) \/
(p <> 0 /\ rd (p + 36) <> Some 0 /\ ~ famof_row rd p t 0 /\ famof_row rd p t 1 /\ r = f1) \/
(p <> 0 /\ rd (p + 36) <> Some 0 /\ ~ famof_row rd p t 0 /\ ~ famof_row rd p t 1 /\ famof_row rd p t 2 /\ r = f2) \/
(p <> 0 /\ rd (p + 36) <> Some 0 /\ ~ famof_row rd p t 0 /\ ~ famof_row rd p t 1 /\ ~ famof_row rd p t 2 /\ r = 0).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
(* The function's address, its table, and the stack it needs: its own 64-byte frame (0x82c20
   addi sp,sp,-64; 0x82ce8 addi sp,sp,64; no other write of sp), then the bcmp wrapper's
   2 * ESTACK below it (abcmp_realizes; the call at 0x82c98 has sp = sp0 - 64). *)
Definition A_reac_box_family_ofP : Z := BASE + AF_reac_box_family_of.
Definition FAMOF_HWF : Z := VAL (A_OBJ 17).
Definition FAMOF_FRAME : Z := 64.
Definition REAC_BOX_FAMILY_OF_STK : Z := FAMOF_FRAME + 2 * ESTACK.
Section h.
Variable B : asyms.
(* The box at p (p <> 0): a heap block of at least the struct's 38 bytes, or a 38-byte object of
   a caller's side-stack frame. *)
Definition famof_box ly S (W : world SEGS) mem (p : Z) : Prop :=
(exists n, In (p, n) (ablocks B ly S) /\ 38 <= n) \/ afobj SEGS B ly S W mem p 38.
(* The table HW_FAMILY (36 bytes at FAMOF_HWF): its bytes are readable and its three family
   fields hold f0, f1, f2. The shadow of the table is NOT stated here: it is re-derived at
   each read from the state's own AR, through the read-only facts below. *)
Definition famof_tbl (W : world SEGS) mem (f0 f1 f2 : Z) : Prop :=
(forall a, FAMOF_HWF <= a < FAMOF_HWF + 36 -> aview SEGS (w_H W) mem a <> None) /\
0 <= f0 < 2 ^ 32 /\ val_mem SEGS (mrestrict (w_H W) mem) FAMOF_HWF 4 f0 /\
0 <= f1 < 2 ^ 32 /\ val_mem SEGS (mrestrict (w_H W) mem) (FAMOF_HWF + 12) 4 f1 /\
0 <= f2 < 2 ^ 32 /\ val_mem SEGS (mrestrict (w_H W) mem) (FAMOF_HWF + 24) 4 f2.
Definition treac_box_family_of_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (p f0 f1 f2 : Z)
: world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOX_FAMILY_OF_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_BOX_FAMILY_OF_STK <= a < spZ regs) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
exists r, famof_res (aview SEGS (w_H W) mem) p FAMOF_HWF f0 f1 f2 r /\ getr regs' 10 = Z_to_bv 64 (famof_sx32 r)).
Definition treac_box_family_of_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p f0 f1 f2 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 ->
(p <> 0 -> famof_box ly S W mem p) ->
famof_tbl W mem f0 f1 f2 ->
SRr SEGS W (cfg_at SEGS A_reac_box_family_ofP regs mem md)
(treac_box_family_of_post regs ly S W mem md p f0 f1 f2).
(* --- the walk ------------------------------------------------------------------------ *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* The bcmp wrapper's contract (cgif AE2s.v:710 bcmp_icpt_contract): a Section hypothesis,
   proved in lib/ReusableB/YE2s.v:711 (Corollary bcmp_icpt_contract, 0x42208), which is image B's
   copy; lib/A/AE2s.v:711 proves the same corollary for image A, at 0x421a0. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
(* The image's read-only data is usable in EVERY state (lib/A/Prog/IdentRo.v, image-generic):
   the shadow of the table is re-derived from the current state's AR at every read through
   ro_read_ok_glob, never carried across a call. *)
Variable GL : list (Z * Z).
Hypothesis IMGSH : img_shadow_vis SEGS B.
Hypothesis GM : globs_marked SEGS B GL.
(* HW_FAMILY is one of the registered globals (asan_globals entry 9 of the B image: beg 0x21100,
   size 36), lies inside the image's read range with room for the wrappers' 64-byte window, and
   lies apart from the shadow GOT slot (object 1) and the shadow cell (object 31). *)
Hypothesis HWFG : In (FAMOF_HWF, 36) GL.
Hypothesis HWFIMG : IMG_LO + 64 <= FAMOF_HWF /\ FAMOF_HWF + 100 <= IMG_TOP.
Hypothesis HWFSEP : (FAMOF_HWF + 36 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= FAMOF_HWF) /\
(FAMOF_HWF + 36 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= FAMOF_HWF).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
(* The shadow base as an atom (the code loads it from the image's cell), its span, and the
   atoms of the walk: 2 = sp, 10 = the box, 32 = the shadow base, 33 = the byte at box+36,
   34, 35, 36 = the table's three family fields, A_OBJ 17 = the table. *)
Definition SB_FO : Z := 0x7fff8000.
Definition Bx_FO : sv := SOff 32 0.
Definition Bspan_FO : Z * Z := (SB_FO, SB_FO + 2 ^ 44 - 1).
Definition famof_extra (b36 f0 f1 f2 : Z) : list word := map (Z_to_bv 64) [SB_FO; b36; f0; f1; f2].
Definition EFO (regs : bvmap 5 word) (b36 f0 f1 f2 : Z) : env := Eimg (Ereg regs (famof_extra b36 f0 f1 f2)).
Definition famof_box_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 38 0 0 [YP09.mkChunk 36 (CVal 1 (SOff 33 0))].
Definition famof_tbl_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 17)) 0 36 0 0
[YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 12 (CVal 4 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SOff 36 0))].
Definition famof_atoms (lo hi al : Z) : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF lo hi al); (32%nat, mkAF SB_FO SB_FO 0);
(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
(36%nat, mkAF 0 (2 ^ 32 - 1) 0); (A_OBJ 17, mkAF IMG_LO IMG_TOP 0) ].
Definition famof_rs : smem := [stack_region FAMOF_FRAME; got_regionP; bcell_regionP 32; famof_box_region; famof_tbl_region].
Definition ss_famof : sstate :=
mkSS AF_reac_box_family_of sr_atoms famof_rs None (mkFacts (famof_atoms 4096 140737479966720 3) [] []).
(* The shadow entries: the box (read once, before the first call) and the table (read after a
   call; its entry is re-made from the state's own AR after every call). *)
Definition famof_SH : list shent := [mkSHE 10 0 38].
Definition famof_SHT : list shent := [mkSHE (A_OBJ 17) 0 36].
(* What the call keeps: every byte outside its stack. *)
Definition famof_keep (regs : bvmap 5 word) (W : world SEGS) mem m' : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_BOX_FAMILY_OF_STK <= a < spZ regs) ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a.
Lemma famof_val_mem1 : forall H (m : word -> option byte) a v,
aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
(* The box's place: 8-aligned, below the allocation ceiling, in application memory, off the image. *)
Lemma famof_boxf : forall ly S W mem md p, AR SEGS B ly S W mem md -> famof_box ly S W mem p ->
p mod 8 = 0 /\ 4096 <= p /\ p + 38 <= alloc_ceiling /\ in_app p 38 /\ off_img p 38.
Proof.
intros ly S W mem md p HAR [(n & Hin & Hn) | ((cid & pos & Hfr & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA)].
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hceil & Happ & _ & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff.
split; [| split; [lia | split; [lia | split; [apply (in_app_sub p (req_size n)); [exact Happ | lia | lia | lia] | unfold off_img; lia]]]].
rewrite (Z.div_mod p 16 ltac:(lia)), H16, Z.add_0_r. replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by ring.
apply Z_mod_mult.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfr) as Hoff.
split; [exact Hp8|]. split; [lia|]. split; [lia|]. split.
+ apply (in_app_sub _ _ p 38 Hfapp); lia.
+ unfold off_img. lia.
Qed.
(* The box's bytes and shadow in a later state of the same journal: a heap block's from that
   state's AR, a frame object's shadow carried by the journal from the entry state. *)
Lemma famof_box_state : forall ly S W mem md p STK sp0 memT mdT,
AR SEGS B ly S W mem md -> famof_box ly S W mem p ->
ajournal SEGS B STK sp0 [] ly S W mem md [] ly S W memT mdT 0 ->
(forall a, p <= a < p + 38 -> apresent (w_H W) memT a) /\
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF p 38 /\
(forall d n, p <= d -> d + n <= p + 38 -> 0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n).
Proof.
intros ly S W mem md p STK sp0 memT mdT HAR Hbox HJ.
pose proof (proj1 HJ) as HART.
destruct Hbox as [(n & Hin & Hn) | ((cid & pos & Hfr & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA)].
- destruct (al_blocks _ _ LAWS ly S W memT mdT p n HART Hin) as (_ & _ & _ & _ & Hpres & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
split; [intros a Ha; exact (proj1 (Hpres a ltac:(lia)))|]. split.
+ apply (range_addressable_of_block SEGS B LAWS ly S W memT mdT p n p 38 HART Hin); lia.
+ intros d k Hd Hdk Hk. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT p n d k HART Hin); lia.
- destruct (al_frames _ _ LAWS ly S W memT mdT cid pos HART Hfr) as (_ & _ & Hpres & _).
split; [intros a Ha; exact (proj1 (Hpres a ltac:(lia)))|]. split.
+ apply (range_addressable_entry_frame SEGS B LAWS STK sp0 [] ly S W mem md [] ly S W memT mdT 0 cid pos p 38 HJ Hfr Hcid Hlo Hhi Hal).
* intros x Hx. exfalso. exact (inFP_nil _ Hx).
* exact HAR.
* exact HRA.
+ intros d k Hd Hdk Hk. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W memT mdT cid pos d k HART Hfr); lia.
Qed.
(* The entry state of a null box: the frame below sp, the shadow GOT slot and the shadow cell. *)
Lemma famof_entry0 : forall ly S W (regs : bvmap 5 word) mem md ch (f0 f1 f2 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 0 -> 0 <= f0 < 2 ^ 32 -> 0 <= f1 < 2 ^ 32 -> 0 <= f2 < 2 ^ 32 ->
st_ok_pi SEGS VAL (EFO regs 0 f0 f1 f2)
(mkSS AF_reac_box_family_of sr_atoms [stack_region FAMOF_FRAME; got_regionP; bcell_regionP 32] None
(mkFacts (famof_atoms 0 0 0) [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_box_family_ofP) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch f0 f1 f2 HPRE H10 Hf0 Hf1 Hf2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := EFO regs 0 f0 f1 f2).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (famof_extra 0 f0 f1 f2)) n)
by (intros n Hn; subst E; unfold EFO; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_FO) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 f1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E31c : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold A_reac_box_family_ofP. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, FAMOF_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite E31c, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 31)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) E31c) by (pose proof (pa_val_range (A_OBJ 31)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 Bx_FO SB_FO);
[cbn [sv_denot Bx_FO]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_FO; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
unfold stack_region, got_regionP, bcell_regionP, extent_of_region, FAMOF_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) E31c) by (pose proof (pa_val_range (A_OBJ 31)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
repeat split; lia.
- pose proof (pa_obj_img 17 ltac:(lia)) as Htb.
pose proof (pa_val_range (A_OBJ 17)) as Htbr.
assert (E17 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17)))
by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
split; [|split; [exact I | exact I]].
cbn [famof_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E17.
rewrite !unsigned_lit_small by (unfold SB_FO; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hf0 Hf1 Hf2 Htb. clear.
unfold SB_FO. intros. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
(* The entry state of a box: the frame below sp, the shadow GOT slot, the shadow cell, the box's
   byte at +36 (atom 33) and the table's three family fields (atoms 34, 35, 36); the shadow
   entry of the box's 38 bytes. *)
Lemma famof_entry : forall ly S W (regs : bvmap 5 word) mem md ch (p b36 f0 f1 f2 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 p -> famof_box ly S W mem p ->
aview SEGS (w_H W) mem (p + 36) = Some b36 -> famof_tbl W mem f0 f1 f2 ->
st_ok_pi SEGS VAL (EFO regs b36 f0 f1 f2) ss_famof
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_box_family_ofP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_FO famof_SH (EFO regs b36 f0 f1 f2) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch p b36 f0 f1 f2 HPRE H10 Hbox Hb36 Htbl.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
destruct (famof_boxf ly S W mem md p HAR Hbox) as (Hp8 & Hp4096 & Hpceil & Happ & Hoff).
destruct Htbl as (Htr & Hf0 & V0 & Hf1 & V1 & Hf2 & V2).
destruct (aview_byte SEGS (w_H W) mem (p + 36) b36 Hb36) as (bb & _ & _ & Hb36r).
pose proof (famof_val_mem1 (w_H W) mem (p + 36) b36 Hb36) as Vb.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 17 ltac:(lia)) as Htb.
pose proof HWFSEP as [Hs1 Hs31]. pose proof HWFIMG as Himg.
unfold FAMOF_HWF in Hs1, Hs31, Himg, V0, V1, V2, Htr. unfold off_img in Hoff.
rewrite restrict_mkst_fx.
set (E := EFO regs b36 f0 f1 f2).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (famof_extra b36 f0 f1 f2)) n)
by (intros n Hn; subst E; unfold EFO; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_FO) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b36) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 f1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E31c : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E17 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (subst E; unfold EFO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Rg1. pose proof (pa_val_range (A_OBJ 31)) as Rg31. pose proof (pa_val_range (A_OBJ 17)) as Rg17.
assert (UB : U E Bx_FO = SHADOW_OFF).
{ unfold U, Bx_FO. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB_FO; lia). reflexivity. }
split.
- unfold ss_famof, A_reac_box_family_ofP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold famof_rs, stack_region, got_regionP, bcell_regionP, famof_box_region, famof_tbl_region, FAMOF_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g Rg1).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite E31c, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) E31c Rg31).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 Bx_FO SB_FO);
[cbn [sv_denot Bx_FO]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_FO; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 36 1 (SOff 33 0) b36);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb].
* rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) E17 Rg17).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 0 4 (SOff 34 0) f0);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact V0.
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 12 4 (SOff 35 0) f1);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V1].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 24 4 (SOff 36 0) f2);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
+ apply pairwise_disjoint_of_extents.
unfold famof_rs, stack_region, got_regionP, bcell_regionP, famof_box_region, famof_tbl_region, extent_of_region, FAMOF_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g Rg1), (VB (A_OBJ 31) (VAL (A_OBJ 31)) E31c Rg31), (VB (A_OBJ 17) (VAL (A_OBJ 17)) E17 Rg17).
rewrite (VB 10%nat p E10) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Htb Hs1 Hs31 Himg Hoff Hp4096 Hpceil. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [famof_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E17.
rewrite !unsigned_lit_small by (unfold SB_FO; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hf0 Hf1 Hf2 Htb Hb36r Hp8 Hp4096 Hpceil. clear.
unfold SB_FO. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, famof_SH. constructor; [|constructor].
destruct Hbox as [(n & Hin & Hn) | ((cid & pos & Hfr & Hcid & Hal & Hlo & Hhi) & _ & HRA)].
+ apply (shent_ok_of_block SEGS B LAWS ly S W mem md E Bx_FO 10 p n 0 38 HAR Hin UB (U_atom E 10 p E10 ltac:(lia))).
* lia.
* pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. lia.
+ apply (shent_ok_of_range SEGS (w_H W) mem E Bx_FO 10 p 38 p 0 38 HRA UB (U_atom E 10 p E10 ltac:(lia))); [lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
(* The UBSan alignment check at 0x82c44/0x82c48: an even box has bit 0 clear. *)
Lemma famof_land1 : forall x, 0 <= x -> x mod 2 = 0 -> Z.land x 1 = 0.
Proof.
intros x Hx H2. replace x with ((x / 2) * 2 ^ 1) by (pose proof (Z.div_mod x 2 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 1) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 1 n) with false; [apply andb_false_r|]. symmetry.
change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
(* The 32-bit signed load of a family field at the return. *)
Lemma famof_sx32_denot : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (famof_sx32 v).
Proof.
intros E n v Hn Hv.
rewrite denot_lit_U, U_SExt, (U_atom E n v Hn ltac:(lia)).
apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold zcanon, M64, bv_swrap, bv_half_modulus, famof_sx32, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (Z.of_N 32) with 32.
change (2 ^ 32 / 2) with (2 ^ 31).
rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct (Z.ltb_spec v (2 ^ 31)) as [Hlt | Hge].
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
rewrite Z.mod_mod by lia. f_equal. lia.
- replace (v + 2 ^ 31) with ((v + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (v + 2 ^ 31 - 2 ^ 32) (2 ^ 32)) by lia.
rewrite Z.mod_mod by lia. f_equal. lia.
Qed.
(* The bcmp call at 0x82c98: x = box + 28, y = HW_FAMILY + 4 + 12i, n = 8. The post states the
   row in the entry state's reader: both ranges are outside the call's window, so the journal's
   bytes are the entry state's bytes. *)
Lemma famof_call : forall ly S W (regs : bvmap 5 word) mem md ch p memT mdT (regsT : bvmap 5 word) (i retk : Z),
afn_pre SEGS B REAC_BOX_FAMILY_OF_STK ly S W regs mem md ch ->
famof_box ly S W mem p ->
(forall a, FAMOF_HWF <= a < FAMOF_HWF + 36 -> aview SEGS (w_H W) mem a <> None) ->
ajournal SEGS B REAC_BOX_FAMILY_OF_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
famof_keep regs W mem memT -> 0 <= i < 3 -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsT 10 = w64 (p + 28) -> getr regsT 11 = w64 (FAMOF_HWF + 4 + 12 * i) -> getr regsT 12 = w64 8 ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> spZ regsT = spZ regs - 64 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B REAC_BOX_FAMILY_OF_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF i) /\
famof_keep regs W mem mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 - 2 * ESTACK <= a < spZ regs - 64) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros ly S W regs mem md ch p memT mdT regsT i retk HPRE Hbox Htr HJ HKT Hi Hrk Hrk2 Ha0 Ha1 Ha2 Hra Hsp Hgp Htp.
pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
destruct (famof_boxf ly S W mem md p HAR Hbox) as (Hp8 & Hp4096 & Hpceil & Happ & Hoff).
destruct (famof_box_state ly S W mem md p REAC_BOX_FAMILY_OF_STK (spZ regs) memT mdT HAR Hbox HJ) as (Hbp & Hbra & Hbh).
pose proof HWFIMG as Himg. unfold FAMOF_HWF in Himg, Htr.
pose proof (proj1 HJ) as HART.
(* the table's bytes and shadow at memT *)
assert (HtrT : forall a, VAL (A_OBJ 17) <= a < VAL (A_OBJ 17) + 36 -> aview SEGS (w_H W) memT a <> None).
{ intros a Ha. rewrite (HKT a ltac:(lia) ltac:(lia)). exact (Htr a Ha). }
assert (HRO : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF (VAL (A_OBJ 17) + 4 + 12 * i) 8 /\
shadow_hull_vis (aview SEGS (w_H W) memT) (VAL (A_OBJ 17) + 4 + 12 * i) 8).
{ apply (ro_read_ok_glob SEGS B GL ly S W memT mdT FAMOF_HWF 36 (VAL (A_OBJ 17) + 4 + 12 * i) 8 GM HWFG IMGSH HART);
unfold FAMOF_HWF in *; try unfold IMG_HI in *; lia. }
destruct HRO as [HyRA HyH].
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W regsT memT
REAC_BOX_FAMILY_OF_STK (spZ regs) [] ly S W mem md [] ly S mdT 0 (p + 28) (VAL (A_OBJ 17) + 4 + 12 * i) 8 (-64)
(Z_to_bv 64 (BASE + retk)) HJ).
- exact Ha0. - unfold FAMOF_HWF in Ha1; exact Ha1. - exact Ha2. - lia.
- lia. - lia. - lia. - lia.
- rewrite Hsp. lia. - reflexivity. - lia. - rewrite WS, HES. lia.
- exact Hgp. - exact Htp. - exact Hra. - apply ret_ok_codeptr_v; [lia | exact Hrk2].
- intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hbp; lia | rewrite Hsp, HES; lia].
- intros a Ha. split; [apply HtrT; lia | rewrite Hsp, HES; lia].
- intros a Ha. lia.
- intros a Ha. lia.
- apply amem_range_high; [lia | | lia]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
- apply amem_range_high; [lia | lia | lia].
- apply (range_addressable_sub (aview SEGS (w_H W) memT) SHADOW_OFF p 38); [exact Hbra | lia | lia].
- intros _. apply (Hbh (p + 28) 8); lia.
- exact HyRA.
- intros _. exact HyH. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
assert (HK2 : famof_keep regs W mem mem2).
{ intros a Ha Hna. rewrite (Hfr2 a Ha ltac:(unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *; lia)).
exact (HKT a Ha Hna). }
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
split; [|split; [exact HK2 | split; [intros a Ha Hna; apply Hfr2; [exact Ha | lia] | exact Hpres2]]].
rewrite Hcmp. unfold famof_row, FAMOF_HWF. split.
- intros HQ j Hj.
rewrite <- (HKT (p + 28 + j) ltac:(lia) ltac:(unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *; lia)).
rewrite <- (HKT (VAL (A_OBJ 17) + 12 * i + 4 + j) ltac:(lia) ltac:(unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *; lia)).
replace (VAL (A_OBJ 17) + 12 * i + 4 + j) with (VAL (A_OBJ 17) + 4 + 12 * i + j) by lia.
replace (p + 28 + j) with (p + 28 + j) by lia. apply HQ. lia.
- intros HQ j Hj.
rewrite (HKT (p + 28 + j) ltac:(lia) ltac:(unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *; lia)).
rewrite (HKT (VAL (A_OBJ 17) + 4 + 12 * i + j) ltac:(lia) ltac:(unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *; lia)).
replace (VAL (A_OBJ 17) + 4 + 12 * i + j) with (VAL (A_OBJ 17) + 12 * i + 4 + j) by lia.
apply HQ. lia.
Qed.
(* Outside the windows of the state's regions a run keeps every byte. *)
Lemma famof_aview_frame : forall (W : world SEGS) E rs (m m' : word -> option byte) a,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' a HF Ha Hna. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hna)). reflexivity.
Qed.
(* A region is writable only in the frame below sp (atom 2), or not at all. *)
Definition famof_wr_ok (r : YP09.region) : bool :=
(match YP09.r_base r with Some 2%nat => true | _ => false end && (- FAMOF_FRAME <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0))
|| (YP09.r_whi r <=? YP09.r_wlo r).
Lemma famof_wrange : forall E rs a sp,
bv_unsigned (ew E 2) = sp -> forallb famof_wr_ok rs = true ->
in_wrange E rs a -> sp - FAMOF_FRAME <= a < sp.
Proof.
intros E rs a sp Hsp Hok (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr1. unfold famof_wr_ok in Hr1.
destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr, Hr1.
apply Bool.orb_true_iff in Hr1 as [Hr1 | Hr1].
- destruct rb as [[|[|[|]]]|]; cbn in Hr1; try discriminate.
apply andb_true_iff in Hr1 as [Hr1 Hr2]. apply Z.leb_le in Hr1, Hr2.
cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
- apply Z.leb_le in Hr1. lia.
Qed.
(* A run whose state's regions pass famof_wr_ok keeps what the call keeps. *)
Lemma famof_keep_run : forall (regs : bvmap 5 word) W mem m1 m2 E rs,
famof_keep regs W mem m1 ->
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
bv_unsigned (ew E 2) = spZ regs -> forallb famof_wr_ok rs = true ->
famof_keep regs W mem m2.
Proof.
intros regs W mem m1 m2 E rs HK HF Hsp Hok a Ha Hna.
rewrite (famof_aview_frame W E rs m1 m2 a HF Ha); [apply HK; assumption|].
intros Hin. apply (famof_wrange E rs a (spZ regs) Hsp Hok) in Hin.
unfold REAC_BOX_FAMILY_OF_STK, FAMOF_FRAME, ESTACK in *. lia.
Qed.
(* A null box: the function stores its frame, takes the branch at AF + 0x20 and returns 0. *)
Lemma famof_null : forall ly S W (regs : bvmap 5 word) mem md ch (f0 f1 f2 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 0 -> 0 <= f0 < 2 ^ 32 -> 0 <= f1 < 2 ^ 32 -> 0 <= f2 < 2 ^ 32 ->
SRr SEGS W (cfg_at SEGS A_reac_box_family_ofP regs mem md)
(treac_box_family_of_post regs ly S W mem md 0 f0 f1 f2).
Proof.
intros ly S W regs mem md ch f0 f1 f2 HPRE H10 Hf0 Hf1 Hf2.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (famof_entry0 ly S W regs mem md ch f0 f1 f2 HPRE H10 Hf0 Hf1 Hf2) as HS.
pose proof (ajournal_init SEGS B REAC_BOX_FAMILY_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
remember (EFO regs 0 f0 f1 f2) as E eqn:HE.
assert (SHOK : sh_ok SEGS Bx_FO [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EFO; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (famof_extra 0 f0 f1 f2)) n)
by (intros n Hn; subst E; unfold EFO; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (famof_extra 0 f0 f1 f2)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at, A_reac_box_family_ofP.
change (w64 (BASE + AF_reac_box_family_of)) with (Z_to_bv 64 (BASE + AF_reac_box_family_of)).
paj_run_tok RUN HS HJ SHOK Bspan_FO;
[awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
assert (HM0 : famof_keep regs W mem mem) by (intros a _ _; reflexivity).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (HM : famof_keep regs W mem m2)
by (apply (famof_keep_run regs W mem m1 m2 Ex rs HM0 HFr); [exact Usp | vm_compute; reflexivity]) end.
clear HM0. repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the branch at AF + 0x20 (beqz a0): taken, a0 = 0 *)
psrr_branch_tok RUN BR HS SHOK Bspan_FO;
[ | exfalso; rewrite branch_eq_U, (U_atom E 10 0 E10) in Hc by lia; vm_compute in Hc; discriminate Hc ].
paj_run_tok RUN HS HJ SHOK Bspan_FO;
[awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HM : famof_keep _ _ _ ?m1 |- _ =>
let HM2 := fresh "HM" in
assert (HM2 : famof_keep regs W mem m2)
by (apply (famof_keep_run regs W mem m1 m2 Ex rs HM HFr); [exact Usp | vm_compute; reflexivity]);
clear HM; rename HM2 into HM end.
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_box_family_of_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (famof_extra 0 f0 f1 f2) HS);
[exact HAE | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HM|];
exists 0; split; [left; split; reflexivity|];
cbn [ms_regs]; rewrite R10; unfold famof_sx32; cbn [Z.ltb Z.compare]; exact E10
end.
Qed.
(* The branch on the bcmp result (beqz a0 at 0x82c9c): taken iff the result is 0. *)
Lemma famof_br_eq : forall E n (v : word), ew E n = v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros E n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma famof_br_ne : forall E n (v : word), ew E n = v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros E n v Hn Hb Hv. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.
(* --- the walk's tactics ---------------------------------------------------------------- *)
(* Every run extends the environment with the atoms it loads (ewset) and every call havocs it
   above A_LIM; these rewrites take a goal about the environment in hand back to the entry
   environment, where the walk's facts (E1, E2, E10, E17, E32..E36, Usp) are stated. *)
Ltac famof_env_old := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ].
(* One run: to the next branch, call or return; the kept-bytes fact follows it. *)
Ltac famof_run_step RUN Bspan Usp :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; famof_env_old; exact Usp |] end;
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HMo : famof_keep ?rg ?Wd ?mm ?m1 |- _ =>
let HM2 := fresh "HM" in
assert (HM2 : famof_keep rg Wd mm m2)
by (apply (famof_keep_run rg Wd mm m1 m2 Ex rs HMo HFr);
[cbn [ew ewset Nat.eqb]; famof_env_old; exact Usp | vm_compute; reflexivity]);
clear HMo end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* The return at 0x82cec with result r: the post up to the famof_res goal and the equation of a0. *)
Ltac famof_leaf RETt Wv lyv Sv regsv xtra E1v Hrav HAEv LAWSv Hsegsv r :=
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msc), HMk : famof_keep _ _ _ (ms_mem ?msc) |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
pose proof (st_ok_pi_restrict_reg _ _ _ _ (10%bv : bv 5) HS) as R10;
let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in R10;
cbn [ms_regs restrict mkst] in R10;
prreg HS (1%bv : bv 5) R1;
eapply (RETt Wv _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_box_family_of_post, apost_base;
exists lyv, Sv, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; famof_env_old; rewrite E1v, Hrav; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWSv Hsegsv); assumption|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regsv xtra HS);
[ split; [intros nn Hnn; famof_env_old; exact (proj1 HAEv nn Hnn) | cbn [ed ewset havoc]; exact (proj2 HAEv)]
| vm_compute; reflexivity ]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HMk|];
exists r; split; [ | cbn [ms_regs]; rewrite R10 ]
end.
(* The bcmp result's atom after a call: ew (havoc X K (map (getr regs') CLOB)) (K + 4) = a0. *)
Ltac famof_hv Hv :=
repeat rewrite ew_ewset_other by lia;
lazymatch goal with |- ew (havoc _ ?K _) ?n = _ =>
let j := eval vm_compute in (n - K)%nat in
change n with (K + j)%nat; rewrite (YN3v.ew_havoc_new _ K _ j (Z_to_bv 64 0)) by (cbn; lia);
cbn [nth map CLOB]; exact Hv end.
(* The walk. A null box: famof_null. A box at p <> 0: run 1 takes the prologue, the null test,
   the UBSan alignment test (decided by atom 10's 8-alignment), the box's shadow test (the
   shadow entry famof_SH) and the load of the byte at p+36, and stops at its test (0x82c70).
   A zero byte returns 0. Otherwise each of the three loop rounds runs to the bcmp call, takes
   famof_call for row i, rebuilds the symbolic state after the call (jafter_call_keep_hi: the
   five regions are kept, the caller-saved registers become fresh atoms, the table's shadow
   entry is re-made from the new state's AR by ro_usable_glob) and branches on the result
   (0x82c9c): 0 runs through the table's shadow test and the load of the family field to the
   return; not 0 goes on to the next row, and after row 2 to the return of 0. *)
Theorem pb_reac_box_family_of : treac_box_family_of_spec.
Proof.
unfold treac_box_family_of_spec.
intros ly S W regs mem md ch p f0 f1 f2 HPRE H10 Hp Hbox Htbl.
pose proof Htbl as (_ & Hf0 & _ & Hf1 & _ & Hf2 & _).
destruct (Z.eq_dec p 0) as [-> | Hp0].
{ exact (famof_null ly S W regs mem md ch f0 f1 f2 HPRE H10 Hf0 Hf1 Hf2). }
specialize (Hbox Hp0).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (famof_boxf ly S W mem md p HAR Hbox) as (Hp8 & Hp4096 & Hpceil & Happ & Hoff).
pose proof (ajournal_init SEGS B REAC_BOX_FAMILY_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
destruct (famof_box_state ly S W mem md p REAC_BOX_FAMILY_OF_STK (spZ regs) mem md HAR Hbox HJ) as (Hbp & _ & _).
destruct (aview SEGS (w_H W) mem (p + 36)) as [b36|] eqn:Hb36;
[| exfalso; exact (aview_some_of_apresent SEGS _ _ _ (Hbp (p + 36) ltac:(lia)) Hb36)].
destruct (aview_byte SEGS (w_H W) mem (p + 36) b36 Hb36) as (_ & _ & _ & Hb36r).
destruct (famof_entry ly S W regs mem md ch p b36 f0 f1 f2 HPRE H10 Hbox Hb36 Htbl) as [HS SHOK].
remember (EFO regs b36 f0 f1 f2) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EFO; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (famof_extra b36 f0 f1 f2)) n)
by (intros n Hn; subst E; unfold EFO; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 b36) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 f1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_FO) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs (famof_extra b36 f0 f1 f2)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at, A_reac_box_family_ofP.
change (w64 (BASE + AF_reac_box_family_of)) with (Z_to_bv 64 (BASE + AF_reac_box_family_of)).
assert (HM : famof_keep regs W mem mem) by (intros a _ _; reflexivity).
assert (Htr : forall a, FAMOF_HWF <= a < FAMOF_HWF + 36 -> aview SEGS (w_H W) mem a <> None) by (apply Htbl).
assert (E17 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (apply (img_env_atomP E (A_OBJ 17) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 17 ltac:(lia)) as Htb17. pose proof (pa_val_range (A_OBJ 17)) as Rg17.
pose proof (pa_obj_img 1 ltac:(lia)) as Hobj1. pose proof (pa_obj_img 31 ltac:(lia)) as Hobj31.
assert (WS : REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (Hspr : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (E10u : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
(* run 1: the prologue, the null test, the UBSan alignment test (not taken: the box is even),
   the shadow test and the load of the byte at box+36; it stops at the branch on that byte. *)
famof_run_step RUN Bspan_FO Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
{ (* the byte at box+36 is 0: the function returns 0 *)
assert (Hb0 : b36 = 0).
{ lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff 33 0)) _ = _ =>
pose proof (famof_br_eq Ev 33 (Z_to_bv 64 b36) ltac:(famof_env_old; exact E33) Hc) as Hz end.
apply (f_equal bv_unsigned) in Hz. rewrite !unsigned_lit_small in Hz by lia. exact Hz. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
famof_leaf RET W ly S regs (famof_extra b36 f0 f1 f2) E1 Hra HAE LAWS Hsegs 0.
- right; left. split; [exact Hp0|]. split; [rewrite Hb36, Hb0; reflexivity | reflexivity].
- reflexivity. }
(* the byte is not 0: the loop, row 0 *)
assert (Hb36ne : b36 <> 0).
{ intros ->.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
rewrite branch_eq_U, (U_atom Ev 33 0 ltac:(famof_env_old; exact E33) ltac:(lia)) in Hc end.
vm_compute in Hc. discriminate Hc. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
(* the call of the bcmp wrapper for row 0 (0x82c98): a0 = box+28, a1 = HW_FAMILY+4, a2 = 8 *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx), HMo : famof_keep _ _ _ ?mx |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
pmkst HS;
eapply SRr_bind;
[ eapply (famof_call ly S W regs mem md ch p mx _ (ms_regs msx) 0 9512 HPRE Hbox Htr HJ HMo);
[ lia | lia | reflexivity
| rewrite Ra0, E10, (unsigned_lit_small p) by lia; reflexivity
| rewrite Ra1; change 258%nat with (A_OBJ 17); rewrite E17, (unsigned_lit_small (VAL (A_OBJ 17))) by lia; unfold FAMOF_HWF; f_equal; lia
| rewrite Ra2; reflexivity
| rewrite Rra; reflexivity
| unfold spZ; rewrite Rsp, E2, Hspr; rewrite (unsigned_lit_small (spZ regs + -64)) by lia; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp ]
| ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v0 & -> & HJ2 & HP2 & Hv0 & Hc0 & HM2 & Hfr0 & Hpres2).
clear HJ. repeat match goal with H : famof_keep _ _ _ ?m |- _ => tryif constr_eq m mem2 then fail else clear H end.
(* the symbolic state after the call: the five regions are kept, the caller-saved registers are
   fresh atoms, and the table's shadow is re-derived from the new state's own AR. *)
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_FO famof_SH ssx) in
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2;3;4]%nat HS2 end.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS2 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
all: eapply region_kept_aview;
[ first [ exact Usp | exact E10u
| exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 31) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ]
| intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr0; lia
| exact Hpres2 ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
assert (HEIa : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
assert (SHOKa : sh_ok SEGS Bx_FO famof_SHT Ev (mrestrict (w_H W) mem2));
[ unfold sh_ok, famof_SHT; apply Forall_cons; [ | apply Forall_nil ];
apply (shent_ok_of_range SEGS (w_H W) mem2 Ev Bx_FO (A_OBJ 17) (VAL (A_OBJ 17)) 36 (VAL (A_OBJ 17)) 0 36
(ro_usable_glob SEGS B GL ly S W mem2 md2 FAMOF_HWF 36 (VAL (A_OBJ 17)) 36 GM HWFG (proj1 HJ2)
ltac:(unfold FAMOF_HWF; lia) ltac:(unfold FAMOF_HWF; lia)));
[ unfold U, Bx_FO; cbn [sv_denot]; famof_env_old; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite unsigned_lit_small by (unfold SB_FO; lia); reflexivity
| exact (U_img_atom Ev HEIa (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| lia | lia
| intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia ]
| ] end.
clear SHOK. rename SHOKa into SHOK.
famof_run_step RUN Bspan_FO Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
{ (* the bcmp result is 0: row 0 matches *)
assert (Hm0 : famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 0).
{ apply Hc0. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_eq Ev n v0); [ famof_hv Hv0 | exact Hc ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
famof_leaf RET W ly S regs (famof_extra b36 f0 f1 f2) E1 Hra HAE LAWS Hsegs f0.
- right; right; left. split; [exact Hp0|]. split; [rewrite Hb36; intros Hq; apply Hb36ne; injection Hq as Hq; exact Hq|].
split; [exact Hm0 | reflexivity].
- apply famof_sx32_denot; [famof_env_old; exact E34 | lia]. }
(* the bcmp result is not 0: row 0 does not match; the loop goes on to row 1 *)
assert (Hn0 : ~ famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 0).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_ne Ev n v0); [ famof_hv Hv0 | exact Hc | apply Hc0; exact Hrow ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
(* the call of the bcmp wrapper for row 1: a1 = HW_FAMILY+16 *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx), HMo : famof_keep _ _ _ ?mx,
HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
prreg HS (10%bv : bv 5) Rb0; prreg HS (11%bv : bv 5) Rb1; prreg HS (12%bv : bv 5) Rb2;
prreg HS (1%bv : bv 5) Rbra; prreg HS (2%bv : bv 5) Rbsp; prreg HS (3%bv : bv 5) Rbgp; prreg HS (4%bv : bv 5) Rbtp;
pmkst HS;
eapply SRr_bind;
[ eapply (famof_call ly S W regs mem md ch p mx _ (ms_regs msx) 1 9512 HPRE Hbox Htr HJx HMo);
[ lia | lia | reflexivity
| rewrite Rb0; famof_env_old; rewrite E10, (unsigned_lit_small p) by lia; reflexivity
| rewrite Rb1; famof_env_old; change 258%nat with (A_OBJ 17); rewrite E17, (unsigned_lit_small (VAL (A_OBJ 17))) by lia;
unfold FAMOF_HWF; f_equal; lia
| rewrite Rb2; reflexivity
| rewrite Rbra; reflexivity
| unfold spZ; rewrite Rbsp; famof_env_old; rewrite E2, Hspr; rewrite (unsigned_lit_small (spZ regs + -64)) by lia; lia
| rewrite Rbgp; famof_env_old; rewrite E3; exact Hgp
| rewrite Rbtp; famof_env_old; rewrite E4; exact Htp ]
| ] end.
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v1 & -> & HJ3 & HP3 & Hv1 & Hc1 & HM3 & Hfr1 & Hpres3).
repeat match goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m _ _ |- _ => tryif constr_eq m mem3 then fail else clear H end.
repeat match goal with H : famof_keep _ _ _ ?m |- _ => tryif constr_eq m mem3 then fail else clear H end.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_FO famof_SHT ssx) in
jafter_call_keep_hi HS K regs3 (mrestrict (w_H W) mem3) HP3 [0;1;2;3;4]%nat HS3 end.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
all: eapply region_kept_aview;
[ first [ exact Usp | exact E10u
| exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 31) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ]
| intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr1; lia
| exact Hpres3 ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
assert (HEIb : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
assert (SHOKb : sh_ok SEGS Bx_FO famof_SHT Ev (mrestrict (w_H W) mem3));
[ unfold sh_ok, famof_SHT; apply Forall_cons; [ | apply Forall_nil ];
apply (shent_ok_of_range SEGS (w_H W) mem3 Ev Bx_FO (A_OBJ 17) (VAL (A_OBJ 17)) 36 (VAL (A_OBJ 17)) 0 36
(ro_usable_glob SEGS B GL ly S W mem3 md3 FAMOF_HWF 36 (VAL (A_OBJ 17)) 36 GM HWFG (proj1 HJ3)
ltac:(unfold FAMOF_HWF; lia) ltac:(unfold FAMOF_HWF; lia)));
[ unfold U, Bx_FO; cbn [sv_denot]; famof_env_old; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite unsigned_lit_small by (unfold SB_FO; lia); reflexivity
| exact (U_img_atom Ev HEIb (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| lia | lia
| intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia ]
| ] end.
clear SHOK. rename SHOKb into SHOK.
famof_run_step RUN Bspan_FO Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
{ (* the bcmp result is 0: row 1 matches *)
assert (Hm1 : famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 1).
{ apply Hc1. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_eq Ev n v1); [ famof_hv Hv1 | exact Hc ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
famof_leaf RET W ly S regs (famof_extra b36 f0 f1 f2) E1 Hra HAE LAWS Hsegs f1.
- right; right; right; left. split; [exact Hp0|]. split; [rewrite Hb36; intros Hq; apply Hb36ne; injection Hq as Hq; exact Hq|].
split; [exact Hn0|]. split; [exact Hm1 | reflexivity].
- apply famof_sx32_denot; [famof_env_old; exact E35 | lia]. }
(* row 1 does not match; the loop goes on to row 2 *)
assert (Hn1 : ~ famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 1).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_ne Ev n v1); [ famof_hv Hv1 | exact Hc | apply Hc1; exact Hrow ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
(* the call of the bcmp wrapper for row 2: a1 = HW_FAMILY+28 *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx), HMo : famof_keep _ _ _ ?mx,
HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
prreg HS (10%bv : bv 5) Rc0; prreg HS (11%bv : bv 5) Rc1; prreg HS (12%bv : bv 5) Rc2;
prreg HS (1%bv : bv 5) Rcra; prreg HS (2%bv : bv 5) Rcsp; prreg HS (3%bv : bv 5) Rcgp; prreg HS (4%bv : bv 5) Rctp;
pmkst HS;
eapply SRr_bind;
[ eapply (famof_call ly S W regs mem md ch p mx _ (ms_regs msx) 2 9512 HPRE Hbox Htr HJx HMo);
[ lia | lia | reflexivity
| rewrite Rc0; famof_env_old; rewrite E10, (unsigned_lit_small p) by lia; reflexivity
| rewrite Rc1; famof_env_old; change 258%nat with (A_OBJ 17); rewrite E17, (unsigned_lit_small (VAL (A_OBJ 17))) by lia;
unfold FAMOF_HWF; f_equal; lia
| rewrite Rc2; reflexivity
| rewrite Rcra; reflexivity
| unfold spZ; rewrite Rcsp; famof_env_old; rewrite E2, Hspr; rewrite (unsigned_lit_small (spZ regs + -64)) by lia; lia
| rewrite Rcgp; famof_env_old; rewrite E3; exact Hgp
| rewrite Rctp; famof_env_old; rewrite E4; exact Htp ]
| ] end.
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v2 & -> & HJ4 & HP4 & Hv2 & Hc2 & HM4 & Hfr2 & Hpres4).
repeat match goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m _ _ |- _ => tryif constr_eq m mem4 then fail else clear H end.
repeat match goal with H : famof_keep _ _ _ ?m |- _ => tryif constr_eq m mem4 then fail else clear H end.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_FO famof_SHT ssx) in
jafter_call_keep_hi HS K regs4 (mrestrict (w_H W) mem4) HP4 [0;1;2;3;4]%nat HS4 end.
match type of HS4 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS4 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
all: eapply region_kept_aview;
[ first [ exact Usp | exact E10u
| exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 31) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (HEI (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ]
| intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr2; lia
| exact Hpres4 ]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
assert (HEIc : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
assert (SHOKc : sh_ok SEGS Bx_FO famof_SHT Ev (mrestrict (w_H W) mem4));
[ unfold sh_ok, famof_SHT; apply Forall_cons; [ | apply Forall_nil ];
apply (shent_ok_of_range SEGS (w_H W) mem4 Ev Bx_FO (A_OBJ 17) (VAL (A_OBJ 17)) 36 (VAL (A_OBJ 17)) 0 36
(ro_usable_glob SEGS B GL ly S W mem4 md4 FAMOF_HWF 36 (VAL (A_OBJ 17)) 36 GM HWFG (proj1 HJ4)
ltac:(unfold FAMOF_HWF; lia) ltac:(unfold FAMOF_HWF; lia)));
[ unfold U, Bx_FO; cbn [sv_denot]; famof_env_old; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite unsigned_lit_small by (unfold SB_FO; lia); reflexivity
| exact (U_img_atom Ev HEIc (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| lia | lia
| intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia ]
| ] end.
clear SHOK. rename SHOKc into SHOK.
famof_run_step RUN Bspan_FO Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
{ (* the bcmp result is 0: row 2 matches *)
assert (Hm2 : famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 2).
{ apply Hc2. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_eq Ev n v2); [ famof_hv Hv2 | exact Hc ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
famof_leaf RET W ly S regs (famof_extra b36 f0 f1 f2) E1 Hra HAE LAWS Hsegs f2.
- right; right; right; right; left. split; [exact Hp0|]. split; [rewrite Hb36; intros Hq; apply Hb36ne; injection Hq as Hq; exact Hq|].
split; [exact Hn0|]. split; [exact Hn1|]. split; [exact Hm2 | reflexivity].
- apply famof_sx32_denot; [famof_env_old; exact E36 | lia]. }
(* no row matches: the loop ends (0x82ca8 not taken) and the function returns 0 *)
assert (Hn2 : ~ famof_row (aview SEGS (w_H W) mem) p FAMOF_HWF 2).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
apply (famof_br_ne Ev n v2); [ famof_hv Hv2 | exact Hc | apply Hc2; exact Hrow ] end. }
clear Hc.
famof_run_step RUN Bspan_FO Usp.
famof_leaf RET W ly S regs (famof_extra b36 f0 f1 f2) E1 Hra HAE LAWS Hsegs 0.
- right; right; right; right; right. split; [exact Hp0|]. split; [rewrite Hb36; intros Hq; apply Hb36ne; injection Hq as Hq; exact Hq|].
split; [exact Hn0|]. split; [exact Hn1|]. split; [exact Hn2 | reflexivity].
- reflexivity.
Qed.
End h.
End f.
End d.

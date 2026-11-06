(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACik.v:90-93, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, with its numbers changed; 745 of its 871 lines of code are new or changed and 529 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), piece `stem`: +0x1440 .. +0x14c8
   (0x81bb4 .. 0x81c3c), from the cut jc1 to the cut jc2 of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v.
   The code chooses the string the expected name starts from:
     0x81bb4            x27 (the record's has_model_name byte) zero goes to 0x81bc4;
     0x81bb8, 0x81bbc   a0 := the word at mf+136 (&id + 3, the model-name field), then a0 := its first byte;
     0x81bc0            that byte non-zero goes to 0x81c3c: the stem is the field and mf+136 keeps its value;
     0x81bc4 .. 0x81bcc x18 := the family minus one (32-bit); above 2 (unsigned) goes to 0x81c30, where a0 := the
                        address of "REAC" (object 8, 0x81c30 .. 0x81c34);
     0x81bd0 .. 0x81bf0 else a0 := the address of entry family-1 of switch.table.LLVMFuzzerTestOneInput (object 7);
                        the shadow byte of that entry ((a0 >> 3) + x12, x12 the shadow base) zero, else the report
                        at 0x827f8; then a0 := the entry;
     0x81c38            the word at mf+136 := a0.
   The walk runs the symbolic engine with the shadow tokens of lib/A/Prog/PaShadow.v over a state of three regions:
   the machine-frame word mf+136 (writable), the first byte of the model-name field and the switch table.
   Section hypotheses beyond the statement's premises: HSTK (the window mf+136 lies in the entry's stack) and the
   prefix file's HRO and HIMG (llvmf_img at every state of the journal, as its j_img). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require disco_box_name_model reac_box_family_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_name_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow addresses below need it (as in
   LLVMFuzzerTestOneInput_seg_J_pre.v). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model: the stem's bytes ------------------------------------------------------------------ *)
Lemma js_nth_fs : forall (A : Type) (l : list A) k n j d, (j < n)%nat ->
nth j (firstn n (skipn k l)) d = nth (k + j) l d.
Proof.
intros A l k n j d Hj. revert l. induction k as [|k IH]; intros l.
- cbn [skipn Nat.add]. revert l j Hj. induction n as [|n IHn]; intros l j Hj; [lia|].
  destruct l as [|x l]; [destruct j; reflexivity|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IHn. lia.
- destruct l as [|x l].
  + cbn [skipn]. rewrite firstn_nil. destruct j; reflexivity.
  + cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma js_garr8_sub : forall segs m a (l : list Z) k n, (k + n <= length l)%nat ->
garr8 segs m a l -> garr8 segs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
intros segs m a l k n Hkn H j Hj. rewrite length_firstn, length_skipn in Hj.
rewrite (js_nth_fs Z l k n j 0) by lia. destruct (H (k + j)%nat ltac:(lia)) as [Hv Hr].
split; [|exact Hr]. replace (a + Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (k + j)) by lia. exact Hv.
Qed.
Lemma js_fz_spec : forall M : list byte, (RcIdentModel.first_zero M < length M)%nat ->
map (fun b : byte => bv_unsigned b) (firstn (RcIdentModel.first_zero M) M ++ [RcIdentModel.zb 0]) =
map (fun b : byte => bv_unsigned b) (firstn (S (RcIdentModel.first_zero M)) M).
Proof.
induction M as [|b r IH]; [cbn; intros H; lia|].
cbn [RcIdentModel.first_zero length].
destruct (Z.eqb_spec (RcIdentModel.bz b) 0) as [E|E]; intros H.
- cbn [firstn app map]. unfold RcIdentModel.bz in E. rewrite E. vm_compute. reflexivity.
- cbn [firstn app map]. f_equal. apply IH. lia.
Qed.
Lemma js_fz_le : forall (M : list byte) i, (i < length M)%nat -> RcIdentModel.bz (nth i M (RcIdentModel.zb 0)) = 0 ->
(RcIdentModel.first_zero M <= i)%nat.
Proof.
induction M as [|b r IH]; intros i Hi Hz; [cbn in Hi; lia|].
cbn [RcIdentModel.first_zero]. destruct (Z.eqb_spec (RcIdentModel.bz b) 0) as [E|E]; [lia|].
destruct i as [|i]; [cbn [nth] in Hz; contradiction|].
cbn [nth length] in Hz, Hi. specialize (IH i ltac:(lia) Hz). lia.
Qed.
(* A named model: the stem is `id.model_name` up to its first NUL, which is inside the field (byte 19 of every
   record is 0, SlotModel.rec_id_b19); its bytes and the NUL are bytes 3 .. 3 + len of `id`. *)
Lemma js_said_bytes : forall segs m a (idb : list byte),
length idb = RcIdentModel.ID_SIZE -> RcIdentModel.bz (RcIdentModel.nthb idb 19) = 0 ->
garr8 segs m a (map (fun b : byte => bv_unsigned b) idb) ->
garr8 segs m (a + 3) (map (fun b : byte => bv_unsigned b) (SlotModel.name_str idb ++ [RcIdentModel.zb 0])) /\
(length (SlotModel.name_str idb) <= 16)%nat.
Proof.
intros segs m a idb Hl H19 Hg. unfold RcIdentModel.ID_SIZE in Hl.
assert (EN : SlotModel.name_str idb =
firstn (RcIdentModel.first_zero (firstn 17 (skipn 3 idb))) (firstn 17 (skipn 3 idb))) by reflexivity.
assert (LM : length (firstn 17 (skipn 3 idb)) = 17%nat) by (rewrite length_firstn, length_skipn; lia).
assert (N16 : nth 16 (firstn 17 (skipn 3 idb)) (RcIdentModel.zb 0) = nth 19 idb (RcIdentModel.zb 0))
by (apply (js_nth_fs byte idb 3 17 16); lia).
assert (FZ : (RcIdentModel.first_zero (firstn 17 (skipn 3 idb)) <= 16)%nat).
{ apply js_fz_le; [lia|]. rewrite N16. exact H19. }
rewrite EN. split; [|rewrite length_firstn; lia].
rewrite js_fz_spec by lia. rewrite firstn_firstn.
replace (Nat.min (S (RcIdentModel.first_zero (firstn 17 (skipn 3 idb)))) 17)
with (S (RcIdentModel.first_zero (firstn 17 (skipn 3 idb)))) by lia.
rewrite <- firstn_map, <- skipn_map.
replace (a + 3) with (a + Z.of_nat 3) by reflexivity.
apply js_garr8_sub; [rewrite length_map; lia | exact Hg].
Qed.
(* The family's string in the image: SlotModel.stem_img against reac_box_name's bn_STEM (as
   lib/U/Prog/Seg/G07.v g7_STEM). *)
Lemma js_stem_img_map : forall f,
map (fun b : byte => bv_unsigned b) (SlotModel.stem_img f ++ [RcIdentModel.zb 0]) =
disco_box_name_model.bn_STEM f ++ [0] /\
length (SlotModel.stem_img f) = length (disco_box_name_model.bn_STEM f).
Proof.
intros f. unfold disco_box_name_model.bn_STEM, SlotModel.stem_img.
destruct (f =? 1); [vm_compute; split; reflexivity|].
destruct (f =? 2); [vm_compute; split; reflexivity|].
destruct (f =? 3); vm_compute; split; reflexivity.
Qed.
Lemma js_stem_other : forall f, ~ (1 <= f <= 3) -> SlotModel.stem_img f = SlotModel.stem_img 0.
Proof.
intros f Hf. unfold SlotModel.stem_img.
destruct (Z.eqb_spec f 1); [lia|]. destruct (Z.eqb_spec f 2); [lia|]. destruct (Z.eqb_spec f 3); [lia|].
reflexivity.
Qed.
Lemma js_mn0 : forall idb : list byte, (4 <= length idb)%nat ->
RcIdentModel.bz (RcIdentModel.nthb (RcIdentModel.model_name idb) 0) =
nth 3 (map (fun b : byte => bv_unsigned b) idb) 0.
Proof. intros idb H. destruct idb as [|a [|b [|c [|d r]]]]; cbn [length] in H; try lia. reflexivity. Qed.
Lemma js_nfam_range : forall inp, 0 <= SlotModel.n_fam inp <= 127.
Proof.
intros inp. unfold SlotModel.n_fam. destruct (128 <=? SlotModel.t_fam_raw inp).
- replace (Z.land (SlotModel.t_fam_raw inp) 127) with (SlotModel.t_fam_raw inp mod 2 ^ 7)
  by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound (SlotModel.t_fam_raw inp) (2 ^ 7) ltac:(lia)). change (2 ^ 7) with 128 in *. lia.
- unfold SlotModel.FAM, reac_box_family_of_c.FAMOF_FAM.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.
Lemma js_tok_len : forall d (l : list byte), (length (SlotModel.tok_go d l) <= length l)%nat.
Proof.
intros d l. revert d. induction l as [|b r IH]; intros d; cbn [SlotModel.tok_go length]; [lia|].
match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length];
[specialize (IH true) | specialize (IH d)]; lia.
Qed.
(* Membership in a literal list of registers, without tauto (which can pull Section hypotheses into a proof). *)
Local Ltac js_inl := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma js_fam_cases : forall f : Z, f = 1 \/ f = 2 \/ f = 3 \/ ~ (1 <= f <= 3).
Proof. intros f. lia. Qed.
(* The bounds test at 0x81bcc for a family outside 1..3: 2 <u (f - 1 as an int) (reac_box_family_stem.v's
   fs_bltu_other, on x18). *)
Lemma js_bltu_other : forall E f, ew E 18 = Z_to_bv 64 f -> - 2 ^ 31 <= f < 2 ^ 31 -> ~ (1 <= f <= 3) ->
branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 18 0) (SLit (-1)))) = true.
Proof.
intros E f H Hf Hn. rewrite branch_ltu_U, U_SLit, U_of_S, S_SAluw, U_SOff, U_SLit, H, Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw]. apply Z.ltb_lt.
assert (A1 : zcanon (bv_wrap 64 f) mod 2 ^ 32 = f mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  Z.div_mod_to_equations; lia. }
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by reflexivity.
replace (zcanon 2) with 2 by reflexivity.
rewrite A1. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z_lt_le_dec f 1); Z.div_mod_to_equations; lia.
Qed.

(* ---- the symbolic state at 0x81bb4 (+0x1440) --------------------------------------------------------------
   Region 0: the machine-frame word mf+136 (base s1, atom 9), writable; it holds &id + 3 (atom 32 is the frame
   address, so SOff 32 355). Region 1: the first byte of id.model_name (frame + 355), read-only, its value atom 33.
   Region 2: switch.table.LLVMFuzzerTestOneInput (object 7), read-only, its three words atoms 34, 35, 36. The facts:
   mf is a 32-aligned stack address, x12 holds the shadow base (the base the shadow test of 0x81be4 adds), the
   byte is a byte, and the table is an 8-aligned image object. *)
Definition js_mf : YP09.region := YP09.mkRegion (Some 9%nat) 136 144 136 144 [YP09.mkChunk 136 (CVal 8 (SOff 32 355))].
Definition js_id : YP09.region := YP09.mkRegion (Some 32%nat) 355 356 355 355 [YP09.mkChunk 355 (CVal 1 (SOff 33 0))].
Definition js_tb : YP09.region := YP09.mkRegion (Some (A_OBJ 7)) 0 24 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0))].
Definition js_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (12%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
(33%nat, mkAF 0 255 0); (A_OBJ 7, mkAF IMG_LO (IMG_TOP - 8) 3)] [] [].
Definition ss_js : sstate := mkSS 0x1440 sr_atoms [js_mf; js_id; js_tb] None js_facts.
Definition js_Bx : sv := SOff 12 0.
Definition js_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition js_SH : list shent := [mkSHE (A_OBJ 7) 0 24].

(* Every write window of the segment's states is mf+136 .. mf+144: the regions keep their bases and windows. *)
Lemma js_win : forall E rs mf, windows rs = windows [js_mf; js_id; js_tb] -> bv_unsigned (ew E 9) = mf ->
forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
mf + 136 <= a < mf + 144.
Proof.
intros E rs mf Hw H9 b wlo whi a Hi Hr. rewrite Hw in Hi.
cbn [windows map js_mf js_id js_tb YP09.r_base YP09.r_wlo YP09.r_whi In] in Hi.
destruct Hi as [Hi|[Hi|[Hi|[]]]]; injection Hi as <- <- <-.
- cbn [base_val] in Hr. rewrite H9 in Hr. lia.
- lia.
- lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation JKEEP := (jkeep B).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC2 := (jc2 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JSTEM := (jstem B LLVMF_STK).
#[local] Notation AJ g pos ly S W mem md k := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
(e_mem g) (e_md g) [(4, pos)] ly S W mem md k).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* The image facts the piece reads, as LLVMFuzzerTestOneInput_seg_J_pre.v states them (its HRO, HIMG). *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.

(* llvmf_img at any state of the walk's journal (j_img of the prefix file). *)
Lemma js_img : forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
AJ g pos ly2 S2 W2 mem2 md2 k -> EPRE g -> llvmf_img B G W2 mem2.
Proof.
intros g pos k ly2 S2 W2 mem2 md2 HJ HPRE.
apply HIMG. apply (IdentBase.arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) []
(e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k HJ).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROD & _). apply HRO. exact HROD.
Qed.

(* The entry's class-4 frame lies apart from the image (its bytes are client bytes, AR_client_img_law). *)
Lemma js_frame_img : forall ly S (W : world SEGS) mem md pos,
AR SEGS B ly S W mem md -> In (4, pos) (frames S) -> AR_laws SEGS B ->
frame_addr ly 4 pos + 1024 <= IMG_LO \/ IMG_TOP <= frame_addr ly 4 pos.
Proof.
intros ly S W mem md pos HAR Hin LW.
pose proof HAR as (M & LG & _). pose proof (pa_img_cover ly S md LG) as [C1 C2].
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct (Z_le_gt_dec (frame_addr ly 4 pos + 1024) IMG_LO) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec IMG_TOP (frame_addr ly 4 pos)) as [H'|H']; [right; exact H'|].
exfalso.
destruct (al_client_img _ _ LW ly S W mem md (Z.max (frame_addr ly 4 pos) IMG_LO) HAR) as [Hn _].
- right; left. exists 4, pos. split; [exact Hin|]. rewrite HFB. lia.
- apply Hn. unfold in_zr. lia.
Qed.

(* The environment of the runs: the registers, then the frame address, the byte, and the three table words. *)
Definition js_extra (SF b3 u1 u2 u3 : Z) : list word := map (Z_to_bv 64) [SF; b3; u1; u2; u3].
Definition js_E (regs : bvmap 5 word) (SF b3 u1 u2 u3 : Z) : env := Eimg (Ereg regs (js_extra SF b3 u1 u2 u3)).
Lemma js_ew : forall (regs : bvmap 5 word) SF b3 u1 u2 u3,
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (js_E regs SF b3 u1 u2 u3) n = getr regs r) /\
ew (js_E regs SF b3 u1 u2 u3) 32 = Z_to_bv 64 SF /\
ew (js_E regs SF b3 u1 u2 u3) 33 = Z_to_bv 64 b3 /\
ew (js_E regs SF b3 u1 u2 u3) 34 = Z_to_bv 64 u1 /\
ew (js_E regs SF b3 u1 u2 u3) 35 = Z_to_bv 64 u2 /\
ew (js_E regs SF b3 u1 u2 u3) 36 = Z_to_bv 64 u3 /\
ew (js_E regs SF b3 u1 u2 u3) (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7)) /\
ew (js_E regs SF b3 u1 u2 u3) (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8)) /\
img_env VAL A_LIM (js_E regs SF b3 u1 u2 u3) /\
env_agree 32 (Ereg regs (js_extra SF b3 u1 u2 u3)) (js_E regs SF b3 u1 u2 u3) /\
regs_ok (js_E regs SF b3 u1 u2 u3) sr_atoms regs.
Proof.
intros regs SF b3 u1 u2 u3. unfold js_E.
split; [intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)|].
split; [apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia|].
split; [apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia|].
split; [apply Eimg_env|].
split; [split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]|].
apply regs_ok_Eimg_Ereg.
Qed.

(* The state at 0x81bb4 holds, with the shadow entry of the table. *)
Lemma js_entry : forall (g : ectx) pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k b3 u1 u2 u3,
AR_laws SEGS B ->
AJ g pos ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] ->
getr regs2 9 = w64 mf -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
getr regs2 12 = w64 SHADOW_OFF ->
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3) ->
val_mem SEGS (rd W2 mem2) (SFa g pos + V_id + 3) 1 b3 -> 0 <= b3 < 256 ->
VAL (A_OBJ 7) mod 8 = 0 ->
0 <= u1 < 2 ^ 64 -> 0 <= u2 < 2 ^ 64 -> 0 <= u3 < 2 ^ 64 ->
val_mem SEGS (rd W2 mem2) (VAL (A_OBJ 7)) 8 u1 ->
val_mem SEGS (rd W2 mem2) (VAL (A_OBJ 7) + 8) 8 u2 ->
val_mem SEGS (rd W2 mem2) (VAL (A_OBJ 7) + 16) 8 u3 ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (VAL (A_OBJ 7)) 24 ->
st_ok_pi SEGS VAL (js_E regs2 (SFa g pos) b3 u1 u2 u3) ss_js
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1440)) mem2 (seg_rom SEGS))) /\
sh_ok SEGS js_Bx js_SH (js_E regs2 (SFa g pos) b3 u1 u2 u3) (mrestrict (w_H W2) mem2).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k b3 u1 u2 u3 LW HJ Hfrs Rs1 Hmfb Hmf32 R12 V136 Vb3 Rb3 H7al
Ru1 Ru2 Ru3 V1 V2 V3 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as HAC.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LW ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. rewrite HFB in HSF1.
pose proof (js_frame_img ly2 S2 W2 mem2 md2 pos HAR2 Hin4 LW) as HOI. rewrite EFa in HOI.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
pose proof (pa_obj_img 7 (proj1 (Nat.ltb_lt 7 32) eq_refl)) as HO7.
destruct (js_ew regs2 (SFa g pos) b3 u1 u2 u3) as (EE & E32 & E33 & E34 & E35 & E36 & EO7 & _ & HEI & _ & HRG).
set (E := js_E regs2 (SFa g pos) b3 u1 u2 u3) in *.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 HAC Hmfb Hshi H47. lia. }
assert (U32 : bv_unsigned (ew E 32) = SFa g pos)
by (rewrite E32; apply unsigned_lit_small; clear - HSF0 HSF1 HAC; lia).
assert (U33 : bv_unsigned (ew E 33) = b3) by (rewrite E33; apply unsigned_lit_small; clear - Rb3; lia).
assert (U7 : bv_unsigned (ew E (A_OBJ 7)) = VAL (A_OBJ 7))
by (rewrite EO7; apply unsigned_lit_small; exact (pa_val_range _)).
assert (U12 : bv_unsigned (ew E 12) = SHADOW_OFF)
by (rewrite (EE 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx.
split.
- unfold ss_js. apply pa_entry_st_ok_full.
  + exact HRG.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor; [|constructor]]].
    * unfold js_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 HAC; lia|]. split; [clear - Hmfb Hshi H47; lia|].
      split.
      -- intros o Ho. apply (apresent_writable SEGS).
         refine (proj1 (awr_byte_present SEGS B LW LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g)
         (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k (mf + o) HJ _)).
         left. clear - Ho Hmfb HSTK' Has. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 32 355) (SFa g pos + V_id + 3));
         [cbn [sv_denot]; rewrite U32; unfold V_id; f_equal; clear; lia
         | clear - HSF0 HSF1 HAC; unfold V_id; cbn; lia | lia | exact V136].
    * unfold js_id, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [clear - HSF0; lia|]. split; [clear - HSF1 HAC; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SFa g pos) 355 1 (SOff 33 0) b3);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rb3; cbn; lia | lia |].
      unfold V_id in Vb3. replace (SFa g pos + 355) with (SFa g pos + 352 + 3) by lia. exact Vb3.
    * unfold js_tb, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U7. split; [clear - HO7; lia|]. split; [clear - HO7; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 0 8 (SOff 34 0) u1);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ru1 | lia | rewrite Z.add_0_r; exact V1].
      -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 8 8 (SOff 35 0) u2);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ru2 | lia | exact V2].
      -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 16 8 (SOff 36 0) u3);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ru3 | lia | exact V3].
  + apply pairwise_disjoint_of_extents. unfold js_mf, js_id, js_tb, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U7.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hmf0 HAC HSF0 HSF1 HO7 HOI. clear. intros. repeat split; lia.
  + unfold facts_ok, js_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9, U12, U33, U7.
    split; [|split; [exact I | exact I]].
    split; [split; [clear - Hmf0 HAC Hmfb Hshi H47; lia | split; [change (2 ^ 5) with 32; exact Hmf32 | lia]]|].
    split; [split; [lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|].
    split; [split; [clear - Rb3; lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|].
    split; [split; [clear - HO7; lia | split; [change (2 ^ 3) with 8; exact H7al | lia]] | exact I].
- unfold sh_ok, js_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E js_Bx (A_OBJ 7) (VAL (A_OBJ 7)) 24 (VAL (A_OBJ 7)) 0 24 HRA).
  + unfold js_Bx. apply (U_atom E 12 SHADOW_OFF); [rewrite (EE 12%nat 12%bv eq_refl); exact R12 | unfold SHADOW_OFF; lia].
  + exact (U_img_atom E HEI (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  + lia.
  + lia.
  + intros x Hx. clear - Hx HO7. unfold SHADOW_OFF. lia.
Qed.

(* No run of the piece writes outside mf+136 .. mf+144, and that window is inside the entry's stack. *)
Lemma js_awr_ok : forall E rs mf STK sp0 FP bl0 blc ly own,
windows rs = windows [js_mf; js_id; js_tb] -> bv_unsigned (ew E 9) = mf ->
sp0 - STK <= mf + 136 -> mf + 144 <= sp0 ->
awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs mf STK sp0 FP bl0 blc ly own Hw H9 H1 H2 a Ha.
destruct (in_wrange_windows E rs a Ha) as (b & wlo & whi & Hi & Hr).
left. pose proof (js_win E rs mf Hw H9 b wlo whi a Hi Hr). lia.
Qed.
Definition js_kept (W2 : world SEGS) (mf : Z) (m' m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 136 <= a < mf + 144) -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a.
Lemma js_kept_step : forall (W2 : world SEGS) mf E rs m0 m1 m2,
windows rs = windows [js_mf; js_id; js_tb] -> bv_unsigned (ew E 9) = mf ->
frame_of E rs (mrestrict (w_H W2) m1) (mrestrict (w_H W2) m2) ->
js_kept W2 mf m1 m0 -> js_kept W2 mf m2 m0.
Proof.
intros W2 mf E rs m0 m1 m2 Hw H9 HF HK a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs (w_H W2) m1 m2 (fun x => mf + 136 <= x < mf + 144) HF
(js_win E rs mf Hw H9) a Ha Hn).
apply HK; assumption.
Qed.
(* The word mf+136 at the end of a run, from the state's region 0. *)
Lemma js_vm136 : forall E ss (ms : machine_state) mf v z r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) 0 = Some r -> YP09.r_base r = Some 9%nat ->
In (YP09.mkChunk 136 (CVal 8 v)) (YP09.r_chunks r) ->
bv_unsigned (ew E 9) = mf -> sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem SEGS (ms_mem ms) (mf + 136) 8 z.
Proof.
intros E ss ms mf v z r HS Hn Hb Hc H9 Hv Hz.
pose proof (st_ok_pi_region_nth E ss ms 0 r HS Hn) as (_ & _ & _ & Hcs).
rewrite Hb in Hcs. cbn [base_val] in Hcs. rewrite H9 in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
exact (val_of_chunk_ok SEGS E (ms_mem ms) mf 136 8 v z Hck Hv
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hz) ltac:(cbn; lia)).
Qed.

(* ---- the stem, in each case -------------------------------------------------------------------------------- *)
(* A string of the image whose bytes the journal keeps (reac_box_name_inv.rbn_fixed) and that lies in a
   registered global: its bytes and its shadow at every state of the walk's journal. *)
Lemma js_any_tbl : forall (g : ectx) pos ly2 S2 (W2 : world SEGS) mem2 md2 k2 st (s : list Z),
globs_marked SEGS B G ->
AJ g pos ly2 S2 W2 mem2 md2 k2 ->
garr8 SEGS (rd W2 mem2) st (s ++ [0]) ->
(exists q z, In (q, z) G /\ q <= st /\ st + (Z.of_nat (length s) + 1) <= q + z) ->
(forall x, st <= x < st + (Z.of_nat (length s) + 1) ->
in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
forall ly S (W : world SEGS) mem md k, AJ g pos ly S W mem md k ->
garr8 SEGS (rd W mem) st (s ++ [0]) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF st (Z.of_nat (length s) + 1).
Proof.
intros g pos ly2 S2 W2 mem2 md2 k2 st s GM HJ2 Hg (q & z & Hq & H1 & H2) Hfix ly S W mem md k HJ.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
assert (NS : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
split.
- apply (j_garr8_moved SEGS (w_H W2) (w_H W) mem2 mem st (s ++ [0])); [|exact Hg].
  intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk.
  destruct (Hfix (st + kk) ltac:(lia)) as (Hi & Ho & He).
  rewrite (F (st + kk) Hi Ho He (fp_spares_closed [] _ NS)).
  rewrite (F2 (st + kk) Hi Ho He (fp_spares_closed [] _ NS)). reflexivity.
- apply (ro_usable_glob SEGS B G ly S W mem md q z); [exact GM | exact Hq | exact HAR | exact H1 | exact H2].
Qed.
(* "REAC" (object 8): llvmf_img gives its bytes at every state of the journal. *)
Lemma js_any_reac : forall (g : ectx) pos,
globs_marked SEGS B G -> In (VAL (A_OBJ 8), 5) G -> EPRE g ->
forall ly S (W : world SEGS) mem md k, AJ g pos ly S W mem md k ->
garr8 SEGS (rd W mem) (VAL (A_OBJ 8)) (disco_box_name_model.bn_STEM 0 ++ [0]) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 8))
(Z.of_nat (length (disco_box_name_model.bn_STEM 0)) + 1).
Proof.
intros g pos GM G8 HPRE ly S W mem md k HJ.
pose proof (js_img g pos k ly S W mem md HJ HPRE) as HIM.
destruct HIM as (_ & _ & _ & _ & _ & _ & _ & Greac & _).
split; [exact Greac|].
pose proof HJ as (HAR & _).
apply (ro_usable_glob SEGS B G ly S W mem md (VAL (A_OBJ 8)) 5); [exact GM | exact G8 | exact HAR | lia |].
change (Z.of_nat (length (disco_box_name_model.bn_STEM 0))) with 4. lia.
Qed.
(* The image case of the cut's stem: a string of the image, at every state of the journal. *)
Lemma js_jstem_img : forall (g : ectx) pos ly2 S2 (W2 : world SEGS) mem3 md3 k3 st (s : list Z),
AR_laws SEGS B ->
AJ g pos ly2 S2 W2 mem3 md3 k3 -> frames S2 = [(4, pos)] ->
map (fun b : byte => bv_unsigned b) (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0]) = s ++ [0] ->
length (SlotModel.n_stem (e_pl g)) = length s ->
IMG_LO <= st -> st + Z.of_nat (length s) + 1 <= IMG_TOP ->
(forall ly S (W : world SEGS) mem md k, AJ g pos ly S W mem md k ->
garr8 SEGS (rd W mem) st (s ++ [0]) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF st (Z.of_nat (length s) + 1)) ->
JSTEM g pos W2 mem3 st.
Proof.
intros g pos ly2 S2 W2 mem3 md3 k3 st s LW HJ3 Hfrs Hmap Hlen Hlo Hhi HANY.
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof (js_frame_img ly2 S2 W2 mem3 md3 pos HAR3 Hin4 LW) as HOI. rewrite EFa in HOI.
assert (HA : forall ly S (W : world SEGS) mem md k, AJ g pos ly S W mem md k ->
bytes_at8 W mem st (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0]) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF st
(Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1)).
{ intros ly S W mem md k HJx. destruct (HANY ly S W mem md k HJx) as [A1 A2].
  unfold bytes_at8. rewrite Hmap, Hlen. split; assumption. }
destruct (HA _ _ _ _ _ _ HJ3) as [B1 B2].
unfold jstem, jstem_any.
split; [right; exact HA|].
split; [exact B1|].
split; [rewrite Hlen; unfold V_nm, N_nm; clear - HOI Hlo Hhi; lia|].
split; [exact B2|].
split; [unfold amem_range, kLowMemEnd; left; rewrite Hlen; clear - Hhi; lia|].
clear - Hlo; lia.
Qed.
(* The named-model case: the stem is id.model_name in the entry's frame, kept by every run of the piece. *)
Lemma js_jstem_said : forall (g : ectx) pos ly2 S2 (W2 : world SEGS) mem2 mem3 md3 k3 mf,
AR_laws SEGS B ->
AJ g pos ly2 S2 W2 mem3 md3 k3 -> frames S2 = [(4, pos)] ->
alloc_ceiling + 16384 <= mf ->
id_at g pos (m_nrec g) W2 mem2 ->
SlotModel.n_use_said (e_pl g) = true ->
js_kept W2 mf mem3 mem2 ->
JSTEM g pos W2 mem3 (SFa g pos + V_id + 3).
Proof.
intros g pos ly2 S2 W2 mem2 mem3 md3 k3 mf LW HJ3 Hfrs Hmf0 Hid HUS KP.
destruct Hid as (Hidb & Hidz & Hidk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as HAC.
pose proof HJ3 as (HAR3 & Hly3 & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LW ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & HSFapp).
rewrite EFa in HSF0, HSF1, HSFapp. rewrite HFB in HSF1, HSFapp.
assert (HST : SlotModel.n_stem (e_pl g) = SlotModel.name_str (m_id g (m_nrec g)))
by (unfold SlotModel.n_stem; rewrite HUS; reflexivity).
assert (Lid : length (m_id g (m_nrec g)) = RcIdentModel.ID_SIZE) by apply SlotModel.rec_id_length.
destruct (js_said_bytes SEGS _ _ _ Lid (SlotModel.rec_id_b19 (e_pl g) (m_nrec g)) Hidb) as [Hg Hlen].
unfold jstem, jstem_any. rewrite HST.
split; [left; reflexivity|].
split.
{ unfold bytes_at8. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hg].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  apply KP; unfold V_id; clear - Hkk Hlen HSF0 HSF1 Hmf0 HAC; lia. }
split; [left; unfold V_id, V_nm; clear - Hlen; lia|].
split.
{ apply (block_shadow_range _ SHADOW_OFF (SFa g pos + V_id) N_id);
  [| unfold V_id; lia | unfold V_id, N_id; clear - Hlen; lia].
  apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF
  (SFa g pos + V_id) N_id); [|exact Hidk].
  intros i Hi. unfold shadow_of_addr. apply KP; unfold V_id, N_id, SHADOW_OFF in *;
  clear - Hi HSF0 HSF1 Hmf0 HAC; lia. }
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct HSFapp as (_ & [Hl | [Hh1 Hh2]]);
  [left; unfold V_id; clear - Hl Hlen; lia | right; unfold V_id; clear - Hh1 Hh2 Hlen HAC; lia]. }
unfold V_id. clear - HSF0. lia.
Qed.

(* ---- the cut at 0x81c3c ------------------------------------------------------------------------------------ *)
(* jc2 from jc1's facts: the runs keep every register jc2 reads and every byte outside mf+136 .. mf+144. *)
Lemma js_exit : forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3 st,
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
getr regs2 12 = w64 SHADOW_OFF ->
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) ->
getr regs2 25 = w64 (SFa g pos + V_nm) -> getr regs2 26 = w64 (SFa g pos + V_dp) ->
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm -> sh_zero W2 mem2 (SFa g pos + V_dp) N_dp ->
val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 0 ->
SlotModel.n_wok (e_pl g) = true ->
AR_laws SEGS B ->
AJ g pos ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
(forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
getr regs3 r = getr regs2 r) ->
js_kept W2 mf mem3 mem2 ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
val_mem SEGS (rd W2 mem3) (mf + 136) 8 st ->
JSTEM g pos W2 mem3 st ->
JC2 g pos mf nm tk dp st W2 (cfg_at SEGS (BASE + 0x14c8) regs3 mem3 md3).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 st
Hfrs Hk MLE MOK HC HK R12 R22 R25 R26 SZnm SZdp Vnm Hwok LW HJ3 RK KP Efds Efs V136 JST.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as HAC.
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LW ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. rewrite HFB in HSF1.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hmfr : mf + 144 <= 2 ^ 47) by (clear - Hmfb Hshi H47; lia).
assert (Hsp : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
(* the four ways a fact of jc1 reaches the end state *)
assert (VM : forall a (n : nat) v, 0 <= a ->
(a + Z.of_nat n <= mf + 136 \/ (mf + 144 <= a /\ a + Z.of_nat n <= 2 ^ 64)) ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H0 H1 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a n v); [|exact Hv].
  intros kk Hkk. apply KP; clear - H0 H1 Hkk Hmfr; lia. }
assert (GA : forall a l, 0 <= a -> a + Z.of_nat (length l) <= mf + 136 ->
garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem3) a l).
{ intros a l H0 H1 Hg. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a l); [|exact Hg].
  intros kk Hkk. apply KP; clear - H0 H1 Hkk Hmfr; lia. }
assert (SZ : forall a n, 0 <= a -> 0 <= n -> SHADOW_OFF + a / 8 + n / 8 <= mf + 136 ->
zero_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W2) mem3) SHADOW_OFF a n).
{ intros a n H0 Hn H1 Hz. apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)
  SHADOW_OFF a n); [|exact Hz].
  intros i Hi. unfold shadow_of_addr. apply KP; unfold SHADOW_OFF in *; clear - H0 Hn H1 Hi Hmfr; lia. }
assert (SB : forall a n, 0 <= a -> 0 <= n -> SHADOW_OFF + a / 8 + (n + 7) / 8 <= mf + 136 ->
block_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n -> block_shadow (aview SEGS (w_H W2) mem3) SHADOW_OFF a n).
{ intros a n H0 Hn H1 Hz. apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)
  SHADOW_OFF a n); [|exact Hz].
  intros i Hi. unfold shadow_of_addr. apply KP; unfold SHADOW_OFF in *; clear - H0 Hn H1 Hi Hmfr; lia. }
assert (Hsh : SHADOW_OFF + (SFa g pos + 1024) / 8 + 8 <= mf + 136).
{ unfold SHADOW_OFF. clear - HSF0 HSF1 Hmf0 HAC. lia. }
assert (Hblk : forall p n, In (p, n) (ablocks B ly2 S2) -> 0 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n).
{ intros p n Hin. destruct (al_blocks _ _ LW ly2 S2 W2 mem3 md3 p n HAR3 Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  clear - H1 H2 H3. lia. }
destruct Hbl as [Hperm Hhs].
assert (Hin_e : forall x, In x (ablocks B (e_ly g) (e_S g)) -> In x (ablocks B ly2 S2)).
{ intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hx. }
unfold jc2, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(js_inl)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(js_inl)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(js_inl)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(js_inl)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(js_inl)); exact Rtp|].
  split; [apply VM; [clear - Hmf0 HAC; lia | left; clear; cbn; lia | exact V16]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | left; clear; cbn; lia | exact V64]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V192]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V168]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact Vra]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact Vs0]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V24]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V32]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V40]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V48]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V56]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V64b]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V72]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V80]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V88]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V96]|].
  split; [apply VM; [clear - Hmfb Hmf0 HAC; lia | right; clear - Hmfb Hsp; cbn; lia | exact V104]|].
  split; [apply VM; [clear - HSF0; lia | left; clear - HSF1 Hmf0; cbn; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efds; exact (Hfds fd)|].
  split; [rewrite Efs; exact Hfs|].
  pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hn0 _] | [_ Hinpb]].
  - assert (Hl0 : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn [length] in Hlen; lia]).
    unfold bytes_at8. rewrite Hl0. apply garr8_nil.
  - destruct (Hblk _ _ (Hin_e _ Hinpb)) as (Hp0 & Hp1 & Hp2).
    pose proof (req_size_pos (e_n g) Hp2) as [_ Hrq].
    unfold bytes_at8 in *. apply GA; [exact Hp0 | rewrite length_map; clear - Hlen Hp1 Hrq Hmf0; lia | exact Hinb]. }
split.
{ unfold jkeep.
  split; [split; [exact Hperm | exact Hhs]|].
  split; [unfold sh_reg; rewrite (RK 23%bv ltac:(js_inl)); exact Rs7|].
  split; [rewrite (RK 24%bv ltac:(js_inl)); exact R24|].
  split; [rewrite (RK 21%bv ltac:(js_inl)); exact R21|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V152]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V184]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V144]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | left; clear; cbn; lia | exact V128]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | left; clear; cbn; lia | exact V120]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V176]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | right; clear - Hmfr; cbn; lia | exact V160]|].
  split; [apply VM; [clear - Hmf0 HAC; lia | left; clear; cbn; lia | exact V112]|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
    - unfold bytes_at8 in *. apply GA; [unfold V_id; clear - HSF0; lia | | exact Hidb].
      rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE.
      clear - HSF1 Hmf0. cbn. lia.
    - unfold sh_zero in *. apply SZ; [unfold V_id; clear - HSF0; lia | unfold N_id; lia | | exact Hidz].
      unfold V_id, N_id. clear - Hsh HSF0. lia.
    - unfold sh_blk in *. apply SB; [unfold V_id; clear - HSF0; lia | unfold N_id; lia | | exact Hidk].
      unfold V_id, N_id. clear - Hsh HSF0. lia. }
  intros H0. destruct (Hbufs H0) as (B1 & B2 & B3).
  pose proof (SlotModel.n_ln_le (e_pl g) Hwok) as Hln. pose proof (SlotModel.n_ld_le (e_pl g) Hwok) as Hld.
  pose proof (js_tok_len false (SlotModel.n_EXP_NM (e_pl g))) as Htk.
  unfold SlotModel.n_ln in Hln. unfold SlotModel.n_ld in Hld.
  destruct (Hblk _ _ (Permutation_in _ (Permutation_sym Hperm) ltac:(left; reflexivity))) as (Hn0 & Hn1 & Hn2).
  destruct (Hblk _ _ (Permutation_in _ (Permutation_sym Hperm) ltac:(right; left; reflexivity))) as (Ht0 & Ht1 & Ht2).
  destruct (Hblk _ _ (Permutation_in _ (Permutation_sym Hperm) ltac:(right; right; left; reflexivity)))
  as (Hd0 & Hd1 & Hd2).
  pose proof (req_size_pos _ Hn2) as [Hrn _]. pose proof (req_size_pos _ Ht2) as [Hrt _].
  pose proof (req_size_pos _ Hd2) as [Hrd _].
  unfold bytes_at8 in *.
  split; [|split].
  - apply GA; [exact Hn0 | | exact B1]. rewrite length_map, length_app. cbn [length].
    clear - Hln Hn1 Hrn Hmf0. lia.
  - apply GA; [exact Ht0 | | exact B2]. rewrite length_map, length_app. cbn [length].
    unfold SlotModel.n_TK, SlotModel.TOK. clear - Hln Htk Ht1 Hrt Hmf0. lia.
  - apply GA; [exact Hd0 | | exact B3]. rewrite length_map, length_app. cbn [length].
    clear - Hld Hd1 Hrd Hmf0. lia. }
split; [rewrite (RK 12%bv ltac:(js_inl)); exact R12|].
split; [rewrite (RK 22%bv ltac:(js_inl)); exact R22|].
split; [rewrite (RK 25%bv ltac:(js_inl)); exact R25|].
split; [rewrite (RK 26%bv ltac:(js_inl)); exact R26|].
split.
{ unfold sh_zero in *. apply SZ; [unfold V_nm; clear - HSF0; lia | unfold N_nm; lia | | exact SZnm].
  unfold V_nm, N_nm. clear - Hsh HSF0. lia. }
split.
{ unfold sh_zero in *. apply SZ; [unfold V_dp; clear - HSF0; lia | unfold N_dp; lia | | exact SZdp].
  unfold V_dp, N_dp. clear - Hsh HSF0. lia. }
split; [apply VM; [unfold V_nm; clear - HSF0; lia | left; unfold V_nm; clear - HSF1 Hmf0; cbn; lia | exact Vnm]|].
split; [exact V136 | exact JST].
Qed.

(* ---- the piece ---------------------------------------------------------------------------------------------- *)
Lemma j_stem : j_stem_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
unfold j_stem_stmt.
intros LW TLb GM ISV G7 G8 g pos mf nm tk dp W2 c2 Hstart Hwok.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & Hmf3 & R12 & R18 & R27 & R22 & R25 & R26 & SZnm & SZdp & Vnm & Vdp).
pose proof HC as (_ & Rs1 & _ & Hmfb & Hmf32 & _ & _ & _ & _ & _ & _ & _ & _ &
_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hid & _).
pose proof Hid as (Hidb & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as HAC.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (HW1 : e_sp0 g - LLVMF_STK <= mf + 136) by (clear - Hmfb HSTK' Has; lia).
assert (HW2 : mf + 144 <= e_sp0 g) by (clear - Hmfb; lia).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LW ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. rewrite HFB in HSF1.
assert (RSF : 0 <= SFa g pos + V_id + 3 < 2 ^ 64) by (unfold V_id; clear - HSF0 HSF1 HAC; lia).
(* the image facts *)
pose proof (js_img g pos _ ly2 S2 W2 mem2 md2 HJ HPRE) as HIM.
destruct HIM as (_ & _ & _ & _ & _ & H7al & (s1 & s2 & s3 & Vs1 & Vs2 & Vs3 & I1 & I2 & I3) & _).
pose proof I1 as (I1lo & I1hi & _ & I1g & I1glob & I1fix & _).
pose proof I2 as (I2lo & I2hi & _ & I2g & I2glob & I2fix & _).
pose proof I3 as (I3lo & I3hi & _ & I3g & I3glob & I3fix & _).
assert (Rs1r : 0 <= s1 < 2 ^ 64) by (clear - I1lo I1hi; lia).
assert (Rs2r : 0 <= s2 < 2 ^ 64) by (clear - I2lo I2hi; lia).
assert (Rs3r : 0 <= s3 < 2 ^ 64) by (clear - I3lo I3hi; lia).
pose proof (js_any_tbl g pos ly2 S2 W2 mem2 md2 _ s1 _ GM HJ I1g I1glob I1fix) as ANY1.
pose proof (js_any_tbl g pos ly2 S2 W2 mem2 md2 _ s2 _ GM HJ I2g I2glob I2fix) as ANY2.
pose proof (js_any_tbl g pos ly2 S2 W2 mem2 md2 _ s3 _ GM HJ I3g I3glob I3fix) as ANY3.
pose proof (js_any_reac g pos GM G8 HPRE) as ANYR.
clear I1 I2 I3 I1g I2g I3g I1glob I2glob I3glob I1fix I2fix I3fix.
pose proof (pa_obj_img 8 (proj1 (Nat.ltb_lt 8 32) eq_refl)) as HO8.
pose proof (ro_usable_glob SEGS B G ly2 S2 W2 mem2 md2 (VAL (A_OBJ 7)) 24 (VAL (A_OBJ 7)) 24 GM G7 HAR2
(Z.le_refl _) (Z.le_refl _)) as HRA7.
(* the first byte of the model-name field *)
assert (Lid : length (m_id g (m_nrec g)) = 38%nat) by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
destruct (Hidb 3%nat ltac:(rewrite length_map, Lid; lia)) as [Vb3 Rb3].
change (Z.of_nat 3) with 3 in Vb3.
assert (HB3 : RcIdentModel.bz (RcIdentModel.nthb (RcIdentModel.model_name (m_id g (m_nrec g))) 0) =
nth 3 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0) by (apply js_mn0; rewrite Lid; lia).
(* the state at 0x81bb4 *)
destruct (js_entry g pos mf ly2 S2 W2 regs2 mem2 md2 _ _ s1 s2 s3 LW HJ Hfrs Rs1 Hmfb Hmf32 R12 Hmf3 Vb3 Rb3
H7al Rs1r Rs2r Rs3r Vs1 Vs2 Vs3 HRA7) as [HS SHOK].
destruct (js_ew regs2 (SFa g pos) (nth 3 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0) s1 s2 s3)
as (EE & E32 & E33 & E34 & E35 & E36 & EO7 & EO8 & HEI & HAE & _).
set (b3 := nth 3 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0) in *.
set (E := js_E regs2 (SFa g pos) b3 s1 s2 s3) in *.
clearbody E.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 HAC Hmfb Hshi H47. lia. }
assert (U32 : bv_unsigned (ew E 32) = SFa g pos)
by (rewrite E32; apply unsigned_lit_small; clear - HSF0 HSF1 HAC; lia).
assert (E27' : ew E 27 = Z_to_bv 64 (RcIdentModel.has_model_name (m_id g (m_nrec g))))
by (rewrite (EE 27%nat 27%bv eq_refl), R27; reflexivity).
assert (E18' : ew E 18 = Z_to_bv 64 (SlotModel.n_fam (e_pl g)))
by (rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity).
assert (Rhm : 0 <= RcIdentModel.has_model_name (m_id g (m_nrec g)) < 2 ^ 64).
{ pose proof (SlotModel.bz_range (RcIdentModel.nthb (m_id g (m_nrec g)) RcIdentModel.OFF_HAS_NAME)) as Hb.
  unfold RcIdentModel.has_model_name. clear - Hb. lia. }
assert (Rb3' : 0 <= b3 < 2 ^ 64) by (clear - Rb3; lia).
assert (R0 : 0 <= 0 < 2 ^ 64) by lia.
pose proof (js_nfam_range (e_pl g)) as Rfam.
assert (Rfam' : - 2 ^ 31 <= SlotModel.n_fam (e_pl g) < 2 ^ 31) by (clear - Rfam; lia).
clear EE Rs1 R18 R27 Vs1 Vs2 Vs3 Vb3 HRA7 H7al Hceil Hslo HSTK' Has Hstatic Hly2 EF.
pose proof (paj_run B LW) as RUN. pose proof (paj_run_to B LW) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
assert (KP : js_kept W2 mf mem2 mem2) by (intros a _ _; reflexivity).
unfold cfg_at. change (w64 (BASE + 0x1440)) with (Z_to_bv 64 (BASE + 0x1440)).
let aw := idtac; apply (js_awr_ok _ _ mf); [vm_compute; reflexivity | exact U9 | exact HW1 | exact HW2] in
let upd := idtac;
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2), KP0 : js_kept _ _ ?m1 _ |- _ =>
    let KP' := fresh "KP" in
    pose proof (js_kept_step W mf E rs mem2 m1 m2 ltac:(vm_compute; reflexivity) U9 HFr KP0) as KP';
    clear KP0
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end in
let fin st v z := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssF (restrict (w_H ?WW) ?ms) |- _ =>
    pmkst HS; apply SRr_ret; cbv beta; exists st;
    let RK := fresh "RK" in
    assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
      getr (ms_regs ms) r = getr regs2 r)
      by (eapply (regs_kept_of_st_ok_pi E ssF _ regs2 _ _ HS HAE); vm_compute; reflexivity);
    let KPx := lazymatch goal with KPx : js_kept _ _ _ _ |- _ => KPx end in
    apply (js_exit g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ st Hfrs Hk MLE MOK HC HK
      R12 R22 R25 R26 SZnm SZdp Vnm Hwok LW HJ RK KPx);
    [ rewrite ?j_wvb_fds; reflexivity
    | rewrite ?j_wvb_fs; reflexivity
    | eapply (js_vm136 E ssF (restrict (w_H WW) ms) mf v z);
      [exact HS | reflexivity | reflexivity | cbn; auto | exact U9 | | ]
    | ]
  end in
let pin f := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 (restrict (w_H _) ?ms) |- _ =>
    let R18m := fresh "R18m" in
    prreg HS (18%bv : bv 5) R18m;
    rewrite E18' in R18m;
    let HP := fresh "HP" in
    pose proof (st_ok_pi_pin_reg' E ss0 _ (18%bv : bv 5) f HS
      ltac:(cbn [ms_regs restrict mkst]; rewrite R18m; f_equal; assumption) eq_refl) as HP;
    clear HS R18m; rename HP into HS;
    lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end
  end in
let tbl f s v ANYf Ilo Ihi Es Rs := idtac;
  pin f;
  paj_run_to_tok RUNTO HS HJ SHOK js_Bspan 0x14c8; [aw | ];
  upd;
  fin s v s;
  [ cbn [sv_denot]; rewrite Es, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | exact Rs
  | apply (js_jstem_img g pos ly2 S2 W2 _ _ _ s (disco_box_name_model.bn_STEM f) LW HJ Hfrs);
    [ lazymatch goal with Ef : SlotModel.n_fam (e_pl g) = _ |- _ =>
        assert (HST : SlotModel.n_stem (e_pl g) = SlotModel.stem_img f)
          by (unfold SlotModel.n_stem; rewrite HUS, Ef; reflexivity) end;
      rewrite HST; exact (proj1 (js_stem_img_map f))
    | lazymatch goal with Ef : SlotModel.n_fam (e_pl g) = _ |- _ =>
        assert (HST : SlotModel.n_stem (e_pl g) = SlotModel.stem_img f)
          by (unfold SlotModel.n_stem; rewrite HUS, Ef; reflexivity) end;
      rewrite HST; exact (proj2 (js_stem_img_map f))
    | clear - Ilo; lia
    | clear - Ihi; lia
    | exact ANYf ] ] in
let reac := idtac;
  paj_run_tok RUN HS HJ SHOK js_Bspan; [aw | ];
  upd;
  psrr_branch_tok RUN BR HS SHOK js_Bspan;
  [ paj_run_to_tok RUNTO HS HJ SHOK js_Bspan 0x14c8; [aw | ];
    upd;
    fin (VAL (A_OBJ 8)) (SOff (A_OBJ 8) 0) (VAL (A_OBJ 8));
    [ cbn [sv_denot]; rewrite EO8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | exact (pa_val_range (A_OBJ 8))
    | apply (js_jstem_img g pos ly2 S2 W2 _ _ _ (VAL (A_OBJ 8)) (disco_box_name_model.bn_STEM 0) LW HJ Hfrs);
      [ lazymatch goal with Ef : ~ (1 <= SlotModel.n_fam (e_pl g) <= 3) |- _ =>
          assert (HST : SlotModel.n_stem (e_pl g) = SlotModel.stem_img 0)
            by (unfold SlotModel.n_stem; rewrite HUS; exact (js_stem_other _ Ef)) end;
        rewrite HST; exact (proj1 (js_stem_img_map 0))
      | lazymatch goal with Ef : ~ (1 <= SlotModel.n_fam (e_pl g) <= 3) |- _ =>
          assert (HST : SlotModel.n_stem (e_pl g) = SlotModel.stem_img 0)
            by (unfold SlotModel.n_stem; rewrite HUS; exact (js_stem_other _ Ef)) end;
        rewrite HST; exact (proj2 (js_stem_img_map 0))
      | clear - HO8; lia
      | change (Z.of_nat (length (disco_box_name_model.bn_STEM 0))) with 4; clear - HO8; lia
      | exact ANYR ] ]
  | exfalso;
    lazymatch goal with
    | Hc : branch_taken _ _ _ = false, Ef : ~ (1 <= SlotModel.n_fam (e_pl g) <= 3) |- _ =>
      rewrite (js_bltu_other E (SlotModel.n_fam (e_pl g)) E18' Rfam' Ef) in Hc; discriminate Hc
    end ] in
let fam := idtac;
  let Ef := fresh "Ef" in
  destruct (js_fam_cases (SlotModel.n_fam (e_pl g))) as [Ef|[Ef|[Ef|Ef]]];
  [ tbl 1 s1 (SOff 34 0) ANY1 I1lo I1hi E34 Rs1r
  | tbl 2 s2 (SOff 35 0) ANY2 I2lo I2hi E35 Rs2r
  | tbl 3 s3 (SOff 36 0) ANY3 I3lo I3hi E36 Rs3r
  | reac ] in
psrr_branch_tok RUN BR HS SHOK js_Bspan;
[ (* x27 = 0: the record named no model *)
  rewrite (jb_eq_lit E 27 _ 0 E27' Rhm R0) in Hc; apply Z.eqb_eq in Hc;
  assert (HUS : SlotModel.n_use_said (e_pl g) = false)
    by (unfold SlotModel.n_use_said, SlotModel.n_said; change (SlotModel.idT (e_pl g)) with (m_id g (m_nrec g));
        rewrite Hc; reflexivity);
  clear Hc;
  paj_run_to_tok RUNTO HS HJ SHOK js_Bspan 0x1450; [aw | ];
  upd; fam
| rewrite (jb_eq_lit E 27 _ 0 E27' Rhm R0) in Hc; apply Z.eqb_neq in Hc; rename Hc into Hhm;
  paj_run_tok RUN HS HJ SHOK js_Bspan; [aw | ];
  upd;
  psrr_branch_tok RUN BR HS SHOK js_Bspan;
  [ (* the field's first byte is not NUL: the stem is the field *)
    rewrite (jb_ne_lit E 33 b3 0 E33 Rb3' R0) in Hc; apply Bool.negb_true_iff, Z.eqb_neq in Hc;
    assert (HUS : SlotModel.n_use_said (e_pl g) = true)
      by (unfold SlotModel.n_use_said, SlotModel.n_said; change (SlotModel.idT (e_pl g)) with (m_id g (m_nrec g));
          rewrite HB3; fold b3; rewrite (proj2 (Z.eqb_neq _ _) Hhm), (proj2 (Z.eqb_neq _ _) Hc); reflexivity);
    paj_run_to_tok RUNTO HS HJ SHOK js_Bspan 0x14c8; [aw | ];
    upd;
    fin (SFa g pos + V_id + 3) (SOff 32 355) (SFa g pos + V_id + 3);
    [ cbn [sv_denot]; rewrite U32; unfold V_id; f_equal; clear; lia
    | exact RSF
    | lazymatch goal with KPx : js_kept _ _ _ _ |- _ =>
        apply (js_jstem_said g pos ly2 S2 W2 mem2 _ _ _ mf LW HJ Hfrs Hmf0 Hid HUS KPx) end ]
  | (* the field is empty: the family's string *)
    rewrite (jb_ne_lit E 33 b3 0 E33 Rb3' R0) in Hc; apply Bool.negb_false_iff, Z.eqb_eq in Hc;
    assert (HUS : SlotModel.n_use_said (e_pl g) = false)
      by (unfold SlotModel.n_use_said, SlotModel.n_said; change (SlotModel.idT (e_pl g)) with (m_id g (m_nrec g));
          rewrite HB3; fold b3; rewrite Hc; apply andb_false_r);
    clear Hc;
    paj_run_to_tok RUNTO HS HJ SHOK js_Bspan 0x1450; [aw | ];
    upd; fam ] ].
Qed.

End c.
End b.
End a.

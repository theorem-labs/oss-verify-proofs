(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1h.v, walk helpers over fuzz_command's listing: module paths, csym; aview_above_of_journal keeps only bytes outside the call's footprint, as the journal now does. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaLibH.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; csym -> ssym; the image's end 0x606000 -> YG0f.kImgEnd (0x601000). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/PaLibH.v, with its module names changed; 206 of its 239 lines of code are new or changed and 178 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of segment
   S13 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (lib/B/Prog/
   LLVMFuzzerTestOneInput_s21.v): the payload's quantities the segment reads (cap, the VLAN seed table), the model's
   m->n, the two VLAN tables and the guard entry from their bytes, the frame's shadow pattern after `n` comes into
   scope, and the image facts of the cut kept when no byte of the image changes. No function of the binary is
   proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegAddr SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================= bytes of the reader ======================================= *)
(* one byte of a value the engine holds as a chunk of n bytes *)
Lemma s21_aview_of_val_mem : forall segs H mem a (n : nat) v k,
  val_mem segs (mrestrict H mem) a n v -> (k < n)%nat ->
  aview segs H mem (a + Z.of_nat k) = Some (le_byte v n k).
Proof.
intros segs H mem a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte, le_byte. apply Z.mod_mod. lia.
Qed.
(* a 4-byte chunk as segconf's sa_val *)
Lemma s21_sa_val_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 4 v -> sa_val (aview segs H mem) a 4 v.
Proof.
intros segs H mem a v Hv k Hk. exact (s21_aview_of_val_mem segs H mem a 4 v k Hv Hk).
Qed.

(* ======================================= the model ======================================= *)
(* the m->n field of a model block: the length of mc_seg, at most 32, as the 4 little-endian bytes lw reads *)
Lemma s21k_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [..|lia]; cbn [nth Z_to_le_bytes]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.

Lemma s21_mconf_n : forall rd m mc, sa_mconf rd m mc ->
  rd32 rd (m + seg_spec.MC_N) (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & Hb & Hl & Hle & _ & [Hr Hf] & _). split; [|exact Hle].
intros k Hk. unfold seg_spec.SEG_M_SIZE in Hl.
assert (O : Z.of_nat (Z.to_nat seg_spec.MC_N) = seg_spec.MC_N) by (apply Z2Nat.id; unfold seg_spec.MC_N; lia).
assert (E : nth k (seg_spec.fldz seg_spec.MC_N 4 bs) ZB0 = nth (Z.to_nat seg_spec.MC_N + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat 4) with 4%nat.
  rewrite nth_firstn. destruct (k <? 4)%nat eqn:K; [|apply Nat.ltb_ge in K; lia]. rewrite nth_skipn. reflexivity. }
rewrite Hf in E. rewrite <- (s21k_le4_nth _ k Hr Hk), E.
replace (m + seg_spec.MC_N + Z.of_nat k) with (m + Z.of_nat (Z.to_nat seg_spec.MC_N + k)) by (rewrite Nat2Z.inj_add, O; ring).
apply Hb. clear - Hl Hk O. unfold seg_spec.MC_N in *. lia.
Qed.
(* m_declared over no segment adds nothing *)
Lemma s21_mdecl_nil : forall mc tab cap, SegModel.mc_seg mc = [] -> SegModel.m_declared mc tab cap = (0, tab).
Proof.
intros mc tab cap E. unfold SegModel.m_declared. rewrite E. reflexivity.
Qed.

(* the VLAN tables from their bytes: empty, or the one seed entry ("enp1s0", 33) *)
Lemma s21_rtab_nil : forall rd tab, sa_rtab rd tab [].
Proof.
intros rd tab. exists []. split; [intros i Hi; cbn in Hi; lia|]. split; [reflexivity | intros i Hi; cbn in Hi; lia].
Qed.
Lemma s21_mtab_nil : forall rd mt, sa_mtab rd mt [].
Proof.
intros rd mt. exists []. split; [intros i Hi; cbn in Hi; lia|]. split; [reflexivity | intros i Hi; cbn in Hi; lia].
Qed.
Lemma s21k_bytes_of_zs : forall rd a l, sa_zs rd a l -> Forall (fun z => 0 <= z < 256) l ->
  sa_bytes rd a (seg_spec.zb l).
Proof.
intros rd a l Hz Hf i Hi. unfold seg_spec.zb in *. rewrite length_map in Hi. rewrite (Hz i Hi). f_equal.
unfold ZB0. rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. rewrite Forall_forall in Hf. apply Hf. apply nth_In. exact Hi.
Qed.
Ltac s21k_zs_tab Hz H7 :=
  intros i Hi; cbn [length app repeat] in Hi;
  do 20 (destruct i as [|i]; [first [ lia
    | match goal with |- _ (_ + Z.of_nat ?k) = _ =>
        first [ exact (Hz k ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) | exact (H7 (Z.of_nat k) ltac:(cbn; lia)) ] end
    | assumption ] |]); lia.

Lemma s21_rtab_enp : forall rd tab,
  sa_zs rd tab (SegModel.S_enp ++ [0]) -> (forall i, 7 <= i < 16 -> rd (tab + i) = Some 0) ->
  rd (tab + 16) = Some 33 -> rd (tab + 17) = Some 0 ->
  sa_rtab rd tab [(SegModel.S_enp, 33)].
Proof.
intros rd tab Hz H7 H16 H17. exists (seg_spec.zb (SegModel.S_enp ++ [0] ++ repeat 0 9 ++ [33; 0])). split.
- apply s21k_bytes_of_zs; [|vm_compute; repeat constructor; discriminate].
  change (SegModel.S_enp ++ [0] ++ repeat 0 9 ++ [33; 0]) with [101; 110; 112; 49; 115; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 33; 0].
  s21k_zs_tab Hz H7.
- split; [vm_compute; reflexivity|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia].
  split; [vm_compute; reflexivity|]. split; [split; [vm_compute; reflexivity|]; split; [vm_compute; lia|];
  split; [vm_compute; intros C; repeat (destruct C as [C|C]; [discriminate C|]); exact C | vm_compute; reflexivity]|].
  split; [cbn [nth snd]; lia | vm_compute; reflexivity].
Qed.
Lemma s21_mtab_enp : forall rd mt,
  sa_zs rd mt (SegModel.S_enp ++ [0]) -> (forall i, 7 <= i < 16 -> rd (mt + i) = Some 0) ->
  rd (mt + 16) = Some 33 -> rd (mt + 17) = Some 0 -> rd (mt + 18) = Some 0 -> rd (mt + 19) = Some 0 ->
  sa_mtab rd mt [(SegModel.S_enp, 33)].
Proof.
intros rd mt Hz H7 H16 H17 H18 H19. exists (seg_spec.zb (SegModel.S_enp ++ [0] ++ repeat 0 9 ++ [33; 0; 0; 0])). split.
- apply s21k_bytes_of_zs; [|vm_compute; repeat constructor; discriminate].
  change (SegModel.S_enp ++ [0] ++ repeat 0 9 ++ [33; 0; 0; 0]) with
    [101; 110; 112; 49; 115; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 33; 0; 0; 0].
  s21k_zs_tab Hz H7.
- split; [vm_compute; reflexivity|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia].
  split; [vm_compute; reflexivity|]. split; [split; [vm_compute; reflexivity|]; split; [vm_compute; lia|];
  split; [vm_compute; intros C; repeat (destruct C as [C|C]; [discriminate C|]); exact C | vm_compute; reflexivity]|].
  split; [cbn [nth snd]; lia | vm_compute; reflexivity].
Qed.
(* the guard entry tab[cap] (memset(&tab[cap], 0x5a, 18), 0x859c0) *)
Lemma s21_guard : forall rd tab cap,
  (forall i, 0 <= i < 18 -> rd (tab + 18 * cap + i) = Some 0x5a) -> sa_guardtab rd tab cap.
Proof.
intros rd tab cap Hg i Hi. unfold seg_spec.GUARD_BYTES in *. rewrite repeat_length in Hi.
rewrite nth_repeat_lt by exact Hi. unfold seg_spec.RVLAN_SIZE. rewrite (Hg (Z.of_nat i)) by lia. reflexivity.
Qed.

(* the frame's shadow after `sb 4, 32(SH(FR))` (0x859d4): n in scope, every other byte as before *)
Lemma s21_fsh : forall (rd rd' : reader) sh,
  sa_zs rd sh (lt_fsh LFO0) -> (forall i, 0 <= i < 36 -> i <> 32 -> rd' (sh + i) = rd (sh + i)) ->
  rd' (sh + 32) = Some 4 -> sa_zs rd' sh (lt_fsh LFO_N).
Proof.
intros rd rd' sh Hz Ha H32 i Hi. cbn [lt_fsh LFO_N fo_v fo_label fo_r fo_probe fo_n length app repeat] in Hi.
destruct (Nat.eq_dec i 32) as [->|Hne]; [exact H32|].
rewrite (Ha (Z.of_nat i)) by lia. rewrite (Hz i ltac:(cbn; lia)). f_equal.
do 36 (destruct i as [|i]; [first [reflexivity | lia] |]); lia.
Qed.

(* the literal "enp1s0": image B's address, the listing's object 9 (SegObj.seg_objs) *)
Lemma s21_lit_enp_addr : seg_litA_fz LIT_ENP = 0x21060 /\ nth 9 seg_objs 0 = 0x21060 /\ (9 < length seg_objs)%nat.
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).

(* the payload's quantities the segment reads (seg_spec over SegModel.decode) *)
Lemma s21_cap_range : forall cx : lcx, 0 <= x_cap cx < 40.
Proof.
intros cx. unfold x_cap, seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 _) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.
Lemma s21_tab0 : forall cx : lcx,
  x_tab0 cx = if negb (Z.land (x_flags cx) 1 =? 0) && (0 <? x_cap cx) then [(SegModel.S_enp, 33)] else [].
Proof.
intros cx. reflexivity.
Qed.
Lemma s21_tab0_len : forall cx : lcx, Z.of_nat (length (x_tab0 cx)) <= x_cap cx.
Proof.
intros cx. apply SegModel.vlan_init_len. exact (proj1 (s21_cap_range cx)).
Qed.
Lemma s21_decl0 : forall cx : lcx, x_decl cx 0 = (0, x_tab0 cx).
Proof.
intros cx. reflexivity.
Qed.

Section e.
Variable B : asyms.
(* a side-stack frame lies outside the image, as a heap block does (SegPaLib.blk_off_imgP) *)
Lemma s21_frame_off_img : forall ly S (W : world SEGS) mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S W mem md cid pos (M & LG & _) Hin. unfold off_img. pose proof (pa_img_cover ly S md LG) as [C1 C2].
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases kImgEnd (frame_addr ly cid pos)) as [|H2]; unfold kImgEnd in *; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. lia.
Qed.
(* the literal the segment copies, from the cut's image facts *)
Lemma s21_lit_enp : forall cx rd, lt_img B cx rd -> sa_lit SEGS B rd (seg_litA_fz LIT_ENP) LIT_ENP.
Proof.
intros cx rd (_ & (_ & _ & HL & _) & _). apply (HL LIT_ENP).
unfold LTOI_FZ_LITS, LTOI_LITS. apply in_or_app. left. right. right. right. left. reflexivity.
Qed.
(* the cut's image facts at a reader that agrees on every image byte *)
(* the bytes a cut's image facts read lie in [0x10000, kImgEnd), so a reader agreeing there keeps each of them *)
Lemma s21k_rdword_keep : forall (rd rd' : reader) a w,
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) -> 0x10000 <= a -> a + 8 <= kImgEnd ->
  rdword rd a = Some w -> rdword rd' a = Some w.
Proof.
intros rd rd' a w AG H1 H2 H. unfold rdword in *.
rewrite (AG a) by lia. rewrite (AG (a + 1)) by lia. rewrite (AG (a + 2)) by lia. rewrite (AG (a + 3)) by lia.
rewrite (AG (a + 4)) by lia. rewrite (AG (a + 5)) by lia. rewrite (AG (a + 6)) by lia. rewrite (AG (a + 7)) by lia.
exact H.
Qed.
Lemma s21k_val_keep : forall (rd rd' : reader) a n v,
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) -> 0x10000 <= a -> a + Z.of_nat n <= kImgEnd ->
  sa_val rd a n v -> sa_val rd' a n v.
Proof.
intros rd rd' a n v AG H1 H2 H k Hk. rewrite AG by lia. exact (H k Hk).
Qed.
Lemma s21k_lit_keep : forall (rd rd' : reader) a s,
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) -> sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros rd rd' a s AG (Hp & ((Hz & Hn) & Ht) & Hpin & Hrt & Himg).
assert (R : forall x, a <= x < a + (Z.of_nat (length s) + 1) -> 0x10000 <= x < kImgEnd).
{ intros x Hx. apply pa_img_range. exact (proj1 (Himg x Hx)). }
split; [exact Hp|]. split; [|exact (conj Hpin (conj Hrt Himg))]. split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite AG by (apply R; lia). exact (Hz i Hi).
- intros x Hx. pose proof (R (a + Z.of_nat (length s)) ltac:(lia)) as [R1 R2].
  rewrite AG; [exact (Ht x Hx)|]. set (e := a + Z.of_nat (length s)) in *. unfold kImgEnd in *. clear - Hx R1 R2. lia.
Qed.

Lemma s21_img_keep : forall cx (rd rd' : reader), lt_img B cx rd ->
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) -> lt_img B cx rd'.
Proof.
intros cx rd rd' (HA & HS & HG) AG.
destruct HS as (HM & HMi & HFZ & HRC & HC & HCa & HW & HR & HSS & HPin & HRt & HIm & HD1 & HD2 & HD3).
split; [|split].
- intros a Hro Ho He. rewrite AG; [exact (HA a Hro Ho He)|].
  destruct Hro as [(sg & Hsg & _ & Ha)|Ha].
  + apply pa_img_range. exists sg. exact (conj Hsg Ha).
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- split. { apply (s21k_val_keep rd rd' _ _ _ AG); [unfold mod40A; lia | unfold mod40A, kImgEnd; cbn; lia | exact HM]. }
  split; [exact HMi|].
  split. { intros s Hs. destruct (HFZ s Hs) as [L P]. exact (conj (s21k_lit_keep rd rd' _ _ AG L) P). }
  split. { intros s Hs. destruct (HRC s Hs) as [L P]. exact (conj (s21k_lit_keep rd rd' _ _ AG L) P). }
  split.
  { destruct HC as (C1 & C2 & C3). refine (conj C1 (conj C2 _)). intros i Hi. destruct (C3 i Hi) as (tp & T1 & T2).
    exists tp. split; [|exact (s21k_lit_keep rd rd' _ _ AG T2)].
    apply (s21k_rdword_keep rd rd' _ _ AG); [..|exact T1]; unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA, kImgEnd;
    unfold pin_spec.CAT_N in Hi; lia. }
  split; [exact HCa|].
  split.
  { destruct HW as (W1 & W2 & W3). refine (conj W1 (conj W2 _)). intros i Hi. destruct (W3 i Hi) as (wp & T1 & T2).
    exists wp. split; [|exact (s21k_lit_keep rd rd' _ _ AG T2)].
    apply (s21k_rdword_keep rd rd' _ _ AG); [..|exact T1]; unfold wordsA, kImgEnd; lia. }
  split.
  { destruct HR as (R1 & R2 & R3). refine (conj R1 (conj R2 _)). intros i Hi.
    apply (s21k_val_keep rd rd' _ _ _ AG); [..|exact (R3 i Hi)]; unfold rolesA, kImgEnd; lia. }
  split.
  { destruct HSS as (S1 & g & S2). split.
    - apply (s21k_rdword_keep rd rd' _ _ AG); [..|exact S1]; unfold gotwA, kImgEnd; lia.
    - exists g. apply (s21k_rdword_keep rd rd' _ _ AG); [..|exact S2]; unfold guardA, kImgEnd; lia. }
  exact (conj HPin (conj HRt (conj HIm (conj HD1 (conj HD2 HD3))))).
- intros i Hi. rewrite AG; [exact (HG i Hi)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.
End e.
End f.
End d.

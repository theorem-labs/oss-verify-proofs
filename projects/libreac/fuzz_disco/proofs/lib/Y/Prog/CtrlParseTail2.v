(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, reac_ctrl_parse at 0x874a4): ported from a working branch edc3e948664 fuzz_grant/lib/B/Prog/CtrlParseTail2.v (fuzz_grant image B's walk of the same 673 instructions at 0x82774; Y pc = image B pc + 0x4d30), with fuzz_disco's plumbing of lib/A/Prog/CtrlParseTail2.v (a working branch afedb375cf7: the premise 50 <= n, the frame f's facts by pz_open_f, the out struct placed by off_img in pz_kept_run) over lib/Y/Prog/CtrlParseCut.v; the inserted UBSan checks are decided by the engine from the atom facts, as in image B's walk. *)
(* reac_ctrl_parse, the walk from cut B (0x876a0) to cut J for the frames of class 2 (pz_P2):
   a frame type other than 00 00, cf ea, ce ea, cd ea: UNKNOWN_CTRL (13).
   From cut B the walk stores is_broadcast (out + 16), counter (out + 20), link (out + 22), seg (out + 23),
   blk_len (out + 24) and opcode (out + 26), each store after its shadow check and its UBSan pointer
   checks; then it compares frame[16] and frame[17] with the four known types (branches 0x878a0,
   0x879bc/0x879c4, 0x879e4/0x879ec, 0x87a0c/0x87a14). On a class-2 frame every comparison fails: the walk
   stores 13 at out + 0 (0x87a70) and jumps to the join 0x878c4 (cut J). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* ---- The model on a class-2 frame (Pau's ctrlparse, lib/Prog/RcParse.v:45) ---------------------- *)
Lemma t2_kind : forall n fr, cp_hdr n fr = true -> pz_P2 fr -> ctrlparse n fr = (13, cp_struct fr 13).
Proof. intros n fr Hh (T0 & T1 & T2 & T3). unfold ctrlparse, cp_kind. rewrite Hh, T0, T1, T2, T3. reflexivity. Qed.
Lemma t2_rec : forall fr, pz_P2 fr -> cp_rec fr = false.
Proof. intros fr (_ & _ & _ & T3). unfold cp_rec. rewrite T3. reflexivity. Qed.
Lemma t2_P2 : forall fr, pz_P2 fr ->
~ (cp_v fr 16 = 0 /\ cp_v fr 17 = 0) /\ ~ (cp_v fr 16 = 207 /\ cp_v fr 17 = 234) /\
~ (cp_v fr 16 = 206 /\ cp_v fr 17 = 234) /\ ~ (cp_v fr 16 = 205 /\ cp_v fr 17 = 234).
Proof.
intros fr (T0 & T1 & T2 & T3). unfold cp_type in *.
split; [intros [Ha Hb]; rewrite Ha, Hb in T0; discriminate|].
split; [intros [Ha Hb]; rewrite Ha, Hb in T1; discriminate|].
split; [intros [Ha Hb]; rewrite Ha, Hb in T2; discriminate|].
intros [Ha Hb]; rewrite Ha, Hb in T3; discriminate.
Qed.
(* ---- The values the walk stores, as the model's bytes ------------------------------------------ *)
Lemma t2_pack : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> zcanon (Z.lor (zcanon (Z.shiftl a 8)) b) = a * 256 + b.
Proof.
intros a b Ha Hb. unfold zcanon, M64.
assert (Hs : Z.shiftl a 8 = a * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (Z.mod_small (Z.shiftl a 8)) by (rewrite Hs; lia).
rewrite Z.lor_comm, Bytes.lor_shiftl8_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma t2_v_atom : forall E fr j, (j < 39)%nat -> ew E (40 + j) = Z_to_bv 64 (cp_v fr j) ->
Z.shiftr (U E (SOff (40 + j) 0)) 0 mod 256 = bv_unsigned (cp_b fr j).
Proof.
intros E fr j _ Hj. pose proof (cp_v_range fr j).
rewrite (U_atom E (40 + j) (cp_v fr j) Hj) by lia. rewrite Z.shiftr_0_r. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma t2_U_pack : forall E fr ja jb, ew E (40 + ja) = Z_to_bv 64 (cp_v fr ja) -> ew E (40 + jb) = Z_to_bv 64 (cp_v fr jb) ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff (40 + ja) 0) (SLit 8)) (SOff (40 + jb) 0)) = cp_v fr ja * 256 + cp_v fr jb.
Proof.
intros E fr ja jb Ha Hb. pose proof (cp_v_range fr ja). pose proof (cp_v_range fr jb).
rewrite U_SAlu, U_SAlu, (U_atom E (40 + ja) (cp_v fr ja) Ha), (U_atom E (40 + jb) (cp_v fr jb) Hb), U_lit by lia.
cbn [zalu_raw]. change (Z.land 8 63) with 8. apply t2_pack; lia.
Qed.
Lemma t2_v_plo : forall E fr ja jb, (ja < 39)%nat -> (jb < 39)%nat ->
ew E (40 + ja) = Z_to_bv 64 (cp_v fr ja) -> ew E (40 + jb) = Z_to_bv 64 (cp_v fr jb) ->
Z.shiftr (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff (40 + ja) 0) (SLit 8)) (SOff (40 + jb) 0))) 0 mod 256 = bv_unsigned (cp_b fr jb).
Proof.
intros E fr ja jb _ _ Ha Hb. pose proof (cp_v_range fr ja). pose proof (cp_v_range fr jb).
rewrite (t2_U_pack E fr ja jb Ha Hb), Z.shiftr_0_r. fold (cp_v fr jb).
replace (cp_v fr ja * 256 + cp_v fr jb) with (cp_v fr jb + cp_v fr ja * 256) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma t2_v_phi : forall E fr ja jb, (ja < 39)%nat -> (jb < 39)%nat ->
ew E (40 + ja) = Z_to_bv 64 (cp_v fr ja) -> ew E (40 + jb) = Z_to_bv 64 (cp_v fr jb) ->
Z.shiftr (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff (40 + ja) 0) (SLit 8)) (SOff (40 + jb) 0))) 8 mod 256 = bv_unsigned (cp_b fr ja).
Proof.
intros E fr ja jb _ _ Ha Hb. pose proof (cp_v_range fr ja). pose proof (cp_v_range fr jb).
rewrite (t2_U_pack E fr ja jb Ha Hb), Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. fold (cp_v fr ja).
replace (cp_v fr ja * 256 + cp_v fr jb) with (cp_v fr jb + cp_v fr ja * 256) by ring.
rewrite Z_div_plus_full by lia. rewrite (Z.div_small (cp_v fr jb)) by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.
Lemma t2_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0.
Proof.
intros E fr Hbc. rewrite U_SAlu, U_lit by lia. cbn [zalu_raw]. rewrite U_SOff, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E 640)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
unfold zcanon, M64. rewrite (Z.mod_small (bv_unsigned (ew E 640))) by lia.
destruct (cp_bcast fr) eqn:Eb.
- rewrite (proj2 Hbc eq_refl). reflexivity.
- assert (N0 : bv_unsigned (ew E 640) <> 0).
  { intros H0. assert (Hz : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite H0; reflexivity).
    pose proof (proj1 Hbc Hz) as Hb. congruence. }
  destruct (Z.ltb_spec (bv_unsigned (ew E 640)) 1); [lia|]. reflexivity.
Qed.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* A byte of the out struct, read back from one chunk of its region. *)
Lemma t2_cv : forall E H mem base off w e k z,
YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal w e)) ->
0 <= k - off < Z.of_N w ->
Z.shiftr (U E e) (8 * (k - off)) mod 256 = z ->
aview SEGS H mem (base + k) = Some z.
Proof.
intros E H mem base off w e k z Hc Hk Hz.
destruct (Hc (k - off) Hk) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
replace (base + off + (k - off)) with (base + k) in Hm by lia.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hz.
Qed.
Lemma t2_cz : forall E H mem base off n k z,
YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CZero n)) ->
0 <= k - off < n -> 0 = z -> aview SEGS H mem (base + k) = Some z.
Proof.
intros E H mem base off n k z Hc Hk <-.
destruct (Hc (k - off) Hk) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
replace (base + off + (k - off)) with (base + k) in Hm by lia.
unfold aview. rewrite Hm. reflexivity.
Qed.
(* The out struct's chunks at every class-2 leaf (0x878c4): the bytes of cut B, the six field stores and
   the kind 13 at out + 0. *)
Definition t2_chunks : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 13)); YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)));
 YP09.mkChunk 4 (CVal 1 (SOff 46 0)); YP09.mkChunk 5 (CVal 1 (SOff 47 0)); YP09.mkChunk 6 (CVal 1 (SOff 48 0));
 YP09.mkChunk 7 (CVal 1 (SOff 49 0)); YP09.mkChunk 8 (CVal 1 (SOff 50 0)); YP09.mkChunk 9 (CVal 1 (SOff 51 0));
 YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 41 0)); YP09.mkChunk 12 (CVal 1 (SOff 42 0));
 YP09.mkChunk 13 (CVal 1 (SOff 43 0)); YP09.mkChunk 14 (CVal 1 (SOff 44 0)); YP09.mkChunk 15 (CVal 1 (SOff 45 0));
 YP09.mkChunk 27 (CZero 9)].
(* The offset of the chunk that covers byte k. *)
Fixpoint t2_off_in (cs : list YP09.chunk) (k : Z) : Z :=
match cs with
| [] => -1
| c :: t => if (YP09.c_off c <=? k) && (k <? YP09.c_off c + YP09.c_len c) then YP09.c_off c else t2_off_in t k
end.
Lemma t2_out : forall E H mem o fr,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) o) t2_chunks ->
(forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) -> cp_rec fr = false ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr 13) cp_z)).
Proof.
intros E H mem o fr Hcs EF Hbc Hrec. unfold t2_chunks in Hcs.
repeat (let C := fresh "C" in apply Forall_cons_iff in Hcs; destruct Hcs as [C Hcs]).
unfold cp_struct. rewrite Hrec. change (13 =? 6) with false. cbn [app].
intros i Hi.
do 36 (destruct i as [|i];
[ cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
  lazymatch goal with |- aview _ _ _ (_ + ?k) = _ =>
  let off := eval vm_compute in (t2_off_in t2_chunks k) in
  lazymatch goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk off ?cv) |- _ =>
  lazymatch cv with
  | CZero _ => apply (t2_cz _ _ _ _ _ _ _ _ C); [lia | reflexivity]
  | CVal _ ?e =>
    apply (t2_cv _ _ _ _ _ _ _ _ _ C); [cbn [Z.of_N]; lia |];
    let s := eval vm_compute in (8 * (k - off)) in change (8 * (k - off)) with s;
    lazymatch e with
    | SOff ?na 0 =>
      let j := eval vm_compute in (na - 40)%nat in
      exact (t2_v_atom E fr j ltac:(lia) (EF j ltac:(lia)))
    | SAlu ALU_OR (SAlu ALU_SLL (SOff ?na 0) (SLit 8)) (SOff ?nb 0) =>
      let ja := eval vm_compute in (na - 40)%nat in let jb := eval vm_compute in (nb - 40)%nat in
      lazymatch s with
      | 0 => exact (t2_v_plo E fr ja jb ltac:(lia) ltac:(lia) (EF ja ltac:(lia)) (EF jb ltac:(lia)))
      | 8 => exact (t2_v_phi E fr ja jb ltac:(lia) ltac:(lia) (EF ja ltac:(lia)) (EF jb ltac:(lia)))
      end
    | SAlu ALU_SLTU _ _ => rewrite (t2_sltu E fr Hbc); destruct (cp_bcast fr); vm_compute; reflexivity
    | SLit _ => rewrite U_lit by lia; vm_compute; reflexivity
    end
  end end end
| ]).
lia.
Qed.
(* ---- The walk ------------------------------------------------------------------------------------
   The tactics below run inside pz_tail2 after pz_std and take its hypotheses as arguments. *)
(* The write windows of every run (awrFL_with of lib/Y/Prog/CtrlParseAwr.v): the out struct (region 12,
   writable), the realigned stack (33) and the saved registers (2), by pz_awr_hd; the frame (516), its shadow
   (529) and the input frame (10) are read-only. *)
Ltac t2_awr AGX fpos F EF := awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF.
(* What the caller keeps, carried across one run: every byte the run may write is in [sp1, sp) or in the
   out struct. *)
Ltac t2_kp B LAWS HAR KP AGX Usp B12 B33 Hoimg :=
lazymatch type of HAR with AR _ _ ?lyc ?Sc ?W ?memc ?mdc =>
lazymatch type of Usp with _ = ?sp =>
lazymatch type of B33 with _ = ?sp1 =>
lazymatch type of B12 with _ = ?o =>
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _ |- _ =>
let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a)
by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR ltac:(lia) ltac:(lia) Hoimg
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1; rename KP' into KP; clear_frames
end end end end end.
(* A branch condition as arithmetic on frame[16] and frame[17] (U56, U57, U5657: the compared values). *)
Ltac t2_hc Hc U56 U57 U5657 :=
rewrite ?branch_ne_U, ?branch_eq_U in Hc; rewrite ?U5657, ?U57, ?U56 in Hc; rewrite ?U_lit in Hc by lia;
lazymatch type of Hc with
| negb (_ =? _) = true => apply negb_true_iff, Z.eqb_neq in Hc
| negb (_ =? _) = false => apply negb_false_iff, Z.eqb_eq in Hc
| (_ =? _) = true => apply Z.eqb_eq in Hc
| (_ =? _) = false => apply Z.eqb_neq in Hc
end;
try (apply Z.lor_eq_0_iff in Hc).
(* A branch side that contradicts pz_P2 (or an earlier comparison of the same byte): only the facts about
   the frame bytes are kept for lia. *)
Ltac t2_refute :=
exfalso;
repeat match goal with H : _ |- _ => lazymatch type of H with context [cp_v _ _] => fail | _ => clear H end end;
lia.
(* The window [0, hi) of the region based at atom n made writable again, as the epilogue needs it (Hp: the
   bytes of the window are writable). *)
Ltac t2_rw HS n hi Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hp)) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end.
(* The finish of every class-2 path, at 0x878c4: the out struct holds cp_struct fr 13 and a0 = 13; the frame
   and shadow windows are made writable, the state is joined to ss_cutJ (dead registers from atom 700) and
   the cut-J hypothesis HJS closes the goal. *)
Ltac t2_leaf HS HJ2 KP HJS HEI AGX RF E528 E529 B12 EFc Hbc Hrec Hhdr HP2 LAWS Hfin2 :=
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msL) =>
lazymatch type of B12 with _ = ?ov =>
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of Hhdr with cp_hdr ?nv ?frv = true =>
lazymatch type of Hfin2 with In (1, ?fpos) _ =>
let HCS := fresh "HCS" in let HOUT := fresh "HOUT" in
pose proof (st_ok_pi_region_nth Ex _ _ 0%nat (YP09.mkRegion (Some 12%nat) 0 36 0 36 t2_chunks) HS ltac:(vm_compute; reflexivity)) as (_ & _ & _ & HCS);
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HCS; rewrite (AGX 12%nat), B12 in HCS by lia;
pose proof (t2_out Ex (w_H Wx) (ms_mem msL) ov frv HCS EFc Hbc Hrec) as HOUT;
let HFpL := fresh "HFpL" in let HFSpL := fresh "HFSpL" in let W529 := fresh "W529" in let W516 := fresh "W516" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpL & HFSpL);
change (fs_frame_bytes 1) with 128 in HFpL, HFSpL; change (128 / 8) with 16 in HFSpL;
assert (W529 : forall q, 0 <= q < 16 -> YP09.writable_at sg (mrestrict (w_H Wx) (ms_mem msL)) (base_val Ex (Some 529%nat) + q))
by (let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
    apply (apresent_writable sg); unfold shadow_addr in HFSpL; rewrite <- SB_SHADOW_OFF in HFSpL; apply (proj1 (HFSpL q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> YP09.writable_at sg (mrestrict (w_H Wx) (ms_mem msL)) (base_val Ex (Some 516%nat) + q))
by (let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia;
    apply (apresent_writable sg); apply (proj1 (HFpL (Fv + q) ltac:(lia))));
t2_rw HS 529%nat 16 W529; t2_rw HS 516%nat 128 W516; clear W529 W516 HFpL HFSpL HCS;
let R10 := fresh "R10" in
prreg HS (10%bv : bv 5) R10;
ra_join HS ss_cutJ 700%nat pz_deadJ idtac;
lazymatch type of HS with st_ok_pi _ _ _ ss_cutJ _ => idtac | _ => fail 1 "t2_leaf: the joined state is not ss_cutJ" end;
let E700 := fresh "E700" in
ra_join_val HS 700%nat 0%nat R10 E700;
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdL) _ =>
apply (HJS E' msL mdL);
[ split; [apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]|];
  split; [let n0 := fresh "n0" in let Hn0 := fresh "Hn0" in intros n0 Hn0; rewrite ew_havoc_old by lia; apply AGX; exact Hn0|];
  split; [rewrite ew_havoc_old by lia; exact RF|];
  split; [rewrite ew_havoc_old by lia; exact E528|];
  split; [rewrite ew_havoc_old by lia; exact E529|];
  split; [exact HJ2 | exact KP]
| exact HS
| rewrite (t2_kind nv frv Hhdr HP2); exact E700
| rewrite (t2_kind nv frv Hhdr HP2); exact HOUT ]
end end end end end end end.
(* The walk from cut B: run to the next branch or to the join; at a branch, each side either contradicts
   pz_P2 (t2_refute) or is walked on. *)
Ltac t2_walk RUN RUNTO BR HS HJ2 SHOK KP HJS HEI AGX RF E528 E529 B12 B33 Usp EFc Hbc Hrec Hhdr HP2 LAWS Hfin2
B HAR Hoimg U56 U57 U5657 fpos F EF :=
paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN;
[ t2_awr AGX fpos F EF
| t2_kp B LAWS HAR KP AGX Usp B12 B33 Hoimg;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  lazymatch (eval vm_compute in (ss_pc ss =? AF_JOIN)) with
  | true => t2_leaf HS HJ2 KP HJS HEI AGX RF E528 E529 B12 EFc Hbc Hrec Hhdr HP2 LAWS Hfin2
  | false =>
    psrr_branch_tok RUN BR HS SHOK PZspan;
    match goal with Hc : branch_taken _ _ _ = _ |- _ => t2_hc Hc U56 U57 U5657 end;
    first
    [ solve [t2_refute]
    | t2_walk RUN RUNTO BR HS HJ2 SHOK KP HJS HEI AGX RF E528 E529 B12 B33 Usp EFc Hbc Hrec Hhdr HP2 LAWS Hfin2
        B HAR Hoimg U56 U57 U5657 fpos F EF
    | match goal with |- ?g => idtac "T2WALK: no rule at" g end; fail 1 ]
  end end ].
Lemma pz_tail2 : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P2.
Proof.
intros B G RT c Hok HJS Hbig E ms md Hcur HS SHOK Hhdr Hbc HP2.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
assert (EFc : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i))
by (intros i Hi; rewrite (AGX (40 + i)%nat) by lia; exact (EFB i Hi)).
pose proof (t2_rec fr HP2) as Hrec.
destruct (t2_P2 fr HP2) as (T00 & Tcf & Tce & Tcd).
pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
assert (U56 : U E (SOff 56 0) = cp_v fr 16) by (apply (U_atom E 56 (cp_v fr 16) (EFc 16%nat ltac:(lia))); lia).
assert (U57 : U E (SAlu ALU_AND (SOff 57 0) (SLit 255)) = cp_v fr 17).
{ rewrite U_SAlu, U_lit by lia. rewrite (U_atom E 57 (cp_v fr 17) (EFc 17%nat ltac:(lia))) by lia.
  cbn [zalu_raw]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (cp_v fr 17) 256) by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (U5657 : U E (SAlu ALU_OR (SOff 56 0) (SAlu ALU_AND (SOff 57 0) (SLit 255))) = Z.lor (cp_v fr 16) (cp_v fr 17)).
{ rewrite U_SAlu, U56, U57. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small.
  pose proof (Bytes.lor_lt_pow2 (cp_v fr 16) (cp_v fr 17) 8 ltac:(change (2 ^ 8) with 256; lia) ltac:(change (2 ^ 8) with 256; lia)) as HL.
  change (2 ^ 8) with 256 in HL. lia. }
(* The disjunctions and the facts the walk does not need slow every lia down: drop them. *)
clear Hdfo Hfsh Hfwin Hfloc HFapp N1 N2 N3 N4 Hosh HBC_RNG HKL1 Hob0 Hob1 Hob12 Hobu Huar4 HBASE HBLO Hroom Ho32 Hra4
HFal HFq HF8 Hsp1al Hsp1al16 Hbot Htop2 Htop HFL4096 HFLce HFimg.
t2_walk RUN RUNTO BR HS HJ2 SHOK KP HJS HEI AGX RF E528 E529 B12 B33 Usp EFc Hbc Hrec Hhdr HP2 LAWS Hfin2
  B HAR Hoimg U56 U57 U5657 fpos F EF.
Qed.
End d.
End b.

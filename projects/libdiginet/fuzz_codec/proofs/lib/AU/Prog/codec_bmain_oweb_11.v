(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 434 of its 520 lines of code are new or changed and 180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe5.v, with its numbers changed; 510 of its 552 lines of code are new or changed and 478 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe10.v; 830 of its 869 lines of code are new or changed and 513 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe11.v, with its module paths, module names, addresses and numbers changed; 297 of its 623 lines of code are new or changed and 543 lines of the source are left out. *)
(* OWE11 (SYSEX) of the image-B walk of LLVMFuzzerTestOneInput: seg_owe 11 of lib/AU/Prog/codec_bmain_inv.v, from the
   cut OWE11 (0x82e60) to CHK (0x82dd4); owe()'s default case (fuzz_codec.c:234-250). It is the image-A segment
   (lib/A/Prog/codec_amain_owe11.v) at image B, where owe_sysex is a call instead of inlined code.
     0x82e60 a1 = k.a; a >= 128 -> 0x82e6c (want_rc = -1)
     0x82edc a2 = k.b; b = 0x70 -> 0x82ee8 (-10); 0x82f90 b > 127 -> 0x82dc8 (-11)
     0x82f98 a4 = k.n; n >= 20 -> 0x82fa8 (-5)
     0x83028 a0 = a3 = &k.bytes (ld 120(s1)), a5 = n, s9 = 128(s1)
     0x83038 the seven-bit test of k.bytes[0 .. n) (lib/AU/Prog/codec_bmain_oweb_11l.v o11_loop0): a byte with bit 7
             set -> 0x82dc8 (-11)
     0x8307c a1 = (uint8_t)a, a2 = (uint8_t)b, a0 = k, a3 = &k.bytes (ld 120(s1)), a4 = n; jal owe_sysex (0x84e8c,
             lib/AU/Prog/codec_bmain_owebl.v bm_owe_sysex_at); 0x83090 j CHK.
   The only UBSan trap edge on these paths, 0x8303c (a0 NULL), lies in the loop, which decides it from a0's range.
   The state: bm_entry's base, k's fields read (region 6: a, b, the 24 bytes, n as atoms 37, 38, 40 .. 63, 39) and
   want_rc (region 5, window [332, 336), chunk 0). The error paths end in lib/AU/Prog/codec_bmain_owel.v
   owe_chk_end. The success path re-seats its state after the loop (st_ok_after_stretch over O11_CLOB), runs to
   owe_sysex, takes the cut facts there (lib/AU/Prog/codec_bmain_encl.v enc_callst; the run wrote no byte, and
   want_rc still reads 0), and goes from the return address to CHK by lib/AU/Prog/codec_bmain_encl.v bm_jump. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgSatU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_encl codec_bmain_owel.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_owebl codec_bmain_oweb_10l codec_bmain_oweb_11l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the state ================================ *)
Definition O11_PC : Z := 0x82e60.
Definition o11_bchunks : list YP09.chunk :=
  map (fun i : nat => YP09.mkChunk (232 + Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 24).
Definition o11_rk : YP09.region :=
  bm_frame_region 216 264 216 216
    ([YP09.mkChunk 216 (CVal 4 (SOff 37 0)); YP09.mkChunk 220 (CVal 4 (SOff 38 0))] ++ o11_bchunks ++
     [YP09.mkChunk 256 (CVal 8 (SOff 39 0))]).
Definition o11_rc : YP09.region := bm_frame_region 332 336 332 336 [YP09.mkChunk 332 (CVal 4 (SLit 0))].
Definition o11_rs : smem := [o11_rc; o11_rk].
Definition o11_AF : list (nat * afact) :=
  [(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 24 0)] ++
  map (fun i : nat => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 24).
(* the values of atoms 37 .. 63 *)
Definition o11_ys (k : kcallZ) : list Z := [kz_a k; kz_b k; kz_n k] ++ kz_bytes k.
(* the bytes a path may write: the cursor's window and want_rc *)
Definition o11_zerr (F sp1 a : Z) : Prop := (sp1 + 184 <= a < sp1 + 200) \/ (F + 332 <= a < F + 336).

(* ================================ small facts ================================ *)
Lemma o11_vm : forall m a (n : nat) u v, val_mem tfibsegs m a n u ->
  u mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n) -> val_mem tfibsegs m a n v.
Proof. intros m a n u v H E j Hj. rewrite (H j Hj). unfold YO0f.le_byte. rewrite E. reflexivity. Qed.

Lemma o11_ys_byte : forall k i, length (kz_bytes k) = 24%nat -> (i < 24)%nat ->
  nth (3 + i) (o11_ys k) 0 = nth i (kz_bytes k) 0.
Proof. intros k i L Hi. unfold o11_ys. replace (3 + i)%nat with (S (S (S i))) by lia. reflexivity. Qed.

Lemma o11_atoms_map : forall E f (l : list nat), (forall i, In i l -> afact_ok E (40 + i) f) ->
  atoms_ok E (map (fun i => ((40 + i)%nat, f)) l).
Proof.
intros E f l H. induction l as [|i l IH]; cbn [map atoms_ok]; [exact I|].
split; [apply H; left; reflexivity | apply IH; intros j Hj; apply H; right; exact Hj].
Qed.

Lemma o11_ntest : forall n, 0 <= n <= 24 -> (18446744073709551590 <? zcanon (n + -20)) = (n <? 20).
Proof.
intros n Hn.
assert (C : forallb (fun y => Bool.eqb (18446744073709551590 <? zcanon (y + -20)) (y <? 20)) (map Z.of_nat (seq 0 25))
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C n ltac:(apply in_map_iff; exists (Z.to_nat n); split; [lia | apply in_seq; lia])).
apply Bool.eqb_prop in C. exact C.
Qed.

(* a register value over one byte atom, read by computing it for every value of the atom *)
Lemma o11_U_byte : forall E n e v (f : Z -> Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> YP06.sv_atoms_lt 1000 e = true ->
  (forall E', forallb (fun y => U (ewset E' n (Z_to_bv 64 y)) e =? f y) (map Z.of_nat (seq 0 256)) = true) ->
  U E e = f v.
Proof.
intros E n e v f Hn Hv Ha C. specialize (C E). rewrite forallb_forall in C.
specialize (C v ltac:(apply in_map_iff; exists (Z.to_nat v); split; [lia | apply in_seq; lia])).
apply Z.eqb_eq in C. rewrite <- C. unfold U. f_equal.
symmetry. apply (YP06.sv_denot_agree 1000 E (ewset E n (Z_to_bv 64 v)) e); [|exact Ha].
split; [|reflexivity]. intros i _. destruct (Nat.eq_dec i n) as [->|Hne].
- rewrite ew_ewset_same. symmetry. exact Hn.
- apply ew_ewset_other. exact Hne.
Qed.

(* bytes that read the same value in two memories *)
Lemma o11_same : forall H (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v ->
  forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H m x = aview tfibsegs H m' x.
Proof.
intros H m m' a n v V V' x Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (V (Z.to_nat (x - a)) ltac:(lia)), (V' (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.

Lemma o11_u8_id : forall l, Forall (fun x => 0 <= x < 256) l -> map u8 l = l.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|y l' Hx Hl]; subst. cbn [map].
unfold u8 at 1. rewrite Z.mod_small by lia. f_equal. exact (IH Hl).
Qed.

Lemma o11_sx_u8 : forall dev fn bs, Forall (fun x => 0 <= x < 256) bs ->
  map u8 (fst (owe_sx dev fn bs)) = fst (owe_sx dev fn bs).
Proof.
intros dev fn bs H. apply o11_u8_id. unfold owe_sx. cbn [fst].
apply Forall_app. split; [|apply Forall_app; split; [exact H|]].
- repeat (apply Forall_cons; [first [lia | unfold u8; apply Z.mod_pos_bound; lia] |]). apply Forall_nil.
- apply Forall_cons; [lia | apply Forall_nil].
Qed.

Lemma o11_kept_eq : forall E (m m' : word -> option byte) r, (forall x, m' x = m x) ->
  region_kept tfibsegs E m m' r.
Proof.
intros E m m' r M. split; intros a _.
- unfold mbyte. rewrite M. reflexivity.
- unfold writable_at, wview. rewrite M. tauto.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the frame's 60 shadow bytes are on no byte a path writes *)
Lemma o11_shadow_out : forall F sp1 i, F mod 64 = 0 -> in_app F 512 -> alloc_ceiling < sp1 - 4096 ->
  0 <= i < 60 -> ~ o11_zerr F sp1 (shadow_addr F + i).
Proof.
intros F sp1 i H64 Happ Hsp Hi Hz.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (D8 : 0 <= F / 8 /\ 8 * (F / 8) <= F) by (split; [apply Z.div_pos | apply Z.mul_div_le]; unfold in_app in Happ; lia).
unfold o11_zerr, shadow_addr, SHADOW_OFF in Hz. appn. lia.
Qed.

Lemma o11_ew_y : forall g pos c regs k j, ew (bm_env g pos c regs (o11_ys k)) (37 + j) =
  Z_to_bv 64 (nth j (o11_ys k) 0).
Proof. intros. exact (bm_ew_y g pos c regs (o11_ys k) j). Qed.

(* the engine's shadow entry of k, from the frame's shadow map shm 0 *)
Lemma o11_shk : forall (W : world tfibsegs) m E F, F mod 64 = 0 -> in_app F 512 ->
  (forall i, 0 <= i < 60 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
  ew E 33 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB ->
  shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) m) owe_SHk.
Proof.
intros W m E F H64 Happ HSH E33 E32.
pose proof (o10_bs_k W m F H64 HSH) as HBS.
pose proof (block_shadow_range (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 192) 184 (F + 192) 184 HBS
  ltac:(lia) ltac:(lia)) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ham : amem_range (F + 192) 184) by (appn; lia).
unfold owe_SHk. change 376 with (192 + 184).
apply (cw_shent_ra_off W m E 33 F 192 184 Hra Ham); [appn; lia | lia | lia | appn; lia | exact E33 | exact E32].
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis OSX : cdcU_owe_sysex_specX tfibsegs B MT BM_owe_sysex.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ================================ the start ================================ *)
Lemma o11_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
  frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
  cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> kz_want_rc k = 0 ->
  0 <= kz_a k < 256 -> 0 <= kz_b k < 256 -> 0 <= kz_n k <= 24 -> Forall (fun x => 0 <= x < 256) (kz_bytes k) ->
  st_ok tfibsegs (bm_env g pos c regs2 (o11_ys k)) (bm_ss O11_PC o11_rs o11_AF)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 O11_PC) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k HJ Hfr HC Hcur Hkat Hwrc Ha Hb Hn Hbs.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in Hchi.
pose proof Hkat as (HK & Hwf).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout & Vwrc & _).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lbytes & _).
set (E := bm_env g pos c regs2 (o11_ys k)).
assert (UF : bv_unsigned (ew E 33) = FA g pos) by (unfold E; rewrite bm_ew_F; apply unsigned_lit_small; lia).
assert (DY : forall j v, nth j (o11_ys k) 0 = v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff (37 + j) 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. cbn [sv_denot]. unfold E. rewrite o11_ew_y, Hj, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o11_rs).
{ unfold o11_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - unfold o11_rc.
    apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (o11_ys k));
      [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. rewrite Hwrc in Vwrc. replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia.
    exact Vwrc.
  - unfold o11_rk.
    apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (o11_ys k));
      [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_app. split; [|apply Forall_app; split].
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs _ _ (FA g pos) 216 4 (SOff 37 0) (kz_a k)); [ | cbn; lia | cbn; lia |].
        -- apply (DY 0%nat); [reflexivity | lia].
        -- change (N.to_nat 4) with 4%nat. replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
      * apply (chunk_ok_val tfibsegs _ _ (FA g pos) 220 4 (SOff 38 0) (kz_b k)); [ | cbn; lia | cbn; lia |].
        -- apply (DY 1%nat); [reflexivity | lia].
        -- change (N.to_nat 4) with 4%nat. replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact Vb.
    + apply Forall_forall. intros ch Hch. unfold o11_bchunks in Hch. apply in_map_iff in Hch as (i & <- & Hi).
      apply in_seq in Hi.
      rewrite Forall_forall in Hbs.
      assert (Hr : 0 <= nth i (kz_bytes k) 0 < 256) by (apply Hbs; apply nth_In; lia).
      apply (chunk_ok_val tfibsegs _ _ (FA g pos) (232 + Z.of_nat i) 1 (SOff (40 + i) 0) (nth i (kz_bytes k) 0));
        [ | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      * change (40 + i)%nat with (37 + (3 + i))%nat. apply (DY (3 + i)%nat); [apply o11_ys_byte; lia | lia].
      * change (N.to_nat 1) with 1%nat.
        replace (FA g pos + (232 + Z.of_nat i)) with (FA g pos + 192 + 40 + Z.of_nat i) by lia.
        exact (proj1 (Gbytes i ltac:(lia))).
    + apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (FA g pos) 256 8 (SOff 39 0) (kz_n k)); [ | cbn; lia | cbn; lia |].
      * apply (DY 2%nat); [reflexivity | lia].
      * change (N.to_nat 8) with 8%nat. replace (FA g pos + 256) with (FA g pos + 192 + 64) by lia. exact Vn. }
assert (Hpd : pairwise_disjoint E o11_rs).
{ cbn [pairwise_disjoint all_disjoint o11_rs]. unfold extent_disjoint, o11_rc, o11_rk, bm_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o11_rs).
{ unfold o11_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: unfold o11_rc, o11_rk; apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (o11_ys k));
  [exact HJ | exact Hfr | exact HC | lia | lia]. }
assert (HAF : atoms_ok E o11_AF).
{ assert (X37 : ew E 37 = Z_to_bv 64 (kz_a k)) by exact (o11_ew_y g pos c regs2 k 0).
  assert (X38 : ew E 38 = Z_to_bv 64 (kz_b k)) by exact (o11_ew_y g pos c regs2 k 1).
  assert (X39 : ew E 39 = Z_to_bv 64 (kz_n k)) by exact (o11_ew_y g pos c regs2 k 2).
  unfold o11_AF. apply bm_atoms_ok_app.
  + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite X37, X38, X39, !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + apply o11_atoms_map. intros i Hi. apply in_seq in Hi.
    rewrite Forall_forall in Hbs.
    assert (Hr : 0 <= nth i (kz_bytes k) 0 < 256) by (apply Hbs; apply nth_In; lia).
    assert (Xi : ew E (40 + i) = Z_to_bv 64 (nth i (kz_bytes k) 0)).
    { rewrite <- (o11_ys_byte k i Lbytes ltac:(lia)). exact (o11_ew_y g pos c regs2 k (3 + i)). }
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Xi, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
exact (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c O11_PC (o11_ys k) o11_rs o11_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd Hap HAF).
Qed.

(* ================================ an error path at CHK ================================ *)
Lemma o11_err_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od E ss ms md3 v,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
  frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
  mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
  ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k od ->
  kz_rc k = fst (enc_kZ k od) -> kz_want_len k = 0 -> kz_want_key k = 0 -> kz_want_display k = 0 ->
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md3 kj ->
  env_agree 37 (bm_env g pos c regs2 ys) E ->
  st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = PC_CHK -> ss_resv ss = None ->
  bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
  nth_error (ss_mem ss) 4 = Some bm_cur_region ->
  nth_error (ss_mem ss) 5 = Some (bm_frame_region 332 336 332 336 [YP09.mkChunk 332 (CVal 4 (SLit v))]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  fst (owe_kZ k od) <> 0 -> - 2 ^ 31 <= fst (owe_kZ k od) < 2 ^ 31 -> 0 <= v < 2 ^ 64 ->
  v mod 2 ^ 32 = fst (owe_kZ k od) mod 2 ^ 32 ->
  SRr tfibsegs W2 (mkCfg ms md3) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od E ss ms md3 v HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc
  Hwl Hwk Hwd HJ3 HAE HS Hpc Hrv Hkeep H20 H4 H5 KE Hr0 Hrr Hv Hvr.
pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv) as Ems. rewrite Hpc in Ems.
rewrite Ems in HS. rewrite Ems.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in Hchi.
pose proof Hkat as (HK & Hwf).
destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vwl & Vwk & Vwd).
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ destruct HAE as [HA _]. rewrite (HA 33%nat ltac:(lia)), bm_ew_F. apply unsigned_lit_small. lia. }
pose proof (st_ok_region_nth E ss _ 5 _ HS H5) as Hr5. rewrite restrict_mkst_fx in Hr5. cbn [ms_mem] in Hr5.
unfold bm_frame_region in Hr5.
pose proof (field_of_region_any E _ 33 (FA g pos) _ 332 336 332 336 332 4 (SLit v) Hr5 UF ltac:(left; reflexivity)
  ltac:(lia)) as V332.
change (N.to_nat 4) with 4%nat in V332.
assert (VK : forall a w x, 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  (forall y, a <= y < a + Z.of_nat w -> ~ o11_zerr (FA g pos) sp1 y) ->
  val_mem tfibsegs (rd W2 mem2) a w x -> val_mem tfibsegs (rd W2 (ms_mem ms)) a w x).
{ intros a w x Ha Haw Hz Vx. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vx].
  intros y Hy. apply KE; [lia | apply Hz; lia]. }
assert (FFS : LLVMF_STK = 32768) by reflexivity.
apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od 0 (ms_mem ms) (ms_regs ms) md3
  E ss (fst (owe_kZ k od)) [] 0 0 0 HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H20 H4 eq_refl
  ltac:(cbn; lia)).
- intros a Ha Hz. apply KE; [exact Ha | intros Hm; apply Hz; unfold owe_zone, o11_zerr in *; lia].
- apply (o11_vm _ _ 4 _ _ V332). cbn [sv_denot]. rewrite unsigned_lit_small by lia.
  change (8 * Z.of_N 4) with 32. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. exact Hvr.
- apply garr8_nil.
- rewrite Hwl in Vwl. replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwl].
- rewrite Hwk in Vwk. replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwk].
- rewrite Hwd in Vwd. replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwd].
- exact Hrr.
- lia.
- lia.
- lia.
- cbn [app length skipn]. apply owe_want_ok_fail; [reflexivity | exact Hr0].
Qed.

(* ================================ the walk's tactics ================================ *)
(* an atom below 64 of the env after runs and re-seats, as in the start env *)
Ltac o11_lift Ev n H0 H := assert (H : ew Ev n = _) by (rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact H0).
Ltac o11_liftb Hb n H0 H := lazymatch type of Hb with branch_taken _ (sv_denot ?Ev _) _ = _ => o11_lift Ev n H0 H end.
Ltac o11_liftS n H0 H := lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => o11_lift Ev n H0 H end.
(* the write windows: the cursor (atom 2), ranges of the frame (atom 33) *)
Ltac o11_inframe EFA :=
  right; right; right; eexists 3, _; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA;
  change (fs_frame_bytes 3) with 512; lia.
Ltac o11_awr sp1v sp0v Fv U2 UF EFA :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1v - sp0v));
    [reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite U2; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact UF
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; o11_inframe EFA
    | ] ].
(* the windows lie in the kept fact's zone *)
Ltac o11_kwr U2 UF :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
     rewrite ?U2, ?UF in Hb; unfold o11_zerr; lia | ]);
  destruct Hr.

Ltac o11_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.
Ltac o11_mkst :=
  lazymatch goal with HS : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
    let p := eval vm_compute in (ss_pc ssv) in change (ss_pc ssv) with p end.
(* an error path at CHK: o11_err_end with the code's literal v and the code's equation Hf *)
Ltac o11_close v Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
    eapply (o11_err_end _ _ _ _ _ _ _ _ _ _ _ _ (o11_ys _) _ _ Ev ssv msv _ v) end;
    [exact HJ0 | exact Hfr | exact Hkj | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat | exact Hrec
    | exact Hrc | exact Hwl | exact Hwk | exact Hwd | exact HJ | env_agree_chain HAE | exact HS | reflexivity
    | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact KE | | | | ];
    rewrite ?Hf; unfold E_ARG, E_REFUSED, E_RANGE, E_SPACE; [lia | lia | lia | reflexivity].
Ltac o11_region HS i Hr :=
  lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Hr : region_ok tfibsegs E (ms_mem ms) r) by (apply (st_ok_region_nth E ss ms i r HS); vm_compute; reflexivity)
  end.
Ltac o11_in := repeat (first [left; reflexivity | right]).
(* a register over the byte atom n with value v: x = Z_to_bv 64 v *)
Ltac o11_byte_reg G n Yn v :=
  lazymatch type of G with _ = sv_denot ?Ev ?e =>
    let Uv := fresh "U" in
    assert (Uv : U Ev e = v)
      by (apply (o11_U_byte Ev n e v (fun y => y) Yn); [lia | vm_compute; reflexivity | intros; vm_compute; reflexivity]);
    let G' := fresh G in pose proof (o11_reg Ev e _ v G Uv) as G'; clear G Uv; rename G' into G end.

(* ================================ the segment ================================ *)
Theorem seg_owe11_holds : seg_owe B MT K XM_LIB 11.
Proof.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & Hmo & HC &
  (Hops & _ & c & k & od & Hcur & Hkat & Hrec & Hkk & Hod & Hrc & Hwrc & Hwl & Hwk & Hwd & R22)).
assert (Hk0 : kj = 0) by (unfold EV_LIB in Hkj; lia). subst kj.
replace (owe_pc 11) with O11_PC by reflexivity.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in Hchi.
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as Happ.
pose proof Hkat as (HK & Hwf).
pose proof HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lbytes & _ & _ & Lwant).
pose proof Hrec as (_ & _ & Hrdr & _ & _). unfold rdr_kZ, reader_ok in Hrdr. rewrite Hkk in Hrdr.
destruct Hrdr as (Ha32 & Hb32 & _ & _ & _ & Fbytes & Hn24 & _ & _ & H11).
destruct (H11 eq_refl) as (Ha8 & Hb8). clear H11.
pose proof HC as (_ & _ & R2 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (Fsp : FA g pos + 512 <= sp1 - 4096) by (clear - Hfceil Hsp0c Hsp Hsp047 FFS C1 C2 C3 C4 C5; lia).
pose proof (o11_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 0 c k HJ Hfr HC Hcur Hkat Hwrc ltac:(lia) ltac:(lia)
  ltac:(lia) Fbytes) as HS.
pose proof (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 0 c (o11_ys k) HJ Hfr HC) as SHK0.
remember (bm_env g pos c regs2 (o11_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 (o11_ys k)) E) by (subst E; apply env_agree_refl).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (subst E; rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply bm_ew_F).
assert (UF : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply bm_ew_SB).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_a k)) by (subst E; exact (o11_ew_y g pos c regs2 k 0)).
assert (E38 : ew E 38 = Z_to_bv 64 (kz_b k)) by (subst E; exact (o11_ew_y g pos c regs2 k 1)).
assert (E39 : ew E 39 = Z_to_bv 64 (kz_n k)) by (subst E; exact (o11_ew_y g pos c regs2 k 2)).
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2))
  by (subst E; apply Forall_cons; [exact SHK0 | apply Forall_nil]).
clear HEE SHK0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 O11_PC) with (Z_to_bv 64 O11_PC).
(* 0x82e60-0x82e68: a = k.a, bltu a,128 *)
cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
cw_branch Hb1.
all: o11_liftb Hb1 37%nat E37 F37; rewrite branch_ltu_U, (U_atom _ 37 (kz_a k) F37), U_lit in Hb1 by lia.
- (* a < 128: 0x82edc a2 = k.b, bne a2,0x70 *)
  apply Z.ltb_lt in Hb1.
  cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
  cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
  cw_branch Hb2.
  all: o11_liftb Hb2 38%nat E38 F38; rewrite branch_ne_U, (U_atom _ 38 (kz_b k) F38), U_lit in Hb2 by lia.
  + (* b <> 0x70: 0x82f90 bltu 127,a2 *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
    cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
    cw_branch Hb3.
    all: o11_liftb Hb3 38%nat E38 F38'; rewrite branch_ltu_U, U_lit, (U_atom _ 38 (kz_b k) F38') in Hb3 by lia.
    * (* b > 127: E_RANGE (0x82dc8) *)
      apply Z.ltb_lt in Hb3.
      cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
      cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
      assert (Hf : fst (owe_kZ k od) = E_RANGE) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_b; lia).
      o11_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
    * (* b <= 127: 0x82f98 a4 = k.n, the n test *)
      apply Z.ltb_ge in Hb3.
      cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
      cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
      cw_branch Hb4.
      all: o11_liftb Hb4 39%nat E39 F39;
        rewrite branch_ltu_U, U_lit, U_SOff, F39, unsigned_lit_small, o11_ntest in Hb4 by lia.
      -- (* n < 20: the loop *)
         apply Z.ltb_lt in Hb4.
         cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) O11_CNT.
         cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
         (* the state at 0x83038 (beqz a4): the loop, o11_loop0 *)
         rename HS into HS4. rename HJ into HJ4. rename KE into KE4. rename SHOK into SHOK4.
         lazymatch goal with HS4 : st_ok _ ?Ev _ (restrict _ ?msv) |- _ =>
           rename msv into ms4;
           o11_lift Ev 33%nat E33 G33; o11_lift Ev 39%nat E39 G39; o11_lift Ev 32%nat E32 G32;
           o11_lift Ev 2%nat E2 G2 end.
         o11_rreg HS4 (10%bv : bv 5) Q10. o11_rreg HS4 (13%bv : bv 5) Q13. o11_rreg HS4 (15%bv : bv 5) Q15.
         o11_rreg HS4 (14%bv : bv 5) Q14. o11_rreg HS4 (21%bv : bv 5) Q21. o11_rreg HS4 (9%bv : bv 5) Q9.
         o11_rreg HS4 (25%bv : bv 5) Q25.
         rewrite (bm_den_off _ 33 (FA g pos) 232 G33) in Q10, Q13 by lia.
         rewrite (bm_den_off _ 39 (kz_n k) 0 G39), Z.add_0_r in Q15, Q14 by lia.
         rewrite (bm_den_off _ 32 SB 0 G32), Z.add_0_r in Q21 by (unfold SB; lia).
         rewrite (bm_den_off _ 2 sp1 0 G2), Z.add_0_r in Q9 by lia.
         rewrite (bm_den_off _ 33 (FA g pos) 448 G33) in Q25 by lia.
         (* the spill 128(sp1) = F + 448 *)
         o11_region HS4 3%nat Hr3.
         change (ms_mem (restrict (w_H W2) ms4)) with (mrestrict (w_H W2) (ms_mem ms4)) in Hr3.
         assert (U2r : bv_unsigned (ew _ 2) = sp1) by (rewrite G2; apply unsigned_lit_small; lia).
         pose proof (field_of_region _ _ 2 sp1 _ 16 160 0 0 128 8 (SOff 33 448) (FA g pos + 448) Hr3 U2r
           ltac:(o11_in) ltac:(apply (bm_den_off _ 33 (FA g pos) 448 G33); lia) ltac:(cbn; lia) ltac:(lia)) as V9.
         change (N.to_nat 8) with 8%nat in V9.
         assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
           by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
         assert (SH4 : forall i, 0 <= i < 60 ->
           aview tfibsegs (w_H W2) (ms_mem ms4) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
         { intros i Hi. rewrite KE4; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
           exact (o11_shadow_out (FA g pos) sp1 i Hf64 Happ ltac:(lia) Hi). }
         pose proof (block_shadow_range (aview tfibsegs (w_H W2) (ms_mem ms4)) SHADOW_OFF (FA g pos + 192) 184
           (FA g pos + 232) (kz_n k) (o10_bs_k W2 (ms_mem ms4) (FA g pos) Hf64 SH4) ltac:(lia) ltac:(lia)) as RA4.
         assert (BY4 : forall j, 0 <= j < kz_n k ->
           aview tfibsegs (w_H W2) (ms_mem ms4) (FA g pos + 232 + j) = Some (nth (Z.to_nat j) (kz_bytes k) 0) /\
           0 <= nth (Z.to_nat j) (kz_bytes k) 0 < 256).
         { intros j Hj. destruct (Gbytes (Z.to_nat j) ltac:(lia)) as (Vj & Rj). rewrite Z2Nat.id in Vj by lia.
           split; [|exact Rj]. rewrite KE4 by (unfold o11_zerr; lia).
           apply o10_aview_vm1; [|exact Rj]. replace (FA g pos + 232 + j) with (FA g pos + 192 + 40 + j) by lia. exact Vj. }
         assert (ERR : forall regs' mem' md' j,
           ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
             mem' md' 0 ->
           (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr (ms_regs ms4) r) ->
           0 <= j < kz_n k -> (forall l, 0 <= l < j -> nth (Z.to_nat l) (kz_bytes k) 0 < 128) ->
           128 <= nth (Z.to_nat j) (kz_bytes k) 0 ->
           (forall x, mrestrict (w_H W2) mem' x = mrestrict (w_H W2) (ms_mem ms4) x) ->
           SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 O11_ERR) mem' (seg_rom tfibsegs)) md')
             (inv_chk B MT K XM_LIB g pos sp1 ops)).
         { intros regs' mem' md' j HJ Hk' Hj Hpre Hbad M'.
           lazymatch type of HS4 with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
             pose proof (st_ok_after_stretch tfibsegs 100 Ev ssv (restrict (w_H W2) msv) regs' (mrestrict (w_H W2) mem')
               (ss_mem ssv) O11_ERR O11_CLOB HS4 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk'
               ltac:(apply Forall_forall; intros r _; apply o11_kept_eq; exact M')) as HS end.
           rewrite <- restrict_mkst_fx in HS.
           assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
             aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
           { intros a Ha Hz. rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' a (M' _)). exact (KE4 a Ha Hz). }
           clear HS4 HJ4 KE4 SHOK4.
           o11_liftS 33%nat E33 L33r. o11_liftS 32%nat E32 L32r.
           lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
             assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] Ev (mrestrict (w_H W2) mem'));
             [ apply Forall_cons; [|apply Forall_nil];
               apply (o11_shk W2 mem' Ev (FA g pos) Hf64 Happ); [|exact L33r | exact L32r];
               intros i Hi; rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' _ (M' _)); exact (SH4 i Hi) | ] end.
           (* 0x82dc8-0x82dd0: want_rc = -11, s9 = 128(s1) *)
           cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
           cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
           assert (Hf : fst (owe_kZ k od) = E_RANGE).
           { unfold owe_kZ. rewrite Hkk. apply o11_fail_s; [lia | lia | lia | lia |].
             rewrite Forall_forall in Fbytes.
             apply (o11_sb_false _ _ j); [lia | rewrite Lbytes; lia | exact Hbad |].
             apply Fbytes. apply nth_In. lia. }
           o11_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
         assert (OK : forall regs' mem' md',
           ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
             mem' md' 0 ->
           (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr (ms_regs ms4) r) ->
           (forall l, 0 <= l < kz_n k -> nth (Z.to_nat l) (kz_bytes k) 0 < 128) ->
           (forall x, mrestrict (w_H W2) mem' x = mrestrict (w_H W2) (ms_mem ms4) x) ->
           SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 O11_OK) mem' (seg_rom tfibsegs)) md')
             (inv_chk B MT K XM_LIB g pos sp1 ops)).
         { intros regs' mem' md' HJ Hk' Hall M'.
           lazymatch type of HS4 with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
             pose proof (st_ok_after_stretch tfibsegs 100 Ev ssv (restrict (w_H W2) msv) regs' (mrestrict (w_H W2) mem')
               (ss_mem ssv) O11_OK O11_CLOB HS4 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk'
               ltac:(apply Forall_forall; intros r _; apply o11_kept_eq; exact M')) as HS end.
           rewrite <- restrict_mkst_fx in HS.
           assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
             aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
           { intros a Ha Hz. rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' a (M' _)). exact (KE4 a Ha Hz). }
           clear HS4 HJ4 KE4 SHOK4.
           o11_liftS 33%nat E33 L33r. o11_liftS 32%nat E32 L32r.
           lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
             assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] Ev (mrestrict (w_H W2) mem'));
             [ apply Forall_cons; [|apply Forall_nil];
               apply (o11_shk W2 mem' Ev (FA g pos) Hf64 Happ); [|exact L33r | exact L32r];
               intros i Hi; rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' _ (M' _)); exact (SH4 i Hi) | ] end.
           (* 0x8307c-0x8308c: the arguments, jal owe_sysex *)
           cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) 0x84e8c.
           cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
           lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ => rename msv into msc end.
           o11_liftS 33%nat E33 Y33. o11_liftS 37%nat E37 Y37. o11_liftS 38%nat E38 Y38. o11_liftS 39%nat E39 Y39.
           (* want_rc still reads 0: the run wrote no byte *)
           o11_region HS 5%nat Hr5.
           change (ms_mem (restrict (w_H W2) msc)) with (mrestrict (w_H W2) (ms_mem msc)) in Hr5.
           assert (UFc : bv_unsigned (ew _ 33) = FA g pos) by (rewrite Y33; apply unsigned_lit_small; lia).
           pose proof (field_of_region _ _ 33 (FA g pos) _ 332 336 332 336 332 4 (SLit 0) 0 Hr5 UFc ltac:(o11_in) eq_refl
             ltac:(cbn; lia) ltac:(lia)) as V332c.
           change (N.to_nat 4) with 4%nat in V332c.
           assert (KEc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
             aview tfibsegs (w_H W2) (ms_mem msc) a = aview tfibsegs (w_H W2) mem2 a).
           { intros a Ha Hz.
             destruct (Z_lt_le_dec a (FA g pos + 332)) as [Hlo | Hlo];
               [|destruct (Z_lt_le_dec a (FA g pos + 336)) as [Hhi | Hhi]].
             - apply KE; [exact Ha | unfold o11_zerr; lia].
             - apply (o11_same _ _ _ (FA g pos + 332) 4 0 V332c); [|cbn; lia].
               rewrite Hwrc in Vwrc. replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. exact Vwrc.
             - apply KE; [exact Ha | unfold o11_zerr; lia]. }
           lazymatch goal with HS : st_ok _ ?Ev _ (restrict _ msc) |- _ =>
             assert (HAEc : env_agree 37 (bm_env g pos c regs2 (o11_ys k)) Ev) by env_agree_chain HAE end.
           destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 0 (o11_ys k) _ _ msc _
             HJ0 Hfr HC Hops Hcur Hkat HJ HAEc HS eq_refl ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; o11_in) KEc) as (HCc & Hopsc & Hcurc & Hkatc).
           (* the arguments *)
           o11_rreg HS (1%bv : bv 5) Gra. o11_rreg HS (10%bv : bv 5) Ga0. o11_rreg HS (11%bv : bv 5) Ga1.
           o11_rreg HS (12%bv : bv 5) Ga2. o11_rreg HS (13%bv : bv 5) Ga3. o11_rreg HS (14%bv : bv 5) Ga4.
           rewrite (bm_den_off _ 33 (FA g pos) 192 Y33) in Ga0 by lia.
           rewrite (bm_den_off _ 33 (FA g pos) 232 Y33) in Ga3 by lia.
           rewrite (bm_den_off _ 39 (kz_n k) 0 Y39), Z.add_0_r in Ga4 by lia.
           o11_byte_reg Ga1 37%nat Y37 (kz_a k). o11_byte_reg Ga2 38%nat Y38 (kz_b k).
           set (bs := firstn (Z.to_nat (kz_n k)) (kz_bytes k)).
           assert (Lbs : length bs = Z.to_nat (kz_n k)) by (unfold bs; rewrite length_firstn, Lbytes; lia).
           pose proof (firstn_skipn (Z.to_nat (kz_n k)) (kz_bytes k)) as FSk.
           assert (Fbs : Forall (fun x => 0 <= x < 256) bs).
           { pose proof Fbytes as Fb. rewrite <- FSk in Fb. apply Forall_app in Fb as (Fb1 & _). exact Fb1. }
           assert (Hspec : owe_kZ k od = (0, (fst (owe_sx (kz_a k) (kz_b k) bs), 0, snd (owe_sx (kz_a k) (kz_b k) bs)))).
           { unfold owe_kZ. rewrite Hkk.
             rewrite o11_ok by (first [lia | apply o11_sb_true; [lia | rewrite Lbytes; lia | exact Fbytes | exact Hall]]).
             unfold u8. rewrite (Z.mod_small (kz_a k) 256), (Z.mod_small (kz_b k) 256) by lia. reflexivity. }
           pose proof HCc as HSHc. do 47 (destruct HSHc as (_ & HSHc)). destruct HSHc as (HSHc & _).
           pose proof (o10_bs_k W2 (ms_mem msc) (FA g pos) Hf64 HSHc) as BSc.
           pose proof HJ as (HARc & _).
           pose proof satU_T_main_owe_sysex as HT1. pose proof satU_T_main_fits as HT2.
           eapply cpw_call with (P := inv_chk B MT K XM_LIB g pos sp1 ops);
             [exact HS | reflexivity | | intros W' c' HP; apply SRr_ret; exact HP].
           cbn [ss_pc].
           apply (bm_owe_sysex_at B MT K XM_LIB LAWS MTL OSX (inv_chk B MT K XM_LIB g pos sp1 ops) g pos sp1 (shm 0) (FA g pos + 448)
             ly2 S2 W2 (ms_regs msc) (ms_mem msc) _ c k (kz_a k) (kz_b k) (FA g pos + 232) bs 0x83090
             HJ Hfr Hmo (mcom_sh_of B MT K XM_LIB g pos sp1 0 ly2 S2 W2 _ _ _ HCc) Hcurc Hkatc).
           - pose proof bmain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
             intros i Hi. apply (Hk23 0 i). lia.
           - exact Ga0.
           - split; [lia | exact Ga1].
           - split; [lia | exact Ga2].
           - exact Ga3.
           - rewrite Lbs, Z2Nat.id by lia. exact Ga4.
           - rewrite Lbs. lia.
           - rewrite Lbs, Z2Nat.id by lia.
             exact (satU_main_bytes_rd_n tfibsegs B LAWS ly2 S2 W2 (ms_mem msc) _ sp1 TB_owe_sysex pos (FA g pos)
               LLVMF_STK (e_sp0 g) (kz_n k) HARc Hin EFA Hf64 ltac:(lia) ltac:(lia) BSc ltac:(lia) ltac:(lia)).
           - intros _. split; [lia|]. split; [|left; rewrite Lbs, Z2Nat.id by lia; lia].
             intros j Hj. rewrite Lbs in Hj. unfold bs. rewrite nth_firstn.
             destruct (Nat.ltb_spec j (Z.to_nat (kz_n k))) as [_|]; [|lia].
             pose proof Hkatc as (HKc & _). destruct HKc as (_ & _ & _ & _ & _ & _ & _ & Gbc & _).
             destruct (Gbc j ltac:(lia)) as (Vj & Rj). split; [|exact Rj].
             replace (FA g pos + 232 + Z.of_nat j) with (FA g pos + 192 + 40 + Z.of_nat j) by lia. exact Vj.
           - exact Gra.
           - apply ret_ok_even. vm_compute. reflexivity.
           - lia.
           - (* the return address 0x83090: j CHK *)
             intros W3 ly3 S3 regs3 mem3 md3 HJ3 Hfr3 Hmo3 HC3 Hcur3 HPR Hk3 KF.
             destruct (owe_sx (kz_a k) (kz_b k) bs) as [w dp] eqn:Esx.
             try rewrite Esx in Hspec; try rewrite Esx in Hk3. cbn [fst snd] in Hspec. cbv beta iota in Hk3.
             unfold inv_chk.
             apply (bm_jump B MT K XM_LIB LAWS g pos sp1 0 0x83090 PC_CHK _ W3 _ ltac:(vm_compute; reflexivity)
               ltac:(unfold PC_CHK; lia)); [intros ly S W regs mem mdx mdy HP; exact HP|].
             exists ly3, S3, regs3, mem3, md3, 0. split; [reflexivity|].
             split; [exact HJ3|]. split; [exact Hfr3|]. split; [exact Hkj|]. split; [exact Hmo3|].
             split; [exact (mcommon_of_sh B MT K XM_LIB g pos sp1 0 ly3 S3 W3 regs3 mem3 md3 HC3)|].
             split.
             { destruct Hopsc as (Ho1 & Ho2). split; [exact Ho1|].
               assert (HPR20 : getr regs3 20 = getr (ms_regs msc) 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
               rewrite HPR20. exact Ho2. }
             exists c, (set_wantZ k (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) dp), od.
             split; [exact Hcur3|]. split; [exact Hk3|]. split; [exact Hrec|]. split; [exact Hrc|].
             replace (set_wantZ k (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) dp)
               with (owe_setZ k 0 (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) 0 dp)
               by (unfold set_wantZ, owe_setZ; rewrite Hwrc, Hwk; reflexivity).
             apply (owe_want_ok_succ k od _ w 0 dp Hspec).
             rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
             pose proof (o11_sx_u8 (kz_a k) (kz_b k) bs Fbs) as U8. rewrite Esx in U8. cbn [fst] in U8.
             symmetry. exact U8. }
         o11_mkst.
         apply (o11_loop0 B LAWS (kz_n k) (FA g pos + 232) (kz_bytes k) W2 (ms_regs ms4) (ms_mem ms4) (ms_mem ms4) _
           LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 0 sp1 (FA g pos + 448)
           (inv_chk B MT K XM_LIB g pos sp1 ops)); [lia | lia | unfold BM_HI; lia | lia | lia | lia | lia | exact HJ4
           | exact Q10 | exact Q13 | exact Q15 | exact Q14 | exact Q21 | exact Q9 | exact Q25 | exact V9
           | intros x; reflexivity | exact BY4 | exact RA4 | appn; lia | exact ERR | exact OK].
      -- (* n >= 20: E_SPACE (0x82fa8) *)
         apply Z.ltb_ge in Hb4.
         cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
         cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
         assert (Hf : fst (owe_kZ k od) = E_SPACE) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_n; lia).
         o11_close 18446744073709551611 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
  + (* b = 0x70: E_REFUSED (0x82ee8) *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
    cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
    assert (Hf : fst (owe_kZ k od) = E_REFUSED) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_70; lia).
    o11_close 18446744073709551606 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
- (* a >= 128: E_ARG (0x82e6c) *)
  apply Z.ltb_ge in Hb1.
  cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) U2 UF EFA) PC_CHK.
  cw_keep ltac:(idtac; o11_kwr U2 UF). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k od) = E_ARG) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_a; lia).
  o11_close 18446744073709551615 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
Qed.

End b.
End a.

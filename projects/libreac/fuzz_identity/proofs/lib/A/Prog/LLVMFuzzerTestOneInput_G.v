(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module names changed; 1594 of its 1728 lines of code are new or changed and 946 lines of the source are left out. *)
(* Segment G of LLVMFuzzerTestOneInput's ASan walk: the two capacity-chosen heap buffers, 0x816e4..0x817bc
   (54 slots). seg_G of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_F_end to inv_G_end.

   The code (BASE + 0xfd8 .. BASE + 0x10b0):
     0x816e4 jal malloc                 s = buf_of(cap_fw): malloc (max cap_fw 1)
     0x816e8 beqz a0 -> abort           not taken: the block is at 4096 or above
     0x816ec .. 0x81704                 s6 = s, s11 = &id (mf+184), a0 = id.fw_milli, s5 = tb9 + 256 * tb10
     0x81708 jal reac_identity_fw_str   (id.fw_milli, s, cap_fw)
     0x81714 jal check_str              (r, s, cap_fw)
     0x81724 jal reac_identity_fw_str   (any_fw, s, cap_fw)
     0x81730 jal check_str              (r, s, cap_fw)
     0x81738 jal free                   s
     0x81744 jal malloc                 s = buf_of(cap_ver)
     0x81748 beqz a0 -> abort           not taken
     0x8176c jal reac_identity_reac_ver_str (major, minor, patch, s, cap_ver); s4 = &ef (mf+80 + 496)
     0x81778 jal check_str              (r, s, cap_ver)
     0x81780 jal free                   s
     0x81784 .. 0x817b8                 the shadow of `f` and `ef` is cleared (s3 + 58, 62, 63), mf+208 := 0, and
                                        put_dec's arguments: (&ef, &n, any_fw / 1000, 1)
   Every run between two calls is a plain run (no checked access). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
check_str reac_identity_fw_str reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require
SlotModel RcIdentModel IdentSpec reac_identity_fw_str_c reac_identity_reac_ver_str_c write_uint_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this file's address arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- facts of the plain model and of the allocator's classes, checked by computation -------------------- *)
Fixpoint g_zall (f : Z -> bool) (k : nat) (lo : Z) : bool :=
  match k with O => true | S k' => f lo && g_zall f k' (lo + 1) end.
Lemma g_zall_spec : forall f k lo, g_zall f k lo = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
intros f k. induction k as [|k IH]; intros lo H x Hx; cbn [g_zall] in H; [lia|].
apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
(* A request of at most 256 bytes is served by the primary allocator, and its class leaves room after the
   requested bytes up to the next 8-byte boundary (the chunk's tail is junk the allocator keeps mapped). *)
Definition g_tailb (n : Z) : bool :=
  from_primary n && (rz_size n + 8 * ((req_size n + 7) / 8) <=? class_size (chunk_class n)).
Lemma g_tail_small : forall n, 0 <= n <= 256 -> g_tailb n = true.
Proof. intros n Hn. apply (g_zall_spec g_tailb (Z.to_nat 257) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia]. Qed.
(* any_fw / 1000 by the listing's multiply-shift (0x81794 .. 0x817a8) *)
Definition g_divb (v : Z) : bool := (v / 8 * 8389) / 2 ^ 20 =? v / 1000.
Lemma g_div1000 : forall v, 0 <= v < 65536 -> (v / 8 * 8389) / 2 ^ 20 = v / 1000.
Proof.
intros v Hv. apply Z.eqb_eq. apply (g_zall_spec g_divb (Z.to_nat 65536) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.
(* tb9 + 256 * tb10 by the listing's slli / or (0x816f8, 0x816fc) *)
Definition g_orb (x : Z) : bool :=
  g_zall (fun y => Z.lor (Z.shiftl y 8) x =? x + 256 * y) (Z.to_nat 256) 0.
Lemma g_or_shift : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (Z.shiftl y 8) x = x + 256 * y.
Proof.
intros x y Hx Hy. apply Z.eqb_eq.
assert (H : g_orb x = true).
{ apply (g_zall_spec g_orb (Z.to_nat 256) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia]. }
apply (g_zall_spec _ (Z.to_nat 256) 0 H). rewrite Z2Nat.id by lia. lia.
Qed.

(* The symbolic state at 0x816e4. Atoms: 32 = SF, 33 = id.fw_milli, 34/35/36 = id's major/minor/patch, 37 = any_fw,
   38 = any_fw / 1000. Region 0: the machine frame (base s1 = atom 9): mf+80 = SF and mf+184 = SF+352 (read at
   0x81750 / 0x816f0), writable on mf+208 (0x81790). Region 1: `id`'s four 16-bit fields (base atom 32, read at
   0x816f4 and 0x81750..0x81758 through s11). Region 2: the frame's shadow (base s3 = atom 19), writable on the
   cells of `f` and `ef` (0x81784..0x8178c). *)
Definition g_R0 : YP09.region := YP09.mkRegion (Some 9%nat) 80 216 208 216
  [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 32 352))].
Definition g_R1 : YP09.region := YP09.mkRegion (Some 32%nat) 352 380 352 352
  [YP09.mkChunk 352 (CVal 2 (SOff 33 0)); YP09.mkChunk 374 (CVal 2 (SOff 34 0));
   YP09.mkChunk 376 (CVal 2 (SOff 35 0)); YP09.mkChunk 378 (CVal 2 (SOff 36 0))].
Definition g_R2 : YP09.region := YP09.mkRegion (Some 19%nat) 0 128 58 64 [].
Definition g_atoms : list (nat * afact) :=
  [(32%nat, mkAF 4096 140737479966720 6); (33%nat, mkAF 0 65535 0); (34%nat, mkAF 0 65535 0);
   (35%nat, mkAF 0 65535 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0)].
Definition ss_g : sstate := mkSS 0xfd8 sr_atoms [g_R0; g_R1; g_R2] None (mkFacts g_atoms [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the heap tail of a small block is visible (am_junk of the allocator's invariant) *)
Section t.
Variable segs : list Segment.
Variable B : asyms.
Lemma g_blk_tail_vis : forall ly S W mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n <= 256 ->
  p + req_size n <= a < p + 8 * ((req_size n + 7) / 8) ->
  aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a (M & _ & _) Hin Hn Ha.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (g_tail_small n Hn) as Ht. unfold g_tailb in Ht. apply andb_prop in Ht as [Hfp Ht]. apply Z.leb_le in Ht.
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (Hext : ck_extent k = class_size (chunk_class n)) by (unfold ck_extent; rewrite Hr, Hfp; reflexivity).
assert (Hrz : ck_rz k = rz_size n) by (unfold ck_rz; rewrite Hr; reflexivity).
assert (Hcn : ck_n k = req_size n) by (unfold ck_n; rewrite Hr; reflexivity).
assert (Hin : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
{ unfold ajunk. right. right. rewrite !in_app_iff. right. right. left. apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. rewrite !in_app_iff. right. right. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ Hin) as V. unfold range_vis in V. cbn [fst snd] in V.
assert (Hb : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k)) = ck_base B ly k + ck_rz k + ck_n k).
{ rewrite aeval_aoff; [unfold ck_base, sptr_addr; lia|]. intros e' He'. destruct (ck_beg k); cbn [sptr_exp] in He'; discriminate. }
rewrite Hb in V. rewrite G4 in Hu.
replace a with (ck_base B ly k + ck_rz k + ck_n k + (a - (ck_base B ly k + ck_rz k + ck_n k))) by lia.
apply V. rewrite Hext, Hrz, Hcn in *. lia.
Qed.
End t.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation MEV := (mo_malloc MT 256 + mo_free MT).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v, _inv.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
(* the call traces of the entry's allocator calls (LLVMFuzzerTestOneInput.v HUMM / HUMF) *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
  In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
    :: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code B)
    :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callees of this segment *)
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- the bytes a call of this segment keeps ---------------------------------------------------------------- *)
(* the entry's frame and its shadow, the input block, and the machine stack from mf up *)
Definition fzone (g : ectx) (pos a : Z) : Prop :=
  (SFa g pos <= a < SFa g pos + 1024) \/ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128).
Definition inblk (g : ectx) (a : Z) : Prop := 0 < e_n g /\ e_p g <= a < e_p g + e_n g.
Definition gprot (g : ectx) (pos mf a : Z) : Prop := (mf <= a < e_sp0 g) \/ fzone g pos a \/ inblk g a.
Definition gkept (g : ectx) (pos mf : Z) (W : world SEGS) (memc : word -> option byte)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  forall a, gprot g pos mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a.

(* What a boundary of the entry's journal says of the frame, the stack and the input block. *)
Lemma G_base : forall g pos lyc Sc W mem md k hs,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  frame_addr lyc 4 pos = SFa g pos /\ In (4, pos) (frames Sc) /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) /\ e_n g = Z.of_nat (length (e_pl g)) /\
  (forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + i)) /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a).
Proof.
intros g pos lyc Sc W mem md k hs HPRE HJ Hfrs Hbl.
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & HFSpres).
rewrite EFA in HF4096, HFceil, HFapp, HF64, HFpres, HFSpres.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
split; [exact EFA|]. split; [exact Hin|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFapp|]. split; [exact HF64|].
split; [clear - Hceil Hslo; lia|]. split; [exact Hsp0al|]. split; [clear - Hshi H47; lia|].
split.
{ intros Hn. destruct Hinp as [[Hn0 _] | [_ Hine]]; [clear - Hn Hn0; lia|].
  destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
split; [exact Hlen|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
intros a Ha. apply Hpres. exact Ha.
Qed.

(* A call's kept bytes, from the three clauses every call post states (acall_kept, tcj_kept, a callee journal). *)
Lemma gkept_of : forall g pos mf lyc Sc (W : world SEGS) memc (W3 : world SEGS) mem3 slo (E : Z -> Prop),
  frame_addr lyc 4 pos = SFa g pos -> In (4, pos) (frames Sc) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  alloc_ceiling <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < mf) -> ~ E a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall a, E a -> a < alloc_ceiling /\ ~ fzone g pos a /\ ~ inblk g a) ->
  gkept g pos mf W memc W3 mem3.
Proof.
intros g pos mf lyc Sc W memc W3 mem3 slo E EFA Hin Hinb Hce Hsp K1 K2 K4 HE a [Ha | [Ha | Ha]].
- apply K1; [lia | lia | intros HEa; destruct (HE a HEa) as (Hx & _); lia].
- apply (K4 4 pos a Hin).
  + unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
    change (1024 / 8) with 128. unfold fzone in Ha. destruct Ha; [left | right]; lia.
  + intros HEa. destruct (HE a HEa) as (_ & Hn & _). exact (Hn Ha).
- pose proof Ha as (Hn & Ha1 & Ha2). replace a with (e_p g + (a - e_p g)) by lia.
  apply (K2 _ _ _ (Hinb Hn)).
  + pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
  + replace (e_p g + (a - e_p g)) with a by lia. intros HEa. destruct (HE a HEa) as (_ & _ & Hn'). exact (Hn' Ha).
Qed.

(* A block of the run's own list is not one of the entry's blocks: the allocator's blocks are pairwise apart. *)
Lemma G_fresh : forall ly S (W : world SEGS) mem md (x : Z * Z) l0 E0,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l0 ++ E0) -> In x l0 -> 0 <= snd x -> ~ In x E0.
Proof.
intros ly S W mem md x l0 E0 HAR HP Hx Hn HxE.
assert (Hz : ~ zdisjoint (block_rng x) (block_rng x)).
{ destruct x as [p m]. unfold zdisjoint, block_rng. cbn [fst snd] in *. pose proof (req_size_pos m Hn). lia. }
apply in_split in Hx as (h1 & h2 & ->). apply in_split in HxE as (e1 & e2 & ->).
assert (Hin : In x (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
apply in_split in Hin as (a1 & a2 & Ea). rewrite Ea in HP.
replace ((h1 ++ x :: h2) ++ e1 ++ x :: e2) with (h1 ++ x :: (h2 ++ e1 ++ x :: e2)) in HP
  by (rewrite <- app_assoc; reflexivity).
pose proof (Permutation_app_inv a1 a2 h1 (h2 ++ e1 ++ x :: e2) x HP) as HP2.
assert (Hin2 : In x (a1 ++ a2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP2|]. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. right. left. reflexivity. }
apply in_app_or in Hin2 as [Hin2 | Hin2]; apply in_split in Hin2 as (b1 & b2 & ->).
- apply Hz. apply (sep_blocks_pos SEGS B LAWS ly S W mem md x x b1 b2 a2 HAR). rewrite Ea. rewrite <- app_assoc. reflexivity.
- apply Hz. apply (sep_blocks_pos SEGS B LAWS ly S W mem md x x a1 b1 b2 HAR). exact Ea.
Qed.

(* A block of the run's own list lies off the frame, its shadow, the input block and the stack. *)
Lemma G_blk_apart : forall g pos ly3 S3 (W3 : world SEGS) mem3 md3 hs b m,
  EPRE g -> AR SEGS B ly3 S3 W3 mem3 md3 -> frame_addr ly3 4 pos = SFa g pos -> In (4, pos) (frames S3) ->
  hblocks B g ly3 S3 hs -> In (b, m) hs ->
  In (b, m) (ablocks B ly3 S3) /\ 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m < MALLOC_MAX /\
  (forall a, b <= a < b + req_size m -> a < alloc_ceiling /\ ~ fzone g pos a /\ ~ inblk g a).
Proof.
intros g pos ly3 S3 W3 mem3 md3 hs b m HPRE HAR EFA Hin4 [Hperm Hfa] Hbm.
pose proof HPRE as (_ & _ & _ & _ & Hinp & _).
assert (Hb : In (b, m) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hbm. }
pose proof (proj1 (Forall_forall _ _) Hfa _ Hbm) as [Hb4096 Hm0]. cbn [fst snd] in Hb4096, Hm0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hbce & _ & _ & _ & Hmmax).
split; [exact Hb|]. split; [exact Hb4096|]. split; [exact Hbce|]. split; [exact Hmmax|].
intros a Ha. split; [lia|]. split.
- intros Hz. apply (block_not_frame_zone SEGS B LAWS ly3 S3 W3 mem3 md3 b m (a - b) 4 pos HAR Hb Hin4); [lia|].
  replace (b + (a - b)) with a by lia. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. unfold fzone in Hz. destruct Hz; [left | right]; lia.
- intros (Hn & Hp1 & Hp2). destruct Hinp as [[Hn0 _] | [_ Hine]]; [lia|].
  assert (Hine3 : In (e_p g, e_n g) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  assert (Hne : (b, m) <> (e_p g, e_n g)).
  { intros Heq. apply (G_fresh ly3 S3 W3 mem3 md3 (b, m) hs (ablocks B (e_ly g) (e_S g)) HAR Hperm Hbm Hm0).
    rewrite Heq. exact Hine. }
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 b m (e_p g) (e_n g) HAR Hb Hine3 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
Qed.

(* The call chain at a call the entry makes from its own frame: s0 = sp0 holds the entry's saved ra and s0, and
   above them is the entry's own chain (its pre-condition's achain), which the journal keeps. *)
Lemma G_chain : forall g pos lyc Sc (W : world SEGS) memc mdc k mf,
  EPRE g -> AJ g pos lyc Sc W memc mdc k ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  val_mem SEGS (rd W memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  exists ch, achain lyc (aview SEGS (w_H W) memc) mf (e_sp0 g) ch /\
    (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]).
Proof.
intros g pos lyc Sc W memc mdc k mf HPRE HJ Hmf Vra Vs0.
pose proof HPRE as (HFN & Hraz & _).
destruct HFN as (_ & _ & Hra40 & _ & _ & _ & _ & Hach & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
change (spZ (e_regs g)) with (e_sp0 g) in Hach.
destruct (Z_lt_le_dec (e_sp0 g) (ly_top lyc - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]. split; [|right; exists (e_sp0 g), (s0Z (e_regs g)); reflexivity].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  assert (HRAr : 0 <= RA_LLVMF < 2 ^ 64).
  { rewrite <- Hraz. unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  apply (achain_push lyc (aview SEGS (w_H (e_W g)) (e_mem g)) _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf).
  + apply (achain_ly_top (e_ly g)); [exact ETop | exact Hach].
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. exact (aview_above_of_journal B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] lyc Sc W memc mdc k HJ a Ha).
  + apply rdword_of_val_mem; [exact Vra | exact HRAr].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; exact Rs0r].
  + rewrite <- Hraz. exact Hra40.
  + clear - Hceil Hslo HSTK'. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmf. lia.
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* The meter after one allocator event. *)
Lemma G_meter : forall S0 Sc S3 k c,
  0 <= k -> k + 1 <= EV_LLVMF -> 0 <= c <= MEV ->
  mo_le MT S0 Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) -> mo_le MT Sc S3 c ->
  mo_le MT S0 S3 ((k + 1) * MEV) /\ mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV).
Proof.
intros S0 Sc S3 k c Hk0 Hk1 Hc HMLE HMOK HM3.
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
split.
- apply (mo_le_mono MT MTL _ _ (k * MEV + c)); [exact (mo_le_trans MT MTL _ _ _ _ _ HMLE HM3)|].
  assert (X : (k + 1) * MEV = k * MEV + MEV) by ring. rewrite X. lia.
- assert (X : (EV_LLVMF - k) * MEV = c + ((EV_LLVMF - k) * MEV - c)) by ring. rewrite X in HMOK.
  pose proof (mo_ok_step MT MTL Sc S3 c ((EV_LLVMF - k) * MEV - c) HMOK HM3) as HM.
  apply (mo_ok_le MT MTL S3 _ _ HM).
  assert (X2 : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring. rewrite X2. lia.
Qed.

(* One malloc from the entry's frame (amalloc04_rule through YC85.amalloc04_sub). *)
Lemma G_malloc_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs n retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  bsum hs + n <= LIVE_LLVMF -> 0 <= n <= 256 ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  getr regsT 10 = w64 n -> getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> In retk LLVMF_MALLOC_RAS ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3 res, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 (k + 1) ->
   aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   getr regs3 10 = w64 res -> 4096 <= res -> hblocks B g ly3 S3 ((res, n) :: hs) ->
   gkept g pos mf W memT W3 mem3 ->
   mo_le MT (e_S g) S3 ((k + 1) * MEV) -> mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs n retk Q HPRE HJ Hfrs Hbl Hlv Hn Hmf Hmf32 Vra Vs0
  Ha0 Rsp Rs0 Rgp Rtp Rra Hras Hretk Hreven Hk0 Hk1 HMLE HMOK Hk.
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _).
destruct (G_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (G_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach & Hsh).
assert (Hch : chain_pre lyc (aview SEGS (w_H W) memT) regsT ch).
{ apply (achain_chain_pre lyc _ mf (e_sp0 g) ch regsT Hach); [rewrite Hspt; clear - Hmf Hsp0 HSTKv; lia | exact Hs0t |].
  rewrite Hrat. clear - HBLO Hretk. lia. }
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
assert (Hmn : mo_malloc MT n <= mo_malloc MT 256) by exact (mo_malloc_mono MT MTL n 256 ltac:(lia)).
assert (Hmn0 : 0 <= mo_malloc MT n) by exact (mo_malloc_nonneg MT MTL n ltac:(lia)).
assert (Hbsum : blocks_bytes Sc = bsum hs + blocks_bytes (e_S g)).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B (e_ly g) (e_S g)).
  destruct Hbl as [Hperm _]. rewrite (bsum_perm _ _ Hperm), bsum_app. reflexivity. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W regsT memT LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k n (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + retk)) ch HJ Ha0).
  - unfold MALLOC_MAX. clear - Hn. lia.
  - rewrite Hbsum. unfold LIVE_LLVMF in *. clear - Hlv Hbb0 HLIVE. lia.
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold ASTACK. clear - Hmf HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - clear - Hnev Hnev0 Hk1 HEV. unfold EV_LLVMF in *. lia.
  - exact Hch.
  - destruct Hsh as [-> | (fp & v & ->)].
    + apply (llvmf_univ_call0 B _ (LLVMF_MALLOC_CTX RA_LLVMF) regsT HUMM). rewrite Hrat. unfold LLVMF_MALLOC_CTX.
      apply in_or_app. right. apply in_map_iff. exists retk. split; [reflexivity | exact Hras].
    + apply (llvmf_univ_call B RA_LLVMF _ (LLVMF_MALLOC_CTX RA_LLVMF) regsT fp v HUMM). rewrite Hrat.
      unfold LLVMF_MALLOC_CTX. apply in_or_app. left. apply in_map_iff. exists retk. split; [reflexivity | exact Hras].
  - apply (mo_ok_le MT MTL Sc (mo_malloc MT n) ((EV_LLVMF - k) * MEV) HMOK).
    assert (X : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring.
    assert (Y : 0 <= (EV_LLVMF - (k + 1)) * MEV) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite X. clear - Y Hmn Hmfree. lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres & Hfr3 & Hr4 & Eb3 & HK3 & HM3 & _).
destruct (G_meter (e_S g) Sc S3 k (mo_malloc MT n) Hk0 Hk1 ltac:(lia) HMLE HMOK HM3) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 ((res, n) :: hs)).
{ destruct Hbl as [Hperm Hfa]. split.
  - rewrite Eb3. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact Hperm.
  - constructor; [cbn [fst snd]; lia | exact Hfa]. }
apply (Hk W3 ly3 S3 regs3 mem3 md3 res Hwle HJ3 HP3 Hfrs3 Hres Hr4 Hbl3); [|exact HMLE3 | exact HMOK3].
destruct (G_base g pos ly3 S3 W3 mem3 md3 (k + 1) ((res, n) :: hs) HPRE HJ3 Hfrs3 Hbl3)
  as (EFA3 & Hin43 & _).
pose proof HJ3 as (HAR3 & _).
destruct (G_blk_apart g pos ly3 S3 W3 mem3 md3 ((res, n) :: hs) res n HPRE HAR3 EFA3 Hin43 Hbl3 (or_introl eq_refl))
  as (_ & _ & _ & _ & Hap).
pose proof HK3 as (K1 & K2 & _ & K4 & _).
replace (e_sp0 g + (mf - e_sp0 g) - ASTACK) with (mf - ASTACK) in K1 by ring.
replace (e_sp0 g + (mf - e_sp0 g)) with mf in K1 by ring.
apply (gkept_of g pos mf lyc Sc W memT W3 mem3 (mf - ASTACK) (fun a => res <= a < res + req_size n) EFA Hin4 Hinb);
  [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | | exact K2 | exact K4 | exact Hap].
intros a Ha1 Ha2 _. apply K1; [exact Ha1 | exact Ha2].
Qed.

(* One free of a block of the run's own list (afree04_rule through YC85.afree04_sub). *)
Lemma G_free_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs0 hs1 pa n retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc (hs0 ++ (pa, n) :: hs1) ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  getr regsT 10 = w64 pa -> getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> In retk LLVMF_FREE_RAS ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 (k + 1) ->
   aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] -> hblocks B g ly3 S3 (hs0 ++ hs1) ->
   gkept g pos mf W memT W3 mem3 ->
   mo_le MT (e_S g) S3 ((k + 1) * MEV) -> mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs0 hs1 pa n retk Q HPRE HJ Hfrs Hbl Hmf Hmf32 Vra Vs0
  Ha0 Rsp Rs0 Rgp Rtp Rra Hras Hretk Hreven Hk0 Hk1 HMLE HMOK Hk.
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & _).
destruct (G_base g pos lyc Sc W memT mdc k _ HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (G_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach & Hsh).
assert (Hch : chain_pre lyc (aview SEGS (w_H W) memT) regsT ch).
{ apply (achain_chain_pre lyc _ mf (e_sp0 g) ch regsT Hach); [rewrite Hspt; clear - Hmf Hsp0 HSTKv; lia | exact Hs0t |].
  rewrite Hrat. clear - HBLO Hretk. lia. }
assert (Hpan : In (pa, n) (hs0 ++ (pa, n) :: hs1)) by (apply in_or_app; right; left; reflexivity).
destruct (G_blk_apart g pos lyc Sc W memT mdc _ pa n HPRE HAR EFA Hin4 Hbl Hpan) as (Hin & _ & _ & _ & Hap).
assert (Hnin : ~ In (pa, n) (ablocks B (e_ly g) (e_S g))).
{ destruct Hbl as [Hperm Hfa]. pose proof (proj1 (Forall_forall _ _) Hfa _ Hpan) as [_ Hn0].
  exact (G_fresh lyc Sc W memT mdc (pa, n) _ _ HAR Hperm Hpan Hn0). }
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W regsT memT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k pa n (mf - e_sp0 g) (Z_to_bv 64 (BASE + retk)) ch HJ Hin).
  - exact Ha0.
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold ASTACK. clear - Hmf HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - clear - Hnev Hnev0 Hk1 HEV. unfold EV_LLVMF in *. lia.
  - exact Hch.
  - destruct Hsh as [-> | (fp & v & ->)].
    + apply (llvmf_univ_call0 B _ (LLVMF_FREE_CTX RA_LLVMF) regsT HUMF). rewrite Hrat. unfold LLVMF_FREE_CTX.
      apply in_or_app. right. apply in_map_iff. exists retk. split; [reflexivity | exact Hras].
    + apply (llvmf_univ_call B RA_LLVMF _ (LLVMF_FREE_CTX RA_LLVMF) regsT fp v HUMF). rewrite Hrat.
      unfold LLVMF_FREE_CTX. apply in_or_app. left. apply in_map_iff. exists retk. split; [reflexivity | exact Hras].
  - intros Hin0. exfalso. exact (Hnin Hin0).
  - apply (mo_ok_le MT MTL Sc (mo_free MT) ((EV_LLVMF - k) * MEV) HMOK).
    assert (X : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring.
    assert (Y : 0 <= (EV_LLVMF - (k + 1)) * MEV) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite X. clear - Y Hmmal. lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & E1 & E2) & Hfr3 & HK3 & HM3 & _).
destruct (G_meter (e_S g) Sc S3 k (mo_free MT) Hk0 Hk1 ltac:(lia) HMLE HMOK HM3) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 (hs0 ++ hs1)).
{ destruct Hbl as [Hperm Hfa]. split.
  - rewrite E2, <- app_assoc. apply (Permutation_app_inv l1 l2 hs0 (hs1 ++ ablocks B (e_ly g) (e_S g)) (pa, n)).
    rewrite <- E1. rewrite <- app_assoc in Hperm. exact Hperm.
  - apply Forall_app in Hfa as [Hf0 Hf1]. apply Forall_app. split; [exact Hf0|]. inversion Hf1; assumption. }
apply (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3); [|exact HMLE3 | exact HMOK3].
pose proof HK3 as (K1 & K2 & _ & K4 & _).
replace (e_sp0 g + (mf - e_sp0 g) - ASTACK) with (mf - ASTACK) in K1 by ring.
replace (e_sp0 g + (mf - e_sp0 g)) with mf in K1 by ring.
apply (gkept_of g pos mf lyc Sc W memT W3 mem3 (mf - ASTACK) (fun a => pa <= a < pa + req_size n) EFA Hin4 Hinb);
  [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | | exact K2 | exact K4 | exact Hap].
intros a Ha1 Ha2 _. apply K1; [exact Ha1 | exact Ha2].
Qed.

(* The meter after a program call: its post keeps the state's meter (HMT0). *)
Lemma G_meter0 : forall S0 Sc S3 k,
  mo_le MT S0 Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  mo_le MT S0 S3 (k * MEV) /\ mo_ok MT S3 ((EV_LLVMF - k) * MEV).
Proof.
intros S0 Sc S3 k HMLE HMOK. pose proof (HMT0 Sc S3) as H0. split.
- replace (k * MEV) with (k * MEV + 0) by ring. exact (mo_le_trans MT MTL _ _ _ _ _ HMLE H0).
- apply (mo_ok_step MT MTL Sc S3 0 ((EV_LLVMF - k) * MEV)); [rewrite Z.add_0_l; exact HMOK | exact H0].
Qed.

Lemma G_aview_present : forall (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview SEGS H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma G_garr8_aview : forall (H : word -> bool) (mem : word -> option byte) a l j,
  garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat -> aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem a l j Hg Hj. destruct (Hg j Hj) as (Hv & Hr). specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The bytes of a block of the run's own list, at the call state: where they lie and what the shadow says. *)
Lemma G_blk_facts : forall g pos lyc Sc (W : world SEGS) memc mdc k hs o m,
  EPRE g -> AJ g pos lyc Sc W memc mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs -> In (o, m) hs ->
  In (o, m) (ablocks B lyc Sc) /\ ~ In (o, m) (ablocks B (e_ly g) (e_S g)) /\
  4096 <= o /\ o mod 16 = 0 /\ o + req_size m <= alloc_ceiling /\ in_app o (req_size m) /\ 0 <= m < MALLOC_MAX /\
  (forall a, o <= a < o + req_size m -> apresent (w_H W) memc a /\ ~ aowned B lyc Sc a) /\
  block_shadow (aview SEGS (w_H W) memc) SHADOW_OFF o (req_size m) /\
  (o + req_size m <= IMG_LO \/ IMG_TOP <= o) /\
  (forall a, o <= a < o + req_size m -> a < alloc_ceiling /\ ~ fzone g pos a /\ ~ inblk g a).
Proof.
intros g pos lyc Sc W memc mdc k hs o m HPRE HJ Hfrs Hbl Hom.
destruct (G_base g pos lyc Sc W memc mdc k hs HPRE HJ Hfrs Hbl) as (EFA & Hin4 & _).
pose proof HJ as (HAR & _).
destruct (G_blk_apart g pos lyc Sc W memc mdc hs o m HPRE HAR EFA Hin4 Hbl Hom) as (Hin & Ho4096 & _ & Hmmax & Hap).
destruct (al_blocks _ _ LAWS _ _ _ _ _ o m HAR Hin) as (Ho16 & _ & Hoce & Happ & Hpres & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ o m HAR Hin) as (Hbs & _).
pose proof (blk_off_imgP B _ _ _ _ _ o m HAR Hin) as Himg.
destruct Hbl as [Hperm Hfa]. pose proof (proj1 (Forall_forall _ _) Hfa _ Hom) as [_ Hm0].
pose proof (G_fresh lyc Sc W memc mdc (o, m) hs _ HAR Hperm Hom Hm0) as Hnin.
split; [exact Hin|]. split; [exact Hnin|]. split; [exact Ho4096|]. split; [exact Ho16|]. split; [exact Hoce|].
split; [exact Happ|]. split; [exact Hmmax|]. split; [exact Hpres|]. split; [exact Hbs|]. split; [exact Himg | exact Hap].
Qed.

(* One call of reac_identity_fw_str (caller-journal form) on a block of the run's own list. *)
Lemma G_fw_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs v o c m retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  In (o, m) hs -> c <= req_size m -> 0 <= c -> 0 <= v < 65536 ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regsT 10 = w64 v -> getr regsT 11 = w64 o -> getr regsT 12 = w64 c -> getr regsT 2 = w64 mf ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 k -> aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   hblocks B g ly3 S3 hs -> gkept g pos mf W memT W3 mem3 ->
   mo_le MT (e_S g) S3 (k * MEV) -> mo_ok MT S3 ((EV_LLVMF - k) * MEV) ->
   (if reac_identity_fw_str.fw_writes o c
    then getr regs3 10 = w64 (reac_identity_fw_str_c.L v) /\
         garr8 SEGS (rd W3 mem3) o (reac_identity_fw_str.fw_bytes v)
    else getr regs3 10 = w64 (-1)) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs v o c m retk Q HPRE HJ Hfrs Hbl Hom Hcm Hc0 Hv Hmf Hmf32
  R10 R11 R12 Rsp Rra Hretk Hreven HMLE HMOK Hk.
destruct (G_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
destruct (G_blk_facts g pos lyc Sc W memT mdc k hs o m HPRE HJ Hfrs Hbl Hom)
  as (Hin & Hnin & Ho4096 & Ho16 & Hoce & Happ & Hmmax & Hpres & Hbs & Himg & Hap).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
pose proof (req_size_pos m ltac:(lia)) as Hrq.
eapply SRr_bind.
{ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k
    regsT v o c HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - exact R10.
  - exact R11.
  - exact R12.
  - exact Hv.
  - clear - Ho4096 Hoce Hrq C1. lia.
  - clear - Hcm Hc0 Hoce Hrq Ho4096 C1. lia.
  - rewrite Hspt. clear - Hmf32. lia.
  - rewrite Hspt. unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK.
    clear - Hmf HSTKv. lia.
  - rewrite Hspt. clear - Hmf. lia.
  - intros Hw. unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hw]. apply Z.leb_le in Hw.
    assert (Hfn : reac_identity_fw_str.fw_n v <= 7).
    { destruct (Z_lt_le_dec v 10000).
      - rewrite reac_identity_fw_str.fw_n_short by lia. lia.
      - rewrite reac_identity_fw_str.fw_n_long by lia. lia. }
    assert (Hfn0 : 0 <= reac_identity_fw_str.fw_n v).
    { unfold reac_identity_fw_str.fw_n, reac_identity_fw_str_c.L. lia. }
    split; [|split].
    + intros a Ha. left. exists o, m. split; [exact Hin | lia].
    + intros a Ha. destruct (Hpres a ltac:(lia)) as [Hp Hno]. split; [|split; [exact Hp | split; [exact Hno|]]].
      * right. right. left. exists o, m. split; [exact Hin|]. split; [exact Hnin | lia].
      * rewrite Hspt. unfold ESTACK. clear - Ha Hoce Hcm Hw Hfn Hmf Hsp0 HSTKv. lia.
    + apply (block_shadow_range _ _ o (req_size m) o (reac_identity_fw_str.fw_n v) Hbs); lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfr3 & Hperm3 & Hres).
rewrite Rra.
destruct (G_meter0 (e_S g) Sc S3 k HMLE HMOK) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 hs).
{ destruct Hbl as [Hperm Hfa]. split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm] | exact Hfa]. }
assert (HKP : forall E : Z -> Prop, (forall a, E a -> o <= a < o + req_size m) ->
  tcj_kept B reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK lyc Sc W memT W3 mem3 (spZ regsT) E ->
  gkept g pos mf W memT W3 mem3).
{ intros E HE (K1 & K2 & _ & K4 & _). rewrite Hspt in K1.
  apply (gkept_of g pos mf lyc Sc W memT W3 mem3 (mf - reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK) E EFA Hin4 Hinb);
    [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | exact K1 | exact K2 | exact K4 |].
  intros a Ha. exact (Hap a (HE a Ha)). }
destruct (reac_identity_fw_str.fw_writes o c) eqn:Ew.
- destruct Hres as (Hr10 & Hg & HK).
  apply (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3); [| exact HMLE3 | exact HMOK3 | split; [exact Hr10 | exact Hg]].
  apply (HKP (fun a => o <= a < o + reac_identity_fw_str.fw_n v)); [|exact HK]. intros a Ha.
  unfold reac_identity_fw_str.fw_writes in Ew. apply andb_prop in Ew as [_ Ew]. apply Z.leb_le in Ew.
  assert (Hfn : reac_identity_fw_str.fw_n v <= 7).
  { destruct (Z_lt_le_dec v 10000).
    - rewrite reac_identity_fw_str.fw_n_short by lia. lia.
    - rewrite reac_identity_fw_str.fw_n_long by lia. lia. }
  lia.
- destruct Hres as (Hr10 & HK).
  apply (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3); [| exact HMLE3 | exact HMOK3 | exact Hr10].
  apply (HKP (fun _ => False)); [intros a [] | exact HK].
Qed.

(* One call of reac_identity_reac_ver_str (caller-journal form) on a block of the run's own list. *)
Lemma G_vs_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs ma mi pa o c m retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  In (o, m) hs -> c <= req_size m -> 0 <= c -> 0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regsT 10 = w64 ma -> getr regsT 11 = w64 mi -> getr regsT 12 = w64 pa ->
  getr regsT 13 = w64 o -> getr regsT 14 = w64 c -> getr regsT 2 = w64 mf ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 k -> aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   hblocks B g ly3 S3 hs -> gkept g pos mf W memT W3 mem3 ->
   mo_le MT (e_S g) S3 (k * MEV) -> mo_ok MT S3 ((EV_LLVMF - k) * MEV) ->
   (if reac_identity_reac_ver_str.rvs_fails o c
    then getr regs3 10 = w64 (-1)
    else getr regs3 10 = w64 (reac_identity_reac_ver_str.rvs_LV ma mi pa) /\
         garr8 SEGS (rd W3 mem3) o (reac_identity_reac_ver_str.rvs_bytes ma mi pa)) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs ma mi pa o c m retk Q HPRE HJ Hfrs Hbl Hom Hcm Hc0 Hma Hmi Hpa Hmf Hmf32
  R10 R11 R12 R13 R14 Rsp Rgp Rtp Rra Hretk Hreven HMLE HMOK Hk.
destruct (G_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
destruct (G_blk_facts g pos lyc Sc W memT mdc k hs o m HPRE HJ Hfrs Hbl Hom)
  as (Hin & Hnin & Ho4096 & Ho16 & Hoce & Happ & Hmmax & Hpres & Hbs & Himg & Hap).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
pose proof (req_size_pos m ltac:(lia)) as Hrq.
assert (HLV : reac_identity_reac_ver_str.rvs_LV ma mi pa <= 16).
{ rewrite reac_identity_reac_ver_str.rvs_LV_eq.
  pose proof (reac_identity_reac_ver_str.rvs_n_range ma). pose proof (reac_identity_reac_ver_str.rvs_n_range mi).
  pose proof (reac_identity_reac_ver_str.rvs_n_range pa). destruct (pa <? 10); lia. }
assert (HLV0 : 0 <= reac_identity_reac_ver_str.rvs_LV ma mi pa)
  by (unfold reac_identity_reac_ver_str.rvs_LV, reac_identity_reac_ver_str_c.reac_ver_str_LV; lia).
eapply SRr_bind.
{ apply (HVS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k
    regsT ma mi pa o c HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - rewrite Hrat. clear - HBLO Hretk. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite Hspt. clear - Hmf32. lia.
  - rewrite Hspt. unfold reac_identity_reac_ver_str.REAC_VER_STR_STK, write_uint.WRITE_UINT_STK, ESTACK.
    clear - Hmf HSTKv. lia.
  - rewrite Hspt. clear - Hmf. lia.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - exact R14.
  - exact Hma.
  - exact Hmi.
  - exact Hpa.
  - clear - Ho4096 Hoce Hrq C1. lia.
  - clear - Hcm Hc0 Hoce Hrq Ho4096 C1. lia.
  - intros Hf. unfold reac_identity_reac_ver_str.rvs_fails in Hf. apply orb_false_iff in Hf as [_ Hf].
    apply Z.ltb_ge in Hf.
    split; [|split].
    + intros a Ha. destruct (Hpres a ltac:(lia)) as [Hp Hno]. split; [|split; [exact Hp | split; [exact Hno|]]].
      * right. right. left. exists o, m. split; [exact Hin|]. split; [exact Hnin | lia].
      * rewrite Hspt. unfold ESTACK. clear - Ha Hoce Hcm Hf Hmf Hsp0 HSTKv. lia.
    + left. exists o, m. split; [exact Hin | lia].
    + apply (block_shadow_range _ _ o (req_size m) o 20 Hbs); lia.
  - rewrite Hfrs. cbn. lia. }
cbv beta. intros W3 c3 Hwle (-> & ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hperm3 & Hfr3 & Hres).
rewrite Rra. change (k + reac_identity_reac_ver_str.EV_REAC_VER_STR) with (k + 0) in HJ3. rewrite Z.add_0_r in HJ3.
destruct (G_meter0 (e_S g) Sc S3 k HMLE HMOK) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 hs).
{ destruct Hbl as [Hperm Hfa]. split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm] | exact Hfa]. }
assert (HKP : forall E : Z -> Prop, (forall a, E a -> o <= a < o + req_size m) ->
  tcj_kept B reac_identity_reac_ver_str.REAC_VER_STR_STK lyc Sc W memT W mem3 (spZ regsT) E ->
  gkept g pos mf W memT W mem3).
{ intros E HE (K1 & K2 & _ & K4 & _). rewrite Hspt in K1.
  apply (gkept_of g pos mf lyc Sc W memT W mem3 (mf - reac_identity_reac_ver_str.REAC_VER_STR_STK) E EFA Hin4 Hinb);
    [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | exact K1 | exact K2 | exact K4 |].
  intros a Ha. exact (Hap a (HE a Ha)). }
destruct (reac_identity_reac_ver_str.rvs_fails o c) eqn:Ef.
- destruct Hres as (Hr10 & HK).
  apply (Hk W ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3); [| exact HMLE3 | exact HMOK3 | exact Hr10].
  apply (HKP (fun _ => False)); [intros a [] | exact HK].
- destruct Hres as (Hr10 & Hg & HK).
  apply (Hk W ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3); [| exact HMLE3 | exact HMOK3 | split; [exact Hr10 | exact Hg]].
  apply (HKP (fun a => o <= a < o + reac_identity_reac_ver_str.rvs_LV ma mi pa + 1)); [|exact HK]. intros a Ha.
  unfold reac_identity_reac_ver_str.rvs_fails in Ef. apply orb_false_iff in Ef as [_ Ef]. apply Z.ltb_ge in Ef. lia.
Qed.

(* One call of check_str (afn_pre form, through YC85.cl_callS) on a string in a block of the run's own list. *)
Lemma G_cs_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs r o c m (l : list Z) retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  getr regsT 10 = w64 r -> getr regsT 11 = w64 o -> getr regsT 12 = w64 c ->
  getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  - 2 ^ 31 <= r < 2 ^ 31 -> 0 <= c < 2 ^ 64 ->
  (0 <= r -> In (o, m) hs /\ 0 <= m <= 256 /\ r < c /\ c <= req_size m /\ Z.of_nat (length l) = r /\
             Forall (fun b => b <> 0) l /\ garr8 SEGS (rd W memT) o (l ++ [0])) ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 k -> aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   hblocks B g ly3 S3 hs -> gkept g pos mf W memT W3 mem3 ->
   mo_le MT (e_S g) S3 (k * MEV) -> mo_ok MT S3 ((EV_LLVMF - k) * MEV) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_check_str)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs r o c m l retk Q HPRE HJ Hfrs Hbl Hmf Hmf32 Vra Vs0
  R10 R11 R12 Rsp Rs0 Rgp Rtp Rra Hretk Hreven Hr Hc Hstr HMLE HMOK Hk.
pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _).
destruct (G_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (G_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach & _).
(* the image's read-only bytes, at the call state *)
assert (Haro : aro_unowned SEGS B (aview SEGS (w_H W) memT)).
{ apply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi).
  apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k HJ).
  apply HRO. exact HROS. }
(* what check_str asks of the string when r >= 0 *)
assert (Hok : 0 <= r -> check_str.tcheck_str_ok W regsT memT r o c).
{ intros Hr0. destruct (Hstr Hr0) as (Hom & Hm & Hrc & Hcm & Hlen & Hnz & Hg).
  destruct (G_blk_facts g pos lyc Sc W memT mdc k hs o m HPRE HJ Hfrs Hbl Hom)
    as (Hin & _ & Ho4096 & Ho16 & Hoce & Happ & _ & Hpres & Hbs & Himg & _).
  pose proof (req_size_pos m ltac:(lia)) as Hrq.
  assert (Hll : length (l ++ [0]) = S (length l)) by (rewrite length_app; cbn; lia).
  split; [exact Hrc|]. split; [lia|]. split; [destruct Himg; [left | right]; lia|].
  split.
  { split; [lia|]. split.
    - intros i Hi. exists (nth (Z.to_nat i) (l ++ [0]) 0). split.
      + replace (o + i) with (o + Z.of_nat (Z.to_nat i)) by lia. apply G_garr8_aview; [exact Hg | lia].
      + rewrite app_nth1 by lia. apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
    - intros _. replace (o + r) with (o + Z.of_nat (length l)) by lia.
      rewrite (G_garr8_aview _ _ o (l ++ [0]) (length l) Hg ltac:(lia)). rewrite app_nth2 by lia.
      rewrite Nat.sub_diag. reflexivity. }
  split; [intros a Ha; rewrite Hspt; unfold check_str.CHECK_STR_STK, ESTACK; clear - Ha Hoce Hcm Hrc Hmf Hsp0 HSTKv; lia|].
  split; [apply (amem_range_sub_app o (req_size m) o (r + 1) Happ Hoce); lia|].
  split; [apply (block_shadow_range _ _ o (req_size m) o (r + 1) Hbs); lia|].
  split; [apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT mdc o m o (r + 1) HAR Hin); lia|].
  intros a Ha.
  destruct (Z_lt_le_dec a (o + req_size m)) as [Hlt | Hge].
  - apply G_aview_present. exact (proj1 (Hpres a ltac:(lia))).
  - apply (g_blk_tail_vis SEGS B lyc Sc W memT mdc o m a HAR Hin Hm). split; [exact Hge|].
    pose proof (Z.div_mod (o + r) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (o + r) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod (req_size m + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (req_size m + 7) 8 ltac:(lia)) as D4.
    pose proof (Z.div_mod o 16 ltac:(lia)) as D5. rewrite Ho16, Z.add_0_r in D5.
    lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W regsT memT (Z_to_bv 64 (BASE + AF_check_str)) LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k check_str.CHECK_STR_STK [] 0 (mf - e_sp0 g)
    (getr regsT 1) ch (fun ly' S' W' _ _ _ => ly' = lyc /\ S' = Sc /\ W' = W) HJ).
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold check_str.CHECK_STR_STK, ESTACK. lia.
  - unfold check_str.CHECK_STR_STK, ESTACK. clear - Hmf HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - change (4096 <= raZ regsT). rewrite Hrat. clear - HBLO Hretk. lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by ring. rewrite Hs0t. exact Hach.
  - intros HPRE1. exact (HCHK lyc Sc W regsT memT mdc ch r o c HPRE1 Haro R10 R11 R12 Hr Hc Hok).
  - intros a (rg & [] & _). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJ1 & HP3 & (-> & -> & ->)).
rewrite Rra in *. rewrite Z.add_0_r in HJ3.
apply (Hk W lyc Sc regs3 mem3 md3 Hwle HJ3 HP3 Hfrs Hbl); [| exact HMLE | exact HMOK].
replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJ1 by ring.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
apply (gkept_of g pos mf lyc Sc W memT W mem3 (mf - check_str.CHECK_STR_STK) (fun _ => False) EFA Hin4 Hinb);
  [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | | | | intros a []].
- intros a Ha1 Ha2 _. apply F1; [exact Ha1 | exact Ha2].
- intros b mm i Hb Hi _. apply (F2 b mm i Hb Hb Hi). intros (rg & [] & _).
- intros cid ps a Hcp Hr' _. apply (F4 cid ps a Hcp Hr'). intros (rg & [] & _).
Qed.

(* ---- the walk's own small facts ----------------------------------------------------------------------------- *)
Lemma G_nth_map : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = RcIdentModel.bz (RcIdentModel.nthb l j).
Proof.
intros l j Hj. unfold RcIdentModel.bz, RcIdentModel.nthb.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; lia).
apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.
Lemma G_val2_garr8 : forall (m : word -> option byte) a l j,
  garr8 SEGS m a l -> (S j < length l)%nat ->
  val_mem SEGS m (a + Z.of_nat j) 2 (nth j l 0 + 256 * nth (S j) l 0).
Proof.
intros m a l j Hg Hj k Hk. destruct (Hg j ltac:(lia)) as (H0 & R0). destruct (Hg (S j) Hj) as (H1 & R1).
specialize (H0 0%nat ltac:(lia)). specialize (H1 0%nat ltac:(lia)). rewrite Z.add_0_r in H0, H1.
set (b0 := nth j l 0) in *. set (b1 := nth (S j) l 0) in *.
assert (k = 0 \/ k = 1)%nat as [-> | ->] by lia.
- rewrite Z.add_0_r, H0. f_equal. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite !Z.shiftr_0_r. rewrite !Z.mod_small by lia. lia.
- replace (a + Z.of_nat j + Z.of_nat 1) with (a + Z.of_nat (S j)) by lia. rewrite H1. f_equal. f_equal.
  unfold YO0f.le_byte.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia. rewrite !Z.mod_small by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma G_region_kept : forall E (H H' : word -> bool) (m m' : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m' a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H' m' a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m' n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma G_garr8_moved : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 _); [|exact Hv].
intros kk Hkk. rewrite <- !Z.add_assoc. apply Hk. lia.
Qed.
Lemma G_zshadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.

(* The cells the segment itself writes: mf+208 and the shadow of `f` and `ef`. *)
Definition gwin (g : ectx) (pos mf a : Z) : Prop :=
  (mf + 208 <= a < mf + 216) \/ (shadow_addr (SFa g pos) + 58 <= a < shadow_addr (SFa g pos) + 64).
(* the caller-saved a0 of a call's post is atom k + 4 of the havoc after the call (CLOB lists x10 fifth) *)
Lemma G_ew_a0 : forall E k (regs : bvmap 5 word) n, n = (k + 4)%nat ->
  ew (havoc E k (map (getr regs) CLOB)) n = getr regs 10.
Proof. intros E k regs n ->. rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (cbn; lia). reflexivity. Qed.
(* the three register expressions of the segment the engine leaves symbolic *)
Lemma G_den_or : forall E x y, bv_unsigned (ew E 18) = y -> bv_unsigned (ew E 21) = x -> 0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 18 0) (SLit 8)) (SOff 21 0)) = Z_to_bv 64 (x + 256 * y).
Proof.
intros E x y H18 H21 Hx Hy. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 18 0) (SLit 8)) (SOff 21 0))))
  with (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 18 0) (SLit 8)) (SOff 21 0))).
rewrite !U_SAlu, !U_SOff, U_SLit, H18, H21, !Z.add_0_r. cbn [zalu_raw]. unfold zcanon, M64.
change (Z.land (8 mod 2 ^ 64) 63) with 8.
rewrite (Z.mod_small y) by lia. rewrite (Z.mod_small x) by lia.
rewrite (Z.mod_small (Z.shiftl y 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite g_or_shift by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite ?Z.mod_small by lia. reflexivity.
Qed.
Lemma G_den_seqz : forall E c, bv_unsigned (ew E 25) = c -> 0 <= c < 32 ->
  sv_denot E (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SLTU (SOff 25 0) (SLit 1))) = Z_to_bv 64 (Z.max c 1).
Proof.
intros E c H25 Hc. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SLTU (SOff 25 0) (SLit 1)))))
  with (U E (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SLTU (SOff 25 0) (SLit 1)))).
rewrite !U_SAlu, !U_SOff, U_SLit, H25, !Z.add_0_r. cbn [zalu_raw]. unfold zcanon, M64.
change (1 mod 2 ^ 64) with 1. rewrite (Z.mod_small c) by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec c 1); rewrite !Z.mod_small; lia.
Qed.
Definition G_div_sv : sv :=
  SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_SLL (SOff 37 0) (SLit 48)) (SLit 51)) (SLit 8389)) (SLit 20).
Lemma G_den_div : forall E v, bv_unsigned (ew E 37) = v -> 0 <= v < 65536 ->
  sv_denot E G_div_sv = Z_to_bv 64 (v / 1000) /\ sv_denot E (SAlu ALU_ADD G_div_sv (SLit 0)) = Z_to_bv 64 (v / 1000).
Proof.
intros E v H37 Hv.
assert (HU : U E G_div_sv = v / 1000).
{ unfold G_div_sv. rewrite !U_SAlu, U_SMd, !U_SAlu, U_SOff, !U_SLit, H37, Z.add_0_r. cbn [zalu_raw zmd_raw].
  unfold zcanon, M64.
  change (Z.land (48 mod 2 ^ 64) 63) with 48. change (Z.land (51 mod 2 ^ 64) 63) with 51.
  change (Z.land (20 mod 2 ^ 64) 63) with 20. change (8389 mod 2 ^ 64) with 8389.
  rewrite (Z.mod_small v) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (v * 2 ^ 48)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. replace (v * 2 ^ 48 / 2 ^ 51) with (v / 8)
    by (change (2 ^ 51) with (2 ^ 48 * 8); rewrite <- Z.div_div by lia; rewrite Z.div_mul by lia; reflexivity).
  rewrite (Z.mod_small (v / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (v / 8 * 8389)) by (split; [pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)); lia |
    assert (v / 8 < 8192) by (apply Z.div_lt_upper_bound; lia); lia]).
  rewrite g_div1000 by lia.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
split.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E G_div_sv)) with (U E G_div_sv). rewrite HU.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E (SAlu ALU_ADD G_div_sv (SLit 0))))
    with (U E (SAlu ALU_ADD G_div_sv (SLit 0))).
  rewrite U_SAlu, U_SLit, HU. cbn [zalu_raw]. unfold zcanon, M64. change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  assert (0 <= v / 1000 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite !Z.mod_small by lia. reflexivity.
Qed.
(* The runs of this segment write only the two windows of ss_g (mf+208 and the shadow cells of `f` / `ef`). *)
Lemma G_awr : forall g pos mf E lyc bl0 blc (rs : smem),
  windows rs = [(Some 9%nat, 208, 216); (Some 32%nat, 352, 352); (Some 19%nat, 58, 64)] ->
  bv_unsigned (ew E 9) = mf -> frame_addr lyc 4 pos = SFa g pos -> bv_unsigned (ew E 19) = shadow_addr (SFa g pos) ->
  e_sp0 g - LLVMF_STK <= mf + 208 -> mf + 216 <= e_sp0 g ->
  awr_ok E rs LLVMF_STK (e_sp0 g) [] bl0 blc lyc [(4, pos)].
Proof.
intros g pos mf E lyc bl0 blc rs Hw U9 EFA U19 H1 H2 a Hin.
destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). rewrite Hw in Hi.
cbn [In] in Hi. destruct Hi as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
- left. rewrite U9 in Hr. lia.
- lia.
- right; right; right. exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EFA. rewrite U19 in Hr. change (fs_frame_bytes 4 / 8) with 128. lia.
Qed.
Lemma G_keep_run : forall g pos mf E (H : word -> bool) (m m' : word -> option byte) (rs : smem),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  windows rs = [(Some 9%nat, 208, 216); (Some 32%nat, 352, 352); (Some 19%nat, 58, 64)] ->
  bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 19) = shadow_addr (SFa g pos) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ gwin g pos mf a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros g pos mf E H m m' rs HF Hw U9 U19 a Ha Hn.
apply (kept_of_frame E rs H m m' (gwin g pos mf) HF); [|exact Ha|exact Hn].
intros b wlo whi aa Hi Hr. rewrite Hw in Hi.
cbn [In] in Hi. destruct Hi as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
- left. rewrite U9 in Hr. lia.
- lia.
- right. rewrite U19 in Hr. lia.
Qed.
Lemma G_bshadow_moved : forall (rd rd' : reader) Bs p n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs p + i) = rd (shadow_of_addr Bs p + i)) ->
  block_shadow rd Bs p n -> block_shadow rd' Bs p n.
Proof.
intros rd rd' Bs p n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.
Lemma G_aview_val1 : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview SEGS H mem a = Some v.
Proof.
intros H mem a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ---- the strings the two formatters print, as check_str asks for them ------------------------------------ *)
Lemma G_lsd_dg : forall k v b, In b (write_uint_c.write_uint_lsd k v) ->
  exists d, 0 <= d <= 9 /\ b = write_uint_c.write_uint_dg d.
Proof.
induction k as [|k IH]; intros v b Hb; cbn [write_uint_c.write_uint_lsd In] in Hb; [destruct Hb|].
destruct Hb as [<- | Hb].
- exists (v mod 10). split; [pose proof (Z.mod_pos_bound v 10 ltac:(lia)); lia | reflexivity].
- destruct (v <? 10); [destruct Hb | exact (IH (v / 10) b Hb)].
Qed.
Lemma G_dg_nz : forall d, 0 <= d <= 9 -> bv_unsigned (write_uint_c.write_uint_dg d) <> 0.
Proof.
intros d Hd. unfold write_uint_c.write_uint_dg. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma G_ver_nz : forall ma mi pa, 0 <= pa ->
  Forall (fun b => b <> 0) (map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa)).
Proof.
intros ma mi pa Hpa. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
assert (HD : forall v b, In b (write_uint_c.write_uint_D v) -> bv_unsigned b <> 0).
{ intros v b0 Hb0. unfold write_uint_c.write_uint_D in Hb0. apply in_rev in Hb0.
  destruct (G_lsd_dg 5 v b0 Hb0) as (d & Hd & ->). exact (G_dg_nz d Hd). }
unfold reac_identity_reac_ver_str_c.reac_ver_str_VER in Hb. rewrite !in_app_iff in Hb.
destruct Hb as [Hb | [Hb | [Hb | Hb]]].
- exact (HD ma b Hb).
- destruct Hb as [<- | []]. intros Hc. vm_compute in Hc. discriminate Hc.
- exact (HD mi b Hb).
- unfold reac_identity_reac_ver_str_c.reac_ver_str_DEC2 in Hb. destruct (Z.ltb_spec pa 10) as [Hl | Hl].
  + destruct Hb as [<- | [<- | []]]; apply G_dg_nz; lia.
  + exact (HD pa b Hb).
Qed.
Lemma G_fw_cs_pre : forall (W : world SEGS) mem hs s v c m,
  In (s, m) hs -> 0 <= v < 65536 -> 0 <= m <= 256 -> c <= req_size m ->
  (if reac_identity_fw_str.fw_writes s c then garr8 SEGS (rd W mem) s (reac_identity_fw_str.fw_bytes v) else True) ->
  0 <= (if reac_identity_fw_str.fw_writes s c then reac_identity_fw_str_c.L v else -1) ->
  In (s, m) hs /\ 0 <= m <= 256 /\ (if reac_identity_fw_str.fw_writes s c then reac_identity_fw_str_c.L v else -1) < c /\
  c <= req_size m /\
  Z.of_nat (length (map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW v))) =
    (if reac_identity_fw_str.fw_writes s c then reac_identity_fw_str_c.L v else -1) /\
  Forall (fun b => b <> 0) (map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW v)) /\
  garr8 SEGS (rd W mem) s (map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW v) ++ [0]).
Proof.
intros W mem hs s v c m Hin Hv Hm Hcm Hg Hr.
destruct (reac_identity_fw_str.fw_writes s c) eqn:Ew; [|lia].
unfold reac_identity_fw_str.fw_writes in Ew. apply andb_prop in Ew as [_ Ew]. apply Z.leb_le in Ew.
pose proof (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v Hv)) as HL.
split; [exact Hin|]. split; [exact Hm|]. split; [destruct (v <? 10000); lia|]. split; [exact Hcm|].
split; [rewrite length_map; unfold reac_identity_fw_str_c.L; reflexivity|].
split.
- apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
  exact (reac_identity_fw_str_c.reac_identity_fw_str_c3_nz v Hv b Hb).
- unfold reac_identity_fw_str.fw_bytes in Hg. rewrite map_app in Hg. exact Hg.
Qed.
Lemma G_vs_cs_pre : forall (W : world SEGS) mem hs s ma mi pa c m,
  In (s, m) hs -> 0 <= pa -> 0 <= m <= 256 -> c <= req_size m ->
  (if reac_identity_reac_ver_str.rvs_fails s c then True
   else garr8 SEGS (rd W mem) s (reac_identity_reac_ver_str.rvs_bytes ma mi pa)) ->
  0 <= (if reac_identity_reac_ver_str.rvs_fails s c then -1 else reac_identity_reac_ver_str.rvs_LV ma mi pa) ->
  In (s, m) hs /\ 0 <= m <= 256 /\
  (if reac_identity_reac_ver_str.rvs_fails s c then -1 else reac_identity_reac_ver_str.rvs_LV ma mi pa) < c /\
  c <= req_size m /\
  Z.of_nat (length (map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa))) =
    (if reac_identity_reac_ver_str.rvs_fails s c then -1 else reac_identity_reac_ver_str.rvs_LV ma mi pa) /\
  Forall (fun b => b <> 0) (map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa)) /\
  garr8 SEGS (rd W mem) s
    (map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa) ++ [0]).
Proof.
intros W mem hs s ma mi pa c m Hin Hpa Hm Hcm Hg Hr.
destruct (reac_identity_reac_ver_str.rvs_fails s c) eqn:Ef; [lia|].
unfold reac_identity_reac_ver_str.rvs_fails in Ef. apply orb_false_iff in Ef as [_ Ef]. apply Z.ltb_ge in Ef.
assert (HLV : reac_identity_reac_ver_str.rvs_LV ma mi pa <= 16).
{ rewrite reac_identity_reac_ver_str.rvs_LV_eq.
  pose proof (reac_identity_reac_ver_str.rvs_n_range ma). pose proof (reac_identity_reac_ver_str.rvs_n_range mi).
  pose proof (reac_identity_reac_ver_str.rvs_n_range pa). destruct (pa <? 10); lia. }
split; [exact Hin|]. split; [exact Hm|]. split; [lia|]. split; [exact Hcm|].
split; [rewrite length_map; reflexivity|].
split; [exact (G_ver_nz ma mi pa Hpa) | exact Hg].
Qed.

(* a register the engine left as the havoc atom of a call's a0 *)
Ltac g_a0 Q regs :=
  match type of Q with context [nth 4 (map (getr regs) CLOB) ?d] =>
    change (nth 4 (map (getr regs) CLOB) d) with (getr regs 10%bv) in Q end.
(* One plain run to the next call: the run writes only ss_g's two windows, so KP (what the run has kept since
   0x816e4) moves to the call state; KR is what the run itself kept (for the heap). *)
Ltac g_run HS HJ EFAc U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv :=
  paj_run_shc RUNP RUNC HS HJ;
  [ eapply G_awr; [reflexivity | exact U9 | exact EFAc | exact U19 | clear - Hmfb HSTKv; lia | clear - Hmfb; lia]
  | match goal with HFr : frame_of _ _ (mrestrict (w_H ?Wc) ?mc) (mrestrict _ ?mn) |- _ =>
      let KR := fresh "KR" in
      assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ gwin g pos mf a -> aview SEGS (w_H Wc) mn a = aview SEGS (w_H Wc) mc a)
        by (eapply G_keep_run; [exact HFr | reflexivity | exact U9 | exact U19]);
      let KP' := fresh "KP" in
      assert (KP' : forall x, gprot g pos mf x -> ~ gwin g pos mf x ->
        aview SEGS (w_H Wc) mn x = aview SEGS (w_H W2) mem2 x)
        by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
            intros x Hx Hw; rewrite (KR x (HPR x Hx) Hw); exact (KP x Hx Hw));
      clear KP; rename KP' into KP
    end;
    match goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG end ].
(* After a call: the three regions are kept (G_region_kept from the call's gkept and the presence of the windows
   at the new state), the caller-saved registers are havoc'd at atoms k .. k + 15, and U9 / U19 / U32 / KP move to
   the new state. *)
Ltac g_post HS k regs3 W3 mem3 HP3 HGK HFSp3 HSp3 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv :=
  let HS3 := fresh "HS3" in
  jafter_call_keep_hi HS k regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat; 1%nat; 2%nat] HS3;
  match type of HS3 with ?Q -> _ =>
    let HQ := fresh "HQ" in assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end;
  [ cbn [ms_mem restrict]; constructor; [|constructor; [|constructor; [|constructor]]];
    [ apply (G_region_kept _ _ _ _ _ 9 mf _ _ _ _ _ U9);
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HGK; left; clear - Ha Hmfb; lia
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HSp3; clear - Ha Hmfb HSTKv; lia ]
    | apply (G_region_kept _ _ _ _ _ 32 (SFa g pos) _ _ _ _ _ U32);
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HGK; right; left; left; clear - Ha; lia
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; clear - Ha; lia ]
    | apply (G_region_kept _ _ _ _ _ 19 (shadow_addr (SFa g pos)) _ _ _ _ _ U19);
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HGK; right; left; right; clear - Ha; lia
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        replace a with (shadow_addr (SFa g pos) + (a - shadow_addr (SFa g pos))) by ring;
        apply HFSp3; clear - Ha; lia ] ]
  | clear HS; rewrite <- restrict_mkst_fx in HS3; rename HS3 into HS;
    lazymatch type of HS with st_ok_pi _ _ (havoc ?Ec _ ?ws) _ _ =>
      let HEc := lazymatch goal with H : img_env _ _ Ec |- _ => H end in
      let HEI' := fresh "HEI" in pose proof (img_env_havoc_hi Ec k ws HEc ltac:(cbv; lia)) as HEI';
      let H9 := fresh "U9" in
      assert (H9 : bv_unsigned (ew (havoc Ec k ws) 9) = mf) by (rewrite ew_havoc_old by lia; exact U9);
      clear U9; rename H9 into U9;
      let H19 := fresh "U19" in
      assert (H19 : bv_unsigned (ew (havoc Ec k ws) 19) = shadow_addr (SFa g pos)) by (rewrite ew_havoc_old by lia; exact U19);
      clear U19; rename H19 into U19;
      let H32 := fresh "U32" in
      assert (H32 : bv_unsigned (ew (havoc Ec k ws) 32) = SFa g pos) by (rewrite ew_havoc_old by lia; exact U32);
      clear U32; rename H32 into U32
    end;
    let KP' := fresh "KP" in
    assert (KP' : forall x, gprot g pos mf x -> ~ gwin g pos mf x ->
      aview SEGS (w_H W3) mem3 x = aview SEGS (w_H W2) mem2 x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
          intros x Hx Hw; rewrite (HGK x Hx); exact (KP x Hx Hw));
    clear KP HGK; rename KP' into KP ].

Theorem seg_G_holds : seg_G B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hid & Hhw & Hbl & Hid3 & Hmid & R10 & R20 & R25 & R26 & R24 & R23 & R21 & R18 &
  V160 & V168 & V144 & V136).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
destruct (G_base g pos ly2 S2 W2 mem2 md2 _ [] HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb2 & Hlen & HFpres & HFSpres & HSpres).
(* the model *)
set (inp := e_pl g) in *.
set (idb := m_id g (m_nrec g)) in *.
assert (Hidl : length idb = 38%nat) by (unfold idb, m_id; apply SlotModel.rec_id_length).
set (fwm := RcIdentModel.fw_milli idb). set (ma := RcIdentModel.major idb).
set (mi := RcIdentModel.minor idb). set (pa := RcIdentModel.patch idb).
set (fwv := SlotModel.t_any_fw inp).
pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 9)) as Ht9.
pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 10)) as Ht10.
change (SlotModel.inb inp (SlotModel.cT inp + 9)) with (SlotModel.tb inp 9) in Ht9.
change (SlotModel.inb inp (SlotModel.cT inp + 10)) with (SlotModel.tb inp 10) in Ht10.
assert (Hfwv : fwv = SlotModel.tb inp 9 + 256 * SlotModel.tb inp 10) by reflexivity.
assert (Hbz : forall j, 0 <= RcIdentModel.bz (RcIdentModel.nthb idb j) < 256)
  by (intros j; unfold RcIdentModel.bz; apply (bv_unsigned_in_range 8)).
assert (Rfwm : 0 <= fwm < 65536) by (unfold fwm, RcIdentModel.fw_milli; pose proof (Hbz 0%nat); pose proof (Hbz 1%nat); lia).
assert (Rma : 0 <= ma < 65536) by (unfold ma, RcIdentModel.major; pose proof (Hbz 22%nat); pose proof (Hbz 23%nat); lia).
assert (Rmi : 0 <= mi < 65536) by (unfold mi, RcIdentModel.minor; pose proof (Hbz 24%nat); pose proof (Hbz 25%nat); lia).
assert (Rpa : 0 <= pa < 65536) by (unfold pa, RcIdentModel.patch; pose proof (Hbz 26%nat); pose proof (Hbz 27%nat); lia).
assert (Rfwv : 0 <= fwv < 65536) by lia.
(* id's four fields in memory *)
destruct Hid as (Hidb & Hidz & Hidk).
unfold bytes_at8 in Hidb.
assert (VID : forall j, (S j < 38)%nat ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + 352 + Z.of_nat j) 2
    (RcIdentModel.bz (RcIdentModel.nthb idb j) + 256 * RcIdentModel.bz (RcIdentModel.nthb idb (S j)))).
{ intros j Hj. rewrite <- !G_nth_map by lia. apply (G_val2_garr8 _ _ _ j Hidb). rewrite length_map. fold idb. lia. }
pose proof (VID 0%nat ltac:(lia)) as Vfwm. pose proof (VID 22%nat ltac:(lia)) as Vma.
pose proof (VID 24%nat ltac:(lia)) as Vmi. pose proof (VID 26%nat ltac:(lia)) as Vpa.
fold fwm in Vfwm. fold ma in Vma. fold mi in Vmi. fold pa in Vpa. clear VID.
change (Z.of_nat 0) with 0 in Vfwm. change (Z.of_nat 22) with 22 in Vma. change (Z.of_nat 24) with 24 in Vmi.
change (Z.of_nat 26) with 26 in Vpa.
replace (SFa g pos + 352 + 0) with (SFa g pos + 352) in Vfwm by ring.
replace (SFa g pos + 352 + 22) with (SFa g pos + 374) in Vma by ring.
replace (SFa g pos + 352 + 24) with (SFa g pos + 376) in Vmi by ring.
replace (SFa g pos + 352 + 26) with (SFa g pos + 378) in Vpa by ring.
(* ranges *)
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hsp0 HSTKv; lia).
assert (Hsh1 : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1. lia. }
assert (HSFr : 0 <= SFa g pos < 2 ^ 64) by (clear - HSF0 HSF1 C1; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf0 Hmfb Hsp47 C1; lia).
(* the environment: atoms 32 .. 38 *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (SFa g pos); Z_to_bv 64 fwm; Z_to_bv 64 ma; Z_to_bv 64 mi; Z_to_bv 64 pa;
  Z_to_bv 64 fwv; Z_to_bv 64 (fwv / 1000)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 fwm)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ma)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 mi)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 pa)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 fwv)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (fwv / 1000))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. exact Hmfr. }
assert (U19 : bv_unsigned (ew E 19) = shadow_addr (SFa g pos)).
{ rewrite (EE 19%nat 19%bv eq_refl), Rs3. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
assert (U32 : bv_unsigned (ew E 32) = SFa g pos) by (rewrite E32; apply unsigned_lit_small; exact HSFr).
(* the symbolic state at 0x816e4 *)
assert (HS : st_ok_pi SEGS VAL E ss_g
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xfd8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_g. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold g_R0, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmfr; lia|]. split; [clear - Hmf0 Hmfb Hsp47; lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HSpres. clear - Ho Hmfb HSTKv. lia.
      * constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val SEGS E _ mf 80 8 (SOff 32 0) (SFa g pos));
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HSFr | lia | exact V80].
        -- apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 352) (SFa g pos + 352));
           [cbn [sv_denot]; rewrite U32; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HSF0 HSF1 C1; lia | lia | exact Hmid].
    + unfold g_R1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [clear - HSFr; lia|]. split; [clear - HSF0 HSF1 C1; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val SEGS E _ (SFa g pos) 352 2 (SOff 33 0) fwm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 2)) with 65536; exact Rfwm | lia | exact Vfwm].
      * apply (chunk_ok_val SEGS E _ (SFa g pos) 374 2 (SOff 34 0) ma);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 2)) with 65536; exact Rma | lia | exact Vma].
      * apply (chunk_ok_val SEGS E _ (SFa g pos) 376 2 (SOff 35 0) mi);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 2)) with 65536; exact Rmi | lia | exact Vmi].
      * apply (chunk_ok_val SEGS E _ (SFa g pos) 378 2 (SOff 36 0) pa);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 2)) with 65536; exact Rpa | lia | exact Vpa].
    + unfold g_R2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply HFSpres. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, g_R0, g_R1, g_R2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U19.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp. unfold shadow_addr, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; clear - HSF0 HSF1 HSFapp Hmf0 C1 Hsh1; lia.
  - unfold facts_ok, g_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U32, E33, E34, E35, E36, E37.
    rewrite (unsigned_lit_small fwm) by (clear - Rfwm; lia). rewrite (unsigned_lit_small ma) by (clear - Rma; lia).
    rewrite (unsigned_lit_small mi) by (clear - Rmi; lia). rewrite (unsigned_lit_small pa) by (clear - Rpa; lia).
    rewrite (unsigned_lit_small fwv) by (clear - Rfwv; lia).
    change (2 ^ 6) with 64. rewrite Z.pow_0_r, !Z.mod_1_r.
    clear - HSF0 HSF1 HSF64 C1 Rfwm Rma Rmi Rpa Rfwv. repeat split; lia. }
unfold cfg_at. change (w64 (BASE + 0xfd8)) with (Z_to_bv 64 (BASE + 0xfd8)).
(* what the stack and frame bytes are, as long as the run keeps them *)
assert (VMK : forall (W' : world SEGS) mem' a (n : nat) v,
  (forall x, gprot g pos mf x -> ~ gwin g pos mf x -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W2) mem2 x) ->
  ((mf <= a /\ a + Z.of_nat n <= e_sp0 g) \/ (SFa g pos <= a /\ a + Z.of_nat n <= SFa g pos + 1024)) ->
  (a + Z.of_nat n <= mf + 208 \/ mf + 216 <= a) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W' mem') a n v).
{ intros W' mem' a n v HK Ha Hw Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W') mem2 mem' a a n v); [|exact Hv].
  intros kk Hkk. apply HK.
  - unfold gprot, fzone. destruct Ha as [Ha | Ha]; [left | right; left; left]; lia.
  - unfold gwin. intros [Hx | Hx]; [lia|]. unfold shadow_addr, SHADOW_OFF in Hx.
    destruct Ha as [Ha | Ha]; [clear - Ha Hx Hmf0 Hsh1 HSF0 HSF1 C1 Hkk; unfold shadow_addr, SHADOW_OFF in *; lia|].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
    clear - Ha Hx HSFapp HSF0 HSF1 C1 Hkk. lia. }
(* ---- run 1: the jal at 0x816e4 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply G_awr; [reflexivity | exact U9 | exact EFA | exact U19 | clear - Hmfb HSTKv; lia | clear - Hmfb; lia]. }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ gwin g pos mf a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (eapply G_keep_run; [exact HFr | reflexivity | exact U9 | exact U19]).
clear HF HFr HG.
prreg HS (10%bv : bv 5) Q10. prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (pal_malloc B TL).
(* facts of the run used at every call *)
assert (Hnr : 0 <= Z.of_nat (m_nrec g) <= 64).
{ unfold m_nrec, SlotModel.nrecn. pose proof (SlotModel.nrec_range inp) as Hn. fold inp. clear - Hn. lia. }
assert (Hcfw : 0 <= SlotModel.t_cap_fw inp < 16).
{ unfold SlotModel.t_cap_fw. apply Z.mod_pos_bound. lia. }
assert (Hcver : 0 <= SlotModel.t_cap_ver inp < 32).
{ unfold SlotModel.t_cap_ver. apply Z.mod_pos_bound. lia. }
assert (HPR : forall x, gprot g pos mf x -> 0 <= x < 2 ^ 64).
{ pose proof HJ as (HARj & _).
  intros x [Hx | [Hx | Hx]].
  - clear - Hx Hmfr Hsp47 Hmfb. lia.
  - unfold fzone in Hx. clear - Hx HSFr HSF1 Hsh1 C1. lia.
  - destruct Hx as (Hn & Hx1 & Hx2). pose proof (Hinb2 Hn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARj Hin) as (_ & Hp4096 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)). clear - Hx1 Hx2 Hp4096 Hpce C1 H. lia. }
assert (KP : forall x, gprot g pos mf x -> ~ gwin g pos mf x ->
  aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x)
  by (intros x Hx Hw; apply KR; [exact (HPR x Hx) | exact Hw]).
clear KR.
assert (VRA : forall (W' : world SEGS) mem',
  (forall x, gprot g pos mf x -> ~ gwin g pos mf x -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W2) mem2 x) ->
  val_mem SEGS (rd W' mem') (e_sp0 g - 8) 8 RA_LLVMF /\ val_mem SEGS (rd W' mem') (e_sp0 g - 16) 8 (s0Z (e_regs g))).
{ intros W' mem' HK. split; (apply (VMK W' mem' _ 8%nat _ HK); [left; clear - Hmfb; lia | right; clear - Hmfb; lia | assumption]). }
(* heap bytes are off the two windows *)
assert (HWH : forall a, 4096 <= a < alloc_ceiling -> (exists p n, in_app p n /\ p <= a < p + n) -> ~ gwin g pos mf a).
{ intros a Ha (p & n & Happ & Hpa) [Hw | Hw]; [clear - Ha Hw Hmf0; lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in Hw.
  clear - Happ Hpa Hw HSF0 HSF1 C1. lia. }
(* ---- the first malloc: s = buf_of(cap_fw) ---- *)
eapply (G_malloc_at g pos mf W2 _ _ _ ly2 S2 _ [] (Z.max (SlotModel.t_cap_fw inp) 1) 0xfdc);
  [exact HPRE | exact HJ | exact Hfrs | exact Hbl | cbn [bsum fold_right]; unfold LIVE_LLVMF; clear - Hcfw; lia
  | clear - Hcfw; lia | exact Hmfb | exact Hmf32 | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | cbn; tauto | lia | reflexivity
  | clear - Hk; lia | clear - Hnr Hk; unfold EV_LLVMF; lia | exact MLE | exact MOK | ].
intros W3 ly3 S3 regs3 mem3 md3 s1 Hwle3 HJ3 HP3 Hfrs3 Hr10 Hs1 Hbl3 HGK MLE3 MOK3.
clear Q10 Q2 Q8 Q3 Q4 Q1.
destruct (G_base g pos ly3 S3 W3 mem3 md3 _ _ HPRE HJ3 Hfrs3 Hbl3)
  as (EFA3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp3 & HSp3).
destruct (G_blk_facts g pos ly3 S3 W3 mem3 md3 _ _ s1 _ HPRE HJ3 Hfrs3 Hbl3 (or_introl eq_refl))
  as (_ & _ & Hs14096 & _ & Hs1ce & Hs1app & _).
assert (Hs1r : 4096 <= s1 /\ s1 + Z.max (SlotModel.t_cap_fw inp) 1 <= alloc_ceiling).
{ pose proof (req_size_pos (Z.max (SlotModel.t_cap_fw inp) 1) ltac:(lia)) as Hq. clear - Hs14096 Hs1ce Hq. lia. }
g_post HS 512%nat regs3 W3 mem3 HP3 HGK HFSp3 HSp3 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* the block is at 4096 or above: the beqz at 0x816e8 falls through *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 516 (mkAF 4096 140737479966720 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (G_ew_a0 _ 512 regs3 516 eq_refl), Hr10;
          unfold w64; rewrite unsigned_lit_small by (clear - Hs1r Hcfw C1; lia); rewrite Z.pow_0_r, Z.mod_1_r;
          clear - Hs1r Hcfw C1; lia)) as HS'
end.
clear HS. rename HS' into HS.
(* ---- run 2: 0x816e8 .. the call of reac_identity_fw_str at 0x81708 ---- *)
g_run HS HJ3 EFA3 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
(* x21 = tb9 + 256 * tb10 (0x816f8, 0x816fc): name it atom 37 *)
lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
  pose proof (st_ok_restrict_reg SEGS Hh Ev ssv msv (21%bv : bv 5) HS) as Q21;
  let e := eval vm_compute in (sr_get (ss_regs ssv) (21%bv : bv 5)) in
  change (sr_get (ss_regs ssv) (21%bv : bv 5)) with e in Q21
end.
cbn [ms_regs restrict] in Q21.
rewrite (G_den_or _ (SlotModel.tb inp 9) (SlotModel.tb inp 10)) in Q21;
  [| rewrite ew_havoc_old by lia; rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; clear - Ht10; lia
   | rewrite ew_havoc_old by lia; rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; clear - Ht9; lia
   | exact Ht9 | exact Ht10].
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_set_reg_fp SEGS Ev ssv msv (21%bv : bv 5) (SOff 37 0) HS eq_refl
    ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; rewrite E37, Z.add_0_r;
          rewrite unsigned_lit_small by (clear - Rfwv; lia); cbn [ms_regs restrict]; rewrite Q21, <- Hfwv; reflexivity))
    as HS'
end.
clear HS Q21. rename HS' into HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
rewrite E33 in Q10. g_a0 Q11 regs3. rewrite Hr10 in Q11.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
pmkst HS. rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
assert (Hn1 : SlotModel.t_cap_fw inp <= req_size (Z.max (SlotModel.t_cap_fw inp) 1)).
{ unfold req_size. destruct (Z.max (SlotModel.t_cap_fw inp) 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia. }
(* ---- reac_identity_fw_str (id.fw_milli, s, cap_fw) ---- *)
eapply (G_fw_at g pos mf W3 _ _ _ ly3 S3 _ _ fwm s1 (SlotModel.t_cap_fw inp) (Z.max (SlotModel.t_cap_fw inp) 1) 0x1000);
  [exact HPRE | exact HJ3 | exact Hfrs3 | exact Hbl3 | left; reflexivity | exact Hn1 | clear - Hcfw; lia | exact Rfwm
  | exact Hmfb | exact Hmf32 | exact Q10 | exact Q11 | exact Q12 | exact Q2 | exact Q1 | lia | reflexivity
  | exact MLE3 | exact MOK3 | ].
intros W4 ly4 S4 regs4 mem4 md4 Hwle4 HJ4 HP4 Hfrs4 Hbl4 HGK4 MLE4 MOK4 Hfw1.
clear Q10 Q11 Q12 Q2 Q1.
destruct (G_base g pos ly4 S4 W4 mem4 md4 _ _ HPRE HJ4 Hfrs4 Hbl4)
  as (EFA4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp4 & HSp4).
g_post HS 528%nat regs4 W4 mem4 HP4 HGK4 HFSp4 HSp4 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
set (r1 := if reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp) then reac_identity_fw_str_c.L fwm else -1).
assert (Hr1 : getr regs4 10 = w64 r1).
{ unfold r1. destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)); [exact (proj1 Hfw1) | exact Hfw1]. }
assert (Hr1r : - 2 ^ 31 <= r1 < 2 ^ 31).
{ unfold r1. destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)); [|lia].
  pose proof (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len fwm Rfwm)). destruct (fwm <? 10000); lia. }
(* ---- run 3: .. check_str at 0x81714 ---- *)
clear KR.
g_run HS HJ4 EFA4 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
g_a0 Q10 regs4. rewrite Hr1 in Q10. g_a0 Q11 regs3. rewrite Hr10 in Q11.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (PSIG IS_check_str AF_check_str eq_refl).
(* the string fw_str printed, at the call state *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mT _) _) _ =>
  assert (Hg1 : if reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)
                then garr8 SEGS (rd W4 mT) s1 (reac_identity_fw_str.fw_bytes fwm) else True)
end.
{ destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)) eqn:Ew; [|exact I].
  destruct Hfw1 as [_ Hg]. eapply G_garr8_moved; [|exact Hg]. intros kk Hkk.
  unfold reac_identity_fw_str.fw_writes in Ew. apply andb_prop in Ew as [_ Ew]. apply Z.leb_le in Ew.
  unfold reac_identity_fw_str.fw_bytes in Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  assert (HL : (length (reac_identity_fw_str_c.FW fwm) <= 6)%nat).
  { pose proof (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len fwm Rfwm)) as HL.
    unfold reac_identity_fw_str_c.L in HL. destruct (fwm <? 10000); lia. }
  apply KR; [clear - Hkk HL Hs1r C1; lia|]. apply HWH; [clear - Hkk HL Hs1r C1 Ew Hcfw; lia|].
  exists s1, (req_size (Z.max (SlotModel.t_cap_fw inp) 1)). split; [exact Hs1app|].
  clear - Hkk HL Hn1 Ew. lia. }
(* ---- check_str (r, s, cap_fw) ---- *)
eapply (G_cs_at g pos mf W4 _ _ _ ly4 S4 _ _ r1 s1 (SlotModel.t_cap_fw inp) (Z.max (SlotModel.t_cap_fw inp) 1)
  (map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW fwm)) 0x100c);
  [exact HPRE | exact HJ4 | exact Hfrs4 | exact Hbl4 | exact Hmfb | exact Hmf32
  | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q11 | exact Q12 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | lia | reflexivity
  | exact Hr1r | clear - Hcfw; lia
  | intros Hr0; exact (G_fw_cs_pre W4 _ [(s1, Z.max (SlotModel.t_cap_fw inp) 1)] s1 fwm _
      (Z.max (SlotModel.t_cap_fw inp) 1) (or_introl eq_refl) Rfwm ltac:(clear - Hcfw; lia) Hn1 Hg1 Hr0)
  | exact MLE4 | exact MOK4 | ].
intros W5 ly5 S5 regs5 mem5 md5 Hwle5 HJ5 HP5 Hfrs5 Hbl5 HGK5 MLE5 MOK5.
clear Q10 Q11 Q12 Q2 Q1 Q3 Q4 Q8 Hg1.
destruct (G_base g pos ly5 S5 W5 mem5 md5 _ _ HPRE HJ5 Hfrs5 Hbl5)
  as (EFA5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp5 & HSp5).
g_post HS 544%nat regs5 W5 mem5 HP5 HGK5 HFSp5 HSp5 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* ---- run 4: .. reac_identity_fw_str (any_fw, s, cap_fw) at 0x81724 ---- *)
clear KR.
g_run HS HJ5 EFA5 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
rewrite E37 in Q10. g_a0 Q11 regs3. rewrite Hr10 in Q11.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
pmkst HS. rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
eapply (G_fw_at g pos mf W5 _ _ _ ly5 S5 _ _ fwv s1 (SlotModel.t_cap_fw inp) (Z.max (SlotModel.t_cap_fw inp) 1) 0x101c);
  [exact HPRE | exact HJ5 | exact Hfrs5 | exact Hbl5 | left; reflexivity | exact Hn1 | clear - Hcfw; lia | exact Rfwv
  | exact Hmfb | exact Hmf32 | exact Q10 | exact Q11 | exact Q12 | exact Q2 | exact Q1 | lia | reflexivity
  | exact MLE5 | exact MOK5 | ].
intros W6 ly6 S6 regs6 mem6 md6 Hwle6 HJ6 HP6 Hfrs6 Hbl6 HGK6 MLE6 MOK6 Hfw2.
clear Q10 Q11 Q12 Q2 Q1.
destruct (G_base g pos ly6 S6 W6 mem6 md6 _ _ HPRE HJ6 Hfrs6 Hbl6)
  as (EFA6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp6 & HSp6).
g_post HS 560%nat regs6 W6 mem6 HP6 HGK6 HFSp6 HSp6 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
set (r2 := if reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp) then reac_identity_fw_str_c.L fwv else -1).
assert (Hr2 : getr regs6 10 = w64 r2).
{ unfold r2. destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)); [exact (proj1 Hfw2) | exact Hfw2]. }
assert (Hr2r : - 2 ^ 31 <= r2 < 2 ^ 31).
{ unfold r2. destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)); [|lia].
  pose proof (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len fwv Rfwv)). destruct (fwv <? 10000); lia. }
(* ---- run 5: .. check_str at 0x81730 ---- *)
clear KR.
g_run HS HJ6 EFA6 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
g_a0 Q10 regs6. rewrite Hr2 in Q10. g_a0 Q11 regs3. rewrite Hr10 in Q11.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (PSIG IS_check_str AF_check_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mT _) _) _ =>
  assert (Hg2 : if reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)
                then garr8 SEGS (rd W6 mT) s1 (reac_identity_fw_str.fw_bytes fwv) else True)
end.
{ destruct (reac_identity_fw_str.fw_writes s1 (SlotModel.t_cap_fw inp)) eqn:Ew; [|exact I].
  destruct Hfw2 as [_ Hg]. eapply G_garr8_moved; [|exact Hg]. intros kk Hkk.
  unfold reac_identity_fw_str.fw_writes in Ew. apply andb_prop in Ew as [_ Ew]. apply Z.leb_le in Ew.
  unfold reac_identity_fw_str.fw_bytes in Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  assert (HL : (length (reac_identity_fw_str_c.FW fwv) <= 6)%nat).
  { pose proof (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len fwv Rfwv)) as HL.
    unfold reac_identity_fw_str_c.L in HL. destruct (fwv <? 10000); lia. }
  apply KR; [clear - Hkk HL Hs1r C1; lia|]. apply HWH; [clear - Hkk HL Hs1r C1 Ew Hcfw; lia|].
  exists s1, (req_size (Z.max (SlotModel.t_cap_fw inp) 1)). split; [exact Hs1app|].
  clear - Hkk HL Hn1 Ew. lia. }
eapply (G_cs_at g pos mf W6 _ _ _ ly6 S6 _ _ r2 s1 (SlotModel.t_cap_fw inp) (Z.max (SlotModel.t_cap_fw inp) 1)
  (map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW fwv)) 0x1028);
  [exact HPRE | exact HJ6 | exact Hfrs6 | exact Hbl6 | exact Hmfb | exact Hmf32
  | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q11 | exact Q12 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | lia | reflexivity
  | exact Hr2r | clear - Hcfw; lia
  | intros Hr0; exact (G_fw_cs_pre W6 _ [(s1, Z.max (SlotModel.t_cap_fw inp) 1)] s1 fwv _
      (Z.max (SlotModel.t_cap_fw inp) 1) (or_introl eq_refl) Rfwv ltac:(clear - Hcfw; lia) Hn1 Hg2 Hr0)
  | exact MLE6 | exact MOK6 | ].
intros W7 ly7 S7 regs7 mem7 md7 Hwle7 HJ7 HP7 Hfrs7 Hbl7 HGK7 MLE7 MOK7.
clear Q10 Q11 Q12 Q2 Q1 Q3 Q4 Q8 Hg2.
destruct (G_base g pos ly7 S7 W7 mem7 md7 _ _ HPRE HJ7 Hfrs7 Hbl7)
  as (EFA7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp7 & HSp7).
g_post HS 576%nat regs7 W7 mem7 HP7 HGK7 HFSp7 HSp7 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* ---- run 6: .. free(s) at 0x81738 ---- *)
clear KR.
g_run HS HJ7 EFA7 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
g_a0 Q10 regs3. rewrite Hr10 in Q10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (pal_free B TL).
eapply (G_free_at g pos mf W7 _ _ _ ly7 S7 _ [] [] s1 (Z.max (SlotModel.t_cap_fw inp) 1) 0x1030);
  [exact HPRE | exact HJ7 | exact Hfrs7 | exact Hbl7 | exact Hmfb | exact Hmf32
  | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | cbn; tauto | lia | reflexivity
  | clear - Hk; lia | clear - Hnr Hk; unfold EV_LLVMF; lia | exact MLE7 | exact MOK7 | ].
intros W8 ly8 S8 regs8 mem8 md8 Hwle8 HJ8 HP8 Hfrs8 Hbl8 HGK8 MLE8 MOK8.
cbn [app] in Hbl8. clear Q10 Q2 Q1 Q3 Q4 Q8.
destruct (G_base g pos ly8 S8 W8 mem8 md8 _ _ HPRE HJ8 Hfrs8 Hbl8)
  as (EFA8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp8 & HSp8).
g_post HS 592%nat regs8 W8 mem8 HP8 HGK8 HFSp8 HSp8 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* ---- run 7: .. malloc(cap_ver ? cap_ver : 1) at 0x81744 ---- *)
clear KR.
g_run HS HJ8 EFA8 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
  pose proof (st_ok_restrict_reg SEGS Hh Ev ssv msv (10%bv : bv 5) HS) as Q10;
  let e := eval vm_compute in (sr_get (ss_regs ssv) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssv) (10%bv : bv 5)) with e in Q10
end.
cbn [ms_regs restrict] in Q10.
rewrite (G_den_seqz _ (SlotModel.t_cap_ver inp)) in Q10;
  [| rewrite !ew_havoc_old by lia; rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; clear - Hcver; lia
   | exact Hcver].
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (pal_malloc B TL).
eapply (G_malloc_at g pos mf W8 _ _ _ ly8 S8 _ [] (Z.max (SlotModel.t_cap_ver inp) 1) 0x103c);
  [exact HPRE | exact HJ8 | exact Hfrs8 | exact Hbl8 | cbn [bsum fold_right]; unfold LIVE_LLVMF; clear - Hcver; lia
  | clear - Hcver; lia | exact Hmfb | exact Hmf32 | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | cbn; tauto | lia | reflexivity
  | clear - Hk; lia | clear - Hnr Hk; unfold EV_LLVMF; lia | exact MLE8 | exact MOK8 | ].
intros W9 ly9 S9 regs9 mem9 md9 s2 Hwle9 HJ9 HP9 Hfrs9 Hr10b Hs2 Hbl9 HGK9 MLE9 MOK9.
clear Q10 Q2 Q8 Q3 Q4 Q1.
destruct (G_base g pos ly9 S9 W9 mem9 md9 _ _ HPRE HJ9 Hfrs9 Hbl9)
  as (EFA9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp9 & HSp9).
destruct (G_blk_facts g pos ly9 S9 W9 mem9 md9 _ _ s2 _ HPRE HJ9 Hfrs9 Hbl9 (or_introl eq_refl))
  as (_ & _ & Hs24096 & _ & Hs2ce & Hs2app & _).
assert (Hs2r : 4096 <= s2 /\ s2 + Z.max (SlotModel.t_cap_ver inp) 1 <= alloc_ceiling).
{ pose proof (req_size_pos (Z.max (SlotModel.t_cap_ver inp) 1) ltac:(lia)) as Hq. clear - Hs24096 Hs2ce Hq. lia. }
g_post HS 608%nat regs9 W9 mem9 HP9 HGK9 HFSp9 HSp9 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 612 (mkAF 4096 140737479966720 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (G_ew_a0 _ 608 regs9 612 eq_refl), Hr10b;
          unfold w64; rewrite unsigned_lit_small by (clear - Hs2r Hcver C1; lia); rewrite Z.pow_0_r, Z.mod_1_r;
          clear - Hs2r Hcver C1; lia)) as HS'
end.
clear HS. rename HS' into HS.
assert (Hn2 : SlotModel.t_cap_ver inp <= req_size (Z.max (SlotModel.t_cap_ver inp) 1)).
{ unfold req_size. destruct (Z.max (SlotModel.t_cap_ver inp) 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia. }
(* ---- run 8: .. reac_identity_reac_ver_str (major, minor, patch, s, cap_ver) at 0x8176c ---- *)
clear KR.
g_run HS HJ9 EFA9 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
rewrite E34 in Q10. rewrite E35 in Q11. rewrite E36 in Q12. g_a0 Q13 regs9. rewrite Hr10b in Q13.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Q14. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
pmkst HS. rewrite (PSIG IS_reac_identity_reac_ver_str AF_reac_identity_reac_ver_str eq_refl).
eapply (G_vs_at g pos mf W9 _ _ _ ly9 S9 _ _ ma mi pa s2 (SlotModel.t_cap_ver inp) (Z.max (SlotModel.t_cap_ver inp) 1)
  0x1064);
  [exact HPRE | exact HJ9 | exact Hfrs9 | exact Hbl9 | left; reflexivity | exact Hn2 | clear - Hcver; lia
  | exact Rma | exact Rmi | exact Rpa | exact Hmfb | exact Hmf32
  | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q2 | exact Q3 | exact Q4 | exact Q1 | lia | reflexivity
  | exact MLE9 | exact MOK9 | ].
intros W10 ly10 S10 regs10 mem10 md10 Hwle10 HJ10 HP10 Hfrs10 Hbl10 HGK10 MLE10 MOK10 Hvs.
clear Q10 Q11 Q12 Q13 Q14 Q2 Q1 Q3 Q4.
destruct (G_base g pos ly10 S10 W10 mem10 md10 _ _ HPRE HJ10 Hfrs10 Hbl10)
  as (EFA10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp10 & HSp10).
g_post HS 624%nat regs10 W10 mem10 HP10 HGK10 HFSp10 HSp10 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
set (r3 := if reac_identity_reac_ver_str.rvs_fails s2 (SlotModel.t_cap_ver inp) then -1
           else reac_identity_reac_ver_str.rvs_LV ma mi pa).
assert (Hr3 : getr regs10 10 = w64 r3).
{ unfold r3. destruct (reac_identity_reac_ver_str.rvs_fails s2 (SlotModel.t_cap_ver inp)); [exact Hvs | exact (proj1 Hvs)]. }
assert (Hr3r : - 2 ^ 31 <= r3 < 2 ^ 31).
{ unfold r3. destruct (reac_identity_reac_ver_str.rvs_fails s2 (SlotModel.t_cap_ver inp)); [lia|].
  rewrite reac_identity_reac_ver_str.rvs_LV_eq.
  pose proof (reac_identity_reac_ver_str.rvs_n_range ma). pose proof (reac_identity_reac_ver_str.rvs_n_range mi).
  pose proof (reac_identity_reac_ver_str.rvs_n_range pa). destruct (pa <? 10); lia. }
(* ---- run 9: .. check_str at 0x81778 ---- *)
clear KR.
g_run HS HJ10 EFA10 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
g_a0 Q10 regs10. rewrite Hr3 in Q10. g_a0 Q11 regs9. rewrite Hr10b in Q11.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (PSIG IS_check_str AF_check_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mT _) _) _ =>
  assert (Hg3 : if reac_identity_reac_ver_str.rvs_fails s2 (SlotModel.t_cap_ver inp) then True
                else garr8 SEGS (rd W10 mT) s2 (reac_identity_reac_ver_str.rvs_bytes ma mi pa))
end.
{ destruct (reac_identity_reac_ver_str.rvs_fails s2 (SlotModel.t_cap_ver inp)) eqn:Ef; [exact I|].
  destruct Hvs as [_ Hg]. eapply G_garr8_moved; [|exact Hg]. intros kk Hkk.
  unfold reac_identity_reac_ver_str.rvs_fails in Ef. apply orb_false_iff in Ef as [_ Ef]. apply Z.ltb_ge in Ef.
  unfold reac_identity_reac_ver_str.rvs_bytes in Hkk. rewrite length_app, length_map in Hkk. cbn [length] in Hkk.
  assert (HL : (length (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa) <= 16)%nat).
  { pose proof (reac_identity_reac_ver_str.rvs_LV_eq ma mi pa) as HL.
    unfold reac_identity_reac_ver_str.rvs_LV, reac_identity_reac_ver_str_c.reac_ver_str_LV in HL.
    pose proof (reac_identity_reac_ver_str.rvs_n_range ma). pose proof (reac_identity_reac_ver_str.rvs_n_range mi).
    pose proof (reac_identity_reac_ver_str.rvs_n_range pa). destruct (pa <? 10); lia. }
  apply KR; [clear - Hkk HL Hs2r C1; lia|]. apply HWH; [clear - Hkk HL Hs2r C1 Ef Hcver; lia|].
  exists s2, (req_size (Z.max (SlotModel.t_cap_ver inp) 1)). split; [exact Hs2app|].
  clear - Hkk HL Hn2 Ef. lia. }
eapply (G_cs_at g pos mf W10 _ _ _ ly10 S10 _ _ r3 s2 (SlotModel.t_cap_ver inp) (Z.max (SlotModel.t_cap_ver inp) 1)
  (map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa)) 0x1070);
  [exact HPRE | exact HJ10 | exact Hfrs10 | exact Hbl10 | exact Hmfb | exact Hmf32
  | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q11 | exact Q12 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | lia | reflexivity
  | exact Hr3r | clear - Hcver; lia
  | intros Hr0; exact (G_vs_cs_pre W10 _ [(s2, Z.max (SlotModel.t_cap_ver inp) 1)] s2 ma mi pa _
      (Z.max (SlotModel.t_cap_ver inp) 1) (or_introl eq_refl) (proj1 Rpa) ltac:(clear - Hcver; lia) Hn2 Hg3 Hr0)
  | exact MLE10 | exact MOK10 | ].
intros W11 ly11 S11 regs11 mem11 md11 Hwle11 HJ11 HP11 Hfrs11 Hbl11 HGK11 MLE11 MOK11.
clear Q10 Q11 Q12 Q2 Q1 Q3 Q4 Q8 Hg3.
destruct (G_base g pos ly11 S11 W11 mem11 md11 _ _ HPRE HJ11 Hfrs11 Hbl11)
  as (EFA11 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp11 & HSp11).
g_post HS 640%nat regs11 W11 mem11 HP11 HGK11 HFSp11 HSp11 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* ---- run 10: .. free(s) at 0x81780 ---- *)
clear KR.
g_run HS HJ11 EFA11 U9 U19 HPR KP g pos mf W2 mem2 Hmfb HSTKv.
prreg HS (10%bv : bv 5) Q10. prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
g_a0 Q10 regs9. rewrite Hr10b in Q10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (pal_free B TL).
eapply (G_free_at g pos mf W11 _ _ _ ly11 S11 _ [] [] s2 (Z.max (SlotModel.t_cap_ver inp) 1) 0x1078);
  [exact HPRE | exact HJ11 | exact Hfrs11 | exact Hbl11 | exact Hmfb | exact Hmf32
  | exact (proj1 (VRA _ _ KP)) | exact (proj2 (VRA _ _ KP))
  | exact Q10 | exact Q2 | exact Q8 | exact Q3 | exact Q4 | exact Q1 | cbn; tauto | lia | reflexivity
  | clear - Hk; lia | clear - Hnr Hk; unfold EV_LLVMF; lia | exact MLE11 | exact MOK11 | ].
intros W12 ly12 S12 regs12 mem12 md12 Hwle12 HJ12 HP12 Hfrs12 Hbl12 HGK12 MLE12 MOK12.
cbn [app] in Hbl12. clear Q10 Q2 Q1 Q3 Q4 Q8.
destruct (G_base g pos ly12 S12 W12 mem12 md12 _ _ HPRE HJ12 Hfrs12 Hbl12)
  as (EFA12 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSp12 & HSp12).
g_post HS 656%nat regs12 W12 mem12 HP12 HGK12 HFSp12 HSp12 U9 U19 U32 KP g pos mf W2 mem2 Hmfb HSTKv.
(* ---- run 11: 0x81784 .. the call of put_dec at 0x817bc ---- *)
clear KR.
paj_run_to_sh RUNTOP HS HJ12 0x10b0.
{ eapply G_awr; [reflexivity | exact U9 | exact EFA12 | exact U19 | clear - Hmfb HSTKv; lia | clear - Hmfb; lia]. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
cbn [ms_mem mkst] in HF, HFr, HG.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ gwin g pos mf a ->
  aview SEGS (w_H W12) (ms_mem msF) a = aview SEGS (w_H W12) mem12 a)
  by (eapply G_keep_run; [exact HFr | reflexivity | exact U9 | exact U19]).
assert (KPF : forall x, gprot g pos mf x -> ~ gwin g pos mf x ->
  aview SEGS (w_H W12) (ms_mem msF) x = aview SEGS (w_H W2) mem2 x)
  by (intros x Hx Hw; rewrite (KR x (HPR x Hx) Hw); exact (KP x Hx Hw)).
clear KP HF HFr HG.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (26%bv : bv 5) Q26. prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9.
prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (19%bv : bv 5) Q19.
(* x18 = x12 = any_fw / 1000, the multiply-shift at 0x81794 .. 0x817b8 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hh ?msx) =>
  pose proof (st_ok_pi_restrict_reg Hh Ev ssx msx (18%bv : bv 5) HS) as Q18;
  let e := eval vm_compute in (sr_get (ss_regs ssx) (18%bv : bv 5)) in
  change (sr_get (ss_regs ssx) (18%bv : bv 5)) with e in Q18;
  pose proof (st_ok_pi_restrict_reg Hh Ev ssx msx (12%bv : bv 5) HS) as Q12;
  let e := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
  change (sr_get (ss_regs ssx) (12%bv : bv 5)) with e in Q12;
  assert (H37 : bv_unsigned (ew Ev 37) = fwv)
    by (repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite E37; apply unsigned_lit_small; clear - Rfwv; lia);
  destruct (G_den_div Ev fwv H37 Rfwv) as [D1 D2]; clear H37
end.
cbn [ms_regs restrict mkst] in Q12, Q18. unfold G_div_sv in D1, D2. rewrite D1 in Q18. rewrite D2 in Q12. clear D1 D2.
rewrite E32 in Q10, Q20. rewrite (unsigned_lit_small (SFa g pos)) in Q10, Q20 by exact HSFr.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q11. unfold w64 in Q11. rewrite (unsigned_lit_small mf) in Q11 by exact Hmfr.
rewrite E37 in Q21.
rewrite (EE 23%nat 23%bv eq_refl), R23 in Q23. rewrite (EE 24%nat 24%bv eq_refl), R24 in Q24.
rewrite (EE 26%nat 26%bv eq_refl), R26 in Q26.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Q19.
(* the stores of the run: mf+208 := 0 and the shadow of `f` (cell 58) and `ef` (cells 62, 63) := 0 *)
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl) as HR2. cbn [restrict ms_mem] in HR2.
pose proof (field_of_region _ _ 9%nat mf _ _ _ _ _ 208 8%N (SLit 0) 0 HR0 U9
  ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as V208.
assert (SZ : forall o, In (YP09.mkChunk o (CVal 1 (SLit 0)))
    [YP09.mkChunk 63 (CVal 1 (SLit 0)); YP09.mkChunk 62 (CVal 1 (SLit 0)); YP09.mkChunk 58 (CVal 1 (SLit 0))] ->
  aview SEGS (w_H W12) (ms_mem msF) (shadow_addr (SFa g pos) + o) = Some 0).
{ intros o Ho. apply G_aview_val1; [|lia].
  exact (field_of_region _ _ 19%nat _ _ _ _ _ _ o 1%N (SLit 0) 0 HR2 U19 Ho eq_refl ltac:(lia) ltac:(lia)). }
clear HR0 HR2.
(* what the segment kept *)
assert (VMF : forall a (n : nat) v,
  ((mf <= a /\ a + Z.of_nat n <= e_sp0 g) \/ (SFa g pos <= a /\ a + Z.of_nat n <= SFa g pos + 1024)) ->
  (a + Z.of_nat n <= mf + 208 \/ mf + 216 <= a) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W12 (ms_mem msF)) a n v)
  by (intros a n v; exact (VMK W12 (ms_mem msF) a n v KPF)).
assert (KFR : forall x, SFa g pos <= x < SFa g pos + 1024 ->
  aview SEGS (w_H W12) (ms_mem msF) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx. apply KPF; [unfold gprot, fzone; right; left; left; exact Hx|].
  unfold gwin. intros [Hw | Hw]; [clear - Hx Hw Hmf0 HSF1; lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp. unfold shadow_addr, SHADOW_OFF in Hw.
  clear - Hx Hw HSFapp HSF0 HSF1 C1. lia. }
assert (KSH : forall i, 0 <= i < 58 ->
  aview SEGS (w_H W12) (ms_mem msF) (shadow_addr (SFa g pos) + i) = aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos) + i)).
{ intros i Hi. apply KPF; [unfold gprot, fzone; right; left; right; lia|].
  unfold gwin. intros [Hw | Hw]; [clear - Hw Hi Hmf0 Hsh1; lia | lia]. }
assert (ESH : forall o, 0 <= o -> shadow_of_addr SHADOW_OFF (SFa g pos + 8 * o) = shadow_addr (SFa g pos) + o).
{ intros o Ho. unfold shadow_of_addr, shadow_addr.
  pose proof (Z.div_mod (SFa g pos) 64 ltac:(lia)) as D. rewrite HSF64, Z.add_0_r in D. clear - D Ho. lia. }
assert (HINB : bytes_at8 W12 (ms_mem msF) (e_p g) inp).
{ unfold bytes_at8 in *. apply (G_garr8_moved (w_H W2) (w_H W12) mem2 (ms_mem msF)); [|exact Hinb].
  intros kk Hkk. rewrite length_map in Hkk.
  assert (Hn : 0 < e_n g) by (rewrite Hlen; lia).
  pose proof HJ as (HARj & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARj (Hinb2 Hn)) as (_ & Hp4096 & Hpce & Hpapp & _).
  assert (Hrq : e_n g <= req_size (e_n g))
    by (unfold req_size; destruct (e_n g =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
  apply KPF.
  - unfold gprot, inblk. right; right. split; [exact Hn|]. rewrite Hlen. lia.
  - apply HWH; [rewrite <- Hlen in Hkk; clear - Hkk Hp4096 Hpce Hrq; lia|].
    exists (e_p g), (req_size (e_n g)). split; [exact Hpapp|]. rewrite <- Hlen in Hkk. clear - Hkk Hrq. lia. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ12) as [Efd Efs].
(* ---- the boundary inv_G_end at 0x817bc ---- *)
apply SRr_ret.
unfold inv_G_end, acut. pmkst HS.
lazymatch type of MLE12 with mo_le _ _ _ (?kk * _) =>
  replace (4 * Z.of_nat (m_nrec g) + 4) with kk by ring end.
exists ly12, S12, (ms_regs msF), (ms_mem msF). eexists.
split; [reflexivity|].
split; [exact HJ12|].
split; [exact Hfrs12|].
split; [clear - Hnr Hk; unfold EV_LLVMF; lia|].
split; [exact MLE12|].
split; [exact MOK12|].
split.
{ unfold ecommon.
  split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q19|].
  split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V80]|].
  split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V192]|].
  split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V176]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact Vra]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V24]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V32]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V40]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V48]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V56]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V64]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V72]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V80b]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V88]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V96]|].
  split; [apply VMF; [left; clear - Hmfb; lia | right; clear - Hmfb; lia | exact V104]|].
  split; [apply VMF; [left; clear - Hmfb; lia | left; clear - Hmfb; lia | exact Vmf24]|].
  split; [apply VMF; [right; clear; lia | left; clear - Hmf0 HSF1; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
unfold id_at, hblocks, mf_id3, mf_id, sh_zero.
split.
{ split; [|split].
  - unfold bytes_at8. apply (G_garr8_moved (w_H W2) (w_H W12) mem2 (ms_mem msF)); [|exact Hidb].
    intros kk Hkk. rewrite length_map in Hkk. apply KFR.
    assert (Hl : length (m_id g (m_nrec g)) = 38%nat) by exact Hidl. unfold V_id. clear - Hkk Hl. lia.
  - apply (G_zshadow_moved (aview SEGS (w_H W2) mem2)); [|exact Hidz].
    intros i Hi. unfold V_id, N_id in *. change (SFa g pos + 352) with (SFa g pos + 8 * 44). rewrite ESH by lia.
    rewrite <- Z.add_assoc. apply KSH. lia.
  - apply (G_bshadow_moved (aview SEGS (w_H W2) mem2)); [|exact Hidk].
    intros i Hi. unfold V_id, N_id in *. change (SFa g pos + 352) with (SFa g pos + 8 * 44). rewrite ESH by lia.
    rewrite <- Z.add_assoc. apply KSH. lia. }
split; [exact Hbl12|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact Hid3]|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact Hmid]|].
split.
{ intros i Hi. unfold V_f, N_f in *. change (SFa g pos + 464) with (SFa g pos + 8 * 58). rewrite ESH by lia.
  assert (i = 0) as -> by lia. rewrite Z.add_0_r. apply SZ. right; right; left; reflexivity. }
split.
{ intros i Hi. unfold V_ef, N_ef in *. change (SFa g pos + 496) with (SFa g pos + 8 * 62). rewrite ESH by lia.
  rewrite <- Z.add_assoc. assert (i = 0 \/ i = 1) as [-> | ->] by lia.
  - apply SZ. right; left; reflexivity.
  - apply SZ. left; reflexivity. }
split; [unfold M_n1; exact V208|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V136]|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V144]|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V160]|].
split; [apply VMF; [left; clear - Hmfb; lia | left; clear; lia | exact V168]|].
split; [rewrite Q10; reflexivity|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q11; reflexivity|].
split; [rewrite Q13; reflexivity|].
split; [rewrite Q12; reflexivity|].
split; [rewrite Q18; reflexivity|].
split; [rewrite Q21; reflexivity|].
split; [exact Q23|].
split; [exact Q24|].
exact Q26.
Qed.

End c.
End b.
End a.

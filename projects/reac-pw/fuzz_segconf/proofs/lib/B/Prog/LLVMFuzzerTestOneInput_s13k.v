(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of send_message in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, jal at 0x86714, back at 0x86718), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, with its module paths and module names changed; 272 of its 315 lines of code are new or changed and 298 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of segment S03
   of the walk of LLVMFuzzerTestOneInput (the segment lemma is LLVMFuzzerTestOneInput_s13.v):
   the payload's cap and file count ranges, the two symbolic seeds (s13_ss1 at K8507c, s13_ss2 at the return pc
   0x850d8), chunk reads off a symbolic state, the shadow band and image band keep lemmas (sa_addr, lt_img, the saved
   registers, the slots, the frame's shadow bytes), and the reader model of the zeroed m block. Statement-free
   helpers: no cut statement, contract or kit file is restated. *)

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_init_c
  LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaLibF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma s13_cap_range : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.
Lemma s13_dec_files_length : forall k i, length (SegModel.dec_files k i) = k.
Proof.
induction k as [|k IH]; intros i; cbn [SegModel.dec_files]; [reflexivity|].
destruct (SegModel.fuzz_u8 i) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma s13_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s13_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma s13_pw_nodup : forall l : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> Forall (fun b => 0 <= snd b) l -> List.NoDup l.
Proof.
induction l as [|[p n] l IH]; intros Hp Hf; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hh Ht]. apply Forall_cons_iff in Hf as [Hn Hf].
constructor; [|exact (IH Ht Hf)].
intros Hin. rewrite Forall_forall in Hh.
assert (Hm : In (p, req_size n) (map (fun b => (fst b, req_size (snd b))) l))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) l (p, n)); exact Hin).
specialize (Hh _ Hm). cbn [fst snd] in Hn, Hh. pose proof (req_size_pos n Hn) as [R _].
unfold zdisjoint in Hh. cbn [fst snd] in Hh. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s13_Bx : sv := SLit SHADOW_OFF.
Definition s13_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s13_rs1 : smem :=
  [ YP09.mkRegion (Some 9%nat) 16 24 16 24 [];
    YP09.mkRegion (Some 9%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 64 72 64 72 [];
    YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
    YP09.mkRegion (Some 9%nat) 112 128 112 128 [];
    YP09.mkRegion (Some 9%nat) 168 176 168 176 [];
    YP09.mkRegion (Some 9%nat) 216 224 216 224 [] ].
Definition s13_f1 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF 4096 (2 ^ 63) 4); (10%nat, mkAF 4096 (2 ^ 63) 4); (32%nat, mkAF 0 39 0) ] [] [].
Definition s13_ss1 : sstate := mkSS LO_K8507c sr_atoms s13_rs1 None s13_f1.
Definition s13_E (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).

Lemma s13_val8 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (rdW W mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (YI04.chunk_ok_val SEGS E _ base off 8 _ v); [cbn [sv_denot]; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | exact Hv | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hrd).
Qed.

Lemma s13_seed1 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 c m cap,
  getr regs 9 = w64 s1 -> getr regs 21 = w64 c -> getr regs 10 = w64 m ->
  4096 <= c <= 2 ^ 63 -> c mod 16 = 0 -> 4096 <= m <= 2 ^ 63 -> m mod 16 = 0 -> 0 <= cap <= 39 ->
  rdword (rdW W mem) (s1 + 56) = Some cap ->
  (forall a, s1 + 16 <= a < s1 + 224 -> apresent (w_H W) mem a) ->
  2 ^ 46 <= s1 -> s1 + 224 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  st_ok_pi SEGS VAL (s13_E regs cap) s13_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K8507c)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 c m cap R9 R21 R10 Hc Hc16 Hm Hm16 Hcap Hrd Hpres Hs0 Hs1 Hs32.
set (E := s13_E regs cap).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 cap]) n)
  by (intros n Hn; subst E; unfold s13_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E9 : bv_unsigned (ew E 9) = s1) by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E21 : bv_unsigned (ew E 21) = c) by (rewrite (EEo 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (E10 : bv_unsigned (ew E 10) = m) by (rewrite (EEo 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (W1 : forall o, 16 <= o < 224 -> YP09.writable_at SEGS (mrestrict (w_H W) mem) (s1 + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
unfold s13_ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s13_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s13_rs1. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9;
    (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply W1; lia|]);
    repeat apply Forall_cons; try apply Forall_nil.
  apply (s13_val8 W mem E s1 56 32 cap E32 ltac:(lia) Hrd).
- apply pairwise_disjoint_of_extents. unfold s13_rs1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s13_f1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E21, E10, E32, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Definition s13_rs2 : smem :=
  [ YP09.mkRegion (Some 9%nat) 72 88 72 88 [];
    YP09.mkRegion (Some 9%nat) 96 112 96 104 [YP09.mkChunk 104 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 176 184 176 184 [];
    YP09.mkRegion (Some 9%nat) 192 200 192 200 [];
    YP09.mkRegion (Some 9%nat) 208 216 208 216 [] ].
Definition s13_f2 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 (2 ^ 63) 4); (32%nat, mkAF 1 4 0) ] [] [].
Definition s13_ss2 : sstate := mkSS 792 sr_atoms s13_rs2 None s13_f2.

Lemma s13_seed2 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m nf,
  getr regs 9 = w64 s1 -> getr regs 22 = w64 m ->
  4096 <= m <= 2 ^ 63 -> m mod 16 = 0 -> 1 <= nf <= 4 ->
  rdword (rdW W mem) (s1 + 104) = Some nf ->
  (forall a, s1 + 16 <= a < s1 + 224 -> apresent (w_H W) mem a) ->
  2 ^ 46 <= s1 -> s1 + 224 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  st_ok_pi SEGS VAL (s13_E regs nf) s13_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 792)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m nf R9 R22 Hm Hm16 Hnf Hrd Hpres Hs0 Hs1 Hs32.
set (E := s13_E regs nf).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 nf]) n)
  by (intros n Hn; subst E; unfold s13_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E9 : bv_unsigned (ew E 9) = s1) by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E22 : bv_unsigned (ew E 22) = m) by (rewrite (EEo 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 nf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (W1 : forall o, 16 <= o < 224 -> YP09.writable_at SEGS (mrestrict (w_H W) mem) (s1 + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
unfold s13_ss2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s13_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s13_rs2. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9;
    (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply W1; lia|]);
    repeat apply Forall_cons; try apply Forall_nil.
  apply (s13_val8 W mem E s1 104 32 nf E32 ltac:(lia) Hrd).
- apply pairwise_disjoint_of_extents. unfold s13_rs2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s13_f2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E32, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
Lemma s13_rconf_kept : forall (rd rd' : reader) c r0,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c r0 -> sa_rconf rd' c r0.
Proof.
intros rd rd' c r0 K (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. pose proof He as (Hl & _). rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma s13_mconf0 : forall (rd : reader) m, zero_atA rd m seg_spec.SEG_M_SIZE -> sa_mconf rd m SegModel.mconf0.
Proof.
intros rd m HZ. exists (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_M_SIZE)). split; [|exact seg_spec.mconf_enc_zero].
intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat_lt by exact Hi.
rewrite (HZ (Z.of_nat i)) by (unfold seg_spec.SEG_M_SIZE in *; lia). reflexivity.
Qed.

Lemma s13_chunk_rd : forall (W : world SEGS) E ss ms i rg p off e a v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (a + off) = Some v.
Proof.
intros W E ss ms i rg p off e a v HS Hi Hb Hin Ha He Hv.
apply (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact Hv].
pose proof (YI67.st_chunk_val SEGS E ss _ i rg p off 8 e a v HS Hi Hb Hin Ha He ltac:(exact Hv) ltac:(lia)) as H.
cbn [ms_mem restrict] in H. exact H.
Qed.
Lemma s13_denot_off : forall E n k v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n k v Hn Hv Hvk. rewrite denot_lit_U, (U_atom_off E n v k Hn Hv Hvk). reflexivity. Qed.
Lemma s13_denot_add : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 + v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 R1 R2 R12. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 v1 H1 R1), (U_atom E n2 v2 H2 R2). apply zcanon_small. lia.
Qed.
(* the shadow band: every shadow byte of an application address lies in it *)
Definition s13_shz (a : Z) : Prop := kLowMemEnd - 16 <= a < kHighMemBeg.
Lemma s13_sa_addr_kept : forall (rd rd' : reader) q n,
  sa_addr rd q n -> in_app q n -> 0 < n -> (forall a, s13_shz a -> rd' a = rd a) -> sa_addr rd' q n.
Proof.
intros rd rd' q n (H0 & H63 & Hmr & Hra & Hhv) Happ Hn K.
pose proof alloc_ceiling_value as [[AC1 AC2] _].
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ.
split; [exact H0|]. split; [exact H63|]. split; [exact Hmr|]. split.
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite K; [exact Hs|]. unfold s13_shz, shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. lia.
- intros _ s0 Hs. rewrite K; [exact (Hhv Hn s0 Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs. unfold s13_shz, kLowMemEnd, kHighMemBeg. lia.
Qed.


Definition s13_band (a : Z) : Prop := 0x10000 <= a < kImgEnd.
Lemma s13_img_band : forall (B : asyms) q n x, sa_img SEGS B q n -> q <= x < q + n -> s13_band x.
Proof. intros B q n x H Hx. destruct (H x Hx) as (Hi & _ & _). exact (pa_img_range x Hi). Qed.
Lemma s13_rdword_band : forall (rd rd' : reader) a, (forall x, s13_band x -> rd' x = rd x) ->
  (forall k, 0 <= k < 8 -> s13_band (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a K Ha. apply rdword_ext. intros k Hk. apply K, Ha. exact Hk. Qed.
Lemma s13_lit_kept : forall (B : asyms) (W W' : world SEGS) mem mem' a s,
  (forall x, s13_band x -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros B W W' mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrt | exact Himg]]].
split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi. apply (s13_img_band B a (Z.of_nat (length s) + 1)); [exact Himg | lia].
Qed.
Lemma s13_img_kept : forall (B : asyms) cx (W W' : world SEGS) mem mem',
  (forall x, s13_band x -> rdW W' mem' x = rdW W mem x) ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W' mem').
Proof.
intros B cx W W' mem mem' K (HRO & HI & HGI).
split; [|split].
- intros a Hro Hown Herr. rewrite K; [exact (HRO a Hro Hown Herr)|].
  destruct Hro as [(s & Hs & Hw & Ha) | Ha].
  + apply pa_img_range. exists s. split; [exact Hs | exact Ha].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. unfold s13_band, kImgEnd. lia.
- destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  split; [|split; [exact H2|]].
  { intros j Hj. rewrite K; [exact (H1 j Hj)|]. apply (s13_img_band B mod40A 8); [exact H2 | lia]. }
  split.
  { intros s Hs. destruct (H3 s Hs) as [Hl Hap]. split; [exact (s13_lit_kept B W W' mem mem' _ _ K Hl) | exact Hap]. }
  split.
  { intros s Hs. destruct (H4 s Hs) as [Hl Hap]. split; [exact (s13_lit_kept B W W' mem mem' _ _ K Hl) | exact Hap]. }
  split.
  { destruct H5 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
    intros i Hi. destruct (P3 i Hi) as (tp & Htp & Hl). exists tp. split.
    - rewrite (s13_rdword_band (rdW W mem) (rdW W' mem')); [exact Htp | exact K |].
      intros j Hj. apply (s13_img_band B catA pin_spec.CAT_BYTES); [exact P2|].
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hi. lia.
    - exact (s13_lit_kept B W W' mem mem' _ _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
    intros i Hi. destruct (P3 i Hi) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (s13_rdword_band (rdW W mem) (rdW W' mem')); [exact Hwp | exact K |].
      intros j Hj. apply (s13_img_band B wordsA 40); [exact P2 | lia].
    - exact (s13_lit_kept B W W' mem mem' _ _ K Hl). }
  split.
  { destruct H8 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
    intros i Hi j Hj. rewrite K; [exact (P3 i Hi j Hj)|]. apply (s13_img_band B rolesA 20); [exact P2 | lia]. }
  split.
  { destruct H9 as (P1 & g & P2). split.
    - rewrite (s13_rdword_band (rdW W mem) (rdW W' mem')); [exact P1 | exact K |].
      intros j Hj. unfold s13_band, gotwA, kImgEnd. lia.
    - exists g. rewrite (s13_rdword_band (rdW W mem) (rdW W' mem')); [exact P2 | exact K |].
      intros j Hj. unfold s13_band, guardA, kImgEnd. lia. }
  repeat (split; [assumption|]). assumption.
- intros i Hi. rewrite K; [exact (HGI i Hi)|].
  destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _).
  apply (s13_img_band B longlA LONGL_N); [exact H12 | unfold LONGL_W, LONGL_N; lia].
Qed.

Lemma s13_saved_kept : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
rewrite (rdword_ext rd rd'); [exact (HS i r Hi)|].
intros j Hj. apply Hk. lia.
Qed.
Lemma s13_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall j, 0 <= j < 8 -> rd' (x_s1 cx + o + j) = rd (x_s1 cx + o + j)) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L Hk HS o v Hin. rewrite (rdword_ext rd rd'); [exact (HS o v Hin)|].
intros j Hj. exact (Hk o v Hin j Hj).
Qed.
Lemma s13_slots_app : forall cx rd L1 L2, lt_slots cx rd L1 -> lt_slots cx rd L2 -> lt_slots cx rd (L1 ++ L2).
Proof. intros cx rd L1 L2 H1 H2 o v Hin. apply in_app_or in Hin as [H|H]; [exact (H1 o v H) | exact (H2 o v H)]. Qed.
Lemma s13_zs_kept : forall (rd rd' : reader) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l Hk H i Hi. rewrite Hk by lia. exact (H i Hi). Qed.

Lemma s13_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

End f.
End d.

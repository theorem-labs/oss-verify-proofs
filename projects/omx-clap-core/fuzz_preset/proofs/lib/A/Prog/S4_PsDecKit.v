(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsRet.v, with its module names changed; 738 of its 816 lines of code are new or changed and 587 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string's decode stretch): the WALK KIT of S4_PsDec.v. The symbolic states the
   stretch runs from (one per cut: the decode loop head PS_DEC, the hex loop head PS_HEX, the \u tail, the returns of
   hex4 and put_utf8) built from concrete facts, and the facts a run's leaf hands back.
   FILE SET: as the kit's cut 7cdbb61b5fa0 carries it (YCbqG blob 219748197d6b); WalkS4's set of record was base
   83f3e37ac7e, a working branch 63997a07aa6, the kit walkkit b7722372682, listing 7c8ffeba5035.
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; base 44a91d58bb5, S4_PsBase.v
   a59ce5bfcbe3): Section d takes an invariant P of the memory (Variable P right after SK). The cut lemmas (dec_facts,
   dec_entry, dec_keep, retok_close, dec_close1, free_close, dec_tmp_w) are over ps_at_decP .. P; the keep lemmas take
   P mem' right after the journal premise (the run's own HPM, YSRrMemnorm's runner twin at P), never derived from where
   the run wrote. The four kit cuts / statements have P forms ps_at_freeP / ps_seg_freeP / ps_dec_afterP / ps_seg_uP;
   the stable four (ps_at_free / ps_seg_free / ps_dec_after / ps_seg_u) are kit blob 28acfaf8b683's but for the cursor
   set (CW for DW), and ps_seg_free_of_True / ps_seg_u_of_True (Section t) are the P := (fun _ => True) instances, both
   ways. Built at the cut's image A' listing (Listing_prog.v 7ed1529926bd, PAImg_prog.v 505a51ff7d08).
   THE SYMBOLIC LAYOUT, at every cut (atoms are the engine's numbering, DERIVED: 0..31 the registers at the cut, 32..43
   the twelve text bytes from the read cursor r; the shadow base is register s8's atom 24):
     rk  = sp + [8, 32)   read-only: the three surrogate constants the prologue block stores (offsets 8, 16, 24)
     rin = q + 8 + [0, 8) read-only: in->end (= text + len, the cut's a1, atom 11)
     rt i = r + i         read-only: text byte i (atom 32 + i), added to a state once the code has checked r + i < end
     ro  = w + [0, 1)     WRITABLE: the out byte the loop stores, in the block fuzz_malloc made
   Numerals: 8 / 16 / 24 / 32 / 36 / 40 (DERIVED frame offsets of parse_string, 144 its frame LENGTH), 2 ^ 46 / 2 ^ 47 /
   2 ^ 44 (DERIVED stack and shadow bounds), 255 (WORD), the constants 34 92 32 101 91 47 98 8 113 102 12 110 10 114 116
   55296 56320 -56613888 (WORD: the values the block at offsets 228-324 loads); no ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ S4_PsBase S4_PsDecModel S4_PsSrc.
(* the re-hiding move's SRr' / SRrG / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic layout (no state) ---- *)
Definition PSO : Z := PS_OFF.
Definition dBx : sv := SOff 24 0.
Definition dBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 24 0).
Definition rg_k : YP09.region := YP09.mkRegion (Some 2%nat) 8 32 0 0
  [YP09.mkChunk 8 (CVal 8 (SLit (2 ^ 64 - 56613888))); YP09.mkChunk 16 (CVal 8 (SLit 56320));
   YP09.mkChunk 24 (CVal 8 (SLit 55296))].
Definition rg_in : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))].
Definition rg_t (i : nat) : YP09.region :=
  YP09.mkRegion (Some 20%nat) (Z.of_nat i) (Z.of_nat i + 1) 0 0 [YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (32 + i) 0))].
Definition rg_o : YP09.region := YP09.mkRegion (Some 19%nat) 0 1 0 1 [].
(* register pins over the register atoms *)
Fixpoint pins (l : list (bv 5 * sv)) (s : list sv) : list sv :=
  match l with [] => s | (r, e) :: l' => pins l' (sr_set s r e) end.
(* the constants every cut of the loop keeps (s10 s11 a6 a7 t0..t6 ra; s9 the shadow cell of q + 8) *)
Definition pins_keep : list (bv 5 * sv) :=
  [(25%bv, shx 9); (26%bv, SLit 34); (16%bv, SLit 92); (17%bv, SLit 91); (5%bv, SLit 47); (6%bv, SLit 98);
   (7%bv, SLit 8); (28%bv, SLit 113); (29%bv, SLit 102); (30%bv, SLit 12); (31%bv, SLit 110); (27%bv, SLit 10);
   (1%bv, SLit 116)].
(* and the three the hex loop and put_utf8 clobber: a4 a5 s5 *)
Definition pins_dec : list (bv 5 * sv) := pins_keep ++ [(14%bv, SLit 32); (15%bv, SLit 101); (21%bv, SLit 114)].
Definition f_base : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (20%nat, mkAF 0 (2 ^ 47 - 64) 0);
   (19%nat, mkAF 4096 (2 ^ 47 - 64) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition f_bytes : list (nat * afact) := map (fun i => ((32 + i)%nat, mkAF 0 255 0)) (seq 0 12).
Definition SH_o : list shent := [mkSHE 19 0 1].
Definition ss_dec : sstate :=
  mkSS (PSO + PS_DEC) (pins pins_dec sr_atoms) [rg_k; rg_in; rg_t 0; rg_o] None (mkFacts (f_base ++ f_bytes) [] []).

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the twelve text bytes from r, the extra atoms 32..43 *)
Definition tx12 (tb : list Z) (text r : Z) : list Z := map (fun i => nth (Z.to_nat (r + Z.of_nat i - text)) tb 0) (seq 0 12).
Definition EK (regs : bvmap 5 word) (tb : list Z) (text r : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) (tx12 tb text r))).

Lemma EK_reg : forall regs tb text r n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (EK regs tb text r) n = getr regs x.
Proof.
  intros regs tb text r n x Hn. unfold EK. rewrite Eimg_low by (pose proof (u5_range x); unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn.
Qed.
Lemma EK_byte : forall regs tb text r i, (i < 12)%nat ->
  ew (EK regs tb text r) (32 + i) = Z_to_bv 64 (nth (Z.to_nat (r + Z.of_nat i - text)) tb 0).
Proof.
  intros regs tb text r i Hi. unfold EK. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. unfold tx12. rewrite map_map.
  set (f := fun x : nat => Z_to_bv 64 (nth (Z.to_nat (r + Z.of_nat x - text)) tb 0)).
  rewrite (nth_indep (map f (seq 0 12)) (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. subst f. reflexivity.
Qed.

(* ---- registers ---- *)
Lemma regs_ok_pin : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e H He r'. destruct (bv_eqb r 0) eqn:Hr0.
  - unfold sr_set. rewrite Hr0. apply H.
  - destruct (decide (r' = r)) as [->|Hne].
    + rewrite sr_get_set_same by exact Hr0. exact He.
    + rewrite sr_get_set_other by exact Hne. apply H.
Qed.
Lemma regs_ok_pins : forall E l s regs,
  regs_ok E s regs -> Forall (fun p => getr regs (fst p) = sv_denot E (snd p)) l -> regs_ok E (pins l s) regs.
Proof.
  intros E l. induction l as [|[r e] l IH]; intros s regs H Hl; cbn [pins]; [exact H|].
  apply Forall_cons_iff in Hl as [He Hl]. apply IH; [|exact Hl]. apply regs_ok_pin; [exact H | exact He].
Qed.
Lemma sv_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof. intros E z Hz. reflexivity. Qed.
Lemma sv_shx : forall E n a, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> ew E 24 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (shx n) = w64 (SHADOW_OFF + a / 8).
Proof.
  intros E n a Hn Ha Hb. rewrite denot_lit_U. unfold w64. f_equal. unfold shx.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hn, Hb, !Z.add_0_r.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold SHADOW_OFF, M64; lia).
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite Z.add_comm. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
Qed.

(* ---- regions from concrete bytes ---- *)
Lemma val_mem_mod64 : forall m a v, val_mem segs m a 8 v -> val_mem segs m a 8 (v mod 2 ^ 64).
Proof.
  intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
  replace ((v mod 2 ^ 64) mod 2 ^ (8 * Z.of_nat 8)) with (v mod 2 ^ (8 * Z.of_nat 8)); [reflexivity|].
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rok_k : forall E m sp, ew E 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 32 <= 2 ^ 64 ->
  val_mem segs m (sp + 8) 8 (-56613888) -> val_mem segs m (sp + 16) 8 56320 -> val_mem segs m (sp + 24) 8 55296 ->
  region_ok segs E m rg_k.
Proof.
  intros E m sp H2 Hs Hs2 V8 V16 V24. unfold region_ok, rg_k.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H2, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val segs E m sp 8 8 (SLit (2 ^ 64 - 56613888)) (2 ^ 64 - 56613888)); [reflexivity | cbn; lia | cbn; lia |].
    replace (2 ^ 64 - 56613888) with ((-56613888) mod 2 ^ 64) by reflexivity. apply val_mem_mod64. exact V8.
  - apply (chunk_ok_val segs E m sp 16 8 (SLit 56320) 56320); [reflexivity | cbn; lia | cbn; lia | exact V16].
  - apply (chunk_ok_val segs E m sp 24 8 (SLit 55296) 55296); [reflexivity | cbn; lia | cbn; lia | exact V24].
Qed.
Lemma rok_in : forall E m a en, ew E 9 = Z_to_bv 64 a -> ew E 11 = Z_to_bv 64 en -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  0 <= en < 2 ^ 64 -> val_mem segs m a 8 en -> region_ok segs E m rg_in.
Proof.
  intros E m a en H9 H11 Ha Ha2 Hen V. unfold region_ok, rg_in.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E m a 0 8 (SOff 11 0) en); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V].
  apply bv_eq. rewrite denot_SOff, H11, Z.add_0_r. rewrite !unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma rok_t : forall E m r i b, ew E 20 = Z_to_bv 64 r -> ew E (32 + i) = Z_to_bv 64 b -> 0 <= r ->
  r + Z.of_nat i + 1 <= 2 ^ 64 -> 0 <= b < 256 -> val_mem segs m (r + Z.of_nat i) 1 b -> region_ok segs E m (rg_t i).
Proof.
  intros E m r i b H20 Hb Hr Hr2 Hb0 V. unfold region_ok, rg_t.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H20, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E m r (Z.of_nat i) 1 (SOff (32 + i) 0) b); [| cbn; lia | cbn; lia | exact V].
  apply bv_eq. rewrite denot_SOff, Hb, Z.add_0_r. rewrite !unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma rok_o : forall E m w, ew E 19 = Z_to_bv 64 w -> 0 <= w -> w + 1 <= 2 ^ 64 -> writable_at segs m w ->
  region_ok segs E m rg_o.
Proof.
  intros E m w H19 Hw Hw2 Wr. unfold region_ok, rg_o.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H19, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (w + o) with w by lia. exact Wr.
Qed.

(* ---- a state at a cut: pinned registers, regions, facts ---- *)
Lemma build_st_ok : forall E pc l rs G regs mem,
  regs_ok E sr_atoms regs -> Forall (fun p => getr regs (fst p) = sv_denot E (snd p)) l ->
  regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
  st_ok_pi segs VAL E (mkSS pc (pins l sr_atoms) rs None G) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)).
Proof.
  intros E pc l rs G regs mem Hr Hl Hwf Hrs Hpd HG. apply pa_entry_st_ok_full; [|exact Hwf|exact Hrs|exact Hpd|exact HG].
  apply regs_ok_pins; [exact Hr | exact Hl].
Qed.
Lemma regs_ok_EK : forall regs tb text r, regs_ok (EK regs tb text r) sr_atoms regs.
Proof. intros. unfold EK. apply regs_ok_Eimg_Ereg. Qed.
Lemma afact_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> afact_ok E n (mkAF 0 255 0).
Proof.
  intros E n v H Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma afact_rng : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> lo <= v <= hi -> 0 <= v < 2 ^ 64 ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hv Hv2 Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia. lia. Qed.
Lemma tx12_byte : forall tb text r i, (i < 12)%nat -> (forall j, (j < length tb)%nat -> 0 <= nth j tb 0 < 256) ->
  0 <= nth (Z.to_nat (r + Z.of_nat i - text)) tb 0 < 256.
Proof.
  intros tb text r i Hi Hb. destruct (Nat.lt_ge_cases (Z.to_nat (r + Z.of_nat i - text)) (length tb)) as [Hl|Hl].
  - apply Hb. exact Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.
Lemma garr8_at : forall m text tb x, garr8 segs m text tb -> text <= x < text + Z.of_nat (length tb) ->
  val_mem segs m x 1 (nth (Z.to_nat (x - text)) tb 0) /\ 0 <= nth (Z.to_nat (x - text)) tb 0 < 256.
Proof.
  intros m text tb x H Hx. destruct (H (Z.to_nat (x - text)) ltac:(lia)) as [V R].
  replace (text + Z.of_nat (Z.to_nat (x - text))) with x in V by lia. auto.
Qed.
Lemma garr8_bytes : forall m text tb, garr8 segs m text tb -> forall j, (j < length tb)%nat -> 0 <= nth j tb 0 < 256.
Proof. intros m text tb H j Hj. exact (proj2 (H j Hj)). Qed.
Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2|]. destruct H1 as [Ha Hb]. split; [exact Ha | exact (IH Hb)]. Qed.
Lemma atoms_ok_bytes : forall regs tb text r, (forall j, (j < length tb)%nat -> 0 <= nth j tb 0 < 256) ->
  atoms_ok (EK regs tb text r) f_bytes.
Proof.
  intros regs tb text r Hb. unfold f_bytes.
  assert (H : forall l, (forall i, In i l -> (i < 12)%nat) -> atoms_ok (EK regs tb text r) (map (fun i => ((32 + i)%nat, mkAF 0 255 0)) l)).
  { intros l. induction l as [|i l IH]; intros Hl; cbn [map atoms_ok]; [exact I|]. split.
    - apply (afact_byte _ _ (nth (Z.to_nat (r + Z.of_nat i - text)) tb 0)); [apply EK_byte; apply Hl; left; reflexivity|].
      apply tx12_byte; [apply Hl; left; reflexivity | exact Hb].
    - apply IH. intros j Hj. apply Hl. right. exact Hj. }
  apply H. intros i Hi. apply in_seq in Hi. lia.
Qed.

(* ---- THE STATE AT PS_DEC, from concrete facts ---- *)
Lemma dec_build : forall (W : world segs) regs mem tb text r w q sp en,
  getr regs 2 = w64 sp -> getr regs 9 = w64 (q + 8) -> getr regs 11 = w64 en -> getr regs 19 = w64 w ->
  getr regs 20 = w64 r -> getr regs 24 = w64 SHADOW_OFF -> getr regs 25 = w64 (SHADOW_OFF + (q + 8) / 8) ->
  getr regs 26 = w64 34 -> getr regs 14 = w64 32 -> getr regs 16 = w64 92 -> getr regs 15 = w64 101 ->
  getr regs 17 = w64 91 -> getr regs 5 = w64 47 -> getr regs 6 = w64 98 -> getr regs 7 = w64 8 ->
  getr regs 28 = w64 113 -> getr regs 29 = w64 102 -> getr regs 30 = w64 12 -> getr regs 31 = w64 110 ->
  getr regs 27 = w64 10 -> getr regs 21 = w64 114 -> getr regs 1 = w64 116 ->
  alloc_ceiling <= sp -> sp + 144 <= q -> q + 24 <= 2 ^ 47 -> sp mod 16 = 0 -> q mod 8 = 0 ->
  0 <= text -> text <= r < text + Z.of_nat (length tb) -> text + Z.of_nat (length tb) <= alloc_ceiling ->
  4096 <= w < alloc_ceiling -> (r + 1 <= w \/ w + 1 <= r) -> 0 <= en < 2 ^ 64 ->
  val_mem segs (rdW W mem) (sp + 8) 8 (-56613888) -> val_mem segs (rdW W mem) (sp + 16) 8 56320 ->
  val_mem segs (rdW W mem) (sp + 24) 8 55296 -> val_mem segs (rdW W mem) (q + 8) 8 en ->
  garr8 segs (rdW W mem) text tb -> writable_at segs (rdW W mem) w ->
  st_ok_pi segs VAL (EK regs tb text r) ss_dec (mkst regs (Z_to_bv 64 (BASE + (PSO + PS_DEC))) (rdW W mem) (seg_rom segs)).
Proof.
  intros W regs mem tb text r w q sp en R2 R9 R11 R19 R20 R24 R25 R26 R14 R16 R15 R17 R5 R6 R7 R28 R29 R30 R31 R27 R21 R1
    Hsp Hq Hq2 Hsp16 Hq8 Ht Hr Htc Hw Hrw Hen V8 V16 V24 Vq Hg Hwr.
  pose proof asan_consts as (C1 & _).
  set (E := EK regs tb text r).
  assert (E2 : ew E 2 = Z_to_bv 64 sp) by (subst E; rewrite (EK_reg regs tb text r 2 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (q + 8)) by (subst E; rewrite (EK_reg regs tb text r 9 9%bv eq_refl); exact R9).
  assert (E11 : ew E 11 = Z_to_bv 64 en) by (subst E; rewrite (EK_reg regs tb text r 11 11%bv eq_refl); exact R11).
  assert (E19 : ew E 19 = Z_to_bv 64 w) by (subst E; rewrite (EK_reg regs tb text r 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 r) by (subst E; rewrite (EK_reg regs tb text r 20 20%bv eq_refl); exact R20).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (EK_reg regs tb text r 24 24%bv eq_refl); exact R24).
  destruct (garr8_at _ text tb r Hg ltac:(lia)) as [Vr Br].
  assert (E32 : ew E (32 + 0) = Z_to_bv 64 (nth (Z.to_nat (r - text)) tb 0)) by (subst E; rewrite EK_byte by lia; do 3 f_equal; lia).
  apply build_st_ok.
  - apply regs_ok_EK.
  - unfold pins_dec, pins_keep. cbn [app].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| | | | | | | | | | | | | | | | apply Forall_nil].
    all: first [ rewrite R25; symmetry; apply sv_shx; [exact E9 | lia | exact E24]
               | rewrite R26; reflexivity | rewrite R16; reflexivity | rewrite R17; reflexivity | rewrite R5; reflexivity
               | rewrite R6; reflexivity | rewrite R7; reflexivity | rewrite R28; reflexivity | rewrite R29; reflexivity
               | rewrite R30; reflexivity | rewrite R31; reflexivity | rewrite R27; reflexivity | rewrite R1; reflexivity
               | rewrite R14; reflexivity | rewrite R15; reflexivity | rewrite R21; reflexivity ].
  - vm_compute. reflexivity.
  - apply Forall_cons; [apply (rok_k E _ sp E2); [lia | lia | exact V8 | exact V16 | exact V24]|].
    apply Forall_cons; [apply (rok_in E _ (q + 8) en E9 E11); [lia | lia | exact Hen | exact Vq]|].
    apply Forall_cons; [apply (rok_t E _ r 0 _ E20 E32); [lia | lia | exact Br | cbn [Z.of_nat]; rewrite Z.add_0_r; exact Vr]|].
    apply Forall_cons; [apply (rok_o E _ w E19); [lia | lia | exact Hwr]|]. apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, rg_k, rg_in, rg_t, rg_o.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E19, E20, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    apply atoms_ok_app; [|apply atoms_ok_bytes; exact (garr8_bytes _ _ _ Hg)].
    cbn [f_base atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
    + apply (afact_rng E 2 sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
    + apply (afact_rng E 9 (q + 8)); [exact E9 | lia | lia | | lia]. change (2 ^ 3) with 8. rewrite Z.add_mod, Hq8 by lia. reflexivity.
    + apply (afact_rng E 20 r); [exact E20 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    + apply (afact_rng E 19 w); [exact E19 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    + apply (afact_rng E 24 SHADOW_OFF); [exact E24 | lia | unfold SHADOW_OFF; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
Qed.
End k.

(* ---- the stretch's concrete facts, from the contract's cut predicates ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the invariant every cut carries (ps_carryP's last conjunct) and every run keeps (S4_PsBase.v Section gp) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* The kit's head width (PRH_Base.v prh_head_wide, the cut's blob ef7c8ca98529): discharged at the preset instance
   by a Theorem Labs lane's preset_head_wide (CfParamsPreset.v:103) *)
Hypothesis HW : prh_head_wide.

Lemma ps_head8 : 8 <= cf_head.
Proof. exact HW. Qed.
Lemma ps_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

(* the text and the new block are apart: the text lives in a Lam block, the image, or a block whose base is not a
   hidden head, while the new block is a hidden head's block not in Lam *)
Lemma ps_txt_out : forall D ly S Hp W mem md out Q a,
  ARx ly S Hp W mem md -> prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) ->
  ps_alloc B D ly S Hp W mem out Q ->
  pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a.
Proof.
  intros D ly S Hp W mem md out Q a HAR HHOME HAL Ha.
  destruct HAL as (Hcnt & Hout & Hout16 & EHp & Eab & HLED & Hvis & Hroom & Hbb).
  pose proof cf_head_nonneg as Hh0.
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  assert (Ro : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head) by (apply ps_req; lia).
  destruct (Z_lt_le_dec a (out - cf_head)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_le_dec a (out + Z.of_nat Q + 1)) as [Hr|Hr]; [|right; exact Hr]. exfalso.
  destruct HHOME as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)].
  - pose proof HLED as HND; apply ps_led_nodup in HND. pose proof HLED as HF; apply ps_led_blocks in HF.
    pose proof (proj1 (Forall_forall _ _) HF (b, m) (or_intror Hin)) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
    assert (Hne : (b - cf_head, m + cf_head) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
    { intros E. injection E as E1 _. cbn [map fst] in HND. inversion HND as [|x l HN HND2]; subst. apply HN.
      assert (Hi : In out (map fst (pi_Lam D))) by (apply in_map_iff; exists (b, m); split; [cbn [fst]; lia | exact Hin]).
      first [ apply list_elem_of_In; exact Hi | apply elem_of_list_In; exact Hi ]. }
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin_o Hne) as Hd.
    pose proof (req_size_pos (m + cf_head) (Z.add_nonneg_nonneg _ _ Hm0 Hh0)) as [_ Rm].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Ro in Hd. lia.
  - destruct (Hro a Ha) as (Hr0 & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HAR Hin_o); [rewrite Ro; lia|].
    destruct Hr0 as [(sg & Hs & _ & Hsr) | Hrr]; [exists sg; split; [exact Hs | exact Hsr] | exact (@pa_relro_img _ _ PS_PAImg a Hrr)].
  - destruct (Hro a Ha) as (Hr0 & _ & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HAR Hin_o); [rewrite Ro; lia|].
    destruct Hr0 as [(sg & Hs & _ & Hsr) | Hrr]; [exists sg; split; [exact Hs | exact Hsr] | exact (@pa_relro_img _ _ PS_PAImg a Hrr)].
  - assert (Hne : (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
    { intros E. injection E as E1 _. apply Hnh. rewrite EHp, E1. left. reflexivity. }
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hin_o Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Ro in Hd.
    assert (Rm : req_size m = m) by (apply ps_req; lia). rewrite Rm in Hd. lia.
Qed.

Lemma ps_frame144 : PS_FRAME = 144.
Proof. vm_compute. reflexivity. Qed.
Lemma ps_stk144 : 144 <= STK_parse_string.
Proof. unfold Z.le. vm_compute. discriminate. Qed.
Lemma ps_scan_some_len : forall tb text r k, text <= r -> PjGrammar.scan (rest_atR tb text r) = Some k ->
  r < text + Z.of_nat (length tb).
Proof.
  intros tb text r k Hr H. destruct (Z_lt_le_dec r (text + Z.of_nat (length tb))) as [Hl|Hl]; [exact Hl|].
  exfalso. unfold rest_atR in H. rewrite skipn_all2 in H by lia. discriminate.
Qed.

(* the numbers the stretch's states rest on, at PS_DEC *)
Lemma dec_facts : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  PS_SP D = spZ (pi_regs D) - 144 /\ alloc_ceiling <= PS_SP D /\ PS_SP D mod 16 = 0 /\
  PS_SP D + 160 <= pi_q D /\ pi_q D + 24 <= 2 ^ 47 /\ pi_q D mod 8 = 0 /\
  0 < pi_text D /\ pi_text D <= pi_p D /\ pi_p D + 1 <= r < pi_text D + pi_len D /\
  pi_text D + pi_len D <= alloc_ceiling /\ Z.of_nat (length (pi_tb D)) = pi_len D /\
  4096 + cf_head <= out /\ out <= w <= out + Z.of_nat Q /\ out + Z.of_nat Q + 1 <= alloc_ceiling /\
  (forall a, pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a) /\
  ARx ly S Hp W mem md.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  pose proof cf_head_nonneg as Hh0. pose proof ps_head8 as Hh8. pose proof ps_stk144 as Hstk144.
  destruct HPRE as (HF & HUNIV & HCH & HCLOW & HCW & HGAP & HROOM & HWRC & H10 & HIN0 & Hpl & Hnth & HWIN & Hq1 & Hq2 & HRA0 & _).
  destruct HF as ((HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & Hrod & H64).
  destruct Hstk as (Hal & Hs0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct HWIN as (He0 & He16 & Hetop & Hepres).
  destruct HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & _) & HAL & HSH & HGT & HCST & HIN & HROD & HSC & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  pose proof (ajx_ar HJ) as HAR. cbv beta in HAR.
  destruct HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Htp' & Hlen & Hg & Hqt & Hd).
  destruct HSRC as (Hb & H4096 & Hsc & Hamr & Hra' & Hhu).
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr & Hwo & Hw & Hsync).
  pose proof (ps_scan_some_len (pi_tb D) (pi_text D) r _ ltac:(lia) Hsync) as Hrlt.
  assert (Hap : forall a, pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a)
    by (intros a Ha; exact (ps_txt_out D ly S Hp W mem md out Q a HAR HHOME HAL Ha)).
  destruct HAL as (Hcnt & Hout & Hout16 & EHp & Eab & HLED & Hvis & Hroom & Hbb).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & _).
  rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco by lia.
  unfold PS_SP. rewrite ps_frame144.
  split; [reflexivity|]. split; [lia|]. split; [rewrite Zminus_mod, Hal; reflexivity|].
  split; [lia|]. split; [lia|]. split; [exact Hq8|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite <- Hlen; lia|]. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hap|].
  exact HAR.
Qed.

(* THE ENTRY OF THE LOOP BODY: the symbolic state at PS_DEC and its shadow entry, from the contract's ps_at_decP *)
Lemma dec_entry : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  st_ok_pi segs VAL (EK regs (pi_tb D) (pi_text D) r) ss_dec
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + PS_DEC))) mem (seg_rom segs))) /\
  sh_ok segs dBx SH_o (EK regs (pi_tb D) (pi_text D) r) (mrestrict (w_H W) mem).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  destruct (dec_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  destruct HDEC as (_ & HAL & (S24 & S23 & S25) & HGT & HCST & HIN & HROD & HSC & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  destruct HCST as (C26 & C14 & C16 & C15 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C27 & C21 & C1 & V24 & V16 & V8).
  destruct HIN as (Vp & Ve & Vd & Hrw & _ & _ & Ht62 & _ & _ & Hg & Hqt & Hd).
  destruct HAL as (Hcnt & Hout' & Hout16 & EHp & Eab & HLED & (Hvra & Hvhu) & Hroom & Hbb).
  pose proof cf_head_nonneg as Hh0.
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & Hpres & _).
  rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ, Hpres by lia.
  assert (Hwr : writable_at segs (rdW W mem) w) by (apply apresent_writable; apply (proj1 (Hpres w ltac:(lia)))).
  pose proof asan_consts as (CC1 & _).
  split.
  - rewrite restrict_mkst_fx.
    apply (dec_build W regs mem (pi_tb D) (pi_text D) r w (pi_q D) (PS_SP D) (pi_text D + pi_len D));
      try assumption; try lia.
    + destruct (Hap r ltac:(lia)); lia.
  - unfold sh_ok, SH_o. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem _ dBx 19 out (Z.of_nat Q + 1) w 0 1 Hvra).
    + unfold dBx. rewrite U_SOff, (EK_reg regs _ _ r 24 24%bv eq_refl), S24, Z.add_0_r.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    + rewrite U_SOff, (EK_reg regs _ _ r 19 19%bv eq_refl), R19, Z.add_0_r.
      unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* ---- what a stretch that writes at most the out byte w keeps ---- *)
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).

Lemma val_mem_keep : forall (W W' : world segs) m m' a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs (w_H W') m' (a + i) = aview segs (w_H W) m (a + i)) ->
  val_mem segs (rdW W m) a n v -> val_mem segs (rdW W' m') a n v.
Proof.
  intros W W' m m' a n v HA H k Hk. rewrite (mbyte_of_aview segs (w_H W) (w_H W') m m'); [exact (H k Hk)|].
  apply HA. lia.
Qed.
Lemma hull_keep : forall (rd rd' : reader) x n, shadow_hull_vis rd x n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n H HA s Hs. rewrite (HA s Hs). exact (H s Hs). Qed.
Lemma ledger_keep : forall ly S Hp (W : world segs) mem mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview segs (w_H W) mem' (a - cf_head + i) = aview segs (w_H W) mem (a - cf_head + i)) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
  intros ly S Hp W mem mem' Lam peak cnt fail ran most own HLD HS HH.
  (* through the base's named ledger helpers only (Batch 2 reshapes prh_glob) *)
  pose proof HLD as HG; apply ps_led_glob in HG. pose proof HLD as HND; apply ps_led_nodup in HND.
  pose proof HLD as HF; apply ps_led_blocks in HF. pose proof HLD as HP; apply ps_led_heads in HP.
  apply ps_led_mk; [| exact HND | | exact HP].
  - exact (ps_glob_keep W mem mem' _ _ _ _ _ _ _ HS HG).
  - apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (H0 & H1 & H2 & H3 & H4).
    cbn [fst snd] in *. split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    apply (val_mem_keep W W mem mem'); [intros i Hi; apply (HH a k i Hin); lia | exact H4].
Qed.

(* the new block was not a block of the entry (FuzzStrdup.v's sd_newblk over ARx) *)
Lemma ps_newblk : forall ly S ly0 S0 Hp W mem md (x : Z * Z), ARx ly S Hp W mem md -> 0 <= snd x ->
  ablocks B ly S = ablocks B ly0 S0 ++ [x] -> ~ In x (ablocks B ly0 S0).
Proof.
  intros ly S ly0 S0 Hp W mem md [p n] HAR Hn E Hin. cbn [snd] in Hn.
  assert (Hin' : In (p, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md p n HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
  rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
  pose proof (pairwise_In2 zdisjoint _ (p, req_size n) (p, req_size n)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
    ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj. pose proof (req_size_pos n Hn). lia.
Qed.

(* THE KEEP STEP of a stretch that writes at most the out byte w (a run's frame_of over the layout's one writable
   window): every memory fact of ps_at_decP holds at the new memory, with the new journal. The invariant at the new
   memory is the run's own (its HPM, YSRrMemnorm's runner twin at P), never derived from where it wrote. *)
Lemma dec_keep : forall CTX CW D ly S Hp W regs mem md out w r Q mem' md' k',
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  (exists k, ps_carryP B ARx SK P D ly S Hp W mem' md' k []) /\ ps_alloc B D ly S Hp W mem' out Q /\
  val_mem segs (rdW W mem') (PS_SP D + 24) 8 55296 /\ val_mem segs (rdW W mem') (PS_SP D + 16) 8 56320 /\
  val_mem segs (rdW W mem') (PS_SP D + 8) 8 (-56613888) /\
  pj_in_okR segs (rdW W mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs (@pa_relro_lo _ A_prog_listing PS_PAImg) (@pa_relro_hi _ A_prog_listing PS_PAImg) B (aview segs (w_H W) mem') /\
  (forall a, 0 <= a < 2 ^ 64 -> a <> w -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG.
  destruct (dec_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof HPRE as ((HPX & _ & _) & _).
  pose proof (proj1 HPX) as HAR0. cbv beta in HAR0.
  pose proof HPX as (_ & _ & _ & _ & _ & (Hal0 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _) & _).
  destruct HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & _) & HAL & HSH & HGT & HCST & HIN & HROD & _).
  pose proof (ajx_ly HJ) as Hly.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof cf_head_nonneg as Hh0. pose proof ps_head8 as Hh8. pose proof ps_stk144 as Hs144.
  pose proof asan_consts as (C1 & _).
  pose proof HAL as (Hcnt & Hout' & Hout16 & EHp & Eab & HLED & (Hvra & Hvhu) & Hroom & Hbb).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & Hpres & _).
  rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ, Hpres by lia.
  assert (Hwimg : ~ in_img segs w) by (apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HAR Hin_o); rewrite ps_req by lia; lia).
  assert (HA : forall a, 0 <= a < 2 ^ 64 -> a <> w -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
  { intros a Ha Hne. apply aview_eq_of. apply HM. rewrite unsigned_lit_small by lia. exact Hne. }
  (* every shadow byte (and hull byte) of an address below 2 ^ 47 is not w *)
  assert (Hsh : forall s, SHADOW_OFF - 8 <= s < kHighMemBeg -> s <> w).
  { intros s Hs E. subst s. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  assert (Hsa : forall x, 0 <= x < 2 ^ 47 -> aview segs (w_H W) mem' (shadow_addr x) = aview segs (w_H W) mem (shadow_addr x)).
  { intros x Hx. apply HA; [unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos x 8); assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia|].
    apply Hsh. unfold shadow_addr, kHighMemBeg, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hhul : forall x n s, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
    shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> aview segs (w_H W) mem' s = aview segs (w_H W) mem s).
  { intros x n s Hx Hxn Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert ((x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
    apply HA; [lia|]. apply Hsh. unfold kHighMemBeg, SHADOW_OFF. lia. }
  (* the text and the stack are not w *)
  assert (Htx : forall a, pi_text D <= a < pi_text D + pi_len D -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply HA; [lia|]. destruct (Hap a Ha); lia. }
  assert (Hst : forall a, PS_SP D <= a < 2 ^ 64 -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply HA; [lia | lia]. }
  (* the out block is new since the entry *)
  assert (Hnew : ~ In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B (pi_ly D) (pi_S D)))
    by (apply (ps_newblk ly S (pi_ly D) (pi_S D) Hp W mem md _ HAR); [cbn [snd]; lia | exact Eab]).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - (* the carried facts *)
    exists k'. split; [exact HJ'|]. split.
    + (* the kept relation from the entry: the old one, then this stretch's (it wrote w, in the new block) *)
      assert (HK2 : cj_kept SK segs B prh_pst STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [(w, w + 1)]
        ly S W mem md ly S W mem' md').
      { eapply (cj_kept_exec SK segs B prh_pst ARx cf_head LAWS (@pa_segs_low _ _ PS_PAImg) _ _ _ _ _ _ _ _ _ _ _ _ (fun a => a = w) HAR).
        - rewrite Eslo. exact Hceil0.
        - rewrite Eslo. lia.
        - rewrite Eshi. lia.
        - intros x Hx. apply HM. exact Hx.
        - intros a Ea. subst a. right; right. split; [exists (w, w + 1); split; [left; reflexivity | cbn; lia]|].
          exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|]. rewrite ps_req by lia. lia.
        - exact Hsame. }
      eapply (cj_kept_trans SK segs B prh_pst ARx cf_head LAWS); [exact HK | exact HK2 | exact HAR0 | exact HAR | lia | lia | |].
      * intros a Ha. exfalso. exact (inFP_nil a Ha).
      * intros a Ha. right; left. destruct Ha as (rr & Hrr & Hra). destruct Hrr as [<-|[]]. cbn [fst snd] in Hra.
        exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|]. split; [exact Hnew|].
        rewrite ps_req by lia. lia.
    + split; [|split; [|split; [exact HHOME | exact HMN']]].
      * unfold ps_saved in *. destruct HSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
        repeat split; (eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | eassumption]).
      * destruct HSRC as (Hb & H4096 & Hsc & Hamr & Hra & Hhu).
        split; [|split; [exact H4096|split; [exact Hsc|split; [exact Hamr|split]]]].
        -- intros j Hj. destruct (Hb j Hj) as [V R]. split; [|exact R].
           apply (val_mem_keep W W mem mem'); [|exact V]. intros i Hi. cbn in Hi. apply Htx. rewrite <- Hlen. lia.
        -- eapply range_addressable_agree; [|exact Hra]. intros x Hx. apply Hsa. rewrite Hlen in Hx. lia.
        -- intros Hn. apply (hull_keep _ _ _ _ (Hhu Hn)). intros s Hs. apply (Hhul (pi_text D) (Z.of_nat (length (pi_tb D)))); [lia | rewrite Hlen; lia | exact Hn | exact Hs].
  - (* the allocation facts *)
    split; [exact Hcnt|]. split; [exact Hout'|]. split; [exact Hout16|]. split; [exact EHp|]. split; [exact Eab|].
    split; [|split; [|split; [exact Hroom | exact Hbb]]].
    + apply (ledger_keep ly S Hp W mem mem' _ _ _ _ _ _ _ HLED).
      * intros a Ha. destruct (PST_ok a Ha) as [Hi _]. apply HA; [pose proof (@pa_segs_low _ _ PS_PAImg a Hi); unfold kLowMemEnd in *; lia|].
        intros E. subst a. exact (Hwimg Hi).
      * intros a kk i Hin Hi. apply HA.
        { pose proof HLED as HF; apply ps_led_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a, kk) Hin) as (Hk0 & Hab & _).
          cbn [fst snd] in Hk0, Hab. destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
          rewrite ps_req in Hc by lia. lia. }
        destruct Hin as [E | Hin].
        { injection E as <- <-. lia. }
        pose proof HLED as HND; apply ps_led_nodup in HND. pose proof HLED as HF; apply ps_led_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a, kk) (or_intror Hin)) as (Hk0 & Hab & _).
        cbn [fst snd] in Hk0, Hab.
        assert (Hne : (a - cf_head, kk + cf_head) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
        { intros E. injection E as E1 _. cbn [map fst] in HND. inversion HND as [|x l HN HND2]; subst. apply HN.
          assert (Hi2 : In out (map fst (pi_Lam D))) by (apply in_map_iff; exists (a, kk); split; [cbn [fst]; lia | exact Hin]).
          first [ apply list_elem_of_In; exact Hi2 | apply elem_of_list_In; exact Hi2 ]. }
        pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin_o Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !ps_req in Hd by lia. lia.
    + split.
      * eapply range_addressable_agree; [|exact Hvra]. intros x Hx. apply Hsa. lia.
      * intros Hn. apply (hull_keep _ _ _ _ (Hvhu Hn)). intros s Hs. apply (Hhul out (Z.of_nat Q + 1)); [lia | lia | exact Hn | exact Hs].
  - destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V24 & _).
    eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact V24].
  - destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V16 & _).
    eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact V16].
  - destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V8).
    eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact V8].
  - destruct HIN as (Vp & Ve & Vd & Hrw & Hq8' & Ht0' & Ht62 & Htp' & Hlen' & Hg & Hqt & Hd).
    split; [eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact Vp]|].
    split; [eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact Ve]|].
    split; [eapply val_mem_keep; [intros i Hi; apply Hst; cbn in Hi; lia | exact Vd]|].
    split; [intros x Hx; apply (writable_at_grows segs _ _ x HG); apply Hrw; exact Hx|].
    do 5 (split; [assumption|]).
    split; [|split; assumption].
    intros j Hj. destruct (Hg j Hj) as [V R]. split; [|exact R].
    apply (val_mem_keep W W mem mem'); [|exact V]. intros i Hi. cbn in Hi. apply Htx. lia.
  - intros a Hro Hno Her. rewrite (HA a); [exact (HROD a Hro Hno Her) | |].
    + pose proof (@pa_segs_low _ _ PS_PAImg a (psrc_ro_img a Hro)). unfold kLowMemEnd in *. lia.
    + intros E. subst a. exact (Hwimg (psrc_ro_img w Hro)).
  - exact HA.
Qed.

(* ---- the leaves of a stretch from PS_DEC: the cut predicates at the leaf's state ---- *)
(* the register part of ps_dec_consts *)
Definition dc_regs (regs : bvmap 5 word) : Prop :=
  getr regs 26 = w64 34 /\ getr regs 14 = w64 32 /\ getr regs 16 = w64 92 /\ getr regs 15 = w64 101 /\
  getr regs 17 = w64 91 /\ getr regs 5 = w64 47 /\ getr regs 6 = w64 98 /\ getr regs 7 = w64 8 /\
  getr regs 28 = w64 113 /\ getr regs 29 = w64 102 /\ getr regs 30 = w64 12 /\ getr regs 31 = w64 110 /\
  getr regs 27 = w64 10 /\ getr regs 21 = w64 114 /\ getr regs 1 = w64 116.

Lemma rest_at_cons : forall tb text r c, text <= r < text + Z.of_nat (length tb) -> nth (Z.to_nat (r - text)) tb 0 = c ->
  rest_atR tb text r = c :: rest_atR tb text (r + 1).
Proof.
  intros tb text r c Hr Hc. apply psd_rest_cons; [lia|]. rewrite <- Hc. apply nth_error_nth'. lia.
Qed.

(* the success tail: the byte at r is the closing quote *)
Lemma retok_close : forall CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k',
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0 = 34 ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  ps_sh_regs D regs' -> ps_gptp D regs' ->
  getr regs' 2 = w64 (PS_SP D) -> getr regs' 18 = w64 out -> getr regs' 19 = w64 w -> getr regs' 20 = w64 r ->
  getr regs' 8 = w64 (pi_q D) -> getr regs' 9 = w64 (pi_q D + 8) ->
  ps_at_retokP B ARx SK P D ly S Hp W regs' mem' md' out w r Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k' HPRE HDEC Hq HJ' HMN' Hsame HM HG HSH HGT R2 R18 R19 R20 R8 R9.
  destruct (dec_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  destruct (dec_keep CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG)
    as (HC & HAL & _ & _ & _ & HIN & _ & HA).
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSC & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr' & Hwo & Hww & Hsync).
  rewrite (rest_at_cons _ _ r 34) in HS, Hsync by (try exact Hq; lia).
  cbn [PjGrammar.scan] in Hsync. injection Hsync as Hsync.
  assert (Er : r = pi_p D + 1 + Z.of_nat Q) by lia.
  split; [exact HC|]. split; [exact HAL|]. split; [exact HSH|]. split; [exact HGT|]. split; [exact HIN|].
  split; [exact HSC|]. split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R8|]. split; [exact R9|]. split; [exact Er|].
  split; [|lia].
  exists done. split; [rewrite <- (app_nil_r done); apply HS; reflexivity|]. split; [|exact Hdl].
  intros j Hj. destruct (Hbd j Hj) as [V R]. split; [|exact R].
  pose proof asan_consts as (C1 & _). pose proof ps_head8 as Hh8.
  apply (val_mem_keep W W mem mem'); [|exact V]. intros i Hi. cbn in Hi. apply HA; lia.
Qed.

(* a one-byte step: the byte c at w, the cursor from r to r' *)
Lemma dec_close1 : forall CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k' r' c,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = PjGrammar.emit [c] (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r')) ->
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (q + Z.to_nat (r' - r))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r')) ->
  r < r' -> 0 <= c < 256 ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  val_mem segs (rdW W mem') w 1 c ->
  ps_sh_regs D regs' -> ps_gptp D regs' -> dc_regs regs' ->
  getr regs' 2 = w64 (PS_SP D) -> getr regs' 18 = w64 out -> getr regs' 19 = w64 (w + 1) -> getr regs' 20 = w64 r' ->
  getr regs' 11 = w64 (pi_text D + pi_len D) -> getr regs' 8 = w64 (pi_q D) -> getr regs' 9 = w64 (pi_q D + 8) ->
  ps_at_decP B ARx SK P D ly S Hp W regs' mem' md' out (w + 1) r' Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k' r' c HPRE HDEC Hstep Hscan Hrr Hc
    HJ' HMN' Hsame HM HG Vc HSH HGT HDC R2 R18 R19 R20 R11 R8 R9.
  destruct (dec_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  destruct (dec_keep CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG)
    as (HC & HAL & V24 & V16 & V8 & HIN & HROD & HA).
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSC & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr' & Hwo & Hww & Hsync).
  destruct (psd_scan_sync _ _ _ _ Hscan Hsync) as [Hsync' Hle].
  split; [exact HC|]. split; [exact HAL|]. split; [exact HSH|]. split; [exact HGT|].
  split; [destruct HDC as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15);
    repeat (split; [eassumption|]); repeat split; assumption|].
  split; [exact HIN|]. split; [exact HROD|]. split; [exact HSC|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R11|]. split; [exact R8|]. split; [exact R9|].
  exists (done ++ [c]). split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Nat.lt_ge_cases j (length done)) as [Hjl|Hjl].
    + rewrite app_nth1 by exact Hjl. destruct (Hbd j Hjl) as [V R]. split; [|exact R].
      pose proof asan_consts as (C1 & _). pose proof ps_head8 as Hh8.
      apply (val_mem_keep W W mem mem'); [|exact V]. intros i Hi. cbn in Hi. apply HA; lia.
    + assert (j = length done) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      split; [|exact Hc]. replace (out + Z.of_nat (length done)) with w by lia. exact Vc.
  - rewrite length_app. cbn [length]. lia.
  - exact (proj1 (psd_rel_step _ _ _ _ _ (conj HS HN) Hstep)).
  - exact (proj2 (psd_rel_step _ _ _ _ _ (conj HS HN) Hstep)).
  - lia.
  - lia.
  - lia.
  - rewrite Hsync'. f_equal. lia.
Qed.

(* the free path's cut (offset 1276, `mv a0, s2` before `jal fuzz_free`): decoding the text is refused *)
Definition ps_at_free (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out : Z) (Q : nat) : Prop :=
  (exists k, ps_carry B ARx SK D ly S Hp W mem md k []) /\ ps_alloc B D ly S Hp W mem out Q /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs (@pa_relro_lo _ A_prog_listing PS_PAImg) (@pa_relro_hi _ A_prog_listing PS_PAImg) B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\ PjGrammar.decode (ps_x D) = None /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 8 = w64 (pi_q D).
(* its P form: the carry with the invariant *)
Definition ps_at_freeP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP B ARx SK P D ly S Hp W mem md k []) /\ ps_alloc B D ly S Hp W mem out Q /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs (@pa_relro_lo _ A_prog_listing PS_PAImg) (@pa_relro_hi _ A_prog_listing PS_PAImg) B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\ PjGrammar.decode (ps_x D) = None /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 8 = w64 (pi_q D).
Lemma free_close : forall CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k',
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  ps_gptp D regs' -> getr regs' 2 = w64 (PS_SP D) -> getr regs' 18 = w64 out -> getr regs' 8 = w64 (pi_q D) ->
  ps_at_freeP D ly S Hp W regs' mem' md' out Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs' mem' md' k' HPRE HDEC HNone HJ' HMN' Hsame HM HG HGT R2 R18 R8.
  destruct (dec_keep CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG)
    as (HC & HAL & _ & _ & _ & HIN & HROD & _).
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSC & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct HREL as (done & _ & _ & _ & HN & _).
  split; [exact HC|]. split; [exact HAL|]. split; [exact HGT|]. split; [exact HIN|]. split; [exact HROD|].
  split; [exact HSC|]. split; [exact (HN HNone)|]. split; [exact R2|]. split; [exact R18 | exact R8].
Qed.

(* the free path, from its cut at offset 1276 (DERIVED: `mv a0, s2` before `jal fuzz_free` at 1280). Its run crosses
   fuzz_free, so it concludes SRr' segs RZ_cf with the post at wle' segs RZ_cf (the kit's primed tfuzz_free_specX); so do
   the loop's back edge and the \u stretch, which may reach it *)
Definition PS_FREECUT : Z := 1276.
Definition ps_seg_free (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out Q, ps_pre B ARx CTX CW D -> ps_at_free D ly S Hp W regs mem md out Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_FREECUT) regs mem md)
    (ps_postR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_freeP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out Q, ps_pre B ARx CTX CW D -> ps_at_freeP D ly S Hp W regs mem md out Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_FREECUT) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).

(* the loop from PS_DEC at every cursor past r0: the induction hypothesis a sub-stretch that reaches the back-edge
   (offset 872 `bltu s6, a1` to PS_DEC) applies *)
Definition ps_dec_after (CW : list (list Z)) (D : ps_in) (r0 : Z) : Prop :=
  forall ly S Hp W regs mem md out w r Q, ps_at_dec B ARx SK D ly S Hp W regs mem md out w r Q -> r0 < r ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_dec_afterP (CW : list (list Z)) (D : ps_in) (r0 : Z) : Prop :=
  forall ly S Hp W regs mem md out w r Q, ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q -> r0 < r ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).
(* the \u sub-stretch: from PS_DEC when the text at r is a backslash then u (WORD 92, 117): the dispatch at
   408..443, the hex loop at PS_HEX (452..551), the tail at 880..1104 with the hex4 call (988) and the put_utf8 call
   (1044), the latch at 856..872; it ends at the back-edge (ps_dec_after) or at the free cut (ps_seg_free) *)
Definition ps_seg_u (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre B ARx CTX CW D -> ps_at_dec B ARx SK D ly S Hp W regs mem md out w r Q ->
  nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0 = 92 -> nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0 = 117 ->
  ps_dec_after CW D r -> SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_uP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0 = 92 -> nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0 = 117 ->
  ps_dec_afterP CW D r -> SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).
(* the out byte lies in the block made since the entry *)
Lemma dec_tmp_w : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  in_tmp_block (ablocks B (pi_ly D) (pi_S D)) (ablocks B ly S) w.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  destruct (dec_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof HDEC as (_ & (_ & _ & _ & _ & Eab & _) & _).
  pose proof cf_head_nonneg as Hh0.
  exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
  split; [rewrite Eab; apply in_or_app; right; left; reflexivity|].
  split; [apply (ps_newblk ly S (pi_ly D) (pi_S D) Hp W mem md _ HAR); [cbn [snd]; lia | exact Eab]|].
  rewrite ps_req by lia. lia.
Qed.
End d.

(* ---- the stable kit statements are the P := (fun _ => True) instances, both ways (S4_PsBase.v's ps_seg_*_of_True) ---- *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Lemma ps_at_decP_T : forall D ly S Hp W regs mem md out w r Q,
  ps_at_dec B ARx SK D ly S Hp W regs mem md out w r Q <-> ps_at_decP B ARx SK (fun _ => True) D ly S Hp W regs mem md out w r Q.
Proof.
intros. split; intros (Hc & H); (split; [|exact H]).
- apply (proj1 (ps_ex_carryP_T B ARx SK _ _ _ _ _ _ _)). exact Hc.
- apply (proj2 (ps_ex_carryP_T B ARx SK _ _ _ _ _ _ _)). exact Hc.
Qed.
Lemma ps_at_freeP_T : forall D ly S Hp W regs mem md out Q,
  ps_at_free B ARx SK D ly S Hp W regs mem md out Q <-> ps_at_freeP B ARx SK (fun _ => True) D ly S Hp W regs mem md out Q.
Proof.
intros. split; intros (Hc & H); (split; [|exact H]).
- apply (proj1 (ps_ex_carryP_T B ARx SK _ _ _ _ _ _ _)). exact Hc.
- apply (proj2 (ps_ex_carryP_T B ARx SK _ _ _ _ _ _ _)). exact Hc.
Qed.
Lemma ps_seg_free_of_True : forall CTX CW, ps_seg_freeP B ARx SK (fun _ => True) CTX CW <-> ps_seg_free B ARx SK CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md out Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out Q HP); exact (proj1 (ps_at_freeP_T D ly S Hp W regs mem md out Q) HA)|].
  intros W' c' _ HQ. apply (proj1 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
- intros H D ly S Hp W regs mem md out Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out Q HP); exact (proj2 (ps_at_freeP_T D ly S Hp W regs mem md out Q) HA)|].
  intros W' c' _ HQ. apply (proj2 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
Qed.
Lemma ps_dec_after_of_True : forall CW D r0, ps_dec_afterP B ARx SK (fun _ => True) CW D r0 <-> ps_dec_after B ARx SK CW D r0.
Proof.
intros CW D r0. split.
- intros H ly S Hp W regs mem md out w r Q HA Hr. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [apply (H ly S Hp W regs mem md out w r Q);
    [exact (proj1 (ps_at_decP_T D ly S Hp W regs mem md out w r Q) HA) | exact Hr]|].
  intros W' c' _ HQ. apply (proj1 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
- intros H ly S Hp W regs mem md out w r Q HA Hr. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [apply (H ly S Hp W regs mem md out w r Q);
    [exact (proj2 (ps_at_decP_T D ly S Hp W regs mem md out w r Q) HA) | exact Hr]|].
  intros W' c' _ HQ. apply (proj2 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
Qed.
Lemma ps_seg_u_of_True : forall CTX CW, ps_seg_uP B ARx SK (fun _ => True) CTX CW <-> ps_seg_u B ARx SK CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md out w r Q HP HA H92 H117 AFT. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [apply (H D ly S Hp W regs mem md out w r Q HP);
    [exact (proj1 (ps_at_decP_T D ly S Hp W regs mem md out w r Q) HA) | exact H92 | exact H117 |
     exact (proj2 (ps_dec_after_of_True CW D r) AFT)]|].
  intros W' c' _ HQ. apply (proj1 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
- intros H D ly S Hp W regs mem md out w r Q HP HA H92 H117 AFT. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [apply (H D ly S Hp W regs mem md out w r Q HP);
    [exact (proj2 (ps_at_decP_T D ly S Hp W regs mem md out w r Q) HA) | exact H92 | exact H117 |
     exact (proj1 (ps_dec_after_of_True CW D r) AFT)]|].
  intros W' c' _ HQ. apply (proj2 (ps_postPR_T B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D W' c')). exact HQ.
Qed.
End t.

Lemma sv_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
Lemma st_reg : forall H E ss ms (r : bv 5) e,
  st_ok_pi (@pa_segs _ A_prog_listing PS_PAImg) (@pa_val _ A_prog_listing PS_PAImg) E ss (restrict H ms) ->
  sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite <- He. exact (st_ok_pi_restrict_reg H E ss ms r HS). Qed.
End rg.

(* ---- a run's frame over the layout's one writable window ---- *)
Definition wwin_ok (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some 19%nat) && (YP09.r_wlo r =? 0) && (YP09.r_whi r =? 1))) rs.
Lemma frame_w : forall E rs (m m' : word -> option byte) w, wwin_ok rs = true -> bv_unsigned (ew E 19) = w ->
  frame_of E rs m m' -> forall x : word, bv_unsigned x <> w -> m' x = m x.
Proof.
  intros E rs m m' w Hok H19 Hfr x Hx. apply Hfr. intros (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply Z.leb_le in Hb; lia|].
  apply andb_true_iff in Hb as [Hb Hh]. apply andb_true_iff in Hb as [Hb Hl]. apply Z.eqb_eq in Hl, Hh.
  destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate]. cbn in Hb. apply Nat.eqb_eq in Hb. subst n.
  cbn [base_val] in Hr. rewrite H19 in Hr. lia.
Qed.
Lemma awr_w : forall E rs STK sp0 FP bl0 blc ly own w, wwin_ok rs = true -> bv_unsigned (ew E 19) = w ->
  in_tmp_block bl0 blc w -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs STK sp0 FP bl0 blc ly own w Hok H19 Ht a (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply Z.leb_le in Hb; lia|].
  apply andb_true_iff in Hb as [Hb Hh]. apply andb_true_iff in Hb as [Hb Hl]. apply Z.eqb_eq in Hl, Hh.
  destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate]. cbn in Hb. apply Nat.eqb_eq in Hb. subst n.
  cbn [base_val] in Hr. rewrite H19 in Hr. replace a with w by lia.
  right; right; left. exact Ht.
Qed.
Section o. Context {fx : YK11.FPState}.
Variable segs : list Segment.
(* a shadow obligation of a run from a range the state's facts make addressable *)
Lemma ob_range : forall H mem E Bx x a n p m, range_addressable (aview segs H mem) SHADOW_OFF a n ->
  U E Bx = SHADOW_OFF -> U E x = p -> a <= p -> p + m <= a + n ->
  range_addressable (rd_of segs (mrestrict H mem)) (U E Bx) (U E x) m.
Proof.
  intros H mem E Bx x a n p m Hra HB Hx Ha Hm. rewrite HB, Hx. rewrite <- (aview_rd_of segs).
  apply (range_addressable_sub _ SHADOW_OFF a n p m Hra Ha Hm).
Qed.
End o.
